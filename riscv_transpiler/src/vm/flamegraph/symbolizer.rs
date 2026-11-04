use addr2line_new::gimli::{EndianSlice, LittleEndian};
use object::{Object, ObjectSection};

/// Thin adapter around addr2line so the profiler deals with simple
/// `pc -> frame names` lookups.
pub(super) struct Addr2LineContext<'a> {
    addr2line_tooling: addr2line_new::Context<EndianSlice<'a, LittleEndian>>,
}

impl<'a> Addr2LineContext<'a> {
    pub(super) fn new(binary: &'a [u8]) -> std::io::Result<Self> {
        use addr2line_new::gimli::{AbbreviationsCacheStrategy, Dwarf, SectionId};

        let object = object::File::parse(binary).map_err(|error| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!("while attempting to parse symbols object file: {error}"),
            )
        })?;
        if object.is_little_endian() == false {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "symbols file must be little-endian",
            ));
        }

        // We keep DWARF data borrowed from the original binary to avoid extra
        // allocation and copying in the common case.
        let load_section_fn = |id: SectionId| -> std::io::Result<EndianSlice<'a, LittleEndian>> {
            let name = id.name();
            let Some(section) = object.section_by_name(name) else {
                return Ok(EndianSlice::new(&[][..], LittleEndian));
            };

            let data = section.uncompressed_data().map_err(|error| {
                std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!("while attempting to read DWARF section {name}: {error}"),
                )
            })?;

            match data {
                std::borrow::Cow::Borrowed(section) => Ok(EndianSlice::new(section, LittleEndian)),
                // Compressed sections would require owned decompression buffers;
                // we reject them to keep lifetimes and memory behavior simple.
                std::borrow::Cow::Owned(_) => Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!("DWARF section {name} is compressed and not supported"),
                )),
            }
        };

        let mut dwarf: Dwarf<EndianSlice<'a, LittleEndian>> = Dwarf::load(load_section_fn)?;
        dwarf.populate_abbreviations_cache(AbbreviationsCacheStrategy::Duplicates);

        let addr2line_tooling = addr2line_new::Context::from_dwarf(dwarf).map_err(|error| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!("while attempting to build addr2line context: {error}"),
            )
        })?;

        Ok(Self { addr2line_tooling })
    }

    pub(super) fn collect_frames(&self, pc: u32) -> Vec<String> {
        // Symbolization is best-effort. If one PC fails, we keep generating the
        // flamegraph from the rest of the samples.
        let Ok(mut it) = self
            .addr2line_tooling
            .find_frames(pc as u64)
            .skip_all_loads()
        else {
            return Vec::new();
        };

        const UNKNOWN_MANGLED: &str = "::unknown mangled::";
        let mut result = Vec::with_capacity(16);

        loop {
            match it.next() {
                Ok(Some(inner)) => {
                    let Some(function) = inner.function else {
                        continue;
                    };

                    // Prefer demangled names for readability, then fall back to
                    // raw symbol bytes when demangling is unavailable.
                    let symbol_name = if let Ok(demangled) = function.demangle() {
                        match demangled {
                            std::borrow::Cow::Owned(owned) => owned,
                            std::borrow::Cow::Borrowed(borrowed) => borrowed.to_string(),
                        }
                    } else if let Ok(name) = std::str::from_utf8(&function.name) {
                        name.to_string()
                    } else {
                        UNKNOWN_MANGLED.to_string()
                    };

                    result.push(symbol_name);
                }
                Ok(None) => return result,
                Err(_) => return result,
            }
        }
    }
}
