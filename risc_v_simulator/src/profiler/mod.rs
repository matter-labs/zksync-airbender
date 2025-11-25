use std::collections::BTreeMap;

use addr2line_new::gimli::EndianSlice;
use addr2line_new::gimli::LittleEndian;
use addr2line_new::Frame;
use rayon::iter::ParallelIterator;
use rayon::slice::ParallelSliceMut;

// NOTE: not send or sync...
pub struct Addr2LineContext<'a> {
    pub binary: &'a [u8],
    text_section_size: usize,
    addr2line_tooling: addr2line_new::Context<EndianSlice<'a, LittleEndian>>,
}

impl<'a> Addr2LineContext<'a> {
    pub fn new(binary: &'a [u8]) -> Self {
        use addr2line_new::gimli::RunTimeEndian;
        use addr2line_new::gimli::SectionId;
        use object::Object;
        use object::ObjectSection;

        let object = object::File::parse(binary).unwrap();
        assert!(object.is_little_endian());

        let section = object.section_by_name(".symtab").unwrap();
        let text_section_size = section.size().next_power_of_two() as usize;

        let load_section_fn = |id: SectionId| -> Result<_, ()> {
            let name = id.name();

            match object.section_by_name(name) {
                Some(section) => match section.uncompressed_data().unwrap() {
                    std::borrow::Cow::Borrowed(section) => {
                        Ok(EndianSlice::new(section, LittleEndian))
                    }
                    std::borrow::Cow::Owned(_) => {
                        unreachable!("We're following the borrowed path.")
                    }
                },
                None => Ok(EndianSlice::new(&[][..], LittleEndian)),
            }
        };

        let mut dwarf: addr2line_new::gimli::Dwarf<EndianSlice<'a, LittleEndian>> =
            addr2line_new::gimli::Dwarf::load(load_section_fn)
                .expect("Debug symbols could not be loaded.");
        dwarf.populate_abbreviations_cache(
            addr2line_new::gimli::AbbreviationsCacheStrategy::Duplicates,
        );

        let addr2line_tooling: addr2line_new::Context<EndianSlice<'a, LittleEndian>> =
            addr2line_new::Context::from_dwarf(dwarf).unwrap();

        assert!(text_section_size > 0);

        Self {
            binary,
            text_section_size,
            addr2line_tooling,
        }
    }

    pub fn duplicate(&self) -> Self {
        Self::new(self.binary)
    }

    pub fn collect_frames(&self, pc: u32) -> Vec<String> {
        let Ok(mut it) = self
            .addr2line_tooling
            .find_frames(pc as u64)
            .skip_all_loads()
        else {
            return Vec::new();
        };

        const MANGLED: &str = "::unknown mangled::";

        let mut result = Vec::with_capacity(16);

        loop {
            match it.next() {
                Ok(inner) => {
                    if let Some(inner) = inner {
                        if let Some(function) = inner.function {
                            let string = if let Ok(demangled) = function.demangle() {
                                use std::borrow::Cow;
                                match demangled {
                                    Cow::Owned(owned) => owned,
                                    Cow::Borrowed(str) => str.to_string(),
                                }
                            } else {
                                if let Ok(name) = std::str::from_utf8(&function.name) {
                                    name.to_string()
                                } else {
                                    MANGLED.to_string()
                                }
                            };
                            result.push(string);
                        }
                    } else {
                        return result;
                    }
                }
                Err(..) => {
                    return result;
                }
            }
        }

        result
    }

    // pub fn symbol_idx_for_pc(&self, pc: u32) -> Option<usize> {
    //     for symbold in self.addr2line_tooling.find_dwarf_and_unit(probe)
    //     let mut unit = self.addr2line_tooling.find_dwarf_and_unit(pc as u64).skip_all_loads()?;
    //     unit.dwarf.attr_ranges_offset(unit, attr)
    //     let unit_offset = unit.header.offset();

    //     loop {
    //         match it.next() {
    //             Ok(inner) => {
    //                 if let Some(inner) = inner {
    //                     if let Some(function) = inner.function {
    //                         let string = if let Ok(demangled) = function.demangle() {
    //                             use std::borrow::Cow;
    //                             match demangled {
    //                                 Cow::Owned(owned) => {
    //                                     owned
    //                                 },
    //                                 Cow::Borrowed(str) => {
    //                                     str.to_string()
    //                                 }
    //                             }
    //                         } else {
    //                             if let Ok(name) = std::str::from_utf8(&function.name) {
    //                                 name.to_string()
    //                             } else {
    //                                 MANGLED.to_string()
    //                             }
    //                         };
    //                         result.push(string);
    //                     }
    //                 } else {
    //                     return result;
    //                 }
    //             },
    //             Err(..) => {
    //                 return result;
    //             }
    //         }
    //     }

    //     todo!();
    // }
}

pub fn get_text_section_max_size(binary: &[u8]) -> usize {
    use addr2line_new::gimli::RunTimeEndian;
    use addr2line_new::gimli::SectionId;
    use object::Object;
    use object::ObjectSection;

    let object = object::File::parse(binary).unwrap();
    assert!(object.is_little_endian());

    let section = object.section_by_name(".symtab").unwrap();
    let text_section_size = section.size().next_power_of_two() as usize;

    text_section_size
}

pub fn produce_cache_for_binary(binary: &[u8]) -> Vec<(u32, Vec<String>)> {
    let pool = rayon::ThreadPoolBuilder::new().build().unwrap();
    let upper_bound = get_text_section_max_size(binary);
    let work_size = upper_bound / 4;

    let mut result = Vec::with_capacity(work_size);
    for i in 0..work_size {
        let pc = (i * 4) as u32;
        result.push((pc, vec![]));
    }
    let chunk_size = result.len().div_ceil(pool.current_num_threads());

    pool.scope(|_| {
        result.par_chunks_mut(chunk_size).for_each(|chunk| {
            let tooling = Addr2LineContext::new(binary);
            for (pc, dst) in chunk.iter_mut() {
                *dst = tooling.collect_frames(*pc);
            }
        });
    });

    result
}

pub fn produce_aggregated_cache_for_binary(binary: &[u8]) -> BTreeMap<u32, Vec<String>> {
    let mut result = BTreeMap::new();
    let mut start: Option<(u32, Vec<String>)> = None;
    for (pc, frames) in produce_cache_for_binary(binary).into_iter() {
        if let Some((start_pc, current_frames)) = start.as_mut() {
            if &current_frames[..] != &frames[..] {
                let previous_chunk = core::mem::replace(current_frames, frames);
                result.insert(*start_pc, previous_chunk);
                *start_pc = pc;
            }
        } else {
            start = Some((pc, frames));
        }
    }

    if let Some((pc, frames)) = start {
        result.insert(pc, frames);
    }

    result
}

// pub fn produce_cache_for_binary(binary: &[u8]) -> Vec<(u32, Vec<String>)> {
//     let pool = rayon::ThreadPoolBuilder::new().build().unwrap();
//     let upper_bound = get_text_section_max_size(binary);
//     let work_size = upper_bound / 4;

//     let mut result = Vec::with_capacity(work_size);
//     for i in 0..work_size {
//         let pc = (i * 4) as u32;
//         result.push((pc, vec![]));
//     }
//     let chunk_size = result.len().div_ceil(pool.current_num_threads());

//     pool.scope(|_| {
//         result.par_chunks_mut(chunk_size).for_each(|chunk| {
//             let tooling = Addr2LineContext::new(binary);
//             for (pc, dst) in chunk.iter_mut() {
//                 *dst = tooling.collect_frames(*pc);
//             }
//         });
//     });

//     result
// }

#[test]
fn test_types() {
    use std::io::Read;
    let mut buffer = vec![];
    let mut file = std::fs::File::open("../../zksync-os/zksync_os/app.elf").unwrap();
    file.read_to_end(&mut buffer).unwrap();

    let context = Addr2LineContext::new(&buffer);

    let frames = context.collect_frames(0x1000);
    dbg!(frames);

    // let mut unit = context.addr2line_tooling.find_dwarf_and_unit(0x1000).skip_all_loads().unwrap();
    // dbg!(unit);

    // let all_frames = produce_cache_for_binary(&buffer);
    // dbg!(&all_frames[..32]);

    let aggregate_cache = produce_aggregated_cache_for_binary(&buffer);
    dbg!(aggregate_cache.len());
    let mut t = aggregate_cache.range(..=0x1000);
    let (pc, frames) = t.next_back().unwrap();
    println!("From PC = 0x{:08x} frames are {:?}", pc, frames);
    let (pc, frames) = t.next_back().unwrap();
    println!("From PC = 0x{:08x} frames are {:?}", pc, frames);
}
