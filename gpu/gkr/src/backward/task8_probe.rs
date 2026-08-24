//! Task-8-only pre-enqueue telemetry.
//!
//! Every stream enqueue the prepared-state differential covers opens a scope
//! *before* the launch or copy it describes and closes it after that call
//! returns, so the recorded order is the order the runtime received the work
//! rather than an order reconstructed afterwards. Each scope carries the
//! pointer arguments that enqueue is about to hand the runtime, taken from the
//! descriptor or copy arguments themselves.
//!
//! The probe is inert unless a differential arm installs it: every entry point
//! reads one thread-local and returns, and the span closure never runs. It
//! makes no CUDA call, allocates no device memory, and changes no launch, copy,
//! allocation, synchronization or geometry behaviour.

use std::cell::RefCell;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Task8EnqueueKind {
    Copy,
    Kernel,
    Callback,
}

/// One pointer argument of one enqueue: the exact address it names and the
/// exact bytes that argument's geometry fixes. A descriptor address slot is
/// recorded as one span per column it names, at the base and stride that slot
/// fixes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Task8Span {
    pub(crate) role: &'static str,
    pub(crate) address: usize,
    pub(crate) bytes: usize,
    pub(crate) write: bool,
    /// `address` is an offset inside the named symbol until the probe resolves
    /// it against the address that symbol's own enqueue reported.
    pub(crate) symbol: bool,
    /// The enqueue reads bytes it did not write and this generation never
    /// wrote: content the allocation or symbol already held.
    pub(crate) resident: bool,
}

impl Task8Span {
    fn plain(role: &'static str, address: usize, bytes: usize) -> Self {
        Self {
            role,
            address,
            bytes,
            write: false,
            symbol: false,
            resident: false,
        }
    }

    pub(crate) fn read(role: &'static str, address: usize, bytes: usize) -> Self {
        Self::plain(role, address, bytes)
    }

    pub(crate) fn write(role: &'static str, address: usize, bytes: usize) -> Self {
        Self {
            write: true,
            ..Self::plain(role, address, bytes)
        }
    }

    pub(crate) fn resident_read(role: &'static str, address: usize, bytes: usize) -> Self {
        Self {
            resident: true,
            ..Self::plain(role, address, bytes)
        }
    }

    /// Reads the whole region an earlier enqueue registered under `symbol`.
    pub(crate) fn symbol_region(symbol: &'static str) -> Self {
        Self {
            bytes: usize::MAX,
            symbol: true,
            ..Self::plain(symbol, 0, 0)
        }
    }

    /// Reads `bytes` at `offset` inside a device symbol the harness or an
    /// earlier enqueue registered by name.
    pub(crate) fn symbol_read(symbol: &'static str, offset: usize, bytes: usize) -> Self {
        Self {
            symbol: true,
            ..Self::plain(symbol, offset, bytes)
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Task8Enqueue {
    pub(crate) ordinal: u64,
    pub(crate) site: &'static str,
    pub(crate) kind: Task8EnqueueKind,
    pub(crate) spans: Vec<Task8Span>,
    /// How many enqueues had already been issued when this one was opened. A
    /// scope opened before its own call sees exactly its own ordinal here.
    pub(crate) issued_at_open: u64,
    pub(crate) issued_at_close: Option<u64>,
}

#[derive(Debug, Default)]
struct Task8ProbeState {
    enqueues: Vec<Task8Enqueue>,
    next_ordinal: u64,
    issued: u64,
    open: Vec<u64>,
    symbols: std::collections::BTreeMap<&'static str, (usize, usize)>,
    descriptor_sources: std::collections::BTreeMap<usize, usize>,
}

thread_local! {
    static PROBE: RefCell<Option<Task8ProbeState>> = const { RefCell::new(None) };
}

/// Installs the probe for one differential arm. Nesting is rejected, so an arm
/// can never inherit another arm's enqueue stream.
pub(crate) struct Task8ProbeGuard {
    active: bool,
}

impl Task8ProbeGuard {
    pub(crate) fn install() -> Self {
        PROBE.with(|probe| {
            let mut probe = probe.borrow_mut();
            assert!(probe.is_none(), "the Task 8 enqueue probe cannot be nested");
            *probe = Some(Task8ProbeState::default());
        });
        Self { active: true }
    }

    /// Takes every enqueue observed since the last drain, in the order the
    /// scopes were opened.
    pub(crate) fn drain(&self) -> Vec<Task8Enqueue> {
        PROBE.with(|probe| {
            let mut probe = probe.borrow_mut();
            let state = probe
                .as_mut()
                .expect("the Task 8 enqueue probe is not installed");
            assert!(
                state.open.is_empty(),
                "a Task 8 enqueue scope was still open at a drain"
            );
            std::mem::take(&mut state.enqueues)
        })
    }

    pub(crate) fn finish(mut self) -> Vec<Task8Enqueue> {
        let remaining = self.drain();
        self.active = false;
        PROBE.with(|probe| {
            *probe.borrow_mut() = None;
        });
        remaining
    }
}

impl Drop for Task8ProbeGuard {
    fn drop(&mut self) {
        if self.active {
            PROBE.with(|probe| {
                *probe.borrow_mut() = None;
            });
        }
    }
}

/// One open enqueue. Created immediately before the launch or copy it
/// describes; closed when it leaves scope, after that call has returned.
pub(crate) struct Task8EnqueueScope {
    ordinal: Option<u64>,
}

impl Drop for Task8EnqueueScope {
    fn drop(&mut self) {
        let Some(ordinal) = self.ordinal else {
            return;
        };
        PROBE.with(|probe| {
            let mut probe = probe.borrow_mut();
            let Some(state) = probe.as_mut() else {
                return;
            };
            assert_eq!(
                state.open.pop(),
                Some(ordinal),
                "Task 8 enqueue scopes closed out of order"
            );
            state.issued += 1;
            let issued = state.issued;
            let entry = state
                .enqueues
                .iter_mut()
                .find(|entry| entry.ordinal == ordinal)
                .expect("a closed Task 8 enqueue scope left no record");
            entry.issued_at_close = Some(issued);
        });
    }
}

/// Names a device symbol by the address an enqueue argument or the harness's
/// own copy already carried, so a launch that reads the symbol without naming
/// it can still record an exact range. A later fill may register a different
/// live extent at the same address; a different address is a fault.
pub(crate) fn task8_register_symbol(symbol: &'static str, address: usize, bytes: usize) {
    PROBE.with(|probe| {
        let mut probe = probe.borrow_mut();
        let Some(state) = probe.as_mut() else {
            return;
        };
        let previous = state.symbols.insert(symbol, (address, bytes));
        assert!(
            previous.is_none_or(|(previous, _)| previous == address),
            "the Task 8 symbol {symbol} moved between enqueues"
        );
    });
}

/// Records how many leading entries of a segmented descriptor's source table
/// are live. The table itself is zero-filled to its ABI capacity, so the count
/// is the one thing a launch cannot recover from the descriptor.
pub(crate) fn task8_register_descriptor_sources(descriptor: usize, sources: usize) {
    PROBE.with(|probe| {
        let mut probe = probe.borrow_mut();
        let Some(state) = probe.as_mut() else {
            return;
        };
        state.descriptor_sources.insert(descriptor, sources);
    });
}

pub(crate) fn task8_descriptor_sources(descriptor: usize) -> Option<usize> {
    PROBE.with(|probe| {
        probe
            .borrow()
            .as_ref()
            .and_then(|state| state.descriptor_sources.get(&descriptor).copied())
    })
}

/// The address and byte extent registered for a symbol, once an enqueue that
/// used it has reported it.
pub(crate) fn task8_symbol(symbol: &'static str) -> Option<(usize, usize)> {
    PROBE.with(|probe| {
        probe
            .borrow()
            .as_ref()
            .and_then(|state| state.symbols.get(symbol).copied())
    })
}

/// Opens one enqueue. `spans` runs only while the probe is installed, so an
/// uninstrumented build pays one thread-local read.
pub(crate) fn task8_enqueue<F>(
    site: &'static str,
    kind: Task8EnqueueKind,
    spans: F,
) -> Task8EnqueueScope
where
    F: FnOnce() -> Vec<Task8Span>,
{
    let ordinal = PROBE.with(|probe| {
        let mut probe = probe.borrow_mut();
        let state = probe.as_mut()?;
        let ordinal = state.next_ordinal;
        state.next_ordinal += 1;
        let issued_at_open = state.issued;
        state.enqueues.push(Task8Enqueue {
            ordinal,
            site,
            kind,
            spans: Vec::new(),
            issued_at_open,
            issued_at_close: None,
        });
        state.open.push(ordinal);
        Some(ordinal)
    });
    if let Some(ordinal) = ordinal {
        let spans = spans();
        PROBE.with(|probe| {
            let mut probe = probe.borrow_mut();
            let state = probe
                .as_mut()
                .expect("the Task 8 enqueue probe was uninstalled mid-scope");
            let spans = spans
                .into_iter()
                .map(|mut span| {
                    if span.symbol {
                        let (base, extent) = *state.symbols.get(span.role).unwrap_or_else(|| {
                            panic!("Task 8 symbol {} was never registered", span.role)
                        });
                        if span.bytes == usize::MAX {
                            span.bytes = extent;
                        }
                        span.address += base;
                        span.symbol = false;
                    }
                    span
                })
                .collect();
            state
                .enqueues
                .iter_mut()
                .find(|entry| entry.ordinal == ordinal)
                .expect("an open Task 8 enqueue scope lost its record")
                .spans = spans;
        });
    }
    Task8EnqueueScope { ordinal }
}
