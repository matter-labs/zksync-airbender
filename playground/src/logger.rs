use log::{Level, Metadata, Record};
use std::cell::RefCell;
use std::time::Instant;

pub struct ThreadLocalLogger {
    pub name: String,
    pub timer: Instant,
}

impl log::Log for ThreadLocalLogger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= Level::Info
    }

    fn log(&self, record: &Record) {
        assert_eq!(record.level(), Level::Info);
        if self.enabled(record.metadata()) {
            println!(
                "| {:>10.6} | {:^6} | {}",
                self.timer.elapsed().as_secs_f32(),
                self.name,
                record.args()
            );
        }
    }

    fn flush(&self) {}
}

thread_local! {
    pub static LOCAL_LOGGER: RefCell<ThreadLocalLogger> = RefCell::new(ThreadLocalLogger {
        name: std::thread::current().name().unwrap_or("unknown").to_string(),
        timer: Instant::now(),
    });
}

pub struct GlobalLogger;

impl log::Log for GlobalLogger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        LOCAL_LOGGER.with_borrow(|l| l.enabled(metadata))
    }

    fn log(&self, record: &Record) {
        LOCAL_LOGGER.with_borrow(|l| l.log(record));
    }

    fn flush(&self) {}
}

pub static LOGGER: GlobalLogger = GlobalLogger;
