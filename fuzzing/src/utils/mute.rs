#[cfg(unix)]
#[cfg(feature = "mute")]
mod imp {
    use libc::c_int;
    use libc::STDERR_FILENO;
    use libc::STDOUT_FILENO;
    use std::fs::File;
    use std::io;
    use std::mem::ManuallyDrop;
    use std::os::fd::AsRawFd;
    use std::os::fd::FromRawFd as _;
    use std::os::fd::IntoRawFd as _;
    use std::os::fd::RawFd;
    use std::path::Path;

    fn override_stdio(stdio: RawFd, other: RawFd, owned: bool) -> io::Result<File> {
        let original = io_res(unsafe { libc::dup(stdio) })?;
        set_stdio(stdio, other)?;

        if owned {
            io_res(unsafe { libc::close(other) })?;
        }

        Ok(unsafe { File::from_raw_fd(original) })
    }

    fn set_stdio(stdio: RawFd, other: RawFd) -> io::Result<()> {
        io_res(unsafe { libc::dup2(other, stdio) })?;
        Ok(())
    }

    fn io_res(res: c_int) -> io::Result<c_int> {
        if res == -1 {
            Err(io::Error::last_os_error())
        } else {
            Ok(res)
        }
    }

    pub struct MuteGuard {
        original_stdout: ManuallyDrop<File>,
        original_stderr: ManuallyDrop<File>,
    }

    impl MuteGuard {
        pub fn new() -> Self {
            Self {
                original_stdout: ManuallyDrop::new(
                    override_stdio(
                        STDOUT_FILENO,
                        File::open(Path::new("/dev/null")).unwrap().into_raw_fd(),
                        true,
                    )
                    .unwrap(),
                ),
                original_stderr: ManuallyDrop::new(
                    override_stdio(
                        STDERR_FILENO,
                        File::open(Path::new("/dev/null")).unwrap().into_raw_fd(),
                        true,
                    )
                    .unwrap(),
                ),
            }
        }
    }

    impl Drop for MuteGuard {
        fn drop(&mut self) {
            set_stdio(STDOUT_FILENO, self.original_stdout.as_raw_fd()).unwrap();
            set_stdio(STDERR_FILENO, self.original_stderr.as_raw_fd()).unwrap();
        }
    }
}

/// Redirects stdout to /dev/null temporarily.
///
/// Do not call this function if you are already within the scope of another call to it.
///
/// Only works on unix and if the mute feature is enabled.
pub fn mute<R>(cb: impl FnOnce() -> R) -> R {
    #[cfg(unix)]
    #[cfg(feature = "mute")]
    let guard = imp::MuteGuard::new();

    let r = cb();

    #[cfg(unix)]
    #[cfg(feature = "mute")]
    drop(guard);

    r
}
