#pragma once

// App code calls this as the final stage of bootstrap after memory relocation
// and libc initialization complete.
[[noreturn]] void app_entrypoint();
