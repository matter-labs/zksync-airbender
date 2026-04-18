#include <stdint.h>
#include <nvtx3/nvToolsExt.h>

nvtxDomainHandle_t gpu_prover_nvtx_domain_create(const char *name) {
    return nvtxDomainCreateA(name);
}

nvtxStringHandle_t gpu_prover_nvtx_register_string(
    nvtxDomainHandle_t domain,
    const char *string
) {
    return nvtxDomainRegisterStringA(domain, string);
}

uint64_t gpu_prover_nvtx_domain_ascii_range_start(
    nvtxDomainHandle_t domain,
    const char *message
) {
    nvtxEventAttributes_t event_attrib = {0};
    event_attrib.version = NVTX_VERSION;
    event_attrib.size = NVTX_EVENT_ATTRIB_STRUCT_SIZE;
    event_attrib.messageType = NVTX_MESSAGE_TYPE_ASCII;
    event_attrib.message.ascii = message;
    return nvtxDomainRangeStartEx(domain, &event_attrib);
}

uint64_t gpu_prover_nvtx_registered_range_start(
    nvtxDomainHandle_t domain,
    nvtxStringHandle_t string
) {
    nvtxEventAttributes_t event_attrib = {0};
    event_attrib.version = NVTX_VERSION;
    event_attrib.size = NVTX_EVENT_ATTRIB_STRUCT_SIZE;
    event_attrib.messageType = NVTX_MESSAGE_TYPE_REGISTERED;
    event_attrib.message.registered = string;
    return nvtxDomainRangeStartEx(domain, &event_attrib);
}

uint64_t gpu_prover_nvtx_ascii_range_start(const char *message) {
    return nvtxRangeStartA(message);
}

void gpu_prover_nvtx_range_end(uint64_t id) {
    nvtxRangeEnd(id);
}
