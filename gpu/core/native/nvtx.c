#include <nvtx3/nvToolsExt.h>
#include <stdint.h>

nvtxDomainHandle_t gpu_core_nvtx_domain_create(const char *name) { return nvtxDomainCreateA(name); }

nvtxStringHandle_t gpu_core_nvtx_register_string(nvtxDomainHandle_t domain, const char *string) { return nvtxDomainRegisterStringA(domain, string); }

uint64_t gpu_core_nvtx_domain_ascii_range_start(nvtxDomainHandle_t domain, const char *message) {
  nvtxEventAttributes_t event_attrib = {0};
  event_attrib.version = NVTX_VERSION;
  event_attrib.size = NVTX_EVENT_ATTRIB_STRUCT_SIZE;
  event_attrib.messageType = NVTX_MESSAGE_TYPE_ASCII;
  event_attrib.message.ascii = message;
  return nvtxDomainRangeStartEx(domain, &event_attrib);
}

uint64_t gpu_core_nvtx_registered_range_start(nvtxDomainHandle_t domain, nvtxStringHandle_t string) {
  nvtxEventAttributes_t event_attrib = {0};
  event_attrib.version = NVTX_VERSION;
  event_attrib.size = NVTX_EVENT_ATTRIB_STRUCT_SIZE;
  event_attrib.messageType = NVTX_MESSAGE_TYPE_REGISTERED;
  event_attrib.message.registered = string;
  return nvtxDomainRangeStartEx(domain, &event_attrib);
}

uint64_t gpu_core_nvtx_ascii_range_start(const char *message) { return nvtxRangeStartA(message); }

void gpu_core_nvtx_range_end(uint64_t id) { nvtxRangeEnd(id); }

uint64_t gpu_core_nvtx_registered_range_start_with_payload(nvtxDomainHandle_t domain, nvtxStringHandle_t string, uint64_t payload) {
  nvtxEventAttributes_t event_attrib = {0};
  event_attrib.version = NVTX_VERSION;
  event_attrib.size = NVTX_EVENT_ATTRIB_STRUCT_SIZE;
  event_attrib.messageType = NVTX_MESSAGE_TYPE_REGISTERED;
  event_attrib.message.registered = string;
  event_attrib.payloadType = NVTX_PAYLOAD_TYPE_UNSIGNED_INT64;
  event_attrib.payload.ullValue = payload;
  return nvtxDomainRangeStartEx(domain, &event_attrib);
}

void gpu_core_nvtx_domain_range_end(nvtxDomainHandle_t domain, uint64_t id) { nvtxDomainRangeEnd(domain, id); }
