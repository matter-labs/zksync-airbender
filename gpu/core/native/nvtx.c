#include <nvtx3/nvToolsExt.h>
#include <nvtx3/nvToolsExtMem.h>
#include <nvtx3/nvToolsExtPayload.h>
#include <stddef.h>
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

// Pool-allocation event record; must mirror the field layout the schema below
// declares and the Rust caller of gpu_core_nvtx_mem_mark passes field by field.
typedef struct gpu_core_mem_event {
  uint64_t id;
  uint64_t address;
  uint64_t bytes;
  uint64_t pool_used_after;
  uint32_t placement;
  uint32_t pad;
} gpu_core_mem_event;

uint64_t gpu_core_nvtx_mem_schema_register(nvtxDomainHandle_t domain) {
  static const nvtxPayloadSchemaEntry_t entries[] = {
      {0, NVTX_PAYLOAD_ENTRY_TYPE_UINT64, "id", NULL, 0, offsetof(gpu_core_mem_event, id)},
      {0, NVTX_PAYLOAD_ENTRY_TYPE_ADDRESS, "address", NULL, 0, offsetof(gpu_core_mem_event, address)},
      {0, NVTX_PAYLOAD_ENTRY_TYPE_UINT64, "bytes", NULL, 0, offsetof(gpu_core_mem_event, bytes)},
      {0, NVTX_PAYLOAD_ENTRY_TYPE_UINT64, "pool_used_after", NULL, 0, offsetof(gpu_core_mem_event, pool_used_after)},
      {0, NVTX_PAYLOAD_ENTRY_TYPE_UINT32, "placement", NULL, 0, offsetof(gpu_core_mem_event, placement)},
  };
  nvtxPayloadSchemaAttr_t attr = {0};
  attr.fieldMask = NVTX_PAYLOAD_SCHEMA_ATTR_FIELD_NAME | NVTX_PAYLOAD_SCHEMA_ATTR_FIELD_TYPE | NVTX_PAYLOAD_SCHEMA_ATTR_FIELD_ENTRIES |
                   NVTX_PAYLOAD_SCHEMA_ATTR_FIELD_NUM_ENTRIES | NVTX_PAYLOAD_SCHEMA_ATTR_FIELD_STATIC_SIZE;
  attr.name = "ab.mem.event";
  attr.type = NVTX_PAYLOAD_SCHEMA_TYPE_STATIC;
  attr.entries = entries;
  attr.numEntries = sizeof(entries) / sizeof(entries[0]);
  attr.payloadStaticSize = sizeof(gpu_core_mem_event);
  return nvtxPayloadSchemaRegister(domain, &attr);
}

void gpu_core_nvtx_mem_mark(nvtxDomainHandle_t domain, uint64_t schema_id, nvtxStringHandle_t site, uint32_t category, uint64_t id, uint64_t address,
                            uint64_t bytes, uint64_t pool_used_after, uint32_t placement) {
  gpu_core_mem_event record = {id, address, bytes, pool_used_after, placement, 0};
  nvtxPayloadData_t payload_data[] = {{schema_id, sizeof(record), &record}};
  nvtxEventAttributes_t event_attrib = {0};
  event_attrib.version = NVTX_VERSION;
  event_attrib.size = NVTX_EVENT_ATTRIB_STRUCT_SIZE;
  event_attrib.messageType = NVTX_MESSAGE_TYPE_REGISTERED;
  event_attrib.message.registered = site;
  event_attrib.category = category;
  event_attrib.payload.ullValue = NVTX_POINTER_AS_PAYLOAD_ULLVALUE(payload_data);
  event_attrib.payloadType = NVTX_PAYLOAD_TYPE_EXT;
  event_attrib.reserved0 = 1;
  nvtxDomainMarkEx(domain, &event_attrib);
}

void *gpu_core_nvtx_mem_heap_register(nvtxDomainHandle_t domain, const void *ptr, size_t size, const char *name) {
  nvtxMemVirtualRangeDesc_t range = {size, ptr};
  nvtxMemHeapDesc_t desc = {0};
  desc.extCompatID = NVTX_EXT_COMPATID_MEM;
  desc.structSize = sizeof(desc);
  desc.usage = NVTX_MEM_HEAP_USAGE_TYPE_SUB_ALLOCATOR;
  desc.type = NVTX_MEM_TYPE_VIRTUAL_ADDRESS;
  desc.typeSpecificDescSize = sizeof(range);
  desc.typeSpecificDesc = &range;
  desc.messageType = NVTX_MESSAGE_TYPE_ASCII;
  desc.message.ascii = name;
  return nvtxMemHeapRegister(domain, &desc);
}

void gpu_core_nvtx_mem_region_register(nvtxDomainHandle_t domain, void *heap, const void *ptr, size_t size) {
  nvtxMemVirtualRangeDesc_t range = {size, ptr};
  nvtxMemRegionsRegisterBatch_t batch = {0};
  batch.extCompatID = NVTX_EXT_COMPATID_MEM;
  batch.structSize = sizeof(batch);
  batch.regionType = NVTX_MEM_TYPE_VIRTUAL_ADDRESS;
  batch.heap = (nvtxMemHeapHandle_t)heap;
  batch.regionCount = 1;
  batch.regionDescElementSize = sizeof(range);
  batch.regionDescElements = &range;
  batch.regionHandleElementsOut = NULL;
  nvtxMemRegionsRegister(domain, &batch);
}

void gpu_core_nvtx_mem_region_unregister(nvtxDomainHandle_t domain, const void *ptr) {
  nvtxMemRegionRef_t ref;
  ref.pointer = ptr;
  nvtxMemRegionsUnregisterBatch_t batch = {0};
  batch.extCompatID = NVTX_EXT_COMPATID_MEM;
  batch.structSize = sizeof(batch);
  batch.refType = NVTX_MEM_REGION_REF_TYPE_POINTER;
  batch.refCount = 1;
  batch.refElementSize = sizeof(ref);
  batch.refElements = &ref;
  nvtxMemRegionsUnregister(domain, &batch);
}

void gpu_core_nvtx_mem_heap_unregister(nvtxDomainHandle_t domain, void *heap) { nvtxMemHeapUnregister(domain, (nvtxMemHeapHandle_t)heap); }

uint64_t gpu_core_nvtx_mem_range_start(nvtxDomainHandle_t domain, uint64_t schema_id, nvtxStringHandle_t site, uint32_t category, uint64_t id, uint64_t address,
                                       uint64_t bytes, uint64_t pool_used_after, uint32_t placement) {
  gpu_core_mem_event record = {id, address, bytes, pool_used_after, placement, 0};
  nvtxPayloadData_t payload_data[] = {{schema_id, sizeof(record), &record}};
  nvtxEventAttributes_t event_attrib = {0};
  event_attrib.version = NVTX_VERSION;
  event_attrib.size = NVTX_EVENT_ATTRIB_STRUCT_SIZE;
  event_attrib.messageType = NVTX_MESSAGE_TYPE_REGISTERED;
  event_attrib.message.registered = site;
  event_attrib.category = category;
  event_attrib.payload.ullValue = NVTX_POINTER_AS_PAYLOAD_ULLVALUE(payload_data);
  event_attrib.payloadType = NVTX_PAYLOAD_TYPE_EXT;
  event_attrib.reserved0 = 1;
  return nvtxDomainRangeStartEx(domain, &event_attrib);
}

void gpu_core_nvtx_domain_range_end(nvtxDomainHandle_t domain, uint64_t id) { nvtxDomainRangeEnd(domain, id); }
