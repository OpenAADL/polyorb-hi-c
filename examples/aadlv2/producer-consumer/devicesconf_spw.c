#include <drivers/configuration/spacewire.h>

__po_hi_c_spacewire_conf_t pohidrv_device_a = {
  .devname = "/dev/grspw0",
  .nodeaddr = 1,
  .corefreq = 0,
  .clockdiv = 0,
  .use_router = FALSE,
  .remove_prot_id = FALSE,
  .rxblock = FALSE,
  .txblock = FALSE,
  .exist = {
    .corefreq = 0,
    .clockdiv = 0,
    .use_router = 0,
    .remove_prot_id = 0,
    .rxblock = 0,
            .txblock = 0
  }
};

__po_hi_c_spacewire_conf_t pohidrv_device_b = {
  .devname = "/dev/grspw1",
  .nodeaddr = 3,
  .corefreq = 0,
  .clockdiv = 0,
  .use_router = FALSE,
  .remove_prot_id = FALSE,
  .rxblock = FALSE,
  .txblock = FALSE,
  .exist = {
    .corefreq = 0,
    .clockdiv = 0,
    .use_router = 0,
    .remove_prot_id = 0,
    .rxblock = 0,
            .txblock = 0
  }
};
