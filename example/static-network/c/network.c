#include "network.h"

void net_assert_config_ok() {
  for (uint32_t i = 0; i != NET_MSG_COUNT; ++i) {
    assert(net_config.common_period % net_config.messages[i].period == 0);
    assert(net_config.messages[i].phase < net_config.messages[i].period);

    for (uint32_t j = i + 1; j != NET_MSG_COUNT; ++j) {
      assert(net_config.messages[i].can_id != net_config.messages[j].can_id);
      // TODO check if phases conflict
      assert(net_config.messages[i].phase != net_config.messages[j].phase);
    }
  }
}

bool net_is_send_scheduled(net_message_id_t m, uint32_t time_ticks) {
  return (time_ticks % net_config.messages[m].period == net_config.messages[m].phase);
}
