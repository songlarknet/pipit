#include "arith.h"
#include "router.h"

#include <memory.h>

static net_message_id_t router_get_send_schedule(router_state_t* router_state, uint32_t time_ticks) {
  net_message_id_t msg = NET_MSG_NONE;
  // naive but mostly constant time
  for (uint32_t send_index = 0; send_index != router_state->send_requests_count; ++send_index) {
    net_message_id_t msg_id = router_state->send_requests[send_index].message_id;

    assert(net_config.messages[msg_id].sender == net_this_node);

    if (is_send_scheduled(msg_id, time_ticks))
      msg = msg_id;
  }
  return msg;
}

static void router_init_send_table(router_state_t *router_state) {
  uint32_t send_index = 0;
  for (uint32_t i = 0; i != NET_MSG_COUNT; ++i) {
    if (net_config.messages[i].sender == net_this_node) {
      router_state->message_config[i].send_table_index = send_index;
      router_state->send_requests[send_index].message_id = (net_message_id_t)i;
      router_state->send_requests[send_index].message.can_id = net_config.messages[i].can_id;
      send_index++;
    }
  }

  router_state->send_requests_count = send_index;
}

void router_init(router_state_t *router_state) {
  net_assert_config_ok();
  memset(router_state, 0, sizeof(*router_state));
  router_state->last_send = NET_MSG_NONE;

  router_init_send_table(router_state);
}

/** message priority (lower is more important) */
static uint32_t message_priority(net_message_id_t m) {
  return net_config.messages[m].can_id;
}


void router_step(router_state_t *router_state) {
  const uint32_t          now         = router_state->time_ticks;
  const net_message_id_t  last_send   = router_state->last_send;
  const bool              last_late   = router_state->last_late;

  net_message_id_t        sched       = router_get_send_schedule(router_state, now);
  if (sched != NET_MSG_NONE && !router_state->send_requests[sched].pending)
    sched = NET_MSG_NONE;

  const can_send_status_t send_status = can_get_send_status(TXBUF0);
  const bool              send_ok     = send_status != CAN_SEND_NONE;


  if (last_send != NET_MSG_NONE) {
    if (send_ok) {
      router_state->stats_total.send_count = sat_inc_u32(router_state->stats_total.send_count);
      router_state->stats_per_message[last_send].send_count = sat_inc_u32(router_state->stats_per_message[last_send].send_count);

    } else {
      if (!last_late) {
        router_state->stats_total.late_count = sat_inc_u32(router_state->stats_total.late_count);
        router_state->stats_per_message[last_send].late_count = sat_inc_u32(router_state->stats_per_message[last_send].late_count);
      }
      router_state->last_late = true;


      // the previous send failed, so check if it is preempted by the newly-scheduled message, or retry.
      // one of them must be dropped, we just need to decide which
      if (sched != NET_MSG_NONE) {
        router_state->stats_total.drop_count = sat_inc_u32(router_state->stats_total.drop_count);
        router_state->stats_per_message[last_send].drop_count = sat_inc_u32(router_state->stats_per_message[last_send].drop_count);

        if (message_priority(sched) > message_priority(last_send)) {
          // scheduled message is strictly lower priority, so ignore the scheduled message
          sched = NET_MSG_NONE;
        }
      }
    }
  }

  if (sched != NET_MSG_NONE) {
    can_set_txbuf(TXBUF0, router_state->send_requests[sched].message);
    router_state->send_requests[sched].pending = false;

    router_state->last_send = sched;
    router_state->last_late = false;
  }

  router_state->time_ticks = (router_state->time_ticks + 1) % net_config.common_period;
}

void router_enqueue_send(router_state_t *router_state, net_message_id_t id, can_message_t message) {
  assert(NET_VALID_MESSAGE_ID(id));
  assert(net_config.messages[id].sender == net_this_node);
  assert(message.can_id == net_config.messages[id].can_id);
  uint32_t send_index = router_state->message_config[id].send_table_index;

  router_state->send_requests[send_index].message = message;
  router_state->send_requests[send_index].pending = true;
}
