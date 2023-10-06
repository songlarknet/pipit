#include "arith.h"
#include "router.h"

#include <memory.h>

net_message_id_t router_get_send_schedule(uint32_t time_ticks) {
  net_message_id_t msg = NET_MSG_NONE;
  // naive but mostly constant time
  for (uint32_t i = 0; i != NET_MSG_COUNT; ++i) {
    if (net_config.messages[i].sender == net_this_node && is_send_scheduled((net_message_id_t)i, time_ticks))
      msg = (net_message_id_t)i;
  }
  return msg;
}

void router_init(router_state_t *router_state) {
  net_assert_config_ok();
  memset(router_state, 0, sizeof(*router_state));
  router_state->last_send = NET_MSG_NONE;
}

/** message priority (lower is more important) */
static uint32_t message_priority(net_message_id_t m) {
  return net_config.messages[m].can_id;
}


void router_step(router_state_t *router_state) {
  uint32_t          now         = router_state->time_ticks;
  net_message_id_t  last_send   = router_state->last_send;
  bool              last_late   = router_state->last_late;

  net_message_id_t  sched       = router_get_send_schedule(now);

  can_send_status_t send_status = can_get_send_status(TXBUF0);
  bool              send_ok     = send_status != SEND_NONE;

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
    }

    // if the previous send failed, then we check if it is preempted by the newly-scheduled message
    bool drop_old =
      !send_ok &&
      (last_send != NET_MSG_NONE) &&
      (sched != NET_MSG_NONE) &&
      (message_priority(sched) <= message_priority(last_send));

    if (drop_old) {
      router_state->stats_total.drop_count = sat_inc_u32(router_state->stats_total.drop_count);
      router_state->stats_per_message[last_send].drop_count = sat_inc_u32(router_state->stats_per_message[last_send].drop_count);

    }
  }



  // we take the new one if the previous one worked, or if dropping the old
  bool take_new =
    send_ok || drop_old;

  // 
  net_message_id_t new_send =
    take_new ? sched : last_send;

  bool requires_txbuf_set =
    (new_send != NET_MSG_NONE) && take_new;
    // (take_new || router_state->send_requests[new_send].pending);

  bool is_late =
    !take_new && (last_send != NET_MSG_NONE) && last_late;

  // PHASE 2: PERFORM ACTIONS
  if (requires_txbuf_set) {
    can_set_txbuf(TXBUF0, router_state->send_requests[new_send].message);
    router_state->send_requests[new_send].pending = false;
  }


  uint32_t latency =
    take_new
    ? 0
    : sat_inc_u32(router_state.stats_total.send_latency_current);

  router_state.stats_total.send_latency_current = latency;
  router_state.stats_total.send_latency_max =
    latency > router_state.stats_total.send_latency_max
    ? latency
    : router_state.stats_total.send_latency_max;


  // PHASE 4: FINISH
  router_state->time_ticks = (router_state->time_ticks + 1) % net_config.common_period;
}

void router_enqueue_send(message_id_t id, message_t message) {
  assert(VALID_MESSAGE_ID(id));
  assert(network_config.messages[id].sender == router_state.this_node);
  assert(message.id == network_config.messages[id].id);

  // update drops and latency
  router_state.stats_per_message[id].send_latency_current = 0;
  if (router_state.send_requests[id].pending) {
    router_state.stats_per_message[id].send_drop_count = sat_inc_u32(router_state.stats_per_message[id].send_drop_count);
    router_state.stats_total.send_drop_count = sat_inc_u32(router_state.stats_total.send_drop_count);
  }
  if (router_state.try_send == id) {
    router_state.stats_total.send_latency_current = 0;
  }

  router_state.send_requests[id].message = message;
  router_state.send_requests[id].pending = true;
}
