#pragma once
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

#include "can_driver.h"
#include "platform_network.h"
#include "network.h"

#define VALID_MESSAGE_ID(id) ( 0 <= (id) && (id) < MSG_COUNT )

typedef struct router_stats {
  uint32_t late_count;
  uint32_t drop_count;
  uint32_t send_count;
  // uint32_t recv_count;
} router_stats_t;

typedef struct router_send_request {
  net_message_id_t message_id;

  bool pending;
  can_message_t message;
} router_send_request_t;

typedef struct router_message_config {
  uint32_t send_table_index;
  uint32_t recv_table_index;
} router_message_config_t;

typedef struct router_state {
  router_message_config_t message_config[NET_MSG_COUNT];

  uint32_t time_ticks;

  net_message_id_t last_send;
  bool last_late;

  router_send_request_t send_requests[NET_MAX_SEND_MSGS];
  uint32_t send_requests_count;
  // router_recv_t recv_requests[NET_MAX_RECV_MSGS];

  router_stats_t stats_per_message[NET_MSG_COUNT];
  router_stats_t stats_total;
} router_state_t;


void router_enqueue_send(router_state_t *state, net_message_id_t id, can_message_t message);

void router_init(router_state_t *state);
void router_step(router_state_t *state);

void assert_config_ok();
bool is_send_scheduled(net_message_id_t m, uint32_t time_ticks);
