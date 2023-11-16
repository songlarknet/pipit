#pragma once
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

#include "can_driver.h"
#include "platform_network.h"

#define NET_VALID_MESSAGE_ID(id) ( 0 <= (id) && (id) < NET_MSG_COUNT )

typedef struct net_message_config {
  can_id_t can_id;
  net_node_id_t sender;
  uint32_t period;
  uint32_t phase;
} net_message_config_t;

typedef struct net_node_config {
  bool subscribes_to[NET_MSG_COUNT];
} net_node_config_t;

typedef struct net_config {
  net_message_config_t messages[NET_MSG_COUNT];
  net_node_config_t nodes[NET_NODE_COUNT];
  uint32_t common_period;
} net_config_t;

extern net_config_t net_config;
extern net_node_id_t net_this_node;

void net_assert_config_ok();
bool net_is_send_scheduled(net_message_id_t m, uint32_t time_ticks);
