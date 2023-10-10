/** Platform-specific definitions: node and messages */
#pragma once

typedef enum net_node_id {
  NET_NODE_ABS = 0,
  NET_NODE_DASHCONTROL,
  NET_NODE_SUPERVISOR,
  NET_NODE_COUNT,
  NET_NODE_NONE = -1,
} net_node_id_t;

typedef enum net_message_id {
  NET_MSG_ABS_STATUS = 0,
  NET_MSG_ABS_DEBUG,
  NET_MSG_DASH_STATUS,
  NET_MSG_DASH_ABS_CMD,
  NET_MSG_DASH_DEBUG,
  NET_MSG_SUPERVISOR_STATUS,
  NET_MSG_COUNT,
  NET_MSG_NONE = -1,
} net_message_id_t;

const uint32_t NET_MAX_SEND_MSGS = 3;
const uint32_t NET_MAX_RECV_MSGS = 3;
