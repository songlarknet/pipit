/** Low-level interface to CAN hardware
 * Based on MCP2515 SPI-controlled stand-alone CAN controller
 * Datasheet: https://ww1.microchip.com/downloads/en/DeviceDoc/MCP2515-Stand-Alone-CAN-Controller-with-SPI-20001801J.pdf
 */
#pragma once
#include <stdint.h>

typedef uint32_t can_id_t;

/**
 * ABTF  bit 6  aborted
 * MLOA  bit 5  message lost arbitration
 * TXERR bit 4 transmission error
 * TXREQ bit 3 transmission request pending
*/
typedef enum can_send_status {
  CAN_SEND_NONE,
  CAN_SEND_ABORTED,
  CAN_SEND_LOST_ARBITRARTION,
  CAN_SEND_ERROR,
  CAN_SEND_PENDING,
} can_send_status_t;

const uint8_t MESSAGE_MAX_LENGTH = 8;

typedef struct can_message {
  can_id_t can_id;
  uint8_t length;
  uint8_t bytes[MESSAGE_MAX_LENGTH];
} can_message_t;


typedef uint8_t can_tx_buf_id_t;
const can_tx_buf_id_t TXBUF0 = 0;

bool can_set_txbuf(can_tx_buf_id_t txbuf, can_message_t message);
can_send_status_t can_get_send_status(can_tx_buf_id_t txbuf);

void can_init();
void can_step();
