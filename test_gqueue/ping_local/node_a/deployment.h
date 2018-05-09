#ifndef __OCARINA_GENERATED_DEPLOYMENT_H_
#define __OCARINA_GENERATED_DEPLOYMENT_H_ 
#include <po_hi_types.h>
/*****************************************************/

/*  This file was automatically generated by Ocarina */

/*  Do NOT hand-modify this file, as your            */

/*  changes will be lost when you re-run Ocarina     */

/*****************************************************/

#define __PO_HI_MY_NODE node_a_k

#define __po_hi_pinger_nb_ports 1

#define __po_hi_ping_me_nb_ports 1

/*  For each node in the distributed application add an enumerator*/

typedef enum
{
  node_a_k = 0
} __po_hi_node_t;

typedef enum
{
  invalid_protocol = -1
} __po_hi_protocol_t;

/*  For each thread in the distributed application nodes, add an enumerator*/

typedef enum
{
  node_a_pinger_k_entity = 0,
  node_a_ping_me_k_entity = 1,
  invalid_entity = -1
} __po_hi_entity_t;

typedef enum
{
  node_a_pinger_k = 0,
  node_a_ping_me_k = 1,
  invalid_task_id = -1
} __po_hi_task_id;

typedef enum
{
  invalid_device_id = -1
} __po_hi_device_id;

typedef enum
{
  invalid_bus_id = -1
} __po_hi_bus_id;

#define __PO_HI_NB_TASKS 2

#define __PO_HI_TASKS_STACK 0

#define __PO_HI_NB_PROTECTED 0

#define __PO_HI_NB_NODES 1

#define __PO_HI_NB_ENTITIES 2

#define __PO_HI_NB_PORTS 2

typedef enum
{
  pinger_global_data_source = 0,
  ping_me_global_data_sink = 1,
  invalid_port_t = -1,
  constant_out_identifier = 3
} __po_hi_port_t;

typedef enum
{
  pinger_local_data_source = 0,
  ping_me_local_data_sink = 0,
  invalid_local_port_t = -1
} __po_hi_local_port_t;

#define __PO_HI_NB_DEVICES 0

#define __PO_HI_NB_BUSES 0

#define __PO_HI_NB_PROTOCOLS 0

#define __PO_HI_PORT_TYPE_CONTENT __po_hi_pinger_nb_ports, __po_hi_ping_me_nb_ports

#endif
