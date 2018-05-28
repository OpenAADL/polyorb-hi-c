#include <deployment.h>
#include <request.h>
#include <po_hi_time.h>

/**
 * \enum events.
 * \brief Nature of the task traced.
 */
typedef enum {
	PERIODIC = 1,
	SPORADIC = -1,
        ANY = 0,
} events;

/**
 * \enum steps.
 * \brief Step in which the traced-task is.
 */
typedef enum {
	/* The task has just been creatd */
	CREATION = 0,
	STORE_OUT = 1,
	TRANSPORT_SEND = 2,
	WAIT_FOR = 3,
	GET_VALUE = 4,
} steps;

/**
 * \struct characteristics.
 * \brief Structure stored when an event is recorded.
 */
typedef struct characteristics characteristics;

struct characteristics{
	events event;
	steps status;
	__po_hi_task_id task_id;
	__po_hi_port_t global_port_src;
	__po_hi_port_t global_port_dest;
	__po_hi_local_port_t loc_port_src;
	__po_hi_local_port_t loc_port_dest;
	__po_hi_time_t mytime;
	__po_hi_request_t *p_request;
};

/**
 * \brief Function initializing the mutex.
 */
void trace_initialize();

/**
 * \brief Function used to trace a task.
 * 
 * The stored events (under the form of "characteristics" structures) are sent in an array 
 * and written in the history.txt file.
 * 
 * WARNING.
 * If an operation is made without movement, that is to say with no source or destination (such as waiting for an event),
 * the concerned port is stored in the "src" port.
 * 
 * \param event The nature of the task.
 * \param status The step in which the task is.
 * \param task_id Identifier of the task.
 * \param p_src and p_dest, the GLOBAL source and destination ports if they exists / are retrievable.
 * \param port_src and port_dest, the LOCAL source and destination ports if they exists / are retrievable.
 * \param p_req a pointer toward the request if it exists and is retrievable.
 * 
 * \return __PO_HI_SUCCESS if successful.
 * \return __PO_HI_INVALID if there is an error with the txt file.
 * \return __PO_HI_UNAVAILABLE is the time isn't retrievable.
 */
int record_event
(int event, 
 int status, 
 __po_hi_task_id t_id,
 __po_hi_port_t p_src,
 __po_hi_port_t p_dest,
 __po_hi_local_port_t port_src,
 __po_hi_local_port_t port_dest,
 __po_hi_request_t *p_req);
