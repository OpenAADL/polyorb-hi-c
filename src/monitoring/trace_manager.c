#include <trace_manager.h>

//#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <request.h>
//#include <pthread.h>
#include <deployment.h>
#include <string.h>


#include <po_hi_debug.h>
#include <po_hi_task.h>
#include <po_hi_protected.h>
#include <po_hi_gqueue.h>
#include <po_hi_returns.h>

#include <activity.h>
#include <request.h>

#define MAX_STRUCT 10

__po_hi_mutex_t      __po_hi_c_trace_mutex;

/* Array receiving all tasks */
characteristics task_log[MAX_STRUCT];
/* Integer allowing to move in the task_log array */
int nb_struct = 0;
/* Initializing the mutex in the main.c */
void trace_initialize(){
	__po_hi_mutex_init (&__po_hi_c_trace_mutex,__PO_HI_MUTEX_REGULAR, 0);	
}




/* Recording all events, trace_managing */
int record_event(int event, int stat, __po_hi_task_id t_id, __po_hi_port_t p_src, __po_hi_port_t p_dest, __po_hi_local_port_t port_src,__po_hi_local_port_t port_dest, __po_hi_request_t *p_req){
	/* CREATION OF STREAM */
        printf("IN PROGRAM");
	FILE *history = NULL;
	/* CREATION OF THE STRUCTURE TO BE SENT TO TASK_LOG */
	characteristics my_task;
	characteristics *p_my_task = &my_task;
	/* EVENT */
	events ev = event;
	p_my_task->event = ev;
	/* STATUS */
	steps step = stat;	
	p_my_task->status = step; 
	/* TASK ID */
	p_my_task->task_id = t_id;
	/* GLOBAL PORT SRC */
	p_my_task->global_port_src = p_src;
	/* GLOBAL PORT DEST */
	p_my_task->global_port_dest = p_dest;
	/* PORT LOCAL SRC */
	p_my_task->loc_port_src = port_src;
	/* PORT LOCAL DEST */
	p_my_task->loc_port_dest = port_dest;
	/* TIME */
	__po_hi_time_t time;
	int gettime = __po_hi_get_time (&time);
	if (gettime == __PO_HI_SUCCESS){
		p_my_task->mytime = time;
	}
	else{
		printf("Can't get the time, break");
		return __PO_HI_UNAVAILABLE;
	}
	/* REQUEST */
	p_my_task->p_request = malloc (sizeof(__po_hi_request_t));
	if (p_req != NULL){
		memcpy(p_my_task->p_request, p_req, sizeof(__po_hi_request_t));
	}
	
	/* LOCKING THE MUTEX */
	printf("lock");
	__po_hi_mutex_lock (&__po_hi_c_trace_mutex);
        printf("locked");

	/* IF the log array is complete */
	if (nb_struct >= 10){
		/* A stream is opened */
                printf("open");
		history = fopen("history.txt", "a+" );
                if (history == NULL){
			printf("no history file is opened or created");
			return __PO_HI_INVALID;
 		}
                printf("close");
		fseek(history, 0, SEEK_END);
		/* The copying is done */
		for (int i = 0; i < 10; i++){
			fprintf(history,"event = %d; age_status = %d; task_id = %d; port_src_id = %d; port_dest_id = %d; local_port_src_id = %d; dest_src_id = %d; time : sec = %d, nsec = %d", task_log[i].event, 				task_log[i].status, task_log[i].task_id, task_log[i].global_port_src, task_log[i].global_port_dest, task_log[i].loc_port_src, task_log[i].loc_port_dest, (task_log[i].mytime).sec,  (task_log[i].mytime).nsec);
			fprintf(history, ", request = ");
			fwrite(task_log[i].p_request,sizeof(__po_hi_request_t),1,history);
			fprintf(history, "\n");
		}
		/* The index is returned back to 0 */
		nb_struct = 0;
		/* The stream is closed */
		fclose(history);
	}

	/* If the log array isn't complete, write in it */
	if (nb_struct < 10){
		task_log[nb_struct] = my_task;
		nb_struct += 1;
	}

	/* UNLOCKING THE MUTEX */
	__po_hi_mutex_unlock (&__po_hi_c_trace_mutex);

	return __PO_HI_SUCCESS;
}


