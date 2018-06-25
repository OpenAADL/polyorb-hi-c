#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <fcntl.h>           /* For O_* constants */
#include <sys/stat.h>        /* For mode constants */
#include <semaphore.h>
#include <string.h>
#include <stdbool.h>

/* Files generated from AADL model */
#include <request.h>
#include <deployment.h>

#include <po_hi_transport.h>
#include <po_hi_gqueue.h>

/*****************************************************************************/
/* Helper macros to access AADL entities                                     */

#define LOCAL_PORT(THREAD_INSTANCE_NAME, PORT_NAME) THREAD_INSTANCE_NAME ## _local_ ## PORT_NAME
#define REQUEST_PORT(THREAD_INSTANCE_NAME, PORT_NAME) THREAD_INSTANCE_NAME ## _global_ ## PORT_NAME
#define PORT_VARIABLE(THREAD_INSTANCE_NAME, PORT_NAME) vars.REQUEST_PORT(THREAD_INSTANCE_NAME,PORT_NAME).REQUEST_PORT(THREAD_INSTANCE_NAME,PORT_NAME)

#define MACRO_TEST 42
#define MACRO_TEST_SECOND 33
#define MAX_TEST 0

int lvl = MACRO_TEST;
int sent_lvl;

int level = MACRO_TEST_SECOND;
int sent_level;

void test_sporad_1(__po_hi_task_id self);
void test_sporad_2(__po_hi_task_id self);
void test_sporad_3(__po_hi_task_id self);
void test_sporad_4(__po_hi_task_id self);
void test_sporad_5(__po_hi_task_id self);

bool init = true;
bool first_iteration = true;
int number = 0;

int count_p1;
int count_p2;
int count_p4;
int count_p5;
int count_p6;

__po_hi_local_port_t port_p1 = LOCAL_PORT (spo_thread,p1);
__po_hi_local_port_t port_p2 = LOCAL_PORT (spo_thread,p2);
__po_hi_local_port_t port_p4 = LOCAL_PORT (per_thread,p4);
__po_hi_local_port_t port_p3 = LOCAL_PORT (per_thread,p3);
__po_hi_local_port_t port_p5 = LOCAL_PORT (per_thread,p5);
__po_hi_local_port_t port_p6 = LOCAL_PORT (per_thread,p6);

/*
 * Semaphore used to coordinate the period and sporad tasks : At the
 * end of the first battery of test (number of message == 1), a
 * sem_post is done which liberates a sem_wait.  The number of
 * messages is increased by one.
 */
sem_t *semaphore;

/*****************************************************************************/
void period(__po_hi_task_id self) {
  int i, j;

  if (init == true){
    semaphore = sem_open("/aadl", O_CREAT|O_EXCL, S_IRUSR | S_IWUSR, 1);
    if (semaphore == NULL) {
      sem_unlink ("/aadl");
      semaphore = sem_open("/aadl", O_CREAT|O_EXCL, S_IRUSR | S_IWUSR, 1);
    }
    init = false;
  }

  /* *** Boolean and semaphore launching the following test with
     *** "number" iterations *** */
  if (first_iteration){
    sem_wait(semaphore);
    printf("\n**** Starting Tests **** \n");
    first_iteration = false;
    number++;
  }

  __po_hi_request_t r1;
  __po_hi_request_t r2;

/*****************************************************************************/
  /* *** Initial Test of the different functions *** */
  /* *** Test of gqueue with one message *** */
  if (number < 2){
    /* Message sent on Period Port 1 to Sporad port 2 */
    sent_lvl = lvl;
    r1.port = REQUEST_PORT (per_thread, p1);
    r1.PORT_VARIABLE (per_thread,p1) = lvl;
    lvl++;

#if defined (TEST_VERBOSE)
    printf("\n Storeout P1 to P2, task id = %d, port id = %d", self, LOCAL_PORT (per_thread, p1));
#endif

    __po_hi_gqueue_store_out
      (self,
       LOCAL_PORT (per_thread, p1),
       &r1);

    /* Message sent on Period Port 2 to Sporad Port 1 */
    sent_level = level;
    r2.port = REQUEST_PORT (per_thread, p2);
    r2.PORT_VARIABLE (per_thread,p2) = level;
    level++;
#if defined (TEST_VERBOSE)
    printf("\n Storeout P2 to P1, task id = %d, port id = %d\n",
           self, LOCAL_PORT (per_thread, p2));
#endif
    __po_hi_gqueue_store_out
      (self,
       LOCAL_PORT (per_thread, p2),
       &r2);
  }

/*****************************************************************************/
  /* *** Test of two messages sent on one port *** */
  /* Transmission */
  count_p4 = __po_hi_gqueue_get_count(self, port_p4);
  if ((number == 2)&&(count_p4 == 0)){
    printf("\n*** TEST PERIODIC 1 ***\n");
    count_p4 = __po_hi_gqueue_get_count(self, port_p4);
    assert (count_p4 == 0);
    for (i = 1; i <= number; i++){
      sent_lvl = lvl;
      r1.port = REQUEST_PORT (per_thread, p3);
      r1.PORT_VARIABLE (per_thread,p3) = lvl;
      lvl++;
#if defined (TEST_VERBOSE)
      printf("\n Storeout P1 to P2, task id = %d, port id = %d", self, LOCAL_PORT (per_thread, p3));
#endif
      __po_hi_gqueue_store_out
        (self,
         LOCAL_PORT (per_thread, p3),
         &r1);
      __po_hi_send_output (self,REQUEST_PORT(per_thread, p3));
    }
    assert (count_p4 == 0);
  }
  /* Reception */
  count_p4 = __po_hi_gqueue_get_count(self, port_p4);
  if ((number == 2)&&(count_p4 == number)){
    __po_hi_request_t request;
    int reception;
    count_p4 = __po_hi_gqueue_get_count(self, port_p4);
    for (j = 0; j < count_p4; j++) {
    __po_hi_gqueue_get_value(self,port_p4,&(request));
    reception = request.PORT_VARIABLE(per_thread,p4);
#if defined (TEST_VERBOSE)
    printf("\nfirst request = %d", MACRO_TEST);
    printf("\nsent_lvl = %d", sent_lvl);
    printf("\nreceived = %d", reception);
    printf("\nnumber, j = %d %d\n", number, j);
#endif
    assert(reception == sent_lvl - number + j + 1);
    __po_hi_gqueue_next_value (self,port_p4);
   }
   printf ("Two Messages test passed\n");
    first_iteration = true;
    sem_post(semaphore);
  }

/*****************************************************************************/
   /* *** Test of gqueue error message *** */
   /* Transmission */

  count_p6 = __po_hi_gqueue_get_count(self, port_p6);
  if ((number == 3 )&&(count_p6 == 0)){

   printf("\n\n*** TEST PERIODIC 2 ***\n");
   count_p6 = __po_hi_gqueue_get_count(self, port_p6);
   assert (count_p6 == 0);
   for (int i = 1; i < number ; i++){
      sent_lvl = lvl;
      r1.port = REQUEST_PORT (per_thread, p5);
      r1.PORT_VARIABLE (per_thread,p5) = lvl;
      lvl++;
#if defined (TEST_VERBOSE)
      printf("\n Storeout P1 to P2, task id = %d, port id = %d", self, LOCAL_PORT (per_thread, p5));
#endif
      __po_hi_gqueue_store_out
        (self,
         LOCAL_PORT (per_thread, p5),
         &r1);
      __po_hi_send_output (self,REQUEST_PORT(per_thread, p5));
    }
  }
  /* Reception */

  count_p6 = __po_hi_gqueue_get_count(self, port_p6);
  if ((number == 3)&&(count_p6 == 1)){
    printf ("\n*** An error message should appear *** \n\n");
    count_p6 = __po_hi_gqueue_get_count(self, port_p6);
    for (int j = 0; j < count_p6; j++) {
    __po_hi_gqueue_next_value (self,port_p6);
    }
     printf ("\n*** If so, error message test passed *** \n\n");
    first_iteration = true;
    sem_post(semaphore);
  }

  if (number > 3){
          sem_unlink("/aadl");
          sem_close(semaphore);
          exit(0);
  }
}


/*****************************************************************************/
void sporad(__po_hi_task_id self) {
  /* Test with one message sent by the Period task */
  if (number == 1){
    /* Test of the get_count function */
    test_sporad_1 (self);
    /* Test of the next_value function */
    test_sporad_2 (self);
    /* Test of the function get_value on an empty port */
    test_sporad_3 (self);
    /* FIFO test on reception port P1 */
    test_sporad_4 (self);
    /* FIFO test on reception port P2 */
    test_sporad_5 (self);
  }

  /* Boolean and semaphore launching the next type of test */
  first_iteration = true;
  sem_post(semaphore);
}

/*****************************************************************************/
void test_sporad_1(__po_hi_task_id self) {
  printf ("\n*** TEST SPORADIC 1 ***\n");
  /*After reception the size used must be 1 */
  count_p1 = __po_hi_gqueue_get_count(self, port_p1);
  count_p2 = __po_hi_gqueue_get_count(self, port_p2);
  assert (count_p1 == 1);
  assert (count_p2 == 1);
  printf ("get_count test passed\n");
}

/*****************************************************************************/
void test_sporad_2(__po_hi_task_id self) {
  int i, reception;
  __po_hi_request_t request;
  __po_hi_local_port_t tryport;
  printf ("\n*** TEST SPORADIC 2 ***\n");
  count_p1 = __po_hi_gqueue_get_count(self, port_p1);
  count_p2 = __po_hi_gqueue_get_count(self, port_p2);
  assert (count_p1 == 1);
  assert (count_p2 == 1);
  /* All values are dequeued */
  for (i = 0; i < count_p1 + count_p2 ; i++) {
    __po_hi_gqueue_wait_for_incoming_event(self, &tryport);
    if (i == 0){
      /* The sending is done first on port p1 to port p1 */
      assert(tryport == port_p2);
      printf ("wait_for_incoming_event test passed \n");
    }
    __po_hi_gqueue_get_value(self,tryport,&(request));
    if (tryport == port_p1){
      reception = request.PORT_VARIABLE(spo_thread,p1);
      assert (reception == sent_level);
      printf ("get_value first test passed \n");
    }
    if (tryport == port_p2){
      reception = request.PORT_VARIABLE(spo_thread,p2);
      assert (reception == sent_lvl);
      printf ("get_value first test passed \n");
    }
    __po_hi_gqueue_next_value (self, tryport);
  }
  /* The ports are supposedly all empty */
  count_p1 = __po_hi_gqueue_get_count(self, port_p1);
  count_p2 = __po_hi_gqueue_get_count(self, port_p2);
  assert (count_p1 == 0);
  assert (count_p2 == 0);
  printf ("next_value test passed\n");
}

/*****************************************************************************/
void test_sporad_3(__po_hi_task_id self) {
  printf ("\n*** TEST SPORADIC 3 ***\n");
  __po_hi_request_t request;

  /* Test of Get_value on an empty port: */
  /* The function supposedly blocks the thread until something is received: */
  __po_hi_gqueue_get_value(self,port_p2,&(request));

  /* Values have been received on each port*/
  count_p1 = __po_hi_gqueue_get_count(self, port_p1);
  count_p2 = __po_hi_gqueue_get_count(self, port_p2);
  assert (count_p1 == 1);
  assert (count_p2 == 1);
  printf ("get_value second test passed \n");
}
/*****************************************************************************/
void test_sporad_4(__po_hi_task_id self) {
  int reception;
  __po_hi_request_t request;

  printf ("\n*** TEST SPORADIC 4 ***\n");
  count_p1 = __po_hi_gqueue_get_count(self, port_p1);
  count_p2 = __po_hi_gqueue_get_count(self, port_p2);
  assert (count_p1 == 1);
  assert (count_p2 == 1);

  /* Dequeuing port P2 */
  __po_hi_gqueue_get_value(self,port_p2,&(request));
  __po_hi_gqueue_next_value (self, port_p2);

  count_p1 = __po_hi_gqueue_get_count(self, port_p1);
  count_p2 = __po_hi_gqueue_get_count(self, port_p2);

  assert (count_p1 == 1);
  assert (count_p2 == 0);

  /* Blocking on port P2 */
  __po_hi_gqueue_get_value(self,port_p2,&(request));

  /* Reception */

  count_p1 = __po_hi_gqueue_get_count(self, port_p1);
  count_p2 = __po_hi_gqueue_get_count(self, port_p2);
  assert (count_p1 == 2);
  assert (count_p2 == 1);
  /* We have attained optimal configuration */

  /* No issue on port P2 */
  __po_hi_gqueue_get_value(self,port_p2,&(request));
  reception = request.PORT_VARIABLE(spo_thread,p2);

#if defined (TEST_VERBOSE)
  printf("\nfirst request = %d", MACRO_TEST);
  printf("\nsent_lvl = %d", sent_lvl);
  printf("\nreceived = %d", reception);
#endif
  assert (reception == sent_lvl);

  /* On port P1 : Due to the FIFO aspect of the gqueue, the value
     received is not the one just sent, but the previous one */
  __po_hi_gqueue_get_value(self,port_p1,&(request));
  reception = request.PORT_VARIABLE(spo_thread,p1);

#if defined (TEST_VERBOSE)
  printf("\nfirst request = %d", MACRO_TEST_SECOND);
  printf("\nsent_level = %d", sent_level);
  printf("\nreceived = %d", reception);
#endif

  assert (reception != sent_level );
  assert (reception == sent_level - 1);

  /* We ensure to have only one value on each port */
  __po_hi_gqueue_next_value (self,port_p1);

  count_p1 = __po_hi_gqueue_get_count(self, port_p1);
  count_p2 = __po_hi_gqueue_get_count(self, port_p2);
  assert (count_p1 == 1);
  assert (count_p2 == 1);

  printf ("FIFO test on port p1 passed \n");

}

/*****************************************************************************/
void test_sporad_5(__po_hi_task_id self) {

  int i, j, reception;
  __po_hi_request_t request;

  printf ("\n*** TEST SPORADIC 5 ****\n");
  count_p1 = __po_hi_gqueue_get_count(self, port_p1);
  count_p2 = __po_hi_gqueue_get_count(self, port_p2);
  assert (count_p1 == 1);
  assert (count_p2 == 1);

  /* Dequeuing port P1  */
  __po_hi_gqueue_get_value(self,port_p1,&(request));
  __po_hi_gqueue_next_value (self, port_p1);

  count_p1 = __po_hi_gqueue_get_count(self, port_p1);
  count_p2 = __po_hi_gqueue_get_count(self, port_p2);

  assert (count_p1 == 0);
  assert (count_p2 == 1);

  /* Blocking on port P1 */
  __po_hi_gqueue_get_value(self,port_p1,&(request));
  count_p1 = __po_hi_gqueue_get_count(self, port_p1);
  count_p2 = __po_hi_gqueue_get_count(self, port_p2);
  assert (count_p1 == 1);
  assert (count_p2 == 2);

  /* On port p2 : Due to the FIFO aspect of the gqueue, the value
     received is not the one just sent, but the previous one */
  __po_hi_gqueue_get_value(self,port_p2,&(request));
  reception = request.PORT_VARIABLE(spo_thread,p2);

#if defined (TEST_VERBOSE)
  printf("\nfirst request = %d", MACRO_TEST);
  printf("\nsent_lvl = %d", sent_lvl);
  printf("\nreceived = %d", reception);
#endif

  assert (reception != sent_lvl);
  assert (reception == sent_lvl - 1);

  /* No issue on port P1 */
  __po_hi_gqueue_get_value(self,port_p1,&(request));
  reception = request.PORT_VARIABLE(spo_thread,p1);

#if defined (TEST_VERBOSE)
  printf("\nfirst request = %d", MACRO_TEST_SECOND);
  printf("\nsent_level = %d", sent_level);
  printf("\nreceived = %d", reception);
#endif

  assert (reception == sent_level);
  __po_hi_gqueue_next_value (self,port_p2);

  count_p1 = __po_hi_gqueue_get_count(self, port_p1);
  count_p2 = __po_hi_gqueue_get_count(self, port_p2);
  assert (count_p1 == 1);
  assert (count_p2 == 1);

  for (i = 0; i < count_p1; i++) {
    __po_hi_gqueue_next_value (self,port_p1);
  }
  for (j = 0; j < count_p2; j++) {
    __po_hi_gqueue_next_value (self,port_p2);
  }

  count_p1 = __po_hi_gqueue_get_count(self, port_p1);
  count_p2 = __po_hi_gqueue_get_count(self, port_p2);
  assert (count_p1 == 0);
  assert (count_p2 == 0);

  printf ("FIFO test on port p2 passed\n");
}
