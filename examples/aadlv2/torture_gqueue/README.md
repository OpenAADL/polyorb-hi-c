# torture.c

## About

This file allows the user to test the functions of the gqueue.
The functions directly tested are listed below :

__po_hi_gqueue_store_out,
__po_hi_gqueue_send_output,
__po_hi_gqueue_get_value,
__po_hi_gqueue_next_value,
__po_hi_gqueue_get_count,
__po_hi_gqueue_wait_for_incoming_event.

The functions directly tested are listed below :
__po_hi_gqueue_store_in.

## Global details

The boolean init is used to initialize the semaphores used in the
test, at the first awakening of the periodic function (first to awaken
between the two tasks).

The boolean first_iteration is used to coordinate the awakening of the
two tasks.

In fact, after the first awakening of the periodic function, we go
through the first five tests. However something is needed to indicate
we switch to the next battery of test.  That is the role of the
"number" integer and the first_iteration boolean.  When the value of
"number" is of 1, the first 5 tests are conducted (with one message at
each awakening).  When the value of "number" switches from 1 to 2, the
periodic test 1 is triggered (two messages).

## Sporadic Test details

Each time messages are sent by the periodic task and received by the
Sporadic Task.

The Per Port 1 is linked to the Spo Port 2.
The Per Port 2 is linked to the Spo Port 1.

From the Sporadic 1 to the Sporadic 5:
- tests are made with only one message sent on a output port to an
  event port (each time the periodic task is triggered).
- the tests are following each other.

Test Sporadic 1 :
A message has been sent and therefore, a message should be found on each port.
The get_count function is tested by verifying its value on each port is 1.

Test Sporadic 2 :
The goal is to verify :

- whether the wait_for_incoming_event function shows the events in the
  right chronological order (FIFO behavior of the function awaited).
- whether the next_value function dequeues correctly the events stored
  on each port.

Secondly, to verify :

- whether the value obtained from the get_value function is correct,
  compared to the sent values.

As the first message sent was from Port P1 to Port P2, we at first
verify that the first port indicated by the wait_for_next_event
function is the port P2.  Then the value sent and obtained thanks to
the get_value function are compared.  Finally we verify that after the
dequeue, the get_count functions shows empty ports.  At this point,
both ports are empty.

Test Sporadic 3 :

The goal is to verify whether the get_value function (thanks to
semaphores) waits correctly when the port is empty.  The test is done
on an empty port.  We verify that, when the lock is released, it is
only because both ports are now full : the Periodic task has been
triggered, releasing the get_value function.

Test Sporadic 4 and 5 :

These tests are used to verify this time the FIFO behavior of the
get_value function.  The first lines roles are to establish the
optimal set up for the test (2 values on one port, and 1 value only on
the other).  We verify thanks to the following assertion that the
value first obtained on the port with 2 events is not the value just
sent, but the previous one (inferior by 1).  assert (reception !=
sent_level ); assert (reception == sent_level - 1); The other port
constitutes a control assay.

## Periodic Test details

Each time messages are sent by the periodic task and received by itself.

The Per Port P3 is linked to the Per Port P4.
The Per Port P5 is linked to the Per Port P6.

Test Periodic 1 :

This time, two messages are sent on the port P3 towards port P4 of the
periodic task : the task are sending messages to itself.

The goal is to verify:
 - whether the send_output (or transport_send) function works correctly.
- whether the FIFO behavior is maintained if two messages are sent in
  only one awakening of the task.

The awaited behavior of the store_out function is to crush the value
stored out if no send_output is done, which we have been able to see
in the past.  We verify that the duo store_out/send_output works fine
when called one after each other.

Finally we verify whether the two functions are recovered in the right
chronological order (the little value and the incremented one next).

The assertion to verify that is quite complex because only the last
value has been stored thanks to sent_lvl.  However, as the
incrementation is of 1 at each awakening, it is easy to recover the
previous value sent thanks to the assertion : reception == sent_lvl -
number + j + 1.  The value is then dequeued to get to the following
value.

Test Periodic 2 :

This time two messages are as well sent to the periodic task to itself.

The goal is to verify whether, if the queue is full, an error message is well sent.
We set up a reception port with a size of 1 and we sent 2 messages to this port.

If a message is printed, then the test is passed.
The user is able to see it itself on the console.
