import threading
import time

#Python module generated from runtime and example specific code using swig 
import po_hi_gqueue

#Class used to run example in background
class ThreadingExample(object):

    def __init__(self, interval=1):
        self.interval = interval

        thread = threading.Thread(target=self.run, args=())
        thread.daemon = True                            # Daemonize thread
        thread.start()                                  # Start the execution

    def run(self):
        po_hi_gqueue.demo_init()

#Factory class to create example specific request taking a value in parameter
class RequestFactory(object):

    def __init__(self):
        pass

    def consumer_global_data_sink_request_init(self, value):
        request = po_hi_gqueue._po_hi_request_t()
        request.port=po_hi_gqueue.pc_consumer_k
        request.vars= po_hi_gqueue._po_hi_request_t_vars_consumer_global_data_sink()
        request.vars.consumer_global_data_sink.consumer_global_data_sink = value
        return request

    def producer_global_data_source_request_init(self, value):
        request = po_hi_gqueue._po_hi_request_t()
        request.port=po_hi_gqueue.pc_producer_k
        request.vars= po_hi_gqueue._po_hi_request_t_vars_producer_global_data_source()
        request.vars.producer_global_data_source.producer_global_data_source = value
        return request

#Creating and starting thread running example
example = ThreadingExample()

#Instanciating request factory
reqfac = RequestFactory()

#Waiting a few job executions
time.sleep(2)

#Calling a po_hi_gqueue function to set an in port value
po_hi_gqueue.__po_hi_gqueue_store_in (po_hi_gqueue.pc_consumer_k, po_hi_gqueue.consumer_local_data_sink, reqfac.consumer_global_data_sink_request_init(40))

#Waiting a few job executions
time.sleep(2)

#Calling a po_hi_gqueue function to set an in port value
po_hi_gqueue.__po_hi_gqueue_store_in (po_hi_gqueue.pc_consumer_k, po_hi_gqueue.consumer_local_data_sink, reqfac.consumer_global_data_sink_request_init(200))

#Waiting a few job executions
time.sleep(2)

#Calling a po_hi_gqueue function to set an out port value
print 'Manual production of a value on an out port : 1000'
po_hi_gqueue.__po_hi_gqueue_store_out (po_hi_gqueue.pc_producer_k, po_hi_gqueue.producer_local_data_source, reqfac.producer_global_data_source_request_init(1000))
res = po_hi_gqueue.__po_hi_gqueue_send_output (po_hi_gqueue.pc_producer_k, po_hi_gqueue.producer_global_data_source)

time.sleep(5)
po_hi_gqueue.__po_hi_tasks_killall();
print 'All tasks are killed manually'

print('End of Example')
