#include <stdio.h>
#include <request.h>
#include <deployment.h>
#include <po_hi_gqueue.h>

int job = 0;

void on_req(__po_hi_task_id self)
{
        __po_hi_request_t request;
        request.port = landing_gear_global_dummy_out;
        printf("=== Starting gear op ===\n");
        __po_hi_gqueue_store_out(self,landing_gear_local_dummy_out,&request);
}

void on_dummy(__po_hi_task_id self)
{
        printf("=== Starting gear done ===\n");
}

void on_dummy_in(__po_hi_task_id self)
{
        __po_hi_request_t request;
        printf("=== Gear op done ===\n");
        __po_hi_gqueue_store_out(self,landing_gear_local_ack,&request);
}

void on_stall_warning (__po_hi_task_id self, int i)
{
        if (i==1)
        {
                printf("=== STALL ALARM %d ====\n", i);
        }
        else
        {
                printf("=== False Alert %d ====\n", i);
        }
}

void on_engine_failure(__po_hi_task_id self)
{
        printf("=== ENGINE FAILURE ALARM ===\n");
}

void on_gear_cmd(__po_hi_task_id self)
{
        __po_hi_request_t request;
        __po_hi_gqueue_store_out(self,hci_local_gear_req,&request);
}

void on_gear_ack(__po_hi_task_id self)
{
        printf("=== Gear Locked ===\n");
}

void on_operator (__po_hi_task_id self)
{
        __po_hi_request_t request;
        __po_hi_gqueue_store_out(self,operator_local_gear_cmd,&request);
}

void on_sensor_sim(__po_hi_task_id self)
{
        int cr_v = 0;
        int aoa_v = 4;
        __po_hi_request_t request1;
        __po_hi_request_t request2;

        job++;

        if ( (job%40) == 0 )
        {
                request1.vars.sensor_sim_global_aoa.sensor_sim_global_aoa = 41;
                request2.vars.sensor_sim_global_climb_rate.sensor_sim_global_climb_rate = 4;
                __po_hi_gqueue_store_out(self,sensor_sim_local_aoa,&request1);
                __po_hi_gqueue_store_out(self,sensor_sim_local_climb_rate,&request2);
                printf("=== Sensor Sim setting soft stall ===\n");
        }
        else
        {
                if ( (job%201) == 0 )
                {
                        request1.vars.sensor_sim_global_aoa.sensor_sim_global_aoa = 25;
                        request2.vars.sensor_sim_global_climb_rate.sensor_sim_global_climb_rate = 9;
                        __po_hi_gqueue_store_out(self,sensor_sim_local_aoa,&request1);
                        __po_hi_gqueue_store_out(self,sensor_sim_local_climb_rate,&request2);
                        printf("=== Sensor Sim setting hard stall ===\n");
                }
                else
                {
                        if ( (job%401) == 0 )
                        {
                                __po_hi_gqueue_store_out(self,sensor_sim_local_engine_failure,&request1);
                                printf("=== Sensor Sim raising engine failure ===\n");
                        }
                        else
                        {
                                request1.vars.sensor_sim_global_aoa.sensor_sim_global_aoa = aoa_v;
                                request2.vars.sensor_sim_global_climb_rate.sensor_sim_global_climb_rate = cr_v;
                                __po_hi_gqueue_store_out(self,sensor_sim_local_aoa,&request1);
                                __po_hi_gqueue_store_out(self,sensor_sim_local_climb_rate,&request2);
                        }
                }
        }
}

void on_stall_monitor(__po_hi_task_id self)
{
        int aoa_v;
        int cr_v;
        __po_hi_request_t request;

        __po_hi_gqueue_get_value(self,stall_monitor_local_aoa,&(request));
        aoa_v = request.vars.sensor_sim_global_aoa.sensor_sim_global_aoa;

        __po_hi_gqueue_get_value(self,stall_monitor_local_climb_rate,&(request));
        cr_v = request.vars.sensor_sim_global_climb_rate.sensor_sim_global_climb_rate;

        if (aoa_v > 40) 
        {
                request.vars.stall_monitor_global_stall_warn.stall_monitor_global_stall_warn = 2;
                __po_hi_gqueue_store_out(self,stall_monitor_local_stall_warn,&request);
        }
        else
        {
                if ((aoa_v > 22 ) && (cr_v < 10))
                {
                        request.vars.stall_monitor_global_stall_warn.stall_monitor_global_stall_warn = 2;
                        __po_hi_gqueue_store_out(self,stall_monitor_local_stall_warn,&request);
                }
        }
}
