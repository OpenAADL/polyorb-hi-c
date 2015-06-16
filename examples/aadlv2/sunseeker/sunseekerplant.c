#include<stdio.h>

float plant_integrator = 0.0;
float plant_transfer_fcn = 0.0;

float plant_period = 0.01;

void user_sunseekerplant
  (float controller_input, float* outputfeedback)
{
        float feedback_error;
        float feedback;
        float integrator_output;
        float plant_output;
        float preamp_output;
        float transfer_fcn_update;

        printf ("PLANT INPUT: %f\n", controller_input);
        preamp_output = controller_input * (-2.0);
        integrator_output = plant_integrator;
        plant_output = 0.002 * plant_transfer_fcn;
        feedback = plant_output * 0.0125;

        *outputfeedback = integrator_output * 0.00125;
        plant_integrator = plant_integrator + 0.001 * plant_output;

        feedback_error = preamp_output - feedback;
        transfer_fcn_update = 1000000 * feedback_error;
        
        plant_transfer_fcn = plant_transfer_fcn + plant_period * transfer_fcn_update;

        printf ("PLANT OUTPUT: %f ERROR : %f\n", *outputfeedback, feedback_error);
}

