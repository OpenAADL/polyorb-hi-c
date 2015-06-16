#include <stdio.h>

float controller_transfer = 0.0;
float reference_input = 0.0;

float clock = 0.0;
const float period = 0.01;

void user_sunseekercontroller
        (float* controllerinput,
         float outputfeedback)
{
        float error;
        float gain_error_1;
        float gain_error;
        float transfer_fcn_update;

        printf ("CONTROLLER INPUT %f\n", outputfeedback);

        if (clock < 1.0)
        {
                reference_input = 0.0;
        }
        else
        {
                reference_input = clock - 1.0;
        }

        error = reference_input - outputfeedback;

        gain_error_1 = error * 0.1;
        gain_error = gain_error_1 * (-10000.0);

        transfer_fcn_update = gain_error - 170.0 * controller_transfer;

        *controllerinput = 29.17 * controller_transfer + transfer_fcn_update;

        controller_transfer = controller_transfer + period * transfer_fcn_update;

        clock = clock + period;

        printf ("CONTROLLER OUTPUT %f\n", *controllerinput);
}

