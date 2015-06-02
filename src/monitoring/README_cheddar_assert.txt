This document list the assertions that need to be checked before
using Cheddar for runtime monitoring purposes.

Those assertions have to be checked upon the AADL architecture model
(in addition with previously existing consistency checking).

-1- All tasks are either periodic or sporadic
-2- The scheduler is specified and within the following list:
	-Posix_1003_Highest_Priority_First_Protocol,
	-will be extended ?
-3- A priority is specified for each task
-4- A capacity > 0 (WCET) is specified for each task

