/*****************************************************/

/*  This file contains all function of TASTE RUNTIME */

/*  MONITORING API.                                  */

/*****************************************************/


void init_all();

void kill_all();

void th_register();

void callback();

void get_port(port_values state);

void set_port(port_values state);

void trigger_task(int th_id);

void tick();

void dump_trace();

//void undo();

//void redo();
