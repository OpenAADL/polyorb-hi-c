/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://www.openaadl.org
 *
 * Copyright (C) 2020 OpenAADL
 */

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
