extern "C"{
void    add_edge(int vertex_id_1,int vertex_id_2);
void    add_vertex(int vertex_id, int task, int local_step, int global_step);
void    set_hyperperiod(unsigned int nb_steps);
void    print_graph_debug();
void    serialize_graph();
void    unserialize_graph();
}
