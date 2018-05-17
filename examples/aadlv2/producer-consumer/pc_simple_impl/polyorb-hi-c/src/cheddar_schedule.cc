/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2017 ESA & ISAE.
 */


// STL
#include <iostream>  // for std::cout
#include <memory>    // unique_ptr
#include <algorithm> // copy, equal
#include <iosfwd>
#include <iterator>
#include <array>



// Boost

#include <boost/graph/adjacency_list.hpp> 
#include "../../../include/monitoring/state_types.hh"
#include <deque>
#include <iterator>
#include <boost/graph/graphviz.hpp>
#include <boost/graph/adj_list_serialize.hpp>
#include <boost/graph/topological_sort.hpp>

#define hyperperiod 100

class state
{
state()
{
;
}
public:

//Graph elements definitions

  typedef boost::adjacency_list< boost::vecS, boost::vecS, boost::bidirectionalS, VertexProperty > Cheddar_graph;

  using array_type_VertexProperty = std::array<VertexProperty,hyperperiod>;

  using array_type_VertexDescriptor = std::array< Cheddar_graph::vertex_descriptor,hyperperiod>;

private:

//Vertex property specification

  struct VertexProperty 
  {
    thread_event_type task_id;
    step_type local_step;
    step_type global_step;
  };

//Graph elements declarations

  unsigned int hyperperiod_;
  Cheddar_graph cheddar_g_;
  array_type_VertexProperty vertexProperties_;
  array_type_VertexDescriptor vertexDescriptors_;


public:

//Graph building functions
  void 
  set_hyperperiod(int nb_steps)
  {
    hyperperiod_ = nb_steps;
  }

  void 
  add_vertex(int vertex_id, int task, int local_step, int global_step)
  {
    vertexProperties_[vertex_id].task_id = task;
    vertexProperties_[vertex_id].local_step = local_step;
    vertexProperties_[vertex_id].global_step = global_step;
    vertexDescriptors_[vertex_id] = boost::add_vertex(vertexProperties_[vertex_id],cheddar_g_);
  }

  void 
  add_edge(int vertex_id_1,int vertex_id_2)
  {
    add_edge(vertexDescriptors_[vertex_id_1], vertexDescriptors_[vertex_id_2], cheddar_g_);
  }

  void 
  print_graph_debug()
  {
    write_graphviz(std::cout, cheddar_g_);
  }

  void
  serialize_graph()
  {
    
  }
  
  void
  unserialize_graph()
  {

  }

};

  
