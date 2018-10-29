// Copyright © Mapotempo, 2013-2018
//
// This file is part of Mapotempo.
//
// Mapotempo is free software. You can redistribute it and/or
// modify since you respect the terms of the GNU Affero General
// Public License as published by the Free Software Foundation,
// either version 3 of the License, or (at your option) any later version.
//
// Mapotempo is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the Licenses for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with Mapotempo. If not, see:
// <http://www.gnu.org/licenses/agpl.html>
//
namespace operations_research {

struct Link {
    TSPTWDataDT* data;
    RoutingModel::NodeIndex source;
    RoutingModel::NodeIndex destination;

    Link(TSPTWDataDT* data_, RoutingModel::NodeIndex source_, RoutingModel::NodeIndex destination_):
      data(data_), source(source_), destination(destination_){}
};

bool EvalDistance(const Link& i, const Link& j) {
  const int64 i_distance = i.data->Vehicles().at(0)->Distance(i.source, i.destination) +
                           i.data->Vehicles().at(0)->Time(i.source, i.destination) +
                           i.data->Vehicles().at(0)->Value(i.source, i.destination);
  const int64 j_distance = j.data->Vehicles().at(0)->Distance(j.source, j.destination) +
                           j.data->Vehicles().at(0)->Time(j.source, j.destination) +
                           j.data->Vehicles().at(0)->Value(j.source, j.destination);
  return i_distance < j_distance;
}

void CapacityFilter(const TSPTWDataDT &data, RoutingModel &routing, Solver *solver, Assignment *assignment) {
  int64 capacity_size = data.Vehicles().at(0)->capacity.size();
  const int size_problem = data.SizeProblem();
  RoutingModel::NodeIndex i(0);

  if (capacity_size > 0) {
    std::vector<int64> maximum_vehicle_capacities(capacity_size, 0);
    for (TSPTWDataDT::Vehicle* vehicle : data.Vehicles()) {
      for (int64 c_index = 0; c_index < capacity_size; ++c_index) {
        int64 v_capacity = vehicle->capacity[c_index];
        maximum_vehicle_capacities[c_index] = std::max(maximum_vehicle_capacities[c_index], v_capacity < 0 ? CUSTOM_MAX_INT : v_capacity);
      }
    }

    std::vector<std::vector<int64>> quantities;

    RoutingModel::NodeIndex k(0);
    for (int activity = 0; activity <= size_problem; ++activity) {
      std::vector<int64> node_quantities;
      for (int64 quantity: data.Quantities(k)) {
        node_quantities.push_back(quantity);
      }
      quantities.push_back(node_quantities);

      int32 alternative_size = data.AlternativeSize(activity);
      k += alternative_size;
    }

    for (int activity = 0; activity <= size_problem; ++activity) {
      int32 alternative_size = data.AlternativeSize(activity);
      RoutingModel::NodeIndex j(i+alternative_size);

      int64 priority = data.Priority(i);
      int64 exclusion_cost = data.ExclusionCost(i);

      for (int second_activity = activity + 1; second_activity <= size_problem; ++ second_activity) {
        int32 second_alternative_size = data.AlternativeSize(second_activity);

        int q = 0;
        do {
          if (quantities[activity][q] + quantities[second_activity][q] > maximum_vehicle_capacities[q] && maximum_vehicle_capacities[q] > 0) {
            q = capacity_size;
            RoutingModel::NodeIndex i_prime(i);
            RoutingModel::NodeIndex j_prime(j);

            IntVar *const active_var = routing.ActiveVar(activity);
            IntVar *const second_active_var = routing.ActiveVar(second_activity);

            IntVar *const vehicle_var = routing.VehicleVar(activity);
            IntVar *const second_vehicle_var = routing.VehicleVar(second_activity);

            for (int alternative = 0; alternative < alternative_size; ++alternative) {
              for(int second_alternative = 0; second_alternative < second_alternative_size; ++second_alternative) {
                int64 index = routing.NodeToIndex(i_prime);
                int64 second_index = routing.NodeToIndex(j_prime);
                routing.NextVar(index)->RemoveValue(second_index);
                routing.NextVar(second_index)->RemoveValue(index);
                ++j_prime;
              }
              ++i_prime;
            }
          }
          ++q;
        } while(q < capacity_size);
        for (int second_alternative = 0; second_alternative < alternative_size; ++second_alternative) {
          ++j;
        }
      }

      for (int alternative = 0; alternative < alternative_size; ++alternative) {
        ++i;
      }
    }
  }
}

void NeighbourFilter(const TSPTWDataDT &data, RoutingModel &routing, Solver *solver, Assignment *assignment, int64 neighbourhood) {
  TSPTWDataDT data2 = data;
  const int size_problem = data.SizeProblem();

  if (neighbourhood > 0 && size_problem > neighbourhood) {
    std::vector<std::vector<Link>> global_vector;

    RoutingModel::NodeIndex i(0);
    for (int activity = 0; activity <= size_problem; ++activity) {

      int32 alternative_size = data.AlternativeSize(activity);
      for (int alternative = 0; alternative < alternative_size; ++alternative) {
        std::vector<Link> link_list;
          RoutingModel::NodeIndex j(0);
        for (int second_activity = 0; second_activity <= size_problem; ++second_activity) {
          int32 second_alternative_size = data.AlternativeSize(second_activity);
          for (int second_alternative = 0; second_alternative < second_alternative_size; ++second_alternative) {
            if (activity != second_activity) {
              link_list.push_back(Link(&data2,i,j));
            }
            ++j;
          }
        }
        global_vector.push_back(link_list);
        ++i;
      }
    }

    int64 array_index = 0;
    RoutingModel::NodeIndex k(0);
    std::vector<int64> index_vector;
    std::vector<std::vector<int64>> remove_vectors;
    for (int activity = 0; activity <= size_problem ; ++activity) index_vector.push_back(activity);

    for (int activity = 0; activity <= size_problem; ++activity) {
      int32 alternative_size = data.AlternativeSize(activity);
      for (int alternative = 0; alternative < alternative_size; ++alternative) {
        std::vector<int64> removable_vector(index_vector);

        int64 index = routing.NodeToIndex(k);
        std::nth_element(global_vector.at(index).begin(), global_vector.at(index).begin() + neighbourhood, global_vector.at(index).end(), EvalDistance);
        global_vector.at(index).erase(global_vector.at(index).begin() + neighbourhood +1, global_vector.at(index).end());
        for (Link valid_link : global_vector.at(index)) {
          removable_vector.erase(std::remove(removable_vector.begin(), removable_vector.end(), routing.NodeToIndex(valid_link.destination)), removable_vector.end());
        }
        remove_vectors.push_back(removable_vector);
        ++array_index;
        ++k;
      }
    }

    RoutingModel::NodeIndex l(0);
    for (int activity = 0; activity <= size_problem; ++activity) {
      int32 alternative_size = data.AlternativeSize(activity);
      for (int alternative = 0; alternative < alternative_size; ++alternative) {
        int64 index = routing.NodeToIndex(l);
        for (int64 node_index: remove_vectors.at(activity)) {
          remove_vectors.at(node_index).erase(std::remove(remove_vectors.at(node_index).begin(), remove_vectors.at(node_index).end(), index), remove_vectors.at(node_index).end());
        }
        ++l;
      }
    }

    for (TSPTWDataDT::Route* route: data.Routes()) {
      int64 current_index;
      int64 previous_index = -1;
      std::vector<RoutingModel::NodeIndex> route_nodes;

      for (std::string service_id: route->service_ids) {
        current_index = data.IdIndex(service_id);
        if (previous_index != -1) {
          remove_vectors.at(current_index).erase(std::remove(remove_vectors.at(current_index).begin(), remove_vectors.at(current_index).end(), previous_index), remove_vectors.at(current_index).end());
          remove_vectors.at(previous_index).erase(std::remove(remove_vectors.at(previous_index).begin(), remove_vectors.at(previous_index).end(), current_index), remove_vectors.at(previous_index).end());
        }
        previous_index = current_index;
      }
    }

    RoutingModel::NodeIndex m(0);
    for (int activity = 0; activity <= size_problem; ++activity) {
      int32 alternative_size = data.AlternativeSize(activity);
      for (int alternative = 0; alternative < alternative_size; ++alternative) {
        int64 index = routing.NodeToIndex(m);
        for (int64 removable_index: remove_vectors.at(activity)) {
          routing.NextVar(index)->RemoveValue(removable_index);
        }
        ++m;
      }
    }
  }
}

void DomainFilters(const TSPTWDataDT &data, RoutingModel &routing, Solver *solver, Assignment *assignment, int64 neighbourhood) {
  CapacityFilter(data, routing, solver, assignment);
  NeighbourFilter(data, routing, solver, assignment, neighbourhood);
}

}
