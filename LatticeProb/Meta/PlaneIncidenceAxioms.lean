module

/-
# Local plane incidence, dense labels and finite-point complements

Axiom reports for principal reusable results, complementing the complete
library declaration and generated-constant census.
-/
public import LatticeProb.Topology.DenseLocalLabels
public import LatticeProb.Topology.FinitePointComplement
public import LatticeProb.Topology.LocalFaceIncidence
public import LatticeProb.Topology.SubintervalParameter
public import LatticeProb.Topology.ArcFaceIncidence
public import LatticeProb.Topology.AxisNeighborhood

@[expose] public section

#print axioms LatticeProb.PlaneTopology.interior_subset_component_incidence_of_regular_axis
#print axioms LatticeProb.PlaneTopology.axis_mem_closure_compl
#print axioms LatticeProb.Topology.eq_of_dense_local_labels
#print axioms LatticeProb.PlaneTopology.isPathConnected_compl_of_finite
#print axioms LatticeProb.PlaneTopology.axis_mem_closure_component_iff
#print axioms LatticeProb.Topology.exists_interior_subintervalParameter
