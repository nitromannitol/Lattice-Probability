/-
# Finite stacks, cycle popping, loop erasure and independent-cell masses

Axiom reports for principal reusable results, complementing the complete
library declaration and generated-constant census.
-/
import LatticeProb.Combinatorics.LoopErasure.Basic
import LatticeProb.Graph.CyclePopping.Basic
import LatticeProb.Graph.TreeOrientation
import LatticeProb.Prob.CountablePartition
import LatticeProb.Prob.FiniteCellFactorization
import LatticeProb.Prob.FiniteOutputNormalization
import LatticeProb.Prob.IidBlocks
import LatticeProb.Combinatorics.LoopErasure.Composition
import LatticeProb.Prob.AdaptiveReads
import LatticeProb.Graph.CyclePopping.Trace
import LatticeProb.Prob.CellTranscripts
import LatticeProb.Graph.CyclePopping.Erasure

#print axioms LatticeProb.Graph.adj_eq_snd_or_eq_snd
#print axioms LatticeProb.Prob.FiniteCellFactorization.measure_event_inter_values
#print axioms LatticeProb.Graph.CyclePopping.pop_step_confluent
#print axioms LatticeProb.Graph.CyclePopping.terminal_top_eq
#print axioms LatticeProb.Prob.AdaptiveReads.measure_finite_reads_of_injective
#print axioms LatticeProb.Combinatorics.LoopErasure.loopErase_length_le
#print axioms LatticeProb.Combinatorics.LoopErasure.loopErase_comp_loop_comp
#print axioms LatticeProb.Graph.CyclePopping.closed_excursion_pop
#print axioms LatticeProb.Graph.CyclePopping.loop_erase_pop_run
#print axioms LatticeProb.Graph.CyclePopping.loop_erase_cursor_spec
#print axioms LatticeProb.Prob.CellTranscripts.measure_cylinder
#print axioms LatticeProb.Prob.CountablePartition.measure_eq_of_partition
#print axioms LatticeProb.Prob.IidBlocks.measure_eq_zero_of_subset_avoidsConstantBlocks
#print axioms LatticeProb.Prob.event_mass_eq_inv_card
