import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.SetupStop
import Mathlib.Topology.Sets.VietorisTopology
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Effros measurability of compact encodings -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace
open LQGMetric.Blueprint LQGMetric.GM

namespace LatticeProb.LQG

/-- A nonempty compact encoding is measurable from the hit sigma-field of its
underlying random set. -/
theorem measurable_compactEncoding_of_setSigma {Ω : Type} (A : Ω → Set ℂ)
    (K : Ω → NonemptyCompacts ℂ) (hK : ∀ ω, A ω = (K ω : Set ℂ))
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)] :
    Measurable[setSigma A] K := by
  classical
  let : MeasurableSpace Ω := setSigma A
  rw [BorelSpace.measurable_eq (α := NonemptyCompacts ℂ),
    NonemptyCompacts.isTopologicalBasis.borel_eq_generateFrom]
  apply measurable_generateFrom
  rintro s ⟨u, ⟨hu, _, hopen⟩, rfl⟩
  have hclosed : ∀ ω, IsClosed (A ω) := fun ω => by rw [hK ω]; exact (K ω).isCompact.isClosed
  have hsubset : MeasurableSet {ω | A ω ⊆ ⋃₀ u} := by
    have hc := gm_setSigma_hit_closed hclosed (isOpen_sUnion hopen).isClosed_compl
    convert hc.compl using 1
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, inter_compl_nonempty_iff, not_not]
  have hhits : MeasurableSet {ω | ∀ U ∈ u, (A ω ∩ U).Nonempty} := by
    simpa only [ofPred_forall] using
      hu.measurableSet_biInter (fun U hU => gm_setSigma_hit_open A (hopen U hU))
  convert hsubset.inter hhits using 1
  ext ω
  simp only [mem_preimage, mem_ofPred_eq, mem_inter_iff, ← hK ω]

end LatticeProb.LQG
