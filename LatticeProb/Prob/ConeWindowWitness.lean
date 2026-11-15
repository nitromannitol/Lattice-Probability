import LatticeProb.Topology.MovingEndpointMinimum
import LatticeProb.Prob.AnalyticUniversalMeasurable

/-! # Measurability of window witnesses for two continuous paths -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- The rational-start conditions for an endpoint to witness strict coverage
of a time in a window. -/
def coneWindowWitness (l r : ℝ) :
    Set (((C(ℝ, ℝ) × C(ℝ, ℝ)) × ℝ) × ℝ) :=
  {p | l < p.1.2 ∧ p.1.2 < p.2 ∧ p.2 ≤ r ∧
    (∃ q : ℚ, (q : ℝ) < p.1.2 ∧ (q : ℝ) < p.2 ∧
      ∀ v ∈ Icc (q : ℝ) p.2,
        p.1.1.1 p.2 ≤ p.1.1.1 v ∧ p.1.1.2 p.2 ≤ p.1.1.2 v) ∧
    ∀ q : ℚ, (q : ℝ) < l → ¬ ((q : ℝ) < p.2 ∧
      ∀ v ∈ Icc (q : ℝ) p.2,
        p.1.1.1 p.2 ≤ p.1.1.1 v ∧ p.1.1.2 p.2 ≤ p.1.1.2 v)}

/-- The strict-window witness relation is Borel. -/
theorem measurableSet_coneWindowWitness (l r : ℝ) :
    MeasurableSet (coneWindowWitness l r) := by
  let E (q : ℚ) : Set (((C(ℝ, ℝ) × C(ℝ, ℝ)) × ℝ) × ℝ) :=
    {p | (q : ℝ) < p.2 ∧ ∀ v ∈ Icc (q : ℝ) p.2,
      p.1.1.1 p.2 ≤ p.1.1.1 v ∧ p.1.1.2 p.2 ≤ p.1.1.2 v}
  have hE (q : ℚ) : MeasurableSet (E q) := by
    exact (measurableSet_two_endpoint_minima q).preimage
      (show Measurable (fun p : (((C(ℝ, ℝ) × C(ℝ, ℝ)) × ℝ) × ℝ) =>
        (p.1.1, p.2)) by fun_prop)
  have hleft : MeasurableSet {p : (((C(ℝ, ℝ) × C(ℝ, ℝ)) × ℝ) × ℝ) | l < p.1.2} :=
    (isOpen_lt continuous_const (continuous_snd.comp continuous_fst)).measurableSet
  have hmid : MeasurableSet {p : (((C(ℝ, ℝ) × C(ℝ, ℝ)) × ℝ) × ℝ) | p.1.2 < p.2} :=
    (isOpen_lt (continuous_snd.comp continuous_fst) continuous_snd).measurableSet
  have hright : MeasurableSet {p : (((C(ℝ, ℝ) × C(ℝ, ℝ)) × ℝ) × ℝ) | p.2 ≤ r} :=
    (isClosed_le continuous_snd continuous_const).measurableSet
  have hex : MeasurableSet (⋃ q : ℚ,
      ({p : (((C(ℝ, ℝ) × C(ℝ, ℝ)) × ℝ) × ℝ) | (q : ℝ) < p.1.2} ∩ E q)) := by
    apply MeasurableSet.iUnion
    intro q
    exact (isOpen_lt continuous_const (continuous_snd.comp continuous_fst)).measurableSet.inter (hE q)
  have hall : MeasurableSet (⋂ q : ℚ, if (q : ℝ) < l then (E q)ᶜ else univ) := by
    apply MeasurableSet.iInter
    intro q
    split_ifs
    · exact (hE q).compl
    · exact MeasurableSet.univ
  have h := hleft.inter (hmid.inter (hright.inter (hex.inter hall)))
  convert h using 1
  ext p
  simp only [coneWindowWitness, mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter,
    mem_ite_univ_right, mem_compl_iff, E]

/-- Strict window coverage is universally measurable as a projection of the
Borel witness relation. -/
theorem nullMeasurableSet_coneWindowCoverage (l r : ℝ)
    (μ : Measure ((C(ℝ, ℝ) × C(ℝ, ℝ)) × ℝ)) [IsFiniteMeasure μ] :
    NullMeasurableSet (Prod.fst '' coneWindowWitness l r) μ := by
  exact AnalyticSet.nullMeasurableSet μ
    ((measurableSet_coneWindowWitness l r).analyticSet.image_of_continuous continuous_fst)

/-- A measurable observation of the paths and time pulls back the projected
coverage event to a completed-measurable event under any finite measure. -/
theorem nullMeasurableSet_preimage_coneWindowCoverage
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f : Ω → (C(ℝ, ℝ) × C(ℝ, ℝ)) × ℝ) (hf : Measurable f) (l r : ℝ) :
    NullMeasurableSet (f ⁻¹' (Prod.fst '' coneWindowWitness l r)) P := by
  have : IsFiniteMeasure (P.map f) := P.isFiniteMeasure_map f
  exact (nullMeasurableSet_coneWindowCoverage l r (P.map f)).preimage
    (hf.quasiMeasurePreserving P)

end LatticeProb
