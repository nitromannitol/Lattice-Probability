import LatticeProb.LQG.MatingOfTreesCouplingPathwise
import LatticeProb.Topology.ContinuousMapBorel
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Interior visits of random curves -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Membership in the interior of a random compact curve image is jointly measurable
in the curve and evaluation time. -/
theorem measurableSet_curve_mem_interior_image
    {Ω E ι : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [T2Space E]
    [TopologicalSpace.SeparableSpace E] [MeasurableSpace E] [BorelSpace E] [Countable ι]
    (B : ι → Set E) (f : Ω → C(ℝ, E)) {K : Set ℝ}
    (hK : IsCompact K) (hf : Measurable f)
    (hopen : ∀ i, IsOpen (B i))
    (hbasis : ∀ (V : Set E), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V) :
    MeasurableSet {p : Ω × ℝ | f p.1 p.2 ∈ interior (f p.1 '' K)} := by
  have heval : Measurable (fun p : Ω × ℝ => f p.1 p.2) :=
    continuous_eval.measurable.comp ((hf.comp measurable_fst).prodMk measurable_snd)
  have heq : {p : Ω × ℝ | f p.1 p.2 ∈ interior (f p.1 '' K)} =
      ⋃ i, ({p : Ω × ℝ | f p.1 p.2 ∈ B i} ∩ {p | B i ⊆ f p.1 '' K}) := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro hp
      obtain ⟨i, hi, hisub⟩ := hbasis _ isOpen_interior _ hp
      exact ⟨i, hi, hisub.trans interior_subset⟩
    · rintro ⟨i, hi, hisub⟩
      exact interior_maximal hisub (hopen i) hi
  rw [heq]
  exact MeasurableSet.iUnion fun i =>
    ((hopen i).measurableSet.preimage heval).inter
      ((ContinuousMap.measurableSet_setOf_subset_image (hopen i) hK).preimage
        (hf.comp measurable_fst))

/-- Fixed-time almost-sure interior visits imply almost-sure visits at almost every
    time in the interval. -/
theorem ae_ae_curve_mem_interior_image_of_fixed_time
    {Ω E ι : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [T2Space E]
    [TopologicalSpace.SeparableSpace E] [MeasurableSpace E] [BorelSpace E] [Countable ι]
    (P : Measure Ω) [SigmaFinite P] (B : ι → Set E) (f : Ω → C(ℝ, E))
    (a b : ℝ) (hf : Measurable f)
    (hopen : ∀ i, IsOpen (B i))
    (hbasis : ∀ (V : Set E), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V)
    (hfixed : ∀ t ∈ Ioo a b, ∀ᵐ ω ∂P, f ω t ∈ interior (f ω '' Icc a b)) :
    ∀ᵐ ω ∂P, ∀ᵐ t ∂volume.restrict (Ioo a b),
      f ω t ∈ interior (f ω '' Icc a b) := by
  apply (Measure.ae_ae_comm
    (measurableSet_curve_mem_interior_image B f isCompact_Icc hf hopen hbasis)).2
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hfixed t ht

end LatticeProb
