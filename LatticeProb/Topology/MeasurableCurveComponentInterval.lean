import LatticeProb.Topology.MeasurableCurveComponentClosure
import LatticeProb.LQG.MatingOfTreesCouplingSegments

/-! # Measurable equality of a component closure and a curve segment -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace LatticeProb

/-- Equality between the closure of a random open set and the image of a fixed
compact interval is measurable when membership at a countable dense family is
measurable. -/
theorem measurableSet_closure_eq_image_Icc
    {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    [SecondCountableTopology E] [Nonempty E] [MeasurableSpace E] [BorelSpace E]
    (U : Ω → Set E) (g : Ω → C(ℝ, E)) (hU : ∀ ω, IsOpen (U ω))
    (hg : Measurable g)
    (hmem : ∀ n : ℕ, MeasurableSet {ω | denseSeq E n ∈ U ω}) :
    MeasurableSet {ω | closure (U ω) = g ω '' Icc (0 : ℝ) 1} := by
  let T := Icc (0 : ℝ) 1
  let : Nonempty T := ⟨⟨0, by simp [T]⟩⟩
  have himage (ω : Ω) : IsClosed (g ω '' Icc (0 : ℝ) 1) :=
    (isCompact_Icc.image (g ω).continuous).isClosed
  have htest (ω : Ω) : closure (U ω) = g ω '' Icc (0 : ℝ) 1 ↔
      (∀ n : ℕ, denseSeq E n ∈ U ω → denseSeq E n ∈ g ω '' Icc (0 : ℝ) 1) ∧
      (∀ n : ℕ, g ω (denseSeq T n : ℝ) ∈ closure (U ω)) := by
    constructor
    · intro h
      constructor
      · intro n hn
        rw [← h]
        exact subset_closure hn
      · intro n
        rw [h]
        exact mem_image_of_mem _ (denseSeq T n).property
    · rintro ⟨hleft, hright⟩
      apply Subset.antisymm
      · apply closure_minimal _ (himage ω)
        apply (denseRange_denseSeq E).open_subset_closure_inter (hU ω) |>.trans
        apply closure_minimal _ (himage ω)
        rintro z ⟨hzU, ⟨n, rfl⟩⟩
        exact hleft n hzU
      · rintro z ⟨t, ht, rfl⟩
        have hc : IsClosed {s : T | g ω s ∈ closure (U ω)} :=
          isClosed_closure.preimage ((g ω).continuous.comp continuous_subtype_val)
        have hd : closure (range (denseSeq T)) ⊆ {s : T | g ω s ∈ closure (U ω)} :=
          closure_minimal (by rintro _ ⟨n, rfl⟩; exact hright n) hc
        exact hd ((denseRange_denseSeq T) ⟨t, ht⟩)
  have heq : {ω | closure (U ω) = g ω '' Icc (0 : ℝ) 1} =
      (⋂ n : ℕ, ({ω | denseSeq E n ∈ U ω}ᶜ ∪
        {ω | denseSeq E n ∈ g ω '' Icc (0 : ℝ) 1})) ∩
      (⋂ n : ℕ, {ω | g ω (denseSeq T n : ℝ) ∈ closure (U ω)}) := by
    ext ω
    simp only [htest, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff, mem_ofPred_eq,
      imp_iff_not_or]
  rw [heq]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro n
    exact (hmem n).compl.union
      ((ContinuousMap.isClosed_setOf_mem_image (E := E) isCompact_Icc).measurableSet.preimage
        (hg.prodMk measurable_const))
  · apply MeasurableSet.iInter
    intro n
    apply measurableSet_mem_closure_of_open U (fun ω => g ω (denseSeq T n : ℝ)) hU
    · exact (ContinuousMap.measurable_eval _).comp hg
    · exact hmem

/-- The closure of a selected component of a compact curve image equals a
variable interval image on a measurable event, including degenerate intervals. -/
theorem measurableSet_component_closure_eq_image_Icc
    {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    [SecondCountableTopology E] [LocallyConnectedSpace E] [Nonempty E]
    [MeasurableSpace E] [BorelSpace E]
    (f : Ω → C(ℝ, E)) (x : Ω → E) (a b : Ω → ℝ) {K : Set ℝ}
    (hK : IsCompact K) (hf : Measurable f) (hx : Measurable x)
    (ha : Measurable a) (hb : Measurable b) :
    MeasurableSet {ω | a ω ≤ b ω ∧
      closure (connectedComponentIn (interior (f ω '' K)) (x ω)) =
        f ω '' Icc (a ω) (b ω)} := by
  let U : Ω → Set E := fun ω => connectedComponentIn (interior (f ω '' K)) (x ω)
  let g : Ω → C(ℝ, E) := fun ω => ContinuousMap.segmentReparam (f ω, a ω, b ω)
  have hg : Measurable g := ContinuousMap.segmentReparam.continuous.measurable.comp
    (hf.prodMk (ha.prodMk hb))
  have hm := measurableSet_closure_eq_image_Icc U g
    (fun _ => isOpen_interior.connectedComponentIn) hg (fun n =>
      measurableSet_mem_component_interior_image_of_locallyConnected f x
        (fun _ => denseSeq E n) hK hf hx measurable_const)
  have heq : {ω | a ω ≤ b ω ∧ closure (U ω) = f ω '' Icc (a ω) (b ω)} =
      {ω | a ω ≤ b ω} ∩ {ω | closure (U ω) = g ω '' Icc (0 : ℝ) 1} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff]
    exact and_congr_right fun h => by rw [ContinuousMap.segmentReparam_image_Icc _ h]
  rw [heq]
  exact (measurableSet_le ha hb).inter hm

end LatticeProb
