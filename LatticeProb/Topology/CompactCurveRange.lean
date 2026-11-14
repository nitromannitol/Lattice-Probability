import LatticeProb.Topology.MovingIntervalCurve
import Mathlib.Topology.Sets.VietorisTopology

/-! # Compact ranges of continuous curves -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped unitInterval

namespace LatticeProb

/-- The nonempty compact range of a continuous map on a nonempty compact space. -/
def compactCurveRange {X E : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    [TopologicalSpace E] (f : C(X, E)) : NonemptyCompacts E :=
  ⟨⟨range f, isCompact_range f.continuous⟩, range_nonempty f⟩

@[simp] theorem coe_compactCurveRange {X E : Type*} [TopologicalSpace X]
    [CompactSpace X] [Nonempty X] [TopologicalSpace E] (f : C(X, E)) :
    (compactCurveRange f : Set E) = range f := rfl

/-- The compact range depends continuously on the map in the compact-open topology. -/
theorem continuous_compactCurveRange {X E : Type*} [TopologicalSpace X]
    [CompactSpace X] [Nonempty X] [TopologicalSpace E] :
    Continuous (compactCurveRange : C(X, E) → NonemptyCompacts E) := by
  let : TopologicalSpace (Set E) := TopologicalSpace.vietoris E
  apply NonemptyCompacts.isEmbedding_coe.continuous_iff.mpr
  change @Continuous C(X, E) (Set E) _ (TopologicalSpace.vietoris E) (fun f => range f)
  rw [TopologicalSpace.vietoris.continuous_iff]
  constructor
  · intro U hU
    exact ContinuousMap.isOpen_setOfPred_range_subset hU
  · intro F hF
    change IsClosed {f : C(X, E) | range f ⊆ F}
    have h : {f : C(X, E) | range f ⊆ F} = ⋂ x : X, {f : C(X, E) | f x ∈ F} := by
      ext f
      simp only [mem_ofPred_eq, mem_iInter, range_subset_iff]
    rw [h]
    exact isClosed_iInter fun x => hF.preimage (continuous_eval_const x)

/-- Compact code of a shifted curve cell. -/
def shiftedCompactCell {E : Type*} [TopologicalSpace E]
    (f : C(ℝ, E)) (ε θ : ℝ) (k : ℤ) : NonemptyCompacts E :=
  compactCurveRange (shiftedCellCurve f ε θ k)

@[simp] theorem coe_shiftedCompactCell {E : Type*} [TopologicalSpace E]
    (f : C(ℝ, E)) (ε θ : ℝ) (k : ℤ) :
    (shiftedCompactCell f ε θ k : Set E) =
      f '' uIcc (ε * ((k : ℝ) - 1 + θ)) (ε * ((k : ℝ) + θ)) :=
  range_shiftedCellCurve f ε θ k

/-- The compact cell varies continuously with the curve, mesh and shift. -/
theorem continuous_shiftedCompactCell {E : Type*} [TopologicalSpace E] (k : ℤ) :
    Continuous (fun p : C(ℝ, E) × ℝ × ℝ => shiftedCompactCell p.1 p.2.1 p.2.2 k) :=
  continuous_compactCurveRange.comp (continuous_shiftedCellCurve k)

/-- The compact cell is jointly Borel measurable in the curve, mesh and shift. -/
theorem measurable_shiftedCompactCell {E : Type*} [TopologicalSpace E]
    [MeasurableSpace C(ℝ, E)] [BorelSpace C(ℝ, E)]
    [MeasurableSpace (NonemptyCompacts E)] [BorelSpace (NonemptyCompacts E)] (k : ℤ) :
    Measurable (fun p : C(ℝ, E) × ℝ × ℝ => shiftedCompactCell p.1 p.2.1 p.2.2 k) :=
  (continuous_shiftedCompactCell k).measurable

end LatticeProb
