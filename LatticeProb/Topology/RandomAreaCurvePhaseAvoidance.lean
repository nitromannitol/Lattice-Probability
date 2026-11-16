import LatticeProb.Topology.AreaCurvePhaseAvoidance
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Prod

/-! # Phase avoidance for random area-parametrized curves -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace LatticeProb

noncomputable local instance : MeasurableSpace (NonemptyCompacts ℂ) := borel _
local instance : BorelSpace (NonemptyCompacts ℂ) := ⟨rfl⟩

/-- An independent atomless phase avoids every compact set in a countable
family determined by the environment, simultaneously for all cell labels. -/
theorem ae_prod_shiftedCompactCell_ne
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (P : Measure Ω) (Q : Measure ℝ) [SFinite Q] [NullSingletonClass Q]
    (η : Ω → C(ℝ, ℂ)) (K : I → Ω → NonemptyCompacts ℂ)
    (hη : Measurable η) (hK : ∀ i, Measurable (K i))
    (harea : ∀ᵐ ω ∂P, ∃ μ : Measure ℂ,
      ∀ a b, a < b → μ (η ω '' Icc a b) = ENNReal.ofReal (b - a))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ p ∂(P.prod Q), ∀ k : ℤ, ∀ i : I,
      shiftedCompactCell (η p.1) ε p.2 k ≠ K i p.1 := by
  have hmeas : MeasurableSet {p : Ω × ℝ | ∀ k : ℤ, ∀ i : I,
      shiftedCompactCell (η p.1) ε p.2 k ≠ K i p.1} := by
    apply measurableSet_setOfPred.2
    refine Measurable.forall fun k => Measurable.forall fun i => ?_
    have hc : Measurable (fun p : Ω × ℝ => shiftedCompactCell (η p.1) ε p.2 k) :=
      (measurable_shiftedCompactCell k).comp
        ((hη.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd))
    exact measurableSet_setOfPred.1
      (measurableSet_eq_fun hc ((hK i).comp measurable_fst)).compl
  apply (Measure.ae_prod_iff_ae_ae hmeas).2
  filter_upwards [harea] with ω hω
  obtain ⟨μ, hμ⟩ := hω
  filter_upwards [ae_shiftedCompactCell_not_mem_countable (η ω) μ hμ hε
    (Set.range (fun i => K i ω)) (Set.countable_range _) Q] with θ hθ k i
  exact fun heq => hθ k ⟨i, heq.symm⟩

end LatticeProb
