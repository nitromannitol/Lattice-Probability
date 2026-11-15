import LatticeProb.Topology.UnboundedRayIntervalIntegrand
import Mathlib.Topology.Order.IntermediateValue

/-! # Measurable oscillation on path intervals -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal unitInterval

namespace LatticeProb.UnboundedRayIntervalIntegrand

private def intervalTime (a b : ℝ≥0) (u : unitInterval) : ℝ≥0 :=
  ⟨(1 - (u : ℝ)) * (a : ℝ) + (u : ℝ) * (b : ℝ),
    add_nonneg (mul_nonneg (sub_nonneg.mpr u.property.2) a.property)
      (mul_nonneg u.property.1 b.property)⟩

private theorem intervalTime_zero (a b : ℝ≥0) : intervalTime a b 0 = a := by
  apply Subtype.ext
  simp [intervalTime]

private theorem intervalTime_one (a b : ℝ≥0) : intervalTime a b 1 = b := by
  apply Subtype.ext
  simp [intervalTime]

private theorem continuous_intervalTime (a b : ℝ≥0) : Continuous (intervalTime a b) := by
  unfold intervalTime
  fun_prop

private theorem intervalTime_mem {a b : ℝ≥0} (hab : a ≤ b) (u : unitInterval) :
    intervalTime a b u ∈ Icc a b := by
  change (a : ℝ) ≤ (1 - (u : ℝ)) * (a : ℝ) + (u : ℝ) * (b : ℝ) ∧
    (1 - (u : ℝ)) * (a : ℝ) + (u : ℝ) * (b : ℝ) ≤ (b : ℝ)
  have hd : 0 ≤ (b : ℝ) - (a : ℝ) := sub_nonneg.mpr hab
  have h₁ := mul_nonneg u.property.1 hd
  have h₂ := mul_nonneg (sub_nonneg.mpr u.property.2) hd
  constructor <;> nlinarith

private def intervalPath {d : ℕ} (f : Path d) (a b : ℝ≥0) :
    C(unitInterval, EuclideanSpace ℝ (Fin d)) :=
  ⟨fun u => f (intervalTime a b u), f.continuous.comp (continuous_intervalTime a b)⟩

private theorem continuous_intervalPath {d : ℕ} :
    Continuous (fun p : Path d × ℝ≥0 × ℝ≥0 => intervalPath p.1 p.2.1 p.2.2) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have ht : Continuous (fun p : (Path d × ℝ≥0 × ℝ≥0) × unitInterval =>
      intervalTime p.1.2.1 p.1.2.2 p.2) := by
    unfold intervalTime
    fun_prop
  exact continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk ht)

private theorem isClosed_diameterBound {d : ℕ} (η : ℝ) :
    IsClosed {f : C(unitInterval, EuclideanSpace ℝ (Fin d)) |
      ∀ s t : unitInterval, dist (f s) (f t) ≤ η} := by
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro t
  exact isClosed_le ((continuous_eval_const s).dist (continuous_eval_const t)) continuous_const

/-- Oscillation on a closed interval with measurable endpoints is measurable,
including when the endpoints are reversed. -/
theorem measurableSet_interval_oscillation_le {d : ℕ} {X : Type*} [MeasurableSpace X]
    (f : X → Path d) (a b : X → ℝ≥0) (η : ℝ)
    (hf : Measurable f) (ha : Measurable a) (hb : Measurable b) :
    MeasurableSet {x | ∀ s ∈ Icc (a x) (b x), ∀ t ∈ Icc (a x) (b x),
      dist (f x s) (f x t) ≤ η} := by
  have hcurve : Measurable (fun x => intervalPath (f x) (a x) (b x)) :=
    continuous_intervalPath.measurable.comp (hf.prodMk (ha.prodMk hb))
  have hclosed := (isClosed_diameterBound (d := d) η).measurableSet.preimage hcurve
  have hrev : MeasurableSet {x | b x < a x} := measurableSet_lt hb ha
  convert hrev.union hclosed using 1
  ext x
  simp only [mem_ofPred_eq, mem_union]
  constructor
  · intro h
    by_cases hab : a x ≤ b x
    · right
      intro s t
      exact h _ (intervalTime_mem hab s) _ (intervalTime_mem hab t)
    · exact Or.inl (lt_of_not_ge hab)
  · rintro (hrev | hbound) s hs t ht
    · exact False.elim ((not_le_of_gt hrev) (hs.1.trans hs.2))
    · have hsurj : Icc (a x) (b x) ⊆ Set.range (intervalTime (a x) (b x)) := by
        simpa only [intervalTime_zero, intervalTime_one] using
          (intermediate_value_univ (0 : unitInterval) (1 : unitInterval)
            (continuous_intervalTime (a x) (b x)))
      obtain ⟨u, hu⟩ := hsurj hs
      obtain ⟨v, hv⟩ := hsurj ht
      simpa only [intervalPath, ContinuousMap.coe_mk, hu, hv] using hbound u v

end LatticeProb.UnboundedRayIntervalIntegrand
