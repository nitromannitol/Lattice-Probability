import LatticeProb.Prob.BrownianExpMartingale

/-!
# Sharp Gaussian tail of the running maximum of Brownian motion

For an almost surely continuous pre-Brownian motion `B` on a probability space and `T, a > 0`,

    `P {∃ t ≤ T, a ≤ B t} ≤ exp (-a² / (2 T))`

and the two-sided version with a factor `2`.  The exponent is the sharp one (the constant of the
dyadic chaining bound `measure_exists_abs_sub_ge_le` is not).  The proof applies the gambler's ruin
estimate `measure_exists_drift_lt_le` with the drift `c = a / (2 T)` and a level `δ < a / 2`, then
lets `δ ↑ a / 2`; almost sure continuity is reduced to everywhere continuity by modifying `B`
on a measurable null set.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Sharp tail of the running maximum of Brownian motion.**  For a pre-Brownian motion with
almost surely continuous paths, `P {∃ t ≤ T, a ≤ B t} ≤ exp (-a² / (2 T))`. -/
theorem measure_exists_le_ge_le_exp (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => B t ω) {T a : ℝ} (hT : 0 < T) (ha : 0 < a) :
    P {ω | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ a ≤ B t ω} ≤
      ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * T)))) := by
  classical
  obtain ⟨N, hNm, hNP, hN⟩ : ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧
      ∀ ω ∉ N, Continuous fun t => B t ω := by
    refine ⟨toMeasurable P {ω | ¬ Continuous fun t => B t ω}, measurableSet_toMeasurable _ _, ?_, ?_⟩
    · rw [measure_toMeasurable]
      exact ae_iff.1 hcont
    · intro ω hω
      by_contra h
      exact hω (subset_toMeasurable _ _ h)
  let B' : ℝ≥0 → Ω → ℝ := fun t => Nᶜ.indicator (B t)
  have hmod : ∀ t, B t =ᵐ[P] B' t := fun t => by
    have : ∀ᵐ ω ∂P, ω ∉ N := by
      rw [ae_iff]
      simpa using hNP
    filter_upwards [this] with ω hω
    simp [B', Set.indicator_of_mem (show ω ∈ Nᶜ from hω)]
  have hB'pre : IsPreBrownianReal B' P := hB.congr hmod
  have hm' : ∀ t, Measurable (B' t) := fun t => (hm t).indicator hNm.compl
  have hcont' : ∀ ω, Continuous fun t => B' t ω := by
    intro ω
    by_cases h : ω ∈ N
    · have : (fun t => B' t ω) = fun _ => 0 := by
        funext t
        simp [B', Set.indicator_of_notMem (show ω ∉ Nᶜ by simpa using h)]
      rw [this]
      exact continuous_const
    · have : (fun t => B' t ω) = fun t => B t ω := by
        funext t
        simp [B', Set.indicator_of_mem (show ω ∈ Nᶜ from h)]
      rw [this]
      exact hN ω h
  set c : ℝ := a / (2 * T) with hc
  have hcpos : 0 < c := by positivity
  have hcT : c * T = a / 2 := by
    rw [hc]
    field_simp
  have key : ∀ δ : ℝ, δ < a / 2 → P {ω | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ a ≤ B t ω} ≤
      ENNReal.ofReal (Real.exp (-(2 * c * δ))) := by
    intro δ hδ
    have hneg := measure_exists_drift_lt_le hB'pre.neg (fun t => (hm' t).neg)
      (fun ω => (hcont' ω).neg) hcpos δ
    calc P {ω | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ a ≤ B t ω}
        ≤ P ({ω | ∃ t : ℝ≥0, (-B') t ω + c * t < -δ} ∪ N) := by
          refine measure_mono fun ω hω => ?_
          obtain ⟨t, htT, hat⟩ := hω
          by_cases hωN : ω ∈ N
          · exact Or.inr hωN
          · refine Or.inl ⟨t, ?_⟩
            have e : B' t ω = B t ω := by simp [B', Set.indicator_of_mem (show ω ∈ Nᶜ from hωN)]
            have hct : c * (t : ℝ) ≤ c * T := mul_le_mul_of_nonneg_left htT hcpos.le
            simp only [Pi.neg_apply, e]
            linarith
      _ ≤ P {ω | ∃ t : ℝ≥0, (-B') t ω + c * t < -δ} + P N := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (-(2 * c * δ))) := by rw [hNP, add_zero]; exact hneg
  have hlim : Tendsto (fun δ : ℝ => ENNReal.ofReal (Real.exp (-(2 * c * δ)))) (𝓝[<] (a / 2))
      (𝓝 (ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * T)))))) := by
    have hcts : Continuous fun δ : ℝ => ENNReal.ofReal (Real.exp (-(2 * c * δ))) :=
      ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))
    have h1 := (hcts.tendsto (a / 2)).mono_left (nhdsWithin_le_nhds (s := Iio (a / 2)))
    have e : 2 * c * (a / 2) = a ^ 2 / (2 * T) := by
      rw [hc]
      field_simp
    rwa [e] at h1
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => key δ hδ)

/-- **Two-sided sharp tail of the running maximum of Brownian motion.**  For a pre-Brownian motion
with almost surely continuous paths, `P {∃ t ≤ T, a ≤ |B t|} ≤ 2 exp (-a² / (2 T))`. -/
theorem measure_exists_le_abs_ge_le_exp (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => B t ω) {T a : ℝ} (hT : 0 < T) (ha : 0 < a) :
    P {ω | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ a ≤ |B t ω|} ≤
      2 * ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * T)))) := by
  have h1 := measure_exists_le_ge_le_exp hB hm hcont hT ha
  have h2 := measure_exists_le_ge_le_exp (B := -B) hB.neg (fun t => (hm t).neg)
    (hcont.mono fun ω h => h.neg) hT ha
  calc P {ω | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ a ≤ |B t ω|}
      ≤ P ({ω | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ a ≤ B t ω} ∪
          {ω | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ a ≤ (-B) t ω}) := by
        refine measure_mono fun ω hω => ?_
        obtain ⟨t, htT, hat⟩ := hω
        rcases le_abs'.1 hat with h | h
        · exact Or.inr ⟨t, htT, by simp only [Pi.neg_apply]; linarith⟩
        · exact Or.inl ⟨t, htT, h⟩
    _ ≤ _ := measure_union_le _ _
    _ ≤ 2 * ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * T)))) := by
        rw [two_mul]
        exact add_le_add h1 h2

end LatticeProb
