import LatticeProb.Prob.ContinuousPathStepTimeCompare
import LatticeProb.Prob.BrownianStepTimeSuperpoly

/-!
# Exit before the `K`-th displacement time at every spatial scale

`measure_exit_by_stepTime_superpoly` bounds the probability that a Brownian motion `B` on `ℝ ^ d`
started at `0` reaches the unit sphere before its `K`-th displacement time of size `r`, for
`K = ⌊r ^ -(2 - ζ)⌋`, by `C r ^ p` for every `p`. By Brownian scaling the same bound holds, with the
same constant, for the sphere of radius `a` and displacements of size `a r`, for every `a > 0`
(`measure_exit_by_stepTime_superpoly_scaled`).

* `stepTime_const_smul`: the displacement times of `c • f` of size `c r` are those of `f` of size
  `r`, for `c > 0`.
* `coe_le_stepTime_comp_iff`: `t ≤ σ_j(g ∘ φ)` iff `φ t ≤ σ_j(g)` for an order isomorphism `φ`.
* `IsBrownianSpace.timeScale`: `t ↦ c^{-1/2} B (c t)` is again a Brownian motion started at `0`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

universe u

namespace LatticeProb

section Smul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma stepSet_const_smul (f : ℝ≥0 → E) {c : ℝ} (hc : 0 < c) (r : ℝ) (a : ℝ≥0) :
    stepSet (fun t => c • f t) (c * r) a = stepSet f r a := by
  ext t
  show (a ≤ t ∧ c * r ≤ ‖c • f t - c • f a‖) ↔ (a ≤ t ∧ r ≤ ‖f t - f a‖)
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg hc.le]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, le_of_mul_le_mul_left h2 hc⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, mul_le_mul_of_nonneg_left h2 hc.le⟩

lemma nextStep_const_smul (f : ℝ≥0 → E) {c : ℝ} (hc : 0 < c) (r : ℝ) (a : ℝ≥0) :
    nextStep (fun t => c • f t) (c * r) a = nextStep f r a := by
  unfold nextStep
  rw [stepSet_const_smul f hc r a]

/-- The displacement times of `c • f` of size `c r` are those of `f` of size `r`, for `c > 0`. -/
theorem stepTime_const_smul (f : ℝ≥0 → E) {c : ℝ} (hc : 0 < c) (r : ℝ) (j : ℕ) :
    stepTime (fun t => c • f t) (c * r) j = stepTime f r j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    by_cases h : stepTime f r j = ⊤
    · rw [stepTime_succ_of_eq_top h, stepTime_succ_of_eq_top (ih.trans h)]
    · rw [stepTime_succ_of_ne_top h, stepTime_succ_of_ne_top (by rwa [ih]), ih,
        nextStep_const_smul f hc]

end Smul

lemma coe_le_stepTime_comp_iff {E : Type*} [NormedAddCommGroup E] (g : ℝ≥0 → E) (r : ℝ)
    (φ : ℝ≥0 ≃o ℝ≥0) (j : ℕ) (t : ℝ≥0) :
    (t : ℝ≥0∞) ≤ stepTime (g ∘ φ) r j ↔ ((φ t : ℝ≥0) : ℝ≥0∞) ≤ stepTime g r j := by
  rcases stepTime_comp_orderIso g r φ j with ⟨h1, h2⟩ | ⟨u, h1, h2⟩
  · rw [h1, h2]; simp
  · rw [h1, h2, ENNReal.coe_le_coe, ENNReal.coe_le_coe, φ.le_iff_le]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Brownian scaling** on `ℝ ^ d`: if `B` is a Brownian motion started at `0` and `c > 0`, then
`t ↦ c^{-1/2} B (c t)` is a Brownian motion started at `0`. -/
theorem IsBrownianSpace.timeScale {d : ℕ} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hB : IsBrownianSpace d 0 B P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsBrownianSpace d 0 (fun t ω => (√(c : ℝ))⁻¹ • B (c * t) ω) P where
  start := by
    filter_upwards [hB.start] with ω hω
    simp [hω]
  coord i := by
    have h := (hB.coord i).smul hc
    have heq : (fun (t : ℝ≥0) (ω : Ω) =>
        Real.sqrt d * (((√(c : ℝ))⁻¹ • B (c * t) ω) i - (0 : EuclideanSpace ℝ (Fin d)) i)) =
        fun t ω => (√(c : ℝ))⁻¹ * (Real.sqrt d * (B (c * t) ω i - (0 : EuclideanSpace ℝ (Fin d)) i)) := by
      funext t ω
      simp only [PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, sub_zero]
      ring
    rw [heq]
    exact h
  indep := by
    have hmeas : Measurable fun (p : ℝ≥0 → ℝ) (s : ℝ≥0) => (√(c : ℝ))⁻¹ * p (c * s) :=
      measurable_pi_iff.mpr fun s => (measurable_pi_apply (c * s)).const_mul _
    have h := hB.indep.comp (fun _ (p : ℝ≥0 → ℝ) (s : ℝ≥0) => (√(c : ℝ))⁻¹ * p (c * s))
      (fun _ => hmeas)
    convert h using 1
    funext i ω
    funext s
    simp only [Function.comp_apply, PiLp.smul_apply, smul_eq_mul]

/-- **Lemma 6.8 at scale `a`.** For a Brownian motion `B` on `ℝ ^ d` started at `0`, `0 < ζ < 1`
and `p ∈ ℕ`, there is `C` such that for all `a > 0` and `0 < r < 1` the probability that `B`
reaches the sphere of radius `a` before its `K`-th displacement time of size `a r`,
`K = ⌊r ^ -(2 - ζ)⌋`, is at most `C r ^ p`. The constant does not depend on `a`. -/
theorem measure_exit_by_stepTime_superpoly_scaled (d : ℕ) (hd : 0 < d) {ζ : ℝ} (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)), IsBrownianSpace d 0 B P →
      ∀ a : ℝ≥0, 0 < a → ∀ r : ℝ≥0, 0 < r → r < 1 →
      P {ω | ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ stepTime (fun t => B t ω) ((a : ℝ) * r)
            ⌊(r : ℝ) ^ (-(2 - ζ))⌋₊ ∧ (a : ℝ) ≤ ‖B t ω‖}
        ≤ ENNReal.ofReal (C * (r : ℝ) ^ p) := by
  obtain ⟨C, hC⟩ := measure_exit_by_stepTime_superpoly.{u} d hd hζ0 hζ1 p
  refine ⟨C, fun Ω _ P _ B hB a ha r hr0 hr1 => ?_⟩
  have ha' : (0 : ℝ) < a := ha
  have hc : a ^ 2 ≠ 0 := pow_ne_zero 2 ha.ne'
  have hsq : √(((a ^ 2 : ℝ≥0)) : ℝ) = a := by
    rw [NNReal.coe_pow, Real.sqrt_sq a.coe_nonneg]
  have hB' := hB.timeScale hc
  rw [hsq] at hB'
  refine le_trans (measure_mono ?_) (hC Ω P _ hB' r hr0 hr1)
  intro ω hω
  obtain ⟨t, ht, hat⟩ := hω
  set φ : ℝ≥0 ≃o ℝ≥0 := OrderIso.mulLeft₀ (a ^ 2) (pow_pos ha 2) with hφ
  have hφt : φ (t / a ^ 2) = t := by
    rw [hφ, OrderIso.mulLeft₀_apply]
    field_simp
  have hfun : (fun s => (a : ℝ)⁻¹ • B (a ^ 2 * s) ω) = (fun s => (a : ℝ)⁻¹ • B s ω) ∘ φ := by
    funext s
    rfl
  have hst : stepTime (fun s => (a : ℝ)⁻¹ • B s ω) (r : ℝ) ⌊(r : ℝ) ^ (-(2 - ζ))⌋₊ =
      stepTime (fun s => B s ω) ((a : ℝ) * r) ⌊(r : ℝ) ^ (-(2 - ζ))⌋₊ := by
    have := stepTime_const_smul (fun s => B s ω) (inv_pos.2 ha') ((a : ℝ) * r)
      ⌊(r : ℝ) ^ (-(2 - ζ))⌋₊
    rwa [inv_mul_cancel_left₀ ha'.ne'] at this
  show ∃ u : ℝ≥0, (u : ℝ≥0∞) ≤ stepTime (fun s => (a : ℝ)⁻¹ • B (a ^ 2 * s) ω) (r : ℝ)
      ⌊(r : ℝ) ^ (-(2 - ζ))⌋₊ ∧ 1 ≤ ‖(a : ℝ)⁻¹ • B (a ^ 2 * u) ω‖
  refine ⟨t / a ^ 2, ?_, ?_⟩
  · rw [hfun, coe_le_stepTime_comp_iff, hφt, hst]
    exact ht
  · have hmt : a ^ 2 * (t / a ^ 2) = t := by field_simp
    rw [hmt, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 a.coe_nonneg)]
    calc (1 : ℝ) = (a : ℝ)⁻¹ * a := (inv_mul_cancel₀ ha'.ne').symm
      _ ≤ (a : ℝ)⁻¹ * ‖B t ω‖ := mul_le_mul_of_nonneg_left hat (inv_nonneg.2 a.coe_nonneg)

end LatticeProb
