import LatticeProb.Prob.CorrelatedBMConeTimes
import LatticeProb.Prob.CorrelatedBMStart
import LatticeProb.Analysis.CorrelatedBMHolder

/-!
# The four half-line Brownian motions of an uncorrelated two-sided pair

Let `μ` be the law of a two-sided correlated planar Brownian motion `(L, R)` (`IsCorrelatedBM2 γ μ`). For
`k = (i, b) : Fin 2 × Bool` and `s ≥ 0`, `halfPath k s` is coordinate `i` at time `s` (if `b = true`) or at time
`-s` (if `b = false`): the forward and backward halves of `L` and of `R`.

* `isBrownianReal_halfPath`: for every `γ`, each of the four halves is a standard Brownian motion.
* `iIndepFun_halfPath`: at `γ = √2`, where the correlation `-cos (π γ² / 4)` of the coordinates vanishes, the four
  halves are mutually independent. This is Mathlib's `IsGaussianProcess.iIndepFun_of_covariance_eq_zero`: the
  covariance of two distinct halves is `lrCov γ i j * twoSidedMin s t`, which vanishes because `lrCov (√2) i j = 0`
  for `i ≠ j`, and `twoSidedMin s (-t) = 0` for `s, t ≥ 0`.
* `map_halfPaths_eq_pi`: equivalently, the joint law of the four half paths is the product of their four laws.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- At `γ = √2` the two coordinates of a correlated Brownian motion are uncorrelated. -/
theorem lrCov_sqrt_two_of_ne {i j : Fin 2} (hij : i ≠ j) : lrCov (√2) i j = 0 := by
  unfold lrCov
  split_ifs with h
  · exact absurd h hij
  · rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), show Real.pi * 2 / 4 = Real.pi / 2 by ring,
      Real.cos_pi_div_two, neg_zero]

/-- The values of a two-sided Brownian motion on opposite sides of `0` are uncorrelated. -/
theorem twoSidedMin_neg_right {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : twoSidedMin s (-t) = 0 := by
  unfold twoSidedMin
  rw [neg_neg, max_eq_left hs, max_eq_right (neg_nonpos.2 ht), max_eq_right (neg_nonpos.2 hs),
    max_eq_left ht, min_eq_right hs, min_eq_left ht, add_zero]

/-- The values of a two-sided Brownian motion on opposite sides of `0` are uncorrelated. -/
theorem twoSidedMin_neg_left {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : twoSidedMin (-s) t = 0 := by
  unfold twoSidedMin
  rw [neg_neg, max_eq_right (neg_nonpos.2 hs), max_eq_left ht, max_eq_left hs,
    max_eq_right (neg_nonpos.2 ht), min_eq_left ht, min_eq_right hs, add_zero]

/-- The time `s` (forward half, `true`) or `-s` (backward half, `false`). -/
def halfTime : Bool → ℝ≥0 → ℝ
  | true, s => s
  | false, s => -(s : ℝ)

@[simp] theorem halfTime_true (s : ℝ≥0) : halfTime true s = s := rfl

@[simp] theorem halfTime_false (s : ℝ≥0) : halfTime false s = -(s : ℝ) := rfl

/-- The half-line coordinate paths of a two-sided pair: `halfPath (i, true) s = lrCoord i s` and
`halfPath (i, false) s = lrCoord i (-s)` for `s ≥ 0`. -/
def halfPath (k : Fin 2 × Bool) (s : ℝ≥0) : Path2 → ℝ :=
  lrCoord k.1 (halfTime k.2 s)

theorem measurable_halfPath (k : Fin 2 × Bool) (s : ℝ≥0) : Measurable (halfPath k s) :=
  measurable_lrCoord_path k.1 _

/-- The half path `ω ↦ (s ↦ halfPath k s ω)` is measurable for the product σ-algebra on `ℝ≥0 → ℝ`. -/
theorem measurable_halfPaths (k : Fin 2 × Bool) :
    Measurable fun (ω : Path2) (s : ℝ≥0) => halfPath k s ω :=
  Measurable.of_eval fun s => measurable_halfPath k s

theorem continuous_halfPath (k : Fin 2 × Bool) (ω : Path2) : Continuous fun s : ℝ≥0 => halfPath k s ω := by
  obtain ⟨i, b⟩ := k
  cases b
  · exact (continuous_lrCoord_time i ω).comp NNReal.continuous_coe.neg
  · exact (continuous_lrCoord_time i ω).comp NNReal.continuous_coe

/-- The four half paths form a jointly Gaussian family. -/
theorem isGaussianProcess_halfPath {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) :
    IsGaussianProcess (fun p : (_ : Fin 2 × Bool) × ℝ≥0 => halfPath p.1 p.2) μ :=
  hμ.isGaussianProcess.comp_right fun p : (_ : Fin 2 × Bool) × ℝ≥0 => (p.1.1, halfTime p.1.2 p.2)

private theorem isBrownianReal_of_coneComb {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    {α β e : ℝ} (he : |e| = 1) (hαβ : α * α + β * β + (α * β + β * α) * lrCov γ 0 1 = 1)
    {X : ℝ≥0 → Path2 → ℝ} (hX : ∀ v : ℝ≥0, coneComb α β (0 + e * v) 0 =ᵐ[μ] X v)
    (hcont : ∀ ω, Continuous fun v => X v ω) : IsBrownianReal X μ :=
  { toIsPreBrownianReal := (isBrownianReal_coneComb hμ he hαβ 0).toIsPreBrownianReal.congr hX
    cont := ae_of_all _ hcont }

/-- **The halves are Brownian.** For every `γ`, each half path of a two-sided correlated Brownian motion is a
standard real Brownian motion. -/
theorem isBrownianReal_halfPath {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) (k : Fin 2 × Bool) :
    IsBrownianReal (halfPath k) μ := by
  have h0 := ae_forall_lrCoord_zero_eq_zero hμ
  have hc := continuous_halfPath k
  obtain ⟨i, b⟩ := k
  fin_cases i <;> cases b
  · refine isBrownianReal_of_coneComb hμ (α := 1) (β := 0) (e := -1) (by simp) (by simp) (fun v => ?_) hc
    filter_upwards [h0] with ω hω
    simp [coneComb, coneIncr, halfPath, hω]
  · refine isBrownianReal_of_coneComb hμ (α := 1) (β := 0) (e := 1) (by simp) (by simp) (fun v => ?_) hc
    filter_upwards [h0] with ω hω
    simp [coneComb, coneIncr, halfPath, hω]
  · refine isBrownianReal_of_coneComb hμ (α := 0) (β := 1) (e := -1) (by simp) (by simp) (fun v => ?_) hc
    filter_upwards [h0] with ω hω
    simp [coneComb, coneIncr, halfPath, hω]
  · refine isBrownianReal_of_coneComb hμ (α := 0) (β := 1) (e := 1) (by simp) (by simp) (fun v => ?_) hc
    filter_upwards [h0] with ω hω
    simp [coneComb, coneIncr, halfPath, hω]

/-- **Independence of the four halves at `γ = √2`.** For a two-sided correlated Brownian motion with uncorrelated
coordinates, the forward and backward halves of `L` and of `R` are mutually independent. -/
theorem iIndepFun_halfPath {μ : Measure Path2} (hμ : IsCorrelatedBM2 (√2) μ) :
    iIndepFun (fun (k : Fin 2 × Bool) (ω : Path2) (s : ℝ≥0) => halfPath k s ω) μ := by
  refine IsGaussianProcess.iIndepFun_of_covariance_eq_zero (S := fun _ => ℝ≥0)
    (X := fun k s => halfPath k s) (isGaussianProcess_halfPath hμ)
    (fun k s => (measurable_halfPath k s).aemeasurable) ?_
  rintro ⟨i, b⟩ ⟨j, b'⟩ hne s t
  show cov[lrCoord i (halfTime b s), lrCoord j (halfTime b' t); μ] = 0
  rw [hμ.covariance_eq]
  by_cases hij : i = j
  · subst hij
    have hbb : b ≠ b' := fun h => hne (congrArg (Prod.mk i) h)
    cases b <;> cases b'
    · exact absurd rfl hbb
    · rw [halfTime_false, halfTime_true, twoSidedMin_neg_left (NNReal.coe_nonneg s) (NNReal.coe_nonneg t),
        mul_zero]
    · rw [halfTime_false, halfTime_true, twoSidedMin_neg_right (NNReal.coe_nonneg s) (NNReal.coe_nonneg t),
        mul_zero]
    · exact absurd rfl hbb
  · rw [lrCov_sqrt_two_of_ne hij, zero_mul]

/-- **Product law of the four halves at `γ = √2`.** The joint law of the four half paths is the product of their
laws. -/
theorem map_halfPaths_eq_pi {μ : Measure Path2} (hμ : IsCorrelatedBM2 (√2) μ) :
    μ.map (fun ω (k : Fin 2 × Bool) (s : ℝ≥0) => halfPath k s ω) =
      Measure.pi fun k => μ.map (fun ω (s : ℝ≥0) => halfPath k s ω) := by
  have := hμ.isProbabilityMeasure
  exact (iIndepFun_iff_map_fun_eq_pi_map fun k => (measurable_halfPaths k).aemeasurable).1
    (iIndepFun_halfPath hμ)

end LatticeProb.CorrelatedBM
