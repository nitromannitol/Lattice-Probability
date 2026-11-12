/-
# The Gaussian logarithmic Sobolev inequality for Lipschitz exponential tilts

For the standard Gaussian measure `γ` of a finite-dimensional real inner product space and a
`K`-Lipschitz `g`,

  `∫ e^g g dγ ≤ (∫ e^g dγ) log (∫ e^g dγ) + (K² / 2) ∫ e^g dγ`

(`integral_exp_mul_le_of_lipschitz`). The `C¹` case is
`LatticeProb.GaussLSI.integral_mul_log_le_of_gradient`. A bounded Lipschitz `g` is the pointwise
limit of its mollifications `LatticeProb.GaussConc.mollify (bumpSeq k) g`, which are `C¹`,
`K`-Lipschitz and bounded by the same constant (`integral_exp_mul_le_of_lipschitz_bdd`); a general
Lipschitz `g` is the pointwise limit of its truncations `max (min g m) (-m)`, dominated by
`e^{|g|} |g|`. Both limits are taken by dominated convergence.
-/
import LatticeProb.Prob.GaussianLogSobolevEntropy
import LatticeProb.Prob.GaussMollify

noncomputable section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped NNReal

namespace LatticeProb.GaussLSI

open GaussConc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The right-hand side of the inequality is continuous in the two integrals. -/
theorem tendsto_rhs {Z : ℕ → ℝ} {Z₀ : ℝ} (hZ₀ : 0 < Z₀) (hZ : Tendsto Z atTop (𝓝 Z₀)) (c : ℝ) :
    Tendsto (fun k => Z k * Real.log (Z k) + c * Z k) atTop
      (𝓝 (Z₀ * Real.log Z₀ + c * Z₀)) :=
  (hZ.mul (hZ.log hZ₀.ne')).add (hZ.const_mul c)

/-- **The `C¹` case** in the form `∫ e^g g ≤ Z log Z + (K² / 2) Z`. -/
theorem integral_exp_mul_le_of_contDiff {g : E → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (hgc : ContDiff ℝ 1 g) :
    ∫ x, Real.exp (g x) * g x ∂(stdGaussian E)
      ≤ (∫ x, Real.exp (g x) ∂(stdGaussian E)) * Real.log (∫ x, Real.exp (g x) ∂(stdGaussian E))
        + (K : ℝ) ^ 2 / 2 * ∫ x, Real.exp (g x) ∂(stdGaussian E) := by
  have hgd : ∀ x, HasGradientAt g (gradient g x) x := fun x =>
    ((hgc.differentiable one_ne_zero) x).hasGradientAt
  have hg'c : Continuous (gradient g) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hgc.continuous_fderiv one_ne_zero)
  have hg'b : ∀ x, ‖gradient g x‖ ≤ K := fun x => by
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hg
  simpa only [Real.log_exp] using integral_mul_log_le_of_gradient hg hgd hg'c hg'b

/-- **The bounded Lipschitz case**, by mollification. -/
theorem integral_exp_mul_le_of_lipschitz_bdd {g : E → ℝ} {K : ℝ≥0} {M : ℝ}
    (hg : LipschitzWith K g) (hM : ∀ x, |g x| ≤ M) :
    ∫ x, Real.exp (g x) * g x ∂(stdGaussian E)
      ≤ (∫ x, Real.exp (g x) ∂(stdGaussian E)) * Real.log (∫ x, Real.exp (g x) ∂(stdGaussian E))
        + (K : ℝ) ^ 2 / 2 * ∫ x, Real.exp (g x) ∂(stdGaussian E) := by
  have hgc := hg.continuous
  set gk : ℕ → E → ℝ := fun k => mollify (bumpSeq k) g
  have hgkc : ∀ k, Continuous (gk k) := fun k => (contDiff_mollify _ hgc).continuous
  have hgkb : ∀ k x, |gk k x| ≤ M := fun k x => abs_mollify_le _ hgc hM x
  have hlim : ∀ x, Tendsto (fun k => gk k x) atTop (𝓝 (g x)) := fun x =>
    ContDiffBump.convolution_tendsto_right_of_continuous (μ := Measure.addHaar)
      tendsto_bumpSeq_rOut hgc x
  have hexpb : ∀ k x, |Real.exp (gk k x)| ≤ Real.exp M := fun k x => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hgkb k x))
  have hZ : Tendsto (fun k => ∫ x, Real.exp (gk k x) ∂(stdGaussian E)) atTop
      (𝓝 (∫ x, Real.exp (g x) ∂(stdGaussian E))) :=
    tendsto_integral_of_dominated_convergence (fun _ => Real.exp M)
      (fun k => (hgkc k).rexp.aestronglyMeasurable) (integrable_const _)
      (fun k => ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hexpb k x)
      (ae_of_all _ fun x => (hlim x).rexp)
  have hL : Tendsto (fun k => ∫ x, Real.exp (gk k x) * gk k x ∂(stdGaussian E)) atTop
      (𝓝 (∫ x, Real.exp (g x) * g x ∂(stdGaussian E))) :=
    tendsto_integral_of_dominated_convergence (fun _ => Real.exp M * M)
      (fun k => ((hgkc k).rexp.mul (hgkc k)).aestronglyMeasurable) (integrable_const _)
      (fun k => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hexpb k x) (hgkb k x) (abs_nonneg _) (Real.exp_pos _).le)
      (ae_of_all _ fun x => (hlim x).rexp.mul (hlim x))
  have hZ₀ : 0 < ∫ x, Real.exp (g x) ∂(stdGaussian E) :=
    integral_exp_pos (Integrable.of_bound hgc.rexp.aestronglyMeasurable (Real.exp M)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hM x))))
  refine le_of_tendsto_of_tendsto' hL (tendsto_rhs hZ₀ hZ _) fun k => ?_
  exact integral_exp_mul_le_of_contDiff (lipschitzWith_mollify _ hg hM)
    (contDiff_mollify _ hgc)

/-- **The Gaussian logarithmic Sobolev inequality for Lipschitz exponential tilts.** -/
theorem integral_exp_mul_le_of_lipschitz {g : E → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    ∫ x, Real.exp (g x) * g x ∂(stdGaussian E)
      ≤ (∫ x, Real.exp (g x) ∂(stdGaussian E)) * Real.log (∫ x, Real.exp (g x) ∂(stdGaussian E))
        + (K : ℝ) ^ 2 / 2 * ∫ x, Real.exp (g x) ∂(stdGaussian E) := by
  have hgc := hg.continuous
  have hK := K.coe_nonneg
  set gm : ℕ → E → ℝ := fun m x => max (min (g x) m) (-(m : ℝ))
  have hm0 : ∀ m : ℕ, (0 : ℝ) ≤ m := fun m => Nat.cast_nonneg m
  have hgm : ∀ m, LipschitzWith K (gm m) := fun m => (hg.min_const _).max_const _
  have hgmb : ∀ m x, |gm m x| ≤ m := fun m x =>
    abs_le.2 ⟨le_max_right _ _, max_le (min_le_right _ _) (by linarith [hm0 m])⟩
  have hgmg : ∀ m x, |gm m x| ≤ |g x| := fun m x =>
    abs_le.2 ⟨le_max_of_le_left (le_min (neg_abs_le _) (by linarith [hm0 m, abs_nonneg (g x)])),
      max_le ((min_le_left _ _).trans (le_abs_self _)) (by linarith [hm0 m, abs_nonneg (g x)])⟩
  have hlim : ∀ x, Tendsto (fun m => gm m x) atTop (𝓝 (g x)) := fun x => by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈|g x|⌉₊] with m hm
    have h1 : |g x| ≤ m := (Nat.le_ceil _).trans (Nat.cast_le.mpr hm)
    simp only [gm]
    rw [min_eq_left ((le_abs_self _).trans h1), max_eq_left (by linarith [neg_abs_le (g x)])]
  have hgb : ∀ x, |g x| ≤ |g 0| + K * ‖x‖ := fun x => by
    have h := hg.dist_le_mul x 0
    rw [Real.dist_eq, dist_zero_right] at h
    have := abs_sub_abs_le_abs_sub (g x) (g 0)
    linarith
  have hexpb : ∀ m x, |Real.exp (gm m x)| ≤ Real.exp |g 0| * Real.exp (K * ‖x‖) := fun m x => by
    rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    exact Real.exp_le_exp.mpr (((le_abs_self _).trans (hgmg m x)).trans (hgb x))
  have hprodb : ∀ m x, |Real.exp (gm m x) * gm m x|
      ≤ Real.exp |g 0| * (|g 0| + K) * Real.exp (((K : ℝ) + 1) * ‖x‖) := fun m x => by
    rw [abs_mul]
    have h2 : |gm m x| ≤ (|g 0| + K) * Real.exp ‖x‖ := by
      have h3 := (hgmg m x).trans (hgb x)
      have h4 := mul_le_mul_of_nonneg_left (Real.add_one_le_exp ‖x‖)
        (add_nonneg (abs_nonneg (g 0)) hK)
      have h5 := mul_nonneg (abs_nonneg (g 0)) (norm_nonneg x)
      nlinarith
    calc |Real.exp (gm m x)| * |gm m x|
        ≤ (Real.exp |g 0| * Real.exp (K * ‖x‖)) * ((|g 0| + K) * Real.exp ‖x‖) :=
          mul_le_mul (hexpb m x) h2 (abs_nonneg _) (by positivity)
      _ = Real.exp |g 0| * (|g 0| + K) * Real.exp (((K : ℝ) + 1) * ‖x‖) := by
          rw [show ((K : ℝ) + 1) * ‖x‖ = K * ‖x‖ + ‖x‖ by ring, Real.exp_add]; ring
  have hZ : Tendsto (fun m => ∫ x, Real.exp (gm m x) ∂(stdGaussian E)) atTop
      (𝓝 (∫ x, Real.exp (g x) ∂(stdGaussian E))) :=
    tendsto_integral_of_dominated_convergence (fun x => Real.exp |g 0| * Real.exp (K * ‖x‖))
      (fun m => (hgm m).continuous.rexp.aestronglyMeasurable)
      ((Kahane.integrable_exp_mul_norm_stdGaussian (E := E) K).const_mul _)
      (fun m => ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hexpb m x)
      (ae_of_all _ fun x => (hlim x).rexp)
  have hL : Tendsto (fun m => ∫ x, Real.exp (gm m x) * gm m x ∂(stdGaussian E)) atTop
      (𝓝 (∫ x, Real.exp (g x) * g x ∂(stdGaussian E))) :=
    tendsto_integral_of_dominated_convergence
      (fun x => Real.exp |g 0| * (|g 0| + K) * Real.exp (((K : ℝ) + 1) * ‖x‖))
      (fun m => ((hgm m).continuous.rexp.mul (hgm m).continuous).aestronglyMeasurable)
      ((Kahane.integrable_exp_mul_norm_stdGaussian (E := E) _).const_mul _)
      (fun m => ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hprodb m x)
      (ae_of_all _ fun x => (hlim x).rexp.mul (hlim x))
  have hZ₀ : 0 < ∫ x, Real.exp (g x) ∂(stdGaussian E) :=
    integral_exp_pos (Kahane.integrable_of_le_exp (f := fun x => Real.exp (g x))
      (A := Real.exp (g 0)) (B := K) hgc.rexp.aestronglyMeasurable fun x => by
        rw [abs_of_pos (Real.exp_pos _)]; exact exp_le_of_lipschitz hg x)
  refine le_of_tendsto_of_tendsto' hL (tendsto_rhs hZ₀ hZ _) fun m => ?_
  exact integral_exp_mul_le_of_lipschitz_bdd (hgm m) (hgmb m)

end LatticeProb.GaussLSI
