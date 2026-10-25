module

/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Gaussian/ConcentrationLip.lean.
-/
public import LatticeProb.Prob.GaussMollify
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Basic

@[expose] public section

/-!
# Gaussian concentration for Lipschitz functions

For a standard Gaussian vector `x` of a finite-dimensional real inner product space `E`
(for example `EuclideanSpace ℝ (Fin n)`) and an `L`-Lipschitz function `F : E → ℝ`, with
`L : ℝ≥0`:

* `E exp (t (F - E F)) ≤ exp (t² L² / 2)` for all real `t` (`mgf_le_of_lipschitz`);
* `P(F - E F ≥ u) ≤ exp (-u² / (2 L²))` and `P(F - E F ≤ -u) ≤ exp (-u² / (2 L²))` for `u ≥ 0`
  (`tail_le_of_lipschitz`, `lowerTail_le_of_lipschitz`).

No boundedness of `F` is assumed. The bounded case is `GaussConc.mgf_le_of_lipschitz_bdd`, proved
by mollification in `LatticeProb.Prob.GaussMollify`. For general `F`, the truncations
`max (min F m) (-m)` are `L`-Lipschitz and bounded by `m`. Their centred MGFs satisfy the bound,
Fatou's lemma passes it to the limit `m → ∞`, and Chernoff's bound gives the tails.
With `L = 0` the right-hand sides equal `1`, since Lean's convention gives `u ^ 2 / 0 = 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal

namespace LatticeProb.GaussConc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {F : E → ℝ} {L : ℝ≥0}

/-- A Lipschitz function of a standard Gaussian vector is integrable. -/
theorem integrable_of_lipschitz (hF : LipschitzWith L F) : Integrable F (stdGaussian E) := by
  refine Integrable.mono' ((integrable_const |F 0|).add
    ((IsGaussian.integrable_id.norm).const_mul (L : ℝ))) hF.continuous.aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  have := hF.dist_le_mul x 0
  rw [Real.dist_eq, dist_zero_right] at this
  rw [Real.norm_eq_abs]
  have h2 := abs_sub_abs_le_abs_sub (F x) (F 0)
  simp only [Pi.add_apply, id]
  linarith

/-- The truncation of `F` to the interval `[-m, m]`, namely `max (min (F x) m) (-m)`. -/
def truncFun (F : E → ℝ) (m : ℕ) (x : E) : ℝ := max (min (F x) m) (-(m : ℝ))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Truncation preserves the Lipschitz constant. -/
lemma lipschitzWith_truncFun (hF : LipschitzWith L F) (m : ℕ) : LipschitzWith L (truncFun F m) :=
  (hF.min_const _).max_const _

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
/-- The truncation of `F` to `[-m, m]` is bounded by `m`. -/
lemma abs_truncFun_le_nat (m : ℕ) (x : E) : |truncFun F m x| ≤ m := by
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  exact abs_le.2 ⟨le_max_right _ _, max_le (min_le_right _ _) (by linarith)⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
/-- The truncation of `F` to `[-m, m]` does not increase the absolute value. -/
lemma abs_truncFun_le (m : ℕ) (x : E) : |truncFun F m x| ≤ |F x| := by
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 := neg_abs_le (F x)
  have h2 := le_abs_self (F x)
  have h3 := abs_nonneg (F x)
  refine abs_le.2 ⟨le_max_of_le_left (le_min h1 (by linarith)), max_le ((min_le_left _ _).trans h2)
    (by linarith)⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
/-- The truncations of `F` converge pointwise to `F` as `m → ∞`. -/
lemma tendsto_truncFun (x : E) : Tendsto (fun m => truncFun F m x) atTop (𝓝 (F x)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈|F x|⌉₊] with m hm
  have hm' : |F x| ≤ m := (Nat.le_ceil _).trans (by exact_mod_cast hm)
  have := abs_le.1 hm'
  simp only [truncFun]
  rw [min_eq_left this.2, max_eq_left this.1]

/-- **Exponential moment bound** (lower-integral form) for Lipschitz functions. -/
theorem lintegral_exp_le_of_lipschitz (hF : LipschitzWith L F) (t : ℝ) :
    ∫⁻ x, ENNReal.ofReal (exp (t * (F x - ∫ y, F y ∂(stdGaussian E)))) ∂(stdGaussian E) ≤
      ENNReal.ofReal (exp (t ^ 2 * (L : ℝ) ^ 2 / 2)) := by
  set μ := stdGaussian E
  set c : ℕ → ℝ := fun m => ∫ y, truncFun F m y ∂μ
  have hc : Tendsto c atTop (𝓝 (∫ y, F y ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => |F x|)
      (fun m => (lipschitzWith_truncFun hF m).continuous.aestronglyMeasurable)
      (integrable_of_lipschitz hF).abs
      (fun m => ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_truncFun_le m x)
      (ae_of_all _ tendsto_truncFun)
  have hmeas : ∀ m, Measurable fun x => ENNReal.ofReal (exp (t * (truncFun F m x - c m))) :=
    fun m => ENNReal.measurable_ofReal.comp ((continuous_const.mul
      ((lipschitzWith_truncFun hF m).continuous.sub continuous_const)).rexp).measurable
  have hlim : ∀ x, Tendsto (fun m => ENNReal.ofReal (exp (t * (truncFun F m x - c m)))) atTop
      (𝓝 (ENNReal.ofReal (exp (t * (F x - ∫ y, F y ∂μ))))) := fun x =>
    (ENNReal.continuous_ofReal.tendsto _).comp
      ((((tendsto_truncFun x).sub hc).const_mul t).rexp)
  calc _ = ∫⁻ x, liminf (fun m => ENNReal.ofReal (exp (t * (truncFun F m x - c m)))) atTop ∂μ :=
        lintegral_congr fun x => (hlim x).liminf_eq.symm
    _ ≤ liminf (fun m => ∫⁻ x, ENNReal.ofReal (exp (t * (truncFun F m x - c m))) ∂μ) atTop :=
        lintegral_liminf_le' fun m => (hmeas m).aemeasurable
    _ ≤ _ := by
        refine liminf_le_of_frequently_le' (Frequently.of_forall fun m => ?_)
        have hb := mgf_le_of_lipschitz_bdd (lipschitzWith_truncFun hF m)
          (abs_truncFun_le_nat (F := F) m) t
        have hint : Integrable (fun x => exp (t * (truncFun F m x - c m))) μ :=
          Integrable.of_bound ((continuous_const.mul ((lipschitzWith_truncFun hF m).continuous.sub
            continuous_const)).rexp).aestronglyMeasurable (exp (|t| * (m + m)))
            (ae_of_all _ fun x => by
              rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
              refine exp_le_exp.2 ((le_abs_self _).trans ?_)
              rw [abs_mul]
              refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add
                (abs_truncFun_le_nat m x) ?_)) (abs_nonneg _)
              rw [← Real.norm_eq_abs]
              refine (norm_integral_le_of_norm_le (integrable_const (m : ℝ))
                (ae_of_all _ fun y => by
                  rw [Real.norm_eq_abs]; exact abs_truncFun_le_nat m y)).trans ?_
              simp)
        rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => (exp_pos _).le)]
        exact ENNReal.ofReal_le_ofReal hb

/-- `exp (t (F - E F))` is integrable for Lipschitz `F`. -/
theorem integrable_exp_of_lipschitz (hF : LipschitzWith L F) (t : ℝ) :
    Integrable (fun x => exp (t * (F x - ∫ y, F y ∂(stdGaussian E)))) (stdGaussian E) := by
  have hm : AEStronglyMeasurable (fun x => exp (t * (F x - ∫ y, F y ∂(stdGaussian E))))
      (stdGaussian E) :=
    ((continuous_const.mul (hF.continuous.sub continuous_const)).rexp).aestronglyMeasurable
  exact (lintegral_ofReal_ne_top_iff_integrable hm (ae_of_all _ fun x => (exp_pos _).le)).1
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_exp_le_of_lipschitz hF t))

/-- **Sharp sub-Gaussian MGF bound**: `E exp (t (F - E F)) ≤ exp (t² L² / 2)` for `L`-Lipschitz
`F` and every real `t`. -/
theorem mgf_le_of_lipschitz (hF : LipschitzWith L F) (t : ℝ) :
    mgf (fun x => F x - ∫ y, F y ∂(stdGaussian E)) (stdGaussian E) t ≤
      exp (t ^ 2 * (L : ℝ) ^ 2 / 2) := by
  rw [mgf, ← ENNReal.ofReal_le_ofReal_iff (exp_pos _).le,
    ofReal_integral_eq_lintegral_ofReal (integrable_exp_of_lipschitz hF t)
      (ae_of_all _ fun x => (exp_pos _).le)]
  exact lintegral_exp_le_of_lipschitz hF t

/-- **Gaussian concentration, upper tail**: `P(F - E F ≥ u) ≤ exp (-u² / (2 L²))` for
`L`-Lipschitz `F` and `u ≥ 0`. -/
theorem tail_le_of_lipschitz (hF : LipschitzWith L F) {u : ℝ} (hu : 0 ≤ u) :
    (stdGaussian E).real {x | u ≤ F x - ∫ y, F y ∂(stdGaussian E)} ≤
      exp (-u ^ 2 / (2 * (L : ℝ) ^ 2)) := by
  rcases eq_zero_or_pos L with hL | hL
  · rw [hL]
    simp
  · have hL' : (0 : ℝ) < L := hL
    have ht : 0 ≤ u / (L : ℝ) ^ 2 := by positivity
    refine (measure_ge_le_exp_mul_mgf u ht (integrable_exp_of_lipschitz hF _)).trans ?_
    refine (mul_le_mul_of_nonneg_left (mgf_le_of_lipschitz hF _) (exp_pos _).le).trans ?_
    rw [← exp_add]
    refine le_of_eq (congrArg exp ?_)
    field_simp
    ring

/-- **Gaussian concentration, lower tail**: `P(F - E F ≤ -u) ≤ exp (-u² / (2 L²))` for
`L`-Lipschitz `F` and `u ≥ 0`. -/
theorem lowerTail_le_of_lipschitz (hF : LipschitzWith L F) {u : ℝ} (hu : 0 ≤ u) :
    (stdGaussian E).real {x | F x - ∫ y, F y ∂(stdGaussian E) ≤ -u} ≤
      exp (-u ^ 2 / (2 * (L : ℝ) ^ 2)) := by
  have hF' : LipschitzWith L fun x => -F x :=
    LipschitzWith.of_dist_le_mul fun x y => by rw [dist_neg_neg]; exact hF.dist_le_mul x y
  have h := tail_le_of_lipschitz hF' hu
  rw [integral_neg] at h
  convert h using 3
  ext x
  constructor <;> intro hx <;> linarith

/-! ### Nonvacuity examples -/

namespace GaussLipConcentrationExample

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace NNReal

/-- The norm `x ↦ ‖x‖` on `EuclideanSpace ℝ (Fin 2)` is `1`-Lipschitz, and unbounded. -/
theorem lipschitzWith_norm_euclidean :
    LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
  exact abs_norm_sub_norm_le x y

/-- **Gaussian tail bound for the norm.** For a standard Gaussian vector `X` on
`EuclideanSpace ℝ (Fin 2)` and `u ≥ 0`, `P(‖X‖ - E‖X‖ ≥ u) ≤ exp (-u² / (2 · 1²))`, where `1`
is the Lipschitz constant of `‖·‖`. -/
theorem tail_norm_euclidean_le {u : ℝ} (hu : 0 ≤ u) :
    (stdGaussian (EuclideanSpace ℝ (Fin 2))).real
        {x | u ≤ ‖x‖ - ∫ y, ‖y‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin 2)))} ≤
      exp (-u ^ 2 / (2 * ((1 : ℝ≥0) : ℝ) ^ 2)) :=
  tail_le_of_lipschitz lipschitzWith_norm_euclidean hu

/-- The linear functional `x ↦ ⟪v, x⟫` on `EuclideanSpace ℝ (Fin 2)` is `‖v‖₊`-Lipschitz. -/
theorem lipschitzWith_inner_left (v : EuclideanSpace ℝ (Fin 2)) :
    LipschitzWith ‖v‖₊ (fun x => ⟪v, x⟫) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h : |⟪v, x⟫ - ⟪v, y⟫| ≤ ‖v‖ * dist x y := by
    rw [← inner_sub_right, dist_eq_norm]
    exact abs_real_inner_le_norm _ _
  rw [Real.dist_eq, coe_nnnorm]
  exact h

/-- **MGF bound for a linear functional.** For a standard Gaussian vector `X` on
`EuclideanSpace ℝ (Fin 2)`, every `v` and every real `t`,
`E exp (t (⟪v, X⟫ - E ⟪v, X⟫)) ≤ exp (t² ‖v‖² / 2)`. -/
theorem mgf_inner_left_le (v : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    mgf (fun x => ⟪v, x⟫ - ∫ y, ⟪v, y⟫ ∂(stdGaussian (EuclideanSpace ℝ (Fin 2))))
        (stdGaussian (EuclideanSpace ℝ (Fin 2))) t ≤ exp (t ^ 2 * ‖v‖ ^ 2 / 2) := by
  have h := mgf_le_of_lipschitz (lipschitzWith_inner_left v) t
  rwa [coe_nnnorm] at h

end GaussLipConcentrationExample

end LatticeProb.GaussConc
