/-
The Herbst argument: the Gaussian log-Sobolev inequality implies the exponential
moment bound for a Lipschitz functional.

`LatticeProb.GaussianLogSobolev n` bounds the entropy of a positive density with
`C`-Lipschitz logarithm by `C²/2`.  Applying it to the tilted density
`h_λ = exp(λ (f - ∫f)) / ∫ exp(λ (f - ∫f))`, whose logarithm is `λ f` up to a
constant and hence `λ L`-Lipschitz when `f` is `L`-Lipschitz, gives the
differential inequality `(d/dλ) log M(λ) ≤ λ L²` for the moment generating
function `M(λ) = ∫ exp(λ (f - ∫f))`.  Since `M(0) = 1`, integrating gives
`M(λ) ≤ exp(λ² L² / 2)`, which is `LatticeProb.GaussianHerbstBound n`.

This module proves the tilt, its positivity, its normalization, the Lipschitz
continuity of its logarithm, the entropy bound that the log-Sobolev inequality
gives for it, and the resulting differential inequality `(log M)' ≤ λ L²` for
the moment generating function `M`.  The integration of that inequality from
`M(0) = 1` is the remaining step.

The argument is the classical one of Herbst (1975), as presented in Ledoux,
*The Concentration of Measure Phenomenon*, Section 5.1.
-/
import LatticeProb.External.GaussianLogSobolev
import LatticeProb.Prob.GaussianConcentration
import LatticeProb.Prob.ConvexProduct

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProb

/-- The tilted density of the Herbst argument: `h_λ = exp(λ (f - ∫f)) / M(λ)`,
where `M(λ) = ∫ exp(λ (f - ∫f))` is the moment generating function of `f - ∫f`.
It is positive and integrates to `1`. -/
noncomputable def herbstTilt (n : ℕ) (f : (Fin n → ℝ) → ℝ) (lam : ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x => Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
    / ∫ x, Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)

/-- The tilted density is positive. -/
theorem herbstTilt_pos (n : ℕ) (f : (Fin n → ℝ) → ℝ) (lam : ℝ)
    (hM : 0 < ∫ x, Real.exp (lam * (f x - ∫ y, f y
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) :
    ∀ x, 0 < herbstTilt n f lam x := by
  intro x
  unfold herbstTilt
  exact div_pos (Real.exp_pos _) hM

/-- The tilted density integrates to `1`. -/
theorem herbstTilt_integral (n : ℕ) (f : (Fin n → ℝ) → ℝ) (lam : ℝ)
    (hM : ∫ x, Real.exp (lam * (f x - ∫ y, f y
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) ≠ 0) :
    ∫ x, herbstTilt n f lam x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 1 := by
  unfold herbstTilt
  rw [integral_div, div_self hM]

/-- The logarithm of the tilted density is `λ f` up to an additive constant, hence
`λ K`-Lipschitz when `f` is `K`-Lipschitz. -/
theorem herbstTilt_log_lipschitz (n : ℕ) (f : (Fin n → ℝ) → ℝ) (K lam : ℝ)
    (hK : 0 ≤ K) (lam0 : 0 ≤ lam) (hf : LipschitzWith ⟨K, hK⟩ f)
    (hM : 0 < ∫ x, Real.exp (lam * (f x - ∫ y, f y
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) :
    LipschitzWith ⟨lam * K, mul_nonneg lam0 hK⟩ (fun x => Real.log (herbstTilt n f lam x)) := by
  have hconst : ∀ x, Real.log (herbstTilt n f lam x)
      = lam * f x - lam * (∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        - Real.log (∫ x, Real.exp (lam * (f x - ∫ y, f y
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) := by
    intro x
    unfold herbstTilt
    rw [Real.log_div (Real.exp_ne_zero _) hM.ne', Real.log_exp]
    ring
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rw [hconst x, hconst y, Real.dist_eq]
  have hdiff : (lam * f x - lam * (∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        - Real.log (∫ x, Real.exp (lam * (f x - ∫ y, f y
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      - (lam * f y - lam * (∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        - Real.log (∫ x, Real.exp (lam * (f x - ∫ y, f y
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      = lam * (f x - f y) := by ring
  rw [hdiff, abs_mul, abs_of_nonneg lam0]
  have hd := hf.dist_le_mul x y
  rw [Real.dist_eq] at hd
  have hd' : |f x - f y| ≤ K * dist x y := hd
  calc lam * |f x - f y| ≤ lam * (K * dist x y) :=
        mul_le_mul_of_nonneg_left hd' lam0
    _ = (lam * K) * dist x y := by ring


/-- The centred functional `g = f - ∫f` is Lipschitz with the same constant as `f`. -/
theorem lipschitzWith_sub_integral (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : LipschitzWith ⟨L, hL⟩ f) :
    LipschitzWith ⟨L, hL⟩ (fun x => f x - ∫ y, f y
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have hd := hf.dist_le_mul x y
  rw [Real.dist_eq] at hd ⊢
  simpa using hd

/-- The exponential of a multiple of the centred functional is integrable. -/
theorem integrable_exp_sub_integral (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L t : ℝ) (hL : 0 < L)
    (hf : LipschitzWith ⟨L, hL.le⟩ f) :
    Integrable (fun x => Real.exp (t * (f x - ∫ y, f y
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
  integrable_exp_lipschitz_gaussian n f L hL hf t

/-- The centred functional times its exponential is integrable. -/
theorem integrable_mul_exp_sub_integral (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L t : ℝ) (hL : 0 < L)
    (hf : LipschitzWith ⟨L, hL.le⟩ f) :
    Integrable (fun x => (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
      * Real.exp (t * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  set g : (Fin n → ℝ) → ℝ := fun x => f x - ∫ y, f y
    ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) with hg
  have hgL : LipschitzWith ⟨L, hL.le⟩ g := lipschitzWith_sub_integral n f L hL.le hf
  have h1 : Integrable (fun x => Real.exp ((|t| + 1) * g x))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    integrable_exp_lipschitz_gaussian n f L hL hf (|t| + 1)
  have h2 : Integrable (fun x => Real.exp (-(|t| + 1) * g x))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    integrable_exp_lipschitz_gaussian n f L hL hf (-(|t| + 1))
  have hsum : Integrable (fun x => Real.exp ((|t| + 1) * g x)
      + Real.exp (-(|t| + 1) * g x)) (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    h1.add h2
  refine hsum.mono' ?_ ?_
  · exact ((hgL.continuous.measurable.mul
      (Real.measurable_exp.comp (measurable_const.mul hgL.continuous.measurable)))).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    have hexp : (0 : ℝ) < Real.exp (t * g x) := Real.exp_pos _
    rw [abs_of_pos hexp]
    have hle : |g x| ≤ Real.exp |g x| :=
      le_trans (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1)) (Real.add_one_le_exp _)
    have hexp_le : Real.exp (t * g x) ≤ Real.exp (|t| * |g x|) := by
      rw [Real.exp_le_exp]
      calc t * g x ≤ |t * g x| := le_abs_self _
        _ = |t| * |g x| := by rw [abs_mul]
    have h1' : |g x| * Real.exp (t * g x) ≤ Real.exp |g x| * Real.exp (|t| * |g x|) :=
      le_trans (mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le)
        (mul_le_mul_of_nonneg_left hexp_le (Real.exp_pos _).le)
    have h2' : Real.exp |g x| * Real.exp (|t| * |g x|)
        = Real.exp ((|t| + 1) * |g x|) := by
      rw [← Real.exp_add]; ring_nf
    have h3' : Real.exp ((|t| + 1) * |g x|) ≤ Real.exp ((|t| + 1) * g x)
        + Real.exp (-(|t| + 1) * g x) := by
      rcases le_total 0 (g x) with hgx | hgx
      · rw [abs_of_nonneg hgx]
        exact le_add_of_nonneg_right (Real.exp_pos _).le
      · rw [abs_of_nonpos hgx]
        rw [show (|t| + 1) * -g x = -(|t| + 1) * g x by ring]
        exact le_add_of_nonneg_left (Real.exp_pos _).le
    calc |g x| * Real.exp (t * g x)
        ≤ Real.exp |g x| * Real.exp (|t| * |g x|) := h1'
      _ = Real.exp ((|t| + 1) * |g x|) := h2'
      _ ≤ _ := h3'

/-- The moment generating function of the centred functional is positive. -/
theorem mgf_centred_pos (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L t : ℝ) (hL : 0 < L)
    (hf : LipschitzWith ⟨L, hL.le⟩ f) :
    0 < ∫ x, Real.exp (t * (f x - ∫ y, f y
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  haveI : IsProbabilityMeasure (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    isProbabilityMeasure_pi_gaussianReal n
  have hint := integrable_exp_sub_integral n f L t hL hf
  have hsupp : Function.support (fun x => Real.exp (t * (f x - ∫ y, f y
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))) = Set.univ := by
    ext x
    simp
  rw [integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le) hint, hsupp]
  haveI : IsProbabilityMeasure (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    isProbabilityMeasure_pi_gaussianReal n
  simp


/-- The entropy of the tilted density is at most `(λ L)² / 2`, by the Gaussian
log-Sobolev inequality applied to `herbstTilt`. -/
theorem herbstTilt_entropy_le (n : ℕ) (h : GaussianLogSobolev n) (f : (Fin n → ℝ) → ℝ)
    (L lam : ℝ) (hL : 0 < L) (hf : LipschitzWith ⟨L, hL.le⟩ f) (hlam : 0 < lam) :
    ∫ x, herbstTilt n f lam x * Real.log (herbstTilt n f lam x)
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
      ≤ (lam * L) ^ 2 / 2 := by
  have hMpos := mgf_centred_pos n f L lam hL hf
  have hpos := herbstTilt_pos n f lam hMpos
  have hint : Integrable (herbstTilt n f lam)
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
    unfold herbstTilt
    exact (integrable_exp_sub_integral n f L lam hL hf).div_const _
  have hintlog : Integrable (fun x => herbstTilt n f lam x * Real.log (herbstTilt n f lam x))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
    have hlog : ∀ x, Real.log (herbstTilt n f lam x)
        = lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
          - Real.log (∫ x, Real.exp (lam * (f x - ∫ y, f y
              ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) := by
      intro x
      unfold herbstTilt
      rw [Real.log_div (Real.exp_ne_zero _) hMpos.ne', Real.log_exp]
    have hsplit : (fun x => herbstTilt n f lam x * Real.log (herbstTilt n f lam x))
        = fun x => (lam * (herbstTilt n f lam x
              * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
            - (Real.log (∫ x, Real.exp (lam * (f x - ∫ y, f y
                ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
              ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))) * herbstTilt n f lam x) := by
      funext x
      rw [hlog x]; ring
    rw [hsplit]
    have hB : Integrable (fun x => herbstTilt n f lam x
        * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
      have hbase : Integrable (fun x => (f x - ∫ y, f y
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
          * Real.exp (lam * (f x - ∫ y, f y
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))))
          (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
        integrable_mul_exp_sub_integral n f L lam hL hf
      refine (hbase.div_const (∫ x, Real.exp (lam * (f x - ∫ y, f y
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))).congr ?_
      filter_upwards with x
      simp only [herbstTilt]
      ring
    have hA : Integrable (fun x => lam * (herbstTilt n f lam x
        * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))))
        (Measure.pi fun _ : Fin n => gaussianReal 0 1) := hB.const_mul lam
    exact hA.sub (hint.const_mul _)
  have hnorm := herbstTilt_integral n f lam hMpos.ne'
  have hlip := herbstTilt_log_lipschitz n f L lam hL.le hlam.le hf hMpos
  exact h (herbstTilt n f lam) hpos hint hintlog hnorm ⟨lam * L, mul_nonneg hlam.le hL.le⟩ hlip


end LatticeProb
