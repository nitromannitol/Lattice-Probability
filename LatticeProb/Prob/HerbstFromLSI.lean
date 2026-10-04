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
import LatticeProb.Prob.ExponentialMoments

noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

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


/-- **The entropy form of the Herbst differential inequality.**  With
`M(λ) = ∫ exp(λ (f - ∫f))`, the entropy of the tilted density is
`λ M'(λ)/M(λ) - log M(λ)`, and the Gaussian log-Sobolev inequality bounds it by
`(λ L)²/2`.  This is the differential inequality the Herbst argument integrates:
it says `(log M / λ)' ≤ L²/2`. -/
theorem herbst_entropy_le (n : ℕ) (h : GaussianLogSobolev n) (f : (Fin n → ℝ) → ℝ)
    (L lam : ℝ) (hL : 0 < L) (hf : LipschitzWith ⟨L, hL.le⟩ f) (hlam : 0 < lam) :
    lam * ((∫ x, (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        * Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
      / (∫ x, Real.exp (lam * (f x - ∫ y, f y
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      - Real.log (∫ x, Real.exp (lam * (f x - ∫ y, f y
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
      ≤ (lam * L) ^ 2 / 2 := by
  have hMpos := mgf_centred_pos n f L lam hL hf
  have hent := herbstTilt_entropy_le n h f L lam hL hf hlam
  have hsplit : ∫ x, herbstTilt n f lam x * Real.log (herbstTilt n f lam x)
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
      = lam * ((∫ x, (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
          * Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        / (∫ x, Real.exp (lam * (f x - ∫ y, f y
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        - Real.log (∫ x, Real.exp (lam * (f x - ∫ y, f y
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) := by
    have hpt : ∀ x, herbstTilt n f lam x * Real.log (herbstTilt n f lam x)
        = lam * ((f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
            * Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
            / (∫ x, Real.exp (lam * (f x - ∫ y, f y
                ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
              ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          - Real.log (∫ x, Real.exp (lam * (f x - ∫ y, f y
              ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
            * (Real.exp (lam * (f x - ∫ y, f y
                ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
              / (∫ x, Real.exp (lam * (f x - ∫ y, f y
                  ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
                ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))) := by
      intro x
      unfold herbstTilt
      rw [Real.log_div (Real.exp_ne_zero _) hMpos.ne', Real.log_exp]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    have h1 : ∫ x, lam * ((f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        * Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        / (∫ x, Real.exp (lam * (f x - ∫ y, f y
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
        = lam * ((∫ x, (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
            * Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
          / (∫ x, Real.exp (lam * (f x - ∫ y, f y
              ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))) := by
      rw [integral_const_mul, integral_div]
    have h2 : ∫ x, Real.log (∫ x, Real.exp (lam * (f x - ∫ y, f y
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        * (Real.exp (lam * (f x - ∫ y, f y
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          / (∫ x, Real.exp (lam * (f x - ∫ y, f y
              ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
        = Real.log (∫ x, Real.exp (lam * (f x - ∫ y, f y
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) := by
      rw [integral_const_mul, integral_div]
      have hT : (∫ x, Real.exp (lam * (f x - ∫ y, f y
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
          / (∫ x, Real.exp (lam * (f x - ∫ y, f y
              ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) = 1 := div_self hMpos.ne'
      rw [hT, mul_one]
    rw [integral_sub, h1, h2]
    · exact (((integrable_mul_exp_sub_integral n f L lam hL hf).div_const _).const_mul lam)
    · exact ((integrable_exp_sub_integral n f L lam hL hf).div_const _).const_mul _
  have hlogM : 0 < ∫ x, Real.exp (lam * (f x - ∫ y, f y
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := hMpos
  have hkey : lam * ((∫ x, (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        * Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
      / (∫ x, Real.exp (lam * (f x - ∫ y, f y
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      - Real.log (∫ x, Real.exp (lam * (f x - ∫ y, f y
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
      ≤ (lam * L) ^ 2 / 2 := by
    rw [← hsplit]; exact hent
  exact hkey

/-- The centred functional has mean zero. -/
theorem integral_sub_integral_eq_zero (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ) (hL : 0 < L)
    (hf : LipschitzWith ⟨L, hL.le⟩ f) :
    ∫ x, (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 0 := by
  haveI : IsProbabilityMeasure (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    isProbabilityMeasure_pi_gaussianReal n
  have hid : Integrable (id : (Fin n → ℝ) → (Fin n → ℝ))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    ConvexOrder.integrable_id_pi (fun _ : Fin n => gaussianReal 0 1)
      (fun _ => integrable_id_of_exp_moment (gaussianReal 0 1) 1 one_pos
        (integrable_exp_abs_gaussian 1 1))
  have hfint : Integrable f (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    ConvexOrder.integrable_real_lipschitz hf hid
  rw [integral_sub hfint (integrable_const _), integral_const]
  simp

/-- The moment generating function of the centred functional is differentiable at
every time, with derivative the first moment of the tilted law. -/
theorem hasDerivAt_mgf_centred (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L t : ℝ) (hL : 0 < L)
    (hf : LipschitzWith ⟨L, hL.le⟩ f) :
    HasDerivAt (fun s => ∫ x, Real.exp (s * (f x - ∫ y, f y
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
      (∫ x, (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        * Real.exp (t * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) t := by
  have hmem : t ∈ interior (integrableExpSet (fun x => f x - ∫ y, f y
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1)) := by
    have hsub : integrableExpSet (fun x => f x - ∫ y, f y
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        (Measure.pi fun _ : Fin n => gaussianReal 0 1) = Set.univ := by
      ext s
      simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact integrable_exp_sub_integral n f L s hL hf
    rw [hsub, interior_univ]
    exact Set.mem_univ t
  exact ProbabilityTheory.hasDerivAt_mgf (X := fun x => f x - ∫ y, f y
    ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
    (μ := Measure.pi fun _ : Fin n => gaussianReal 0 1) hmem

/-- **The Herbst argument, completed.**  The Gaussian log-Sobolev inequality
implies the exponential moment bound for a Lipschitz functional: for an
`L`-Lipschitz `f` and every `λ > 0`, `∫ exp(λ (f - ∫f)) ≤ exp(λ² L² / 2)`. -/
theorem gaussianHerbstBound_of_logSobolev (n : ℕ) (h : GaussianLogSobolev n) :
    GaussianHerbstBound n := by
  intro f L hL hf lam hlam
  set g : (Fin n → ℝ) → ℝ := fun x => f x - ∫ y, f y
    ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) with hg
  set M : ℝ → ℝ := fun t => ∫ x, Real.exp (t * g x)
    ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) with hM
  have hMpos : ∀ t : ℝ, 0 < M t := fun t => mgf_centred_pos n f L t hL hf
  have hderiv : ∀ t : ℝ, HasDerivAt M (∫ x, g x * Real.exp (t * g x)
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) t :=
    fun t => hasDerivAt_mgf_centred n f L t hL hf
  have hM0 : M 0 = 1 := by simp [hM, hg]
  have hderiv0 : HasDerivAt M 0 0 := by
    have h0 := hderiv 0
    have hz : (∫ x, g x * Real.exp (0 * g x)
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) = 0 := by
      simp only [zero_mul, Real.exp_zero, mul_one]
      exact integral_sub_integral_eq_zero n f L hL hf
    rw [hz] at h0
    exact h0
  -- The entropy inequality in the form `M'(t)/M(t) - t L²/2 ≤ log M(t)/t`.
  have hkey : ∀ t : ℝ, 0 < t →
      (∫ x, g x * Real.exp (t * g x) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) / M t
        ≤ ((t * L) ^ 2 / 2 + Real.log (M t)) / t := by
    intro t ht
    have hd := herbst_entropy_le n h f L t hL hf ht
    have h2 : t * ((∫ x, g x * Real.exp (t * g x)
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) / M t)
        ≤ (t * L) ^ 2 / 2 + Real.log (M t) := by linarith [hd]
    rw [le_div_iff₀ ht]
    have h3 : t * ((∫ x, g x * Real.exp (t * g x)
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) / M t) * t
        ≤ ((t * L) ^ 2 / 2 + Real.log (M t)) * t := by
      exact mul_le_mul_of_nonneg_right h2 ht.le
    have h4 : t * ((∫ x, g x * Real.exp (t * g x)
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) / M t) * t
        = t * (((∫ x, g x * Real.exp (t * g x)
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) / M t) * t) := by ring
    rw [h4] at h3
    have h5 : ((∫ x, g x * Real.exp (t * g x)
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) / M t) * t
        ≤ (t * L) ^ 2 / 2 + Real.log (M t) := by
      have h6 : t * (((∫ x, g x * Real.exp (t * g x)
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) / M t) * t)
          ≤ t * ((t * L) ^ 2 / 2 + Real.log (M t)) := by
        calc t * (((∫ x, g x * Real.exp (t * g x)
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) / M t) * t)
            = t * ((∫ x, g x * Real.exp (t * g x)
              ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) / M t) * t := by ring
          _ ≤ ((t * L) ^ 2 / 2 + Real.log (M t)) * t := by
              rw [mul_assoc]; exact h3
          _ = t * ((t * L) ^ 2 / 2 + Real.log (M t)) := by ring
      exact le_of_mul_le_mul_left h6 ht
    linarith [h5]

  -- `G t = log M t / t - t L²/2` has derivative at most `0` on `t > 0`.
  have hGderiv : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s => Real.log (M s) / s - s * L ^ 2 / 2)
        ((∫ x, g x * Real.exp (t * g x) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
            / M t / t - Real.log (M t) / t ^ 2 - L ^ 2 / 2) t := by
    intro t ht
    have h1 : HasDerivAt (fun s => Real.log (M s))
        ((∫ x, g x * Real.exp (t * g x) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
          / M t) t :=
      (hderiv t).log (hMpos t).ne'
    have h2 : HasDerivAt (fun s => Real.log (M s) / s)
        ((∫ x, g x * Real.exp (t * g x) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
            / M t / t - Real.log (M t) / t ^ 2) t := by
      have h3 := h1.div (hasDerivAt_id t) ht.ne'
      have h4 : ((∫ x, g x * Real.exp (t * g x) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
              / M t * t - Real.log (M t) * 1) / t ^ 2
          = (∫ x, g x * Real.exp (t * g x) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
              / M t / t - Real.log (M t) / t ^ 2 := by
        field_simp
        ring
      have h5 : HasDerivAt (fun s => Real.log (M s) / s)
          (((∫ x, g x * Real.exp (t * g x) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
              / M t * t - Real.log (M t) * 1) / t ^ 2) t := by
        have h6 : HasDerivAt (fun s => Real.log (M s) / s)
            (((∫ x, g x * Real.exp (t * g x) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
                / M t * t - Real.log (M t) * 1) / t ^ 2) t :=
          h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => rfl)
        exact h6
      rw [h4] at h5
      exact h5
    have h7 : HasDerivAt (fun s : ℝ => s * L ^ 2 / 2) (L ^ 2 / 2) t := by
      have h8 : HasDerivAt (fun s : ℝ => s * (L ^ 2 / 2)) (L ^ 2 / 2) t := by
        simpa using (hasDerivAt_id t).mul_const (L ^ 2 / 2)
      have h9 : (fun s : ℝ => s * L ^ 2 / 2) = fun s => s * (L ^ 2 / 2) := by
        funext s; ring
      rw [h9]; exact h8
    have h10 : (fun s : ℝ => Real.log (M s) / s - s * L ^ 2 / 2)
        = (fun s => Real.log (M s) / s) - fun s => s * L ^ 2 / 2 := rfl
    rw [h10]
    exact h2.sub h7
  have hanti : AntitoneOn (fun s => Real.log (M s) / s - s * L ^ 2 / 2) (Set.Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
    · intro s hs
      have hs' : 0 < s := by simpa [interior_Ioi] using hs
      exact (hGderiv s hs').continuousAt.continuousWithinAt
    · intro s hs
      have hs' : 0 < s := by simpa [interior_Ioi] using hs
      exact (hGderiv s hs').differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : 0 < s := by simpa [interior_Ioi] using hs
      rw [(hGderiv s hs').deriv]
      have hb := hkey s hs'
      have hs2 : (0 : ℝ) < s ^ 2 := by positivity
      have h1 : (∫ x, g x * Real.exp (s * g x)
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) / M s * s
          ≤ (s * L) ^ 2 / 2 + Real.log (M s) := by
        rw [le_div_iff₀ hs'] at hb
        linarith [hb]
      have h2 : (∫ x, g x * Real.exp (s * g x)
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) / M s * s - Real.log (M s)
          ≤ s ^ 2 * L ^ 2 / 2 := by
        nlinarith [h1]
      have h3 : ((∫ x, g x * Real.exp (s * g x)
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) / M s * s - Real.log (M s)) / s ^ 2
          ≤ L ^ 2 / 2 := by
        rw [div_le_iff₀ hs2]
        nlinarith [h2]
      have h4 : (∫ x, g x * Real.exp (s * g x)
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) / M s / s
          - Real.log (M s) / s ^ 2
          = ((∫ x, g x * Real.exp (s * g x)
              ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) / M s * s - Real.log (M s)) / s ^ 2 := by
        field_simp
        ring
      rw [h4]
      linarith [h3]
  -- `G t → 0` as `t → 0+`, since `log M` has derivative `0` at `0`.
  have hlim : Filter.Tendsto (fun s => Real.log (M s) / s - s * L ^ 2 / 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hlog0 : Real.log (M 0) = 0 := by rw [hM0, Real.log_one]
    have hlogderiv : HasDerivAt (fun s => Real.log (M s)) 0 0 := by
      have h1 : HasDerivAt (fun s => Real.log (M s)) (0 / M 0) 0 :=
        hderiv0.log (by rw [hM0]; norm_num)
      simpa using h1
    have hconv : Filter.Tendsto (fun t : ℝ => t⁻¹ * (Real.log (M (0 + t)) - Real.log (M 0)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := hlogderiv.tendsto_slope_zero_right
    have h1 : Filter.Tendsto (fun s => Real.log (M s) / s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hconv' : Filter.Tendsto (fun t : ℝ => t⁻¹ * Real.log (M t))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa [hlog0] using hconv
      simpa [div_eq_inv_mul] using hconv'
    have h2 : Filter.Tendsto (fun s : ℝ => s * L ^ 2 / 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h3 : Filter.Tendsto (fun s : ℝ => s * L ^ 2 / 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
        have heq : (fun s : ℝ => s * L ^ 2 / 2) = fun s => (L ^ 2 / 2) * s := by
          funext s; ring
        rw [heq]
        simpa using tendsto_const_nhds.mul (tendsto_id : Filter.Tendsto (fun s : ℝ => s)
          (𝓝 (0:ℝ)) (𝓝 0))
      exact h3.mono_left nhdsWithin_le_nhds
    simpa using h1.sub h2
  have hle : Real.log (M lam) / lam - lam * L ^ 2 / 2 ≤ 0 := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hlam)] with s hs0 hslam
    exact hanti hs0 (show lam ∈ Set.Ioi (0:ℝ) from hlam) (show s ≤ lam from le_of_lt hslam)
  have hlog : Real.log (M lam) ≤ lam ^ 2 * L ^ 2 / 2 := by
    have h1 : Real.log (M lam) / lam ≤ lam * L ^ 2 / 2 := by linarith [hle]
    rw [div_le_iff₀ hlam] at h1
    nlinarith [h1]
  calc M lam = Real.exp (Real.log (M lam)) := (Real.exp_log (hMpos lam)).symm
    _ ≤ Real.exp (lam ^ 2 * L ^ 2 / 2) := Real.exp_le_exp.mpr hlog


end LatticeProb

