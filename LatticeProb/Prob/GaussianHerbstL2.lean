/-
# Gaussian concentration in the ℓ² (Cameron–Martin) metric

`LatticeProb.GaussianLogSobolev n` and `LatticeProb.GaussianHerbstBound n` are
stated for the *sup-norm* Lipschitz class: `LipschitzWith` on `Fin n → ℝ` is
Lipschitz continuity for the metric `dist x y = max i, |x i - y i|`, i.e. for the
`ℓ∞` distance.  Applied to a function that is `L`-Lipschitz for the `ℓ²`
(Cameron–Martin) distance, that class gives the tail `exp (-t² / (2 n L²))`
instead of the sharp `exp (-t² / (2 L²))`, because `ℓ∞ ≤ ℓ² ≤ √n · ℓ∞`.
`Sandpile.External.GaussianLipschitzConcentration` is stated exactly for the
`ℓ²` class, so the existing chain does not reach its constant.

This module records the two restatements that close the gap:

* `GaussianLogSobolevL2 n` — the Gaussian log-Sobolev inequality with the `ℓ²`
  (`Cameron–Martin`) Lipschitz hypothesis on `log h`.  This is the standard
  gradient form of the inequality of Gross (1975) and is *strictly stronger*
  than `GaussianLogSobolev n`: it is not derivable from the sup-norm form.
* `GaussianHerbstBoundL2 n` — the Herbst exponential moment bound in the same
  `ℓ²` class, with the sharp constant.

`gaussianHerbstBoundL2_of_gaussianLogSobolevL2` proves the `ℓ²` Herbst bound from
the `ℓ²` log-Sobolev inequality (the argument is that of the sup-norm case, with
the entropy bound fed in at the `ℓ²` constant).
`gaussian_lipschitz_concentration_l2` is the Chernoff step, giving the sharp tail
`exp (-t² / (2 L²))` in the `ℓ²` class.
`gaussianHerbstBoundL2_weakened_of_gaussianLogSobolev` records what the
*existing* sup-norm machinery reaches: the same conclusion with `L²` replaced by
`(√n L + 1)²`, i.e. the factor `n` the supervisor identified.
-/
import LatticeProb.Prob.HerbstBound
import LatticeProb.Prob.GaussianHerbst

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProb

/-- **The Gaussian log-Sobolev inequality in the ℓ² (Cameron–Martin) metric.**
For a positive density `h` with `∫ h = 1` whose logarithm is `C`-Lipschitz for the
Euclidean distance `√(∑ (xᵢ - yᵢ)²)`, the entropy is at most `C² / 2`.  This is the
gradient form of the inequality of Gross (1975) and Bakry–Émery (1985); it is
strictly stronger than `GaussianLogSobolev n`, which carries the sup-norm
Lipschitz constant. -/
def GaussianLogSobolevL2 (n : ℕ) : Prop :=
  ∀ h : (Fin n → ℝ) → ℝ, (∀ x, 0 < h x) →
    Integrable h (Measure.pi fun _ : Fin n => gaussianReal 0 1) →
    Integrable (fun x => h x * Real.log (h x))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) →
    (∫ x, h x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 1) →
    ∀ C : ℝ≥0, (∀ x y : Fin n → ℝ,
        |Real.log (h x) - Real.log (h y)| ≤ C * Real.sqrt (∑ i, (x i - y i) ^ 2)) →
    ∫ x, h x * Real.log (h x) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
      ≤ (C : ℝ) ^ 2 / 2

/-- **The Herbst exponential moment bound in the ℓ² (Cameron–Martin) metric.**
For a functional `f` of `n` independent standard Gaussians that is `L`-Lipschitz
for the Euclidean distance `√(∑ (xᵢ - yᵢ)²)`, the moment generating function of
`f - ∫f` is at most `exp (λ² L² / 2)`.  This is the `ℓ²` counterpart of
`GaussianHerbstBound n`, whose `LipschitzWith` hypothesis is the sup-norm one. -/
def GaussianHerbstBoundL2 (n : ℕ) : Prop :=
  ∀ (f : (Fin n → ℝ) → ℝ) (L : ℝ), 0 < L →
    (∀ x y : Fin n → ℝ, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) →
    ∀ lam : ℝ, 0 < lam →
      ∫ x, Real.exp (lam * (f x - ∫ y, f y
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
        ≤ Real.exp (lam ^ 2 * L ^ 2 / 2)

/-- An `ℓ²`-Lipschitz function on `Fin n → ℝ` is Lipschitz for the sup-norm metric
with constant `√n L + 1`, since `ℓ∞ ≤ ℓ² ≤ √n · ℓ∞`. -/
theorem lipschitzWith_of_l2 {n : ℕ} {f : (Fin n → ℝ) → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y : Fin n → ℝ, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) :
    LipschitzWith ⟨Real.sqrt n * L + 1, by positivity⟩ f := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq]
  have hd : (0 : ℝ) ≤ dist x y := dist_nonneg
  have hterm : ∀ i : Fin n, (x i - y i) ^ 2 ≤ (dist x y) ^ 2 := by
    intro i
    have h1 : |x i - y i| ≤ dist x y := by
      have := dist_le_pi_dist x y i
      rwa [Real.dist_eq] at this
    have h2 : |x i - y i| ^ 2 ≤ (dist x y) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rwa [sq_abs] at h2
  have hsum : ∑ i, (x i - y i) ^ 2 ≤ (n : ℝ) * (dist x y) ^ 2 := by
    calc ∑ i, (x i - y i) ^ 2 ≤ ∑ _i : Fin n, (dist x y) ^ 2 :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = (n : ℝ) * (dist x y) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsqrt : Real.sqrt (∑ i, (x i - y i) ^ 2) ≤ Real.sqrt n * dist x y := by
    calc Real.sqrt (∑ i, (x i - y i) ^ 2) ≤ Real.sqrt ((n : ℝ) * (dist x y) ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = Real.sqrt n * dist x y := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hd]
  calc |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2) := hf x y
    _ ≤ L * (Real.sqrt n * dist x y) := mul_le_mul_of_nonneg_left hsqrt hL
    _ ≤ (Real.sqrt n * L + 1) * dist x y := by nlinarith

/-- The sup-norm metric on `Fin n → ℝ` is at most the Euclidean distance. -/
theorem dist_le_l2 {n : ℕ} (x y : Fin n → ℝ) :
    dist x y ≤ Real.sqrt (∑ i, (x i - y i) ^ 2) := by
  rw [dist_pi_le_iff (Real.sqrt_nonneg _)]
  intro i
  rw [Real.dist_eq]
  calc |x i - y i| = Real.sqrt ((x i - y i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, (x j - y j) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j : Fin n => (x j - y j) ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i))

/-- The logarithm of the Herbst tilt `h_λ` is `λ f` up to an additive constant, so
when `f` is `ℓ²`-Lipschitz with constant `K` so is `log h_λ`, with constant
`λ K`. -/
theorem herbstTilt_log_lipschitz_l2 (n : ℕ) (f : (Fin n → ℝ) → ℝ) (K lam : ℝ)
    (hlam : 0 ≤ lam) (hf : ∀ x y : Fin n → ℝ,
      |f x - f y| ≤ K * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (hM : 0 < ∫ x, Real.exp (lam * (f x - ∫ y, f y
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) :
    ∀ x y : Fin n → ℝ,
      |Real.log (herbstTilt n f lam x) - Real.log (herbstTilt n f lam y)|
        ≤ (lam * K) * Real.sqrt (∑ i, (x i - y i) ^ 2) := by
  intro x y
  have hconst : ∀ z, Real.log (herbstTilt n f lam z)
      = lam * (f z - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        - Real.log (∫ x, Real.exp (lam * (f x - ∫ y, f y
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) := by
    intro z
    unfold herbstTilt
    rw [Real.log_div (Real.exp_ne_zero _) hM.ne', Real.log_exp]
  rw [hconst x, hconst y]
  have hdiff : (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        - Real.log (∫ x, Real.exp (lam * (f x - ∫ y, f y
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      - (lam * (f y - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        - Real.log (∫ x, Real.exp (lam * (f x - ∫ y, f y
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      = lam * (f x - f y) := by ring
  rw [hdiff, abs_mul, abs_of_nonneg hlam]
  calc lam * |f x - f y| ≤ lam * (K * Real.sqrt (∑ i, (x i - y i) ^ 2)) :=
        mul_le_mul_of_nonneg_left (hf x y) hlam
    _ = (lam * K) * Real.sqrt (∑ i, (x i - y i) ^ 2) := by ring

/-- The Herbst tilt is integrable. -/
theorem herbstTilt_integrable (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L lam : ℝ) (hL : 0 < L)
    (hf : LipschitzWith ⟨L, hL.le⟩ f) :
    Integrable (herbstTilt n f lam) (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  unfold herbstTilt
  exact (integrable_exp_sub_integral n f L lam hL hf).div_const _

/-- The Herbst tilt times its logarithm is integrable. -/
theorem herbstTilt_mul_log_integrable (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L lam : ℝ)
    (hL : 0 < L) (hf : LipschitzWith ⟨L, hL.le⟩ f) :
    Integrable (fun x => herbstTilt n f lam x * Real.log (herbstTilt n f lam x))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  set Mv : ℝ := ∫ x, Real.exp (lam * (f x - ∫ y, f y
    ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
    ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) with hMv
  have hMpos : 0 < Mv := mgf_centred_pos n f L lam hL hf
  have hint := herbstTilt_integrable n f L lam hL hf
  have hlog : ∀ x, Real.log (herbstTilt n f lam x)
      = lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        - Real.log Mv := by
    intro x
    unfold herbstTilt
    rw [← hMv, Real.log_div (Real.exp_ne_zero _) hMpos.ne', Real.log_exp]
  have hB : Integrable (fun x => herbstTilt n f lam x
      * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
    have hbase : Integrable (fun x => (f x - ∫ y, f y
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        * Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))))
        (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
      integrable_mul_exp_sub_integral n f L lam hL hf
    refine (hbase.div_const Mv).congr ?_
    filter_upwards with x
    simp only [herbstTilt]
    rw [← hMv]
    ring
  have heq : (fun x => lam * (herbstTilt n f lam x
        * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      - Real.log Mv * herbstTilt n f lam x)
      = fun x => herbstTilt n f lam x * Real.log (herbstTilt n f lam x) := by
    funext x
    rw [hlog x]
    ring
  refine ((hB.const_mul lam).sub (hint.const_mul (Real.log Mv))).congr ?_
  filter_upwards with x
  exact congrFun heq x

/-- The entropy of the tilt is at most `(λ K)² / 2` when `f` is `ℓ²`-Lipschitz with
constant `K`, by the `ℓ²` Gaussian log-Sobolev inequality. -/
theorem herbstTilt_entropy_le_L2 {n : ℕ} (h : GaussianLogSobolevL2 n)
    {f : (Fin n → ℝ) → ℝ} {L K lam : ℝ} (hL : 0 < L)
    (hf : LipschitzWith ⟨L, hL.le⟩ f) (hK : 0 ≤ K)
    (hfK : ∀ x y : Fin n → ℝ, |f x - f y| ≤ K * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (hlam : 0 < lam) :
    ∫ x, herbstTilt n f lam x * Real.log (herbstTilt n f lam x)
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
      ≤ (lam * K) ^ 2 / 2 := by
  have hMpos := mgf_centred_pos n f L lam hL hf
  have hpos := herbstTilt_pos n f lam hMpos
  have hint := herbstTilt_integrable n f L lam hL hf
  have hintlog := herbstTilt_mul_log_integrable n f L lam hL hf
  have hnorm := herbstTilt_integral n f lam hMpos.ne'
  have hlip := herbstTilt_log_lipschitz_l2 n f K lam hlam.le hfK hMpos
  exact h (herbstTilt n f lam) hpos hint hintlog hnorm
    ⟨lam * K, mul_nonneg hlam.le hK⟩ hlip

/-- **The ℓ² Herbst bound from the ℓ² log-Sobolev inequality.**  If
`GaussianLogSobolevL2 n` holds then an `ℓ²`-Lipschitz functional has moment
generating function at most `exp (λ² L² / 2)`, i.e. `GaussianHerbstBoundL2 n`. -/
theorem gaussianHerbstBoundL2_of_gaussianLogSobolevL2 (n : ℕ)
    (h : GaussianLogSobolevL2 n) : GaussianHerbstBoundL2 n := by
  intro f L hL hf lam hlam
  refine mgf_le_of_entropy_bound n f (Real.sqrt n * L + 1) (by positivity)
    (lipschitzWith_of_l2 hL.le hf) L ?_ lam hlam
  intro mu hmu
  exact herbstTilt_entropy_le_L2 h (by positivity : (0 : ℝ) < Real.sqrt n * L + 1)
    (lipschitzWith_of_l2 hL.le hf) hL.le hf hmu

/-- **The Chernoff step in the ℓ² class.**  An `ℓ²`-Lipschitz functional whose
moment generating function is bounded by `exp (λ² L² / 2)` exceeds its mean by
`t` with probability at most `exp (-t² / (2 L²))`. -/
theorem gaussian_lipschitz_concentration_l2 (n : ℕ) (hHerbst : GaussianHerbstBoundL2 n)
    (f : (Fin n → ℝ) → ℝ) (L : ℝ) (hL : 0 < L)
    (hf : ∀ x y : Fin n → ℝ, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).real
        {x | t ≤ f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)}
      ≤ Real.exp (-(t ^ 2) / (2 * L ^ 2)) := by
  have hsup := lipschitzWith_of_l2 hL.le hf
  rcases eq_or_lt_of_le ht with h | ht'
  · subst h
    have : Real.exp (-(0 : ℝ) ^ 2 / (2 * L ^ 2)) = 1 := by simp [Real.exp_zero]
    rw [this]
    exact MeasureTheory.measureReal_le_one
  · exact measure_ge_le_of_mgf_bound _ f _ L t hL ht'
      (fun lam hlam => integrable_exp_lipschitz_gaussian n f (Real.sqrt n * L + 1)
        (by positivity) hsup lam)
      (fun lam hlam => hHerbst f L hL hf lam hlam)

/-- **What the sup-norm machinery reaches in the ℓ² class.**  From the existing
`GaussianLogSobolev n`, an `ℓ²`-Lipschitz functional of constant `L` satisfies the
Herbst bound with the sup-norm constant `√n L + 1`: the `ℓ²` condition gives
sup-norm Lipschitz continuity after inflation by `√n`, which is the factor `n` in
the exponent.  The sharp constant needs `GaussianLogSobolevL2 n`. -/
theorem gaussianHerbstBoundL2_weakened_of_gaussianLogSobolev (n : ℕ)
    (h : GaussianLogSobolev n) (f : (Fin n → ℝ) → ℝ) (L : ℝ) (hL : 0 < L)
    (hf : ∀ x y : Fin n → ℝ, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (lam : ℝ) (hlam : 0 < lam) :
    ∫ x, Real.exp (lam * (f x - ∫ y, f y
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
      ≤ Real.exp (lam ^ 2 * (Real.sqrt n * L + 1) ^ 2 / 2) :=
  gaussianHerbstBound_of_gaussianLogSobolev n h f (Real.sqrt n * L + 1)
    (by positivity) (lipschitzWith_of_l2 hL.le hf) lam hlam

/-- The Chernoff step for the inflated ℓ² Herbst bound, i.e. the tail the
existing sup-norm chain produces for an `ℓ²`-Lipschitz functional. -/
theorem gaussian_lipschitz_concentration_l2_weakened (n : ℕ) (h : GaussianLogSobolev n)
    (f : (Fin n → ℝ) → ℝ) (L : ℝ) (hL : 0 < L)
    (hf : ∀ x y : Fin n → ℝ, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).real
        {x | t ≤ f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)}
      ≤ Real.exp (-(t ^ 2) / (2 * (Real.sqrt n * L + 1) ^ 2)) :=
  gaussian_lipschitz_concentration n (gaussianHerbstBound_of_gaussianLogSobolev n h) f
    (Real.sqrt n * L + 1) (by positivity) (lipschitzWith_of_l2 hL.le hf) t ht

/-- Every `ℓ²` statement with a positive constant is an instance of the sup-norm
statement: the sup-norm log-Lipschitz condition implies the `ℓ²` one with the same
constant (`ℓ∞ ≤ ℓ²`), so `GaussianLogSobolevL2 n` is strictly stronger than
`GaussianLogSobolev n`.  This records the direction of the gap. -/
theorem gaussianLogSobolev_of_gaussianLogSobolevL2 {n : ℕ} (h : GaussianLogSobolevL2 n) :
    GaussianLogSobolev n := by
  intro hh hpos hint hintlog hnorm C hlip
  refine h hh hpos hint hintlog hnorm C (fun x y => ?_)
  calc |Real.log (hh x) - Real.log (hh y)|
      = dist (Real.log (hh x)) (Real.log (hh y)) := by rw [Real.dist_eq]
    _ ≤ (C : ℝ) * dist x y := hlip.dist_le_mul x y
    _ ≤ (C : ℝ) * Real.sqrt (∑ i, (x i - y i) ^ 2) :=
        mul_le_mul_of_nonneg_left (dist_le_l2 x y) (by positivity)

end LatticeProb
