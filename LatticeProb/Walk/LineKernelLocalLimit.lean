import Mathlib
import LatticeProb.Walk.LineKernelGauss

/-!
# The local limit theorem for the one-dimensional continuous-time kernel

For every `s > 0` and every integer `k`,
`|lineKernel s k - lineGauss s k| ≤ C s^{-3/2} exp(-k²/(10(s + |k|)))`
(`exists_abs_lineKernel_sub_lineGauss_le`). The error is Gaussian in `k` in the diffusive
range and exponential in `|k|` beyond it. In the range `|k| ≤ s/2` the contour of the Fourier
integral is moved to `Im z = k/s` and the two integrands are compared there; in the range
`|k| ≥ s/2` both kernels are bounded separately, the lattice one by its exponential bound at
`Im z = ±1/2`.
-/

open MeasureTheory

noncomputable section

namespace LatticeProb.ContinuousTime

/-- Away from the origin the kernel decays like `exp (-|k| / 5)`. -/
private lemma abs_lineKernel_le_exp_neg {s : ℝ} (hs : 0 < s) (k : ℤ)
    (hk : s / 2 ≤ |(k : ℝ)|) :
    |lineKernel s k| ≤ Real.exp (-|(k : ℝ)| / 5) := by
  have hK : 0 ≤ |(k : ℝ)| := abs_nonneg _
  have hsK : s ≤ 2 * |(k : ℝ)| := by linarith
  have hcosh : Real.cosh (1 / 2) - 1 ≤ 3 / 20 := by
    have h := cosh_sub_one_le (l := (1 / 2 : ℝ)) (by norm_num)
    norm_num at h ⊢
    exact h
  rcases lt_or_ge (k : ℝ) 0 with hkneg | hk0
  · have hkabs : |(k : ℝ)| = -(k : ℝ) := abs_of_neg hkneg
    have hstep : Real.exp (-((-1 / 2 : ℝ) * k) + s * (Real.cosh (-1 / 2) - 1))
        ≤ Real.exp (-|(k : ℝ)| / 5) := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.cosh_neg]
      apply Real.exp_le_exp.mpr
      rw [hkabs]
      have h1 : s * (Real.cosh (1 / 2) - 1) ≤ s * (3 / 20) :=
        mul_le_mul_of_nonneg_left hcosh hs.le
      have h2 : s * (3 / 20) ≤ (2 * (-(k : ℝ))) * (3 / 20) := by
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        linarith [hsK, hkabs]
      nlinarith [h1, h2]
    exact (abs_lineKernel_le_exp hs.le k (-1 / 2)).trans hstep
  · have hkabs : |(k : ℝ)| = (k : ℝ) := abs_of_nonneg hk0
    have hstep : Real.exp (-((1 / 2 : ℝ) * k) + s * (Real.cosh (1 / 2) - 1))
        ≤ Real.exp (-|(k : ℝ)| / 5) := by
      apply Real.exp_le_exp.mpr
      rw [hkabs]
      have h1 : s * (Real.cosh (1 / 2) - 1) ≤ s * (3 / 20) :=
        mul_le_mul_of_nonneg_left hcosh hs.le
      have h2 : s * (3 / 20) ≤ (2 * (k : ℝ)) * (3 / 20) := by
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        linarith [hsK, hkabs]
      nlinarith [h1, h2]
    exact (abs_lineKernel_le_exp hs.le k (1 / 2)).trans hstep

/-- The Gaussian term decays like `exp (-|k| / 4)`. -/
private lemma lineGauss_le_exp_neg {s : ℝ} (hs : 0 < s) (k : ℤ)
    (hk : s / 2 ≤ |(k : ℝ)|) :
    lineGauss s k ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-|(k : ℝ)| / 4) := by
  have hK : 0 ≤ |(k : ℝ)| := abs_nonneg _
  have hsK : s ≤ 2 * |(k : ℝ)| := by linarith
  unfold lineGauss
  apply mul_le_mul_of_nonneg_left _
    (by positivity : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi * s))⁻¹)
  apply Real.exp_le_exp.mpr
  have hsq : (k : ℝ) ^ 2 = |(k : ℝ)| ^ 2 := (sq_abs _).symm
  have h1 : |(k : ℝ)| * s ≤ |(k : ℝ)| * (2 * |(k : ℝ)|) :=
    mul_le_mul_of_nonneg_left hsK hK
  have h2 : |(k : ℝ)| * s / 2 ≤ (k : ℝ) ^ 2 := by rw [hsq]; nlinarith [h1]
  have h3 : |(k : ℝ)| / 4 ≤ (k : ℝ) ^ 2 / (2 * s) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * s)]
    nlinarith [h2]
  have h4 : -((k : ℝ) ^ 2 / (2 * s)) ≤ -|(k : ℝ)| / 4 := by
    rw [show -|(k : ℝ)| / 4 = -(|(k : ℝ)| / 4) by ring]
    exact neg_le_neg h3
  have h5 : -(k : ℝ) ^ 2 / (2 * s) = -((k : ℝ) ^ 2 / (2 * s)) := by ring
  rwa [h5]

/-- `s * sqrt s ≤ 1 + s ^ 2` for `s ≥ 0`. -/
private lemma mul_sqrt_self_le_one_add_sq {s : ℝ} (hs : 0 ≤ s) :
    s * Real.sqrt s ≤ 1 + s ^ 2 := by
  rcases le_total s 1 with h1 | h1
  · have hsqrt : Real.sqrt s ≤ 1 := Real.sqrt_le_one.mpr h1
    have : s * Real.sqrt s ≤ s * 1 := mul_le_mul_of_nonneg_left hsqrt hs
    nlinarith [this, hs]
  · have hsqrt : Real.sqrt s ≤ s := by
      rw [Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ s)]
      nlinarith [h1]
    have : s * Real.sqrt s ≤ s * s := mul_le_mul_of_nonneg_left hsqrt hs
    nlinarith [this]

/-- `x ^ 2 * exp (-x / 10) ≤ 200` for `x ≥ 0`. -/
private lemma sq_mul_exp_neg_le (x : ℝ) (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-x / 10) ≤ 200 := by
  have hquad := Real.quadratic_le_exp_of_nonneg (show 0 ≤ x / 10 by positivity)
  have h1 : (x / 10) ^ 2 / 2 ≤ Real.exp (x / 10) := by linarith
  have hexp : 0 < Real.exp (x / 10) := Real.exp_pos _
  rw [show -x / 10 = -(x / 10) by ring, Real.exp_neg]
  rw [mul_inv_le_iff₀ hexp]
  nlinarith [h1]

/-- `x * exp (-3 x / 20) ≤ 20 / 3` for every real `x`. -/
private lemma mul_exp_neg_le (x : ℝ) :
    x * Real.exp (-3 * x / 20) ≤ 20 / 3 := by
  have h := Real.add_one_le_exp (3 * x / 20)
  have hx' : 3 * x / 20 ≤ Real.exp (3 * x / 20) := by linarith
  rw [show -3 * x / 20 = -(3 * x / 20) by ring, Real.exp_neg]
  rw [mul_inv_le_iff₀ (Real.exp_pos _)]
  nlinarith [hx']

/-- `(s * sqrt s) * exp (-x / 10) ≤ 801` when `0 < s` and `s ≤ 2 x`. -/
private lemma sqrt_self_mul_exp_le {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) (hsx : s ≤ 2 * x) :
    (s * Real.sqrt s) * Real.exp (-x / 10) ≤ 801 := by
  have hD := mul_sqrt_self_le_one_add_sq hs.le
  have hs2 : s ^ 2 ≤ 4 * x ^ 2 := by nlinarith [hsx, hx]
  have hxexp := sq_mul_exp_neg_le x hx
  have hexp1 : Real.exp (-x / 10) ≤ 1 := by
    have : Real.exp (-x / 10) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    simpa using this
  calc (s * Real.sqrt s) * Real.exp (-x / 10)
      ≤ (1 + s ^ 2) * Real.exp (-x / 10) :=
        mul_le_mul_of_nonneg_right hD (Real.exp_nonneg _)
    _ ≤ (1 + 4 * x ^ 2) * Real.exp (-x / 10) := by gcongr
    _ = Real.exp (-x / 10) + 4 * (x ^ 2 * Real.exp (-x / 10)) := by ring
    _ ≤ 1 + 4 * 200 := by nlinarith [hexp1, hxexp]
    _ = 801 := by norm_num

/-- `(s * sqrt s) * (sqrt (2 π s))⁻¹ * exp (-3 x / 20) ≤ 20` when `0 < s` and `s ≤ 2 x`. -/
private lemma sqrt_self_div_sqrt_mul_exp_le {s x : ℝ} (hs : 0 < s) (hsx : s ≤ 2 * x) :
    (s * Real.sqrt s) * (Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-3 * x / 20) ≤ 20 := by
  have hDsimp : (s * Real.sqrt s) * (Real.sqrt (2 * Real.pi * s))⁻¹
      = s * (Real.sqrt (2 * Real.pi))⁻¹ := by
    have h2pi : 0 < 2 * Real.pi := by positivity
    rw [Real.sqrt_mul h2pi.le]
    field_simp
  have hsqrt2pi : 1 ≤ Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
  have hcoef : s * (Real.sqrt (2 * Real.pi))⁻¹ ≤ s := by
    have hle : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]
      exact hsqrt2pi
    calc s * (Real.sqrt (2 * Real.pi))⁻¹ ≤ s * 1 :=
          mul_le_mul_of_nonneg_left hle hs.le
      _ = s := by ring
  have hxexp := mul_exp_neg_le x
  calc (s * Real.sqrt s) * (Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-3 * x / 20)
      = (s * (Real.sqrt (2 * Real.pi))⁻¹) * Real.exp (-3 * x / 20) := by rw [hDsimp]
    _ ≤ s * Real.exp (-3 * x / 20) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
    _ ≤ (2 * x) * Real.exp (-3 * x / 20) :=
        mul_le_mul_of_nonneg_right hsx (Real.exp_nonneg _)
    _ = 2 * (x * Real.exp (-3 * x / 20)) := by ring
    _ ≤ 2 * (20 / 3) := mul_le_mul_of_nonneg_left hxexp (by norm_num)
    _ ≤ 20 := by norm_num

/-- `s ^ (-(3 : ℝ) / 2) = (s * sqrt s)⁻¹` for `s > 0`. -/
private lemma rpow_neg_three_halves {s : ℝ} (hs : 0 < s) :
    s ^ (-(3 : ℝ) / 2) = (s * Real.sqrt s)⁻¹ := by
  have hD : s * Real.sqrt s = s ^ ((3 : ℝ) / 2) := by
    calc s * Real.sqrt s = s ^ (1 : ℝ) * s ^ (1 / 2 : ℝ) := by
          rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = s ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add hs 1 (1 / 2)).symm
      _ = s ^ ((3 : ℝ) / 2) := by norm_num
  rw [hD, show (-(3 : ℝ) / 2) = -((3 : ℝ) / 2) by norm_num, Real.rpow_neg hs.le]

/-- In the range `|k| ≥ s/2` both kernels are exponentially small in `|k|`, and so within
`C s^{-3/2} e^{-|k|/10}` of each other. -/
theorem exists_abs_lineKernel_sub_lineGauss_le_far :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 < s → ∀ k : ℤ, s / 2 ≤ |(k : ℝ)| →
      |lineKernel s k - lineGauss s k|
        ≤ C * s ^ (-(3 : ℝ) / 2) * Real.exp (-|(k : ℝ)| / 10) := by
  refine ⟨821, by norm_num, ?_⟩
  intro s hs k hk
  have hK : 0 ≤ |(k : ℝ)| := abs_nonneg _
  have hsK : s ≤ 2 * |(k : ℝ)| := by linarith
  have hq := abs_lineKernel_le_exp_neg hs k hk
  have hg := lineGauss_le_exp_neg hs k hk
  have hg_nonneg : 0 ≤ lineGauss s k := by unfold lineGauss; positivity
  have hDpos : 0 < s * Real.sqrt s := by positivity
  have hb1 := sqrt_self_mul_exp_le hs hK hsK
  have hb2 := sqrt_self_div_sqrt_mul_exp_le (s := s) (x := |(k : ℝ)|) hs hsK
  have hE5 : Real.exp (-|(k : ℝ)| / 5)
      = Real.exp (-|(k : ℝ)| / 10) * Real.exp (-|(k : ℝ)| / 10) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE4 : Real.exp (-|(k : ℝ)| / 4)
      = Real.exp (-3 * |(k : ℝ)| / 20) * Real.exp (-|(k : ℝ)| / 10) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp10_le : Real.exp (-|(k : ℝ)| / 10) ≤ 801 / (s * Real.sqrt s) := by
    rw [le_div_iff₀ hDpos]
    simpa [mul_comm] using hb1
  have hexp3_le : (Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-3 * |(k : ℝ)| / 20)
      ≤ 20 / (s * Real.sqrt s) := by
    rw [le_div_iff₀ hDpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hb2
  have hqa : Real.exp (-|(k : ℝ)| / 5)
      ≤ (801 / (s * Real.sqrt s)) * Real.exp (-|(k : ℝ)| / 10) := by
    rw [hE5]
    exact mul_le_mul_of_nonneg_right hexp10_le (Real.exp_nonneg _)
  have hgb : (Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-|(k : ℝ)| / 4)
      ≤ (20 / (s * Real.sqrt s)) * Real.exp (-|(k : ℝ)| / 10) := by
    rw [hE4, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hexp3_le (Real.exp_nonneg _)
  calc |lineKernel s k - lineGauss s k|
      ≤ |lineKernel s k| + lineGauss s k := by
        rw [sub_eq_add_neg]
        calc |lineKernel s k + -lineGauss s k|
              ≤ |lineKernel s k| + |-lineGauss s k| := abs_add_le _ _
          _ = |lineKernel s k| + lineGauss s k := by
              rw [abs_neg, abs_of_nonneg hg_nonneg]
    _ ≤ Real.exp (-|(k : ℝ)| / 5)
          + (Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-|(k : ℝ)| / 4) :=
        add_le_add hq hg
    _ ≤ (801 / (s * Real.sqrt s)) * Real.exp (-|(k : ℝ)| / 10)
          + (20 / (s * Real.sqrt s)) * Real.exp (-|(k : ℝ)| / 10) :=
        add_le_add hqa hgb
    _ = 821 * s ^ (-(3 : ℝ) / 2) * Real.exp (-|(k : ℝ)| / 10) := by
        rw [rpow_neg_three_halves hs]
        ring

/-- In the range `|k| ≤ s/2` the lattice kernel is the Gaussian up to
`C s^{-3/2} e^{-k²/(5s)}`: shift the contour to `Im z = k/s`. -/
theorem exists_abs_lineKernel_sub_lineGauss_le_near :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 < s → ∀ k : ℤ, |(k : ℝ)| ≤ s / 2 →
      |lineKernel s k - lineGauss s k|
        ≤ C * s ^ (-(3 : ℝ) / 2) * Real.exp (-(k : ℝ) ^ 2 / (5 * s)) := by
  set c : ℝ := 2 / Real.pi ^ 2 with hc
  have hcpos : 0 < c := by positivity
  set A₁ : ℝ := 8 * Real.sqrt (2 * Real.pi / c) / c ^ 2 with hA₁
  set A₂ : ℝ := Real.sqrt (Real.pi / c) with hA₂
  have hA₁pos : 0 ≤ A₁ := by positivity
  have hA₂pos : 0 ≤ A₂ := by positivity
  refine ⟨(120 * (A₁ + 50 * A₂) + 2) / (2 * Real.pi), by positivity, ?_⟩
  intro s hs k hk
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hD : 0 < s * Real.sqrt s := mul_pos hs hsq
  have hrpow : s ^ (-(3 : ℝ) / 2) = (s * Real.sqrt s)⁻¹ := by
    rw [show -(3 : ℝ) / 2 = -(1 + 1 / 2) by norm_num, Real.rpow_neg hs.le,
      Real.rpow_add hs, Real.rpow_one, ← Real.sqrt_eq_rpow]
  set l : ℝ := (k : ℝ) / s with hl
  have hl2 : |l| ≤ 1 / 2 := by
    rw [hl, abs_div, abs_of_pos hs, div_le_iff₀ hs]
    linarith
  set v : ℝ := (k : ℝ) ^ 2 / s with hv
  have hv0 : 0 ≤ v := by positivity
  have hE₁ : -((k : ℝ) * l) + 3 / 5 * s * l ^ 2 = -(2 / 5) * v := by
    rw [hl, hv]; field_simp; ring
  have hE₂ : -((k : ℝ) * l) + s * l ^ 2 / 2 = -(1 / 2) * v := by
    rw [hl, hv]; field_simp; ring
  -- the two pieces of `2π (q - g)`
  have heq := lineKernel_sub_lineGauss_eq hs k l
  set I₁ := ∫ θ in (-Real.pi)..Real.pi,
      (lineIntegrand s k (θ + l * Complex.I) - gaussIntegrand s k (θ + l * Complex.I)) with hI₁
  set I₂ := ∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ, gaussIntegrand s k (θ + l * Complex.I)
    with hI₂
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  set E : ℝ := Real.exp (-((k : ℝ) * l) + 3 / 5 * s * l ^ 2) with hE
  have hg1 : Continuous fun θ : ℝ => θ ^ 4 * Real.exp (-(c * s) * θ ^ 2) := by fun_prop
  have hg2 : Continuous fun θ : ℝ => Real.exp (-(c * s) * θ ^ 2) := by fun_prop
  have hbound1 : ‖I₁‖ ≤ 120 * s * E * (∫ θ in (-Real.pi)..Real.pi,
      θ ^ 4 * Real.exp (-(c * s) * θ ^ 2))
      + 120 * s * E * l ^ 4 * (∫ θ in (-Real.pi)..Real.pi, Real.exp (-(c * s) * θ ^ 2)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hg1.const_mul _).intervalIntegrable _ _)
        ((hg2.const_mul _).intervalIntegrable _ _)]
    refine intervalIntegral.norm_integral_le_of_norm_le hpi
      (Filter.Eventually.of_forall fun θ hθ => ?_)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    have hθ' : |θ| ≤ Real.pi := abs_le.mpr ⟨hθ.1.le, hθ.2⟩
    have h := norm_lineIntegrand_sub_gaussIntegrand_le hs.le k hθ' hl2
    rw [← hE] at h
    calc _ ≤ _ := h
      _ = _ := by rw [hc]; ring_nf
  have hq := integral_quartic_gauss_le (a := c * s) (by positivity)
  have hq0 := integral_gauss_le (a := c * s) (by positivity)
  have hsq1 : Real.sqrt (2 * Real.pi / (c * s)) = Real.sqrt (2 * Real.pi / c) / Real.sqrt s := by
    rw [← div_div, Real.sqrt_div' _ hs.le]
  have hsq2 : Real.sqrt (Real.pi / (c * s)) = Real.sqrt (Real.pi / c) / Real.sqrt s := by
    rw [← div_div, Real.sqrt_div' _ hs.le]
  rw [hsq1] at hq
  rw [hsq2] at hq0
  have hEpos : 0 < E := Real.exp_pos _
  have hI₁le : ‖I₁‖
      ≤ 120 * Real.exp (-(2 / 5) * v) * (A₁ + A₂ * v ^ 2) / (s * Real.sqrt s) := by
    refine hbound1.trans ?_
    have hstep : 120 * s * E * (8 / (c * s) ^ 2 * (Real.sqrt (2 * Real.pi / c) / Real.sqrt s))
        + 120 * s * E * l ^ 4 * (Real.sqrt (Real.pi / c) / Real.sqrt s)
        = 120 * Real.exp (-(2 / 5) * v) * (A₁ + A₂ * v ^ 2) / (s * Real.sqrt s) := by
      rw [hE, hE₁, hA₁, hA₂, hl, hv]
      field_simp
    rw [← hstep]
    gcongr
  have hI₂le : ‖I₂‖ ≤ 2 * Real.exp (-(1 / 2) * v) / (s * Real.sqrt s) := by
    have h := norm_integral_compl_gaussIntegrand_le hs k l
    rw [hE₂, hrpow] at h
    calc ‖I₂‖ ≤ _ := h
      _ = _ := by field_simp
  have hpoly : (A₁ + A₂ * v ^ 2) * Real.exp (-(2 / 5) * v)
      ≤ (A₁ + 50 * A₂) * Real.exp (-v / 5) := by
    have hq5 := Real.quadratic_le_exp_of_nonneg (show 0 ≤ v / 5 by positivity)
    have hsplit : Real.exp (-(2 / 5) * v) = Real.exp (-v / 5) * (Real.exp (v / 5))⁻¹ := by
      rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring
    have hmono : Real.exp (-(2 / 5) * v) ≤ Real.exp (-v / 5) :=
      Real.exp_le_exp.mpr (by linarith)
    have hv2 : v ^ 2 * Real.exp (-(2 / 5) * v) ≤ 50 * Real.exp (-v / 5) := by
      rw [hsplit, ← mul_assoc, mul_comm (v ^ 2), mul_assoc]
      have hpos5 := Real.exp_pos (v / 5)
      have : v ^ 2 * (Real.exp (v / 5))⁻¹ ≤ 50 := by
        rw [← div_eq_mul_inv, div_le_iff₀ hpos5]
        have h' : 0 ≤ 50 + 10 * v := by linarith only [hv0]
        linear_combination 50 * hq5 + h'
      calc Real.exp (-v / 5) * (v ^ 2 * (Real.exp (v / 5))⁻¹)
          ≤ Real.exp (-v / 5) * 50 := by gcongr
        _ = 50 * Real.exp (-v / 5) := by ring
    linear_combination mul_le_mul_of_nonneg_left hmono hA₁pos
      + mul_le_mul_of_nonneg_left hv2 hA₂pos
  have hmono2 : Real.exp (-(1 / 2) * v) ≤ Real.exp (-v / 5) := Real.exp_le_exp.mpr (by linarith)
  -- the real absolute value through the complex identity
  have habs : 2 * Real.pi * |lineKernel s k - lineGauss s k| = ‖I₁ - I₂‖ := by
    rw [← heq, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    congr 1
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have htot : 2 * Real.pi * |lineKernel s k - lineGauss s k|
      ≤ (120 * (A₁ + 50 * A₂) + 2) * Real.exp (-v / 5) / (s * Real.sqrt s) := by
    rw [habs]
    calc ‖I₁ - I₂‖ ≤ ‖I₁‖ + ‖I₂‖ := norm_sub_le _ _
      _ ≤ 120 * Real.exp (-(2 / 5) * v) * (A₁ + A₂ * v ^ 2) / (s * Real.sqrt s)
          + 2 * Real.exp (-(1 / 2) * v) / (s * Real.sqrt s) := add_le_add hI₁le hI₂le
      _ ≤ (120 * (A₁ + 50 * A₂) + 2) * Real.exp (-v / 5) / (s * Real.sqrt s) := by
          rw [← add_div]
          gcongr
          linear_combination 120 * hpoly + 2 * hmono2
  have hv5 : -v / 5 = -(k : ℝ) ^ 2 / (5 * s) := by rw [hv]; field_simp
  rw [hrpow, ← hv5]
  have h2pi : 0 < 2 * Real.pi := by positivity
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ h2pi]
  calc |lineKernel s k - lineGauss s k| * (2 * Real.pi)
      = 2 * Real.pi * |lineKernel s k - lineGauss s k| := by ring
    _ ≤ (120 * (A₁ + 50 * A₂) + 2) * Real.exp (-v / 5) / (s * Real.sqrt s) := htot
    _ = (120 * (A₁ + 50 * A₂) + 2) * (s * Real.sqrt s)⁻¹ * Real.exp (-v / 5) := by
        field_simp

/-- **The Gaussian comparison with a Gaussian-weighted error**: for all `s > 0` and `k`,
`|q_s(k) - g_s(k)| ≤ C s^{-3/2} exp(-k²/(10(s + |k|)))`. -/
theorem exists_abs_lineKernel_sub_lineGauss_le :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 < s → ∀ k : ℤ,
      |lineKernel s k - lineGauss s k|
        ≤ C * s ^ (-(3 : ℝ) / 2) * Real.exp (-(k : ℝ) ^ 2 / (10 * (s + |(k : ℝ)|))) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_abs_lineKernel_sub_lineGauss_le_near
  obtain ⟨C₂, hC₂, h₂⟩ := exists_abs_lineKernel_sub_lineGauss_le_far
  refine ⟨C₁ + C₂, by positivity, fun s hs k => ?_⟩
  have hrp : 0 < s ^ (-(3 : ℝ) / 2) := Real.rpow_pos_of_pos hs _
  have hk0 : 0 ≤ |(k : ℝ)| := abs_nonneg _
  have hden : 0 < 10 * (s + |(k : ℝ)|) := by positivity
  set E := Real.exp (-(k : ℝ) ^ 2 / (10 * (s + |(k : ℝ)|))) with hE
  have hEpos : 0 < E := Real.exp_pos _
  rcases le_total |(k : ℝ)| (s / 2) with hk | hk
  · have hexp : Real.exp (-(k : ℝ) ^ 2 / (5 * s)) ≤ E := by
      rw [hE]
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
    calc |lineKernel s k - lineGauss s k|
        ≤ C₁ * s ^ (-(3 : ℝ) / 2) * Real.exp (-(k : ℝ) ^ 2 / (5 * s)) := h₁ s hs k hk
      _ ≤ C₁ * s ^ (-(3 : ℝ) / 2) * E := by gcongr
      _ ≤ (C₁ + C₂) * s ^ (-(3 : ℝ) / 2) * E := by gcongr; linarith
  · have hexp : Real.exp (-|(k : ℝ)| / 10) ≤ E := by
      rw [hE]
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 10)]
      have hsq : (k : ℝ) ^ 2 = |(k : ℝ)| * |(k : ℝ)| := by rw [← sq, sq_abs]
      rw [hsq]
      nlinarith [mul_nonneg hk0 hs.le]
    calc |lineKernel s k - lineGauss s k|
        ≤ C₂ * s ^ (-(3 : ℝ) / 2) * Real.exp (-|(k : ℝ)| / 10) := h₂ s hs k hk
      _ ≤ C₂ * s ^ (-(3 : ℝ) / 2) * E := by gcongr
      _ ≤ (C₁ + C₂) * s ^ (-(3 : ℝ) / 2) * E := by gcongr; linarith

end LatticeProb.ContinuousTime
