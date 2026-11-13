/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Brownian.OneStep at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Oscillation

/-!
# One step of the Brownian tube argument

For a real Brownian motion `B` with measurable coordinates, continuous paths and `B 0 = 0`,
a time step `Δ > 0`, a tolerance `ε > 0` and a target `a` with `|a| ≤ ε/8`:

`P(sup_{t ≤ Δ} |B_t| < 3ε/4, |B_Δ - a| < ε/16) ≥ oneStepConst ε Δ`
(`oneStepConst_le_measure`), where

`oneStepConst ε Δ = 2 (ε/16) φ_Δ(3ε/16) - 2 exp(-(ε/2)² / (2Δ))`,

`φ_Δ` the centred Gaussian density of variance `Δ`. The first term is the Gaussian window bound
(`ofReal_le_gaussianReal_Ioo`: density bounded below on the window), the second the maximal
inequality `P(sup_{t ≤ Δ} |B_t| > ε/2) ≤ 2 exp(-(ε/2)²/(2Δ))` (QuantumZipper's
`BMOsc.bmOsc_tail`, Doob's inequality for the exponential martingale). The constant is positive
as soon as `Δ ≤ ε²/512` (`oneStepConst_pos`).

We also record the Gaussian window upper bound `gaussianReal_Ioo_le` (used for the almost sure
exit of planar Brownian motion from balls).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal Topology

namespace MatedCRTHarmonic.Brownian

/-! ### Gaussian window bounds -/

/-- The centred Gaussian density is antitone in `|x|`. -/
theorem gaussianPDFReal_zero_le_of_abs_le {v : ℝ≥0} {x y : ℝ} (h : |x| ≤ |y|) :
    gaussianPDFReal 0 v y ≤ gaussianPDFReal 0 v x := by
  simp only [gaussianPDFReal, sub_zero]
  refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (inv_nonneg.2 (sqrt_nonneg _))
  have hxy : x ^ 2 ≤ y ^ 2 := sq_le_sq.2 h
  have h2v : (0 : ℝ) ≤ 2 * v := by positivity
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_right hxy h2v

/-- The centred Gaussian density is at most its value at `0`. -/
theorem gaussianPDFReal_zero_le_sqrt_inv (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal 0 v x ≤ (√(2 * π * v))⁻¹ := by
  have h := gaussianPDFReal_zero_le_of_abs_le (v := v) (x := 0) (y := x) (by simp)
  simpa [gaussianPDFReal] using h

/-- **Gaussian window lower bound.** -/
theorem ofReal_le_gaussianReal_Ioo {v : ℝ≥0} (hv : v ≠ 0) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (2 * r * gaussianPDFReal 0 v (|a| + r)) ≤
      gaussianReal 0 v (Ioo (a - r) (a + r)) := by
  rw [gaussianReal_apply 0 hv]
  have hconst : ∀ x ∈ Ioo (a - r) (a + r),
      ENNReal.ofReal (gaussianPDFReal 0 v (|a| + r)) ≤ gaussianPDF 0 v x := by
    intro x hx
    rw [gaussianPDF]
    refine ENNReal.ofReal_le_ofReal (gaussianPDFReal_zero_le_of_abs_le ?_)
    have h1 : |x| ≤ |a| + r := by
      have : |x - a| < r := abs_sub_lt_iff.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩
      calc |x| = |(x - a) + a| := by ring_nf
        _ ≤ |x - a| + |a| := abs_add_le _ _
        _ ≤ |a| + r := by linarith
    calc |x| ≤ |a| + r := h1
      _ = |(|a| + r)| := (abs_of_nonneg (by positivity)).symm
  calc ENNReal.ofReal (2 * r * gaussianPDFReal 0 v (|a| + r))
      = ENNReal.ofReal (gaussianPDFReal 0 v (|a| + r)) * volume (Ioo (a - r) (a + r)) := by
        rw [Real.volume_Ioo, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
        congr 1
        ring
    _ = ∫⁻ _ in Ioo (a - r) (a + r), ENNReal.ofReal (gaussianPDFReal 0 v (|a| + r)) := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ x in Ioo (a - r) (a + r), gaussianPDF 0 v x :=
        setLIntegral_mono' measurableSet_Ioo hconst

/-- **Gaussian window upper bound.** -/
theorem gaussianReal_Ioo_le {v : ℝ≥0} (hv : v ≠ 0) (a r : ℝ) :
    gaussianReal 0 v (Ioo (a - r) (a + r)) ≤ ENNReal.ofReal (2 * r * (√(2 * π * v))⁻¹) := by
  rw [gaussianReal_apply 0 hv]
  calc ∫⁻ x in Ioo (a - r) (a + r), gaussianPDF 0 v x
      ≤ ∫⁻ _ in Ioo (a - r) (a + r), ENNReal.ofReal ((√(2 * π * v))⁻¹) := by
        refine setLIntegral_mono' measurableSet_Ioo fun x _ => ?_
        exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_zero_le_sqrt_inv v x)
    _ = ENNReal.ofReal (2 * r * (√(2 * π * v))⁻¹) := by
        rw [setLIntegral_const, Real.volume_Ioo, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-! ### The oscillation of a continuous path dominates its values -/

/-- For a continuous path, the oscillation on `[t₀, t₀ + s]` dominates every increment. -/
theorem abs_sub_le_bmOsc {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω))
    {t₀ s t : ℝ≥0} (ht : t ∈ Icc t₀ (t₀ + s)) :
    |B t ω - B t₀ ω| ≤ QuantumZipper.bmOsc B t₀ s ω := by
  rw [QuantumZipper.bmOsc_eq_iSup_subtype hc]
  have hbdd : BddAbove (Set.range fun x : Set.Icc t₀ (t₀ + s) => |B x ω - B t₀ ω|) := by
    obtain ⟨C, hC⟩ := ((isCompact_Icc : IsCompact (Set.Icc t₀ (t₀ + s))).image
      (f := fun r => |B r ω - B t₀ ω|) (by fun_prop)).bddAbove
    exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC ⟨x, x.2, rfl⟩⟩
  exact le_ciSup (f := fun x : Set.Icc t₀ (t₀ + s) => |B x ω - B t₀ ω|) hbdd ⟨t, ht⟩

/-! ### The one-step constant -/

/-- The one-step probability bound of the tube argument. -/
noncomputable def oneStepConst (ε : ℝ) (Δ : ℝ≥0) : ℝ :=
  2 * (ε / 16) * gaussianPDFReal 0 Δ (3 * ε / 16) - 2 * rexp (-(ε / 2) ^ 2 / (2 * Δ))

/-- The one-step constant is positive for `Δ ≤ ε² / 512`. -/
theorem oneStepConst_pos {ε : ℝ} (hε : 0 < ε) {Δ : ℝ≥0} (hΔ : 0 < Δ)
    (hΔε : (Δ : ℝ) ≤ ε ^ 2 / 512) : 0 < oneStepConst ε Δ := by
  have hΔ' : (0 : ℝ) < Δ := hΔ
  set E1 : ℝ := -(3 * ε / 16 - 0) ^ 2 / (2 * Δ) with hE1
  set E2 : ℝ := -(ε / 2) ^ 2 / (2 * Δ) with hE2
  set A : ℝ := 2 * (ε / 16) * (√(2 * π * Δ))⁻¹ with hA
  -- `A > 1`
  have hsq : √(2 * π * Δ) < ε / 8 := by
    rw [sqrt_lt' (by positivity)]
    have : 2 * π * (Δ : ℝ) ≤ 2 * π * (ε ^ 2 / 512) := by gcongr
    nlinarith [pi_lt_four, sq_nonneg ε, pi_pos]
  have hsqpos : 0 < √(2 * π * Δ) := sqrt_pos.2 (by positivity)
  have hA1 : 1 < A := by
    rw [hA, show 2 * (ε / 16) * (√(2 * π * Δ))⁻¹ = (ε / 8) / √(2 * π * Δ) by ring]
    rw [one_lt_div hsqpos]
    exact hsq
  -- `E2 ≤ E1 - 55`
  have hgap : E2 ≤ E1 - 55 := by
    have hx : 1 ≤ ε ^ 2 / (512 * Δ) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have : E2 = E1 - 55 * (ε ^ 2 / (512 * Δ)) := by
      rw [hE1, hE2]
      field_simp
      ring
    rw [this]
    linarith
  have hexp55 : 2 * rexp (-55) < 1 := by
    have h1 : (56 : ℝ) ≤ rexp 55 := by linarith [add_one_le_exp (55 : ℝ)]
    rw [exp_neg]
    rw [mul_inv_lt_iff₀ (exp_pos _)]
    linarith
  have hkey : 2 * rexp E2 < A * rexp E1 := by
    calc 2 * rexp E2 ≤ 2 * (rexp E1 * rexp (-55)) := by
          rw [← exp_add]
          gcongr
          linarith
      _ = (2 * rexp (-55)) * rexp E1 := by ring
      _ < 1 * rexp E1 := by gcongr
      _ < A * rexp E1 := by gcongr
  have hform : oneStepConst ε Δ = A * rexp E1 - 2 * rexp E2 := by
    simp only [oneStepConst, gaussianPDFReal, hA, hE1, hE2]
    ring
  rw [hform]
  linarith

/-! ### The one-step bound -/

/-- **One step.** For a real Brownian motion with measurable coordinates, continuous paths and
`B 0 = 0`, the path stays within `3ε/4` of `0` up to time `Δ` and ends within `ε/16` of `a`,
`|a| ≤ ε/8`, with probability at least `oneStepConst ε Δ`. -/
theorem oneStepConst_le_measure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) {ε : ℝ} (hε : 0 < ε) {Δ : ℝ≥0}
    (hΔ : 0 < Δ) {a : ℝ} (ha : |a| ≤ ε / 8) :
    ENNReal.ofReal (oneStepConst ε Δ) ≤
      P {ω | (∀ t ≤ Δ, |B t ω| < 3 * ε / 4) ∧ |B Δ ω - a| < ε / 16} := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set G : Set Ω := {ω | ∀ t ≤ Δ, |B t ω| < 3 * ε / 4} with hG
  set H : Set Ω := {ω | |B Δ ω - a| < ε / 16} with hH
  have hset : {ω | (∀ t ≤ Δ, |B t ω| < 3 * ε / 4) ∧ |B Δ ω - a| < ε / 16} = G ∩ H := rfl
  rw [hset]
  -- the Gaussian window
  have hHeq : H = B Δ ⁻¹' Ioo (a - ε / 16) (a + ε / 16) := by
    ext ω
    simp only [hH, mem_ofPred_eq, mem_preimage, mem_Ioo, abs_sub_lt_iff]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  have hΔ0 : Δ ≠ 0 := hΔ.ne'
  have hH_ge : ENNReal.ofReal (2 * (ε / 16) * gaussianPDFReal 0 Δ (3 * ε / 16)) ≤ P H := by
    rw [hHeq, ← Measure.map_apply (hBm Δ) measurableSet_Ioo, (hB.hasLaw_eval Δ).map_eq]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_)
      (ofReal_le_gaussianReal_Ioo hΔ0 a (r := ε / 16) (by positivity))
    refine mul_le_mul_of_nonneg_left (gaussianPDFReal_zero_le_of_abs_le ?_) (by positivity)
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * ε / 16),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ |a| + ε / 16)]
    linarith
  -- the maximal inequality
  have hGc : Gᶜ ⊆ {ω | ε / 2 < QuantumZipper.bmOsc B 0 Δ ω} := by
    intro ω hω
    simp only [hG, mem_compl_iff, mem_ofPred_eq, not_forall, not_lt] at hω
    obtain ⟨t, ht, hle⟩ := hω
    have h1 := abs_sub_le_bmOsc (B := B) (hBc ω) (t₀ := 0) (s := Δ) (t := t)
      ⟨bot_le, by simpa using ht⟩
    rw [hB0 ω, sub_zero] at h1
    show ε / 2 < QuantumZipper.bmOsc B 0 Δ ω
    linarith
  have hGc_le : P Gᶜ ≤ ENNReal.ofReal (2 * rexp (-(ε / 2) ^ 2 / (2 * Δ))) :=
    (measure_mono hGc).trans (QuantumZipper.BMOsc.bmOsc_tail hB hBm hBc 0 Δ hΔ (by positivity))
  -- combine
  have hHle : P H ≤ P (G ∩ H) + P Gᶜ := by
    calc P H ≤ P (H ∩ G) + P (H \ G) := measure_le_inter_add_sdiff P H G
      _ ≤ P (G ∩ H) + P Gᶜ := by
          rw [inter_comm]
          gcongr
          exact sdiff_subset_compl _ _
  calc ENNReal.ofReal (oneStepConst ε Δ)
      = ENNReal.ofReal (2 * (ε / 16) * gaussianPDFReal 0 Δ (3 * ε / 16)) -
          ENNReal.ofReal (2 * rexp (-(ε / 2) ^ 2 / (2 * Δ))) := by
        rw [oneStepConst, ENNReal.ofReal_sub _ (by positivity)]
    _ ≤ P H - P Gᶜ := tsub_le_tsub hH_ge hGc_le
    _ ≤ P (G ∩ H) := tsub_le_iff_right.2 hHle

end MatedCRTHarmonic.Brownian
