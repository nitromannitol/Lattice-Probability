/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.RS.TailBounds at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.RS.MartingaleBound
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.TwoPoint
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ReverseFlow

/-!
# RS E2: tail bounds for `|(revMap)'|`

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §3, node E2.

## Main statements

With `W = drive κ B ω`, `u_T = revMap W T z`, `y = Im z`, `λ = rsLam κ r`, `ζ = rsZeta κ r`:

* `RS.rs_tail_bound (hB : IsBrownianReal B P) (hκ : 0 < κ) (hr : 0 ≤ r) (hT : 0 ≤ T)
    (hz : z ∈ H) (hlam : 0 ≤ rsLam κ r) (hzeta : 0 ≤ rsZeta κ r) (β : ℝ) :
    P {ω | z.im ^ (β - 1) < ‖deriv (revMap (drive κ B ω) T) z‖}
      ≤ ENNReal.ofReal ((‖z‖ / z.im) ^ (2 * r) * z.im ^ ((1 - β) * (rsLam κ r + rsZeta κ r)))`
* `RS.rs_tail_bound_axis`: the same for `z = y * I` (`y > 0`), where `‖z‖ / z.im = 1`:
  `P {ω | y ^ (β - 1) < ‖deriv (revMap (drive κ B ω) T) (y * I)‖}
      ≤ ENNReal.ofReal (y ^ ((1 - β) * (rsLam κ r + rsZeta κ r)))`.
* Exponent arithmetic: `rsR1 κ = (8+κ)/(4κ)` (on-axis, RS Thm 3.6's `b`) with
  `rsLam + rsZeta = (8+κ)²/(16κ)`, `> 2` for `κ ≠ 8`, `rsZeta ≥ 0` for `κ ≤ 8`; and
  `rsR2 κ = (4+κ)/(4κ)` (off-axis, RS Thm 5.2's `b = 1/4 + 1/κ`) with
  `rsLam + rsZeta − 2 rsR2 = (4+κ)²/(16κ)`, `> 1` for `κ ≠ 4`, `rsZeta ≥ 0` for `κ ≤ 12`.
  In both cases `rsLam ≥ 0` and the parameter is `≥ 0`.

Relative to the blueprint text, the hypotheses `0 ≤ β ≤ 1` and `z.im ≤ 1` are dropped: the proof
does not use them, so the statement is a strengthening (no junk-value issue arises: the event is
stated for `z ∈ H`, `T ≥ 0`, where `revMap` is the genuine solution a.s.). The probability is
an outer measure; the event need not be shown measurable.

## Proof

Following RS Cor 3.5 (proof, p. 14) / Kemppainen Thm 5.5 second claim (p. 98, "Chebyshev"):
the deterministic bound `‖u_T'‖ ≤ Im u_T / Im z` (`TwoPoint.norm_deriv_revMap_le`) gives, on the
event `‖u_T'‖ > y^{β−1}`, `Im u_T > y^β`; together with `(Im u_T/|u_T|)^{−2r} ≥ 1` the E1
integrand `M = |u_T'|^λ (Im u_T)^ζ (Im u_T/|u_T|)^{−2r}` is `≥ y^{(β−1)λ + βζ}`. Markov's
inequality and E1 (`rs_martingale_bound`) give the bound. Measurability of `M` is obtained on a
continuous, jointly measurable version of `B` (`WedgeRes.exists_good_version`); the derivative
is a pointwise limit of difference quotients of `measurable_revMap_drive`.

Literature: S. Rohde, O. Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), Cor 3.5
(p. 14), Thm 3.6 (p. 16, `b = (8+κ)/(4κ)` there), Thm 5.2 proof (p. 22, `b = 1/4 + 1/κ`);
A. Kemppainen, *Schramm–Loewner Evolution*, SpringerBriefs Math. Phys. 24 (2017), Thm 5.5 second
claim and Cor 5.1 (p. 98), and the optimization `r₀ = 1/4 + 2/κ` on p. 99; G. Lawler,
*Conformally Invariant Processes in the Plane*, AMS 2005, Cor 7.3 (p. 156).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace QuantumZipper
namespace RS

/-! ### Deterministic lower bound for the E1 integrand on the event -/

/-- The E1 integrand `|u_T'|^λ (Im u_T)^ζ (Im u_T/|u_T|)^{−2r}`. -/
def rsIntegrand (κ r : ℝ) (W : ℝ → ℝ) (T : ℝ) (z : ℂ) : ℝ :=
  ‖deriv (revMap W T) z‖ ^ rsLam κ r * (revMap W T z).im ^ rsZeta κ r *
    ((revMap W T z).im / ‖revMap W T z‖) ^ (-2 * r)

/-- On the event `‖u_T'‖ > y^{β−1}`, the E1 integrand is at least `y^{(β−1)λ + βζ}`. -/
theorem rsIntegrand_ge {W : ℝ → ℝ} (hW : Continuous W) {κ r T : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T)
    {z : ℂ} (hz : z ∈ H) (hlam : 0 ≤ rsLam κ r) (hzeta : 0 ≤ rsZeta κ r) {β : ℝ}
    (hev : z.im ^ (β - 1) < ‖deriv (revMap W T) z‖) :
    z.im ^ ((β - 1) * rsLam κ r + β * rsZeta κ r) ≤ rsIntegrand κ r W T z := by
  have hy : 0 < z.im := hz
  set a := ‖deriv (revMap W T) z‖ with ha
  set Y := (revMap W T z).im with hY
  have hYpos : 0 < Y := hy.trans_le (im_le_im_revMap W hW z hy hT)
  have haY : a ≤ Y / z.im := TwoPoint.norm_deriv_revMap_le hW hz hT
  have hc0 : 0 < z.im ^ (β - 1) := Real.rpow_pos_of_pos hy _
  have hYb : z.im ^ β ≤ Y := by
    have h1 : z.im ^ β = z.im * z.im ^ (β - 1) := by
      calc z.im ^ β = z.im ^ ((1 : ℝ) + (β - 1)) := by ring_nf
        _ = z.im ^ (1 : ℝ) * z.im ^ (β - 1) := Real.rpow_add hy _ _
        _ = z.im * z.im ^ (β - 1) := by rw [Real.rpow_one]
    rw [h1]
    have h2 : z.im * a ≤ Y := by
      rw [le_div_iff₀ hy] at haY; linarith
    nlinarith
  have hA : z.im ^ ((β - 1) * rsLam κ r) ≤ a ^ rsLam κ r := by
    rw [Real.rpow_mul hy.le]
    exact Real.rpow_le_rpow hc0.le hev.le hlam
  have hB : z.im ^ (β * rsZeta κ r) ≤ Y ^ rsZeta κ r := by
    rw [Real.rpow_mul hy.le]
    exact Real.rpow_le_rpow (Real.rpow_pos_of_pos hy _).le hYb hzeta
  have hn : 0 < ‖revMap W T z‖ := hYpos.trans_le (Complex.im_le_norm _)
  have hS : 1 ≤ (Y / ‖revMap W T z‖) ^ (-2 * r) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (div_pos hYpos hn)
      ((div_le_one hn).2 (Complex.im_le_norm _)) (by linarith)
  have hA0 : 0 ≤ z.im ^ ((β - 1) * rsLam κ r) := (Real.rpow_pos_of_pos hy _).le
  have hB0 : 0 ≤ z.im ^ (β * rsZeta κ r) := (Real.rpow_pos_of_pos hy _).le
  rw [Real.rpow_add hy]
  calc z.im ^ ((β - 1) * rsLam κ r) * z.im ^ (β * rsZeta κ r)
      ≤ a ^ rsLam κ r * Y ^ rsZeta κ r := mul_le_mul hA hB hB0 (hA0.trans hA)
    _ = a ^ rsLam κ r * Y ^ rsZeta κ r * 1 := (mul_one _).symm
    _ ≤ rsIntegrand κ r W T z := by
      unfold rsIntegrand
      exact mul_le_mul_of_nonneg_left hS
        (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hYpos.le _))

/-! ### Measurability of the derivative in the driving path -/

theorem measurable_deriv_revMap_drive {Ω : Type*} [MeasurableSpace Ω] (κ : ℝ)
    {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous fun t => B t ω)
    {z : ℂ} (hz : z ∈ H) {T : ℝ} (hT : 0 ≤ T) :
    Measurable fun ω => deriv (revMap (drive κ B ω) T) z := by
  have hz' : 0 < z.im := hz
  let h : ℕ → ℂ := fun n => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  let q : ℕ → Ω → ℂ := fun n ω =>
    (h n)⁻¹ • (revMap (drive κ B ω) T (z + h n) - revMap (drive κ B ω) T z)
  have hq : ∀ n, Measurable (q n) := by
    intro n
    have h1 : 0 < (z + h n).im := by simp [h, hz']
    exact ((ReverseFlow.measurable_revMap_drive κ B hBm hc _ h1 hT).sub
      (ReverseFlow.measurable_revMap_drive κ B hBm hc z hz' hT)).const_smul ((h n)⁻¹ : ℂ)
  have hs : Tendsto h atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
      mem_compl_singleton_iff.2 (Complex.ofReal_ne_zero.2 (by positivity))⟩
    have := (Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [Complex.ofReal_zero] at this
    exact this
  refine measurable_of_tendsto_metrizable hq (tendsto_pi_nhds.2 fun ω => ?_)
  have hd := hasDerivAt_revMap (drive κ B ω) (NonSwallow.continuous_drive_ns hc κ ω) hT hz
  rw [hd.deriv]
  exact hd.tendsto_slope_zero.comp hs

/-! ### The tail bound -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **RS E2 (tail bound).** RS Cor 3.5; Kemppainen Thm 5.5 (second claim), p. 98. -/
theorem rs_tail_bound (hB : IsBrownianReal B P) {κ r T : ℝ} (hκ : 0 < κ) (hr : 0 ≤ r)
    (hT : 0 ≤ T) {z : ℂ} (hz : z ∈ H) (hlam : 0 ≤ rsLam κ r) (hzeta : 0 ≤ rsZeta κ r) (β : ℝ) :
    P {ω | z.im ^ (β - 1) < ‖deriv (revMap (drive κ B ω) T) z‖}
      ≤ ENNReal.ofReal ((‖z‖ / z.im) ^ (2 * r) *
          z.im ^ ((1 - β) * (rsLam κ r + rsZeta κ r))) := by
  have hy : 0 < z.im := hz
  have hzn : 0 < ‖z‖ := hy.trans_le (Complex.im_le_norm z)
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := WedgeRes.exists_good_version hB
  have hB'mt : ∀ t, Measurable (B' t) := fun t => hB'm.comp measurable_prodMk_left
  have hdr : ∀ᵐ ω ∂P, drive κ B' ω = drive κ B ω := by
    filter_upwards [hB'eq] with ω hω
    exact funext fun t => by simp only [drive, hω]
  have hE1 : ∫⁻ ω, ENNReal.ofReal (rsIntegrand κ r (drive κ B ω) T z) ∂P
      ≤ ENNReal.ofReal (z.im ^ rsZeta κ r * (z.im / ‖z‖) ^ (-2 * r)) :=
    rs_martingale_bound hB hκ hr hT hz
  have hE1' : ∫⁻ ω, ENNReal.ofReal (rsIntegrand κ r (drive κ B' ω) T z) ∂P
      ≤ ENNReal.ofReal (z.im ^ rsZeta κ r * (z.im / ‖z‖) ^ (-2 * r)) := by
    refine le_of_eq_of_le (lintegral_congr_ae ?_) hE1
    filter_upwards [hdr] with ω hω
    rw [hω]
  set c := z.im ^ ((β - 1) * rsLam κ r + β * rsZeta κ r) with hcdef
  have hc : 0 < c := Real.rpow_pos_of_pos hy _
  have hmono : P {ω | z.im ^ (β - 1) < ‖deriv (revMap (drive κ B ω) T) z‖}
      ≤ P {ω | ENNReal.ofReal c ≤ ENNReal.ofReal (rsIntegrand κ r (drive κ B' ω) T z)} := by
    refine measure_mono_ae ?_
    filter_upwards [hdr] with ω hω
    intro hmem
    have hmem' : z.im ^ (β - 1) < ‖deriv (revMap (drive κ B' ω) T) z‖ := by
      rw [hω]; exact hmem
    exact ENNReal.ofReal_le_ofReal
      (rsIntegrand_ge (NonSwallow.continuous_drive_ns hB'c κ ω) hr hT hz hlam hzeta hmem')
  have hmeas : Measurable fun ω => ENNReal.ofReal (rsIntegrand κ r (drive κ B' ω) T z) := by
    have hd := measurable_deriv_revMap_drive κ hB'mt hB'c hz hT
    have hu := ReverseFlow.measurable_revMap_drive κ B' hB'mt hB'c z hy hT
    have him : Measurable fun ω => (revMap (drive κ B' ω) T z).im :=
      Complex.measurable_im.comp hu
    exact (((hd.norm.pow_const _).mul (him.pow_const _)).mul
      ((him.div hu.norm).pow_const _)).ennreal_ofReal
  have hX : (z.im / ‖z‖) ^ (-2 * r) = (‖z‖ / z.im) ^ (2 * r) := by
    rw [show -2 * r = -(2 * r) by ring, Real.rpow_neg (div_nonneg hy.le hzn.le),
      ← Real.inv_rpow (div_nonneg hy.le hzn.le), inv_div]
  calc P {ω | z.im ^ (β - 1) < ‖deriv (revMap (drive κ B ω) T) z‖}
      ≤ P {ω | ENNReal.ofReal c ≤ ENNReal.ofReal (rsIntegrand κ r (drive κ B' ω) T z)} := hmono
    _ ≤ (∫⁻ ω, ENNReal.ofReal (rsIntegrand κ r (drive κ B' ω) T z) ∂P) / ENNReal.ofReal c :=
      meas_ge_le_lintegral_div hmeas.aemeasurable (ENNReal.ofReal_pos.2 hc).ne'
        ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (z.im ^ rsZeta κ r * (z.im / ‖z‖) ^ (-2 * r)) / ENNReal.ofReal c :=
      ENNReal.div_le_div_right hE1' _
    _ = ENNReal.ofReal (z.im ^ rsZeta κ r * (z.im / ‖z‖) ^ (-2 * r) / c) :=
      (ENNReal.ofReal_div_of_pos hc).symm
    _ = ENNReal.ofReal ((‖z‖ / z.im) ^ (2 * r) *
          z.im ^ ((1 - β) * (rsLam κ r + rsZeta κ r))) := by
      congr 1
      rw [hX, show (1 - β) * (rsLam κ r + rsZeta κ r) =
        rsZeta κ r - ((β - 1) * rsLam κ r + β * rsZeta κ r) by ring, Real.rpow_sub hy, hcdef]
      ring

/-- **RS E2 on the imaginary axis** (`z = y i`, so `‖z‖ / Im z = 1`). -/
theorem rs_tail_bound_axis (hB : IsBrownianReal B P) {κ r T : ℝ} (hκ : 0 < κ) (hr : 0 ≤ r)
    (hT : 0 ≤ T) {y : ℝ} (hy : 0 < y) (hlam : 0 ≤ rsLam κ r) (hzeta : 0 ≤ rsZeta κ r) (β : ℝ) :
    P {ω | y ^ (β - 1) < ‖deriv (revMap (drive κ B ω) T) (y * Complex.I)‖}
      ≤ ENNReal.ofReal (y ^ ((1 - β) * (rsLam κ r + rsZeta κ r))) := by
  have him : ((y : ℂ) * Complex.I).im = y := by simp
  have hn : ‖(y : ℂ) * Complex.I‖ = y := by simp [abs_of_pos hy]
  have hz : (y : ℂ) * Complex.I ∈ H := by show 0 < ((y : ℂ) * Complex.I).im; rw [him]; exact hy
  have := rs_tail_bound hB hκ hr hT hz hlam hzeta β
  rwa [him, hn, div_self hy.ne', Real.one_rpow, one_mul] at this

/-! ### Exponent arithmetic: the two choices of `r` -/

/-- On-axis parameter `r₁ = (8+κ)/(4κ)` (RS Thm 3.6's `b`; Kem p. 99's `r₀ = 1/4 + 2/κ`). -/
def rsR1 (κ : ℝ) : ℝ := (8 + κ) / (4 * κ)

/-- Off-axis parameter `r₂ = (4+κ)/(4κ) = 1/4 + 1/κ` (RS Thm 5.2 proof, p. 22). -/
def rsR2 (κ : ℝ) : ℝ := (4 + κ) / (4 * κ)

theorem rsR1_nonneg {κ : ℝ} (hκ : 0 < κ) : 0 ≤ rsR1 κ := by unfold rsR1; positivity

theorem rsR2_nonneg {κ : ℝ} (hκ : 0 < κ) : 0 ≤ rsR2 κ := by unfold rsR2; positivity

theorem rsLam_rsR1 {κ : ℝ} (hκ : 0 < κ) :
    rsLam κ (rsR1 κ) = (8 + κ) * (8 + 3 * κ) / (32 * κ) := by
  unfold rsLam rsR1; field_simp; ring

theorem rsZeta_rsR1 {κ : ℝ} (hκ : 0 < κ) :
    rsZeta κ (rsR1 κ) = (8 + κ) * (8 - κ) / (32 * κ) := by
  unfold rsZeta rsR1; field_simp; ring

theorem rsLam_add_rsZeta_rsR1 {κ : ℝ} (hκ : 0 < κ) :
    rsLam κ (rsR1 κ) + rsZeta κ (rsR1 κ) = (8 + κ) ^ 2 / (16 * κ) := by
  rw [rsLam_rsR1 hκ, rsZeta_rsR1 hκ]; field_simp; ring

theorem rsLam_rsR1_nonneg {κ : ℝ} (hκ : 0 < κ) : 0 ≤ rsLam κ (rsR1 κ) := by
  rw [rsLam_rsR1 hκ]; positivity

theorem rsZeta_rsR1_nonneg {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ ≤ 8) : 0 ≤ rsZeta κ (rsR1 κ) := by
  rw [rsZeta_rsR1 hκ]
  exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)

theorem rsLam_rsR2 {κ : ℝ} (hκ : 0 < κ) :
    rsLam κ (rsR2 κ) = (4 + κ) * (12 + 3 * κ) / (32 * κ) := by
  unfold rsLam rsR2; field_simp; ring

theorem rsZeta_rsR2 {κ : ℝ} (hκ : 0 < κ) :
    rsZeta κ (rsR2 κ) = (4 + κ) * (12 - κ) / (32 * κ) := by
  unfold rsZeta rsR2; field_simp; ring

theorem rsLam_add_rsZeta_sub_rsR2 {κ : ℝ} (hκ : 0 < κ) :
    rsLam κ (rsR2 κ) + rsZeta κ (rsR2 κ) - 2 * rsR2 κ = (4 + κ) ^ 2 / (16 * κ) := by
  rw [rsLam_rsR2 hκ, rsZeta_rsR2 hκ]; unfold rsR2; field_simp; ring

theorem rsLam_rsR2_nonneg {κ : ℝ} (hκ : 0 < κ) : 0 ≤ rsLam κ (rsR2 κ) := by
  rw [rsLam_rsR2 hκ]; positivity

theorem rsZeta_rsR2_nonneg {κ : ℝ} (hκ : 0 < κ) (hκ12 : κ ≤ 12) : 0 ≤ rsZeta κ (rsR2 κ) := by
  rw [rsZeta_rsR2 hκ]
  exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)

/-- `λ + ζ − 2r > 1` at `r₂` for `κ ≠ 4` (RS Thm 5.2 proof, p. 22). -/
theorem one_lt_rsLam_add_rsZeta_sub_rsR2 {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≠ 4) :
    1 < rsLam κ (rsR2 κ) + rsZeta κ (rsR2 κ) - 2 * rsR2 κ := by
  rw [rsLam_add_rsZeta_sub_rsR2 hκ, lt_div_iff₀ (by linarith)]
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.2 hκ4)]

end RS
end QuantumZipper
