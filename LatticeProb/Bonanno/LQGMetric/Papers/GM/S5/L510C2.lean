/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.L510C2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.L510C1

/-!
# GM Lemma 5.10, condition (5): the probabilistic part (task P2-M2M6)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`,
l. 3313–3320: "By Lemma 2.9 [= DFGPS Lemma 3.20] … (5.33) … holds with probability close to 1
… (5.33) implies condition 5 since each `V` is a connected union of at most a constant number of
squares." Here:

* `l510_sqEvent`: GM (5.33) at all dyadic levels, from DFGPS Lemma 3.20 (second display;
  `Blueprint.DFGPSLem3_20`) at the level `ε' = 2^{-k} ε` with `k` large (the probability bound
  `C ε'^p ≤ q` of "polynomially high probability"), transferred from the normalized field
  `h − h_1(0)` to `h` by Axiom III (adding a constant), as in `gm_L56_sqDiam`.
* `l510_tubes_diam`: simultaneously for every preconnected tube of side `εr` whose squares meet
  `cl B_{Rr}(0)`, `internalDiam D_h V V ≤ A 𝔠_r e^{ξ h_r(0)}`: subdivide the squares to side
  `ε'r` (`tubeOf_refineF`), count them (`card_le_of_meet_ball`), chain (`l510_conn_tube_diam`).
* `gm_L510Diam`: condition (5) (`L510Diam` with `0 < γ < 2`, see the report).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- **GM (5.33)** at every dyadic level below `ε' = 2^{-k} ε` (DFGPS Lemma 3.20, Axiom III) -/
theorem l510_sqEvent (h320 : DFGPSLem3_20) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {χ : ℝ} (hχ0 : 0 < χ)
    (hχQ : χ < xiGamma γ * (Q γ - 2)) {K : Set ℂ} (hK : IsCompact K) {q ε : ℝ} (hq : 0 < q)
    (hε : 0 < ε) :
    ∃ k : ℕ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r →
      P {ω | ¬ ∀ (j : ℕ) (m : ℤ × ℤ),
        (gridSquare ((2 : ℝ)⁻¹ ^ j * ((2 : ℝ)⁻¹ ^ k * ε * r)) m ∩ scaleSet r 0 K).Nonempty →
        internalDiam (D (h ω)) (gridSquare ((2 : ℝ)⁻¹ ^ j * ((2 : ℝ)⁻¹ ^ k * ε * r)) m)
          (gridSquare ((2 : ℝ)⁻¹ ^ j * ((2 : ℝ)⁻¹ ^ k * ε * r)) m) ≤
          ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j) ^ χ *
            (((2 : ℝ)⁻¹ ^ k * ε) ^ χ * scaleFac (xiGamma γ) c (h ω) r 0))} ≤
        ENNReal.ofReal q := by
  set ξ := xiGamma γ with hξ
  obtain ⟨-, p, hp, C, ε₂, hε₂, H2⟩ := h320 γ hγ0 hγ2 D c hD K hK χ hχ0 hχQ
  obtain ⟨a₀, ha₀, ha₀ε, hB⟩ := gm_exists_small_rpow (C := C) hp hε₂ hq
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos ha₀ hε) (by norm_num : (2 : ℝ)⁻¹ < 1)
  set ε' : ℝ := (2 : ℝ)⁻¹ ^ k * ε with hε'
  have hε'0 : 0 < ε' := by positivity
  have hε'a : ε' ≤ a₀ := by
    rw [hε']; rw [lt_div_iff₀ hε] at hk; exact hk.le
  refine ⟨k, ?_⟩
  intro Ω _ P _ h hh r hr
  have hm : Measurable fun ω => -circleAvg (h ω) 1 0 :=
    ((measurable_circleAvg_left 1 0).comp hh.measurable).neg
  set h' : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) 1 0)
  have hh' : IsNormalizedWPGFF h' P := by
    refine ⟨hh.addConst hm, ?_⟩
    filter_upwards [CircleAvg.ae_circleAvg_addConst hh 0 one_pos] with ω hω
    simp only [h', hω, add_neg_cancel]
  have hT : ∀ᵐ ω ∂P, (∀ x y, (D (h' ω)).1 (x, y) =
      Real.exp (-(ξ * circleAvg (h ω) 1 0)) * (D (h ω)).1 (x + 0, y + 0)) ∧
      circleAvg (h' ω) r 0 = circleAvg (h ω) r 0 - circleAvg (h ω) 1 0 := by
    filter_upwards [hD.ae_dist_addConst (Tight.isGFFPlusCont_of_wp hh),
      CircleAvg.ae_circleAvg_addConst hh 0 hr] with ω h2 h3
    refine ⟨fun x y => ?_, ?_⟩
    · simp only [h', add_zero]; rw [h2, mul_neg]
    · simp only [h']; rw [h3, sub_eq_add_neg]
  set E2 : Set Ω := h' ⁻¹' {g : DistC | ∀ (j : ℕ) (m : ℤ × ℤ),
    (gridSquare ((2 : ℝ)⁻¹ ^ j * ε' * r) m ∩ scaleSet r 0 K).Nonempty →
    ENNReal.ofReal ((c r)⁻¹ * Real.exp (-xiGamma γ * circleAvg g r 0)) *
      internalDiam (D g) (gridSquare ((2 : ℝ)⁻¹ ^ j * ε' * r) m)
        (gridSquare ((2 : ℝ)⁻¹ ^ j * ε' * r) m) ≤ ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j * ε') ^ χ)}
  have hP2 : P E2ᶜ ≤ ENNReal.ofReal q :=
    (H2 P h' hh' ε' ⟨hε'0, lt_of_le_of_lt hε'a ha₀ε⟩ r hr).trans
      (ENNReal.ofReal_le_ofReal (hB ε' ⟨hε'0, hε'a⟩))
  have hcr : 0 < c r := hD.tightness.1 r hr
  have hsub : {ω | ¬ ∀ (j : ℕ) (m : ℤ × ℤ),
        (gridSquare ((2 : ℝ)⁻¹ ^ j * ((2 : ℝ)⁻¹ ^ k * ε * r)) m ∩ scaleSet r 0 K).Nonempty →
        internalDiam (D (h ω)) (gridSquare ((2 : ℝ)⁻¹ ^ j * ((2 : ℝ)⁻¹ ^ k * ε * r)) m)
          (gridSquare ((2 : ℝ)⁻¹ ^ j * ((2 : ℝ)⁻¹ ^ k * ε * r)) m) ≤
          ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j) ^ χ *
            (((2 : ℝ)⁻¹ ^ k * ε) ^ χ * scaleFac (xiGamma γ) c (h ω) r 0))} ≤ᵐ[P] E2ᶜ := by
    filter_upwards [hT] with ω ⟨hd1, hd2⟩
    intro hω
    by_contra hcon
    simp only [mem_compl_iff, not_not] at hcon
    apply hω
    intro j m hm
    have h2 := hcon j m (by convert hm using 3; simp only [hε']; ring)
    have key := DFGPS.internalDiam_transl_smul (Real.exp_pos _) 0 hd1
      (gridSquare ((2 : ℝ)⁻¹ ^ j * ε' * r) m) (gridSquare ((2 : ℝ)⁻¹ ^ j * ε' * r) m)
    simp only [sub_zero, image_id'] at key
    rw [key, hd2, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)] at h2
    have hkey : (c r)⁻¹ * Real.exp (-xiGamma γ * (circleAvg (h ω) r 0 - circleAvg (h ω) 1 0)) *
        Real.exp (-(ξ * circleAvg (h ω) 1 0)) =
        (c r * Real.exp (ξ * circleAvg (h ω) r 0))⁻¹ := by
      rw [mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
      congr 2; rw [hξ]; ring
    rw [hkey] at h2
    set F := c r * Real.exp (ξ * circleAvg (h ω) r 0) with hF
    have hF0 : 0 < F := mul_pos hcr (Real.exp_pos _)
    set Sq := gridSquare ((2 : ℝ)⁻¹ ^ j * ε' * r) m
    have h3 : internalDiam (D (h ω)) Sq Sq ≤ ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j * ε') ^ χ * F) := by
      have e : internalDiam (D (h ω)) Sq Sq =
          ENNReal.ofReal F * (ENNReal.ofReal F⁻¹ * internalDiam (D (h ω)) Sq Sq) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hF0.le, mul_inv_cancel₀ hF0.ne',
          ENNReal.ofReal_one, one_mul]
      rw [e, mul_comm _ F, ENNReal.ofReal_mul hF0.le]
      exact mul_le_mul_right h2 _
    have eSq : gridSquare ((2 : ℝ)⁻¹ ^ j * ((2 : ℝ)⁻¹ ^ k * ε * r)) m = Sq := by
      simp only [Sq, hε', mul_assoc]
    rw [eSq]
    refine h3.trans (le_of_eq ?_)
    rw [Real.mul_rpow (by positivity) hε'0.le]
    simp only [scaleFac, hF, hξ, hε']; congr 1; ring
  calc _ ≤ P E2ᶜ := measure_mono_ae hsub
    _ ≤ ENNReal.ofReal q := hP2

/-- **Condition (5) for all connected tubes of side `εr` near `cl B_{Rr}(0)`** (GM l. 3313–3320) -/
theorem l510_tubes_diam (h320 : DFGPSLem3_20) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {ε R q : ℝ}
    (hε : 0 < ε) (hR : 0 ≤ R) (hq : 0 < q) :
    ∃ A : ℝ, 1 < A ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r →
      P {ω | ¬ ∀ F : Finset (ℤ × ℤ),
        (∀ m ∈ F, (gridSquare (ε * r) m ∩ closedBall 0 (R * r)).Nonempty) →
        IsPreconnected (tubeOf (ε * r) F) →
        internalDiam (D (h ω)) (tubeOf (ε * r) F) (tubeOf (ε * r) F) ≤
          ENNReal.ofReal (A * scaleFac (xiGamma γ) c (h ω) r 0)} ≤ ENNReal.ofReal q := by
  set χ : ℝ := xiGamma γ * (Q γ - 2) / 2 with hχ
  have hχ0 : 0 < χ := by have := xiQ_pos hγ0 hγ2; rw [hχ]; linarith
  have hχQ : χ < xiGamma γ * (Q γ - 2) := by have := xiQ_pos hγ0 hγ2; rw [hχ]; linarith
  set R' : ℝ := R + 3 * ε with hR'
  obtain ⟨k, Hk⟩ := l510_sqEvent h320 hγ0 hγ2 hD hχ0 hχQ (isCompact_closedBall (0 : ℂ) R') hq hε
  have hε'0 : 0 < (2 : ℝ)⁻¹ ^ k * ε := by positivity
  set Nc : ℕ := (2 * ⌈R' / ((2 : ℝ)⁻¹ ^ k * ε)⌉₊ + 3) ^ 2 with hNc
  have hW0 : 0 < whitC χ := whitC_pos hχ0
  have hpow0 : 0 < ((2 : ℝ)⁻¹ ^ k * ε) ^ χ := Real.rpow_pos_of_pos hε'0 _
  set A : ℝ := (2 + 2 * (Nc : ℝ)) * whitC χ * ((2 : ℝ)⁻¹ ^ k * ε) ^ χ + 2 with hA
  have hA1 : 1 < A := by
    rw [hA]; have : 0 ≤ (Nc : ℝ) := Nat.cast_nonneg _
    have : 0 ≤ (2 + 2 * (Nc : ℝ)) * whitC χ * ((2 : ℝ)⁻¹ ^ k * ε) ^ χ := by positivity
    linarith
  refine ⟨A, hA1, ?_⟩
  intro Ω _ P _ h hh r hr
  refine le_trans (measure_mono ?_) (Hk P h hh r hr)
  intro ω hω hgood
  apply hω
  intro F hF hconn
  have hN : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hs : 0 < ε * r := mul_pos hε hr
  have hs' : 0 < (2 : ℝ)⁻¹ ^ k * ε * r := mul_pos hε'0 hr
  have es : ε * r / ((2 ^ k : ℕ) : ℝ) = (2 : ℝ)⁻¹ ^ k * ε * r := by
    rw [Nat.cast_pow, Nat.cast_ofNat, inv_pow]; field_simp
  have ht : tubeOf (ε * r) F = tubeOf ((2 : ℝ)⁻¹ ^ k * ε * r) (refineF (2 ^ k) F) := by
    rw [← tubeOf_refineF hs hN F, es]
  rw [ht] at hconn ⊢
  have hsq : ∀ m' ∈ refineF (2 ^ k) F, gridSquare ((2 : ℝ)⁻¹ ^ k * ε * r) m' ⊆
      closedBall 0 (R' * r) := by
    intro m' hm' y hy
    obtain ⟨m, hmF, hsub⟩ := mem_refineF_sub hs hN hm'
    rw [es] at hsub
    obtain ⟨x, hxS, hxB⟩ := hF m hmF
    have hy' := gridSquare_subset_ball hs hxS (hsub hy)
    rw [mem_ball, dist_eq_norm] at hy'
    rw [mem_closedBall, dist_zero_right] at hxB ⊢
    have := norm_le_norm_add_norm_sub' y x
    rw [hR']; nlinarith
  have hWF : ∀ m' ∈ refineF (2 ^ k) F, gridSquare ((2 : ℝ)⁻¹ ^ k * ε * r) m' ⊆
      scaleSet r 0 (closedBall (0 : ℂ) R') := by
    intro m' hm' y hy
    have hyB := hsq m' hm' hy
    rw [mem_closedBall, dist_zero_right] at hyB
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    refine ⟨y / r, ?_, by field_simp; ring⟩
    rw [mem_closedBall, dist_zero_right, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le,
      div_le_iff₀ hr]
    exact hyB
  have hcard : (refineF (2 ^ k) F).card ≤ Nc := by
    have hcorner : ∀ m' : ℤ × ℤ, (⟨m'.1 * ((2 : ℝ)⁻¹ ^ k * ε * r),
        m'.2 * ((2 : ℝ)⁻¹ ^ k * ε * r)⟩ : ℂ) ∈ gridSquare ((2 : ℝ)⁻¹ ^ k * ε * r) m' := by
      intro m'
      refine ⟨le_rfl, ?_, le_rfl, ?_⟩
      · show (m'.1 : ℝ) * ((2 : ℝ)⁻¹ ^ k * ε * r) ≤ (m'.1 + 1) * ((2 : ℝ)⁻¹ ^ k * ε * r)
        nlinarith
      · show (m'.2 : ℝ) * ((2 : ℝ)⁻¹ ^ k * ε * r) ≤ (m'.2 + 1) * ((2 : ℝ)⁻¹ ^ k * ε * r)
        nlinarith
    have := card_le_of_meet_ball hs' (refineF (2 ^ k) F) (R := R' * r) fun m' hm' =>
      ⟨_, hcorner m', hsq m' hm' (hcorner m')⟩
    rwa [show R' * r / ((2 : ℝ)⁻¹ ^ k * ε * r) = R' / ((2 : ℝ)⁻¹ ^ k * ε) by
      field_simp] at this
  have hsf : 0 ≤ scaleFac (xiGamma γ) c (h ω) r 0 :=
    mul_nonneg (hD.tightness.1 r hr).le (Real.exp_pos _).le
  refine (l510_conn_tube_diam (D (h ω)) hs' _ hconn hχ0 (mul_nonneg hpow0.le hsf) hWF
    hgood).trans (ENNReal.ofReal_le_ofReal ?_)
  have hc' : ((refineF (2 ^ k) F).card : ℝ) ≤ Nc := by exact_mod_cast hcard
  rw [hA]
  have := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : (2 + 2 * ((refineF (2 ^ k) F).card : ℝ)) ≤
      2 + 2 * (Nc : ℝ)) hW0.le) (mul_nonneg hpow0.le hsf)
  nlinarith

/-- `L510Diam` (condition (5), `L510B.lean`) with the range `0 < γ < 2` of GM (`L510Diam` omits
it; `DFGPSLem3_20` needs it, and `gm_L5_10_of_parts` has it from `PairSetting`) -/
def L510DiamG : Prop := ∀ {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}, 0 < γ → γ < 2 →
  IsWeakLQGMetric γ D c →
  ∀ {ε₀ q : ℝ}, 0 < ε₀ → 0 < q → ∃ A : ℝ, 1 < A ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r →
    P {ω | ¬ ∀ V : Set ℂ, IsOpen V → IsConnected V →
      IsSquareTube V (ε₀ * r) {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r} →
      internalDiam (D (h ω)) V V ≤ ENNReal.ofReal (A * scaleFac (xiGamma γ) c (h ω) r 0)} ≤
      ENNReal.ofReal q

/-- **GM Lemma 5.10, condition (5)** (l. 3313–3320) -/
theorem gm_L510Diam (h320 : DFGPSLem3_20) : L510DiamG := by
  intro γ D c hγ0 hγ2 hD ε₀ q hε₀ hq
  obtain ⟨A, hA, H⟩ := l510_tubes_diam h320 hγ0 hγ2 hD hε₀ (by norm_num : (0 : ℝ) ≤ 2) hq
  refine ⟨A, hA, fun P _ h hh r hr => le_trans (measure_mono ?_) (H P h hh r hr)⟩
  intro ω hω hgood
  apply hω
  rintro V - hVc ⟨F, hFs, rfl⟩
  refine hgood F (fun m hm => ?_) hVc.isPreconnected
  obtain ⟨x, hx1, -, hx2⟩ := hFs hm
  exact ⟨x, hx1, by rw [mem_closedBall, dist_zero_right]; exact hx2⟩

end LQGMetric.GM
