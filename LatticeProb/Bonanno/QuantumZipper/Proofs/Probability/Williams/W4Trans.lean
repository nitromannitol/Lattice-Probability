/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W4Trans at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W4Cond

/-!
Node W4 of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1): `lintegral_shift_postLast`.

This file discharges the hypothesis `hgood` of `lintegral_shift_postLast_of_ae` (`W4Cond.lean`):
almost surely the drift Brownian motion `Y = dpath σ μ b` (`σ, μ > 0`) has a last zero, after
which it is positive (transience; Revuz–Yor, *Continuous Martingales and Brownian Motion*, VII §3
and XI; Williams 1974). The argument is own bookkeeping on the committed W1/W3 inputs:

* `P(Y has a zero after n) = E h(Y_n)` with `h(y) = P(τ_{-y} < ∞)` (Markov property at `n`);
* `h(y) ≤ K · occ((y + ·)⁻¹[-1,1])` for all `y` (for `y ≤ 0` because the occupation density is
  `1/μ` on `[0,∞)`; for `y > 0` by `occ_shift_neg`: `h(y) · occ(-1,0] = occ(-y-1,-y]`);
* `E occ((Y_n + ·)⁻¹[-1,1]) = ∫_n^∞ P(Y_t ∈ [-1,1]) dt → 0`, the tail of `occ [-1,1] < ∞`;
* hence `P(zeros unbounded) = 0`, and a path that hits every positive integer level is positive
  after its last zero (intermediate value theorem).
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ} {σ μ : ℝ}

/-- A continuous path with bounded zero set that hits every level `k + 1` is positive after its
last zero. Own elementary proof (intermediate value theorem). -/
theorem pos_after_lastPass {w : ℝ≥0 → ℝ} (hw : Continuous w) (hbdd : BddAbove {t | w t = 0})
    (hhit : ∀ k : ℕ, ∃ t, w t = (k : ℝ) + 1) : ∀ t, lastPass w 0 < t → 0 < w t := by
  intro t ht
  have hnz : ∀ s, lastPass w 0 < s → w s ≠ 0 := fun s hs h0 =>
    absurd (le_csSup hbdd (show s ∈ {t | w t = 0} from h0)) (not_le.2 hs)
  by_contra hneg
  have hlt : w t < 0 := lt_of_le_of_ne (not_lt.1 hneg) (hnz t ht)
  have hall : ∀ s, lastPass w 0 < s → w s < 0 := by
    intro s hs
    by_contra hge
    obtain ⟨z, hz, hz0⟩ := intermediate_value_uIcc (a := t) (b := s) hw.continuousOn
      (show (0 : ℝ) ∈ Set.uIcc (w t) (w s) from Set.mem_uIcc.2 (Or.inl ⟨hlt.le, not_lt.1 hge⟩))
    have hzL : lastPass w 0 < z := lt_of_lt_of_le (lt_min ht hs) hz.1
    exact hnz z hzL hz0
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := lastPass w 0)).bddAbove_image
    hw.continuousOn
  obtain ⟨k, hk⟩ := exists_nat_gt M
  obtain ⟨s, hs⟩ := hhit k
  rcases le_or_gt s (lastPass w 0) with hsL | hsL
  · have := hM ⟨s, ⟨zero_le, hsL⟩, rfl⟩
    rw [hs] at this
    linarith
  · have := hall s hsL
    rw [hs] at this
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith

/-- The occupation density is positive everywhere (its integrand is a positive Gaussian density).
Own elementary proof. -/
theorem occDens_pos (hσ : 0 < σ) (hμ : 0 < μ) (y : ℝ) : 0 < occDens σ μ y := by
  rw [occDens, integral_pos_iff_support_of_nonneg (fun m => gaussianPDFReal_nonneg _ _ _)
    (integrable_occDens_integrand hσ hμ y)]
  have hsub : Set.Ioi (0 : ℝ) ⊆ Function.support fun m => gaussianPDFReal (μ * m) (occVar σ m) y :=
    fun m hm => (gaussianPDFReal_pos _ _ _ (occVar_ne_zero hm hσ.ne')).ne'
  calc (0 : ℝ≥0∞) < volume (Set.Ioi (0 : ℝ)) := by simp
    _ = (volume.restrict (Set.Ioi (0 : ℝ))) (Set.Ioi 0) := by rw [Measure.restrict_apply_self]
    _ ≤ _ := measure_mono hsub

theorem occ_Ioc_neg_one_pos (hσ : 0 < σ) (hμ : 0 < μ) : 0 < occ σ μ (Set.Ioc (-1) 0) := by
  rw [occ_Ioc_eq_ofReal_integral hσ hμ (by norm_num)]
  exact ENNReal.ofReal_pos.2 (intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_occDens hσ hμ).intervalIntegrable _ _) (fun x _ => occDens_pos hσ hμ x)
    (by norm_num))

theorem occ_Ioc_neg_one_ne_top (hσ : 0 < σ) (hμ : 0 < μ) : occ σ μ (Set.Ioc (-1) 0) ≠ ⊤ := by
  rw [occ_Ioc_eq_ofReal_integral hσ hμ (by norm_num)]
  exact ENNReal.ofReal_ne_top

theorem occ_Ioc_pos_eq (hσ : 0 < σ) (hμ : 0 < μ) {a : ℝ} (ha : 0 ≤ a) :
    occ σ μ (Set.Ioc a (a + 1)) = ENNReal.ofReal (1 / μ) := by
  rw [occ_Ioc_eq_ofReal_integral hσ hμ (by linarith)]
  congr 1
  rw [intervalIntegral.integral_congr (g := fun _ => 1 / μ) (fun x hx => ?_),
    intervalIntegral.integral_const, smul_eq_mul]
  · ring
  · have hx' : a ≤ x := by
      rw [Set.uIcc_of_le (by linarith)] at hx
      exact hx.1
    simp only
    rw [occDens_nonneg_const hσ hμ x (by linarith), occDens_zero_eq_inv_mu hσ hμ]

/-- **The hitting probability of `-y` is dominated by an occupation measure.** -/
theorem prob_zero_le (hb : GoodBM b P) (hσ : 0 < σ) (hμ : 0 < μ) (y : ℝ) :
    ∫⁻ ω, zeroSet.indicator (1 : (ℝ≥0 → ℝ) → ℝ≥0∞) (fun u => y + dpath σ μ b ω u) ∂P ≤
      (ENNReal.ofReal μ + (occ σ μ (Set.Ioc (-1) 0))⁻¹)
        * occ σ μ ((fun z => y + z) ⁻¹' Set.Icc (-1) 1) := by
  haveI := isProbabilityMeasure_of_goodBM hb
  set c' := occ σ μ (Set.Ioc (-1) 0) with hc'
  have hm : Measurable fun ω => fun u : ℝ≥0 => y + dpath σ μ b ω u :=
    measurable_pi_iff.2 fun u => measurable_const.add (measurable_dpath hb σ μ u)
  have hS : {ω | ∃ t, dpath σ μ b ω t = -y}
      = (fun ω => fun u : ℝ≥0 => y + dpath σ μ b ω u) ⁻¹' zeroSet := by
    ext ω
    simp only [mem_setOf_eq, mem_preimage]
    rw [mem_zeroSet_iff (show Continuous fun u : ℝ≥0 => y + dpath σ μ b ω u from
      continuous_const.add (continuous_dpath hb σ μ ω))]
    constructor <;> rintro ⟨t, ht⟩ <;> exact ⟨t, by linarith⟩
  have hset : ∫⁻ ω, zeroSet.indicator (1 : (ℝ≥0 → ℝ) → ℝ≥0∞) (fun u => y + dpath σ μ b ω u) ∂P
      = P {ω | ∃ t, dpath σ μ b ω t = -y} := by
    rw [hS, ← lintegral_indicator_one (measurableSet_zeroSet.preimage hm)]
    rfl
  rw [hset]
  rcases le_or_gt y 0 with hy | hy
  · calc P {ω | ∃ t, dpath σ μ b ω t = -y} ≤ 1 := prob_le_one
      _ = ENNReal.ofReal μ * ENNReal.ofReal (1 / μ) := by
          rw [← ENNReal.ofReal_mul hμ.le, mul_one_div_cancel hμ.ne', ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal μ * occ σ μ ((fun z => y + z) ⁻¹' Set.Icc (-1) 1) := by
          gcongr
          rw [← occ_Ioc_pos_eq hσ hμ (show 0 ≤ -y by linarith)]
          refine measure_mono fun z hz => ?_
          simp only [mem_preimage, mem_Icc]
          simp only [mem_Ioc] at hz
          constructor <;> linarith [hz.1, hz.2]
      _ ≤ _ := by gcongr; exact le_self_add
  · have hshift := occ_shift_neg hb σ μ (show -y < 0 by linarith) (A := Set.Ioc (-y - 1) (-y))
      measurableSet_Ioc Set.Ioc_subset_Iic_self
    have hpre : (fun z => z + -y) ⁻¹' Set.Ioc (-y - 1) (-y) = Set.Ioc (-1) 0 := by
      ext z
      simp only [mem_preimage, mem_Ioc]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [hpre] at hshift
    have hc'0 : c' ≠ 0 := (occ_Ioc_neg_one_pos hσ hμ).ne'
    have hc'top : c' ≠ ⊤ := occ_Ioc_neg_one_ne_top hσ hμ
    have hle : occ σ μ (Set.Ioc (-y - 1) (-y))
        ≤ occ σ μ ((fun z => y + z) ⁻¹' Set.Icc (-1) 1) := by
      refine measure_mono fun z hz => ?_
      simp only [mem_preimage, mem_Icc]
      simp only [mem_Ioc] at hz
      constructor <;> linarith [hz.1, hz.2]
    calc P {ω | ∃ t, dpath σ μ b ω t = -y}
        = P {ω | ∃ t, dpath σ μ b ω t = -y} * c' * c'⁻¹ := by
          rw [mul_assoc, ENNReal.mul_inv_cancel hc'0 hc'top, mul_one]
      _ = occ σ μ (Set.Ioc (-y - 1) (-y)) * c'⁻¹ := by rw [hshift]
      _ ≤ occ σ μ ((fun z => y + z) ⁻¹' Set.Icc (-1) 1) * c'⁻¹ := by gcongr
      _ = c'⁻¹ * occ σ μ ((fun z => y + z) ⁻¹' Set.Icc (-1) 1) := mul_comm _ _
      _ ≤ _ := by gcongr; exact le_add_self

end QuantumZipper.Williams
