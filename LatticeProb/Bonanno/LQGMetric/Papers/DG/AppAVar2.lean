/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.AppAVar2 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppAVar

/-!
DG (`metric-comparison-final.tex`, DG:2236–2240; (A.3) at DG:2156–2160 for `f = ĥ − ĥ^tr`), in
kernel form, uniformly in the truncation `t ∈ (0, 1]`:

`dg_A2_var : ∃ C, ∀ t ∈ (0,1], ∀ z₁ z₂, π ‖(k_t(z₁) − k^tr_t(z₁)) − (k_t(z₂) − k^tr_t(z₂))‖² ≤ C|z₁ − z₂|`,

where `k_t(z) = phiKernelL2 t 1 z` (kernel of `ĥ_t(z) = √π W(k_t(z))`) and
`k^tr_t(z) = hatTrKernel t z` (kernel of `ĥ^tr_t(z)`), so the left side is
`Var((ĥ_t − ĥ^tr_t)(z₁) − (ĥ_t − ĥ^tr_t)(z₂))`.

Proof: slice the `L²(ℝ × ℂ)` norm in time (`integral_sq_le_slices`), use the per-slice bound
`lintegral_kerDiff_le` for `|z₁ − z₂| ≤ 1/40` and the time integral `lintegral_Icc_diag_sub_le`
with `log((r+δ)/(r−δ)) ≤ 2δ/(r−δ)`; for `|z₁ − z₂| > 1/40` bound each kernel separately by the
exit bound `lintegral_sq_compK_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ

/-- `‖G‖² = ∫ g²` for `G =ᵐ g` in `L²(ℝ × ℂ)`. -/
lemma norm_sq_eq_of_ae {G : WNSpace} {g : ℝ × ℂ → ℝ} (hg : (G : ℝ × ℂ → ℝ) =ᵐ[volume] g) :
    ‖G‖ ^ 2 = ∫ p, g p ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg] with p hp
  rw [hp, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [sq]

/-- Time slicing of `∫ g²` for `g(s, w) = 1_I(s) h(s, w)`. -/
lemma integral_sq_le_slices {g : ℝ × ℂ → ℝ} (hgm : Measurable g) {I : Set ℝ}
    (hI : MeasurableSet I) {h : ℝ → ℂ → ℝ}
    (hgh : ∀ s w, g (s, w) = I.indicator (fun s => h s w) s) {B : ℝ≥0∞}
    (hB : ∫⁻ s in I, ∫⁻ w, ENNReal.ofReal (h s w ^ 2) ≤ B) (hBt : B ≠ ⊤) :
    ∫ p, g p ^ 2 ≤ B.toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun p => sq_nonneg _)
    (hgm.pow_const 2).aestronglyMeasurable]
  refine ENNReal.toReal_mono hBt (le_trans (le_of_eq ?_) hB)
  rw [Measure.volume_eq_prod, lintegral_prod _ (hgm.pow_const 2).ennreal_ofReal.aemeasurable,
    ← lintegral_indicator hI]
  refine lintegral_congr fun s => ?_
  by_cases hs : s ∈ I
  · rw [indicator_of_mem hs]
    refine lintegral_congr fun w => ?_
    rw [hgh, indicator_of_mem hs]
  · rw [indicator_of_notMem hs]
    simp [hgh, indicator_of_notMem hs]

/-- The kernel of `ĥ_t − ĥ^tr_t` at `z` as a function on `ℝ × ℂ`. -/
def kerA (t : ℝ) (z : ℂ) : ℝ × ℂ → ℝ :=
  phiKernel t 1 z - wndKernel (Metric.ball z (1 / 10)) (Icc (t ^ 2) 1) z

lemma measurable_kerA (t : ℝ) (z : ℂ) : Measurable (kerA t z) :=
  (measurable_phiKernel t 1 z).sub (measurable_wndKernel Metric.isOpen_ball measurableSet_Icc z)

lemma kerA_apply (t : ℝ) (z : ℂ) (s : ℝ) (w : ℂ) :
    kerA t z (s, w) = (Icc (t ^ 2) 1).indicator (fun s => kerDiff z s w) s := by
  by_cases hs : s ∈ Icc (t ^ 2) 1
  · simp [kerA, phiKernel, wndKernel, kerDiff, hs]
  · simp [kerA, phiKernel, wndKernel, kerDiff, hs]

lemma coeFn_kernel_sub {t : ℝ} (ht : 0 < t) (z : ℂ) :
    ((phiKernelL2 t 1 z - hatTrKernel t z : WNSpace) : ℝ × ℂ → ℝ) =ᵐ[volume] kerA t z := by
  have hc : (0 : ℝ) < t ^ 2 / 2 := by positivity
  have hI : Icc (t ^ 2) 1 ⊆ Ioi (t ^ 2 / 2) := fun s hs => by
    have := hs.1; simp only [mem_Ioi]; nlinarith [sq_nonneg t]
  have hmem := memLp_wndKernel Metric.isOpen_ball (c := z) (R := 1 / 10) (by norm_num) subset_rfl
    measurableSet_Icc hc hI z
  have e : hatTrKernel t z = hmem.toLp _ := by
    rw [hatTrKernel, wndKernelL2, dite_eq_left_of_eq_true (eq_true hmem)]
  rw [e]
  filter_upwards [Lp.coeFn_sub (phiKernelL2 t 1 z) (hmem.toLp _), coeFn_phiKernelL2 t 1 ht z,
    hmem.coeFn_toLp] with p h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]
  rfl

lemma volume_Icc_sq_le {t : ℝ} : volume (Icc (t ^ 2) 1) ≤ 1 := by
  rw [Real.volume_Icc, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg t])

/-- `∫⁻_{[t²,1]} c ≤ c`. -/
lemma setLIntegral_Icc_const_le {t : ℝ} (c : ℝ≥0∞) : ∫⁻ _ in Icc (t ^ 2) 1, c ≤ c := by
  rw [setLIntegral_const]
  calc c * volume (Icc (t ^ 2) 1) ≤ c * 1 := mul_le_mul_of_nonneg_left volume_Icc_sq_le zero_le
    _ = c := mul_one c

/-- The bound for a single kernel: `‖k_t(z) − k^tr_t(z)‖² ≤ 4374/(4π (1/10)⁶)`. -/
def dgM : ℝ := 4374 / (Real.pi * (1 / 10 : ℝ) ^ 6) * (1 / 4)

lemma dgM_nonneg : 0 ≤ dgM := by unfold dgM; have := Real.pi_pos; positivity

theorem norm_sq_kernel_le {t : ℝ} (ht : 0 < t) (z : ℂ) :
    ‖phiKernelL2 t 1 z - hatTrKernel t z‖ ^ 2 ≤ dgM := by
  rw [norm_sq_eq_of_ae (coeFn_kernel_sub ht z)]
  have hB : ∫⁻ s in Icc (t ^ 2) 1, ∫⁻ w, ENNReal.ofReal (kerDiff z s w ^ 2) ≤
      ENNReal.ofReal dgM := by
    refine le_trans (lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).2
      (ae_of_all _ fun s hs => ?_))) (setLIntegral_Icc_const_le _)
    have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs.1
    have hτ : (s / 2).toNNReal ≠ 0 := by simpa using hs0
    simp_rw [kerDiff_eq_compK hs0]
    refine (lintegral_sq_compK_le Metric.isOpen_ball (by norm_num : (0 : ℝ) < 1 / 10) subset_rfl
      hτ).trans (ENNReal.ofReal_le_ofReal ?_)
    refine (eB_le_sq (by norm_num) (pos_of_ne hτ)).trans ?_
    unfold dgM
    rw [Real.coe_toNNReal _ (by positivity)]
    have := Real.pi_pos
    have h1 : (s / 2) ^ 2 ≤ 1 / 4 := by nlinarith [hs.2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  exact (integral_sq_le_slices (measurable_kerA t z) measurableSet_Icc (kerA_apply t z) hB
    ENNReal.ofReal_ne_top).trans (le_of_eq (ENNReal.toReal_ofReal dgM_nonneg))

/-- The constant for `|z₁ − z₂| ≤ 1/40`. -/
def dgCs : ℝ := 2 * dgC0 + 2 * (80 / 3) / Real.pi

theorem norm_sq_kernel_sub_le_small {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) {z₁ z₂ : ℂ}
    (hδ : ‖z₁ - z₂‖ ≤ 1 / 40) :
    ‖(phiKernelL2 t 1 z₁ - hatTrKernel t z₁) - (phiKernelL2 t 1 z₂ - hatTrKernel t z₂)‖ ^ 2 ≤
      dgCs * ‖z₁ - z₂‖ := by
  have hpi := Real.pi_pos
  have hCs : 0 ≤ dgCs := by unfold dgCs; have := dgC0_nonneg; positivity
  set δ := ‖z₁ - z₂‖ with hδdef
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hae : (((phiKernelL2 t 1 z₁ - hatTrKernel t z₁) - (phiKernelL2 t 1 z₂ - hatTrKernel t z₂) :
      WNSpace) : ℝ × ℂ → ℝ) =ᵐ[volume] kerA t z₁ - kerA t z₂ := by
    filter_upwards [Lp.coeFn_sub (phiKernelL2 t 1 z₁ - hatTrKernel t z₁)
      (phiKernelL2 t 1 z₂ - hatTrKernel t z₂), coeFn_kernel_sub ht z₁, coeFn_kernel_sub ht z₂]
      with p h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, Pi.sub_apply]
  rw [norm_sq_eq_of_ae hae]
  have hgh : ∀ s w, (kerA t z₁ - kerA t z₂) (s, w) =
      (Icc (t ^ 2) 1).indicator (fun s => kerDiff z₁ s w - kerDiff z₂ s w) s := by
    intro s w
    rw [Pi.sub_apply, kerA_apply, kerA_apply]
    by_cases hs : s ∈ Icc (t ^ 2) 1 <;> simp [hs]
  have ha : 0 < t ^ 2 := by positivity
  have ha1 : t ^ 2 ≤ 1 := by nlinarith
  set Kd : ℝ → ℝ := fun s => killedHeat (Metric.ball z₂ (1 / 10 + δ)) s.toNNReal z₂ z₂ -
    killedHeat (Metric.ball z₂ (1 / 10 - δ)) s.toNNReal z₂ z₂
  have hlog : Real.log ((1 / 10 + δ) / (1 / 10 - δ)) ≤ 80 / 3 * δ := by
    have hpos : 0 < (1 / 10 + δ) / (1 / 10 - δ) := div_pos (by linarith) (by linarith)
    refine (Real.log_le_sub_one_of_pos hpos).trans ?_
    rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
    nlinarith
  have hB : ∫⁻ s in Icc (t ^ 2) 1, ∫⁻ w,
      ENNReal.ofReal ((kerDiff z₁ s w - kerDiff z₂ s w) ^ 2) ≤
      ENNReal.ofReal (dgCs * δ) := by
    calc ∫⁻ s in Icc (t ^ 2) 1, ∫⁻ w, ENNReal.ofReal ((kerDiff z₁ s w - kerDiff z₂ s w) ^ 2)
        ≤ ∫⁻ s in Icc (t ^ 2) 1, (2 * ENNReal.ofReal (dgC0 * δ) + 2 * ENNReal.ofReal (Kd s)) :=
          lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun s hs =>
            lintegral_kerDiff_le (lt_of_lt_of_le ha hs.1) hδ))
      _ = (∫⁻ s in Icc (t ^ 2) 1, 2 * ENNReal.ofReal (dgC0 * δ)) +
            2 * ∫⁻ s in Icc (t ^ 2) 1, ENNReal.ofReal (Kd s) := by
          rw [lintegral_add_left' aemeasurable_const,
            lintegral_const_mul' 2 (fun s => ENNReal.ofReal (Kd s)) (by simp)]
      _ ≤ 2 * ENNReal.ofReal (dgC0 * δ) +
            2 * ENNReal.ofReal (Real.log ((1 / 10 + δ) / (1 / 10 - δ)) / Real.pi) := by
          refine add_le_add (setLIntegral_Icc_const_le _) (mul_le_mul_of_nonneg_left ?_ zero_le)
          exact lintegral_Icc_diag_sub_le z₂ hδ0 (by linarith) ha ha1
      _ ≤ ENNReal.ofReal (dgCs * δ) := by
          have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
          have hl0 : 0 ≤ Real.log ((1 / 10 + δ) / (1 / 10 - δ)) / Real.pi :=
            div_nonneg (Real.log_nonneg ((one_le_div (by linarith)).2 (by linarith))) hpi.le
          rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by have := dgC0_nonneg; positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          unfold dgCs
          have : Real.log ((1 / 10 + δ) / (1 / 10 - δ)) / Real.pi ≤ 80 / 3 * δ / Real.pi :=
            div_le_div_of_nonneg_right hlog hpi.le
          have e : (2 * dgC0 + 2 * (80 / 3) / Real.pi) * δ =
              2 * (dgC0 * δ) + 2 * (80 / 3 * δ / Real.pi) := by ring
          rw [e]
          linarith
  exact (integral_sq_le_slices ((measurable_kerA t z₁).sub (measurable_kerA t z₂))
    measurableSet_Icc hgh hB ENNReal.ofReal_ne_top).trans
    (le_of_eq (ENNReal.toReal_ofReal (mul_nonneg hCs hδ0)))

/-- **DG Lemma A.2, variance bound** (DG:2236–2240 with (A.3)):
`Var((ĥ_t − ĥ^tr_t)(z₁) − (ĥ_t − ĥ^tr_t)(z₂)) = π ‖…‖² ≤ C |z₁ − z₂|`, uniformly in `t ∈ (0, 1]`. -/
theorem dg_A2_var : ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ z₁ z₂ : ℂ,
    Real.pi * ‖(phiKernelL2 t 1 z₁ - hatTrKernel t z₁) -
      (phiKernelL2 t 1 z₂ - hatTrKernel t z₂)‖ ^ 2 ≤ C * ‖z₁ - z₂‖ := by
  refine ⟨Real.pi * (dgCs + 160 * dgM), fun t ht z₁ z₂ => ?_⟩
  have hpi := Real.pi_pos
  have hM := dgM_nonneg
  have hCs : 0 ≤ dgCs := by unfold dgCs; have := dgC0_nonneg; positivity
  have hδ0 : 0 ≤ ‖z₁ - z₂‖ := norm_nonneg _
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hpi.le
  rcases le_or_gt ‖z₁ - z₂‖ (1 / 40) with hδ | hδ
  · refine (norm_sq_kernel_sub_le_small ht.1 ht.2 hδ).trans ?_
    nlinarith [mul_nonneg hM hδ0]
  · set F₁ := phiKernelL2 t 1 z₁ - hatTrKernel t z₁
    set F₂ := phiKernelL2 t 1 z₂ - hatTrKernel t z₂
    have h1 := norm_sq_kernel_le ht.1 z₁
    have h2 := norm_sq_kernel_le ht.1 z₂
    have htri : ‖F₁ - F₂‖ ≤ ‖F₁‖ + ‖F₂‖ := norm_sub_le _ _
    have hsq : ‖F₁ - F₂‖ ^ 2 ≤ 2 * ‖F₁‖ ^ 2 + 2 * ‖F₂‖ ^ 2 := by
      nlinarith [norm_nonneg (F₁ - F₂), sq_nonneg (‖F₁‖ - ‖F₂‖), norm_nonneg F₁, norm_nonneg F₂]
    nlinarith [mul_nonneg hCs hδ0]

end DG
end LQGMetric
