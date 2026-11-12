/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.AppA1Var at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppA1SP2
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppAVar2

/-!
DG (`metric-comparison-final.tex`, proof of Lemma A.1, DG:2141–2232): for a bounded open `U`,
`f_t(z) = h^U_{t,1}(z) − ĥ^tr_t(z) = √π ∫_{t²}^1 ∫ q_s(z, w) W(dw, ds)` with
`q_s(z, ·) = p_U(s/2; z, ·) − p_{B_{1/10}(z)}(s/2; z, ·)`, and (A.3):
`Var(f(z₁) − f(z₂)) ≲ |z₁ − z₂|` on `K = {z : dist(z, ∂U) ≥ 1/10}` (here: `B(z, 1/10) ⊆ U`).

* `lintegral_kerU_le` — per time slice (start-point change in `B(z₁, 1/10)` via
  `lintegral_sq_compK2_sub_le_unif`, recentring via `integral_sq_recentre_le`);
* `dg_A1_var` — (A.3) for `f_t`, uniformly in `t ∈ (0, 1]`.

The identification of `h^U = lim_{t→0} h^U_{t,∞}` with the zero-boundary GFF ([RV review,
Lemma 5.4], DG:2146) is not part of this file (handoff/P2-DG3B.md). Own semigroup route
(DEVIATIONS DG3B-1, DG3B-2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ

/-- DG's constant for the start-point term of A.1 with `ρ = 3/40`. -/
def dgC1 : ℝ := 3 / (4 * Real.pi) + 87480 / (Real.pi * (3 / 40 : ℝ) ^ 6)

lemma dgC1_nonneg : 0 ≤ dgC1 := by unfold dgC1; have := Real.pi_pos; positivity

/-- The kernel `q_s(z, w) = p_U(s/2; z, w) − p_{B_{1/10}(z)}(s/2; z, w)` of A.1. -/
def kerU (U : Set ℂ) (z : ℂ) (s : ℝ) (w : ℂ) : ℝ :=
  killedHeat U (s / 2).toNNReal z w - killedHeat (Metric.ball z (1 / 10)) (s / 2).toNNReal z w

/-- **Per-slice bound** for A.1's kernel, `δ = |z₁ − z₂| ≤ 1/40`, `B(z₁, 1/10) ⊆ U`. -/
theorem lintegral_kerU_le {U : Set ℂ} (hU : IsOpen U) {s : ℝ} (hs : 0 < s) {z₁ z₂ : ℂ}
    (hz₁ : Metric.ball z₁ (1 / 10) ⊆ U) (hδ : ‖z₁ - z₂‖ ≤ 1 / 40) :
    ∫⁻ w, ENNReal.ofReal ((kerU U z₁ s w - kerU U z₂ s w) ^ 2) ≤
      2 * ENNReal.ofReal (dgC1 * ‖z₁ - z₂‖) +
        2 * ENNReal.ofReal (killedHeat (Metric.ball z₂ (1 / 10 + ‖z₁ - z₂‖)) s.toNNReal z₂ z₂ -
          killedHeat (Metric.ball z₂ (1 / 10 - ‖z₁ - z₂‖)) s.toNNReal z₂ z₂) := by
  set τ : ℝ≥0 := (s / 2).toNNReal with hτdef
  have hτ : τ ≠ 0 := by simpa [hτdef] using hs
  have hττ : τ + τ = s.toNNReal := by
    rw [hτdef, ← Real.toNNReal_add (by positivity) (by positivity)]; ring_nf
  set B₁ := Metric.ball z₁ (1 / 10 : ℝ)
  set B₂ := Metric.ball z₂ (1 / 10 : ℝ)
  set SP : ℂ → ℝ := fun w => compK2 U B₁ τ z₁ w - compK2 U B₁ τ z₂ w
  set RC : ℂ → ℝ := fun w => killedHeat B₁ τ z₂ w - killedHeat B₂ τ z₂ w
  have hpt : ∀ w, kerU U z₁ s w - kerU U z₂ s w = SP w - RC w := by
    intro w
    simp only [kerU, SP, RC, compK2]
    ring
  have hSPm : Measurable SP :=
    (measurable_compK2_right hU Metric.isOpen_ball hτ z₁).sub
      (measurable_compK2_right hU Metric.isOpen_ball hτ z₂)
  -- the start-point term
  have hd : dist z₁ z₂ ≤ 1 / 40 := by rwa [dist_eq_norm]
  have hb1 : Metric.ball z₁ (3 / 40) ⊆ B₁ := Metric.ball_subset_ball (by norm_num)
  have hb2 : Metric.ball z₂ (3 / 40) ⊆ B₁ := fun w hw => by
    rw [Metric.mem_ball] at hw ⊢
    linarith [dist_triangle w z₂ z₁, dist_comm z₁ z₂]
  have hSP := lintegral_sq_compK2_sub_le_unif hU Metric.isOpen_ball hz₁
    (by norm_num : (0 : ℝ) < 3 / 40) hb1 hb2 hτ
  -- the recentring term
  have hRC : ∫⁻ w, ENNReal.ofReal (RC w ^ 2) ≤
      ENNReal.ofReal (killedHeat (Metric.ball z₂ (1 / 10 + ‖z₁ - z₂‖)) s.toNNReal z₂ z₂ -
          killedHeat (Metric.ball z₂ (1 / 10 - ‖z₁ - z₂‖)) s.toNNReal z₂ z₂) := by
    have hint : Integrable fun w => RC w ^ 2 := by
      refine (WhiteNoise.integrable_heatKernel_mul_heatKernel _ (pos_of_ne hτ) z₂ z₂).mono'
        (((measurable_killedHeat_right Metric.isOpen_ball hτ z₂).sub
          (measurable_killedHeat_right Metric.isOpen_ball hτ z₂)).pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun w => ?_)
      have a1 := killedHeat_nonneg B₁ τ z₂ w
      have a2 := killedHeat_nonneg B₂ τ z₂ w
      have a3 := killedHeat_le_heatKernel B₁ τ z₂ w
      have a4 := killedHeat_le_heatKernel B₂ τ z₂ w
      rw [Real.norm_of_nonneg (sq_nonneg _), sq]
      simp only [RC]
      have : |killedHeat B₁ τ z₂ w - killedHeat B₂ τ z₂ w| ≤ heatKernel τ z₂ w := by
        rw [abs_le]; constructor <;> linarith
      calc (killedHeat B₁ τ z₂ w - killedHeat B₂ τ z₂ w) *
            (killedHeat B₁ τ z₂ w - killedHeat B₂ τ z₂ w)
          = |killedHeat B₁ τ z₂ w - killedHeat B₂ τ z₂ w| *
            |killedHeat B₁ τ z₂ w - killedHeat B₂ τ z₂ w| := (abs_mul_abs_self _).symm
        _ ≤ heatKernel τ z₂ w * heatKernel τ z₂ w :=
            mul_le_mul this this (abs_nonneg _) (heatKernel_nonneg' _ _ _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun w => sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := integral_sq_recentre_le (r := 1 / 10) (δ := ‖z₁ - z₂‖) (z₁ := z₁) (z₂ := z₂)
      le_rfl hτ
    rw [hττ] at h
    exact h
  calc ∫⁻ w, ENNReal.ofReal ((kerU U z₁ s w - kerU U z₂ s w) ^ 2)
      ≤ ∫⁻ w, (2 * ENNReal.ofReal (SP w ^ 2) + 2 * ENNReal.ofReal (RC w ^ 2)) :=
        lintegral_mono fun w => by rw [hpt w]; exact ofReal_sq_sub_le _ _
    _ = 2 * (∫⁻ w, ENNReal.ofReal (SP w ^ 2)) + 2 * ∫⁻ w, ENNReal.ofReal (RC w ^ 2) := by
        rw [lintegral_add_left' (((hSPm.pow_const 2).ennreal_ofReal).const_mul 2).aemeasurable,
          lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp)]
    _ ≤ _ := by
        refine add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le)
          (mul_le_mul_of_nonneg_left hRC zero_le)
        exact hSP.trans (le_of_eq (by rfl))


/-- The kernel of `h^U_{t,1} − ĥ^tr_t` at `z` as a function on `ℝ × ℂ`. -/
def kerAU (U : Set ℂ) (t : ℝ) (z : ℂ) : ℝ × ℂ → ℝ :=
  wndKernel U (Icc (t ^ 2) 1) z - wndKernel (Metric.ball z (1 / 10)) (Icc (t ^ 2) 1) z

lemma measurable_kerAU {U : Set ℂ} (hU : IsOpen U) (t : ℝ) (z : ℂ) : Measurable (kerAU U t z) :=
  (measurable_wndKernel hU measurableSet_Icc z).sub (measurable_wndKernel Metric.isOpen_ball measurableSet_Icc z)

lemma kerAU_apply (U : Set ℂ) (t : ℝ) (z : ℂ) (s : ℝ) (w : ℂ) :
    kerAU U t z (s, w) = (Icc (t ^ 2) 1).indicator (fun s => kerU U z s w) s := by
  by_cases hs : s ∈ Icc (t ^ 2) 1
  · simp [kerAU, wndKernel, kerU, hs]
  · simp [kerAU, wndKernel, kerU, hs]

lemma coeFn_kernelU_sub {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ Metric.ball c R) {t : ℝ} (ht : 0 < t) (z : ℂ) :
    ((wndKernelL2 U (Icc (t ^ 2) 1) z - hatTrKernel t z : WNSpace) : ℝ × ℂ → ℝ) =ᵐ[volume]
      kerAU U t z := by
  have hc : (0 : ℝ) < t ^ 2 / 2 := by positivity
  have hI : Icc (t ^ 2) 1 ⊆ Ioi (t ^ 2 / 2) := fun s hs => by
    have := hs.1; simp only [mem_Ioi]; nlinarith [sq_nonneg t]
  have hmem := memLp_wndKernel Metric.isOpen_ball (c := z) (R := 1 / 10) (by norm_num) subset_rfl
    measurableSet_Icc hc hI z
  have e : hatTrKernel t z = hmem.toLp _ := by
    rw [hatTrKernel, wndKernelL2, dite_eq_left_of_eq_true (eq_true hmem)]
  have hmU := memLp_wndKernel hU hR hUR measurableSet_Icc hc hI z
  have eU : wndKernelL2 U (Icc (t ^ 2) 1) z = hmU.toLp _ := by
    rw [wndKernelL2, dite_eq_left_of_eq_true (eq_true hmU)]
  rw [e, eU]
  filter_upwards [Lp.coeFn_sub (hmU.toLp _) (hmem.toLp _), hmU.coeFn_toLp,
    hmem.coeFn_toLp] with p h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]
  rfl

theorem norm_sq_kernelU_le {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ Metric.ball c R) {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : Metric.ball z (1 / 10) ⊆ U) :
    ‖wndKernelL2 U (Icc (t ^ 2) 1) z - hatTrKernel t z‖ ^ 2 ≤ dgM := by
  rw [norm_sq_eq_of_ae (coeFn_kernelU_sub hU hR hUR ht z)]
  have hB : ∫⁻ s in Icc (t ^ 2) 1, ∫⁻ w, ENNReal.ofReal (kerU U z s w ^ 2) ≤
      ENNReal.ofReal dgM := by
    refine le_trans (lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).2
      (ae_of_all _ fun s hs => ?_))) (setLIntegral_Icc_const_le _)
    have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs.1
    have hτ : (s / 2).toNNReal ≠ 0 := by simpa using hs0
    refine (lintegral_sq_compK2_le Metric.isOpen_ball hz (by norm_num : (0 : ℝ) < 1 / 10)
      subset_rfl hτ).trans (ENNReal.ofReal_le_ofReal ?_)
    refine (eB_le_sq (by norm_num) (pos_of_ne hτ)).trans ?_
    unfold dgM
    rw [Real.coe_toNNReal _ (by positivity)]
    have := Real.pi_pos
    have h1 : (s / 2) ^ 2 ≤ 1 / 4 := by nlinarith [hs.2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  exact (integral_sq_le_slices (measurable_kerAU hU t z) measurableSet_Icc (kerAU_apply U t z) hB
    ENNReal.ofReal_ne_top).trans (le_of_eq (ENNReal.toReal_ofReal dgM_nonneg))

/-- The constant for `|z₁ − z₂| ≤ 1/40` (A.1). -/
def dgCsU : ℝ := 2 * dgC1 + 2 * (80 / 3) / Real.pi

theorem norm_sq_kernelU_sub_le_small {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ Metric.ball c R) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) {z₁ z₂ : ℂ}
    (hz₁ : Metric.ball z₁ (1 / 10) ⊆ U) (hδ : ‖z₁ - z₂‖ ≤ 1 / 40) :
    ‖(wndKernelL2 U (Icc (t ^ 2) 1) z₁ - hatTrKernel t z₁) -
      (wndKernelL2 U (Icc (t ^ 2) 1) z₂ - hatTrKernel t z₂)‖ ^ 2 ≤ dgCsU * ‖z₁ - z₂‖ := by
  have hpi := Real.pi_pos
  have hCs : 0 ≤ dgCsU := by unfold dgCsU; have := dgC1_nonneg; positivity
  set δ := ‖z₁ - z₂‖ with hδdef
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hae : (((wndKernelL2 U (Icc (t ^ 2) 1) z₁ - hatTrKernel t z₁) - (wndKernelL2 U (Icc (t ^ 2) 1) z₂ - hatTrKernel t z₂) :
      WNSpace) : ℝ × ℂ → ℝ) =ᵐ[volume] kerAU U t z₁ - kerAU U t z₂ := by
    filter_upwards [Lp.coeFn_sub (wndKernelL2 U (Icc (t ^ 2) 1) z₁ - hatTrKernel t z₁)
      (wndKernelL2 U (Icc (t ^ 2) 1) z₂ - hatTrKernel t z₂), coeFn_kernelU_sub hU hR hUR ht z₁, coeFn_kernelU_sub hU hR hUR ht z₂]
      with p h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, Pi.sub_apply]
  rw [norm_sq_eq_of_ae hae]
  have hgh : ∀ s w, (kerAU U t z₁ - kerAU U t z₂) (s, w) =
      (Icc (t ^ 2) 1).indicator (fun s => kerU U z₁ s w - kerU U z₂ s w) s := by
    intro s w
    rw [Pi.sub_apply, kerAU_apply, kerAU_apply]
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
      ENNReal.ofReal ((kerU U z₁ s w - kerU U z₂ s w) ^ 2) ≤
      ENNReal.ofReal (dgCsU * δ) := by
    calc ∫⁻ s in Icc (t ^ 2) 1, ∫⁻ w, ENNReal.ofReal ((kerU U z₁ s w - kerU U z₂ s w) ^ 2)
        ≤ ∫⁻ s in Icc (t ^ 2) 1, (2 * ENNReal.ofReal (dgC1 * δ) + 2 * ENNReal.ofReal (Kd s)) :=
          lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun s hs =>
            lintegral_kerU_le hU (lt_of_lt_of_le ha hs.1) hz₁ hδ))
      _ = (∫⁻ s in Icc (t ^ 2) 1, 2 * ENNReal.ofReal (dgC1 * δ)) +
            2 * ∫⁻ s in Icc (t ^ 2) 1, ENNReal.ofReal (Kd s) := by
          rw [lintegral_add_left' aemeasurable_const,
            lintegral_const_mul' 2 (fun s => ENNReal.ofReal (Kd s)) (by simp)]
      _ ≤ 2 * ENNReal.ofReal (dgC1 * δ) +
            2 * ENNReal.ofReal (Real.log ((1 / 10 + δ) / (1 / 10 - δ)) / Real.pi) := by
          refine add_le_add (setLIntegral_Icc_const_le _) (mul_le_mul_of_nonneg_left ?_ zero_le)
          exact lintegral_Icc_diag_sub_le z₂ hδ0 (by linarith) ha ha1
      _ ≤ ENNReal.ofReal (dgCsU * δ) := by
          have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
          have hl0 : 0 ≤ Real.log ((1 / 10 + δ) / (1 / 10 - δ)) / Real.pi :=
            div_nonneg (Real.log_nonneg ((one_le_div (by linarith)).2 (by linarith))) hpi.le
          rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by have := dgC1_nonneg; positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          unfold dgCsU
          have : Real.log ((1 / 10 + δ) / (1 / 10 - δ)) / Real.pi ≤ 80 / 3 * δ / Real.pi :=
            div_le_div_of_nonneg_right hlog hpi.le
          have e : (2 * dgC1 + 2 * (80 / 3) / Real.pi) * δ =
              2 * (dgC1 * δ) + 2 * (80 / 3 * δ / Real.pi) := by ring
          rw [e]
          linarith
  exact (integral_sq_le_slices ((measurable_kerAU hU t z₁).sub (measurable_kerAU hU t z₂))
    measurableSet_Icc hgh hB ENNReal.ofReal_ne_top).trans
    (le_of_eq (ENNReal.toReal_ofReal (mul_nonneg hCs hδ0)))

/-- **DG (A.3) for Lemma A.1** (DG:2156–2232): for a bounded open `U`, uniformly in
`t ∈ (0, 1]` and `z₁, z₂ ∈ K = {z : B(z, 1/10) ⊆ U}`,
`Var(f_t(z₁) − f_t(z₂)) = π ‖…‖² ≤ C |z₁ − z₂|` for `f_t = h^U_{t,1} − ĥ^tr_t`
(`h^U_{t,1}(z) = √π ∫_{t²}^1 ∫ p_U(s/2; z, w) W(dw, ds)`, DG:2144). -/
theorem dg_A1_var {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ z₁ z₂ : ℂ, Metric.ball z₁ (1 / 10) ⊆ U →
      Metric.ball z₂ (1 / 10) ⊆ U →
      Real.pi * ‖(wndKernelL2 U (Icc (t ^ 2) 1) z₁ - hatTrKernel t z₁) -
        (wndKernelL2 U (Icc (t ^ 2) 1) z₂ - hatTrKernel t z₂)‖ ^ 2 ≤ C * ‖z₁ - z₂‖ := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).1 hUb
  have hR' : U ⊆ Metric.ball 0 (max R 0) :=
    hR.trans (Metric.ball_subset_ball (le_max_left _ _))
  have hR0 : (0 : ℝ) ≤ max R 0 := le_max_right _ _
  refine ⟨Real.pi * (dgCsU + 160 * dgM), fun t ht z₁ z₂ hz₁ hz₂ => ?_⟩
  have hpi := Real.pi_pos
  have hM := dgM_nonneg
  have hCs : 0 ≤ dgCsU := by unfold dgCsU; have := dgC1_nonneg; positivity
  have hδ0 : 0 ≤ ‖z₁ - z₂‖ := norm_nonneg _
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hpi.le
  rcases le_or_gt ‖z₁ - z₂‖ (1 / 40) with hδ | hδ
  · refine (norm_sq_kernelU_sub_le_small hU hR0 hR' ht.1 ht.2 hz₁ hδ).trans ?_
    nlinarith [mul_nonneg hM hδ0]
  · set F₁ := wndKernelL2 U (Icc (t ^ 2) 1) z₁ - hatTrKernel t z₁
    set F₂ := wndKernelL2 U (Icc (t ^ 2) 1) z₂ - hatTrKernel t z₂
    have h1 := norm_sq_kernelU_le hU hR0 hR' ht.1 hz₁
    have h2 := norm_sq_kernelU_le hU hR0 hR' ht.1 hz₂
    have htri : ‖F₁ - F₂‖ ≤ ‖F₁‖ + ‖F₂‖ := norm_sub_le _ _
    have hsq : ‖F₁ - F₂‖ ^ 2 ≤ 2 * ‖F₁‖ ^ 2 + 2 * ‖F₂‖ ^ 2 := by
      nlinarith [norm_nonneg (F₁ - F₂), sq_nonneg (‖F₁‖ - ‖F₂‖), norm_nonneg F₁, norm_nonneg F₂]
    nlinarith [mul_nonneg hCs hδ0]

end DG
end LQGMetric
