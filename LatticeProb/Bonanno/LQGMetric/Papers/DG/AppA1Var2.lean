/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.AppA1Var2 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppA1Var
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppAVar3

/-!
# Ding–Gwynne Lemma A.1 at `t = 0` (task P2-DG3B)

DG (`metric-comparison-final.tex`, DG:2150–2160): `f(z) := lim_{t→0} f_t(z)` for
`f_t = h^U_{t,1} − ĥ^tr_t`, with `Var(f(z₁) − f(z₂)) ≲ |z₁ − z₂|` on `K`. Kernel form, as
`AppAVar3` for Lemma A.2:

* `kernelU0 U z` — the `L²` kernel `1_{(0,1]}(s) q_s(z, w)` of `f(z)`;
* `tendsto_kernelU_kernelU0` — `L²` convergence of the kernels of `f_t(z)` as `t → 0⁺`;
* `dg_A1_var0` — `π ‖k(z₁) − k(z₂)‖² ≤ C |z₁ − z₂|` for `z₁, z₂ ∈ K`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ

/-- `1_I(s) · kerU U z s w`. -/
def kerIU (U : Set ℂ) (I : Set ℝ) (z : ℂ) : ℝ × ℂ → ℝ :=
  fun p => I.indicator (fun s => kerU U z s p.2) p.1

lemma measurable_kerU_uncurry {U : Set ℂ} (hU : IsOpen U) (z : ℂ) :
    Measurable fun p : ℝ × ℂ => kerU U z p.1 p.2 :=
  ((measurable_killedHeat hU).comp
    ((measurable_fst.div_const 2).real_toNNReal.prodMk (measurable_const.prodMk measurable_snd))).sub
    ((measurable_killedHeat Metric.isOpen_ball).comp
    ((measurable_fst.div_const 2).real_toNNReal.prodMk (measurable_const.prodMk measurable_snd)))

lemma measurable_kerIU {U : Set ℂ} (hU : IsOpen U) {I : Set ℝ} (hI : MeasurableSet I) (z : ℂ) :
    Measurable (kerIU U I z) := by
  have e : kerIU U I z = (Prod.fst ⁻¹' I).indicator (fun p : ℝ × ℂ => kerU U z p.1 p.2) := by
    funext p
    by_cases h : p.1 ∈ I <;> simp [kerIU, h]
  rw [e]
  exact (measurable_kerU_uncurry hU z).indicator (measurable_fst hI)

/-- Per slice: `‖kerDiff z s ·‖₂² ≤ 4374/(π (1/10)⁶) (s/2)²`. -/
lemma lintegral_kerU_sq_le {U : Set ℂ} {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : Metric.ball z (1 / 10) ⊆ U) :
    ∫⁻ w, ENNReal.ofReal (kerU U z s w ^ 2) ≤
      ENNReal.ofReal (4374 / (Real.pi * (1 / 10 : ℝ) ^ 6) * (s / 2) ^ 2) := by
  have hτ : (s / 2).toNNReal ≠ 0 := by simpa using hs
  refine (lintegral_sq_compK2_le Metric.isOpen_ball hz (by norm_num : (0 : ℝ) < 1 / 10)
    subset_rfl hτ).trans (ENNReal.ofReal_le_ofReal ?_)
  refine (eB_le_sq (by norm_num) (pos_of_ne hτ)).trans (le_of_eq ?_)
  rw [Real.coe_toNNReal _ (by positivity)]

/-- `∫ kerI_I(z)² ≤ c · vol(I)` when `(s/2)² ≤ m` on `I ⊆ (0, ∞)`. -/
lemma lintegral_kerIU_sq_le {U : Set ℂ} (hU : IsOpen U) {I : Set ℝ} (hI : MeasurableSet I)
    (hI0 : I ⊆ Ioi 0) {m : ℝ} (hm : ∀ s ∈ I, (s / 2) ^ 2 ≤ m) {z : ℂ}
    (hz : Metric.ball z (1 / 10) ⊆ U) :
    ∫⁻ p, ENNReal.ofReal (kerIU U I z p ^ 2) ≤
      ENNReal.ofReal (4374 / (Real.pi * (1 / 10 : ℝ) ^ 6) * m) * volume I := by
  have hpi := Real.pi_pos
  rw [Measure.volume_eq_prod, lintegral_prod _
    ((measurable_kerIU hU hI z).pow_const 2).ennreal_ofReal.aemeasurable, ← setLIntegral_const]
  calc ∫⁻ s, ∫⁻ w, ENNReal.ofReal (kerIU U I z (s, w) ^ 2)
      = ∫⁻ s in I, ∫⁻ w, ENNReal.ofReal (kerU U z s w ^ 2) := by
        rw [← lintegral_indicator hI]
        refine lintegral_congr fun s => ?_
        by_cases hs : s ∈ I
        · simp [kerIU, hs]
        · simp [kerIU, hs]
    _ ≤ ∫⁻ _ in I, ENNReal.ofReal (4374 / (Real.pi * (1 / 10 : ℝ) ^ 6) * m) :=
        lintegral_mono_ae ((ae_restrict_iff' hI).2 (ae_of_all _ fun s hs =>
          (lintegral_kerU_sq_le (hI0 hs) hz).trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left (hm s hs) (by positivity)))))

lemma memLp_kerIU {U : Set ℂ} (hU : IsOpen U) {I : Set ℝ} (hI : MeasurableSet I)
    (hI1 : I ⊆ Ioc 0 1) {z : ℂ} (hz : Metric.ball z (1 / 10) ⊆ U) :
    MemLp (kerIU U I z) 2 volume := by
  rw [memLp_two_iff_integrable_sq (measurable_kerIU hU hI z).aestronglyMeasurable]
  refine ⟨((measurable_kerIU hU hI z).pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun p => sq_nonneg _)]
  refine lt_of_le_of_lt (lintegral_kerIU_sq_le hU hI (hI1.trans Ioc_subset_Ioi_self)
    (m := 1) (fun s hs => by have := hI1 hs; nlinarith [this.1, this.2]) hz) ?_
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ((measure_mono hI1).trans_lt measure_Ioc_lt_top)

open Classical in
/-- The kernel of A.1's `f(z) = lim_{t→0} f_t(z)` (junk `0` off `K`). -/
def kernelU0 (U : Set ℂ) (z : ℂ) : WNSpace :=
  if h : MemLp (kerIU U (Ioc 0 1) z) 2 volume then h.toLp _ else 0

lemma kernelU0_eq {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : Metric.ball z (1 / 10) ⊆ U) :
    kernelU0 U z = (memLp_kerIU hU measurableSet_Ioc subset_rfl hz).toLp _ := by
  rw [kernelU0, dite_eq_left_of_eq_true (eq_true (memLp_kerIU hU measurableSet_Ioc subset_rfl hz))]

lemma kerAU_eq_kerIU (U : Set ℂ) (t : ℝ) (z : ℂ) : kerAU U t z = kerIU U (Icc (t ^ 2) 1) z := by
  funext p; exact kerAU_apply U t z p.1 p.2

/-- `‖(k_t(z) − k^tr_t(z)) − k_0(z)‖² ≤ dgM t⁶` for `t ∈ (0, 1]`. -/
theorem norm_sq_kernelU_sub_kernelU0_le {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) {z : ℂ}
    (hz : Metric.ball z (1 / 10) ⊆ U) :
    ‖(wndKernelL2 U (Icc (t ^ 2) 1) z - hatTrKernel t z) - kernelU0 U z‖ ^ 2 ≤
      4 * dgM * t ^ 6 := by
  have hpi := Real.pi_pos
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hae : (((wndKernelL2 U (Icc (t ^ 2) 1) z - hatTrKernel t z) - kernelU0 U z : WNSpace) :
      ℝ × ℂ → ℝ) =ᵐ[volume] fun p => -kerIU U (Ioo 0 (t ^ 2)) z p := by
    rw [kernelU0_eq hU hz]
    filter_upwards [Lp.coeFn_sub (wndKernelL2 U (Icc (t ^ 2) 1) z - hatTrKernel t z)
      ((memLp_kerIU hU measurableSet_Ioc subset_rfl hz).toLp _),
      coeFn_kernelU_sub hU hR hUR ht z, (memLp_kerIU hU measurableSet_Ioc subset_rfl hz).coeFn_toLp]
      with p h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, kerAU_eq_kerIU]
    simp only [kerIU]
    by_cases hs1 : p.1 ∈ Icc (t ^ 2) 1
    · have : p.1 ∉ Ioo 0 (t ^ 2) := fun h => absurd hs1.1 (not_le.2 h.2)
      have h' : p.1 ∈ Ioc 0 1 := ⟨lt_of_lt_of_le (by positivity) hs1.1, hs1.2⟩
      simp [hs1, this, h']
    · by_cases hs2 : p.1 ∈ Ioo 0 (t ^ 2)
      · have h' : p.1 ∈ Ioc 0 1 := ⟨hs2.1, hs2.2.le.trans ht2⟩
        simp [hs1, hs2, h']
      · have h' : p.1 ∉ Ioc 0 1 := by
          rintro ⟨a, b⟩
          rcases lt_or_ge p.1 (t ^ 2) with h | h
          · exact hs2 ⟨a, h⟩
          · exact hs1 ⟨h, b⟩
        simp [hs1, hs2, h']
  rw [norm_sq_eq_of_ae hae]
  simp_rw [neg_sq]
  have hm : ∀ s ∈ Ioo 0 (t ^ 2), (s / 2) ^ 2 ≤ t ^ 4 / 4 := fun s hs => by
    have := hs.1; have := hs.2; nlinarith
  have hB := lintegral_kerIU_sq_le hU measurableSet_Ioo (fun s hs => hs.1) hm hz
  rw [Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul (by positivity)] at hB
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun p => sq_nonneg _)
    ((measurable_kerIU hU measurableSet_Ioo z).pow_const 2).aestronglyMeasurable]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hB).trans ?_
  rw [ENNReal.toReal_ofReal (by positivity)]
  unfold dgM
  have e : 4374 / (Real.pi * (1 / 10 : ℝ) ^ 6) * (t ^ 4 / 4) * t ^ 2 =
      4 * (4374 / (Real.pi * (1 / 10) ^ 6) * (1 / 4)) * t ^ 6 / 4 := by ring
  rw [e]
  have : 0 ≤ 4 * (4374 / (Real.pi * (1 / 10 : ℝ) ^ 6) * (1 / 4)) * t ^ 6 := by positivity
  linarith

/-- **DG (A.3) for Lemma A.1 at `t = 0`**: `Var(f(z₁) − f(z₂)) ≤ C |z₁ − z₂|` on `K`. -/
theorem dg_A1_var0 {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ C : ℝ, ∀ z₁ z₂ : ℂ, Metric.ball z₁ (1 / 10) ⊆ U → Metric.ball z₂ (1 / 10) ⊆ U →
      Real.pi * ‖kernelU0 U z₁ - kernelU0 U z₂‖ ^ 2 ≤ C * ‖z₁ - z₂‖ := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).1 hUb
  have hR' : U ⊆ Metric.ball 0 (max R 0) :=
    hR.trans (Metric.ball_subset_ball (le_max_left _ _))
  have hR0 : (0 : ℝ) ≤ max R 0 := le_max_right _ _
  obtain ⟨C, hC⟩ := dg_A1_var hU hUb
  refine ⟨C, fun z₁ z₂ hz₁ hz₂ => ?_⟩
  have hpi := Real.pi_pos
  have hM := dgM_nonneg
  set a := Real.sqrt (C * ‖z₁ - z₂‖ / Real.pi)
  set b := 2 * Real.sqrt (4 * dgM)
  have hbound : ∀ n : ℕ, ‖kernelU0 U z₁ - kernelU0 U z₂‖ ≤ a + b * (1 / (n + 1)) := by
    intro n
    set t : ℝ := 1 / (n + 1)
    have ht : 0 < t := by positivity
    have ht1 : t ≤ 1 := by
      simp only [t]; rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    set F₁ := wndKernelL2 U (Icc (t ^ 2) 1) z₁ - hatTrKernel t z₁
    set F₂ := wndKernelL2 U (Icc (t ^ 2) 1) z₂ - hatTrKernel t z₂
    have h12 : ‖F₁ - F₂‖ ≤ a := by
      rw [← Real.sqrt_sq (norm_nonneg _)]
      refine Real.sqrt_le_sqrt ?_
      rw [le_div_iff₀ hpi, mul_comm]
      exact hC t ⟨ht, ht1⟩ z₁ z₂ hz₁ hz₂
    have hk : ∀ z, Metric.ball z (1 / 10) ⊆ U →
        ‖(wndKernelL2 U (Icc (t ^ 2) 1) z - hatTrKernel t z) - kernelU0 U z‖ ≤
        Real.sqrt (4 * dgM) * t := by
      intro z hz
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1
        ((norm_sq_kernelU_sub_kernelU0_le hU hR0 hR' ht ht1 hz).trans ?_)
      have : t ^ 6 ≤ t ^ 2 := pow_le_pow_of_le_one ht.le ht1 (by norm_num)
      have h4 : 0 ≤ 4 * dgM := by positivity
      rw [mul_pow, Real.sq_sqrt h4]
      nlinarith
    have e : kernelU0 U z₁ - kernelU0 U z₂ =
        (F₁ - F₂) - (F₁ - kernelU0 U z₁) + (F₂ - kernelU0 U z₂) := by abel
    rw [e]
    calc ‖(F₁ - F₂) - (F₁ - kernelU0 U z₁) + (F₂ - kernelU0 U z₂)‖
        ≤ ‖F₁ - F₂‖ + ‖F₁ - kernelU0 U z₁‖ + ‖F₂ - kernelU0 U z₂‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ a + Real.sqrt (4 * dgM) * t + Real.sqrt (4 * dgM) * t :=
          add_le_add (add_le_add h12 (hk z₁ hz₁)) (hk z₂ hz₂)
      _ = a + b * t := by simp only [b]; ring
  have hlim : Tendsto (fun n : ℕ => a + b * (1 / ((n : ℝ) + 1))) atTop (𝓝 (a + b * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat)
  rw [mul_zero, add_zero] at hlim
  have hle := ge_of_tendsto' hlim hbound
  have hC0 : 0 ≤ C * ‖z₁ - z₂‖ := by
    have := hC 1 ⟨one_pos, le_rfl⟩ z₁ z₂ hz₁ hz₂
    exact le_trans (by positivity) this
  have hsq : ‖kernelU0 U z₁ - kernelU0 U z₂‖ ^ 2 ≤ C * ‖z₁ - z₂‖ / Real.pi := by
    calc ‖kernelU0 U z₁ - kernelU0 U z₂‖ ^ 2 ≤ a ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = C * ‖z₁ - z₂‖ / Real.pi := Real.sq_sqrt (div_nonneg hC0 hpi.le)
  rw [le_div_iff₀ hpi] at hsq
  linarith

end DG
end LQGMetric
