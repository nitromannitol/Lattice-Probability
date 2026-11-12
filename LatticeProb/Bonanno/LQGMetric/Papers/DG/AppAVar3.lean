/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.AppAVar3 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppAVar2

/-!
# Ding–Gwynne Lemma A.2 at `t = 0`: the field `f = ĥ − ĥ^tr` (task P2-DG3B)

DG (`metric-comparison-final.tex`, DG:2150–2155, used verbatim for Lemma A.2, DG:2240): "`Var f_t(z)`
converges as `t → 0` … the function `f(z) := lim_{t→0} f_t(z)` is a.s. defined … and is Gaussian".
In kernel form, with `f_t(z) = (ĥ_t − ĥ^tr_t)(z) = √π W(k_t(z) − k^tr_t(z))`:

* `hatDiffKernel0 z` — the `L²` kernel `1_{(0,1]}(s) (p(s/2; z, w) − p_{B_{1/10}(z)}(s/2; z, w))`
  of `f(z) = (ĥ − ĥ^tr)(z)`;
* `norm_sq_kernel_sub_kernel0_le` — `‖(k_t(z) − k^tr_t(z)) − k_0(z)‖² ≤ dgM · t⁶`, hence
  `tendsto_kernel_kernel0` (the `L²` convergence `f_t(z) → f(z)` as `t → 0⁺`);
* `dg_A2_var0` — `π ‖k_0(z₁) − k_0(z₂)‖² ≤ C |z₁ − z₂|`, i.e. (A.3) for `f = ĥ − ĥ^tr`;
* `norm_sq_kernel0_le` — `π ‖k_0(z)‖² ≤ π dgM` (bounded variance).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ

/-- `1_I(s) · kerDiff z s w`. -/
def kerI (I : Set ℝ) (z : ℂ) : ℝ × ℂ → ℝ := fun p => I.indicator (fun s => kerDiff z s p.2) p.1

lemma measurable_kerDiff_uncurry (z : ℂ) : Measurable fun p : ℝ × ℂ => kerDiff z p.1 p.2 :=
  (measurable_heatKernel_half z).sub ((measurable_killedHeat Metric.isOpen_ball).comp
    ((measurable_fst.div_const 2).real_toNNReal.prodMk (measurable_const.prodMk measurable_snd)))

lemma measurable_kerI {I : Set ℝ} (hI : MeasurableSet I) (z : ℂ) : Measurable (kerI I z) := by
  have e : kerI I z = (Prod.fst ⁻¹' I).indicator (fun p : ℝ × ℂ => kerDiff z p.1 p.2) := by
    funext p
    by_cases h : p.1 ∈ I <;> simp [kerI, h]
  rw [e]
  exact (measurable_kerDiff_uncurry z).indicator (measurable_fst hI)

/-- Per slice: `‖kerDiff z s ·‖₂² ≤ 4374/(π (1/10)⁶) (s/2)²`. -/
lemma lintegral_kerDiff_sq_le {s : ℝ} (hs : 0 < s) (z : ℂ) :
    ∫⁻ w, ENNReal.ofReal (kerDiff z s w ^ 2) ≤
      ENNReal.ofReal (4374 / (Real.pi * (1 / 10 : ℝ) ^ 6) * (s / 2) ^ 2) := by
  have hτ : (s / 2).toNNReal ≠ 0 := by simpa using hs
  simp_rw [kerDiff_eq_compK hs]
  refine (lintegral_sq_compK_le Metric.isOpen_ball (by norm_num : (0 : ℝ) < 1 / 10) subset_rfl
    hτ).trans (ENNReal.ofReal_le_ofReal ?_)
  refine (eB_le_sq (by norm_num) (pos_of_ne hτ)).trans (le_of_eq ?_)
  rw [Real.coe_toNNReal _ (by positivity)]

/-- `∫ kerI_I(z)² ≤ c · vol(I)` when `(s/2)² ≤ m` on `I ⊆ (0, ∞)`. -/
lemma lintegral_kerI_sq_le {I : Set ℝ} (hI : MeasurableSet I) (hI0 : I ⊆ Ioi 0) {m : ℝ}
    (hm : ∀ s ∈ I, (s / 2) ^ 2 ≤ m) (z : ℂ) :
    ∫⁻ p, ENNReal.ofReal (kerI I z p ^ 2) ≤
      ENNReal.ofReal (4374 / (Real.pi * (1 / 10 : ℝ) ^ 6) * m) * volume I := by
  have hpi := Real.pi_pos
  rw [Measure.volume_eq_prod, lintegral_prod _
    ((measurable_kerI hI z).pow_const 2).ennreal_ofReal.aemeasurable, ← setLIntegral_const]
  calc ∫⁻ s, ∫⁻ w, ENNReal.ofReal (kerI I z (s, w) ^ 2)
      = ∫⁻ s in I, ∫⁻ w, ENNReal.ofReal (kerDiff z s w ^ 2) := by
        rw [← lintegral_indicator hI]
        refine lintegral_congr fun s => ?_
        by_cases hs : s ∈ I
        · simp [kerI, hs]
        · simp [kerI, hs]
    _ ≤ ∫⁻ _ in I, ENNReal.ofReal (4374 / (Real.pi * (1 / 10 : ℝ) ^ 6) * m) :=
        lintegral_mono_ae ((ae_restrict_iff' hI).2 (ae_of_all _ fun s hs =>
          (lintegral_kerDiff_sq_le (hI0 hs) z).trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left (hm s hs) (by positivity)))))

lemma memLp_kerI {I : Set ℝ} (hI : MeasurableSet I) (hI1 : I ⊆ Ioc 0 1) (z : ℂ) :
    MemLp (kerI I z) 2 volume := by
  rw [memLp_two_iff_integrable_sq (measurable_kerI hI z).aestronglyMeasurable]
  refine ⟨((measurable_kerI hI z).pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun p => sq_nonneg _)]
  refine lt_of_le_of_lt (lintegral_kerI_sq_le hI (hI1.trans Ioc_subset_Ioi_self)
    (m := 1) (fun s hs => by have := hI1 hs; nlinarith [this.1, this.2]) z) ?_
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ((measure_mono hI1).trans_lt measure_Ioc_lt_top)

/-- The kernel of `f(z) = (ĥ − ĥ^tr)(z)` (DG's `f = lim_{t→0} f_t`). -/
def hatDiffKernel0 (z : ℂ) : WNSpace := (memLp_kerI measurableSet_Ioc subset_rfl z).toLp _

lemma kerA_eq_kerI (t : ℝ) (z : ℂ) : kerA t z = kerI (Icc (t ^ 2) 1) z := by
  funext p; exact kerA_apply t z p.1 p.2

/-- `‖(k_t(z) − k^tr_t(z)) − k_0(z)‖² ≤ dgM t⁶` for `t ∈ (0, 1]`. -/
theorem norm_sq_kernel_sub_kernel0_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (z : ℂ) :
    ‖(phiKernelL2 t 1 z - hatTrKernel t z) - hatDiffKernel0 z‖ ^ 2 ≤ 4 * dgM * t ^ 6 := by
  have hpi := Real.pi_pos
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hae : (((phiKernelL2 t 1 z - hatTrKernel t z) - hatDiffKernel0 z : WNSpace) :
      ℝ × ℂ → ℝ) =ᵐ[volume] fun p => -kerI (Ioo 0 (t ^ 2)) z p := by
    filter_upwards [Lp.coeFn_sub (phiKernelL2 t 1 z - hatTrKernel t z) (hatDiffKernel0 z),
      coeFn_kernel_sub ht z, (memLp_kerI measurableSet_Ioc subset_rfl z).coeFn_toLp]
      with p h1 h2 h3
    rw [h1, Pi.sub_apply, h2, hatDiffKernel0, h3, kerA_eq_kerI]
    simp only [kerI]
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
  have hB := lintegral_kerI_sq_le measurableSet_Ioo (fun s hs => hs.1) hm z
  rw [Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul (by positivity)] at hB
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun p => sq_nonneg _)
    ((measurable_kerI measurableSet_Ioo z).pow_const 2).aestronglyMeasurable]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hB).trans ?_
  rw [ENNReal.toReal_ofReal (by positivity)]
  unfold dgM
  have e : 4374 / (Real.pi * (1 / 10 : ℝ) ^ 6) * (t ^ 4 / 4) * t ^ 2 =
      4 * (4374 / (Real.pi * (1 / 10) ^ 6) * (1 / 4)) * t ^ 6 / 4 := by ring
  rw [e]
  have : 0 ≤ 4 * (4374 / (Real.pi * (1 / 10 : ℝ) ^ 6) * (1 / 4)) * t ^ 6 := by positivity
  linarith

/-- **DG (A.3) for `f = ĥ − ĥ^tr`** (Lemma A.2): `Var(f(z₁) − f(z₂)) ≤ C |z₁ − z₂|`. -/
theorem dg_A2_var0 : ∃ C : ℝ, ∀ z₁ z₂ : ℂ,
    Real.pi * ‖hatDiffKernel0 z₁ - hatDiffKernel0 z₂‖ ^ 2 ≤ C * ‖z₁ - z₂‖ := by
  obtain ⟨C, hC⟩ := dg_A2_var
  refine ⟨C, fun z₁ z₂ => ?_⟩
  have hpi := Real.pi_pos
  have hM := dgM_nonneg
  set a := Real.sqrt (C * ‖z₁ - z₂‖ / Real.pi)
  set b := 2 * Real.sqrt (4 * dgM)
  have hbound : ∀ n : ℕ, ‖hatDiffKernel0 z₁ - hatDiffKernel0 z₂‖ ≤ a + b * (1 / (n + 1)) := by
    intro n
    set t : ℝ := 1 / (n + 1)
    have ht : 0 < t := by positivity
    have ht1 : t ≤ 1 := by
      simp only [t]; rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    set F₁ := phiKernelL2 t 1 z₁ - hatTrKernel t z₁
    set F₂ := phiKernelL2 t 1 z₂ - hatTrKernel t z₂
    have h12 : ‖F₁ - F₂‖ ≤ a := by
      rw [← Real.sqrt_sq (norm_nonneg _)]
      refine Real.sqrt_le_sqrt ?_
      rw [le_div_iff₀ hpi, mul_comm]
      exact hC t ⟨ht, ht1⟩ z₁ z₂
    have hk : ∀ z, ‖(phiKernelL2 t 1 z - hatTrKernel t z) - hatDiffKernel0 z‖ ≤
        Real.sqrt (4 * dgM) * t := by
      intro z
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1
        ((norm_sq_kernel_sub_kernel0_le ht ht1 z).trans ?_)
      have : t ^ 6 ≤ t ^ 2 := pow_le_pow_of_le_one ht.le ht1 (by norm_num)
      have h4 : 0 ≤ 4 * dgM := by positivity
      rw [mul_pow, Real.sq_sqrt h4]
      nlinarith
    have e : hatDiffKernel0 z₁ - hatDiffKernel0 z₂ =
        (F₁ - F₂) - (F₁ - hatDiffKernel0 z₁) + (F₂ - hatDiffKernel0 z₂) := by abel
    rw [e]
    calc ‖(F₁ - F₂) - (F₁ - hatDiffKernel0 z₁) + (F₂ - hatDiffKernel0 z₂)‖
        ≤ ‖F₁ - F₂‖ + ‖F₁ - hatDiffKernel0 z₁‖ + ‖F₂ - hatDiffKernel0 z₂‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ a + Real.sqrt (4 * dgM) * t + Real.sqrt (4 * dgM) * t :=
          add_le_add (add_le_add h12 (hk z₁)) (hk z₂)
      _ = a + b * t := by simp only [b]; ring
  have hlim : Tendsto (fun n : ℕ => a + b * (1 / ((n : ℝ) + 1))) atTop (𝓝 (a + b * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat)
  rw [mul_zero, add_zero] at hlim
  have hle := ge_of_tendsto' hlim hbound
  have hC0 : 0 ≤ C * ‖z₁ - z₂‖ := by
    have := hC 1 ⟨one_pos, le_rfl⟩ z₁ z₂
    exact le_trans (by positivity) this
  have hsq : ‖hatDiffKernel0 z₁ - hatDiffKernel0 z₂‖ ^ 2 ≤ C * ‖z₁ - z₂‖ / Real.pi := by
    calc ‖hatDiffKernel0 z₁ - hatDiffKernel0 z₂‖ ^ 2 ≤ a ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = C * ‖z₁ - z₂‖ / Real.pi := Real.sq_sqrt (div_nonneg hC0 hpi.le)
  rw [le_div_iff₀ hpi] at hsq
  linarith

end DG
end LQGMetric
