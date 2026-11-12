/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127E3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127E2
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# D127 N3, step 2: smooth approximation of a bounded density in the killed-Green seminorm

`exists_smooth_approx`: for a bounded open `U` and a measurable `0 ≤ ρ ≤ C` vanishing off `U`,
for every `η > 0` there is `ρ' ∈ C_c^∞(U)` with `0 ≤ ρ' ≤ C` and `√B(ρ − ρ', ρ − ρ') ≤ η`.

Route (D127 addendum, DECISIONS.md 2026-10-02 22:15): cut `ρ` off to a compact `K ⊆ U`
(`exists_compact_cut`, S3D127E2), then mollify `ρ 1_K` with normed bumps `φ_r` of radius
`r < dist(K, Uᶜ)`; `φ_r ⋆ g → g` a.e. by Lebesgue differentiation
(`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`), and `B(g − φ_r ⋆ g) → 0` by
`tendsto_killedGreenForm_zero`. Standard mollification; own elementary bookkeeping.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped Real ContDiff Convolution

namespace LQGMetric.CONF.ZBM

open KilledHeat

variable {U : Set ℂ} {c : ℂ} {R : ℝ}

/-- `φ ⋆ g` at a point -/
lemma moll_apply (φ : ContDiffBump (0 : ℂ)) (g : ℂ → ℝ) (x : ℂ) :
    (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x =
      ∫ t, φ.normed volume t * g (x - t) := by
  simp [convolution_def, smul_eq_mul]

lemma moll_bounds (φ : ContDiffBump (0 : ℂ)) {g : ℂ → ℝ} {C : ℝ} (hg0 : ∀ z, 0 ≤ g z)
    (hgC : ∀ z, g z ≤ C) (x : ℂ) :
    0 ≤ (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x ∧
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x ≤ C := by
  rw [moll_apply]
  refine ⟨integral_nonneg fun t => mul_nonneg (φ.nonneg_normed t) (hg0 _), ?_⟩
  have h := norm_integral_le_of_norm_le (φ.integrable_normed (μ := volume).mul_const C)
    (Eventually.of_forall fun t => ?_) (f := fun t => φ.normed volume t * g (x - t))
  · rw [integral_mul_const, φ.integral_normed, one_mul] at h
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (φ.nonneg_normed t), abs_of_nonneg (hg0 _)]
    exact mul_le_mul_of_nonneg_left (hgC _) (φ.nonneg_normed t)

lemma moll_eq_zero (φ : ContDiffBump (0 : ℂ)) {g : ℂ → ℝ} {K : Set ℂ}
    (hgK : ∀ z, z ∉ K → g z = 0) {x : ℂ} (hx : x ∉ thickening φ.rOut K) :
    (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x = 0 := by
  rw [moll_apply]
  refine (integral_congr_ae (Eventually.of_forall fun t => ?_)).trans (integral_zero ℂ ℝ)
  show φ.normed volume t * g (x - t) = 0
  by_cases ht : t ∈ ball (0 : ℂ) φ.rOut
  · have : x - t ∉ K := fun h => hx (mem_thickening_iff.2 ⟨x - t, h, by
      rw [dist_eq_norm, sub_sub_cancel]; simpa using ht⟩)
    rw [hgK _ this, mul_zero]
  · have : t ∉ Function.support (φ.normed volume) := by
      rw [φ.support_normed_eq]; exact ht
    rw [Function.notMem_support.1 this, zero_mul]

/-- **mollification step**: a bounded `0 ≤ g ≤ C` vanishing off a compact `K ⊆ U` is
approximated in `B` by smooth `0 ≤ ρ' ≤ C` with compact support in `U` -/
theorem exists_moll_approx (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    {K : Set ℂ} (hKc : IsCompact K) (hKU : K ⊆ U) {g : ℂ → ℝ} (hg : Measurable g) {C : ℝ}
    (hg0 : ∀ z, 0 ≤ g z) (hgC : ∀ z, g z ≤ C) (hgK : ∀ z, z ∉ K → g z = 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ ρ' : ℂ → ℝ, ContDiff ℝ ∞ ρ' ∧ HasCompactSupport ρ' ∧ tsupport ρ' ⊆ U ∧
      (∀ z, 0 ≤ ρ' z) ∧ (∀ z, ρ' z ≤ C) ∧
      killedGreenForm U (fun z => g z - ρ' z) (fun z => g z - ρ' z) < η := by
  obtain ⟨δ, hδ, hδU⟩ := hKc.exists_cthickening_subset_open hU hKU
  set r : ℕ → ℝ := fun n => δ * (1 / ((n : ℝ) + 1)) with hr
  have hr0 : ∀ n, 0 < r n := fun n => by positivity
  have hrδ : ∀ n, r n ≤ δ := fun n => by
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    simpa [hr] using mul_le_of_le_one_right hδ.le this
  set φ : ℕ → ContDiffBump (0 : ℂ) := fun n => ⟨r n / 2, r n, by linarith [hr0 n],
    by linarith [hr0 n]⟩ with hφ
  set m : ℕ → ℂ → ℝ := fun n => (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g
  have hC0 : 0 ≤ C := (hg0 0).trans (hgC 0)
  have hgi : Integrable g := integrable_of_bdd_of_vanish hUR hg (C := C)
    (fun z => by rw [abs_of_nonneg (hg0 z)]; exact hgC z) (fun z hz => hgK z fun h => hz (hKU h))
  have hms : ∀ n, ContDiff ℝ ∞ (m n) := fun n =>
    ((φ n).hasCompactSupport_normed).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ n).contDiff_normed
      hgi.locallyIntegrable
  have hts : ∀ n, tsupport (m n) ⊆ cthickening δ K := fun n => by
    refine closure_minimal (fun x hx => ?_) isClosed_cthickening
    by_contra h
    refine hx (moll_eq_zero (φ n) hgK fun h' => h ?_)
    exact cthickening_mono (hrδ n) K (thickening_subset_cthickening _ _ h')
  have hd := tendsto_killedGreenForm_zero hU hR hUR (d := fun n z => g z - m n z) (C := 2 * C)
    (fun n => hg.sub (hms n).continuous.measurable)
    (fun n z => by
      have := moll_bounds (φ n) hg0 hgC z
      rw [abs_le]; constructor <;> linarith [hg0 z, hgC z])
    (fun n z hz => by
      have h1 : z ∉ tsupport (m n) := fun h => hz (hδU (hts n h))
      rw [image_eq_zero_of_notMem_tsupport h1, hgK z fun h => hz (hKU h), sub_zero])
    (by
      have hT : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
        simpa [hφ, hr] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
      have := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
        (φ := φ) (K := 2) hT (Eventually.of_forall fun n => by
          show r n ≤ 2 * (r n / 2); linarith) hgi.locallyIntegrable
      filter_upwards [this] with z hz
      simpa using (tendsto_const_nhds (x := g z)).sub hz)
  obtain ⟨n, hn⟩ := (hd.eventually (gt_mem_nhds hη)).exists
  refine ⟨m n, hms n, (hKc.cthickening).of_isClosed_subset (isClosed_tsupport _) (hts n),
    (hts n).trans hδU, fun z => (moll_bounds (φ n) hg0 hgC z).1,
    fun z => (moll_bounds (φ n) hg0 hgC z).2, hn⟩

/-- **smooth approximation in `√B`** -/
theorem exists_smooth_approx (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    {ρ : ℂ → ℝ} (hρ : Measurable ρ) {C : ℝ} (hρ0 : ∀ z, 0 ≤ ρ z) (hρC : ∀ z, ρ z ≤ C)
    (hρU : ∀ z, z ∉ U → ρ z = 0) {η : ℝ} (hη : 0 < η) :
    ∃ ρ' : ℂ → ℝ, ContDiff ℝ ∞ ρ' ∧ HasCompactSupport ρ' ∧ tsupport ρ' ⊆ U ∧
      (∀ z, 0 ≤ ρ' z) ∧ (∀ z, ρ' z ≤ C) ∧
      √(killedGreenForm U (fun z => ρ z - ρ' z) (fun z => ρ z - ρ' z)) ≤ η := by
  classical
  have hC : ∀ z, |ρ z| ≤ C := fun z => by rw [abs_of_nonneg (hρ0 z)]; exact hρC z
  have hη2 : 0 < (η / 2) ^ 2 := by positivity
  obtain ⟨n, hn⟩ := exists_compact_cut hU hR hUR hρ hC hρU hη2
  set K := exhK U c R n
  have hKm : MeasurableSet K := (isCompact_exhK n).measurableSet
  set g := K.indicator ρ with hg
  have hg0 : ∀ z, 0 ≤ g z := fun z => by
    by_cases hz : z ∈ K <;> simp [hg, hz, hρ0 z]
  have hgC : ∀ z, g z ≤ C := fun z => by
    by_cases hz : z ∈ K
    · simp [hg, hz, hρC z]
    · simp only [hg, indicator_of_notMem hz]; exact (hρ0 z).trans (hρC z)
  obtain ⟨ρ', h1, h2, h3, h4, h5, h6⟩ := exists_moll_approx hU hR hUR (isCompact_exhK n)
    (exhK_subset n) (hρ.indicator hKm) hg0 hgC (fun z hz => indicator_of_notMem hz _) hη2
  refine ⟨ρ', h1, h2, h3, h4, h5, ?_⟩
  have hC0 : 0 ≤ C := (hρ0 0).trans (hρC 0)
  have hm1 : Measurable (fun z => ρ z - g z) := hρ.sub (hρ.indicator hKm)
  have hm2 : Measurable (fun z => g z - ρ' z) := (hρ.indicator hKm).sub h1.continuous.measurable
  have hb1 : ∀ z, |ρ z - g z| ≤ 2 * C := fun z => by
    rw [abs_le]; constructor <;> linarith [hg0 z, hgC z, hρ0 z, hρC z]
  have hb2 : ∀ z, |g z - ρ' z| ≤ 2 * C := fun z => by
    rw [abs_le]; constructor <;> linarith [hg0 z, hgC z, h4 z, h5 z]
  have hv1 : ∀ z, z ∉ U → ρ z - g z = 0 := fun z hz => by
    have : z ∉ K := fun h => hz (exhK_subset n h)
    simp [hg, this, hρU z hz]
  have hv2 : ∀ z, z ∉ U → g z - ρ' z = 0 := fun z hz => by
    have : z ∉ K := fun h => hz (exhK_subset n h)
    rw [image_eq_zero_of_notMem_tsupport fun h => hz (h3 h)]
    simp [hg, this]
  have htri := sqrt_killedGreenForm_add_le hU hR hUR hm1 hm2 hb1 hb2
    (integrable_of_bdd_of_vanish hUR hm1 hb1 hv1) (integrable_of_bdd_of_vanish hUR hm2 hb2 hv2)
  have e : (fun z => (ρ z - g z) + (g z - ρ' z)) = fun z => ρ z - ρ' z :=
    funext fun z => by ring
  rw [e] at htri
  have s1 : √(killedGreenForm U (fun z => ρ z - g z) (fun z => ρ z - g z)) ≤ η / 2 := by
    rw [Real.sqrt_le_left (by positivity)]; exact hn.le
  have s2 : √(killedGreenForm U (fun z => g z - ρ' z) (fun z => g z - ρ' z)) ≤ η / 2 := by
    rw [Real.sqrt_le_left (by positivity)]; exact h6.le
  linarith

end LQGMetric.CONF.ZBM
