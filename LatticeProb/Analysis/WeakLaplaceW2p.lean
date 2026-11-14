import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Thickening

/-!
# `W^{2,p}` limits of smooth approximate solutions of the Laplace equation

Let `U` be an open subset of a finite-dimensional real inner product space with an additive Haar
measure `μ`, and let `1 ≤ p`. Assume the interior `L^p` Hessian bound: for every ball `B(a, r)` there
is a finite constant `C` with `‖D² w‖_{L^p(B(a, r/2))} ≤ C (‖Δ w‖_{L^p(B(a, r))} + ‖w‖_{L^∞(B(a, r))})`
for every `w` smooth on `B(a, r)`. Let `uε n` be smooth on `{x | closedBall x (ε n) ⊆ U}` with
`Δ (uε n) = sε n` there, where `ε n → 0`, `uε n → u` uniformly on compact subsets of `U` and
`sε n → s` in `L^p` on compact subsets of `U`. Then the Hessians `D² (uε n)` converge in `L^p` on
compact subsets of `U` to a function `G`, and `G` is the weak Hessian of `u` in `U`
(`weakHessian_of_hessianLp`).

The interior Hessian bound is a hypothesis here.
-/

open MeasureTheory Metric Filter Topology Set
open scoped InnerProductSpace ContDiff ENNReal
open Laplacian

namespace LatticeProb.PegdenSmart

/-- A compact subset `K` of an open set `U` has an open neighbourhood contained in
`{x | closedBall x (ε n) ⊆ U}` for all large `n`, when `ε n → 0`. -/
theorem exists_isOpen_eventually_subset {X : Type*} [PseudoMetricSpace X] {U K : Set X}
    {ε : ℕ → ℝ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (hε : Tendsto ε atTop (𝓝 0)) :
    ∃ V, IsOpen V ∧ K ⊆ V ∧ ∀ᶠ n in atTop, V ⊆ {x | closedBall x (ε n) ⊆ U} := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨thickening (δ / 2) K, isOpen_thickening, self_subset_thickening (half_pos hδ) K, ?_⟩
  filter_upwards [hε (Iio_mem_nhds (half_pos hδ))] with n hn x hx y hy
  obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.mp hx
  refine hδU (mem_cthickening_of_dist_le y z δ K hz ?_)
  have hy' : dist y x ≤ ε n := hy
  have hn' : ε n < δ / 2 := hn
  linarith [dist_triangle y x z]

/-- The compact sets `closedBall 0 j \ thickening (1 / (j + 1)) Uᶜ` lie in the open set `U`, and
every compact subset of `U` lies in one of them. -/
theorem exists_isCompact_cover_of_isOpen {F : Type*} [NormedAddCommGroup F] [ProperSpace F]
    {U : Set F} (hU : IsOpen U) :
    ∃ K : ℕ → Set F, (∀ j, IsCompact (K j)) ∧ (∀ j, K j ⊆ U) ∧
      ∀ C, IsCompact C → C ⊆ U → ∃ j, C ⊆ K j := by
  refine ⟨fun j => closedBall 0 j \ thickening (1 / ((j : ℝ) + 1)) Uᶜ,
    fun j => (isCompact_closedBall _ _).diff isOpen_thickening, fun j x hx => ?_,
    fun C hC hCU => ?_⟩
  · by_contra h
    exact hx.2 (self_subset_thickening (by positivity) _ h)
  · obtain ⟨δ, hδ, hδU⟩ := hC.exists_cthickening_subset_open hU hCU
    obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall 0
    obtain ⟨j₁, hj₁⟩ := exists_nat_one_div_lt hδ
    obtain ⟨j₂, hj₂⟩ := exists_nat_ge R
    refine ⟨max j₁ j₂, fun x hx => ⟨?_, fun hx' => ?_⟩⟩
    · refine closedBall_subset_closedBall (hj₂.trans ?_) (hR hx)
      exact_mod_cast le_max_right j₁ j₂
    · obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.mp hx'
      apply hz
      apply hδU
      refine mem_cthickening_of_dist_le z x δ C hx ?_
      have h1 : (1 : ℝ) / ((max j₁ j₂ : ℕ) + 1) ≤ 1 / ((j₁ : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity)
          (by exact_mod_cast Nat.add_le_add_right (le_max_left j₁ j₂) 1)
      rw [dist_comm]
      linarith

/-- A sequence which is Cauchy for the `L^p` seminorm, `1 ≤ p`, converges in `L^p` to a strongly
measurable function. -/
theorem exists_stronglyMeasurable_tendsto_eLpNorm_norm {α F : Type*} [MeasurableSpace α]
    {ν : Measure α} [NormedAddCommGroup F] [CompleteSpace F] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : ℕ → α → F} (hf : ∀ n, MemLp (f n) p ν)
    (hc : Tendsto (fun nm : ℕ × ℕ => eLpNorm (fun x => ‖f nm.1 x - f nm.2 x‖) p ν)
      (atTop ×ˢ atTop) (𝓝 0)) :
    ∃ g : α → F, StronglyMeasurable g ∧
      Tendsto (fun n => eLpNorm (fun x => ‖f n x - g x‖) p ν) atTop (𝓝 0) := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  have hL : CauchySeq fun n => (hf n).toLp (f n) := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0, ← prod_atTop_atTop_eq]
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hc
    rw [ENNReal.toReal_zero] at h
    refine h.congr fun nm => ?_
    simp only [Function.comp_apply, dist_edist, Lp.edist_toLp_toLp]
    congr 1
    exact eLpNorm_norm (f nm.1 - f nm.2)
      ((hf nm.1).aestronglyMeasurable.sub (hf nm.2).aestronglyMeasurable)
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hL
  have hg' : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 ((Lp.memLp g).toLp g)) := by
    rwa [Lp.toLp_coeFn]
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf _ (Lp.memLp g)] at hg'
  refine ⟨(Lp.aestronglyMeasurable g).mk g, (Lp.aestronglyMeasurable g).stronglyMeasurable_mk,
    hg'.congr fun n => ?_⟩
  rw [← eLpNorm_norm (f n - (g : α → F))
    ((hf n).aestronglyMeasurable.sub (Lp.aestronglyMeasurable g))]
  refine eLpNorm_congr_ae ?_
  filter_upwards [(Lp.aestronglyMeasurable g).ae_eq_mk] with x hx
  simp [hx]

/-- The `L^p` seminorm of the restriction of `‖f‖` to a measurable set is that of the restriction
of `f`. -/
theorem eLpNorm_indicator_norm_eq {α F : Type*} [MeasurableSpace α] {ν : Measure α}
    [NormedAddCommGroup F] {p : ℝ≥0∞} {s : Set α} (hs : MeasurableSet s) {f : α → F}
    (hf : AEStronglyMeasurable f ν) :
    eLpNorm (s.indicator fun x => ‖f x‖) p ν = eLpNorm (s.indicator f) p ν := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs, eLpNorm_indicator_eq_eLpNorm_restrict hs]
  exact eLpNorm_norm f hf.restrict

/-- A sequence converging uniformly on a set `B` is Cauchy in `L^∞` on `B`. -/
theorem tendsto_eLpNorm_top_sub_of_tendstoUniformlyOn {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {f : ℕ → X → ℝ} {g : X → ℝ} {B : Set X} (hB : MeasurableSet B)
    (hunif : TendstoUniformlyOn f g atTop B)
    (hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable (f n) (ν.restrict B)) :
    Tendsto (fun nm : ℕ × ℕ => eLpNorm (f nm.1 - f nm.2) ⊤ (ν.restrict B)) (atTop ×ˢ atTop)
      (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨η', -, hη'0, hη'⟩ := ENNReal.lt_iff_exists_real_btwn.mp hη
  have hη'pos : 0 < η' := ENNReal.ofReal_pos.mp hη'0
  filter_upwards [hunif.uniformCauchySeqOn _ (Metric.dist_mem_uniformity hη'pos),
    hmeas.prod_mk hmeas] with nm hnm hm
  refine (eLpNorm_le_of_ae_bound (C := η') (hm.1.sub hm.2) ((ae_restrict_iff' hB).mpr
    (Eventually.of_forall fun x hx => ?_))).trans ?_
  · rw [Pi.sub_apply, ← dist_eq_norm]
    exact (show dist (f nm.1 x) (f nm.2 x) < η' from hnm x hx).le
  · simpa using hη'.le

/-- The derivative of `y ↦ g y w` is `v ↦ g' v w`. -/
theorem fderiv_apply_const_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F →L[ℝ] ℝ} {x : E}
    (hg : DifferentiableAt ℝ g x) (v : E) (w : F) :
    fderiv ℝ (fun y => g y w) x v = fderiv ℝ g x v w := by
  rw [(hg.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv]
  simp

/-- On an open set where `f` and `g` are smooth, the second derivative of `f - g` is the difference
of the second derivatives. -/
theorem fderiv_fderiv_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → ℝ}
    {V : Set E} (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V) (hg : ContDiffOn ℝ ∞ g V) {x : E}
    (hx : x ∈ V) :
    fderiv ℝ (fderiv ℝ (f - g)) x = fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) x := by
  have hf1 := (hf.fderiv_of_isOpen hV (m := ∞) (by simp)).differentiableOn (by simp)
  have hg1 := (hg.fderiv_of_isOpen hV (m := ∞) (by simp)).differentiableOn (by simp)
  have h : fderiv ℝ (f - g) =ᶠ[𝓝 x] fderiv ℝ f - fderiv ℝ g := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact fderiv_sub ((hf.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hy))
      ((hg.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hy))
  rw [h.fderiv_eq]
  exact fderiv_sub (hf1.differentiableAt (hV.mem_nhds hx)) (hg1.differentiableAt (hV.mem_nhds hx))

/-- The first derivative vanishes outside the topological support. -/
theorem fderiv_eq_zero_of_notMem_tsupport {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : E → F} {x : E} (hx : x ∉ tsupport φ) :
    fderiv ℝ φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (tsupport_fderiv_subset ℝ h)

/-- The second derivative vanishes outside the topological support. -/
theorem fderiv_fderiv_eq_zero_of_notMem_tsupport {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : E → F} {x : E}
    (hx : x ∉ tsupport φ) : fderiv ℝ (fderiv ℝ φ) x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h =>
    hx (tsupport_fderiv_subset ℝ (tsupport_fderiv_subset ℝ h))

/-- A function continuous on a compact set `K` and vanishing outside `K` is integrable. -/
theorem integrable_of_continuousOn_of_eq_zero {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {g : X → ℝ} {K : Set X} (hK : IsCompact K) (hg : ContinuousOn g K)
    (h0 : ∀ x ∉ K, g x = 0) : Integrable g μ :=
  (hg.integrableOn_compact hK).integrable_of_forall_notMem_eq_zero h0

/-- Integration by parts twice: `∫ f ∂_v ∂_w φ = ∫ (∂_v ∂_w f) φ` for a smooth function `φ` with
compact support in an open set `V` on which `f` is smooth. -/
theorem integral_mul_fderiv_fderiv_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] {f φ : E → ℝ} {V : Set E} (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) (v w : E) :
    ∫ x, f x * fderiv ℝ (fderiv ℝ φ) x v w ∂μ = ∫ x, fderiv ℝ (fderiv ℝ f) x v w * φ x ∂μ := by
  have hK : IsCompact (tsupport φ) := hφc
  have hdφ : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  have hd2φ : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hdφ.fderiv_right (m := ∞) (by simp)).continuous
  have hdf : ContDiffOn ℝ ∞ (fderiv ℝ f) V := hf.fderiv_of_isOpen hV (by simp)
  have hf₂ : ContDiffOn ℝ ∞ (fun y => fderiv ℝ f y w) V := hdf.clm_apply contDiffOn_const
  have hψ : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y v) := hdφ.clm_apply contDiff_const
  have hφ0 : ∀ x ∉ tsupport φ, φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hdφ0 : ∀ x ∉ tsupport φ, fderiv ℝ φ x = 0 := fun x hx =>
    fderiv_eq_zero_of_notMem_tsupport hx
  have hd2φ0 : ∀ x ∉ tsupport φ, fderiv ℝ (fderiv ℝ φ) x = 0 := fun x hx =>
    fderiv_fderiv_eq_zero_of_notMem_tsupport hx
  have htψ : tsupport (fun y => fderiv ℝ φ y v) ⊆ tsupport φ :=
    closure_minimal (fun x hx => by_contra fun h => hx (by simp [hdφ0 x h])) (isClosed_tsupport φ)
  have hψd : ∀ x, fderiv ℝ (fun y => fderiv ℝ φ y v) x w = fderiv ℝ (fderiv ℝ φ) x v w :=
    fun x => by
      rw [fderiv_apply_const_apply ((hdφ.differentiable (by simp)) x)]
      exact hφ.contDiffAt.isSymmSndFDerivAt (by simp) w v
  have hf₂d : ∀ x ∈ V, fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fderiv ℝ f) x v w :=
    fun x hx =>
      fderiv_apply_const_apply ((hdf.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hx))
        v w
  have h1 : ∫ x, f x * fderiv ℝ (fun y => fderiv ℝ φ y v) x w ∂μ =
      -∫ x, fderiv ℝ f x w * fderiv ℝ φ x v ∂μ := by
    refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ ?_ ?_
    · exact integrable_of_continuousOn_of_eq_zero hK
        (((hdf.continuousOn.clm_apply continuousOn_const).mono hφV).mul hψ.continuous.continuousOn)
        fun x hx => by simp [hdφ0 x hx]
    · simp only [hψd]
      exact integrable_of_continuousOn_of_eq_zero hK
        ((hf.continuousOn.mono hφV).mul
          ((hd2φ.clm_apply continuous_const).clm_apply continuous_const).continuousOn)
        fun x hx => by simp [hd2φ0 x hx]
    · exact integrable_of_continuousOn_of_eq_zero hK
        ((hf.continuousOn.mono hφV).mul hψ.continuous.continuousOn) fun x hx => by simp [hdφ0 x hx]
    · exact fun x hx => (hf.differentiableOn (by simp)).differentiableAt
        (hV.mem_nhds (hφV (htψ hx)))
    · exact fun x _ => hψ.differentiable (by simp) x
  have h2 : ∫ x, fderiv ℝ f x w * fderiv ℝ φ x v ∂μ =
      -∫ x, fderiv ℝ (fun y => fderiv ℝ f y w) x v * φ x ∂μ := by
    refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (f := fun y => fderiv ℝ f y w)
      (g := φ) ?_ ?_ ?_ ?_ ?_
    · exact integrable_of_continuousOn_of_eq_zero hK
        ((((hf₂.continuousOn_fderiv_of_isOpen hV (by simp)).clm_apply continuousOn_const).mono
          hφV).mul hφ.continuous.continuousOn) fun x hx => by simp [hφ0 x hx]
    · exact integrable_of_continuousOn_of_eq_zero hK
        ((hf₂.continuousOn.mono hφV).mul (hdφ.continuous.clm_apply continuous_const).continuousOn)
        fun x hx => by simp [hdφ0 x hx]
    · exact integrable_of_continuousOn_of_eq_zero hK
        ((hf₂.continuousOn.mono hφV).mul hφ.continuous.continuousOn) fun x hx => by simp [hφ0 x hx]
    · exact fun x hx => (hf₂.differentiableOn (by simp)).differentiableAt (hV.mem_nhds (hφV hx))
    · exact fun x _ => hφ.differentiable (by simp) x
  calc ∫ x, f x * fderiv ℝ (fderiv ℝ φ) x v w ∂μ
      = ∫ x, f x * fderiv ℝ (fun y => fderiv ℝ φ y v) x w ∂μ := by simp only [hψd]
    _ = ∫ x, fderiv ℝ (fun y => fderiv ℝ f y w) x v * φ x ∂μ := by rw [h1, h2, neg_neg]
    _ = ∫ x, fderiv ℝ (fderiv ℝ f) x v w * φ x ∂μ := by
      congr 1
      ext x
      by_cases hx : x ∈ V
      · rw [hf₂d x hx]
      · simp [hφ0 x fun h => hx (hφV h)]

/-- If `f n → g` uniformly on a compact set `K` and `h` is continuous and vanishes outside `K`,
then `∫ f n * h → ∫ g * h`. -/
theorem tendsto_integral_mul_of_tendstoUniformlyOn {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {f : ℕ → X → ℝ} {g h : X → ℝ} {K : Set X} (hK : IsCompact K)
    (hunif : TendstoUniformlyOn f g atTop K) (hcont : ∀ᶠ n in atTop, ContinuousOn (f n) K)
    (hh : Continuous h) (hh0 : ∀ x ∉ K, h x = 0) :
    Tendsto (fun n => ∫ x, f n x * h x ∂μ) atTop (𝓝 (∫ x, g x * h x ∂μ)) := by
  have hg : ContinuousOn g K := hunif.continuousOn hcont.frequently
  refine tendsto_integral_filter_of_dominated_convergence (fun x => (|g x| + 1) * |h x|) ?_ ?_ ?_ ?_
  · filter_upwards [hcont] with n hn
    exact (integrable_of_continuousOn_of_eq_zero hK (hn.mul hh.continuousOn)
      fun x hx => by simp [hh0 x hx]).aestronglyMeasurable
  · filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif 1 one_pos] with n hn
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ K
    · have h1 : dist (g x) (f n x) < 1 := hn x hx
      rw [Real.dist_eq, abs_sub_comm] at h1
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have := abs_sub_abs_le_abs_sub (f n x) (g x)
      linarith
    · simp [hh0 x hx]
  · exact integrable_of_continuousOn_of_eq_zero hK
      ((hg.abs.add continuousOn_const).mul hh.abs.continuousOn) fun x hx => by simp [hh0 x hx]
  · refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ K
    · exact (hunif.tendsto_at hx).mul_const _
    · simp [hh0 x hx]

/-- If `H n → G` in `L^p` on the support of a continuous compactly supported `φ`, `1 ≤ p < ∞`, then
`∫ H n (v, w) φ → ∫ G (v, w) φ`. -/
theorem tendsto_integral_apply_mul_of_tendsto_eLpNorm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    {H : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ} {G : E → E →L[ℝ] E →L[ℝ] ℝ} {φ : E → ℝ}
    (hHm : ∀ n, Measurable (H n)) (hGm : Measurable G) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hHc : ∀ᶠ n in atTop, ContinuousOn (H n) (tsupport φ))
    (hc : Tendsto (fun n => eLpNorm ((tsupport φ).indicator fun x => ‖H n x - G x‖) p μ) atTop
      (𝓝 0)) (v w : E) :
    Tendsto (fun n => ∫ x, H n x v w * φ x ∂μ) atTop (𝓝 (∫ x, G x v w * φ x ∂μ)) := by
  have hK : IsCompact (tsupport φ) := hφc
  have hKm : MeasurableSet (tsupport φ) := (isClosed_tsupport φ).measurableSet
  have hφ0 : ∀ x ∉ tsupport φ, φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  obtain ⟨Mφ, hMφ⟩ := hφ.bounded_above_of_compact_support hφc
  have hMφ0 : 0 ≤ Mφ := (norm_nonneg _).trans (hMφ 0)
  have hevm : Measurable fun L : E →L[ℝ] E →L[ℝ] ℝ => L v w :=
    ((ContinuousLinearMap.apply ℝ ℝ w).comp
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v)).continuous.measurable
  refine tendsto_integral_of_L1' _ ?_ ?_
  · filter_upwards [hHc] with n hn
    exact integrable_of_continuousOn_of_eq_zero hK
      (((hn.clm_apply continuousOn_const).clm_apply continuousOn_const).mul hφ.continuousOn)
      fun x hx => by simp [hφ0 x hx]
  have hp1 : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp_top hp
  set c : ℝ≥0∞ := ‖(‖v‖ * ‖w‖ * Mφ : ℝ)‖ₑ * μ (tsupport φ) ^ (1 - 1 / p.toReal) with hc_def
  have hcfin : c ≠ ⊤ := ENNReal.mul_ne_top enorm_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by
      rw [sub_nonneg]
      exact (div_le_one (by linarith)).mpr hp1) hK.measure_lt_top.ne)
  have hlim : Tendsto (fun n => c * eLpNorm ((tsupport φ).indicator
      fun x => ‖H n x - G x‖) p μ) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hc (Or.inr hcfin)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) fun n => ?_
  have : ContinuousSub (E →L[ℝ] E →L[ℝ] ℝ) :=
    IsTopologicalAddGroup.to_continuousSub (G := E →L[ℝ] E →L[ℝ] ℝ)
  have hDm : Measurable fun x => ‖H n x - G x‖ := ((hHm n).sub hGm).norm
  have hmeasF : AEStronglyMeasurable ((fun x => H n x v w * φ x) - fun x => G x v w * φ x) μ :=
    (((hevm.comp (hHm n)).mul hφ.measurable).sub
      ((hevm.comp hGm).mul hφ.measurable)).aestronglyMeasurable
  have hHolder : eLpNorm ((tsupport φ).indicator fun x => ‖H n x - G x‖) 1 μ ≤
      eLpNorm ((tsupport φ).indicator fun x => ‖H n x - G x‖) p μ *
        μ (tsupport φ) ^ (1 - 1 / p.toReal) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hKm, eLpNorm_indicator_eq_eLpNorm_restrict hKm]
    simpa [Measure.restrict_apply_univ] using
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict (tsupport φ)) hp
        hDm.aestronglyMeasurable
  have hpt : ∀ x, ‖((fun x => H n x v w * φ x) - fun x => G x v w * φ x) x‖ ≤
      (‖v‖ * ‖w‖ * Mφ) * (tsupport φ).indicator (fun x => ‖H n x - G x‖) x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · rw [indicator_of_mem hx]
      simp only [Pi.sub_apply]
      rw [← sub_mul, norm_mul]
      have h1 : H n x v w - G x v w = (H n x - G x) v w := by simp
      rw [h1]
      calc ‖(H n x - G x) v w‖ * ‖φ x‖ ≤ (‖H n x - G x‖ * ‖v‖ * ‖w‖) * Mφ :=
            mul_le_mul (ContinuousLinearMap.le_opNorm₂ _ v w) (hMφ x) (norm_nonneg _)
              (by positivity)
        _ = _ := by ring
    · rw [indicator_of_notMem hx]
      simp [hφ0 x hx]
  calc eLpNorm ((fun x => H n x v w * φ x) - fun x => G x v w * φ x) 1 μ
      ≤ eLpNorm ((‖v‖ * ‖w‖ * Mφ) • (tsupport φ).indicator fun x => ‖H n x - G x‖) 1 μ :=
        eLpNorm_mono_real hmeasF hpt
    _ = ‖(‖v‖ * ‖w‖ * Mφ : ℝ)‖ₑ *
          eLpNorm ((tsupport φ).indicator fun x => ‖H n x - G x‖) 1 μ := eLpNorm_const_smul _ _ _ _
    _ ≤ ‖(‖v‖ * ‖w‖ * Mφ : ℝ)‖ₑ * (eLpNorm ((tsupport φ).indicator fun x => ‖H n x - G x‖) p μ *
          μ (tsupport φ) ^ (1 - 1 / p.toReal)) := by gcongr
    _ = c * eLpNorm ((tsupport φ).indicator fun x => ‖H n x - G x‖) p μ := by
        rw [hc_def]
        ring

/-- The interior Hessian bound on `B(a, r)`, with `closedBall a r ⊆ U`, makes the Hessians of the
approximations Cauchy in `L^p` on `B(a, r / 2)`. -/
theorem tendsto_eLpNorm_norm_hessian_sub_ball {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} {p : ℝ≥0∞} (hp : 1 ≤ p) {U : Set E} {u s : E → ℝ} {uε sε : ℕ → E → ℝ}
    {ε : ℕ → ℝ} (hU : IsOpen U) (hε : Tendsto ε atTop (𝓝 0))
    (hsmooth : ∀ n, ContDiffOn ℝ ∞ (uε n) {x | closedBall x (ε n) ⊆ U})
    (hΔ : ∀ n, ∀ x ∈ {x | closedBall x (ε n) ⊆ U}, Δ (uε n) x = sε n x)
    {a : E} {r : ℝ} (hr : 0 < r) (hrU : closedBall a r ⊆ U)
    (hunif : TendstoUniformlyOn uε u atTop (closedBall a r))
    (hsε : Tendsto (fun n => eLpNorm ((closedBall a r).indicator fun x => sε n x - s x) p μ)
      atTop (𝓝 0))
    {C0 : ℝ≥0∞} (hC0 : C0 ≠ ⊤)
    (hbd : ∀ w : E → ℝ, ContDiffOn ℝ ∞ w (ball a r) →
      eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ w) x‖) p (μ.restrict (ball a (r / 2))) ≤
        C0 * (eLpNorm (Δ w) p (μ.restrict (ball a r)) + eLpNorm w ⊤ (μ.restrict (ball a r)))) :
    Tendsto (fun nm : ℕ × ℕ => eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ (uε nm.1)) x -
      fderiv ℝ (fderiv ℝ (uε nm.2)) x‖) p (μ.restrict (ball a (r / 2)))) (atTop ×ˢ atTop)
      (𝓝 0) := by
  obtain ⟨V, hVo, hBV, hVev⟩ :=
    exists_isOpen_eventually_subset (isCompact_closedBall a r) hU hrU hε
  have hBV' : ball a r ⊆ V := ball_subset_closedBall.trans hBV
  have hd := tendsto_eLpNorm_top_sub_of_tendstoUniformlyOn (ν := μ) measurableSet_ball
    (hunif.mono ball_subset_closedBall) (hVev.mono fun n hn =>
      ((hsmooth n).continuousOn.mono (hBV'.trans hn)).aestronglyMeasurable measurableSet_ball)
  have hmain : ∀ᶠ nm : ℕ × ℕ in atTop ×ˢ atTop,
      eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ (uε nm.1)) x - fderiv ℝ (fderiv ℝ (uε nm.2)) x‖) p
        (μ.restrict (ball a (r / 2))) ≤
        C0 * (eLpNorm ((closedBall a r).indicator fun x => sε nm.1 x - s x) p μ +
          eLpNorm ((closedBall a r).indicator fun x => sε nm.2 x - s x) p μ +
          eLpNorm (uε nm.1 - uε nm.2) ⊤ (μ.restrict (ball a r))) := by
    filter_upwards [hVev.prod_mk hVev] with nm hnm
    obtain ⟨hn, hm⟩ := hnm
    have hwn : ContDiffOn ℝ ∞ (uε nm.1) V := (hsmooth _).mono hn
    have hwm : ContDiffOn ℝ ∞ (uε nm.2) V := (hsmooth _).mono hm
    have h1 := hbd (uε nm.1 - uε nm.2) ((hwn.sub hwm).mono hBV')
    have hL : eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ (uε nm.1 - uε nm.2)) x‖) p
        (μ.restrict (ball a (r / 2))) = eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ (uε nm.1)) x -
          fderiv ℝ (fderiv ℝ (uε nm.2)) x‖) p (μ.restrict (ball a (r / 2))) := by
      refine eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_ball).mpr
        (Eventually.of_forall fun x hx => ?_))
      dsimp only
      rw [fderiv_fderiv_sub hVo hwn hwm (hBV' (ball_subset_ball (half_le_self hr.le) hx))]
    have hΔw : eLpNorm (Δ (uε nm.1 - uε nm.2)) p (μ.restrict (ball a r)) ≤
        eLpNorm ((closedBall a r).indicator fun x => sε nm.1 x - s x) p μ +
          eLpNorm ((closedBall a r).indicator fun x => sε nm.2 x - s x) p μ := by
      have hcongr : eLpNorm (Δ (uε nm.1 - uε nm.2)) p (μ.restrict (ball a r)) =
          eLpNorm ((fun x => sε nm.1 x - s x) - fun x => sε nm.2 x - s x) p
            (μ.restrict (ball a r)) := by
        refine eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_ball).mpr
          (Eventually.of_forall fun x hx => ?_))
        have hxV : x ∈ V := hBV' hx
        have h2n : ContDiffAt ℝ 2 (uε nm.1) x :=
          (hwn.contDiffAt (hVo.mem_nhds hxV)).of_le (by simp)
        have h2m : ContDiffAt ℝ 2 (uε nm.2) x :=
          (hwm.contDiffAt (hVo.mem_nhds hxV)).of_le (by simp)
        rw [h2n.laplacian_sub h2m, hΔ nm.1 x (hn hxV), hΔ nm.2 x (hm hxV)]
        simp only [Pi.sub_apply]
        ring
      rw [hcongr]
      refine (eLpNorm_sub_le hp).trans (add_le_add ?_ ?_) <;>
      · rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]
        exact eLpNorm_mono_measure _ (Measure.restrict_mono ball_subset_closedBall le_rfl)
    rw [← hL]
    refine h1.trans ?_
    gcongr
  have hlim : Tendsto (fun nm : ℕ × ℕ =>
      C0 * (eLpNorm ((closedBall a r).indicator fun x => sε nm.1 x - s x) p μ +
        eLpNorm ((closedBall a r).indicator fun x => sε nm.2 x - s x) p μ +
        eLpNorm (uε nm.1 - uε nm.2) ⊤ (μ.restrict (ball a r)))) (atTop ×ˢ atTop) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul
      (((hsε.comp tendsto_fst).add (hsε.comp tendsto_snd)).add hd) (Or.inr hC0)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) hmain

/-- The interior Hessian bound makes the Hessians of the approximations Cauchy in `L^p` on every
compact subset of `U`. -/
theorem tendsto_eLpNorm_indicator_norm_hessian_sub {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hQ2 : ∀ (a : E) (r : ℝ), 0 < r → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ w : E → ℝ,
      ContDiffOn ℝ ∞ w (ball a r) →
      eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ w) x‖) p (μ.restrict (ball a (r / 2))) ≤
        C * (eLpNorm (Δ w) p (μ.restrict (ball a r)) + eLpNorm w ⊤ (μ.restrict (ball a r))))
    {U : Set E} {u s : E → ℝ} {uε sε : ℕ → E → ℝ} {ε : ℕ → ℝ} (hU : IsOpen U)
    (hε : Tendsto ε atTop (𝓝 0))
    (hsmooth : ∀ n, ContDiffOn ℝ ∞ (uε n) {x | closedBall x (ε n) ⊆ U})
    (hΔ : ∀ n, ∀ x ∈ {x | closedBall x (ε n) ⊆ U}, Δ (uε n) x = sε n x)
    (hunif : ∀ C : Set E, IsCompact C → C ⊆ U → TendstoUniformlyOn uε u atTop C)
    (hsε : ∀ C : Set E, IsCompact C → C ⊆ U →
      Tendsto (fun n => eLpNorm (C.indicator fun x => sε n x - s x) p μ) atTop (𝓝 0))
    {C : Set E} (hC : IsCompact C) (hCU : C ⊆ U) :
    Tendsto (fun nm : ℕ × ℕ => eLpNorm (C.indicator fun x => ‖fderiv ℝ (fderiv ℝ (uε nm.1)) x -
      fderiv ℝ (fderiv ℝ (uε nm.2)) x‖) p μ) (atTop ×ˢ atTop) (𝓝 0) := by
  have hr : ∀ x ∈ U, ∃ r, 0 < r ∧ closedBall x r ⊆ U := fun x hx => by
    obtain ⟨r, hr, h⟩ := Metric.isOpen_iff.mp hU x hx
    exact ⟨r / 2, half_pos hr, (closedBall_subset_ball (half_lt_self hr)).trans h⟩
  choose! r hr0 hrU using hr
  obtain ⟨t, htC, hCt⟩ := hC.elim_nhds_subcover (fun x => ball x (r x / 2))
    fun x hx => ball_mem_nhds x (half_pos (hr0 x (hCU hx)))
  have hsum := tendsto_finsetSum t fun x hx => by
    obtain ⟨C0, hC0, hbd⟩ := hQ2 x (r x) (hr0 x (hCU (htC x hx)))
    exact tendsto_eLpNorm_norm_hessian_sub_ball hp hU hε hsmooth hΔ (hr0 x (hCU (htC x hx)))
      (hrU x (hCU (htC x hx))) (hunif _ (isCompact_closedBall _ _) (hrU x (hCU (htC x hx))))
      (hsε _ (isCompact_closedBall _ _) (hrU x (hCU (htC x hx)))) hC0 hbd
  rw [Finset.sum_const_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) fun nm => ?_
  set D : E → ℝ := fun y => ‖fderiv ℝ (fderiv ℝ (uε nm.1)) y - fderiv ℝ (fderiv ℝ (uε nm.2)) y‖
    with hD
  have hD0 : ∀ y, 0 ≤ D y := fun y => by
    simp only [hD]
    positivity
  have : ContinuousSub (E →L[ℝ] E →L[ℝ] ℝ) :=
    IsTopologicalAddGroup.to_continuousSub (G := E →L[ℝ] E →L[ℝ] ℝ)
  have hDm : Measurable D := by
    rw [hD]
    exact ((measurable_fderiv ℝ _).sub (measurable_fderiv ℝ _)).norm
  calc eLpNorm (C.indicator D) p μ
      ≤ eLpNorm (∑ x ∈ t, (ball x (r x / 2)).indicator D) p μ := by
        refine eLpNorm_mono_real (hDm.indicator hC.isClosed.measurableSet).aestronglyMeasurable
          fun y => ?_
        rw [Finset.sum_apply]
        by_cases hy : y ∈ C
        · obtain ⟨x, hxt, hyx⟩ : ∃ x ∈ t, y ∈ ball x (r x / 2) := by simpa using hCt hy
          rw [indicator_of_mem hy, Real.norm_eq_abs, abs_of_nonneg (hD0 y)]
          exact le_trans (le_of_eq (indicator_of_mem hyx D).symm) (Finset.single_le_sum
            (f := fun x => (ball x (r x / 2)).indicator D y)
            (fun x _ => indicator_nonneg (fun _ _ => hD0 _) _) hxt)
        · rw [indicator_of_notMem hy, norm_zero]
          exact Finset.sum_nonneg fun x _ => indicator_nonneg (fun _ _ => hD0 _) _
    _ ≤ ∑ x ∈ t, eLpNorm ((ball x (r x / 2)).indicator D) p μ := eLpNorm_sum_le hp
    _ = ∑ x ∈ t, eLpNorm D p (μ.restrict (ball x (r x / 2))) :=
        Finset.sum_congr rfl fun x _ => eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball

/-- On a compact subset `K` of `U`, Hessians which are Cauchy in `L^p` converge in `L^p`. -/
theorem exists_tendsto_eLpNorm_norm_hessian_sub {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {p : ℝ≥0∞} (hp : 1 ≤ p) {U : Set E}
    {uε : ℕ → E → ℝ} {ε : ℕ → ℝ} (hU : IsOpen U) (hε : Tendsto ε atTop (𝓝 0))
    (hsmooth : ∀ n, ContDiffOn ℝ ∞ (uε n) {x | closedBall x (ε n) ⊆ U})
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    (hc : Tendsto (fun nm : ℕ × ℕ => eLpNorm (K.indicator fun x =>
      ‖fderiv ℝ (fderiv ℝ (uε nm.1)) x - fderiv ℝ (fderiv ℝ (uε nm.2)) x‖) p μ)
      (atTop ×ˢ atTop) (𝓝 0)) :
    ∃ g : E → E →L[ℝ] E →L[ℝ] ℝ, StronglyMeasurable g ∧
      Tendsto (fun n => eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ (uε n)) x - g x‖) p
        (μ.restrict K)) atTop (𝓝 0) := by
  obtain ⟨V, hVo, hKV, hVev⟩ := exists_isOpen_eventually_subset hK hU hKU hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp hVev
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hmem : ∀ n, MemLp (fderiv ℝ (fderiv ℝ (uε (n + N)))) p (μ.restrict K) := by
    intro n
    have hcont : ContinuousOn (fderiv ℝ (fderiv ℝ (uε (n + N)))) K :=
      ((((hsmooth _).mono (hN _ (Nat.le_add_left N n))).fderiv_of_isOpen hVo (m := ∞)
        (by simp)).continuousOn_fderiv_of_isOpen hVo (by simp)).mono hKV
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ (fderiv ℝ (uε (n + N))))
      hcont
    exact MemLp.of_bound (measurable_fderiv ℝ _).aestronglyMeasurable M
      ((ae_restrict_iff' hKm).mpr (Eventually.of_forall hM))
  have hc' : Tendsto (fun nm : ℕ × ℕ => eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ (uε (nm.1 + N))) x -
      fderiv ℝ (fderiv ℝ (uε (nm.2 + N))) x‖) p (μ.restrict K)) (atTop ×ˢ atTop) (𝓝 0) := by
    refine (hc.comp ((tendsto_add_atTop_nat N).prodMap (tendsto_add_atTop_nat N))).congr
      fun nm => ?_
    exact eLpNorm_indicator_eq_eLpNorm_restrict hKm
  obtain ⟨g, hgm, hg⟩ := exists_stronglyMeasurable_tendsto_eLpNorm_norm
    (f := fun n => fderiv ℝ (fderiv ℝ (uε (n + N)))) hp (by exact hmem) (by exact hc')
  exact ⟨g, hgm, (tendsto_add_atTop_iff_nat
    (f := fun n => eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ (uε n)) x - g x‖) p (μ.restrict K))
    N).mp hg⟩

/-- Hessians which are Cauchy in `L^p` on every compact subset of `U` converge in `L^p` on every
compact subset of `U` to a single measurable function. -/
theorem exists_measurable_tendsto_eLpNorm_norm_hessian_sub {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {p : ℝ≥0∞} (hp : 1 ≤ p) {U : Set E}
    {uε : ℕ → E → ℝ} {ε : ℕ → ℝ} (hU : IsOpen U) (hε : Tendsto ε atTop (𝓝 0))
    (hsmooth : ∀ n, ContDiffOn ℝ ∞ (uε n) {x | closedBall x (ε n) ⊆ U})
    (hc : ∀ C : Set E, IsCompact C → C ⊆ U → Tendsto (fun nm : ℕ × ℕ => eLpNorm (C.indicator
      fun x => ‖fderiv ℝ (fderiv ℝ (uε nm.1)) x - fderiv ℝ (fderiv ℝ (uε nm.2)) x‖) p μ)
      (atTop ×ˢ atTop) (𝓝 0)) :
    ∃ G : E → E →L[ℝ] E →L[ℝ] ℝ, Measurable G ∧ ∀ C : Set E, IsCompact C → C ⊆ U →
      Tendsto (fun n => eLpNorm (C.indicator fun x => ‖fderiv ℝ (fderiv ℝ (uε n)) x - G x‖) p μ)
        atTop (𝓝 0) := by
  obtain ⟨K, hKc, hKU, hKcov⟩ := exists_isCompact_cover_of_isOpen hU
  have hKm : ∀ j, MeasurableSet (K j) := fun j => (hKc j).isClosed.measurableSet
  choose G hGm hGt using fun j =>
    exists_tendsto_eLpNorm_norm_hessian_sub hp hU hε hsmooth (hKc j) (hKU j) (hc _ (hKc j) (hKU j))
  have hcov : ∀ x, ∃ j, x ∈ K j ∪ Uᶜ := fun x => by
    by_cases hx : x ∈ U
    · obtain ⟨j, hj⟩ := hKcov {x} isCompact_singleton (singleton_subset_iff.mpr hx)
      exact ⟨j, Or.inl (hj rfl)⟩
    · exact ⟨0, Or.inr hx⟩
  obtain ⟨G0, hG0m, hG0⟩ : ∃ G0 : E → E →L[ℝ] E →L[ℝ] ℝ, Measurable G0 ∧
      ∀ x ∈ U, ∀ J, x ∈ K J → ∃ j ≤ J, x ∈ K j ∧ G0 x = G j x := by
    classical
    have hmeas := Measurable.find (p := fun j x => x ∈ K j ∪ Uᶜ)
      (fun j => (hGm j).measurable) (fun j => (hKm j).union hU.measurableSet.compl) hcov
    exact ⟨_, hmeas, fun x hx J hJ => ⟨Nat.find (hcov x), Nat.find_min' _ (Or.inl hJ),
      (Nat.find_spec (hcov x)).resolve_right fun h => h hx, rfl⟩⟩
  refine ⟨G0, hG0m, fun C hC hCU => ?_⟩
  obtain ⟨J, hJ⟩ := hKcov C hC hCU
  have hsum := tendsto_finsetSum (Finset.range (J + 1)) fun j _ => hGt j
  rw [Finset.sum_const_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) fun n => ?_
  set D : ℕ → E → ℝ := fun j x => ‖fderiv ℝ (fderiv ℝ (uε n)) x - G j x‖ with hD
  have hD0 : ∀ j x, 0 ≤ D j x := fun j x => by
    simp only [hD]
    positivity
  have hDj : ∀ j x, D j x = ‖fderiv ℝ (fderiv ℝ (uε n)) x - G j x‖ := fun j x => by rw [hD]
  have : ContinuousSub (E →L[ℝ] E →L[ℝ] ℝ) :=
    IsTopologicalAddGroup.to_continuousSub (G := E →L[ℝ] E →L[ℝ] ℝ)
  calc eLpNorm (C.indicator fun x => ‖fderiv ℝ (fderiv ℝ (uε n)) x - G0 x‖) p μ
      ≤ eLpNorm (∑ j ∈ Finset.range (J + 1), (K j).indicator (D j)) p μ := by
        refine eLpNorm_mono_real (((measurable_fderiv ℝ _).sub hG0m).norm.indicator
          hC.isClosed.measurableSet).aestronglyMeasurable fun x => ?_
        rw [Finset.sum_apply]
        by_cases hx : x ∈ C
        · obtain ⟨j, hjJ, hxj, hGj⟩ := hG0 x (hCU hx) J (hJ hx)
          have hnn : 0 ≤ ‖fderiv ℝ (fderiv ℝ (uε n)) x - G0 x‖ := by positivity
          rw [indicator_of_mem hx, Real.norm_of_nonneg hnn, hGj]
          exact le_trans (le_of_eq ((indicator_of_mem hxj (D j)).trans (hDj j x)).symm)
            (Finset.single_le_sum
            (f := fun j => (K j).indicator (D j) x)
            (fun j _ => indicator_nonneg (fun _ _ => hD0 _ _) _)
            (Finset.mem_range.mpr (Nat.lt_succ_of_le hjJ)))
        · rw [indicator_of_notMem hx, norm_zero]
          exact Finset.sum_nonneg fun j _ => indicator_nonneg (fun _ _ => hD0 _ _) _
    _ ≤ ∑ j ∈ Finset.range (J + 1), eLpNorm ((K j).indicator (D j)) p μ := eLpNorm_sum_le hp
    _ = ∑ j ∈ Finset.range (J + 1), eLpNorm (D j) p (μ.restrict (K j)) :=
        Finset.sum_congr rfl fun j _ => eLpNorm_indicator_eq_eLpNorm_restrict (hKm j)

/-- The `L^p` limit of the Hessians on compact subsets of `U` is the weak Hessian of the uniform
limit `u`. -/
theorem integral_mul_fderiv_fderiv_eq_of_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤) {U : Set E}
    {u : E → ℝ} {uε : ℕ → E → ℝ} {ε : ℕ → ℝ} (hU : IsOpen U) (hε : Tendsto ε atTop (𝓝 0))
    (hsmooth : ∀ n, ContDiffOn ℝ ∞ (uε n) {x | closedBall x (ε n) ⊆ U})
    (hunif : ∀ C : Set E, IsCompact C → C ⊆ U → TendstoUniformlyOn uε u atTop C)
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} (hGm : Measurable G)
    (hG : ∀ C : Set E, IsCompact C → C ⊆ U →
      Tendsto (fun n => eLpNorm (C.indicator fun x => ‖fderiv ℝ (fderiv ℝ (uε n)) x - G x‖) p μ)
        atTop (𝓝 0))
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (v w : E) :
    ∫ x, u x * fderiv ℝ (fderiv ℝ φ) x v w ∂μ = ∫ x, G x v w * φ x ∂μ := by
  have hK : IsCompact (tsupport φ) := hφc
  obtain ⟨V, hVo, hKV, hVev⟩ := exists_isOpen_eventually_subset hK hU hφU hε
  have hgc : Continuous fun x => fderiv ℝ (fderiv ℝ φ) x v w :=
    ((((hφ.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).continuous.clm_apply
      continuous_const).clm_apply continuous_const)
  have hL := tendsto_integral_mul_of_tendstoUniformlyOn (μ := μ) hK (hunif _ hK hφU)
    (hVev.mono fun n hn => (hsmooth n).continuousOn.mono (hKV.trans hn)) hgc
    fun x hx => by rw [fderiv_fderiv_eq_zero_of_notMem_tsupport hx]; rfl
  have hR := tendsto_integral_apply_mul_of_tendsto_eLpNorm (μ := μ) hp hp_top
    (fun n => measurable_fderiv ℝ (fderiv ℝ (uε n))) hGm hφ.continuous hφc
    (hVev.mono fun n hn => ((((hsmooth n).mono hn).fderiv_of_isOpen hVo (m := ∞)
      (by simp)).continuousOn_fderiv_of_isOpen hVo (by simp)).mono hKV) (hG _ hK hφU) v w
  have hid : ∀ᶠ n in atTop, ∫ x, uε n x * fderiv ℝ (fderiv ℝ φ) x v w ∂μ =
      ∫ x, fderiv ℝ (fderiv ℝ (uε n)) x v w * φ x ∂μ := by
    filter_upwards [hVev] with n hn
    exact integral_mul_fderiv_fderiv_eq hVo ((hsmooth n).mono hn) hφ hφc hKV v w
  exact tendsto_nhds_unique hL (hR.congr' (hid.mono fun n hn => hn.symm))

/-- **`W^{2,p}` limit and weak Hessian of smooth approximate solutions of `Δ u = s`**, given the
interior `L^p` Hessian bound for the exponent `p` as a hypothesis. If `uε n` is smooth on
`{x | closedBall x (ε n) ⊆ U}` with `Δ (uε n) = sε n` there, `ε n → 0`, `uε n → u` uniformly on
compact subsets of `U` and `sε n → s` in `L^p` on compact subsets of `U`, then the Hessians
`D² (uε n)` converge in `L^p` on compact subsets of `U` to some `G`, and
`∫ u ∂_v ∂_w φ = ∫ G(v, w) φ` for every smooth `φ` with compact support in `U`. -/
theorem weakHessian_of_hessianLp {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (hQ2 : ∀ (a : E) (r : ℝ), 0 < r → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ w : E → ℝ,
      ContDiffOn ℝ ∞ w (ball a r) →
      eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ w) x‖) p (μ.restrict (ball a (r / 2))) ≤
        C * (eLpNorm (Δ w) p (μ.restrict (ball a r)) + eLpNorm w ⊤ (μ.restrict (ball a r))))
    (U : Set E) (u s : E → ℝ) (uε sε : ℕ → E → ℝ) (ε : ℕ → ℝ)
    (hU : IsOpen U) (_hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hsmooth : ∀ n, ContDiffOn ℝ ∞ (uε n) {x | closedBall x (ε n) ⊆ U})
    (hΔ : ∀ n, ∀ x ∈ {x | closedBall x (ε n) ⊆ U}, Δ (uε n) x = sε n x)
    (hunif : ∀ C : Set E, IsCompact C → C ⊆ U → TendstoUniformlyOn uε u atTop C)
    (hsε : ∀ C : Set E, IsCompact C → C ⊆ U →
      Tendsto (fun n => eLpNorm (C.indicator fun x => sε n x - s x) p μ) atTop (𝓝 0)) :
    ∃ G : E → (E →L[ℝ] E →L[ℝ] ℝ),
      (∀ C : Set E, IsCompact C → C ⊆ U →
        Tendsto (fun n => eLpNorm (C.indicator fun x => fderiv ℝ (fderiv ℝ (uε n)) x - G x) p μ)
          atTop (𝓝 0)) ∧
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ v w : E,
        ∫ x, u x * fderiv ℝ (fderiv ℝ φ) x v w ∂μ = ∫ x, G x v w * φ x ∂μ) := by
  obtain ⟨G, hGm, hG⟩ := exists_measurable_tendsto_eLpNorm_norm_hessian_sub hp hU hε hsmooth
    fun C hC hCU =>
      tendsto_eLpNorm_indicator_norm_hessian_sub hp hQ2 hU hε hsmooth hΔ hunif hsε hC hCU
  have : ContinuousSub (E →L[ℝ] E →L[ℝ] ℝ) :=
    IsTopologicalAddGroup.to_continuousSub (G := E →L[ℝ] E →L[ℝ] ℝ)
  refine ⟨G, fun C hC hCU => (hG C hC hCU).congr fun n => by
    exact eLpNorm_indicator_norm_eq (f := fun x => fderiv ℝ (fderiv ℝ (uε n)) x - G x)
      hC.isClosed.measurableSet
      ((measurable_fderiv ℝ (fderiv ℝ (uε n))).sub hGm).aestronglyMeasurable,
    fun φ hφ hφc hφU v w =>
      integral_mul_fderiv_fderiv_eq_of_tendsto hp hp_top hU hε hsmooth hunif hGm hG hφ hφc hφU v w⟩

end LatticeProb.PegdenSmart
