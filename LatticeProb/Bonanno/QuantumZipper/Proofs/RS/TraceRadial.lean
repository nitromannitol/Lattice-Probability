/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.RS.TraceRadial at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.RS.TraceShift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# EXT-RS node TR3: the trace from the radial derivative bound

Blueprint `blueprint/EXT_RS_BLUEPRINT.md` §3, node **TR3** (as corrected by AUDIT7 R1).
Source: A. Kemppainen, *Schramm–Loewner Evolution* (SpringerBriefs 2017), the proof of Thm 5.2
(§6.2.3), (6.19), p. 112 (corrected from "Prop. 6.5", AUDIT10 P10-4); first paragraph of the proof
of Thm 6.4 (p. 109) for the continuity.

If `0 < δ`, `0 ≤ C` and `‖(f̂_t)'(iy)‖ ≤ C y^{δ−1}` on `[0,N] × (0,1]`, with `W` continuous and
`W 0 = 0`, then for every `t ∈ [0,N]`:

* the radial limit `lim_{y↓0} f̂_t(iy) = trace W t` exists;
* `‖f̂_t(iy) − trace W t‖ ≤ (C/δ) y^δ` for `y ∈ (0,1]`;
* `t ↦ trace W t` is continuous on `[0,N]`.

Proof, following Kemppainen (6.19), p. 112: `s ↦ f̂_t(is)` is differentiable on `(0,1]` with
derivative `(f̂_t)'(is) · i`, so for `0 < y₂ ≤ y₁ ≤ 1` the fencing/comparison lemma
`image_norm_le_of_norm_deriv_right_le_deriv_boundary'` with the comparison function
`B s = (C/δ)(s^δ − y₂^δ)`, `B' s = C s^{δ−1}` (the sharp integral `∫_{y₂}^{y₁} C s^{δ−1} ds`)
gives `‖f̂_t(iy₁) − f̂_t(iy₂)‖ ≤ (C/δ)(y₁^δ − y₂^δ)`; hence `y ↦ f̂_t(iy)` is Cauchy as `y ↓ 0`,
and the limit exists because `ℂ` is complete. Passing to the limit in the estimate gives both
the limit statement and the bound. Continuity in `t` is the first paragraph of the proof of
Kem Thm 6.4, p. 109: for fixed `y > 0`, `t ↦ f̂_t(iy)` is continuous, since
`f̂_t = revMap (W (t − ·) − W t) t` on `H` and the reverse flow is stable under small changes of
the driver (`ReverseFlow.norm_revMap_sub_revMap_le`) and continuous in time for a fixed driver
(`ReverseFlow.continuousOn_revMap_time`); the convergence `y ↓ 0` is uniform in `t ∈ [0,N]`
by the bound above, so the limit is continuous.

Notation: `f̂_t = fwdMapInv W t`, `f_t = fwdMap W t`, `trace W t = limUnder (𝓝[>] 0) (f̂_t(i·))`.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace QuantumZipper
namespace RS

open UnzipInvariance

variable {W : ℝ → ℝ} {N δ C : ℝ}

/-! ## The derivative of `s ↦ f̂_t(is)` -/

/-- `f̂_t = fwdMapInv W t` is complex differentiable at every point of `H` (for `0 ≤ t`), by
comparison with the reverse flow `revMap (W (t − ·) − W t) t` (`P3(e)` project lemma
`fwdMapInv_eq_revMap_timeRev`). -/
theorem differentiableAt_fwdMapInv (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {w : ℂ} (hw : w ∈ H) : DifferentiableAt ℂ (fwdMapInv W t) w :=
  ((differentiableOn_revMap (fun s => W (t - s) - W t) (by fun_prop) ht).differentiableAt
      (isOpen_H.mem_nhds hw)).congr_of_eventuallyEq
    (eventually_of_mem (isOpen_H.mem_nhds hw) fun z hz =>
      fwdMapInv_eq_revMap_timeRev W hW hW0 ht hz)

/-! ## The radial estimate (Kemppainen (6.19), p. 112) -/

/-- **TR3, radial step.** Integrating `‖(f̂_t)'(iy)‖ ≤ C y^{δ−1}` along the vertical ray: for
`0 < y₂ ≤ y₁ ≤ 1`, `‖f̂_t(iy₁) − f̂_t(iy₂)‖ ≤ (C/δ)(y₁^δ − y₂^δ)`. Fencing lemma with the
comparison function `B s = (C/δ)(s^δ − y₂^δ)` whose derivative is `C s^{δ−1}`. -/
theorem norm_fwdMapInv_mul_I_sub_le_rpow (hδ : 0 < δ) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {y₁ y₂ : ℝ} (hy₂ : 0 < y₂) (hy : y₂ ≤ y₁)
    (hy₁ : y₁ ≤ 1)
    (hbd : ∀ y ∈ Ioc (0 : ℝ) 1, ‖deriv (fwdMapInv W t) (y * I)‖ ≤ C * y ^ (δ - 1)) :
    ‖fwdMapInv W t (y₁ * I) - fwdMapInv W t (y₂ * I)‖ ≤ C / δ * (y₁ ^ δ - y₂ ^ δ) := by
  set f : ℂ → ℂ := fwdMapInv W t with hf
  set φ : ℝ → ℂ := fun x => f (x * I) - f (y₂ * I) with hφ
  set B : ℝ → ℝ := fun x => C / δ * (x ^ δ - y₂ ^ δ) with hB
  have hγ : ∀ s : ℝ, HasDerivAt (fun y : ℝ => (y : ℂ) * I) I s := fun s =>
    (hasDerivAt_mul_const (x := (s : ℂ)) (I : ℂ)).comp_ofReal
  have hderiv : ∀ x ∈ Icc y₂ y₁, HasDerivAt φ (deriv f (x * I) * I) x := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hy₂ hx.1
    have hd : DifferentiableAt ℂ f (x * I) :=
      differentiableAt_fwdMapInv hW hW0 ht (mul_I_mem_H hxpos)
    have h3 := (hd.hasDerivAt.comp x (hγ x)).sub_const (f (y₂ * I))
    simpa [hφ] using h3
  have hBd : ∀ x : ℝ, 0 < x → HasDerivAt B (C * x ^ (δ - 1)) x := by
    intro x hx
    have h1 : HasDerivAt (fun z : ℝ => z ^ δ) (1 * δ * x ^ (δ - 1)) x :=
      (hasDerivAt_id x).rpow_const (Or.inl hx.ne')
    have h2 : HasDerivAt (fun z : ℝ => C / δ * (z ^ δ - y₂ ^ δ))
        ((C / δ) * (1 * δ * x ^ (δ - 1))) x :=
      ((h1.sub_const (y₂ ^ δ)).const_mul (C / δ))
    have h3 : HasDerivAt B ((C / δ) * (1 * δ * x ^ (δ - 1))) x := by
      rw [hB]; exact h2
    refine h3.congr_deriv ?_
    field_simp
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary' (a := y₂) (b := y₁)
    (f := φ) (f' := fun x => deriv f (x * I) * I) (B := B) (B' := fun x => C * x ^ (δ - 1))
    (fun x hx => (hderiv x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hderiv x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt)
    (by rw [hφ, hB]; simp)
    (fun x hx => (hBd x (lt_of_lt_of_le hy₂ hx.1)).continuousAt.continuousWithinAt)
    (fun x hx => (hBd x (lt_of_lt_of_le hy₂ hx.1)).hasDerivWithinAt)
    (fun x hx => by
      have hxI : x ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_lt_of_le hy₂ hx.1, hx.2.le.trans hy₁⟩
      rw [norm_mul, Complex.norm_I, mul_one]
      exact hbd x hxI)
    ⟨hy, le_rfl⟩
  rw [hφ, hB] at key
  exact key

/-- Symmetrized radial estimate: `‖f̂_t(iy₁) − f̂_t(iy₂)‖ ≤ (C/δ)|y₁^δ − y₂^δ|` for
`y₁, y₂ ∈ (0,1]`. -/
theorem norm_fwdMapInv_mul_I_sub_le_abs (hδ : 0 < δ) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {y₁ y₂ : ℝ} (hy₁ : y₁ ∈ Ioc (0 : ℝ) 1)
    (hy₂ : y₂ ∈ Ioc (0 : ℝ) 1)
    (hbd : ∀ y ∈ Ioc (0 : ℝ) 1, ‖deriv (fwdMapInv W t) (y * I)‖ ≤ C * y ^ (δ - 1)) :
    ‖fwdMapInv W t (y₁ * I) - fwdMapInv W t (y₂ * I)‖ ≤ C / δ * |y₁ ^ δ - y₂ ^ δ| := by
  rcases le_total y₂ y₁ with h | h
  · have h1 := norm_fwdMapInv_mul_I_sub_le_rpow hδ hW hW0 ht hy₂.1 h hy₁.2 hbd
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hy₂.1.le h hδ.le))]
    exact h1
  · have h1 := norm_fwdMapInv_mul_I_sub_le_rpow hδ hW hW0 ht hy₁.1 h hy₂.2 hbd
    rw [norm_sub_rev,
      abs_of_nonpos (sub_nonpos.mpr (Real.rpow_le_rpow hy₁.1.le h hδ.le)), neg_sub]
    exact h1

/-! ## Smallness of `K y^δ` and the limit as `y ↓ 0` -/

theorem Ioc_mem_nhdsGT_zero {η : ℝ} (hη : 0 < η) : Ioc (0 : ℝ) η ∈ 𝓝[>] (0 : ℝ) :=
  (nhdsGT_basis_Ioc (0 : ℝ)).mem_iff.2 ⟨η, hη, Subset.rfl⟩

/-- For `δ > 0` and `ε > 0` there is `y ∈ (0,1]` with `K y^δ < ε`. -/
theorem exists_mul_rpow_lt {K ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ y ∈ Ioc (0 : ℝ) 1, K * y ^ δ < ε := by
  have h0 : Tendsto (fun y : ℝ => y ^ δ) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := (Real.continuousAt_rpow_const (0 : ℝ) δ (Or.inr hδ.le)).tendsto
    rwa [Real.zero_rpow hδ.ne'] at h
  have htend : Tendsto (fun y : ℝ => K * y ^ δ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h1 := h0.const_mul K
    rw [mul_zero] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), K * y ^ δ ∈ Iio ε := htend.eventually (Iio_mem_nhds hε)
  have hmem : Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioc_mem_nhdsGT_zero one_pos
  obtain ⟨y, hyε, hyIoc⟩ := (hev.and (Filter.eventually_of_mem hmem fun _ h => h)).exists
  exact ⟨y, hyIoc, hyε⟩

/-- **TR3, existence of the radial limit.** The Cauchy estimate above gives, in a complete
space, a limit of `y ↦ f̂_t(iy)` as `y ↓ 0`. -/
theorem exists_tendsto_fwdMapInv_mul_I (hδ : 0 < δ) (hC : 0 ≤ C) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (hbd : ∀ y ∈ Ioc (0 : ℝ) 1, ‖deriv (fwdMapInv W t) (y * I)‖ ≤ C * y ^ (δ - 1)) :
    ∃ L : ℂ, Tendsto (fun y : ℝ => fwdMapInv W t (y * I)) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  have hsymm : ∀ y₁ ∈ Ioc (0 : ℝ) 1, ∀ y₂ ∈ Ioc (0 : ℝ) 1,
      ‖fwdMapInv W t (y₁ * I) - fwdMapInv W t (y₂ * I)‖ ≤ C / δ * |y₁ ^ δ - y₂ ^ δ| :=
    fun y₁ hy₁ y₂ hy₂ => norm_fwdMapInv_mul_I_sub_le_abs hδ hW hW0 ht hy₁ hy₂ hbd
  refine cauchy_map_iff_exists_tendsto.mp ?_
  rw [cauchy_map_iff']
  rw [Filter.tendsto_def]
  intro s hs
  rw [Metric.mem_uniformity_dist] at hs
  obtain ⟨ε, hε, hεs⟩ := hs
  obtain ⟨η, hηIoc, hηlt⟩ := exists_mul_rpow_lt (K := C / δ) hδ hε
  have hsub : Ioc (0 : ℝ) η ⊆ Ioc (0 : ℝ) 1 := fun x hx => ⟨hx.1, hx.2.trans hηIoc.2⟩
  refine mem_of_superset
    (Filter.prod_mem_prod (Ioc_mem_nhdsGT_zero hηIoc.1) (Ioc_mem_nhdsGT_zero hηIoc.1)) ?_
  rintro ⟨y₁, y₂⟩ ⟨hy₁, hy₂⟩
  have hb : |y₁ ^ δ - y₂ ^ δ| ≤ η ^ δ := by
    rw [abs_sub_le_iff]
    refine ⟨?_, ?_⟩
    · have h1 : y₁ ^ δ ≤ η ^ δ := Real.rpow_le_rpow hy₁.1.le hy₁.2 hδ.le
      have h2 : 0 ≤ y₂ ^ δ := Real.rpow_nonneg hy₂.1.le δ
      linarith
    · have h1 : y₂ ^ δ ≤ η ^ δ := Real.rpow_le_rpow hy₂.1.le hy₂.2 hδ.le
      have h2 : 0 ≤ y₁ ^ δ := Real.rpow_nonneg hy₁.1.le δ
      linarith
  refine hεs (lt_of_le_of_lt ?_ hηlt)
  rw [dist_eq_norm]
  calc ‖fwdMapInv W t (y₁ * I) - fwdMapInv W t (y₂ * I)‖
      ≤ C / δ * |y₁ ^ δ - y₂ ^ δ| := hsymm y₁ (hsub hy₁) y₂ (hsub hy₂)
    _ ≤ C / δ * η ^ δ := mul_le_mul_of_nonneg_left hb (div_nonneg hC hδ.le)

/-- **TR3, bound at the limit.** Passing `y₂ ↓ 0` in the radial estimate gives
`‖f̂_t(iy) − trace W t‖ ≤ (C/δ) y^δ` for `y ∈ (0,1]`. -/
theorem norm_fwdMapInv_mul_I_sub_trace_le (hδ : 0 < δ) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) 1)
    (hbd : ∀ y ∈ Ioc (0 : ℝ) 1, ‖deriv (fwdMapInv W t) (y * I)‖ ≤ C * y ^ (δ - 1))
    (hlim : Tendsto (fun y : ℝ => fwdMapInv W t (y * I)) (𝓝[>] (0 : ℝ)) (𝓝 (trace W t))) :
    ‖fwdMapInv W t (y * I) - trace W t‖ ≤ C / δ * y ^ δ := by
  have h0 : Tendsto (fun y' : ℝ => y' ^ δ) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := (Real.continuousAt_rpow_const (0 : ℝ) δ (Or.inr hδ.le)).tendsto
    rwa [Real.zero_rpow hδ.ne'] at h
  have hleft : Tendsto (fun y' : ℝ => ‖fwdMapInv W t (y * I) - fwdMapInv W t (y' * I)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 ‖fwdMapInv W t (y * I) - trace W t‖) :=
    (tendsto_const_nhds.sub hlim).norm
  have hright : Tendsto (fun y' : ℝ => C / δ * (y ^ δ - y' ^ δ)) (𝓝[>] (0 : ℝ))
      (𝓝 (C / δ * y ^ δ)) := by
    have h2 : Tendsto (fun y' : ℝ => y ^ δ - y' ^ δ) (𝓝[>] (0 : ℝ)) (𝓝 (y ^ δ - 0)) :=
      tendsto_const_nhds.sub (h0.mono_left nhdsWithin_le_nhds)
    rw [sub_zero] at h2
    exact h2.const_mul (C / δ)
  refine le_of_tendsto_of_tendsto hleft hright ?_
  filter_upwards [Ioc_mem_nhdsGT_zero hy.1] with y' hy'
  exact norm_fwdMapInv_mul_I_sub_le_rpow hδ hW hW0 ht hy'.1 hy'.2 hy.2 hbd

/-! ## Continuity in time (Kemppainen, proof of Thm 6.4, p. 109) -/

/-- Driver stability of the inverse flow: if `W` moves by at most `ε` on pairs at distance
`≤ |t − t₀|` inside the window `[−1, N+1]`, then `f̂_t(iy)` differs from the reverse map driven
by the frozen time-reversed driver `W (t₀ − ·) − W t₀` by at most `2ε e^{2N/y²}`
(Grönwall: `ReverseFlow.norm_revMap_sub_revMap_le`). -/
theorem norm_fwdMapInv_sub_revMap_timeRev_le (hW : Continuous W) (hW0 : W 0 = 0)
    {t t₀ y ε : ℝ} (ht : t ∈ Icc 0 N) (ht₀ : t₀ ∈ Icc 0 N) (hy : 0 < y) (h1 : |t - t₀| ≤ 1)
    (hε : 0 ≤ ε)
    (hWε : ∀ a b : ℝ, a ∈ Icc (-1) (N + 1) → b ∈ Icc (-1) (N + 1) → |a - b| ≤ |t - t₀| →
      |W a - W b| ≤ ε) :
    ‖fwdMapInv W t (y * I) - revMap (fun r => W (t₀ - r) - W t₀) t (y * I)‖ ≤
      2 * ε * Real.exp (2 * N / y ^ 2) := by
  set Vt : ℝ → ℝ := fun r => W (t - r) - W t with hVt
  set V₀ : ℝ → ℝ := fun r => W (t₀ - r) - W t₀ with hV₀
  rw [fwdMapInv_eq_revMap_timeRev W hW hW0 ht.1 (mul_I_mem_H hy)]
  have hVtc : Continuous Vt := by rw [hVt]; fun_prop
  have hV₀c : Continuous V₀ := by rw [hV₀]; fun_prop
  have hmain := ReverseFlow.norm_revMap_sub_revMap_le Vt V₀ hVtc hV₀c (y * I) (by simpa using hy)
    (ε := 2 * ε) ht.1 ?_
  · refine hmain.trans ?_
    have him : (y * I).im = y := by simp
    rw [him]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith [ht.2]) (by positivity))
  · intro r hr
    have hmem1 : t - r ∈ Icc (-1) (N + 1) :=
      ⟨by linarith [hr.1, hr.2], by linarith [ht.2, hr.1]⟩
    have hmem2 : t₀ - r ∈ Icc (-1) (N + 1) :=
      ⟨by have := (abs_le.mp h1).2; linarith [hr.2], by linarith [ht₀.2, hr.1]⟩
    have hb1 : |W (t - r) - W (t₀ - r)| ≤ ε :=
      hWε _ _ hmem1 hmem2 (le_of_eq (by rw [sub_sub_sub_cancel_right]))
    have hb2 : |W t - W t₀| ≤ ε :=
      hWε _ _ ⟨by linarith [ht.1], by linarith [ht.2]⟩
        ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩ le_rfl
    calc |(W (t - r) - W t) - (W (t₀ - r) - W t₀)|
        = |(W (t - r) - W (t₀ - r)) + (W t₀ - W t)| := by ring_nf
      _ ≤ |W (t - r) - W (t₀ - r)| + |W t₀ - W t| := abs_add_le _ _
      _ = |W (t - r) - W (t₀ - r)| + |W t - W t₀| := by rw [abs_sub_comm (W t₀) (W t)]
      _ ≤ 2 * ε := by linarith

/-- **TR3, continuity in time.** For fixed `y > 0` the map `t ↦ f̂_t(iy)` is continuous on
`[0,N]`: at `t ≈ t₀` the map `f̂_t` is close to the reverse flow with the frozen driver
`W (t₀ − ·) − W t₀` (previous lemma, via uniform continuity of `W` on the compact window)
and the frozen flow is continuous in time (`continuousOn_revMap_time`). -/
theorem continuousOn_fwdMapInv_mul_I (hW : Continuous W) (hW0 : W 0 = 0) {y : ℝ} (hy : 0 < y)
    (hN : 0 ≤ N) : ContinuousOn (fun t : ℝ => fwdMapInv W t (y * I)) (Icc 0 N) := by
  rw [Metric.continuousOn_iff]
  intro t₀ ht₀ ε hε
  set E : ℝ := Real.exp (2 * N / y ^ 2) with hE
  have hEpos : 0 < E := by rw [hE]; positivity
  have huc : UniformContinuousOn W (Icc (-1) (N + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hW.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ₁, hδ₁, hδ₁prop⟩ := huc (ε / (8 * E)) (by positivity)
  set V₀ : ℝ → ℝ := fun r => W (t₀ - r) - W t₀ with hV₀
  have hV₀c : Continuous V₀ := by rw [hV₀]; fun_prop
  have hcontV : ContinuousWithinAt (fun t : ℝ => revMap V₀ t (y * I)) (Icc 0 N) t₀ :=
    continuousOn_revMap_time V₀ hV₀c (z := y * I) (by simpa using hy) (T := N) hN t₀ ht₀
  rw [Metric.continuousWithinAt_iff] at hcontV
  obtain ⟨δ₂, hδ₂, hδ₂prop⟩ := hcontV (ε / 2) (by linarith)
  refine ⟨min (min δ₁ 1) δ₂, lt_min (lt_min hδ₁ one_pos) hδ₂, fun t ht htd => ?_⟩
  have htd₁ : dist t t₀ < min δ₁ 1 := htd.trans_le (min_le_left _ _)
  have hlt2 : dist t t₀ < δ₂ := htd.trans_le (min_le_right _ _)
  have hlt1 : dist t t₀ < δ₁ := htd₁.trans_le (min_le_left _ _)
  have hlt1' : dist t t₀ ≤ 1 := (htd₁.trans_le (min_le_right _ _)).le
  have hlt1'' : |t - t₀| ≤ 1 := by rw [← Real.dist_eq]; exact hlt1'
  have hWε : ∀ a b : ℝ, a ∈ Icc (-1) (N + 1) → b ∈ Icc (-1) (N + 1) →
      |a - b| ≤ |t - t₀| → |W a - W b| ≤ ε / (8 * E) := by
    intro a b ha hb hab
    have hab' : dist a b ≤ dist t t₀ := by rwa [Real.dist_eq, Real.dist_eq]
    have h := hδ₁prop a ha b hb (lt_of_le_of_lt hab' hlt1)
    rw [Real.dist_eq] at h
    exact h.le
  have hpiece1 := norm_fwdMapInv_sub_revMap_timeRev_le (N := N) hW hW0 ht ht₀ hy hlt1''
    (by positivity) hWε
  have hpiece1' : ‖fwdMapInv W t (y * I) - revMap V₀ t (y * I)‖ ≤ ε / 4 := by
    rw [← hE] at hpiece1
    refine hpiece1.trans ?_
    have heq : 2 * (ε / (8 * E)) * E = ε / 4 := by
      field_simp
      try ring
    exact heq.le
  have hpiece2 : ‖revMap V₀ t (y * I) - revMap V₀ t₀ (y * I)‖ < ε / 2 := by
    have h := hδ₂prop ht hlt2
    rwa [dist_eq] at h
  have hft₀ : fwdMapInv W t₀ (y * I) = revMap V₀ t₀ (y * I) := by
    rw [hV₀]
    exact fwdMapInv_eq_revMap_timeRev W hW hW0 ht₀.1 (mul_I_mem_H hy)
  rw [dist_eq]
  calc ‖fwdMapInv W t (y * I) - fwdMapInv W t₀ (y * I)‖
      = ‖(fwdMapInv W t (y * I) - revMap V₀ t (y * I))
          + (revMap V₀ t (y * I) - revMap V₀ t₀ (y * I))‖ := by
        rw [hft₀]; congr 1; abel
    _ ≤ ‖fwdMapInv W t (y * I) - revMap V₀ t (y * I)‖
        + ‖revMap V₀ t (y * I) - revMap V₀ t₀ (y * I)‖ := norm_add_le _ _
    _ ≤ ε / 4 + ε / 2 := add_le_add hpiece1' hpiece2.le
    _ < ε := by linarith

/-! ## The trace (TR3) -/

/-- **TR3 (EXT-RS), trace from the radial derivative bound.** Kemppainen, *Schramm–Loewner
Evolution*, (6.19) p. 112, in the proof of Thm 5.2 (§6.2.3). If `0 < δ`, `0 ≤ C`, `W` is continuous with
`W 0 = 0`, and `‖(f̂_t)'(iy)‖ ≤ C y^{δ−1}` for every `t ∈ [0,N]` and `y ∈ (0,1]`, then for
every `t ∈ [0,N]` the radial limit `trace W t = lim_{y↓0} f̂_t(iy)` exists,
`‖f̂_t(iy) − trace W t‖ ≤ (C/δ) y^δ` on `(0,1]`, and `t ↦ trace W t` is continuous on
`[0,N]`.

(The hypotheses `0 < δ`, `0 ≤ C`, `Continuous W`, `W 0 = 0` are those of the corrected
statement: with `δ = 0` the bound `C/δ · y^δ` degenerates and the statement is false.) -/
theorem trace_of_radialBound (hδ : 0 < δ) (hC : 0 ≤ C) (hW : Continuous W) (hW0 : W 0 = 0)
    (h : ∀ t ∈ Icc 0 N, ∀ y ∈ Ioc (0 : ℝ) 1,
      ‖deriv (fwdMapInv W t) (y * I)‖ ≤ C * y ^ (δ - 1)) :
    (∀ t ∈ Icc 0 N, Tendsto (fun y : ℝ => fwdMapInv W t (y * I)) (𝓝[>] (0 : ℝ)) (𝓝 (trace W t))) ∧
    (∀ t ∈ Icc 0 N, ∀ y ∈ Ioc (0 : ℝ) 1,
      ‖fwdMapInv W t (y * I) - trace W t‖ ≤ C / δ * y ^ δ) ∧
    ContinuousOn (trace W) (Icc 0 N) := by
  have htend : ∀ t ∈ Icc 0 N,
      Tendsto (fun y : ℝ => fwdMapInv W t (y * I)) (𝓝[>] (0 : ℝ)) (𝓝 (trace W t)) := by
    intro t ht
    unfold trace
    exact tendsto_nhds_limUnder
      (exists_tendsto_fwdMapInv_mul_I hδ hC hW hW0 ht.1 fun y hy => h t ht y hy)
  refine ⟨htend, ?_, ?_⟩
  · intro t ht y hy
    exact norm_fwdMapInv_mul_I_sub_trace_le hδ hW hW0 ht.1 hy
      (fun y hy => h t ht y hy) (htend t ht)
  · by_cases hN : 0 ≤ N
    · rw [Metric.continuousOn_iff]
      intro t₀ ht₀ ε hε
      obtain ⟨y, hyIoc, hyb⟩ :=
        exists_mul_rpow_lt (K := C / δ) hδ (by linarith : 0 < ε / 3)
      obtain ⟨δc, hδc, hδcprop⟩ :=
        (Metric.continuousOn_iff.mp (continuousOn_fwdMapInv_mul_I hW hW0 hyIoc.1 hN)) t₀ ht₀
          (ε / 3) (by linarith)
      refine ⟨δc, hδc, fun t ht htd => ?_⟩
      have h1 : ‖fwdMapInv W t (y * I) - trace W t‖ ≤ C / δ * y ^ δ :=
        norm_fwdMapInv_mul_I_sub_trace_le hδ hW hW0 ht.1 hyIoc
          (fun y hy => h t ht y hy) (htend t ht)
      have h2 : ‖fwdMapInv W t₀ (y * I) - trace W t₀‖ ≤ C / δ * y ^ δ :=
        norm_fwdMapInv_mul_I_sub_trace_le hδ hW hW0 ht₀.1 hyIoc
          (fun y hy => h t₀ ht₀ y hy) (htend t₀ ht₀)
      have h3 : ‖fwdMapInv W t (y * I) - fwdMapInv W t₀ (y * I)‖ < ε / 3 := by
        have h := hδcprop t ht htd
        rwa [dist_eq] at h
      rw [dist_eq]
      calc ‖trace W t - trace W t₀‖
          = ‖(trace W t - fwdMapInv W t (y * I))
              + (fwdMapInv W t (y * I) - fwdMapInv W t₀ (y * I))
              + (fwdMapInv W t₀ (y * I) - trace W t₀)‖ := by congr 1; abel
        _ ≤ ‖trace W t - fwdMapInv W t (y * I)‖
              + ‖fwdMapInv W t (y * I) - fwdMapInv W t₀ (y * I)‖
              + ‖fwdMapInv W t₀ (y * I) - trace W t₀‖ := by
            have ha := norm_add_le (trace W t - fwdMapInv W t (y * I))
              (fwdMapInv W t (y * I) - fwdMapInv W t₀ (y * I))
            have hb := norm_add_le (trace W t - fwdMapInv W t (y * I)
              + (fwdMapInv W t (y * I) - fwdMapInv W t₀ (y * I)))
              (fwdMapInv W t₀ (y * I) - trace W t₀)
            linarith
        _ < ε := by
            have h3' := h1
            rw [norm_sub_rev] at h3'
            linarith
    · intro t ht
      exact absurd ht (by rw [Icc_eq_empty hN]; simp)

end RS
end QuantumZipper
