/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovWeyl3 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovWeyl2Mv
import LatticeProb.Bonanno.LQGMetric.Field.MarkovWeylConv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Weyl's lemma: the representation `T φ = ∫ g φ` (task P2-MKH2, leaf (H))

For `T ∈ 𝒟'(V)` with `T(−Δf/2π) = 0` for all `f ∈ C_c^∞(V)`, the harmonic function
`g = weylFun T` (`MarkovWeyl2Mv.harmonicOnNhd_weylFun`) represents `T`:
`T φ = ∫ g φ` (`integral_mul_weylFun`), hence `exists_harmonic_of_laplacian_eq_zero`.

Proof (Hörmander, *The Analysis of Linear Partial Differential Operators I*, Thm 4.1.4 / the
regularization `u * ρ_ε → u` and Thm 4.4.1): fix `K = tsupport φ` and `δ > 0` with
`K' = cthickening δ K ⊆ V`. For `0 < ε ≤ δ`, `φ * ρ_ε ∈ 𝓓_{K'}` and, `T` commuting with the
convolution integral (`exists_conv_pairing_on`, a version of `MarkovWeyl.exists_conv_pairing` for
an arbitrary compact `K'` containing the supports),
* `T(φ * ρ_ε) = ∫ φ(y) T(ρ_ε(· − y)) dy = ∫ φ g` (independent of `ε`), and
* `T(φ * ρ_ε) = ∫ ρ_ε(t) T(φ(· − t)) dt → T φ` as `ε → 0` (continuity of translation in `𝓓_{K'}`).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric TopologicalSpace InnerProductSpace
open scoped Real Distributions BoundedContinuousFunction

namespace LQGMetric
namespace MarkovWeyl3

open MarkovWeyl MarkovWeyl2

lemma structureMap_congr {K₁ K₂ : Compacts ℂ} {f : 𝓓^{⊤}_{K₁}(ℂ, ℝ)} {g : 𝓓^{⊤}_{K₂}(ℂ, ℝ)}
    (h : ∀ x, f x = g x) (i : ℕ) :
    ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i f =
      ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i g := by
  have e : (f : ℂ → ℝ) = g := funext h
  refine DFunLike.coe_injective ?_
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply,
    ContDiffMapSupportedIn.structureMapCLM_top_apply, e]

/-- continuity of a family in `𝓓_{K₂}` transfers from a family in `𝓓_{K₁}` with the same
underlying functions -/
lemma continuous_of_congr {X : Type*} [TopologicalSpace X] {K₁ K₂ : Compacts ℂ}
    {F : X → 𝓓^{⊤}_{K₁}(ℂ, ℝ)} {G : X → 𝓓^{⊤}_{K₂}(ℂ, ℝ)} (hF : Continuous F)
    (h : ∀ y x, G y x = F y x) : Continuous G := by
  rw [ContDiffMapSupportedIn.continuous_iff_comp]
  intro i
  exact ((ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i).continuous.comp hF).congr fun y =>
    (structureMap_congr (h y) i).symm

/-- **Distributions commute with convolution integrals**, on any compact `K'` containing the
supports of the translates. -/
theorem exists_conv_pairing_on {K' : Compacts ℂ} {ρ φ : ℂ → ℝ}
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) {R S : ℝ}
    (hρS : ∀ x, S < ‖x‖ → ρ x = 0) (hφR : ∀ y, R < ‖y‖ → φ y = 0) (hφ : Continuous φ)
    (hK : ∀ y x, φ y * ρ (x - y) ≠ 0 → x ∈ (K' : Set ℂ)) :
    ∃ F : ℂ → 𝓓^{⊤}_{K'}(ℂ, ℝ), (∀ y x, F y x = φ y * ρ (x - y)) ∧
      ∃ I : 𝓓^{⊤}_{K'}(ℂ, ℝ), (∀ x, I x = ∫ y, φ y * ρ (x - y)) ∧
        ∀ L : 𝓓^{⊤}_{K'}(ℂ, ℝ) →L[ℝ] ℝ, L I = ∫ y, L (F y) := by
  let F : ℂ → 𝓓^{⊤}_{K'}(ℂ, ℝ) := fun y => ContDiffMapSupportedIn.of_support_subset
    (contDiff_const.mul (hρ.comp (contDiff_id.sub contDiff_const))) (fun x hx => hK y x hx)
  have hFa : ∀ y x, F y x = φ y * ρ (x - y) := fun _ _ => rfl
  have hsm : ∀ i y, ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (F y) =
      ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (convFam hρ hρS hφR y) :=
    fun i y => structureMap_congr (fun x => by rw [hFa, convFam_apply]) i
  have hcont : Continuous F :=
    continuous_of_congr (continuous_convFam hρ hρS hφR hφ) fun y x => by rw [hFa, convFam_apply]
  have hφc : HasCompactSupport φ := HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R)
    fun x hx => hφR x (by simpa [mem_closedBall, dist_zero_right] using hx)
  obtain ⟨C, hC⟩ := hφc.exists_bound_of_continuous hφ
  have hB : ∀ i, ∃ B, ∀ y, ‖ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (F y)‖ ≤ B := by
    intro i
    obtain ⟨B, hB⟩ := bound_convFam hρ hρS hφR (C := C)
      (fun y => by simpa [Real.norm_eq_abs] using hC y) i
    exact ⟨B, fun y => by rw [hsm]; exact hB y⟩
  set μ : Measure ℂ := volume.restrict (closedBall 0 R)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 (measure_closedBall_lt_top).ne
  obtain ⟨I, hI, hT⟩ := exists_testIntegral_measure μ hcont hB
  have hout : ∀ y ∉ closedBall (0 : ℂ) R, F y = 0 := fun y hy => by
    refine ContDiffMapSupportedIn.ext fun x => ?_
    rw [hFa, hφR y (by simpa [mem_closedBall, dist_zero_right] using hy), zero_mul]
    rfl
  refine ⟨F, hFa, I, fun x => ?_, fun L => ?_⟩
  · rw [hI x]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    rw [hFa, hφR y (by simpa [mem_closedBall, dist_zero_right] using hy), zero_mul]
  · rw [hT L]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    rw [hout y hy, map_zero]

/-- **Weyl's lemma, representation.** A weakly harmonic distribution is integration against the
harmonic function `weylFun T`. -/
theorem integral_mul_weylFun {V : Opens ℂ} (T : DistOn V)
    (hT : ∀ f : MarkovZB.zsSub (V : Set ℂ), T (MarkovHarm.cmTestOn f) = 0) (φ : TestOn V) :
    T φ = ∫ x, weylFun T x * φ x := by
  set Kφ := tsupport (φ : ℂ → ℝ)
  have hKc : IsCompact Kφ := φ.hasCompactSupport
  obtain ⟨δ, hδ, hδV⟩ := hKc.exists_cthickening_subset_open V.isOpen φ.tsupport_subset
  let K' : Compacts ℂ := ⟨cthickening δ Kφ, hKc.cthickening⟩
  have hK'V : (K' : Set ℂ) ⊆ V := hδV
  obtain ⟨R, hR0⟩ := hKc.isBounded.subset_closedBall 0
  have hR : ∀ y, R < ‖y‖ → φ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport fun h => by
    have := hR0 h; rw [mem_closedBall, dist_zero_right] at this; linarith
  have hφs : ∀ y, φ y ≠ 0 → y ∈ Kφ := fun y hy => subset_tsupport _ hy
  let L : 𝓓^{⊤}_{K'}(ℂ, ℝ) →L[ℝ] ℝ := T.comp (TestFunction.ofSupportedInCLM ℝ hK'V)
  -- translates of `φ`, as a continuous family in `𝓓_{K'}`
  have hqK : ∀ t : ℂ, closedBall (projB 0 δ t) R ⊆ (ballK0 (R + δ) : Set ℂ) := fun t =>
    closedBall_subset_closedBall' (by
      have := norm_projB_sub_le hδ 0 t; rw [sub_zero] at this; rw [dist_zero_right]; linarith)
  have hGs : ∀ t, Function.support (fun x => φ (x - projB 0 δ t)) ⊆ (K' : Set ℂ) :=
    fun t x hx => mem_cthickening_of_dist_le x (x - projB 0 δ t) δ Kφ (hφs _ hx) (by
      rw [dist_eq_norm, sub_sub_cancel]
      simpa using norm_projB_sub_le hδ 0 t)
  let G : ℂ → 𝓓^{⊤}_{K'}(ℂ, ℝ) := fun t => ContDiffMapSupportedIn.of_support_subset
    (φ.contDiff.comp (contDiff_id.sub contDiff_const)) (hGs t)
  have hGc : Continuous G := continuous_of_congr
    (continuous_transFam φ.contDiff hR hqK (continuous_projB 0 δ)) fun t x => rfl
  let c : ℂ → ℝ := fun t => L (G t)
  have hc : Continuous c := L.continuous.comp hGc
  have hc0 : c 0 = T φ := by
    show T (TestFunction.ofSupportedIn hK'V (G 0)) = T φ
    congr 1
    refine TestFunction.ext fun x => ?_
    show φ (x - projB 0 δ 0) = φ x
    rw [projB_eq hδ (by simpa using hδ.le), sub_zero]
  -- the two expressions of `T(φ * ρ_ε)`
  have key : ∀ ε, 0 < ε → ε ≤ δ → ∫ y, φ y * weylFun T y = ∫ t, rbump ε t * c t := by
    intro ε hε hεδ
    obtain ⟨FA, hFA, IA, hIA, hLA⟩ := exists_conv_pairing_on (K' := K') (contDiff_rbump ε)
      (S := ε) (fun x hx => rbump_eq_zero hε.le hx) hR φ.continuous (fun y x hyx => by
        have h1 := hφs y (left_ne_zero_of_mul hyx)
        have h2 : ‖x - y‖ ≤ ε :=
          not_lt.1 fun h => right_ne_zero_of_mul hyx (rbump_eq_zero hε.le h)
        exact mem_cthickening_of_dist_le x y δ Kφ h1 (by rw [dist_eq_norm]; linarith))
    obtain ⟨FB, hFB, IB, hIB, hLB⟩ := exists_conv_pairing_on (K' := K') φ.contDiff
      (R := ε) hR (fun y hy => rbump_eq_zero hε.le hy) (continuous_rbump ε) (fun t x htx => by
        have h1 : ‖t‖ ≤ ε :=
          not_lt.1 fun h => left_ne_zero_of_mul htx (rbump_eq_zero hε.le h)
        have h2 := hφs _ (right_ne_zero_of_mul htx)
        exact mem_cthickening_of_dist_le x (x - t) δ Kφ h2 (by
          rw [dist_eq_norm, sub_sub_cancel]; linarith))
    have hIAB : IA = IB := ContDiffMapSupportedIn.ext fun x => by
      rw [hIA, hIB]
      have := integral_sub_left_eq_self (fun t => rbump ε t * φ (x - t)) (volume : Measure ℂ) x
      simp only [sub_sub_cancel] at this
      rw [← this]
      exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
    have hA : ∀ y, L (FA y) = φ y * weylFun T y := by
      intro y
      by_cases hy : φ y = 0
      · have : FA y = 0 := ContDiffMapSupportedIn.ext fun x => by rw [hFA, hy, zero_mul]; rfl
        rw [this, map_zero, hy, zero_mul]
      · have hball : closedBall y ε ⊆ V :=
          ((closedBall_subset_cthickening (hφs y hy) ε).trans (cthickening_mono hεδ _)).trans hδV
        rw [weylFun_eq T hT hε hball, ← smul_eq_mul, ← map_smul]
        show T (TestFunction.ofSupportedIn hK'V (FA y)) = _
        congr 1
        refine TestFunction.ext fun x => ?_
        show FA y x = φ y * rbump ε (x - y)
        rw [hFA]
    have hB : ∀ t, L (FB t) = rbump ε t * c t := by
      intro t
      by_cases ht : ‖t‖ ≤ ε
      · have hp : projB 0 δ t = t := projB_eq hδ (by rw [sub_zero]; linarith)
        have : FB t = rbump ε t • G t := ContDiffMapSupportedIn.ext fun x => by
          rw [hFB]
          show _ = rbump ε t * φ (x - projB 0 δ t)
          rw [hp]
        rw [this, map_smul, smul_eq_mul]
      · have h0 := rbump_eq_zero hε.le (not_le.1 ht)
        have : FB t = 0 := ContDiffMapSupportedIn.ext fun x => by rw [hFB, h0, zero_mul]; rfl
        rw [this, map_zero, h0, zero_mul]
    calc ∫ y, φ y * weylFun T y = ∫ y, L (FA y) :=
          integral_congr_ae (Eventually.of_forall fun y => (hA y).symm)
      _ = L IB := by rw [← hLA, hIAB]
      _ = ∫ t, rbump ε t * c t := by rw [hLB]; exact integral_congr_ae (Eventually.of_forall hB)
  -- the limit `ε → 0`
  rw [← hc0, show (fun x => weylFun T x * φ x) = fun x => φ x * weylFun T x from
    funext fun x => mul_comm _ _]
  refine eq_of_forall_dist_le fun η hη => ?_
  obtain ⟨ε₀, hε₀, hcε⟩ := Metric.continuous_iff.mp hc 0 η hη
  obtain ⟨ε, hε, hεδ, hεle⟩ : ∃ ε, 0 < ε ∧ ε ≤ δ ∧ ε ≤ ε₀ / 2 :=
    ⟨min (ε₀ / 2) δ, lt_min (by positivity) hδ, min_le_right _ _, min_le_left _ _⟩
  rw [key ε hε hεδ]
  have hiρ : Integrable (rbump ε) :=
    integrable_of_vanish (continuous_rbump ε) (r := ε) fun t ht => rbump_eq_zero hε.le ht
  have hint : Integrable fun t => rbump ε t * c t :=
    integrable_of_vanish ((continuous_rbump ε).mul hc) (r := ε) fun t ht => by
      rw [rbump_eq_zero hε.le ht, zero_mul]
  have e : (∫ t, rbump ε t * c t) - c 0 = ∫ t, rbump ε t * (c t - c 0) := by
    simp_rw [mul_sub]
    rw [integral_sub hint (hiρ.mul_const _), integral_mul_const, integral_rbump hε, one_mul]
  rw [dist_comm, dist_eq_norm, e]
  calc ‖∫ t, rbump ε t * (c t - c 0)‖ ≤ ∫ t, rbump ε t * η := by
        refine norm_integral_le_of_norm_le (hiρ.mul_const _) (Eventually.of_forall fun t => ?_)
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (rbump_nonneg ε t)]
        by_cases ht : ‖t‖ ≤ ε
        · refine mul_le_mul_of_nonneg_left ?_ (rbump_nonneg ε t)
          have := hcε t (by rw [dist_zero_right]; linarith)
          rw [Real.norm_eq_abs, ← Real.dist_eq]; exact this.le
        · rw [rbump_eq_zero hε.le (not_le.1 ht), zero_mul, zero_mul]
    _ = η := by rw [integral_mul_const, integral_rbump hε, one_mul]

/-- **Weyl's lemma** (Hörmander, *ALPDO I*, Thm 4.4.1 for `Δ`): a distribution on `V` with
`T(−Δf/2π) = 0` for all `f ∈ C_c^∞(V)` is (integration against) a harmonic function. -/
theorem exists_harmonic_of_laplacian_eq_zero {V : Opens ℂ} (T : DistOn V)
    (hT : ∀ f : MarkovZB.zsSub (V : Set ℂ), T (MarkovHarm.cmTestOn f) = 0) :
    ∃ g : ℂ → ℝ, HarmonicOnNhd g V ∧ ∀ φ : TestOn V, T φ = ∫ x, g x * φ x :=
  ⟨weylFun T, harmonicOnNhd_weylFun T hT, integral_mul_weylFun T hT⟩

end MarkovWeyl3
end LQGMetric
