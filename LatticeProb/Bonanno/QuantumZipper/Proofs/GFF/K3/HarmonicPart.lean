/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.HarmonicPart at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.HalfDiscTV
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Harmonic sample paths of the harmonic part (L4 prerequisite (a))

1. **Weyl lemma for the mean-value property** (`harmonicOnNhd_of_meanValue`): a continuous
   `u : ℂ → ℝ` whose averages over all circles `∂B(z,s)` with `closedBall z s ⊆ U` equal `u z` is
   harmonic on the open set `U`. Proof: (i) mollifying with a radial bump reproduces `u`
   (polar coordinates and the mean-value property), so `u` is locally smooth; (ii) for a radial
   test function `φ` near `z`, `∫ φ Δu = ∫ u Δφ = u(z) ∫ Δφ = 0` (F3, radiality of `Δφ`), which
   forces `Δu(z) = 0`.
-/

noncomputable section

open MeasureTheory Filter Set Metric Laplacian
open scoped Real Topology ComplexConjugate ENNReal Convolution

namespace QuantumZipper

namespace K3

/-! ## Radial bumps -/

/-- A smooth radial bump about `z`, positive exactly on `ball z ε`. -/
def rbump (z : ℂ) (ε : ℝ) (x : ℂ) : ℝ := Real.smoothTransition (1 - ‖x - z‖ ^ 2 / ε ^ 2)

theorem contDiff_rbump (z : ℂ) (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (rbump z ε) :=
  Real.smoothTransition.contDiff.comp
    (contDiff_const.sub (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _))

theorem rbump_nonneg (z : ℂ) (ε : ℝ) (x : ℂ) : 0 ≤ rbump z ε x :=
  Real.smoothTransition.nonneg _

theorem rbump_eq_zero {z : ℂ} {ε : ℝ} (hε : 0 < ε) {x : ℂ} (hx : ε ≤ ‖x - z‖) :
    rbump z ε x = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have h1 : ε ^ 2 ≤ ‖x - z‖ ^ 2 := pow_le_pow_left₀ hε.le hx 2
  have h2 : 1 ≤ ‖x - z‖ ^ 2 / ε ^ 2 := (one_le_div (by positivity)).2 h1
  linarith

theorem rbump_pos {z : ℂ} {ε : ℝ} (hε : 0 < ε) {x : ℂ} (hx : x ∈ ball z ε) :
    0 < rbump z ε x := by
  refine Real.smoothTransition.pos_of_pos ?_
  have hx' : ‖x - z‖ < ε := mem_ball_iff_norm.1 hx
  have h1 : ‖x - z‖ ^ 2 < ε ^ 2 := pow_lt_pow_left₀ hx' (norm_nonneg _) two_ne_zero
  have h2 : ‖x - z‖ ^ 2 / ε ^ 2 < 1 := (div_lt_one (by positivity)).2 h1
  linarith

theorem tsupport_rbump_subset {z : ℂ} {ε : ℝ} (hε : 0 < ε) :
    tsupport (rbump z ε) ⊆ closedBall z ε :=
  closure_minimal (fun x hx => by
    by_contra h
    rw [mem_closedBall_iff_norm, not_le] at h
    exact hx (rbump_eq_zero hε h.le)) isClosed_closedBall

theorem hasCompactSupport_rbump {z : ℂ} {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (rbump z ε) :=
  (isCompact_closedBall z ε).of_isClosed_subset (isClosed_tsupport _) (tsupport_rbump_subset hε)

/-! ## Rotation invariance of the Laplacian -/

theorem bilin_rot' (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (p q : ℝ) (hn : p ^ 2 + q ^ 2 = 1) :
    B (p • (1 : ℂ) + q • Complex.I) (p • (1 : ℂ) + q • Complex.I) +
      B ((-q) • (1 : ℂ) + p • Complex.I) ((-q) • (1 : ℂ) + p • Complex.I) =
      B 1 1 + B Complex.I Complex.I := by
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  linear_combination (B 1 1 + B Complex.I Complex.I) * hn

theorem bilin_rot (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) {a : ℂ} (ha : ‖a‖ = 1) :
    B a a + B (a * Complex.I) (a * Complex.I) = B 1 1 + B Complex.I Complex.I := by
  have hn : a.re ^ 2 + a.im ^ 2 = 1 := by
    have := sq_norm_eq_k3 a; rw [ha] at this; linarith
  have ea : a = a.re • (1 : ℂ) + a.im • Complex.I := by
    apply Complex.ext <;> simp
  have eb : a * Complex.I = (-a.im) • (1 : ℂ) + a.re • Complex.I := by
    apply Complex.ext <;> simp
  calc B a a + B (a * Complex.I) (a * Complex.I)
      = B (a.re • (1 : ℂ) + a.im • Complex.I) (a.re • (1 : ℂ) + a.im • Complex.I) +
        B ((-a.im) • (1 : ℂ) + a.re • Complex.I) ((-a.im) • (1 : ℂ) + a.re • Complex.I) := by
          rw [← ea, ← eb]
    _ = _ := bilin_rot' B a.re a.im hn

theorem laplacian_comp_rot {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (z a : ℂ) (ha : ‖a‖ = 1)
    (x : ℂ) : Δ (fun y => f (z + a * (y - z))) x = Δ f (z + a * (x - z)) := by
  set L : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℂ ℂ a).restrictScalars ℝ with hL
  set b : ℂ := z - a * z with hb
  have hT : (fun y => f (z + a * (y - z))) = (fun y => f (y + b)) ∘ L := by
    funext y; simp only [Function.comp, hL, hb, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.mul_apply']
    congr 1; ring
  have hg : ContDiff ℝ 2 (fun y => f (y + b)) := hf.comp (contDiff_id.add contDiff_const)
  have hLx : L x + b = z + a * (x - z) := by
    simp only [hL, hb, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.mul_apply']
    ring
  rw [hT, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only
  rw [L.iteratedFDeriv_comp_right hg x (by norm_num)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_comp_add_right, iteratedFDeriv_two_apply, hLx]
  have e1 : L 1 = a := by simp [hL]
  have e2 : L Complex.I = a * Complex.I := by simp [hL]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e1, e2]
  exact bilin_rot _ ha

/-- Radiality about `z`: equal distance to `z` gives equal values. -/
def IsRadialAt (g : ℂ → ℝ) (z : ℂ) : Prop := ∀ x y, ‖x - z‖ = ‖y - z‖ → g x = g y

theorem exists_rot {z x y : ℂ} (h : ‖x - z‖ = ‖y - z‖) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ y = z + a * (x - z) := by
  by_cases hx : x - z = 0
  · have hy : y - z = 0 := by rw [hx, norm_zero] at h; exact norm_eq_zero.1 h.symm
    exact ⟨1, by simp, by rw [hx]; linear_combination hy⟩
  · refine ⟨(y - z) / (x - z), ?_, ?_⟩
    · rw [norm_div, h, div_self (by rw [← h]; exact norm_ne_zero_iff.2 hx)]
    · field_simp; ring

theorem isRadialAt_rbump (z : ℂ) (ε : ℝ) : IsRadialAt (rbump z ε) z := fun x y h => by
  unfold rbump; rw [h]

theorem isRadialAt_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) {z : ℂ} (hr : IsRadialAt φ z) :
    IsRadialAt (Δ φ) z := by
  intro x y h
  obtain ⟨a, ha, rfl⟩ := exists_rot h
  have hinv : (fun w => φ (z + a * (w - z))) = φ := funext fun w => by
    refine (hr _ _ ?_).symm
    · rw [add_sub_cancel_left, norm_mul, ha, one_mul]
  rw [← laplacian_comp_rot hφ z a ha x, hinv]

/-! ## The radial integration formula -/

/-- If `u` has the mean-value property at `z` for radii `< δ` and `g` is continuous, radial
about `z` and vanishes off `ball z δ`, then `∫ u g = u z ∫ g`. -/
theorem integral_mul_radial {u g : ℂ → ℝ} (hu : Continuous u) (hg : Continuous g) {z : ℂ}
    {δ : ℝ} (hδ : 0 < δ) (hgr : IsRadialAt g z) (hgs : ∀ x, δ ≤ ‖x - z‖ → g x = 0)
    (hmv : ∀ s, 0 < s → s < δ → ∫ w, u w ∂circleUnif z s = u z) :
    ∫ x, u x * g x = u z * ∫ x, g x := by
  have hgc : HasCompactSupport g := HasCompactSupport.intro (isCompact_closedBall z δ)
    fun x hx => hgs x (by rw [mem_closedBall_iff_norm, not_le] at hx; exact hx.le)
  have hI1 : Integrable fun x => u x * g x := (hu.mul hg).integrable_of_hasCompactSupport
    hgc.mul_left
  have hI2 : Integrable fun x => g x := hg.integrable_of_hasCompactSupport hgc
  suffices h0 : ∫ x, (u x - u z) * g x = 0 by
    have e : (fun x => (u x - u z) * g x) = fun x => u x * g x - u z * g x := by
      funext x; ring
    rw [e, integral_sub hI1 (hI2.const_mul _), integral_const_mul] at h0
    linarith
  set F : ℂ → ℝ := fun x => (u x - u z) * g x with hF
  have hFc : Continuous F := (hu.sub continuous_const).mul hg
  rw [← integral_add_right_eq_self _ z]
  rw [← Complex.integral_comp_polarCoord_symm]
  have hpt : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  set G : ℝ × ℝ → ℝ := fun p => p.1 * F (circleMap z p.1 p.2) with hG
  have hstep : ∀ p ∈ polarCoord.target,
      p.1 • F (Complex.polarCoord.symm p + z) = G p := by
    intro p _
    rw [polarCoord_symm_eq_circleMap, smul_eq_mul]
    congr 2
    simp [circleMap, add_comm]
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hstep, hpt]
  have hcm := continuous_circleMap_uncurry z
  have hGc : Continuous G := continuous_fst.mul (hFc.comp hcm)
  have hGz : ∀ p : ℝ × ℝ, δ < p.1 → G p = 0 := by
    intro p hp
    simp only [hG, hF]
    rw [hgs _ (by rw [norm_circleMap_sub_center, abs_of_pos (hδ.trans hp)]; exact hp.le)]
    ring
  have hint : IntegrableOn G (Ioi 0 ×ˢ Ioo (-π) π) (volume.prod volume) := by
    have hS : IntegrableOn G (Icc 0 δ ×ˢ Icc (-π) π) (volume.prod volume) :=
      hGc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hS' : IntegrableOn G (Ioc 0 δ ×ˢ Ioo (-π) π) (volume.prod volume) :=
      hS.mono_set (prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self)
    refine hS'.of_forall_sdiff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    rintro p ⟨⟨hp1, hp2⟩, hpS⟩
    apply hGz
    by_contra h
    exact hpS ⟨⟨hp1, not_lt.mp h⟩, hp2⟩
  rw [Measure.volume_eq_prod, setIntegral_prod _ hint]
  refine setIntegral_eq_zero_of_forall_eq_zero fun ρ hρ => ?_
  have hρ0 : 0 < ρ := hρ
  have hrad : ∀ θ, g (circleMap z ρ θ) = g (circleMap z ρ 0) := fun θ =>
    hgr _ _ (by rw [norm_circleMap_sub_center, norm_circleMap_sub_center])
  have e : (fun θ => G (ρ, θ)) =
      fun θ => (ρ * g (circleMap z ρ 0)) * (u (circleMap z ρ θ) - u z) := by
    funext θ; simp only [hG, hF, hrad θ]; ring
  rw [e, integral_const_mul]
  by_cases hρδ : ρ < δ
  · have hcu := integral_circleUnif_eq hu z ρ
    rw [hmv ρ hρ0 hρδ] at hcu
    have hint2 : IntegrableOn (fun θ => u (circleMap z ρ θ)) (Ioo (-π) π) :=
      ((hu.comp (continuous_circleMap z ρ)).integrableOn_Icc).mono_set Ioo_subset_Icc_self
    rw [integral_sub hint2 (integrable_const _), setIntegral_const, measureReal_def,
      Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), smul_eq_mul]
    have h2π : (2 * π) ≠ 0 := by positivity
    have : ∫ θ in Ioo (-π) π, u (circleMap z ρ θ) = 2 * π * u z := by
      rw [hcu, ← mul_assoc, mul_inv_cancel₀ h2π, one_mul]
    rw [this]; ring
  · rw [hgs _ (by rw [norm_circleMap_sub_center, abs_of_pos hρ0]; exact not_lt.mp hρδ)]
    ring

theorem integral_pos_of_pos_on_ball {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hnn : ∀ x, 0 ≤ f x) {z : ℂ} {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x ∈ ball z ε, 0 < f x) :
    0 < ∫ x, f x :=
  (integral_pos_iff_support_of_nonneg hnn (hf.integrable_of_hasCompactSupport hfc)).2
    (lt_of_lt_of_le (measure_ball_pos volume z hε)
      (measure_mono fun x hx => (hpos x hx).ne'))

/-! ## The Weyl lemma -/

/-- The mean-value property on circles inside `U`. -/
def MeanValueOn (u : ℂ → ℝ) (U : Set ℂ) : Prop :=
  ∀ z ∈ U, ∀ s, 0 < s → closedBall z s ⊆ U → ∫ w, u w ∂circleUnif z s = u z

/-- A continuous cutoff equal to `1` on `closedBall z S`. -/
def cutK3 (z : ℂ) (S : ℝ) (x : ℂ) : ℝ := bumpK3 S (x - z)

theorem exists_smooth_eq_of_meanValue {u : ℂ → ℝ} (hu : Continuous u) {U : Set ℂ}
    (hU : IsOpen U) (hmv : MeanValueOn u U) {z : ℂ} (hz : z ∈ U) :
    ∃ w : ℂ → ℝ, ContDiff ℝ 2 w ∧ HasCompactSupport w ∧ ∃ δ > 0, closedBall z (3 * δ) ⊆ U ∧
      ∀ y ∈ ball z δ, u y = w y := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z hz
  set δ := ε / 4 with hδdef
  have hδ : 0 < δ := by positivity
  have hsub : closedBall z (3 * δ) ⊆ U :=
    (closedBall_subset_ball (by rw [hδdef]; linarith)).trans hball
  set ψ := rbump 0 δ with hψ
  set I := ∫ x, ψ x with hI
  have hIpos : 0 < I := integral_pos_of_pos_on_ball (contDiff_rbump 0 δ (n := 0)).continuous
    (hasCompactSupport_rbump hδ) (rbump_nonneg 0 δ) hδ fun x hx => rbump_pos hδ hx
  set χ := cutK3 z (2 * δ) with hχ
  have hχc : Continuous χ := (continuous_bumpK3 _).comp (continuous_id.sub continuous_const)
  have hχs : HasCompactSupport χ :=
    HasCompactSupport.intro (isCompact_closedBall z (2 * δ + 1)) fun v hv => by
      rw [mem_closedBall_iff_norm, not_le] at hv
      simp only [hχ, cutK3, bumpK3]
      rw [min_eq_right (by linarith), max_eq_left (by linarith)]
  have hχ1 : ∀ x, ‖x - z‖ ≤ 2 * δ → χ x = 1 := fun x hx => bumpK3_eq_one hx
  set v : ℂ → ℝ := fun x => χ x * u x with hv
  have hvc : Continuous v := hχc.mul hu
  have hvs : HasCompactSupport v := hχs.mul_right
  set w : ℂ → ℝ := fun y => I⁻¹ * (v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) y with hw
  refine ⟨w, ?_, ?_, δ, hδ, hsub, fun y hy => ?_⟩
  · exact contDiff_const.mul ((hasCompactSupport_rbump hδ).contDiff_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hvc.locallyIntegrable (contDiff_rbump 0 δ))
  · exact (hvs.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (hasCompactSupport_rbump hδ)).mul_left
  · have hyz : ‖y - z‖ < δ := mem_ball_iff_norm.1 hy
    have e1 : (v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) y = ∫ t, u t * ψ (y - t) := by
      rw [convolution_def]
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, hv]
      by_cases ht : ‖y - t‖ < δ
      · rw [hχ1 t (by
          calc ‖t - z‖ = ‖(y - z) - (y - t)‖ := by ring_nf
            _ ≤ ‖y - z‖ + ‖y - t‖ := norm_sub_le _ _
            _ ≤ 2 * δ := by linarith), one_mul]
      · rw [hψ, rbump_eq_zero hδ (by rw [sub_zero]; exact not_lt.mp ht)]; ring
    have e2 : ∫ t, u t * ψ (y - t) = u y * ∫ t, ψ (y - t) := by
      refine integral_mul_radial hu ((contDiff_rbump 0 δ (n := 0)).continuous.comp
        (continuous_const.sub continuous_id)) hδ ?_ ?_ ?_
      · intro a b hab
        show rbump 0 δ (y - a) = rbump 0 δ (y - b)
        unfold rbump
        rw [sub_zero, sub_zero, norm_sub_rev y a, norm_sub_rev y b, hab]
      · intro t ht
        show rbump 0 δ (y - t) = 0
        exact rbump_eq_zero hδ (by rw [sub_zero, norm_sub_rev]; exact ht)
      · intro s hs hsδ
        refine hmv y (hsub (ball_subset_closedBall (mem_ball.2 (by
          rw [dist_eq_norm]; linarith)))) s hs ?_
        refine (closedBall_subset_closedBall' ?_).trans hsub
        rw [dist_eq_norm]; linarith
    have e3 : ∫ t, ψ (y - t) = I := integral_sub_left_eq_self (fun t => ψ t) volume y
    simp only [hw]
    rw [e1, e2, e3, mul_comm (u y), ← mul_assoc, inv_mul_cancel₀ hIpos.ne', one_mul]

theorem gradInner_comm_k3 (u φ : ℂ → ℝ) (z : ℂ) : gradInner u φ z = gradInner φ u z := by
  simp only [gradInner]; ring

theorem integral_laplacian_eq_zero {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    ∫ x, Δ φ x = 0 := by
  have h := integral_gradInner_eq_neg_integral_mul_laplacian (u := fun _ => (1 : ℝ))
    contDiff_const hφ hc
  simp only [gradInner, fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply,
    zero_mul, add_zero, integral_zero, one_mul] at h
  linarith

theorem laplacian_eq_zero_of_meanValue {u : ℂ → ℝ} (hu : Continuous u) {U : Set ℂ}
    (hU : IsOpen U) (hmv : MeanValueOn u U) {z : ℂ} (hz : z ∈ U) :
    Δ u z = 0 ∧ ContDiffAt ℝ 2 u z := by
  obtain ⟨w, hw2, hwc, δ, hδ, hsub, heq⟩ := exists_smooth_eq_of_meanValue hu hU hmv hz
  have heqn : u =ᶠ[𝓝 z] w := Filter.mem_of_superset (ball_mem_nhds z hδ) fun y hy => heq y hy
  have hw1 : ContDiff ℝ 1 w := hw2.of_le (by norm_num)
  have key : ∀ ε, 0 < ε → ε < δ → ∫ x, rbump z ε x * Δ w x = 0 := by
    intro ε hε hεδ
    set φ := rbump z ε with hφ
    have hφ2 : ContDiff ℝ 2 φ := contDiff_rbump z ε
    have hφc := hasCompactSupport_rbump (z := z) hε
    have hts : ∀ x, δ ≤ ‖x - z‖ → x ∉ tsupport φ := fun x hx h => by
      have := mem_closedBall_iff_norm.1 (tsupport_rbump_subset hε h); linarith
    have F3a := integral_gradInner_eq_neg_integral_mul_laplacian hw1 hφ2 hφc
    have F3b := integral_gradInner_eq_neg_integral_mul_laplacian (hφ2.of_le (by norm_num))
      hw2 hwc
    simp only [gradInner_comm_k3 w φ] at F3a
    have h1 : ∫ x, φ x * Δ w x = ∫ x, w x * Δ φ x := by linarith
    have h2 : ∫ x, w x * Δ φ x = ∫ x, u x * Δ φ x := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show w x * Δ φ x = u x * Δ φ x
      by_cases hx : x ∈ ball z δ
      · rw [heq x hx]
      · rw [laplacian_eq_zero_of_notMem_tsupport (hts x (by
          rw [mem_ball_iff_norm, not_lt] at hx; exact hx))]; ring
    have h3 : ∫ x, u x * Δ φ x = u z * ∫ x, Δ φ x := by
      refine integral_mul_radial hu (continuous_laplacian_K3 hφ2) hδ
        (isRadialAt_laplacian hφ2 (isRadialAt_rbump z ε))
        (fun x hx => laplacian_eq_zero_of_notMem_tsupport (hts x hx)) fun s hs hsδ => ?_
      exact hmv z hz s hs ((closedBall_subset_closedBall (by linarith)).trans hsub)
    rw [h1, h2, h3, integral_laplacian_eq_zero hφ2 hφc, mul_zero]
  have hΔc := continuous_laplacian_K3 hw2
  have hΔs := hasCompactSupport_laplacian_K3 hwc
  have hsign : ∀ c : ℝ, c = 1 ∨ c = -1 → ¬ (0 < c * Δ w z) := by
    intro c hc hpos
    have hcont : Continuous fun x => c * Δ w x := continuous_const.mul hΔc
    obtain ⟨ε₀, hε₀, hε₀b⟩ := Metric.continuousAt_iff.1
      (hcont.continuousAt (x := z)) (c * Δ w z) hpos
    set ε := min ε₀ (δ / 2)
    have hε : 0 < ε := lt_min hε₀ (by positivity)
    have hεδ : ε < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hposb : ∀ x ∈ ball z ε, 0 < c * Δ w x := by
      intro x hx
      have h := hε₀b (lt_of_lt_of_le (mem_ball.1 hx) (min_le_left _ _))
      rw [Real.dist_eq, abs_lt] at h
      linarith [h.1]
    have hint : 0 < ∫ x, rbump z ε x * (c * Δ w x) := by
      refine integral_pos_of_pos_on_ball ((contDiff_rbump z ε (n := 0)).continuous.mul
        (continuous_const.mul hΔc)) (hasCompactSupport_rbump hε).mul_right ?_ hε
        fun x hx => mul_pos (rbump_pos hε hx) (hposb x hx)
      intro x
      by_cases hx : x ∈ ball z ε
      · exact (mul_pos (rbump_pos hε hx) (hposb x hx)).le
      · rw [rbump_eq_zero hε (by rw [mem_ball_iff_norm, not_lt] at hx; exact hx), zero_mul]
    have e : ∫ x, rbump z ε x * (c * Δ w x) = c * ∫ x, rbump z ε x * Δ w x := by
      rw [← integral_const_mul]; congr 1; funext x; ring
    rw [e, key ε hε hεδ, mul_zero] at hint
    exact lt_irrefl _ hint
  have hwz : Δ w z = 0 := by
    rcases lt_trichotomy (Δ w z) 0 with h | h | h
    · exact absurd (by linarith : 0 < -1 * Δ w z) (hsign (-1) (Or.inr rfl))
    · exact h
    · exact absurd (by linarith : 0 < 1 * Δ w z) (hsign 1 (Or.inl rfl))
  refine ⟨?_, hw2.contDiffAt.congr_of_eventuallyEq heqn⟩
  rw [(InnerProductSpace.laplacian_congr_nhds heqn).eq_of_nhds, hwz]

/-- **Weyl lemma (mean-value form).** A continuous function with the circle mean-value property
on an open set is harmonic there. -/
theorem harmonicOnNhd_of_meanValue {u : ℂ → ℝ} (hu : Continuous u) {U : Set ℂ}
    (hU : IsOpen U) (hmv : MeanValueOn u U) : InnerProductSpace.HarmonicOnNhd u U :=
  fun z hz => ⟨(laplacian_eq_zero_of_meanValue hu hU hmv hz).2,
    Filter.mem_of_superset (hU.mem_nhds hz) fun z' hz' =>
      (laplacian_eq_zero_of_meanValue hu hU hmv hz').1⟩

/-! ## Symmetry and averaging of half-disc Poisson measures -/

theorem foldH_conj_k3 (z : ℂ) : foldH (conj z) = foldH z := by
  rw [CircleFubini.foldH_eq_mk, CircleFubini.foldH_eq_mk]
  simp [abs_neg]

theorem norm_foldH_sub_ofReal (t : ℝ) (z : ℂ) : ‖foldH z - t‖ = ‖z - t‖ := by
  unfold foldH
  split_ifs
  · rfl
  · exact norm_conj_sub_ofReal_k3 z t

theorem conj_circleMap_ofReal (t r θ : ℝ) :
    conj (circleMap (t : ℂ) r θ) = circleMap (t : ℂ) r (-θ) := by
  simp only [circleMap, map_add, map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.conj_I]
  push_cast
  ring_nf

theorem integral_circleUnif_conj {t r : ℝ} {g : ℂ → ℝ} (hg : Measurable g) :
    ∫ x, g (conj x) ∂circleUnif (t : ℂ) r = ∫ x, g x ∂circleUnif (t : ℂ) r := by
  rw [circleUnif_eq_circMeas_k3, LQGDimension.Coupling.integral_circMeas'
      (f := fun x => g (conj x)) (hg.comp Complex.continuous_conj.measurable).aestronglyMeasurable,
    LQGDimension.Coupling.integral_circMeas' hg.aestronglyMeasurable]
  congr 1
  simp_rw [conj_circleMap_ofReal]
  rw [intervalIntegral.integral_comp_neg (fun θ => g (circleMap (t : ℂ) r θ)), neg_zero]
  have h := ((periodic_circleMap (t : ℂ) r).comp g).intervalIntegral_add_eq (-(2 * π)) 0
  simp only [Function.comp_def, neg_add_cancel, zero_add] at h
  exact h

theorem halfDiscPoisson_conj {t r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ ball (t : ℂ) r) :
    halfDiscPoisson t r (conj w) = halfDiscPoisson t r w := by
  have hw' : conj w ∈ ball (t : ℂ) r := by
    rw [mem_ball_iff_norm, norm_conj_sub_ofReal_k3]; exact mem_ball_iff_norm.1 hw
  have := isProbabilityMeasure_halfDiscPoisson hr hw
  have := isProbabilityMeasure_halfDiscPoisson hr hw'
  ext A hA
  rw [← ENNReal.ofReal_toReal (measure_ne_top (halfDiscPoisson t r (conj w)) A),
    ← ENNReal.ofReal_toReal (measure_ne_top (halfDiscPoisson t r w) A)]
  congr 1
  have hm : Measurable (A.indicator (1 : ℂ → ℝ)) := measurable_const.indicator hA
  rw [← measureReal_def, ← measureReal_def, ← integral_indicator_one hA,
    ← integral_indicator_one hA,
    integral_halfDiscPoisson_eq_circle' hw' hm.aestronglyMeasurable,
    integral_halfDiscPoisson_eq_circle' hw hm.aestronglyMeasurable]
  have hGm : Measurable fun x : ℂ =>
      (r ^ 2 - ‖w - t‖ ^ 2) / ‖x - w‖ ^ 2 * A.indicator 1 (foldH x) :=
    (measurable_const.div ((measurable_id.sub measurable_const).norm.pow_const 2)).mul
      (hm.comp measurable_foldH)
  rw [← integral_circleUnif_conj (t := t) (r := r) hGm]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [foldH_conj_k3, norm_conj_sub_ofReal_k3]
  rw [show ‖x - conj w‖ = ‖conj x - w‖ by rw [← Complex.norm_conj, map_sub, Complex.conj_conj]]

theorem harmonicOnNhd_density {t r : ℝ} {x : ℂ} (hx : ‖x - t‖ = r) :
    InnerProductSpace.HarmonicOnNhd (fun w : ℂ => (r ^ 2 - ‖w - t‖ ^ 2) / ‖x - w‖ ^ 2)
      (ball (t : ℂ) r) := by
  have e : (fun w : ℂ => (r ^ 2 - ‖w - t‖ ^ 2) / ‖x - w‖ ^ 2) =
      fun w => (((x - t) + (w - t)) / (x - w)).re := by
    funext w
    have := congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := (t : ℂ)) (w := w)) x
    rw [Function.comp_apply, herglotzRieszKernel_def, poissonKernel_def, hx,
      sub_sub_sub_cancel_right] at this
    exact this
  rw [e]
  intro w hw
  have hxw : x - w ≠ 0 := by
    intro h
    have hxw' : x = w := sub_eq_zero.1 h
    rw [hxw'] at hx
    exact (ne_of_lt (mem_ball_iff_norm.1 hw)) hx
  exact AnalyticAt.harmonicAt_re ((analyticAt_const.add (analyticAt_id.sub analyticAt_const)).div
    (analyticAt_const.sub analyticAt_id) hxw)

theorem norm_sub_le_of_sphere {t : ℝ} {z w : ℂ} {s : ℝ} (hw : ‖w - z‖ = s) :
    ‖w - t‖ ≤ ‖z - t‖ + s := by
  calc ‖w - t‖ = ‖(w - z) + (z - t)‖ := by ring_nf
    _ ≤ ‖w - z‖ + ‖z - t‖ := norm_add_le _ _
    _ = _ := by rw [hw]; ring

/-- Circle averages of half-disc Poisson measures: `∫ P_w dσ_{z,s}(w) = P_z`. -/
theorem bind_circleUnif_halfDiscPoisson {t r : ℝ} (hr : 0 < r) {z : ℂ} {s : ℝ} (hs : 0 < s)
    (hzs : ‖z - t‖ + s < r) :
    (circleUnif z s).bind (halfDiscPoisson t r) = halfDiscPoisson t r z := by
  set r'' := ‖z - t‖ + s with hr''
  have hz : z ∈ ball (t : ℂ) r := mem_ball_iff_norm.2 (by linarith)
  have hcirc : ∀ᵐ (w : ℂ) ∂circleUnif z s, ‖w - (t : ℂ)‖ ≤ r'' := by
    filter_upwards [ae_mem_sphere_circleUnif_k3 z hs] with w hw
    exact norm_sub_le_of_sphere (mem_sphere_iff_norm.1 hw)
  have hsph := ae_mem_sphere_circleUnif_k3 (t : ℂ) hr
  have := isProbabilityMeasure_halfDiscPoisson hr hz
  ext A hA
  have hm : Measurable (A.indicator (1 : ℂ → ℝ)) := measurable_const.indicator hA
  set g : ℂ → ℝ := fun x => A.indicator 1 (foldH x) with hg
  have hgm : Measurable g := hm.comp measurable_foldH
  have hg01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1 := fun x => by
    by_cases h : foldH x ∈ A <;> simp [hg, h]
  set f : ℂ × ℂ → ℝ := fun p => (r ^ 2 - ‖p.1 - t‖ ^ 2) / ‖p.2 - p.1‖ ^ 2 * g p.2 with hf
  have hfm : Measurable f :=
    (measurable_const.sub ((measurable_fst.sub measurable_const).norm.pow_const 2)).div
      ((measurable_snd.sub measurable_fst).norm.pow_const 2) |>.mul (hgm.comp measurable_snd)
  set M := r ^ 2 / (r - r'') ^ 2
  have hbd : ∀ w x : ℂ, ‖w - t‖ ≤ r'' → ‖x - t‖ = r → 0 ≤ f (w, x) ∧ f (w, x) ≤ M := by
    intro w x hw hx
    have hd := halfDiscPoisson_density_le (by linarith : r'' < r) hw hx
    have h0 : 0 ≤ (r ^ 2 - ‖w - t‖ ^ 2) / ‖x - w‖ ^ 2 :=
      div_nonneg (by nlinarith [norm_nonneg (w - t)]) (sq_nonneg _)
    obtain ⟨g0, g1⟩ := hg01 x
    exact ⟨mul_nonneg h0 g0, by
      calc _ ≤ (r ^ 2 - ‖w - t‖ ^ 2) / ‖x - w‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left g1 h0
        _ ≤ M := by rw [mul_one]; exact hd⟩
  -- `P_w A` as an integral
  set F : ℂ → ℝ := fun w => ∫ x, f (w, x) ∂circleUnif (t : ℂ) r with hF
  have hPw : ∀ w : ℂ, w ∈ ball (t : ℂ) r → halfDiscPoisson t r w A = ENNReal.ofReal (F w) := by
    intro w hw
    have := isProbabilityMeasure_halfDiscPoisson hr hw
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ A), ← measureReal_def,
      ← integral_indicator_one hA, integral_halfDiscPoisson_eq_circle' hw hm.aestronglyMeasurable]
  have hFm : Measurable F := (hfm.stronglyMeasurable.integral_prod_right' (ν := circleUnif
    (t : ℂ) r)).measurable
  have hFb : ∀ w : ℂ, ‖w - t‖ ≤ r'' → 0 ≤ F w ∧ F w ≤ M := by
    intro w hw
    constructor
    · exact integral_nonneg_of_ae (hsph.mono fun x hx => (hbd w x hw (mem_sphere_iff_norm.1 hx)).1)
    · calc F w ≤ ∫ _, M ∂circleUnif (t : ℂ) r :=
            integral_mono_of_nonneg (hsph.mono fun x hx =>
              (hbd w x hw (mem_sphere_iff_norm.1 hx)).1) (integrable_const _)
              (hsph.mono fun x hx => (hbd w x hw (mem_sphere_iff_norm.1 hx)).2)
        _ = M := by simp
  have hFi : Integrable F (circleUnif z s) :=
    Integrable.of_bound hFm.aestronglyMeasurable M (hcirc.mono fun w hw => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hFb w hw).1]; exact (hFb w hw).2)
  rw [Measure.bind_apply hA (measurable_halfDiscPoisson t r).aemeasurable]
  rw [lintegral_congr_ae (hcirc.mono fun w hw =>
      hPw w (mem_ball_iff_norm.2 (by linarith)))]
  rw [← ofReal_integral_eq_lintegral_ofReal hFi (hcirc.mono fun w hw => (hFb w hw).1),
    ← ENNReal.ofReal_toReal (measure_ne_top (halfDiscPoisson t r z) A), ← measureReal_def,
    ← integral_indicator_one hA, integral_halfDiscPoisson_eq_circle' hz hm.aestronglyMeasurable]
  congr 1
  -- Fubini and the mean-value property in `w`
  have hprod : ∀ᵐ (p : ℂ × ℂ) ∂(circleUnif z s).prod (circleUnif (t : ℂ) r),
      ‖p.1 - (t : ℂ)‖ ≤ r'' ∧ ‖p.2 - (t : ℂ)‖ = r := by
    refine (Measure.ae_prod_iff_ae_ae ?_).2 (hcirc.mono fun w hw => hsph.mono fun x hx =>
      ⟨hw, mem_sphere_iff_norm.1 hx⟩)
    exact (measurableSet_le ((measurable_fst.sub measurable_const).norm) measurable_const).inter
      (measurableSet_eq_fun ((measurable_snd.sub measurable_const).norm) measurable_const)
  have hfi : Integrable f ((circleUnif z s).prod (circleUnif (t : ℂ) r)) :=
    Integrable.of_bound hfm.aestronglyMeasurable M (hprod.mono fun p hp => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hbd p.1 p.2 hp.1 hp.2).1]; exact (hbd _ _ hp.1 hp.2).2)
  rw [hF, integral_integral_swap (f := fun w x => f (w, x)) hfi]
  refine integral_congr_ae (hsph.mono fun x hx => ?_)
  have hx' := mem_sphere_iff_norm.1 hx
  show ∫ w, (r ^ 2 - ‖w - t‖ ^ 2) / ‖x - w‖ ^ 2 * g x ∂circleUnif z s =
    (r ^ 2 - ‖z - t‖ ^ 2) / ‖x - z‖ ^ 2 * g x
  rw [integral_mul_const]
  congr 1
  have hcl : closedBall z |s| ⊆ ball (t : ℂ) r := by
    intro w hw
    rw [mem_closedBall_iff_norm, abs_of_pos hs] at hw
    rw [mem_ball_iff_norm]
    have := norm_sub_le_of_sphere (t := t) (z := z) (w := w) (s := ‖w - z‖) rfl
    linarith
  have hharm := (harmonicOnNhd_density hx').mono hcl
  have hmeas : Measurable fun a : ℂ => (r ^ 2 - ‖a - t‖ ^ 2) / ‖x - a‖ ^ 2 :=
    (measurable_const.sub ((measurable_id.sub measurable_const).norm.pow_const 2)).div
      ((measurable_const.sub measurable_id).norm.pow_const 2)
  rw [circleUnif_eq_circMeas_k3, LQGDimension.Coupling.integral_circMeas_eq_circleAverage
    (f := fun a : ℂ => (r ^ 2 - ‖a - t‖ ^ 2) / ‖x - a‖ ^ 2) hmeas.aestronglyMeasurable]
  exact hharm.circleAverage_eq

theorem bind_foldedCircle_halfDiscPoisson {t r : ℝ} (hr : 0 < r) {z : ℂ} {s : ℝ} (hs : 0 < s)
    (hzs : ‖z - t‖ + s < r) :
    (foldedCircle z s).bind (halfDiscPoisson t r) = halfDiscPoisson t r z := by
  rw [← bind_circleUnif_halfDiscPoisson hr hs hzs]
  ext A hA
  have hPA : Measurable fun w => halfDiscPoisson t r w A :=
    (Measure.measurable_coe hA).comp (measurable_halfDiscPoisson t r)
  rw [Measure.bind_apply hA (measurable_halfDiscPoisson t r).aemeasurable,
    Measure.bind_apply hA (measurable_halfDiscPoisson t r).aemeasurable, foldedCircle,
    lintegral_map hPA measurable_foldH]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_sphere_circleUnif_k3 z hs] with w hw
  have hwb : w ∈ ball (t : ℂ) r := mem_ball_iff_norm.2
    (lt_of_le_of_lt (norm_sub_le_of_sphere (mem_sphere_iff_norm.1 hw)) hzs)
  unfold foldH
  split_ifs
  · rfl
  · rw [halfDiscPoisson_conj hr hwb]

/-! ## Mean-value property of the harmonic part -/

section Paths

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem harmH_conj (t r r' : ℝ) (ω : Ω) (z : ℂ) :
    harmH X t r r' ω (conj z) = harmH X t r r' ω z := by
  simp only [harmH, foldH_conj_k3]

/-- Stochastic Fubini for `kolY (harmIncr …)` against a finite measure carried by the closed
half-disc (as in `markov_decomposition`). -/
theorem integral_kolY_harmIncr_ae [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {t r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (hr'r : r' < r) (ν : Measure ℂ)
    [IsFiniteMeasure ν] (hν : ν (closedBall (t : ℂ) r' ∩ Hbar)ᶜ = 0) :
    (fun ω => ∫ z, kolY (harmIncr X t r r') z ω ∂ν) =ᵐ[P] fun ω =>
      X ω (ν.bind (halfDiscPoisson t r)) - X ω (ν Set.univ • halfDiscPoisson t r (t : ℂ)) := by
  set K := closedBall (t : ℂ) r' ∩ Hbar with hK_def
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have ht0 : ‖(t : ℂ) - t‖ ≤ r' := by rw [norm_self_sub_ofReal]; exact hr'.le
  have htK : (t : ℂ) ∈ K := ⟨mem_closedBall_iff_norm.2 ht0, by show (0 : ℝ) ≤ (t : ℂ).im; simp⟩
  have hKb : ∀ z ∈ K, ‖z - t‖ ≤ r' := fun z hz => mem_closedBall_iff_norm.1 hz.1
  obtain ⟨hYc, hY⟩ := kolY_harmIncr_spec (P := P) hX hr hr' hr'r
  exact stochFubini_kernel hX (measurable_halfDiscPoisson t r) hKc
    Set.inter_subset_right htK (R := |t| + r) (potC_ne_top r r')
    (fun z hz => by
      have := isProbabilityMeasure_halfDiscPoisson hr (mem_ball_of_le_k3 hr'r (hKb z hz))
      exact measure_univ)
    (fun z _ => halfDiscPoisson_ballH_compl hr z le_rfl)
    (fun z hz y => halfDiscPoisson_pot_le hr hr'r (hKb z hz) y)
    hYc (W := harmIncr X t r r')
    (fun z => show Measurable (harmIncr X t r r' z) from
      (hX.measurable_coord _).sub (hX.measurable_coord _)) hY
    (fun z hz => by
      funext ω
      simp only [harmIncr, retr_eq_self hz.2 (hKb z hz)])
    ν hν

/-- For a fixed circle inside the disc of radius `r'`, the harmonic part has the mean-value
property almost surely. -/
theorem ae_meanValue_harmH [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {t r r' : ℝ}
    (hr : 0 < r) (hr' : 0 < r') (hr'r : r' < r) {z : ℂ} {s : ℝ} (hs : 0 < s)
    (hzs : ‖z - t‖ + s < r') :
    ∀ᵐ ω ∂P, ∫ w, harmH X t r r' ω w ∂circleUnif z s = harmH X t r r' ω z := by
  set ν := foldedCircle z s with hνdef
  set K := closedBall (t : ℂ) r' ∩ Hbar with hK_def
  have hKm : MeasurableSet K := isClosed_closedBall.measurableSet.inter isClosed_Hbar.measurableSet
  have hνK : ∀ᵐ x ∂ν, x ∈ K := by
    rw [hνdef, foldedCircle]
    refine (ae_map_iff measurable_foldH.aemeasurable hKm).2 ?_
    filter_upwards [ae_mem_sphere_circleUnif_k3 z hs] with w hw
    refine ⟨mem_closedBall_iff_norm.2 ?_, CircleFubini.foldH_mem_Hbar' w⟩
    rw [norm_foldH_sub_ofReal]
    exact (norm_sub_le_of_sphere (mem_sphere_iff_norm.1 hw)).trans hzs.le
  have hν0 : ν Kᶜ = 0 := mem_ae_iff.1 hνK
  have hF := integral_kolY_harmIncr_ae hX hr hr' hr'r ν hν0
  have hbind : ν.bind (halfDiscPoisson t r) = halfDiscPoisson t r z :=
    bind_foldedCircle_halfDiscPoisson hr hs (by linarith)
  have hν1 : ν Set.univ • halfDiscPoisson t r (t : ℂ) = halfDiscPoisson t r (t : ℂ) := by
    rw [measure_univ, one_smul]
  obtain ⟨hYc, hY⟩ := kolY_harmIncr_spec (P := P) hX hr hr' hr'r
  have hkz := hY (foldH z) (CircleFubini.foldH_mem_Hbar' z)
  have hzb : z ∈ ball (t : ℂ) r := mem_ball_iff_norm.2 (by linarith)
  have hfz : ‖foldH z - t‖ ≤ r' := by rw [norm_foldH_sub_ofReal]; linarith
  have hPf : halfDiscPoisson t r (foldH z) = halfDiscPoisson t r z := by
    unfold foldH; split_ifs
    · rfl
    · exact halfDiscPoisson_conj hr hzb
  filter_upwards [hF, hkz] with ω h1 h2
  have hae : AEStronglyMeasurable (fun x => kolY (harmIncr X t r r') x ω) ν := by
    have hH : ∀ᵐ x ∂ν, x ∈ Hbar := hνK.mono fun x hx => hx.2
    rw [← Measure.restrict_eq_self_of_ae_mem hH]
    exact (hYc ω).aestronglyMeasurable isClosed_Hbar.measurableSet
  have e1 : ∫ w, harmH X t r r' ω w ∂circleUnif z s = ∫ x, kolY (harmIncr X t r r') x ω ∂ν := by
    rw [hνdef, foldedCircle, integral_map measurable_foldH.aemeasurable hae]
    rfl
  rw [e1, h1, hbind, hν1]
  show _ = kolY (harmIncr X t r r') (foldH z) ω
  rw [h2]
  simp only [harmIncr, retr_eq_self (CircleFubini.foldH_mem_Hbar' z) hfz, hPf]

theorem add_lt_of_closedBall_subset_ball {t : ℝ} {r' : ℝ} {z : ℂ} {s : ℝ} (hs : 0 < s)
    (h : closedBall z s ⊆ ball (t : ℂ) r') : ‖z - t‖ + s < r' := by
  by_cases hz : z - t = 0
  · have hp : z + s ∈ closedBall z s := by
      rw [mem_closedBall_iff_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs]
    have := mem_ball_iff_norm.1 (h hp)
    rw [show z + s - t = (z - t) + s by ring, hz, zero_add, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs] at this
    rw [hz, norm_zero, zero_add]; exact this
  · set n := ‖z - t‖
    have hn : 0 < n := norm_pos_iff.2 hz
    set p := z + ((s / n : ℝ) : ℂ) * (z - t)
    have hp : p ∈ closedBall z s := by
      rw [mem_closedBall_iff_norm, show p - z = ((s / n : ℝ) : ℂ) * (z - t) by simp [p],
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hs hn),
        div_mul_cancel₀ _ hn.ne']
    have := mem_ball_iff_norm.1 (h hp)
    rw [show p - t = ((1 + s / n : ℝ) : ℂ) * (z - t) by simp only [p]; push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), add_mul,
      one_mul, div_mul_cancel₀ _ hn.ne'] at this
    exact this

theorem continuous_circleUnif_average {u : ℂ → ℝ} (hu : Continuous u) :
    Continuous fun p : ℂ × ℝ => ∫ w, u w ∂circleUnif p.1 p.2 := by
  have e : (fun p : ℂ × ℝ => ∫ w, u w ∂circleUnif p.1 p.2) =
      fun p => (2 * π)⁻¹ * ∫ θ in Icc (-π) π, u (circleMap p.1 p.2 θ) := by
    funext p
    rw [integral_circleUnif_eq hu, integral_Icc_eq_integral_Ioo]
  rw [e]
  refine continuous_const.mul (continuous_parametric_integral_of_continuous ?_ isCompact_Icc)
  have hcm : Continuous fun q : (ℂ × ℝ) × ℝ => circleMap q.1.1 q.1.2 q.2 := by
    unfold circleMap; fun_prop
  exact hu.comp hcm

/-- Almost surely, the harmonic part has the mean-value property on the disc `ball t r'`. -/
theorem ae_meanValueOn_harmH [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {t r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (hr'r : r' < r) :
    ∀ᵐ ω ∂P, MeanValueOn (harmH X t r r' ω) (ball (t : ℂ) r') := by
  set Q : (ℚ × ℚ) × ℚ → ℂ × ℝ :=
    Prod.map (Complex.equivRealProdCLM.symm ∘ Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ))
      ((↑) : ℚ → ℝ) with hQ
  have hdense : DenseRange Q := by
    refine DenseRange.prodMap ?_ Rat.denseRange_cast
    exact (Complex.equivRealProdCLM.symm.surjective.denseRange).comp
      (Rat.denseRange_cast.prodMap Rat.denseRange_cast)
      Complex.equivRealProdCLM.symm.continuous
  set E : Set (ℂ × ℝ) := {p | 0 < p.2 ∧ ‖p.1 - t‖ + p.2 < r'} with hE
  have hEo : IsOpen E := (isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt (((continuous_fst.sub continuous_const).norm).add continuous_snd) continuous_const)
  have hall : ∀ᵐ ω ∂P, ∀ q, Q q ∈ E →
      ∫ w, harmH X t r r' ω w ∂circleUnif (Q q).1 (Q q).2 = harmH X t r r' ω (Q q).1 := by
    rw [ae_all_iff]
    intro q
    by_cases hq : Q q ∈ E
    · filter_upwards [ae_meanValue_harmH hX hr hr' hr'r hq.1 hq.2] with ω h _ using h
    · exact ae_of_all _ fun ω h => absurd h hq
  filter_upwards [hall] with ω hω
  have hu := continuous_harmH (P := P) (t := t) hX hr hr' hr'r ω
  have heq : Set.EqOn (fun p : ℂ × ℝ => ∫ w, harmH X t r r' ω w ∂circleUnif p.1 p.2)
      (fun p => harmH X t r r' ω p.1) E := by
    refine Set.EqOn.of_subset_closure (s := E ∩ Set.range Q) ?_
      (continuous_circleUnif_average hu).continuousOn (hu.comp continuous_fst).continuousOn
      Set.inter_subset_left (hdense.open_subset_closure_inter hEo)
    rintro p ⟨hpE, q, rfl⟩
    exact hω q hpE
  intro z _ s hs hsub
  exact heq (x := (z, s)) ⟨hs, add_lt_of_closedBall_subset_ball hs hsub⟩

/-- **Harmonic sample paths.** Almost surely, `harmH X t r r' ω` is harmonic on `ball t r'`;
it is even across `ℝ` for every `ω` (`harmH_conj`). -/
theorem ae_harmonicOnNhd_harmH [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {t r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (hr'r : r' < r) :
    ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (harmH X t r r' ω) (ball (t : ℂ) r') := by
  filter_upwards [ae_meanValueOn_harmH hX hr hr' hr'r] with ω h
  exact harmonicOnNhd_of_meanValue (continuous_harmH (P := P) (t := t) hX hr hr' hr'r ω)
    isOpen_ball h

end Paths

end K3

end QuantumZipper
