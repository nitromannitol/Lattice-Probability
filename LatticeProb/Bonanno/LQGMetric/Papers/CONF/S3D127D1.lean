/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127D1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127B1
import LatticeProb.Bonanno.LQGMetric.Field.MarkovWeyl3
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm11.FrozenLocalDynkin
import Mathlib.Analysis.Complex.Harmonic.Analytic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D127 N4b: the Green potential of a smooth density is smooth, with `Δ u = −2π ρ` (BP Prop. 1.18)

Packet P-127D of DEC-127 (§3, item N4(b), with the orchestrator's addendum: `ρ` smooth with
compact support in `U`, of arbitrary sign). For a bounded open `U` and
`u x = ∫ y, G_U(x, y) ρ(y) dy` (`G_U = KilledHeat.killedGreen U = π ∫₀^∞ p_U`), given N1
(`hN1`, the form of S3D127B1) and the continuity of `u` on `U` (`hcont`, packet P-127C):

* `contDiffOn_greenPot : ContDiffOn ℝ ∞ u U`;
* `laplacian_greenPot : ∀ x ∈ U, Δ u x = −(2π) ρ x`.

Proof (Berestycki–Powell, *Gaussian free field and Liouville quantum gravity*, arXiv:2404.16642,
§1.5, Prop. 1.18 `Δ_y G_D(x, ·) = −δ_x` read in the sense of distributions, and Weyl's lemma):
* by N1 and the symmetry of the killed-Green form (`killedGreenForm_eq_inner`, Chapman–Kolmogorov),
  `∫ (−Δf) u = 2π ∫ ρ f` for `f ∈ C_c^∞(U)`: `u` solves `−Δu = 2πρ` weakly;
* the logarithmic potential `L = log‖·‖ ⋆ ρ` (`MarkovWeyl2.logConv`, smooth with `ΔL = 2πρ`,
  `MarkovWeyl2.laplacian_logConv`) is a particular solution, so `w = u + L` is weakly harmonic;
* Weyl's lemma (`MarkovWeyl3.exists_harmonic_of_laplacian_eq_zero`, Hörmander ALPDO I Thm 4.4.1)
  gives a harmonic `g` on `U` with `w = g` a.e. on `U`, hence everywhere on `U` by continuity;
* harmonic functions are real analytic (mathlib `HarmonicAt.analyticAt`), so `u = g − L` is smooth
  on `U` and `Δu = 0 − 2πρ`.
The Green identity `∫ L Δf = ∫ f ΔL` (`integral_mul_laplacian_comm`) is the cutoff argument of
`HarmLoc.integral_mul_laplacian_of_harmonic` (Field/HarmLocA) with `ΔH = 0` replaced by `ΔL`.
-/

noncomputable section

open MeasureTheory Filter Set Topology InnerProductSpace
open scoped Real Laplacian ContDiff

namespace LQGMetric.CONF.ZBM

open KilledHeat QuantumZipper QuantumZipper.K3

variable {U : Set ℂ} {c : ℂ} {R : ℝ}

/-- **Green's second identity** `∫ L Δf = ∫ f ΔL` for `L ∈ C²(ℂ)` and `f ∈ C²_c` (adapted from
`HarmLoc.integral_mul_laplacian_of_harmonic`) -/
theorem integral_mul_laplacian_comm {L : ℂ → ℝ} (hL : ContDiff ℝ 2 L) {f : ℂ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∫ x, L x * Δ f x = ∫ x, f x * Δ L x := by
  obtain ⟨χ, hχd, -, hχc, -, hχ1⟩ :=
    FrozenMart.exists_cutoff_of_isCompact hfc isOpen_univ (subset_univ _)
  set u : ℂ → ℝ := fun x => χ x * L x with hu_def
  have hu : ContDiff ℝ 2 u := (hχd.of_le (by norm_num)).mul hL
  have huc : HasCompactSupport u := hχc.mul_right
  have e1 : ∫ x, L x * Δ f x = ∫ x, u x * Δ f x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport f
    · have : χ x = 1 := (hχ1 x hx).self_of_nhds
      simp [hu_def, this]
    · simp [laplacian_eq_zero_of_notMem_tsupport hx]
  have e2 : ∫ x, u x * Δ f x = -∫ x, gradInner u f x := by
    rw [integral_gradInner_eq_neg_integral_mul_laplacian (hu.of_le (by norm_num)) hf hfc,
      neg_neg]
  have e3 : ∫ x, gradInner u f x = -∫ x, f x * Δ u x := by
    simp_rw [gradInner_comm_k3 u f]
    exact integral_gradInner_eq_neg_integral_mul_laplacian (hf.of_le (by norm_num)) hu huc
  have e4 : ∫ x, f x * Δ u x = ∫ x, f x * Δ L x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport f
    · have hev : u =ᶠ[𝓝 x] L := by
        filter_upwards [hχ1 x hx] with y hy
        simp [hu_def, hy]
      show f x * Δ u x = f x * Δ L x
      rw [(laplacian_congr_nhds hev).eq_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [e1, e2, e3, e4, neg_neg]

/-- symmetry of the killed-Green form -/
theorem killedGreenForm_comm (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    {a b : ℂ → ℝ} (ha : Measurable a) (hb : Measurable b) {C : ℝ} (haC : ∀ z, |a z| ≤ C)
    (hbC : ∀ z, |b z| ≤ C) (hai : Integrable a) (hbi : Integrable b) :
    killedGreenForm U a b = killedGreenForm U b a := by
  rw [killedGreenForm_eq_inner hU hR hUR ha hb haC hbC hai hbi,
    killedGreenForm_eq_inner hU hR hUR hb ha hbC haC hbi hai, real_inner_comm]

/-- the Green potential `u x = ∫ G_U(x, y) ρ(y) dy` -/
def greenPot (U : Set ℂ) (ρ : ℂ → ℝ) (x : ℂ) : ℝ := ∫ y, killedGreen U x y * ρ y

/-- **`u` solves `−Δu = 2πρ` weakly** (N1 + symmetry): `∫ (−Δf) u = 2π ∫ ρ f` -/
theorem integral_negLap_mul_greenPot (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    (hN1 : ∀ g ∈ QuantumZipper.zeroSpace U, ∀ y ∈ U,
      ∫ x, killedGreen U y x * Δ g x = -(2 * π) * g y)
    {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    {f : ℂ → ℝ} (hf : f ∈ QuantumZipper.zeroSpace U) :
    ∫ y, -Δ f y * greenPot U ρ y = 2 * π * ∫ y, ρ y * f y := by
  obtain ⟨am, ⟨C', hC'⟩, ai, -⟩ := negLap_props hf
  have hρcont : Continuous ρ := hρ.continuous
  obtain ⟨C, hC⟩ := hρcont.norm.bddAbove_range_of_hasCompactSupport hρc.norm
  have hCb : ∀ z, |ρ z| ≤ C := fun z => by simpa [Real.norm_eq_abs] using hC ⟨z, rfl⟩
  have hρi : Integrable ρ := hρcont.integrable_of_hasCompactSupport hρc
  have hρ0 : ∀ z, z ∉ U → ρ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (hρU h)
  have h1 := killedGreenForm_eq_iter hU hR hUR am hρcont.measurable hCb ai hρi
  rw [killedGreenForm_comm hU hR hUR am hρcont.measurable (C := max C C')
    (fun z => (hC' z).trans (le_max_right _ _)) (fun z => (hCb z).trans (le_max_left _ _)) ai hρi,
    killedGreenForm_negLap_right hU hR hUR hN1 hρcont.measurable hρi hρ0 hf] at h1
  rw [h1]
  rfl

/-- **Weyl step.** `u + log‖·‖ ⋆ ρ` coincides on `U` with a harmonic function -/
theorem exists_harmonic_greenPot_add (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    (hN1 : ∀ g ∈ QuantumZipper.zeroSpace U, ∀ y ∈ U,
      ∫ x, killedGreen U y x * Δ g x = -(2 * π) * g y)
    {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (hcont : ContinuousOn (greenPot U ρ) U) :
    ∃ g : ℂ → ℝ, HarmonicOnNhd g U ∧
      EqOn (fun x => greenPot U ρ x + MarkovWeyl2.logConv ρ x) g U := by
  set V : TopologicalSpace.Opens ℂ := ⟨U, hU⟩
  set L := MarkovWeyl2.logConv ρ with hLdef
  have hLs : ContDiff ℝ ∞ L := MarkovWeyl2.contDiff_logConv hρ hρc
  have hui : LocallyIntegrableOn (greenPot U ρ) (V : Set ℂ) volume :=
    hcont.locallyIntegrableOn hU.measurableSet
  have hLi : LocallyIntegrableOn L (V : Set ℂ) volume :=
    hLs.continuous.continuousOn.locallyIntegrableOn hU.measurableSet
  set T : DistOn V := Distribution.ofFun V (greenPot U ρ + L) volume ⊤ with hTdef
  have hT : ∀ f : MarkovZB.zsSub (V : Set ℂ), T (MarkovHarm.cmTestOn f) = 0 := by
    intro f
    have hf : f.1 ∈ QuantumZipper.zeroSpace U := f.2
    rw [hTdef, Distribution.ofFun_add hui hLi, add_apply,
      Distribution.ofFun_apply hui, Distribution.ofFun_apply hLi]
    simp only [MarkovHarm.cmTestOn_apply, cmTest_apply, smul_eq_mul]
    have hz : (⇑(MarkovZB.zsTest f.2) : ℂ → ℝ) = f.1 := rfl
    rw [hz]
    have h1 := integral_negLap_mul_greenPot hU hR hUR hN1 hρ hρc hρU hf
    have h2 := integral_mul_laplacian_comm (hLs.of_le (by simp)) (hf.1.of_le (by simp)) hf.2.1
    simp_rw [hLdef, MarkovWeyl2.laplacian_logConv hρ hρc] at h2
    have e1 : ∫ x, -(2 * π)⁻¹ * Δ f.1 x * greenPot U ρ x =
        (2 * π)⁻¹ * ∫ y, -Δ f.1 y * greenPot U ρ y := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    have e2 : ∫ x, -(2 * π)⁻¹ * Δ f.1 x * MarkovWeyl2.logConv ρ x =
        -(2 * π)⁻¹ * ∫ x, MarkovWeyl2.logConv ρ x * Δ f.1 x := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    have e3 : ∫ x, f.1 x * (2 * π * ρ x) = 2 * π * ∫ y, ρ y * f.1 y := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [e1, e2, h1, h2, e3]
    have hπ : (2 * π) ≠ 0 := by positivity
    field_simp
    ring
  obtain ⟨g, hg, hgT⟩ := MarkovWeyl3.exists_harmonic_of_laplacian_eq_zero T hT
  have hgc : ContinuousOn g U := hg.contDiffOn.continuousOn
  have hgi : LocallyIntegrableOn g (V : Set ℂ) volume := hgc.locallyIntegrableOn hU.measurableSet
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (f := fun x => (greenPot U ρ x + L x) - g x) ((hui.add hLi).sub hgi) (by
      intro ψ hψ hψc hψU
      set φ : TestOn V := ⟨ψ, hψ, hψc, hψU⟩
      have hφ := hgT φ
      rw [hTdef, Distribution.ofFun_apply (hui.add hLi)] at hφ
      have i1 := φ.integrable_smul (hui.add hLi)
      have i2 := φ.integrable_smul hgi
      have h3 : ∫ x, φ x • g x = ∫ x, g x * φ x :=
        integral_congr_ae (Eventually.of_forall fun x => by
          simp only [smul_eq_mul]; exact mul_comm _ _)
      refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans
        ((integral_sub i1 i2).trans (sub_eq_zero.2 (hφ.trans h3.symm)))
      simp only [Pi.add_apply, smul_eq_mul]
      change ψ x * _ = ψ x * _ - ψ x * _
      ring)
  refine ⟨g, hg, ?_⟩
  refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hU (hcont.add hLs.continuous.continuousOn) hgc
  · exact (ae_restrict_iff' hU.measurableSet).2 (hae.mono fun x hx hxU => sub_eq_zero.1 (hx hxU))

lemma nonneg_of_mem_ball (hUR : U ⊆ Metric.ball c R) {x : ℂ} (hx : x ∈ U) : 0 ≤ R :=
  le_of_lt (lt_of_le_of_lt dist_nonneg (Metric.mem_ball.1 (hUR hx)))

/-- the local representation `u = g − log‖·‖ ⋆ ρ` near a point of `U` -/
lemma greenPot_eventuallyEq (hU : IsOpen U) (hUR : U ⊆ Metric.ball c R)
    (hN1 : ∀ g ∈ QuantumZipper.zeroSpace U, ∀ y ∈ U,
      ∫ x, killedGreen U y x * Δ g x = -(2 * π) * g y)
    {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (hcont : ContinuousOn (fun x => ∫ y, killedGreen U x y * ρ y) U) {x : ℂ} (hx : x ∈ U) :
    ∃ g : ℂ → ℝ, HarmonicAt g x ∧
      (fun x => ∫ y, killedGreen U x y * ρ y) =ᶠ[𝓝 x] g - MarkovWeyl2.logConv ρ := by
  obtain ⟨g, hg, heq⟩ := exists_harmonic_greenPot_add hU (nonneg_of_mem_ball hUR hx) hUR hN1
    hρ hρc hρU hcont
  refine ⟨g, hg x hx, ?_⟩
  filter_upwards [hU.mem_nhds hx] with y hy
  have := heq hy
  simp only [greenPot] at this
  simp only [Pi.sub_apply]
  linarith

/-- **D127 N4b, smoothness**: the Green potential of a smooth density with compact support in
`U` is smooth on `U` -/
theorem contDiffOn_greenPot (hU : IsOpen U) (hUR : U ⊆ Metric.ball c R)
    (hN1 : ∀ g ∈ QuantumZipper.zeroSpace U, ∀ y ∈ U,
      ∫ x, killedGreen U y x * Δ g x = -(2 * π) * g y)
    {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (hcont : ContinuousOn (fun x => ∫ y, killedGreen U x y * ρ y) U) :
    ContDiffOn ℝ ∞ (fun x => ∫ y, killedGreen U x y * ρ y) U := by
  intro x hx
  obtain ⟨g, hg, hev⟩ := greenPot_eventuallyEq hU hUR hN1 hρ hρc hρU hcont hx
  exact (((HarmonicAt.analyticAt hg).contDiffAt.sub (MarkovWeyl2.contDiff_logConv hρ hρc).contDiffAt)
    |>.congr_of_eventuallyEq hev).contDiffWithinAt

/-- **D127 N4b, the equation** (BP Prop. 1.18): `Δu = −2πρ` on `U` -/
theorem laplacian_greenPot (hU : IsOpen U) (hUR : U ⊆ Metric.ball c R)
    (hN1 : ∀ g ∈ QuantumZipper.zeroSpace U, ∀ y ∈ U,
      ∫ x, killedGreen U y x * Δ g x = -(2 * π) * g y)
    {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (hcont : ContinuousOn (fun x => ∫ y, killedGreen U x y * ρ y) U) :
    ∀ x ∈ U, Δ (fun x => ∫ y, killedGreen U x y * ρ y) x = -(2 * π) * ρ x := by
  intro x hx
  obtain ⟨g, hg, hev⟩ := greenPot_eventuallyEq hU hUR hN1 hρ hρc hρU hcont hx
  rw [(laplacian_congr_nhds hev).eq_of_nhds,
    ContDiffAt.laplacian_sub ((HarmonicAt.analyticAt hg).contDiffAt)
      ((MarkovWeyl2.contDiff_logConv hρ hρc).contDiffAt.of_le (by simp)),
    hg.2.self_of_nhds, MarkovWeyl2.laplacian_logConv hρ hρc]
  simp only [Pi.zero_apply]
  ring

end LQGMetric.CONF.ZBM
