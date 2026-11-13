/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.LemmaA3FieldCM at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.FieldData
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.Energy
import LatticeProb.Bonanno.LQGMetric.Papers.MQ.Lem41
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.IG.GFF.AbsContCore
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.ZBCMLaw

/-!
# The pointwise change of measure between two harmonic parts

[18], proof of Lemma A.5: for two realizations `𝔥, 𝔥̃` of the harmonic
part (with the same centre value), the laws of `(𝔥 + h̊)|_{B_δ}` and `(𝔥̃ + h̊)|_{B_δ}` are compared through the
Cameron–Martin shift `g_δ = φ_δ (𝔥 − 𝔥̃)`, with density `exp((h̊, g_δ)_∇ − ½ (g_δ, g_δ)_∇)`. Here the comparison is made
for each fixed pair `(ω, ω')` of sample points (the coupling of the paper is the product `P ⊗ P`), with the energy
`(g_δ, g_δ)_∇` bounded by the measurable quantity
`MfG(ω, ω') = energyConst δ^{-2} ∫_{B̄_{5δ}(0)} (ĝ_ω − ĝ_{ω'})²`, `ĝ_ω(y) = G_ω(ψ_y − ψ_0)/∫ψ = 𝔥_ω(y) − 𝔥_ω(0)`.

* `GMSAppA.DiskMarkov.pvG`, `GMSAppA.DiskMarkov.MfG` — the pairing representation and the energy bound.
* `GMSAppA.DiskMarkov.cm_shift` — the shift `T`, its density `ρ` and the moments of `ρ`.
* `GMSAppA.DiskMarkov.cm_pointwise` — the hypothesis `hCM` of `lemmaA3_product`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric InnerProductSpace
open LQGMetric LQGMetric.GM LQGMetric.Blueprint QuantumZipper
open MatedCRTHarmonic.MoTPort.IG.GFFAbsCont MatedCRTHarmonic.MoTPort LQGMetric.MarkovZB
open scoped ENNReal

namespace MatedCRTHarmonic.GMSAppA

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

namespace DiskMarkov

/-- `ĝ_ω(y) = G_ω(ψ_y − ψ_0)/∫ψ` -/
def pvG (M : DiskMarkov P h) (p : Ω × ℂ) : ℝ := M.G p.1 (radDiff quarter_pos.le p.2 0).1 / massQ

lemma measurable_pvG (M : DiskMarkov P h) (hh : Measurable h) : Measurable M.pvG := by
  have hG := M.measurable_G hh
  have e : M.pvG = fun p : Ω × ℂ => (M.G p.1 (radBump (1 / 4) quarter_pos.le p.2) -
      M.G p.1 (radBump (1 / 4) quarter_pos.le 0)) / massQ := by
    funext p
    simp only [pvG]
    congr 1
    show M.G p.1 (radBump (1 / 4) quarter_pos.le p.2 - radBump (1 / 4) quarter_pos.le 0) = _
    rw [map_sub]
  rw [e]
  exact (((measurable_apply_radBump (1 / 4) quarter_pos.le).comp
    ((hG.comp measurable_fst).prodMk measurable_snd)).sub
    (((measurable_distOn_apply _).comp hG).comp measurable_fst)).div_const _

/-- the energy bound `energyConst δ^{-2} ∫_{B̄_{5δ}} (ĝ_ω − ĝ_{ω'})²` -/
def MfG (M : DiskMarkov P h) (δ : ℝ) (x : Ω × Ω) : ℝ :=
  energyConst / δ ^ 2 * ∫ y in closedBall (0 : ℂ) (5 * δ), (M.pvG (x.1, y) - M.pvG (x.2, y)) ^ 2
lemma measurable_MfG (M : DiskMarkov P h) (hh : Measurable h) (δ : ℝ) : Measurable (M.MfG δ) := by
  have hp := M.measurable_pvG hh
  have hF : Measurable fun q : (Ω × Ω) × ℂ => (M.pvG (q.1.1, q.2) - M.pvG (q.1.2, q.2)) ^ 2 :=
    ((hp.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).sub
      (hp.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).pow_const 2
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (closedBall 0 (5 * δ)))
    ).measurable.const_mul _

/-- the measurable map `(e, c, z) ↦ (e + z + c)|_{B_δ}` -/
lemma measurable_fieldOf (δ : ℝ) :
    Measurable fun x : DistOn (ballO 0 1) × ℝ × DistOn (ballO 0 1) =>
      resOn (ballO 0 δ) (ballO 0 1) (addConstOn (ballO 0 1) (x.1 + x.2.2) x.2.1) :=
  (measurable_resOn _ _).comp ((measurable_addConstOn _).comp
    ((measurable_fst.comp measurable_snd).prodMk ((measurable_add_distOn _).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))))

/-- a.s. the harmonic representative of `G` has centre value `h_1(0)` -/
lemma ae_good [IsProbabilityMeasure P] (M : DiskMarkov P h) (hh : IsWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∃ g, HarmRep (M.G ω) g ∧ g 0 = cAvg h ω := by
  filter_upwards [M.harm, M.center hh] with ω ⟨g, hg⟩ hc
  exact ⟨g, hg, hc g hg⟩

/-- `E_ω` is represented on `𝔻` by `ĝ = g − g(0)`. -/
lemma Ed_apply {M : DiskMarkov P h} {ω : Ω} {g : ℂ → ℝ} (hg : HarmRep (M.G ω) g)
    (hc : g 0 = cAvg h ω) (φ : TestOn (ballO 0 1)) :
    M.Ed ω φ = ∫ x, (g x - g 0) * φ x := by
  simp only [Ed, LQGMetric.DG.L22T.restrictTo_addConst, hg.2, hc]
  have hgi : Integrable fun x => g x * φ x := by
    have := integrable_mul_test (contDiffOn_of_harmonicOnNhd hg.1 (n := 0)) φ
    exact this
  have hφi : Integrable fun x => φ x :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  rw [show (fun x => (g x - cAvg h ω) * φ x) = fun x => g x * φ x - cAvg h ω * φ x by
    funext x; ring, integral_sub hgi (hφi.const_mul _), integral_const_mul]
  ring

/-- **The pointwise Cameron–Martin shift**: for `(P ⊗ P)`-a.e. `(ω, ω')` there are a deterministic shift `T` and a
density `ρ > 0` on `𝒟'(𝔻)`, with the moments of a Gaussian tilt of variance `V ≤ MfG δ (ω, ω')`, such that the law of
`Z + T` is `ρ` times the law of `Z`, and `(E_ω + z + c)|_{B_δ} = (E_{ω'} + (z + T) + c)|_{B_δ}` for all `z`, `c`. -/
theorem cm_shift [IsProbabilityMeasure P] (M : DiskMarkov P h) (hh : IsWholePlaneGFF h P)
    {δ : ℝ} (hδ : 0 < δ) (hδ10 : δ < 1 / 10) :
    ∀ᵐ x ∂(P.prod P), ∃ T : DistOn (ballO 0 1), ∃ ρ : DistOn (ballO 0 1) → ℝ, Measurable ρ ∧
      (∀ z, 0 < ρ z) ∧ ∃ V : ℝ, 0 ≤ V ∧ V ≤ M.MfG δ x ∧
        (∀ s : ℝ, ∫⁻ z, ENNReal.ofReal (ρ z) ^ s ∂(P.map M.Zd) =
          ENNReal.ofReal (Real.exp (s * (s - 1) * V / 2))) ∧
        (∀ Ψ : DistOn (ballO 0 1) → ℝ≥0∞, Measurable Ψ →
          ∫⁻ z, Ψ (z + T) ∂(P.map M.Zd) = ∫⁻ z, Ψ z * ENNReal.ofReal (ρ z) ∂(P.map M.Zd)) ∧
        ∀ (z : DistOn (ballO 0 1)) (c : ℝ),
          resOn (ballO 0 δ) (ballO 0 1) (addConstOn (ballO 0 1) (M.Ed x.1 + z) c) =
            resOn (ballO 0 δ) (ballO 0 1) (addConstOn (ballO 0 1) (M.Ed x.2 + (z + T)) c) := by
  have hδ5 : δ < 1 / 5 := by linarith
  have hgood := M.ae_good hh
  have h1 : ∀ᵐ x ∂(P.prod P), ∃ g, HarmRep (M.G x.1) g ∧ g 0 = cAvg h x.1 :=
    Measure.quasiMeasurePreserving_fst.ae hgood
  have h2 : ∀ᵐ x ∂(P.prod P), ∃ g, HarmRep (M.G x.2) g ∧ g 0 = cAvg h x.2 :=
    Measure.quasiMeasurePreserving_snd.ae hgood
  filter_upwards [h1, h2] with x ⟨g₁, hg₁, hc₁⟩ ⟨g₂, hg₂, hc₂⟩
  set D : ℂ → ℝ := fun y => (g₁ y - g₁ 0) - (g₂ y - g₂ 0) with hDdef
  have hD : HarmonicOnNhd D (ball (0 : ℂ) 1) :=
    (hg₁.1.sub (harmonicOnNhd_const _)).sub (hg₂.1.sub (harmonicOnNhd_const _))
  set F : ℂ → ℝ := fun y => cutδ δ y * D y with hFdef
  have hF : F ∈ zeroSpace (ball (0 : ℂ) 1) := mem_zeroSpace_cut_mul hD hδ (by linarith)
  set f : zsSub ((ballO 0 1 : TopologicalSpace.Opens ℂ) : Set ℂ) := ⟨F, hF⟩
  set T : DistOn (ballO 0 1) := ofFunOn (ballO 0 1) F
  have hT : ∀ φ : TestOn (ballO 0 1), T φ = ∫ x, f.1 x * φ x := by
    intro φ
    rw [GFFBdry.ofFunOn_apply (hF.1.continuous.locallyIntegrable.locallyIntegrableOn _)]
    simp only [mul_comm]
    rfl
  have hadm : ZBAdmissible (ballO 0 1) := zbAdmissible_of_isBounded isBounded_ball
  have hne : ((ballO 0 1 : TopologicalSpace.Opens ℂ) : Set ℂ).Nonempty :=
    ⟨0, by show (0 : ℂ) ∈ ball (0 : ℂ) 1; simp⟩
  have hkey : ∀ ψ : TestOn (ballO 0 δ),
      M.Ed x.1 (GM.testIncl (ballO 0 δ) (ballO 0 1) ψ) =
        M.Ed x.2 (GM.testIncl (ballO 0 δ) (ballO 0 1) ψ) +
          T (GM.testIncl (ballO 0 δ) (ballO 0 1) ψ) := by
    intro ψ
    set φ' := GM.testIncl (ballO 0 δ) (ballO 0 1) ψ with hφ'
    have hi : ∀ g : ℂ → ℝ, HarmonicOnNhd g (ball (0 : ℂ) 1) →
        Integrable fun x => g x * φ' x := fun g hg =>
      integrable_mul_test (contDiffOn_of_harmonicOnNhd hg (n := 0)) φ'
    have hFD : ∫ x, f.1 x * φ' x = ∫ x, D x * φ' x := by
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      show cutδ δ y * D y * φ' y = D y * φ' y
      by_cases hy : φ' y = 0
      · rw [hy]; ring
      · have hyB : y ∈ ball (0 : ℂ) δ := by
          have : y ∈ tsupport (ψ : ℂ → ℝ) := by
            rw [← GM.coe_testIncl (show ballO 0 δ ≤ ballO 0 1 from fun z hz => by
              rw [ballO, TopologicalSpace.Opens.mem_mk, mem_ball, dist_zero_right] at hz ⊢
              show ‖z‖ < 1; linarith) ψ]
            exact subset_closure hy
          exact ψ.tsupport_subset this
        rw [mem_ball, dist_zero_right] at hyB
        rw [cutδ_eq_one hδ hyB.le, one_mul]
    have hA : Integrable fun x => (g₁ x - g₁ 0) * φ' x :=
      hi (fun x => g₁ x - g₁ 0) (hg₁.1.sub (harmonicOnNhd_const _))
    have hB : Integrable fun x => (g₂ x - g₂ 0) * φ' x :=
      hi (fun x => g₂ x - g₂ 0) (hg₂.1.sub (harmonicOnNhd_const _))
    have hsplit : ∫ x, D x * φ' x =
        (∫ x, (g₁ x - g₁ 0) * φ' x) - ∫ x, (g₂ x - g₂ 0) * φ' x := by
      calc ∫ x, D x * φ' x = ∫ x, ((g₁ x - g₁ 0) * φ' x - (g₂ x - g₂ 0) * φ' x) := by
            congr 1; funext y; simp only [hDdef]; ring
        _ = _ := integral_sub hA hB
    rw [Ed_apply hg₁ hc₁, Ed_apply hg₂ hc₂, hT, hFD, hsplit]
    ring
  have hshift : ∀ (z : DistOn (ballO 0 1)) (c : ℝ),
      resOn (ballO 0 δ) (ballO 0 1) (addConstOn (ballO 0 1) (M.Ed x.1 + z) c) =
        resOn (ballO 0 δ) (ballO 0 1) (addConstOn (ballO 0 1) (M.Ed x.2 + (z + T)) c) := by
    intro z c
    ext ψ
    rw [resOn_apply, resOn_apply, addConstOn_apply, addConstOn_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      hkey ψ]
    ring
  refine ⟨T, zbDensity f, measurable_zbDensity f, fun z => Real.exp_pos _,
    dirichletEnergyOn (ball (0 : ℂ) 1) F, ?_, ?_, fun s => zbcm_moment hadm M.zb f s,
    fun Ψ hΨ => zbcm_lintegral (P := P) hadm hne M.zb f hT hΨ, hshift⟩
  · unfold dirichletEnergyOn
    exact mul_nonneg (by positivity) (integral_nonneg fun _ => by positivity)
  · refine (energy_cut_le hD hδ hδ5).trans (le_of_eq ?_)
    simp only [MfG]
    congr 1
    refine setIntegral_congr_fun measurableSet_closedBall fun y hy => ?_
    have hy' : ‖y‖ < 3 / 4 := by
      rw [mem_closedBall, dist_zero_right] at hy; linarith
    simp only [hDdef, pvG]
    rw [← harm_sub_eq_pairing hg₁.1 hg₁.2 hy', ← harm_sub_eq_pairing hg₂.1 hg₂.2 hy']

/-- **The pointwise Cameron–Martin property** (the hypothesis `hCM` of `lemmaA3_product`): for `(P ⊗ P)`-a.e.
`(ω, ω')` there is a density `ρ` on `𝒟'(𝔻)` with the moments of a Gaussian tilt of variance `V ≤ MfG δ (ω, ω')` such
that, for every measurable functional `Fn` of the field on `B_δ` and the centre value `c`,
`E_Z[Fn((E_ω + Z + c)|_{B_δ}, c)] = E_Z[Fn((E_{ω'} + Z + c)|_{B_δ}, c) ρ(Z)]`. -/
theorem cm_pointwise [IsProbabilityMeasure P] (M : DiskMarkov P h) (hh : IsWholePlaneGFF h P)
    {δ : ℝ} (hδ : 0 < δ) (hδ10 : δ < 1 / 10) :
    ∀ᵐ x ∂(P.prod P), ∃ ρ : DistOn (ballO 0 1) → ℝ, Measurable ρ ∧ (∀ z, 0 ≤ ρ z) ∧
      ∃ V : ℝ, 0 ≤ V ∧ V ≤ M.MfG δ x ∧
        (∀ s : ℝ, ∫⁻ z, ENNReal.ofReal (ρ z) ^ s ∂(P.map M.Zd) =
          ENNReal.ofReal (Real.exp (s * (s - 1) * V / 2))) ∧
        ∀ (Fn : DistOn (ballO 0 δ) × ℝ → ℝ), Measurable Fn → ∀ c : ℝ,
          ∫⁻ z, ENNReal.ofReal (Fn (resOn (ballO 0 δ) (ballO 0 1)
              (addConstOn (ballO 0 1) (M.Ed x.1 + z) c), c)) ∂(P.map M.Zd) =
            ∫⁻ z, ENNReal.ofReal (Fn (resOn (ballO 0 δ) (ballO 0 1)
              (addConstOn (ballO 0 1) (M.Ed x.2 + z) c), c)) * ENNReal.ofReal (ρ z)
                ∂(P.map M.Zd) := by
  filter_upwards [M.cm_shift hh hδ hδ10] with x ⟨T, ρ, hρm, hρ0, V, hV0, hVM, hmom, hcm, hshift⟩
  refine ⟨ρ, hρm, fun z => (hρ0 z).le, V, hV0, hVM, hmom, fun Fn hFn c => ?_⟩
  have hΨ0 : Measurable fun z : DistOn (ballO 0 1) =>
      resOn (ballO 0 δ) (ballO 0 1) (addConstOn (ballO 0 1) (M.Ed x.2 + z) c) := by
    refine measurable_distOn_iff.2 fun φ => ?_
    simp only [resOn_apply, addConstOn_apply, ContinuousLinearMap.add_apply]
    exact ((measurable_distOn_apply _).const_add _).add_const _
  have hΨ : Measurable fun z : DistOn (ballO 0 1) => ENNReal.ofReal (Fn (resOn (ballO 0 δ)
      (ballO 0 1) (addConstOn (ballO 0 1) (M.Ed x.2 + z) c), c)) :=
    ENNReal.measurable_ofReal.comp (hFn.comp (hΨ0.prodMk measurable_const))
  refine Eq.trans ?_ (hcm _ hΨ)
  refine lintegral_congr fun z => ?_
  rw [hshift z c]

end DiskMarkov

end MatedCRTHarmonic.GMSAppA
