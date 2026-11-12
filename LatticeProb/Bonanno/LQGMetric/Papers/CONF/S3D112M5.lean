/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D112M5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112M4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `CONFHarmPartLink` (CONF Lemma 3.3, Step 1; D110 P3)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381, C:1187–1190: "we can assume
… `h` is normalized so that `h_{r₀}(z₀) = 0` … By the Markov property … `h|_U = h̊^U + 𝔥^U`".
The Blueprint harmonic part `harmPart P h U` (conditioning on `σ(h|_{ℂ∖U})` modulo constants,
`Blueprint.IsHarmPart`, D110) is, on `U`, the harmonic part `𝔥` of the Markov decomposition of
`h − h_ρ(w)` plus the constant `h_ρ(w)`.

Proof: the conditional-expectation computation of `HarmExist.exists_isHarmPartRaw_of_normAt`
(Field/HarmExistA) for the Markov version `X = (h − h_ρ(w)) − G`, with the conditioning
σ-algebra `σ(h|_{ℂ∖U} mod constants)`: it is contained in `recSigma` (so `X` is independent of
it), and `G(χ)` is a.e. measurable for it (`aestronglyMeasurable_fieldSigmaClosed0_of_recSigma`,
S3D112M4). Then `HarmExist.isHarmPart_ae_eq` (a.s. uniqueness of versions) and the mean value
property (`HarmLoc.integral_mul_unitBump`) identify `harmPart` with `𝔥 + h_ρ(w)` on `U`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint HarmExist

/-- two functions harmonic on `U` with the same pairings against `𝓓(U)` agree on `U` -/
lemma eqOn_of_harmonic_pairing {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℝ}
    (hf : InnerProductSpace.HarmonicOnNhd f U) (hg : InnerProductSpace.HarmonicOnNhd g U)
    (hfg : ∀ φ : TestOn (toOpens U hU), ∫ x, f x * φ x = ∫ x, g x * φ x) :
    ∀ u ∈ U, f u = g u := by
  intro u hu
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU u hu
  have hδ : (0 : ℝ) < ε / 2 := by positivity
  have hB : closedBall u (ε / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  have hsupp : tsupport (HarmLoc.unitBump (ε / 2) hδ u : ℂ → ℝ) ⊆ (toOpens U hU : Set ℂ) :=
    (HarmLoc.tsupport_unitBump _ hδ u).trans hB
  have := hfg (testOnHE (toOpens U hU) _ hsupp)
  rw [← HarmLoc.integral_mul_unitBump hU hf hδ hB, ← HarmLoc.integral_mul_unitBump hU hg hδ hB]
  exact this

/-- **`CONFHarmPartLink`** (CONF C:1187–1190; D110 P3) -/
theorem confHarmPartLink : CONFHarmPartLink := by
  intro Ω mΩ P _ h hh ρ w hρ U hU hUb hUw X G hX hGm hXG
  obtain ⟨hXm, hXind, hh₀, hz, hdec, hXz, hharm, hzb, hvan⟩ := hX
  set V := toOpens U hU
  set k := recField h ρ w with hk_def
  have hsph : sphere w ρ ⊆ Uᶜ := fun y hy hyU => disjoint_left.1 hUw hyU hy
  have hle : recSigma h ρ w Uᶜ ≤ mΩ := recSigma_le hh ρ w Uᶜ
  have h0le : fieldSigmaClosed0 h Uᶜ ≤ recSigma h ρ w Uᶜ := by
    show fieldSigmaClosed0 h Uᶜ ≤
      fieldSigmaClosed (fun ω => addConst (h ω) (-circleAvg (h ω) ρ w)) Uᶜ
    rw [← fieldSigmaClosed0_addConst h (fun ω => -circleAvg (h ω) ρ w) Uᶜ]
    exact fieldSigmaClosed0_le_fieldSigmaClosed _ _
  have hindX : Indep (MeasurableSpace.comap X inferInstance) (fieldSigmaClosed0 h Uᶜ) P := by
    have := hXind
    rw [IndepFun_iff_Indep, comap_toSig] at this
    exact indep_of_indep_of_le_right this.symm h0le
  have hkXG : ∀ ω, k ω - X ω = G ω := fun ω => by rw [hXG ω, sub_sub_cancel]
  -- the harmonic clause for `k − X`, almost surely
  have hharm' : ∀ᵐ ω ∂P, ∃ f : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd f U ∧
      ∀ φ : TestOn V, restrictTo V (k ω - X ω) φ = ∫ x, f x * φ x := by
    filter_upwards [hharm, hXz] with ω hg hXω
    obtain ⟨g, hg, hgT⟩ := hg
    refine ⟨g, hg, fun φ => ?_⟩
    have e : k ω - X ω = hh₀ ω := by rw [hdec ω, hXω, add_sub_cancel_right]
    rw [e]; exact hgT φ
  classical
  set Hf : Ω → ℂ → ℝ := fun ω =>
    if hω : ∃ f : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd f U ∧
      ∀ φ : TestOn V, restrictTo V (k ω - X ω) φ = ∫ x, f x * φ x then hω.choose else 0
    with hHf
  have hHfh : ∀ ω, InnerProductSpace.HarmonicOnNhd (Hf ω) U := fun ω => by
    by_cases hω : ∃ f : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd f U ∧
      ∀ φ : TestOn V, restrictTo V (k ω - X ω) φ = ∫ x, f x * φ x
    · simp only [hHf, dif_pos hω]; exact hω.choose_spec.1
    · simp only [hHf, dif_neg hω]; exact InnerProductSpace.harmonicOnNhd_const (s := U) (0 : ℝ)
  set H₀ : Ω → ℂ → ℝ := fun ω x => Hf ω x + circleAvg (h ω) ρ w with hH₀_def
  have hH₀ : IsHarmPart P h U H₀ := by
    refine ⟨fun ω => (hHfh ω).add (InnerProductSpace.harmonicOnNhd_const (s := U) _),
      fun φ ψ hφ hψ hψ1 => ?_⟩
    set χ : TestC := φ - (∫ x, φ x) • ψ
    have hint : ∫ x, χ x = 0 := integral_sub_smul_unit hψ1
    have hzψ : ∀ ω, hz ω ψ = 0 := fun ω => by
      have := DFunLike.congr_fun (hvan ω) (testOnHE _ ψ hψ)
      exact (restrictTo_testOnHE _ (hz ω) ψ hψ).symm.trans this
    have hXψ : ∀ᵐ ω ∂P, X ω ψ = 0 := by
      filter_upwards [hXz] with ω hω
      rw [hω, hzψ ω]
    have hkapp : ∀ ω (θ : TestC), k ω θ = h ω θ - (∫ x, θ x) * circleAvg (h ω) ρ w :=
      fun ω θ => by
        show addConst (h ω) (-circleAvg (h ω) ρ w) θ = _
        rw [GFFInv.addConst_apply]; ring
    have hhχ : ∀ ω, h ω χ = G ω χ + X ω χ := fun ω => by
      have e1 : h ω χ = k ω χ := by rw [hkapp, hint, zero_mul, sub_zero]
      rw [e1, ← hkXG ω]
      show k ω χ = (k ω χ - X ω χ) + X ω χ
      ring
    -- integrability
    have hgχ : Integrable (fun ω => h ω χ) P :=
      (MarkovZB.memLp_pair hh ⟨χ, hint⟩).integrable one_le_two
    have hzφ : Integrable (fun ω => hz ω φ) P := by
      have := ((hzb.process.gaussian.hasGaussianLaw_eval (testOnHE V φ hφ)).memLp_two).integrable
        one_le_two
      refine this.congr (Eventually.of_forall fun ω => ?_)
      exact restrictTo_testOnHE V (hz ω) φ hφ
    have hXφ : Integrable (fun ω => X ω φ) P :=
      hzφ.congr (hXz.mono fun ω hω => by simp only [hω])
    have hsplit : (fun ω => h ω χ) =ᵐ[P] fun ω => G ω χ + X ω φ := by
      filter_upwards [hXψ] with ω h1
      rw [hhχ ω]
      simp only [χ, map_sub, map_smul, h1, smul_zero, sub_zero]
    have hGχ : (fun ω => G ω χ) =ᵐ[P] fun ω => h ω χ - X ω φ := by
      filter_upwards [hsplit] with ω h1
      rw [h1]; ring
    have hGχi : Integrable (fun ω => G ω χ) P := (hgχ.sub hXφ).congr hGχ.symm
    -- the conditional expectation
    have hc1 : P[fun ω => G ω χ | fieldSigmaClosed0 h Uᶜ] =ᵐ[P] fun ω => G ω χ :=
      condExp_of_aestronglyMeasurable' (h0le.trans hle)
        (aestronglyMeasurable_fieldSigmaClosed0_of_recSigma hh hρ w hsph
          ((GFFInv.measurable_pair χ).comp hGm)) hGχi
    have hc2 : P[fun ω => X ω φ | fieldSigmaClosed0 h Uᶜ] =ᵐ[P] fun _ => ∫ ω, X ω φ ∂P :=
      condExp_indep_eq hXm.comap_le (h0le.trans hle)
        ((GFFInv.measurable_pair φ).comp (comap_measurable X)).stronglyMeasurable hindX
    have hmean : ∫ ω, X ω φ ∂P = 0 := by
      rw [integral_congr_ae (hXz.mono fun ω hω => show X ω φ = hz ω φ by rw [hω])]
      refine (integral_congr_ae (Eventually.of_forall fun ω => ?_)).trans
        (hzb.process.centered (testOnHE V φ hφ))
      exact (restrictTo_testOnHE V (hz ω) φ hφ).symm
    have hRHS : (fun ω => (∫ x, H₀ ω x * φ x) - (∫ x, φ x) * h ω ψ) =ᵐ[P]
        fun ω => G ω χ := by
      filter_upwards [hharm', hXψ] with ω hω h1
      have e : Hf ω = hω.choose := dif_pos hω
      have hrep : G ω φ = ∫ x, Hf ω x * φ x := by
        rw [e, ← hkXG ω, ← restrictTo_testOnHE V _ φ hφ]
        exact hω.choose_spec.2 _
      have hGψ : G ω ψ = h ω ψ - circleAvg (h ω) ρ w := by
        rw [← hkXG ω]
        show k ω ψ - X ω ψ = _
        rw [h1, sub_zero, hkapp, hψ1, one_mul]
      have e2 : (fun x => H₀ ω x * φ x) =
          fun x => Hf ω x * φ x + circleAvg (h ω) ρ w * φ x := by
        ext x; simp only [hH₀_def]; ring
      rw [e2, integral_add (integrable_harm_mul_test (hHfh ω) φ hφ)
        ((GM.gm_integrable_testC φ).const_mul _), integral_const_mul, ← hrep]
      have eχ : G ω χ = G ω φ - (∫ x, φ x) * G ω ψ := by
        simp only [χ, map_sub, map_smul, smul_eq_mul]
      rw [eχ, hGψ]
      ring
    refine (condExp_congr_ae hsplit).trans ?_
    refine (condExp_add hGχi hXφ (fieldSigmaClosed0 h Uᶜ)).trans ?_
    filter_upwards [hc1, hc2, hRHS] with ω h1 h2 h3
    rw [Pi.add_apply, h1, h2, hmean, add_zero, h3]
  -- identification of the chosen version
  have hex : ∃ H, IsHarmPart P h U H := ⟨H₀, hH₀⟩
  have hHP : IsHarmPart P h U (harmPart P h U) := by
    unfold harmPart
    rw [dif_pos hex]
    exact hex.choose_spec
  filter_upwards [isHarmPart_ae_eq hU hUb hHP hH₀, hharm'] with ω h1 hω 𝔥 h𝔥 hp u hu
  rw [h1 u hu]
  show Hf ω u + circleAvg (h ω) ρ w = 𝔥 u + circleAvg (h ω) ρ w
  congr 1
  refine eqOn_of_harmonic_pairing hU (hHfh ω) h𝔥 (fun φ => ?_) u hu
  have e : Hf ω = hω.choose := dif_pos hω
  rw [e, ← hω.choose_spec.2 φ, hp φ]

end LQGMetric.CONF
