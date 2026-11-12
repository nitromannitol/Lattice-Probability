/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HarmExistB at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.HarmExistA

/-!
# Existence and a.s. uniqueness of the harmonic part (DEC-110 packet P3, part B)

Source: Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381,
`confluence-final.tex` C:1187–1190 (normalize `h` away from `U`, then the Markov property
[LM, Lemma 2.1]: `h|_U = h̊^U + 𝔥^U`); the harmonic part is constant-covariant (CONF C:1154,
1187; `CONF.isHarmPart0_addConst_iff`).

* `exists_isHarmPart` : for every whole-plane GFF `h` (any random additive constant) and every
  bounded open `U`, a harmonic part `𝔥^U` in the sense of `Blueprint.IsHarmPart` (conditioning on
  `σ(h|_{ℂ∖U})` modulo additive constants) exists. Proof: normalize `k = h − h(ψ₀)` with a unit
  bump `ψ₀` outside `U`, then `g = k − k_ρ(0)` on a circle outside `cl U`; the raw harmonic part
  of `g` (`HarmExist.exists_isHarmPartRaw_of_normAt`) is a mod-constant one since
  `σ(g|_{ℂ∖U}) = σ(h|_{ℂ∖U} mod constants)` (`k_ρ(0)` is `σ(k|_{ℂ∖U})`-measurable), and
  `h = g + (k_ρ(0) + h(ψ₀))`.
* `isHarmPart_ae_eq` : any two versions agree a.s. on all of `U` (pair with radial unit bumps at
  a countable dense set of centres; mean value property and continuity; the argument of
  `LM.lmRep_harm_eq`, Papers/LM/L3_4N4.lean).
* `harmPart_addConst_ae` : `𝔥^U_{h+a} = 𝔥^U_h + a` a.s. on `U`, for the chosen versions
  `Blueprint.harmPart`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter TopologicalSpace
open scoped ENNReal

namespace LQGMetric.HarmExist

open Blueprint

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **existence of the harmonic part** `𝔥^U` (CONF C:1187–1190, LM Lemma 2.1) for every
whole-plane GFF and every bounded open `U` -/
theorem exists_isHarmPart {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {U : Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) : ∃ H, IsHarmPart P h U H := by
  obtain ⟨M, hM⟩ := hUb.subset_ball (0 : ℂ)
  set ρ : ℝ := |M| + 1 with hρ_def
  have hρ : 0 < ρ := by positivity
  have hnormU : ∀ y ∈ U, ‖y‖ < |M| := fun y hy => by
    have := hM hy
    rw [mem_ball, dist_zero_right] at this
    exact this.trans_le (le_abs_self M)
  -- the unit bump `ψ₀` outside `U`
  set ψ₀ : TestC := HarmLoc.unitBump (1 / 2) (by norm_num) (ρ : ℂ)
  have hψ₀1 : ∫ x, ψ₀ x = 1 := HarmLoc.integral_unitBump _ _ _
  have hψ₀K : tsupport (ψ₀ : ℂ → ℝ) ⊆ Uᶜ := by
    refine (HarmLoc.tsupport_unitBump _ _ _).trans fun y hy hyU => ?_
    rw [mem_closedBall, dist_eq_norm] at hy
    have h1 := hnormU y hyU
    have h2 : ‖(ρ : ℂ)‖ ≤ ‖y‖ + ‖y - ρ‖ := by
      have := norm_sub_le y (y - ρ); simp only [sub_sub_cancel] at this; linarith
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ] at h2
    linarith
  have hsph : sphere (0 : ℂ) |ρ| ⊆ Uᶜ := fun y hy hyU => by
    rw [mem_sphere, dist_zero_right, abs_of_pos hρ] at hy
    have := hnormU y hyU
    linarith
  have hUw : Disjoint U (sphere (0 : ℂ) ρ) := by
    rw [Set.disjoint_right]
    intro y hy hyU
    exact hsph (by rwa [abs_of_pos hρ]) hyU
  -- the normalized fields
  set k := CONF.normIn h ψ₀
  have hk : IsWholePlaneGFF k P := CONF.isWholePlaneGFF_normIn hh ψ₀
  set g := CONF.recField k ρ 0
  have hg : IsWholePlaneGFF g P := CONF.isWholePlaneGFF_recField hk ρ 0
  have hn : ∀ᵐ ω ∂P, circleAvg (g ω) ρ 0 = 0 := by
    filter_upwards [CircleAvg.ae_circleAvg_addConst hk 0 hρ] with ω hω
    simp only [g, CONF.recField, hω, add_neg_cancel]
  obtain ⟨H, hH⟩ := exists_isHarmPartRaw_of_normAt hg hρ 0 hn hU hUw
  -- `σ(g|_{ℂ∖U}) = σ(g|_{ℂ∖U} mod constants)`
  have hF : Measurable[fieldSigmaClosed k Uᶜ] fun ω => -circleAvg (k ω) ρ 0 :=
    (GM.measurable_circleAvg_fieldSigmaClosed k ρ 0 hsph).neg
  have h0g : fieldSigmaClosed0 g Uᶜ = fieldSigmaClosed0 h Uᶜ := by
    show fieldSigmaClosed0 (fun ω => addConst (k ω) (-circleAvg (k ω) ρ 0)) Uᶜ = _
    rw [CONF.fieldSigmaClosed0_addConst]
    exact CONF.fieldSigmaClosed0_addConst h _ Uᶜ
  have hσ : fieldSigmaClosed g Uᶜ = fieldSigmaClosed0 g Uᶜ := by
    refine le_antisymm ?_ (CONF.fieldSigmaClosed0_le_fieldSigmaClosed g _)
    refine (fieldSigmaClosed_addConst_le k _ Uᶜ hF).trans ?_
    rw [CONF.fieldSigmaClosed_normIn_eq h hψ₀1 hψ₀K, h0g]
  have hHg : IsHarmPart P g U H := by
    refine ⟨hH.1, fun φ ψ hφ hψ hψ1 => ?_⟩
    have := hH.2 φ ψ hφ hψ hψ1
    rwa [hσ] at this
  have key := (CONF.isHarmPart0_addConst_iff g (fun ω => circleAvg (k ω) ρ 0 + h ω ψ₀) U H).2
    hHg
  have e : (fun ω => addConst (g ω) (circleAvg (k ω) ρ 0 + h ω ψ₀)) = h := by
    funext ω
    ext φ
    simp only [g, CONF.recField, k, CONF.normIn, GFFInv.addConst_apply]
    ring
  rw [e] at key
  exact ⟨_, key⟩

omit [IsProbabilityMeasure P] in
/-- **a.s. uniqueness of the harmonic part**: two versions agree a.s. on all of `U` -/
theorem isHarmPart_ae_eq {h : Ω → DistC} {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {H₁ H₂ : Ω → ℂ → ℝ} (h₁ : IsHarmPart P h U H₁)
    (h₂ : IsHarmPart P h U H₂) : ∀ᵐ ω ∂P, ∀ u ∈ U, H₁ ω u = H₂ ω u := by
  -- a unit test function outside `cl U`
  have hne : ((closure U)ᶜ).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hne
    exact NormedSpace.unbounded_univ ℝ ℂ (hne ▸ hUb.closure)
  obtain ⟨ψ, hψ, hψ1⟩ := HarmLoc.exists_unit_test isClosed_closure.isOpen_compl hne
  have hδ : ∀ v ∈ U, ∃ δ : ℝ, 0 < δ ∧ closedBall v δ ⊆ U := fun v hv => by
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU v hv
    exact ⟨ε / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hεU⟩
  choose δ hδpos hδB using hδ
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℂ
  set S' := U ∩ S
  have hS'c : S'.Countable := hSc.mono inter_subset_right
  have hpair : ∀ v (hv : v ∈ S'), ∀ᵐ ω ∂P,
      ∫ x, H₁ ω x * HarmLoc.unitBump (δ v hv.1) (hδpos v hv.1) v x =
        ∫ x, H₂ ω x * HarmLoc.unitBump (δ v hv.1) (hδpos v hv.1) v x := fun v hv => by
    have hs := (HarmLoc.tsupport_unitBump _ (hδpos v hv.1) v).trans (hδB v hv.1)
    filter_upwards [(h₁.2 _ ψ hs hψ hψ1).symm.trans (h₂.2 _ ψ hs hψ hψ1)] with ω hω
    exact sub_left_injective hω
  filter_upwards [(ae_ball_iff hS'c).2 hpair] with ω hω u hu
  have hval : ∀ v ∈ S', H₁ ω v - H₂ ω v = 0 := fun v hv => by
    have k := hω v hv
    rw [HarmLoc.integral_mul_unitBump hU (h₁.1 ω) _ (hδB v hv.1),
      HarmLoc.integral_mul_unitBump hU (h₂.1 ω) _ (hδB v hv.1)] at k
    rw [k, sub_self]
  have hcont : ContinuousAt (fun x => H₁ ω x - H₂ ω x) u :=
    (h₁.1 ω u hu).1.continuousAt.sub (h₂.1 ω u hu).1.continuousAt
  have hcl : u ∈ closure S' := hSd.open_subset_closure_inter hU hu
  have hmem := mem_closure_image hcont hcl
  have himg : (fun x => H₁ ω x - H₂ ω x) '' S' ⊆ {0} := by
    rintro _ ⟨v, hv, rfl⟩; exact hval v hv
  have := closure_mono himg hmem
  rw [closure_singleton, mem_singleton_iff, sub_eq_zero] at this
  exact this

/-- **the chosen harmonic part is constant-covariant a.s.**: `𝔥^U_{h+a} = 𝔥^U_h + a` on `U` -/
theorem harmPart_addConst_ae {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {U : Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (a : Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ u ∈ U,
      harmPart P (fun ω => addConst (h ω) (a ω)) U ω u = harmPart P h U ω u + a ω := by
  have hex := exists_isHarmPart hh hU hUb
  have h0 : IsHarmPart P h U (harmPart P h U) := CONF.isHarmPart0_harmPart0 hex
  have h1 := (CONF.isHarmPart0_addConst_iff h a U (harmPart P h U)).2 h0
  have h2 : IsHarmPart P (fun ω => addConst (h ω) (a ω)) U
      (harmPart P (fun ω => addConst (h ω) (a ω)) U) := CONF.isHarmPart0_harmPart0 ⟨_, h1⟩
  exact isHarmPart_ae_eq hU hUb h2 h1

end LQGMetric.HarmExist
