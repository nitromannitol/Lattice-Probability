/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L35B5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L35B4
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.MarkovNorm

/-!
# Scale and translation covariance of the harmonic part (task P2-CONF35b)

Source: Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381,
`confluence-final.tex` C:1169–1172 ("`𝒰_r(z;δ) = r𝒰_1(0;δ) + z`" combined with "the translation
and scale invariance of the law of `h`, modulo additive constant"): the first step of
`CONFHarmBoundU` is that the harmonic part transforms with the field.

**`isHarmPart_affineComp`**: if `𝔥` is a harmonic part of `h` on `U` (D110 form, conditioning on
`σ(h|_{ℂ∖U})` modulo constants), then `x ↦ 𝔥(r x + z)` is a harmonic part of `h(r · + z)` on
`U₁ = {x | r x + z ∈ U}`. Ingredients: `harmonicOnNhd_comp_holo`; the change of variables
`GFFInv.integral_eq_smul_add`; the σ-algebras `σ(h(r·+z)|_{ℂ∖U₁}) = σ(h|_{ℂ∖U})` modulo constants,
via inside normalization (`CONF.fieldSigmaClosed_normIn_eq`, D110) and the raw transport
`DFGPS.fieldSigmaClosed_le_affineComp`, `DFGPS.fieldSigmaClosed_affineComp_le`. Own routine glue.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace

namespace LQGMetric.CONF

open Blueprint GFFInv

variable {Ω : Type} [MeasurableSpace Ω] {r : ℝ} {z : ℂ}

/-- the affine pushforward `(r²)⁻¹ φ((· − z)/r)` of a test function -/
def affPush (r : ℝ) (z : ℂ) (φ : TestC) : TestC := (r ^ 2)⁻¹ • testAffinePull r z φ

theorem affineComp_apply_eq_affPush (r : ℝ) (z : ℂ) (g : DistC) (φ : TestC) :
    affineComp r z g φ = g (affPush r z φ) := by
  rw [affineComp_apply, affPush, map_smul, smul_eq_mul]

theorem integral_affPush (hr : 0 < r) (z : ℂ) (φ : TestC) :
    ∫ x, affPush r z φ x = ∫ x, φ x := by
  have e : (affPush r z φ : ℂ → ℝ) = fun x => (r ^ 2)⁻¹ * testAffinePull r z φ x := by
    ext x; simp [affPush]
  rw [e, integral_const_mul, integral_testAffinePull φ hr z]
  field_simp

theorem tsupport_affPush_subset (hr : 0 < r) (z : ℂ) (φ : TestC) {S : Set ℂ}
    (hφ : tsupport (φ : ℂ → ℝ) ⊆ S) :
    tsupport (affPush r z φ : ℂ → ℝ) ⊆ {y | (y - z) / r ∈ S} := by
  have e : (affPush r z φ : ℂ → ℝ) = fun y => (r ^ 2)⁻¹ * φ ((y - z) / r) := by
    ext y; simp [affPush, testAffinePull_apply r z hr.ne']
  rw [e]
  refine (tsupport_mul_subset_right (f := fun _ => (r ^ 2)⁻¹)).trans ?_
  refine (tsupport_comp_subset_preimage (φ : ℂ → ℝ) (f := fun y => (y - z) / r)
    (by fun_prop)).trans fun y hy => hφ hy

theorem affMap_div_cancel (hr : 0 < r) (z y : ℂ) : r • ((y - z) / r) + z = y := by
  rw [Complex.real_smul, mul_div_cancel₀ _ (by exact_mod_cast hr.ne'), sub_add_cancel]

theorem div_affMap_cancel (hr : 0 < r) (z x : ℂ) : (r • x + z - z) / r = x := by
  rw [add_sub_cancel_right, Complex.real_smul, mul_div_cancel_left₀ _ (by exact_mod_cast hr.ne')]

/-- `σ(h(r·+z)|_{ℂ∖U₁}) = σ(h|_{ℂ∖U})` modulo constants -/
theorem fieldSigmaClosed0_affineComp (hr : 0 < r) (z : ℂ) {U : Set ℂ} (hU : IsOpen U)
    (h : Ω → DistC) {ψ : TestC} (hψ1 : ∫ x, ψ x = 1)
    (hψ : tsupport (ψ : ℂ → ℝ) ⊆ ((fun x => r • x + z) ⁻¹' U)ᶜ) :
    fieldSigmaClosed0 (fun ω => affineComp r z (h ω)) ((fun x => r • x + z) ⁻¹' U)ᶜ =
      fieldSigmaClosed0 h Uᶜ := by
  set U₁ := (fun x => r • x + z) ⁻¹' U
  set g : Ω → DistC := fun ω => affineComp r z (h ω)
  set ψ' := affPush r z ψ
  have hψ'1 : ∫ x, ψ' x = 1 := by rw [integral_affPush hr z, hψ1]
  have hψ'U : tsupport (ψ' : ℂ → ℝ) ⊆ Uᶜ := fun y hy => by
    have := tsupport_affPush_subset hr z ψ hψ hy
    simp only [mem_ofPred_eq, U₁, mem_compl_iff, mem_preimage, affMap_div_cancel hr] at this
    exact this
  set k := normIn h ψ'
  have e2 : (fun ω => affineComp r z (k ω)) = normIn g ψ := by
    funext ω
    simp only [k, normIn, g]
    rw [GM.affineComp_addConst hr, affineComp_apply_eq_affPush]
  have hV : (DFGPS.preOpens r z (toOpens U hU) : Set ℂ) = U₁ := by
    ext y; exact DFGPS.mem_preOpens hr.ne' (toOpens U hU) y
  have e4 : fieldSigmaClosed (fun ω => affineComp r z (k ω)) U₁ᶜ = fieldSigmaClosed k Uᶜ := by
    rw [← hV]
    exact le_antisymm (DFGPS.fieldSigmaClosed_affineComp_le hr (toOpens U hU) k)
      (DFGPS.fieldSigmaClosed_le_affineComp hr (toOpens U hU) k)
  rw [← fieldSigmaClosed_normIn_eq g hψ1 hψ, ← e2, e4, fieldSigmaClosed_normIn_eq h hψ'1 hψ'U]

/-- **the harmonic part transforms with the field**: `𝔥^{U₁}_{h(r·+z)} = 𝔥^U_h(r · + z)` -/
theorem isHarmPart_affineComp {P : Measure Ω} {h : Ω → DistC} (hr : 0 < r) (z : ℂ)
    {U : Set ℂ} (hU : IsOpen U) {H : Ω → ℂ → ℝ} (hH : IsHarmPart P h U H) :
    IsHarmPart P (fun ω => affineComp r z (h ω)) ((fun x => r • x + z) ⁻¹' U)
      (fun ω x => H ω (r • x + z)) := by
  set U₁ := (fun x => r • x + z) ⁻¹' U
  have hA : Continuous fun x : ℂ => r • x + z := by fun_prop
  have hU₁ : IsOpen U₁ := hU.preimage hA
  refine ⟨fun ω => ?_, fun φ ψ hφ hψ hψ1 => ?_⟩
  · have := harmonicOnNhd_comp_holo hU hU₁ (hH.1 ω)
      (f := fun x => r • x + z) (by
        have : (fun x : ℂ => r • x + z) = fun x => (r : ℂ) * x + z := by
          funext x; rw [Complex.real_smul]
        rw [this]; fun_prop) (fun x hx => hx)
    exact this
  -- the pushed test functions
  set φ' := affPush r z φ
  set ψ' := affPush r z ψ
  have hψ'1 : ∫ x, ψ' x = 1 := by rw [integral_affPush hr z, hψ1]
  have hφ'U : tsupport (φ' : ℂ → ℝ) ⊆ U := fun y hy => by
    have := tsupport_affPush_subset hr z φ hφ hy
    simp only [mem_ofPred_eq, U₁, mem_preimage, affMap_div_cancel hr] at this
    exact this
  have hcl : (fun y => (y - z) / r) '' closure U ⊆ closure U₁ := by
    refine (image_closure_subset_closure_image (by fun_prop)).trans (closure_mono ?_)
    rintro _ ⟨y, hy, rfl⟩
    show r • ((y - z) / r) + z ∈ U
    rw [affMap_div_cancel hr]; exact hy
  have hψ'U : tsupport (ψ' : ℂ → ℝ) ⊆ (closure U)ᶜ := fun y hy hyU => by
    have := tsupport_affPush_subset hr z ψ hψ hy
    exact this (hcl ⟨y, hyU, rfl⟩)
  have hψU₁ : tsupport (ψ : ℂ → ℝ) ⊆ U₁ᶜ :=
    hψ.trans (compl_subset_compl.2 subset_closure)
  have hint : ∫ x, φ' x = ∫ x, φ x := integral_affPush hr z φ
  have key : (fun ω => affineComp r z (h ω) (φ - (∫ x, φ x) • ψ)) =
      fun ω => h ω (φ' - (∫ x, φ' x) • ψ') := by
    funext ω
    rw [map_sub, map_smul, map_sub, map_smul, affineComp_apply_eq_affPush,
      affineComp_apply_eq_affPush, hint]
  rw [key, fieldSigmaClosed0_affineComp hr z hU h hψ1 hψU₁]
  refine (hH.2 φ' ψ' hφ'U hψ'U hψ'1).trans (Eventually.of_forall fun ω => ?_)
  have hchg : ∫ x, H ω x * φ' x = ∫ x, H ω (r • x + z) * φ x := by
    rw [integral_eq_smul_add _ hr z, ← integral_const_mul]
    congr 1
    funext v
    simp only [φ', affPush, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
      testAffinePull_apply r z hr.ne', div_affMap_cancel hr]
    field_simp
  simp only
  rw [hchg, hint, affineComp_apply_eq_affPush]

end LQGMetric.CONF
