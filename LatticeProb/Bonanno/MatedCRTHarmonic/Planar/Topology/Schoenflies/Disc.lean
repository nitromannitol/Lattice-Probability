/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Planar.Topology.Schoenflies.Disc at commit fdb5cad; only the module paths of local imports are changed. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Planar.Topology.Jordan.Complex

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # The Schoenflies theorem, part 1: the closed-disc form

For a Jordan curve `Γ ⊆ ℂ` (LQGMetric's `IsJordanCurve`) and a point `p` of the bounded
component `U` of `Γᶜ`, there is a map `φ`, continuous and injective on the closed unit disc,
holomorphic inside, with `φ 0 = p`, `φ '' 𝔻 = U` and `φ '' ∂𝔻 = Γ` (`schoenflies_disc`), hence a
homeomorphism of the closed unit disc onto `closure U` carrying the circle onto `Γ`
(`schoenflies_closedDisc`).

Proof (standard derivation of Schoenflies from Carathéodory, e.g. Pommerenke, *Boundary Behaviour
of Conformal Maps*, 1992, Thm 2.6 and the remark after it): by the Jordan curve theorem
(`MatedCRTHarmonic.Planar.Jordan.jordan_curve_components_complex`) `frontier U = Γ` and
`Uᶜ = Γ ∪ V = closure V` with `V` the unbounded component, so `Uᶜ` is connected and unbounded;
Carathéodory's theorem for Jordan domains (LQGMetric `jm_jordan_closedDisc_extension'`) applies
after translating `p` to `0`. Only the translation and the bookkeeping are new.
-/

noncomputable section

namespace MatedCRTHarmonic.Planar.Schoenflies

open Metric Set Function Bornology Topology
open LQGMetric.JordanMap

/-- The image of a Jordan curve under a map continuous and injective on it is a Jordan curve. -/
theorem isJordanCurve_image {Γ : Set ℂ} (hΓ : IsJordanCurve Γ) {F : ℂ → ℂ}
    (hFc : ContinuousOn F Γ) (hFi : InjOn F Γ) : IsJordanCurve (F '' Γ) := by
  obtain ⟨γ, hγc, hγi, rfl⟩ := hΓ
  exact ⟨F ∘ γ, hFc.comp hγc (mapsTo_image _ _), hFi.comp hγi (mapsTo_image _ _),
    image_comp _ _ _⟩

/-- A Jordan curve is compact. -/
theorem isCompact_of_isJordanCurve {Γ : Set ℂ} (hΓ : IsJordanCurve Γ) : IsCompact Γ := by
  obtain ⟨γ, hγc, -, rfl⟩ := hΓ
  exact (isCompact_sphere 0 1).image_of_continuousOn hγc

/-- **Carathéodory's theorem with base point `p`.** `jm_jordan_closedDisc_extension'` after
translating `p ∈ U` to `0`. -/
theorem carath_basepoint {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) {p : ℂ}
    (hp : p ∈ U) (hUb : IsBounded U)
    (hcomp : ∀ a ∉ U, ¬ IsBounded (connectedComponentIn Uᶜ a))
    (hJ : IsJordanCurve (frontier U)) :
    ∃ φ : ℂ → ℂ, ContinuousOn φ (closedBall 0 1) ∧ InjOn φ (closedBall 0 1) ∧
      DifferentiableOn ℂ φ (ball 0 1) ∧ φ 0 = p ∧ φ '' ball 0 1 = U ∧
      φ '' sphere 0 1 = frontier U := by
  set e : ℂ ≃ᵢ ℂ := IsometryEquiv.addRight (-p)
  set h : ℂ ≃ₜ ℂ := e.toHomeomorph
  have he : ∀ z, h z = z + -p := fun z => rfl
  have hback : ∀ S : Set ℂ, (fun w => w + p) '' (h '' S) = S := fun S => by
    rw [image_image]; simp [he]
  have hcomp' : ∀ a ∉ h '' U, ¬ IsBounded (connectedComponentIn (h '' U)ᶜ a) := by
    intro a ha hba
    have hb : h.symm a ∉ U := fun hU => ha ⟨_, hU, h.apply_symm_apply a⟩
    refine hcomp _ hb ?_
    have hcc := h.image_connectedComponentIn (mem_compl hb)
    rw [h.apply_symm_apply, image_compl_eq h.bijective] at hcc
    rw [← hcc] at hba
    have := e.symm.isometry.lipschitzWith.isBounded_image hba
    rwa [show ⇑e.symm '' (h '' connectedComponentIn Uᶜ (h.symm a)) =
      connectedComponentIn Uᶜ (h.symm a) from h.symm_image_image _] at this
  have hJ' : IsJordanCurve (frontier (h '' U)) := by
    rw [← h.image_frontier]
    exact isJordanCurve_image hJ h.continuous.continuousOn h.injective.injOn
  obtain ⟨φ, hc, hi, hd, h0, hb, hs⟩ := jm_jordan_closedDisc_extension' (U := h '' U)
    (h.isOpenMap _ hUo) (hUc.image _ h.continuous.continuousOn)
    ⟨p, hp, by simp [he]⟩ (e.isometry.lipschitzWith.isBounded_image hUb) hcomp' hJ'
  refine ⟨fun z => φ z + p, hc.add continuousOn_const,
    fun z hz w hw hzw => hi hz hw (add_right_cancel hzw), hd.add_const p, by simp [h0], ?_, ?_⟩
  · rw [← image_image (g := fun w => w + p), hb, hback]
  · rw [← image_image (g := fun w => w + p), hs, ← h.image_frontier, hback]

/-- **Jordan curve theorem, usable form at a point of a bounded component.** -/
theorem jordan_split {Γ : Set ℂ} (hΓ : IsJordanCurve Γ) {p : ℂ} (hp : p ∈ Γᶜ)
    (hb : IsBounded (connectedComponentIn Γᶜ p)) :
    frontier (connectedComponentIn Γᶜ p) = Γ ∧ ∃ V : Set ℂ, IsOpen V ∧ IsPreconnected V ∧
      ¬ IsBounded V ∧ Disjoint (connectedComponentIn Γᶜ p) V ∧
      Γᶜ = connectedComponentIn Γᶜ p ∪ V ∧ frontier V = Γ := by
  obtain ⟨x₁, -, x₀, -, -, hu₀, hd, hun, hf₁, hf₀⟩ :=
    MatedCRTHarmonic.Planar.Jordan.jordan_curve_components_complex hΓ
  have hΓo : IsOpen Γᶜ := (isCompact_of_isJordanCurve hΓ).isClosed.isOpen_compl
  have hp' := hp
  rw [hun] at hp'
  rcases hp' with hp₁ | hp₀
  · rw [← connectedComponentIn_eq hp₁]
    exact ⟨hf₁, _, hΓo.connectedComponentIn, isPreconnected_connectedComponentIn, hu₀, hd,
      hun, hf₀⟩
  · exact absurd (connectedComponentIn_eq hp₀ ▸ hb) hu₀

/-- The complement of the bounded component is the closure of the unbounded one. -/
theorem compl_eq_closure {Γ U V : Set ℂ} (hd : Disjoint U V) (hun : Γᶜ = U ∪ V)
    (hfV : frontier V = Γ) : Uᶜ = closure V := by
  rw [closure_eq_self_union_frontier, hfV]
  ext z
  constructor
  · intro hz
    by_cases hzΓ : z ∈ Γ
    · exact Or.inr hzΓ
    · have : z ∈ U ∪ V := hun ▸ hzΓ
      exact Or.inl (this.resolve_left hz)
  · rintro (hzV | hzΓ) hzU
    · exact hd.ne_of_mem hzU hzV rfl
    · have : z ∈ U ∪ V := Or.inl hzU
      rw [← hun] at this
      exact this hzΓ

/-- **Schoenflies, closed-disc form (map version).** -/
theorem schoenflies_disc {Γ : Set ℂ} (hΓ : IsJordanCurve Γ) {p : ℂ} (hp : p ∈ Γᶜ)
    (hb : IsBounded (connectedComponentIn Γᶜ p)) :
    ∃ φ : ℂ → ℂ, ContinuousOn φ (closedBall 0 1) ∧ InjOn φ (closedBall 0 1) ∧
      DifferentiableOn ℂ φ (ball 0 1) ∧ φ 0 = p ∧ φ '' ball 0 1 = connectedComponentIn Γᶜ p ∧
      φ '' sphere 0 1 = Γ := by
  obtain ⟨hfr, V, hVo, hVc, hVu, hd, hun, hfV⟩ := jordan_split hΓ hp hb
  have hΓo : IsOpen Γᶜ := (isCompact_of_isJordanCurve hΓ).isClosed.isOpen_compl
  have hcl := compl_eq_closure hd hun hfV
  have hcomp : ∀ a ∉ connectedComponentIn Γᶜ p,
      ¬ IsBounded (connectedComponentIn (connectedComponentIn Γᶜ p)ᶜ a) := by
    intro a ha hba
    have hsub : (connectedComponentIn Γᶜ p)ᶜ ⊆ connectedComponentIn (connectedComponentIn Γᶜ p)ᶜ a :=
      (hcl ▸ hVc.closure).subset_connectedComponentIn ha subset_rfl
    exact hVu (hba.subset ((hcl ▸ subset_closure).trans hsub))
  have := carath_basepoint hΓo.connectedComponentIn isPreconnected_connectedComponentIn
    (mem_connectedComponentIn hp) hb hcomp (by rw [hfr]; exact hΓ)
  rwa [hfr] at this

/-- **Schoenflies, closed-disc form (deliverable 1).** For a Jordan curve `Γ` and a point `p` of
the bounded component `U` of `Γᶜ`, a homeomorphism of the closed unit disc onto `closure U`
carrying the unit circle onto `Γ` and the open disc onto `U`. -/
theorem schoenflies_closedDisc {Γ : Set ℂ} (hΓ : IsJordanCurve Γ) {p : ℂ} (hp : p ∈ Γᶜ)
    (hb : IsBounded (connectedComponentIn Γᶜ p)) :
    ∃ e : closedBall (0 : ℂ) 1 ≃ₜ closure (connectedComponentIn Γᶜ p),
      (fun z => (e z : ℂ)) '' {z | (z : ℂ) ∈ sphere 0 1} = Γ ∧
      (fun z => (e z : ℂ)) '' {z | (z : ℂ) ∈ ball 0 1} = connectedComponentIn Γᶜ p := by
  obtain ⟨φ, hc, hi, -, -, hball, hsph⟩ := schoenflies_disc hΓ hp hb
  have hfr := (jordan_split hΓ hp hb).1
  have hcl : φ '' closedBall 0 1 = closure (connectedComponentIn Γᶜ p) := by
    rw [← ball_union_sphere, image_union, hball, hsph, closure_eq_self_union_frontier, hfr]
  have : CompactSpace (closedBall (0 : ℂ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  let F : closedBall (0 : ℂ) 1 → closure (connectedComponentIn Γᶜ p) :=
    fun z => ⟨φ z, by rw [← hcl]; exact mem_image_of_mem φ z.2⟩
  have hF : Bijective F := by
    refine ⟨fun z w hzw => Subtype.ext (hi z.2 w.2 (congrArg Subtype.val hzw)), fun y => ?_⟩
    have hy : (y : ℂ) ∈ φ '' closedBall 0 1 := by rw [hcl]; exact y.2
    obtain ⟨z, hz, hzy⟩ := hy
    exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
  have hFc : Continuous F :=
    (hc.comp_continuous continuous_subtype_val (fun z => z.2)).subtype_mk _
  refine ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F hF) hFc, ?_, ?_⟩
  · refine Eq.trans ?_ hsph
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, sphere_subset_closedBall hz⟩, hz, rfl⟩
  · refine Eq.trans ?_ hball
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, ball_subset_closedBall hz⟩, hz, rfl⟩

end MatedCRTHarmonic.Planar.Schoenflies
