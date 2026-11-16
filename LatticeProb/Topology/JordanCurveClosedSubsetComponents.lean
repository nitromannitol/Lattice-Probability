import LatticeProb.Topology.EmbeddedDiskJordan
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UnitInterval

/-! Compact connected proper subsets of a Jordan curve are points or arcs. -/

set_option autoImplicit false

noncomputable section

open Set Metric
open LQGMetric.JordanMap

namespace LatticeProb

/-- A compact connected space continuously embedded in the real line is a point or an arc. -/
theorem subsingleton_or_homeomorph_unitInterval_of_continuous_injective_real
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    (f : X → ℝ) (hf : Continuous f) (hi : Function.Injective f) :
    Subsingleton X ∨ Nonempty (X ≃ₜ unitInterval) := by
  classical
  let S := range f
  have hS : S = Icc (sInf S) (sSup S) :=
    eq_Icc_of_connected_compact (isConnected_range hf) (isCompact_range hf)
  let e : X ≃ₜ S := (hf.subtype_mk _).homeoOfEquivCompactToT2
    (f := Equiv.ofInjective f hi)
  have hab : sInf S ≤ sSup S := by
    have hne : (Icc (sInf S) (sSup S)).Nonempty := hS ▸ range_nonempty f
    exact nonempty_Icc.mp hne
  rcases hab.eq_or_lt with hab | hab
  · left
    constructor
    intro x y
    apply hi
    have hx : f x ∈ Icc (sInf S) (sSup S) := hS ▸ mem_range_self x
    have hy : f y ∈ Icc (sInf S) (sSup S) := hS ▸ mem_range_self y
    exact le_antisymm (hx.2.trans (hab ▸ hy.1)) (hy.2.trans (hab ▸ hx.1))
  · right
    exact ⟨e.trans ((Homeomorph.setCongr hS).trans (iccHomeoI _ _ hab))⟩


/-- A compact connected proper subset of a Jordan curve is a point or an arc. -/
theorem subsingleton_or_homeomorph_unitInterval_of_isJordanCurve
    {Γ K : Set ℂ} (hΓ : IsJordanCurve Γ) (hK : IsCompact K) (hc : IsConnected K)
    (hsub : K ⊆ Γ) (hproper : ∃ p ∈ Γ, p ∉ K) :
    Subsingleton K ∨ Nonempty (K ≃ₜ unitInterval) := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : ConnectedSpace K := isConnected_iff_connectedSpace.mp hc
  obtain ⟨γ, hγ, hiγ, hΓeq⟩ := hΓ
  let g : sphere (0 : ℂ) 1 → ℂ := fun z => γ z
  have hg : Continuous g := continuousOn_iff_continuous_domRestrict.mp hγ
  have hig : Function.Injective g := by
    intro x y h
    exact Subtype.ext (hiγ x.2 y.2 h)
  have hrange : range g = Γ := by
    rw [← hΓeq]
    ext z
    simp [g]
  let eg : (sphere (0 : ℂ) 1) ≃ₜ Γ :=
    (hg.subtype_mk _ |>.homeoOfEquivCompactToT2 (f := Equiv.ofInjective g hig)).trans
      (Homeomorph.setCongr hrange)
  obtain ⟨p, hpΓ, hpK⟩ := hproper
  let v : sphere (0 : ℂ) 1 := eg.symm ⟨p, hpΓ⟩
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨Complex.finrank_real_complex⟩
  let chart := stereographic' 1 v
  let r : EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ :=
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toHomeomorph
  let t : K → sphere (0 : ℂ) 1 := fun x => eg.symm ⟨x, hsub x.2⟩
  have ht : Continuous t := eg.symm.continuous.comp (continuous_subtype_val.subtype_mk _)
  have htinj : Function.Injective t := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : Γ => (z : ℂ)) (eg.symm.injective h)
  have hsource : ∀ x : K, t x ∈ chart.source := by
    intro x
    rw [stereographic'_source]
    simp only [mem_compl_iff, mem_singleton_iff]
    intro h
    have heq : (x : ℂ) = p := congrArg (fun z : Γ => (z : ℂ)) (eg.symm.injective h)
    exact hpK (heq ▸ x.2)
  let f : K → ℝ := fun x => r (chart (t x))
  have hf : Continuous f := r.continuous.comp (chart.continuousOn.comp_continuous ht hsource)
  have hi : Function.Injective f := by
    intro x y h
    apply htinj
    exact chart.injOn (hsource x) (hsource y) (r.injective h)
  exact subsingleton_or_homeomorph_unitInterval_of_continuous_injective_real f hf hi


/-- Each component of a proper closed subset of a Jordan curve is a singleton or a Jordan arc. -/
theorem connectedComponentIn_eq_singleton_or_arc_of_isJordanCurve
    {Γ T : Set ℂ} (hΓ : IsJordanCurve Γ) (hT : IsClosed T) (hsub : T ⊆ Γ)
    (hproper : ∃ p ∈ Γ, p ∉ T) {x : ℂ} (hx : x ∈ T) :
    (∃ p : ℂ, connectedComponentIn T x = {p}) ∨
      ∃ f : unitInterval → ℂ, Continuous f ∧ Function.Injective f ∧
        range f = connectedComponentIn T x := by
  classical
  let K := connectedComponentIn T x
  have hKclosed : IsClosed K := by
    change IsClosed (connectedComponentIn T x)
    rw [connectedComponentIn_eq_image hx]
    exact hT.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hKsub : K ⊆ Γ := (connectedComponentIn_subset T x).trans hsub
  have hKcompact : IsCompact K :=
    (MatedCRTHarmonic.Planar.Schoenflies.isCompact_of_isJordanCurve hΓ).of_isClosed_subset hKclosed hKsub
  have hKconn : IsConnected K := isConnected_connectedComponentIn_iff.mpr hx
  have hKproper : ∃ p ∈ Γ, p ∉ K := by
    obtain ⟨p, hp, hpT⟩ := hproper
    exact ⟨p, hp, fun hpK => hpT (connectedComponentIn_subset T x hpK)⟩
  rcases subsingleton_or_homeomorph_unitInterval_of_isJordanCurve hΓ hKcompact hKconn hKsub
      hKproper with hs | he
  · left
    refine ⟨x, ?_⟩
    ext y
    constructor
    · intro hy
      have h : (⟨y, hy⟩ : K) = ⟨x, mem_connectedComponentIn hx⟩ := hs.elim _ _
      simpa using congrArg Subtype.val h
    · intro hy
      have : y = x := mem_singleton_iff.mp hy
      subst y
      exact mem_connectedComponentIn hx
  · right
    obtain ⟨e⟩ := he
    let f : unitInterval → ℂ := fun t => e.symm t
    have hf : Continuous f := continuous_subtype_val.comp e.symm.continuous
    have hfi : Function.Injective f := Subtype.val_injective.comp e.symm.injective
    refine ⟨f, hf, hfi, ?_⟩
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact (e.symm t).2
    · intro hy
      exact ⟨e ⟨y, hy⟩, by simp [f]⟩

end LatticeProb
