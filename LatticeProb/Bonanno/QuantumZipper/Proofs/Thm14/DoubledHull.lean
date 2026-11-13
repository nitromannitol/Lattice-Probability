/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm14.DoubledHull at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Loewner.Curves
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Order.IntermediateValue

/-!
# The doubled SLE hull has empty interior

Node F1 of `blueprint/EXT_JS_BLUEPRINT.md`. An arc in the plane has empty interior (standard;
cf. M. H. A. Newman, *Elements of the Topology of Plane Sets of Points*, Ch. V: no arc separates
the plane, in particular a point does not separate a disk). We use the following elementary
argument (our own write-up of the standard fact, no separate source formalized): if the arc
`γ '' [a,b]` contained a disk around an interior point `p = γ t₀`, a small circle around `p`
would be a connected set covered by the two closed subarcs `γ '' [a,t₀]`, `γ '' [t₀,b]`, meeting
both (intermediate value theorem) but not their intersection `{p}`.
-/

open Set Metric

namespace QuantumZipper

theorem interior_image_Icc_eq_empty_of_injOn {γ : ℝ → ℂ} {a b : ℝ}
    (hc : ContinuousOn γ (Icc a b)) (hi : InjOn γ (Icc a b)) :
    interior (γ '' Icc a b) = ∅ := by
  by_contra hne
  obtain ⟨z, hz⟩ := nonempty_iff_ne_empty.2 hne
  have hinf : (interior (γ '' Icc a b)).Infinite :=
    infinite_of_mem_nhds z (isOpen_interior.mem_nhds hz)
  obtain ⟨p, hp, hpab⟩ := (hinf.sdiff (toFinite {γ a, γ b})).nonempty
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hpab
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior p hp
  obtain ⟨t₀, ht₀, rfl⟩ := interior_subset hp
  have ha : a < t₀ := lt_of_le_of_ne ht₀.1 (by rintro rfl; exact hpab.1 rfl)
  have hb : t₀ < b := lt_of_le_of_ne ht₀.2 (by rintro rfl; exact hpab.2 rfl)
  have hda : 0 < dist (γ a) (γ t₀) := dist_pos.2 (Ne.symm hpab.1)
  have hdb : 0 < dist (γ b) (γ t₀) := dist_pos.2 (Ne.symm hpab.2)
  set ρ := min (r / 2) (min (dist (γ a) (γ t₀)) (dist (γ b) (γ t₀))) with hρ
  have hρ0 : 0 < ρ := lt_min (half_pos hr) (lt_min hda hdb)
  have hf : ContinuousOn (fun t => dist (γ t) (γ t₀)) (Icc a b) :=
    continuous_dist.comp_continuousOn (hc.prodMk continuousOn_const)
  -- the circle of radius `ρ`
  have hS : IsPreconnected (sphere (γ t₀) ρ) :=
    isPreconnected_sphere (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) _ _
  have hSsub : sphere (γ t₀) ρ ⊆ γ '' Icc a t₀ ∪ γ '' Icc t₀ b := by
    intro q hq
    have : q ∈ ball (γ t₀) r := by
      rw [mem_sphere] at hq
      rw [mem_ball, hq]
      exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr)
    rw [← image_union, Icc_union_Icc_eq_Icc ht₀.1 ht₀.2]
    exact interior_subset (hball this)
  have h1 : ((sphere (γ t₀) ρ) ∩ γ '' Icc a t₀).Nonempty := by
    obtain ⟨s, hs, hs'⟩ := intermediate_value_Icc' ht₀.1 (hf.mono (Icc_subset_Icc le_rfl ht₀.2))
      (show ρ ∈ Icc _ _ by
        simp only [dist_self]
        exact ⟨hρ0.le, (min_le_right _ _).trans (min_le_left _ _)⟩)
    exact ⟨γ s, mem_sphere.2 hs', s, hs, rfl⟩
  have h2 : ((sphere (γ t₀) ρ) ∩ γ '' Icc t₀ b).Nonempty := by
    obtain ⟨s, hs, hs'⟩ := intermediate_value_Icc ht₀.2 (hf.mono (Icc_subset_Icc ht₀.1 le_rfl))
      (show ρ ∈ Icc _ _ by
        simp only [dist_self]
        exact ⟨hρ0.le, (min_le_right _ _).trans (min_le_right _ _)⟩)
    exact ⟨γ s, mem_sphere.2 hs', s, hs, rfl⟩
  have hcl1 : IsClosed (γ '' Icc a t₀) :=
    ((isCompact_Icc).image_of_continuousOn (hc.mono (Icc_subset_Icc le_rfl ht₀.2))).isClosed
  have hcl2 : IsClosed (γ '' Icc t₀ b) :=
    ((isCompact_Icc).image_of_continuousOn (hc.mono (Icc_subset_Icc ht₀.1 le_rfl))).isClosed
  obtain ⟨q, hqS, ⟨u, hu, rfl⟩, ⟨v, hv, huv⟩⟩ :=
    isPreconnected_closed_iff.1 hS _ _ hcl1 hcl2 hSsub h1 h2
  have huv' : v = u :=
    hi ⟨ht₀.1.trans hv.1, hv.2⟩ ⟨hu.1, hu.2.trans ht₀.2⟩ huv
  have hut : u = t₀ := le_antisymm hu.2 (huv' ▸ hv.1)
  subst hut
  rw [mem_sphere, dist_self] at hqS
  exact hρ0.ne hqS

/-- Node F1: the closure of a simple-curve hull together with its complex conjugate has empty
interior. -/
theorem interior_doubledHull_eq_empty {K : Set ℂ} (hK : IsSimpleCurveHull K) :
    interior (closure K ∪ (starRingEnd ℂ) '' closure K) = ∅ := by
  obtain ⟨γ, hc, hi, -, -, rfl⟩ := hK
  have hcl : IsClosed (γ '' Icc 0 1) := (isCompact_Icc.image_of_continuousOn hc).isClosed
  have hsub : closure (γ '' Ioc 0 1) ⊆ γ '' Icc 0 1 :=
    closure_minimal (image_mono Ioc_subset_Icc_self) hcl
  have hc' : ContinuousOn ((starRingEnd ℂ) ∘ γ) (Icc 0 1) :=
    Complex.continuous_conj.comp_continuousOn hc
  have hi' : InjOn ((starRingEnd ℂ) ∘ γ) (Icc 0 1) :=
    (star_injective.comp_injOn hi)
  have hcl' : IsClosed (((starRingEnd ℂ) ∘ γ) '' Icc 0 1) :=
    (isCompact_Icc.image_of_continuousOn hc').isClosed
  have hsub' : (starRingEnd ℂ) '' closure (γ '' Ioc 0 1) ⊆ ((starRingEnd ℂ) ∘ γ) '' Icc 0 1 := by
    rw [image_comp]; exact image_mono hsub
  apply subset_empty_iff.1
  calc interior (closure (γ '' Ioc 0 1) ∪ (starRingEnd ℂ) '' closure (γ '' Ioc 0 1))
      ⊆ interior (γ '' Icc 0 1 ∪ ((starRingEnd ℂ) ∘ γ) '' Icc 0 1) :=
        interior_mono (union_subset_union hsub hsub')
    _ = ∅ := by
        rw [interior_union_isClosed_of_interior_empty hcl
          (interior_image_Icc_eq_empty_of_injOn hc' hi')]
        exact interior_image_Icc_eq_empty_of_injOn hc hi

end QuantumZipper
