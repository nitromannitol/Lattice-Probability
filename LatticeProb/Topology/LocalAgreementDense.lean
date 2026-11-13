import LatticeProb.Topology.LocalAgreementChainsAt
import LatticeProb.Topology.ContinuousOfDiagonalLimit

/-!
# Gluing a continuous distance function with a pseudometric, from data on a dense set

Let `S ⊆ D` be dense in `D` and `z ∈ D`. Let `d₁` be continuous on `D × D` and satisfy, on `S` only, vanishing on the
diagonal, symmetry and the triangle inequality, and have fine chains at the pairs of points of `S`. Let `d₂` be
symmetric with the triangle inequality on `D`, tend to `0` along the diagonal at every point of `D`, and have fine
chains at the pairs of points of `S`. If `d₁ = d₂` on a small ball around every point `q ≠ z` of `D`, then `d₁ = d₂` on
`D × D` (`eqOn_of_local_agreement_of_dense`).

The metric axioms of `d₁` pass from `S` to `D` by continuity (`metricAxioms_of_dense`); `d₂` is continuous on `D × D`
by `continuousOn_uncurry_of_tendsto_diag`; the gluing along fine chains (`eqOn_of_local_agreement_of_fineChainsAt`)
gives the agreement on `S × S`, and continuity extends it to `D × D` (`eqOn_of_eqOn_dense`).
-/

open Set Filter Metric Topology
open scoped ENNReal

namespace LatticeProb.Topology

/-- Vanishing on the diagonal, symmetry and the triangle inequality of a function continuous on `D × D` pass from a set
`S ⊆ D` dense in `D` to `D`. -/
theorem metricAxioms_of_dense {α : Type*} [TopologicalSpace α] {D S : Set α} (hSD : S ⊆ D)
    (hdense : D ⊆ closure S) {d : α → α → ℝ≥0∞}
    (hd : ContinuousOn (fun p : α × α => d p.1 p.2) (D ×ˢ D))
    (hdiag : ∀ x ∈ S, d x x = 0) (hsymm : ∀ x ∈ S, ∀ y ∈ S, d x y = d y x)
    (htri : ∀ x ∈ S, ∀ y ∈ S, ∀ w ∈ S, d x w ≤ d x y + d y w) :
    (∀ x ∈ D, d x x = 0) ∧ (∀ x ∈ D, ∀ y ∈ D, d x y = d y x) ∧
      (∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, d x w ≤ d x y + d y w) := by
  refine ⟨?_, ?_, ?_⟩
  · have hc : ContinuousOn (fun x => d x x) D :=
      hd.comp (f := fun x : α => (x, x)) (by fun_prop : Continuous fun x : α => (x, x)).continuousOn
        (fun x hx => mk_mem_prod hx hx)
    intro x hx
    exact Set.EqOn.of_subset_closure (f := fun x => d x x) (g := fun _ => (0 : ℝ≥0∞)) hdiag hc
      continuousOn_const hSD hdense hx
  · have hswap : ContinuousOn (fun p : α × α => d p.2 p.1) (D ×ˢ D) :=
      hd.comp (f := Prod.swap) continuous_swap.continuousOn (fun p hp => ⟨hp.2, hp.1⟩)
    have hS : EqOn (fun p : α × α => d p.1 p.2) (fun p => d p.2 p.1) (S ×ˢ S) :=
      fun p hp => hsymm p.1 hp.1 p.2 hp.2
    have hcl : D ×ˢ D ⊆ closure (S ×ˢ S) := by
      rw [closure_prod_eq]
      exact prod_mono hdense hdense
    exact fun x hx y hy => hS.of_subset_closure hd hswap (prod_mono hSD hSD) hcl (mk_mem_prod hx hy)
  · intro x hx y hy w hw
    have hT : (x, y, w) ∈ closure (S ×ˢ S ×ˢ S) := by
      rw [closure_prod_eq, closure_prod_eq]
      exact ⟨hdense hx, hdense hy, hdense hw⟩
    have hxD : (x, y, w) ∈ D ×ˢ D ×ˢ D := ⟨hx, hy, hw⟩
    have hsub : S ×ˢ S ×ˢ S ⊆ D ×ˢ D ×ˢ D := prod_mono hSD (prod_mono hSD hSD)
    have hf : ContinuousOn (fun p : α × α × α => d p.1 p.2.2) (D ×ˢ D ×ˢ D) :=
      hd.comp (f := fun p : α × α × α => (p.1, p.2.2))
        (by fun_prop : Continuous fun p : α × α × α => (p.1, p.2.2)).continuousOn
        (fun p hp => ⟨hp.1, hp.2.2⟩)
    have hg₁ : ContinuousOn (fun p : α × α × α => d p.1 p.2.1) (D ×ˢ D ×ˢ D) :=
      hd.comp (f := fun p : α × α × α => (p.1, p.2.1))
        (by fun_prop : Continuous fun p : α × α × α => (p.1, p.2.1)).continuousOn
        (fun p hp => ⟨hp.1, hp.2.1⟩)
    have hg₂ : ContinuousOn (fun p : α × α × α => d p.2.1 p.2.2) (D ×ˢ D ×ˢ D) :=
      hd.comp (f := fun p : α × α × α => p.2) continuous_snd.continuousOn (fun p hp => hp.2)
    exact ContinuousWithinAt.closure_le (f := fun p : α × α × α => d p.1 p.2.2)
      (g := fun p => d p.1 p.2.1 + d p.2.1 p.2.2) hT
      ((hf _ hxD).mono hsub) (((hg₁ _ hxD).add (hg₂ _ hxD)).mono hsub)
      (fun p hp => htri p.1 hp.1 p.2.1 hp.2.1 p.2.2 hp.2.2)

/-- **Gluing from local agreement and data on a dense set.** Let `S ⊆ D` be dense in `D` and `z ∈ D`. Let `d₁` be
continuous on `D × D`, vanish on the diagonal of `S`, be symmetric and satisfy the triangle inequality on `S`, and have
fine chains at the pairs of points of `S`. Let `d₂` be symmetric with the triangle inequality on `D`, with
`d₂ w p → 0` as `w → p` in `D` for every `p ∈ D`, and have fine chains at the pairs of points of `S`. If `d₁ = d₂` on a
ball around every point `q ≠ z` of `D`, then `d₁ = d₂` on `D × D`. -/
theorem eqOn_of_local_agreement_of_dense {α : Type*} [PseudoMetricSpace α] {D S : Set α} {z : α}
    (hz : z ∈ D) (hSD : S ⊆ D) (hdense : D ⊆ closure S) {d₁ d₂ : α → α → ℝ≥0∞}
    (hd₁ : ContinuousOn (fun p : α × α => d₁ p.1 p.2) (D ×ˢ D))
    (hdiag₁ : ∀ x ∈ S, d₁ x x = 0) (hsymm₁ : ∀ x ∈ S, ∀ y ∈ S, d₁ x y = d₁ y x)
    (htri₁ : ∀ x ∈ S, ∀ y ∈ S, ∀ w ∈ S, d₁ x w ≤ d₁ x y + d₁ y w)
    (hch₁ : ∀ x ∈ S, ∀ y ∈ S, HasFineChainsAt D d₁ x y)
    (htri₂ : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, d₂ x w ≤ d₂ x y + d₂ y w)
    (hsymm₂ : ∀ x ∈ D, ∀ y ∈ D, d₂ x y = d₂ y x)
    (hdiag₂ : ∀ p ∈ D, Tendsto (fun w => d₂ w p) (𝓝[D] p) (𝓝 0))
    (hch₂ : ∀ x ∈ S, ∀ y ∈ S, HasFineChainsAt D d₂ x y)
    (hloc : ∀ q ∈ D, q ≠ z → ∃ s > 0, ∀ u ∈ ball q s, ∀ v ∈ ball q s, d₁ u v = d₂ u v) :
    ∀ x ∈ D, ∀ y ∈ D, d₁ x y = d₂ x y := by
  obtain ⟨hdiag₁', hsymm₁', htri₁'⟩ := metricAxioms_of_dense hSD hdense hd₁ hdiag₁ hsymm₁ htri₁
  have hc : ContinuousWithinAt (fun w => d₁ w z) D z :=
    (hd₁ (z, z) (mk_mem_prod hz hz)).comp (f := fun w : α => (w, z))
      (by fun_prop : Continuous fun w : α => (w, z)).continuousWithinAt (fun w hw => mk_mem_prod hw hz)
  have hroot₁ : Tendsto (fun w => d₁ w z) (𝓝[D] z) (𝓝 0) := by
    have h := hc.tendsto
    rwa [hdiag₁' z hz] at h
  exact eqOn_of_eqOn_dense hSD hdense hd₁ (continuousOn_uncurry_of_tendsto_diag htri₂ hsymm₂ hdiag₂)
    (eqOn_of_local_agreement_of_fineChainsAt hz htri₁' htri₂ hsymm₁' hsymm₂ hroot₁ (hdiag₂ z hz) hch₁ hch₂ hloc)

end LatticeProb.Topology
