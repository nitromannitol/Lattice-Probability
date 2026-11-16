import LatticeProb.Topology.DirectedIntersectionGaps
import Mathlib.Order.Zorn

/-! # Minimal closed parameter sets with equal-image gaps -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A continuous map on the real line has an inclusion-minimal closed subset of
an interval containing its endpoints on which gap endpoints have equal images. -/
theorem exists_minimal_closed_equal_gap {Y : Type*} [MetricSpace Y]
    (f : ℝ → Y) (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    ∃ K : Set ℝ, K ⊆ Icc a b ∧ IsClosed K ∧ a ∈ K ∧ b ∈ K ∧
      (∀ u ∈ K, ∀ v ∈ K, u < v →
        (∀ w ∈ K, ¬ (u < w ∧ w < v)) → f u = f v) ∧
      ∀ L : Set ℝ, L ⊆ K → IsClosed L → a ∈ L → b ∈ L →
        (∀ u ∈ L, ∀ v ∈ L, u < v →
          (∀ w ∈ L, ¬ (u < w ∧ w < v)) → f u = f v) → L = K := by
  classical
  let S : Set (Set ℝ) := {K | K ⊆ Icc a b ∧ IsClosed K ∧ a ∈ K ∧ b ∈ K ∧
    ∀ u ∈ K, ∀ v ∈ K, u < v →
      (∀ w ∈ K, ¬ (u < w ∧ w < v)) → f u = f v}
  have hseed : Icc a b ∈ S := by
    refine ⟨Subset.rfl, isClosed_Icc, ⟨le_rfl, hab⟩, ⟨hab, le_rfl⟩, ?_⟩
    intro u hu v hv huv hgap
    have hm : (u + v) / 2 ∈ Icc a b := by
      constructor <;> linarith [hu.1, hv.2]
    exact False.elim (hgap ((u + v) / 2) hm (by constructor <;> linarith))
  obtain ⟨K, _, hmin⟩ := zorn_superset_nonempty S (fun c hcS hc hne => by
    let ι := c
    have : Nonempty ι := hne.to_subtype
    let F : ι → Set ℝ := fun i => i.1
    have hclosed (i : ι) : IsClosed (F i) := (hcS i.2).2.1
    have hdir : Directed (· ⊇ ·) F := by
      intro i j
      obtain hij | hji := hc.total i.2 j.2
      · exact ⟨i, Subset.rfl, hij⟩
      · exact ⟨j, hji, Subset.rfl⟩
    let I := ⋂ i, F i
    let i₀ : ι := Classical.choice inferInstance
    have hsub : I ⊆ Icc a b := (iInter_subset F i₀).trans (hcS i₀.2).1
    have haI : a ∈ I := mem_iInter.mpr fun i => (hcS i.2).2.2.1
    have hbI : b ∈ I := mem_iInter.mpr fun i => (hcS i.2).2.2.2.1
    have hgapI : ∀ u ∈ I, ∀ v ∈ I, u < v →
        (∀ w ∈ I, ¬ (u < w ∧ w < v)) → f u = f v := by
      intro u hu v hv huv hbetween
      exact equal_of_gap_iInter F f hclosed hdir (fun i => (hcS i.2).2.2.2.2)
        hu hv huv hbetween hf.continuousAt hf.continuousAt
    refine ⟨I, ⟨hsub, isClosed_iInter hclosed, haI, hbI, hgapI⟩, ?_⟩
    intro L hLc
    exact iInter_subset F ⟨L, hLc⟩) (Icc a b) hseed
  refine ⟨K, hmin.prop.1, hmin.prop.2.1, hmin.prop.2.2.1,
    hmin.prop.2.2.2.1, hmin.prop.2.2.2.2, ?_⟩
  intro L hLK hclosed ha hb hgap
  exact (hmin.eq_of_ge ⟨hLK.trans hmin.prop.1, hclosed, ha, hb, hgap⟩ hLK).symm

end LatticeProb
