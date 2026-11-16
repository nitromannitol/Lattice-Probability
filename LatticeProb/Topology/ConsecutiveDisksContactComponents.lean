import LatticeProb.Topology.ConsecutiveDiskIntersectionComponents
import LatticeProb.Topology.JordanDiskIntersectionBoundary
import LatticeProb.Topology.RegularClosedUnionDisjoint

/-! Bounded complementary components of unions of consecutive embedded disks. -/

open Set Metric Bornology

namespace LatticeProb

/-- If every consecutive union of a family of disks is a disk, then the union of two
nonadjacent disks has at most one bounded complementary component. -/
theorem bounded_complement_components_eq_of_consecutive_disks
    (K : ℕ → Set ℂ)
    (hK : ∀ k, Nonempty (closedBall (0 : ℂ) 1 ≃ₜ K k))
    (hsegments : ∀ a b : ℕ, a ≤ b →
      Nonempty (closedBall (0 : ℂ) 1 ≃ₜ ⋃ k ∈ Icc a b, K k))
    (hdis : ∀ a b, a ≠ b → Disjoint (interior (K a)) (interior (K b)))
    {i j : ℕ} (hij : i + 1 < j)
    {p q : ℂ} (hp : p ∈ (K i ∪ K j)ᶜ) (hq : q ∈ (K i ∪ K j)ᶜ)
    (hpb : IsBounded (connectedComponentIn (K i ∪ K j)ᶜ p))
    (hqb : IsBounded (connectedComponentIn (K i ∪ K j)ᶜ q)) :
    connectedComponentIn (K i ∪ K j)ᶜ p = connectedComponentIn (K i ∪ K j)ᶜ q := by
  let B := ⋃ k ∈ Icc (i + 1) (j - 1), K k
  have hregular : ∀ k, closure (interior (K k)) = K k := fun k =>
    closure_interior_of_homeomorph_closedDisk (hK k).some
  have hmiddle : ∀ a, (∀ k ∈ Icc (i + 1) (j - 1), a ≠ k) →
      Disjoint (interior B) (interior (K a)) := by
    intro a ha
    let F : Icc (i + 1) (j - 1) → Set ℂ := fun k => K k
    have hB : (⋃ k, F k) = B := by
      ext x
      simp [F, B]
    have hd : Disjoint (interior (⋃ k, F k)) (K a) :=
      disjoint_interior_iUnion_of_regularClosed (hregular a)
        (fun k => hregular k) (fun k => hdis a k (ha k k.2))
    rw [hB] at hd
    exact hd.mono_right interior_subset
  have hleft : Disjoint (interior B) (interior (K i)) := by
    apply hmiddle
    intro k hk
    simp only [mem_Icc] at hk
    omega
  have hright : Disjoint (interior B) (interior (K j)) := by
    apply hmiddle
    intro k hk
    simp only [mem_Icc] at hk
    omega
  have hunion : (K i ∪ K j) ∪ B = ⋃ k ∈ Icc i j, K k := by
    ext x
    simp only [mem_union, mem_iUnion, mem_Icc, B]
    constructor
    · rintro ((hx | hx) | ⟨k, ⟨hk₁, hk₂⟩, hx⟩)
      · exact ⟨i, ⟨le_rfl, by omega⟩, hx⟩
      · exact ⟨j, ⟨by omega, le_rfl⟩, hx⟩
      · exact ⟨k, ⟨by omega, by omega⟩, hx⟩
    · rintro ⟨k, ⟨hk₁, hk₂⟩, hx⟩
      by_cases hki : k = i
      · exact Or.inl (Or.inl (hki ▸ hx))
      by_cases hkj : k = j
      · exact Or.inl (Or.inr (hkj ▸ hx))
      · exact Or.inr ⟨k, ⟨by omega, by omega⟩, hx⟩
  have eB : closedBall (0 : ℂ) 1 ≃ₜ B := (hsegments (i + 1) (j - 1) (by omega)).some
  have eD : closedBall (0 : ℂ) 1 ≃ₜ ↥((K i ∪ K j) ∪ B) :=
    (hsegments i j (by omega)).some.trans (Homeomorph.setCongr hunion.symm)
  obtain ⟨hext, hunbounded⟩ := complex_embedded_closed_disk_compl_preconnected_unbounded eD
  exact bounded_complement_components_eq_of_embedded_middle_disk
    (hregular i) (hregular j) eB hext hunbounded hleft hright hp hq hpb hqb

end LatticeProb
