/-
Ranking the elements of a finite set by an injective key.

`LatticeProb.card_filter_rank_lt` is the counting fact behind every rule of the
form "the arrivals at a site fill the holes there in increasing order of their
keys until one of the two runs out".  Give each element `p` of a finite set `A`
its rank, the number of elements of `A` whose key is smaller.  When the key is
injective on `A` the ranks run over `0, 1, …, |A| - 1` exactly once each, so the
elements of rank below `H` number `min |A| H`.  Nothing here is about the
lattice; it is stated for a finite set and a key in an arbitrary linear order.
-/
import Mathlib

namespace LatticeProb

open Finset

variable {α β : Type*} [DecidableEq α] [LinearOrder β]

/-- The rank of `p` in `A` for the key `f`: how many elements of `A` have a
strictly smaller key. -/
def rankIn (A : Finset α) (f : α → β) (p : α) : ℕ :=
  (A.filter fun q => f q < f p).card

theorem rankIn_lt_card {A : Finset α} {f : α → β} {p : α} (hp : p ∈ A) :
    rankIn A f p < A.card := by
  have hsub : (A.filter fun q => f q < f p) ⊆ A.erase p := by
    intro q hq
    rw [Finset.mem_filter] at hq
    refine Finset.mem_erase.mpr ⟨?_, hq.1⟩
    rintro rfl
    exact lt_irrefl _ hq.2
  calc rankIn A f p ≤ (A.erase p).card := Finset.card_le_card hsub
    _ < A.card := Finset.card_erase_lt_of_mem hp

omit [DecidableEq α] in
/-- Elements of `A` with different keys have different ranks. -/
theorem rankIn_lt_rankIn {A : Finset α} {f : α → β} {p q : α} (hp : p ∈ A) (_hq : q ∈ A)
    (h : f p < f q) : rankIn A f p < rankIn A f q := by
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2.trans h⟩
  · intro hsub
    have hpmem : p ∈ A.filter fun z => f z < f q := Finset.mem_filter.mpr ⟨hp, h⟩
    have := hsub hpmem
    rw [Finset.mem_filter] at this
    exact lt_irrefl _ this.2

theorem rankIn_injOn {A : Finset α} {f : α → β} (hf : Set.InjOn f A) :
    Set.InjOn (rankIn A f) A := by
  intro p hp q hq h
  by_contra hne
  rcases lt_trichotomy (f p) (f q) with hlt | heq | hgt
  · exact absurd h (ne_of_lt (rankIn_lt_rankIn hp hq hlt))
  · exact hne (hf hp hq heq)
  · exact absurd h.symm (ne_of_lt (rankIn_lt_rankIn hq hp hgt))

/-- The ranks of the elements of `A` are exactly `0, …, |A| - 1`. -/
theorem image_rankIn {A : Finset α} {f : α → β} (hf : Set.InjOn f A) :
    A.image (rankIn A f) = Finset.range A.card := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (rankIn_lt_card hp)
  · rw [Finset.card_range, Finset.card_image_of_injOn (rankIn_injOn hf)]

/-- Give each element of `A` the number of elements of `A` with a strictly
smaller key.  When the key is injective on `A`, exactly `min |A| H` elements get
a number below `H`. -/
theorem card_filter_rank_lt (A : Finset α) (f : α → β) (hf : Set.InjOn f A) (H : ℕ) :
    (A.filter fun p => (A.filter fun q => f q < f p).card < H).card = min A.card H := by
  classical
  have hkey : ∀ p, ((A.filter fun q => f q < f p).card < H) ↔ (rankIn A f p < H) := by
    intro p; rfl
  have hsub : (A.filter fun p => rankIn A f p < H) ⊆ A := Finset.filter_subset _ _
  have hinj : Set.InjOn (rankIn A f) (A.filter fun p => rankIn A f p < H) :=
    (rankIn_injOn hf).mono (by exact_mod_cast hsub)
  have h1 : ((A.filter fun p => rankIn A f p < H).image (rankIn A f)).card
      = (A.filter fun p => rankIn A f p < H).card := Finset.card_image_of_injOn hinj
  have h2 : (A.filter fun p => rankIn A f p < H).image (rankIn A f)
      = (A.image (rankIn A f)).filter fun k => k < H := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp.1, rfl⟩, hp.2⟩
    · rintro ⟨⟨p, hp, rfl⟩, hk⟩
      exact ⟨p, ⟨hp, hk⟩, rfl⟩
  have h3 : (Finset.range A.card).filter (fun k => k < H) = Finset.range (min A.card H) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  calc (A.filter fun p => (A.filter fun q => f q < f p).card < H).card
      = (A.filter fun p => rankIn A f p < H).card := by
        simp only [rankIn]
    _ = ((A.filter fun p => rankIn A f p < H).image (rankIn A f)).card := h1.symm
    _ = ((A.image (rankIn A f)).filter fun k => k < H).card := by rw [h2]
    _ = ((Finset.range A.card).filter fun k => k < H).card := by rw [image_rankIn hf]
    _ = (Finset.range (min A.card H)).card := by rw [h3]
    _ = min A.card H := Finset.card_range _

end LatticeProb
