/-
Elementary algebra of `LatticeProb.Network.HarmonicOn`: it is closed under
restriction, sums and scalar multiples; the network Laplacian written as a
signed neighbour sum; the discrete maximum principle at equality (a harmonic
vertex whose neighbours are all at most its own value has every neighbour
exactly equal); and two sign lemmas for a weighted zero-sum family, used to
locate a negative term forced by a large positive one.

Moved from Unique-Continuation-Planar, `UCPlanar/Support/Harmonic.lean`.
-/
import LatticeProb.Network.Basic

open scoped BigOperators Classical

namespace LatticeProb.Network

variable {V : Type*} {G : SimpleGraph V}

/-- The network Laplacian as the negative of the signed neighbour sum. -/
theorem laplacian_sign [G.LocallyFinite] (c : V → V → ℝ) (f : V → ℝ) (x : V) :
    ∑ y ∈ G.neighborFinset x, c x y * (f x - f y) = -netLaplacian G c f x := by
  classical
  simp only [netLaplacian, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- Harmonicity restricts to a subset. -/
theorem harmonic_mono [G.LocallyFinite] {c : V → V → ℝ} {f : V → ℝ} {S T : Set V}
    (h : HarmonicOn G c f S) (hTS : T ⊆ S) :
    HarmonicOn G c f T := by
  intro x hx
  exact h x (hTS hx)

/-- Harmonic functions add. -/
theorem harmonic_add [G.LocallyFinite] {c : V → V → ℝ} {f g : V → ℝ} {S : Set V}
    (hf : HarmonicOn G c f S) (hg : HarmonicOn G c g S) :
    HarmonicOn G c (f + g) S := by
  intro x hx
  rw [netLaplacian_add, hf x hx, hg x hx, add_zero]

/-- A scalar multiple of a harmonic function is harmonic. -/
theorem harmonic_smul [G.LocallyFinite] {c : V → V → ℝ} {f : V → ℝ} {S : Set V}
    (hf : HarmonicOn G c f S) (a : ℝ) :
    HarmonicOn G c (fun x => a * f x) S := by
  intro x hx
  rw [netLaplacian_smul, hf x hx, mul_zero]

/-- In a positively weighted zero-sum family, a term above `0` forces some
other term below `0`. -/
theorem weighted_opposite {ι : Type*} (s : Finset ι) (c f : ι → ℝ)
    (hc : ∀ i ∈ s, 0 < c i) (hzero : ∑ i ∈ s, c i * f i = 0)
    (i : ι) (hi : i ∈ s) (hfi : 0 < f i) : ∃ j ∈ s, f j < 0 := by
  classical
  by_contra h
  push Not at h
  have hp : 0 < ∑ j ∈ s, c j * f j :=
    Finset.sum_pos' (fun j hj => mul_nonneg (hc j hj).le (h j hj))
      ⟨i, hi, mul_pos (hc i hi) hfi⟩
  linarith

/-- **The discrete maximum principle at equality.**  At a harmonic vertex
whose neighbours are all at most its own value, every neighbour equals it
exactly (the mean-value property forces the inequality to be tight
termwise). -/
theorem maximum_neighbors [G.LocallyFinite] {c : V → V → ℝ} {f : V → ℝ}
    (hc : IsCond G c) (x : V)
    (hh : netLaplacian G c f x = 0)
    (hmax : ∀ y, G.Adj x y → f y ≤ f x) : ∀ y, G.Adj x y → f y = f x := by
  classical
  rw [netLaplacian] at hh
  have hn : ∀ y ∈ G.neighborFinset x, c x y * (f y - f x) ≤ 0 := by
    intro y hy
    have ha := (SimpleGraph.mem_neighborFinset G x y).mp hy
    exact mul_nonpos_of_nonneg_of_nonpos (hc.pos ha).le (sub_nonpos.mpr (hmax y ha))
  have hz := (Finset.sum_eq_zero_iff_of_nonpos hn).mp hh
  intro y hy
  have he := hz y ((SimpleGraph.mem_neighborFinset G x y).mpr hy)
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (hc.pos hy).ne')

/-- A weighted-average deviation bound: if a weighted zero-sum family has
conductances in a band `[lam, big]` and one term `f i` is large enough
relative to the band ratio and the family size, some other term is below
`-A`. -/
theorem band_opposite {ι : Type*} (s : Finset ι) (c f : ι → ℝ)
    (A lam big : ℝ) (hA : 0 ≤ A) (hlam : 0 < lam) (hbig : 0 ≤ big)
    (hc : ∀ i ∈ s, lam ≤ c i ∧ c i ≤ big) (hmean : ∑ i ∈ s, c i * f i = 0)
    (i : ι) (hi : i ∈ s) (hlarge : big * s.card * A < lam * f i) :
    ∃ j ∈ s, f j < -A := by
  classical
  by_contra hn
  push Not at hn
  have hc0 : ∀ j ∈ s, 0 ≤ c j := fun j hj => le_trans hlam.le (hc j hj).1
  have hb : ∀ j ∈ s, -big * A ≤ c j * f j := by
    intro j hj
    have h1 := mul_le_mul_of_nonneg_left (hn j hj) (hc0 j hj)
    have h2 := mul_le_mul_of_nonneg_right (hc j hj).2 hA
    nlinarith
  have hsum : ∑ j ∈ s, (c j * f j + big * A) = (s.card : ℝ) * big * A := by
    rw [Finset.sum_add_distrib, hmean, Finset.sum_const, nsmul_eq_mul]
    ring
  have hone : c i * f i + big * A ≤ ∑ j ∈ s, (c j * f j + big * A) :=
    Finset.single_le_sum (f := fun j => c j * f j + big * A)
      (fun j hj => by nlinarith [hb j hj]) hi
  rw [hsum] at hone
  have hfi : 0 < f i := by
    have hn0 : 0 ≤ big * (s.card : ℝ) * A := by positivity
    nlinarith
  have hweight := mul_le_mul_of_nonneg_right (hc i hi).1 hfi.le
  have hba : 0 ≤ big * A := mul_nonneg hbig hA
  nlinarith

end LatticeProb.Network
