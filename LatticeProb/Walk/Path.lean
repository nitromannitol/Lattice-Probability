/-
Elementary facts about a path on the lattice, and the law of the first `n`
steps of simple random walk.

The geometry first: a direction vector is never zero, the two signs of one
coordinate give opposite vectors, the walk starts at the origin and moves by
the direction vector of the letter it reads, the sites visited up to time `k`
are `pathRange w k`, and the edges crossed are named exactly once each by a
site together with a positive coordinate direction, so `pathEdges w k` has at
most `d` times as many elements as `pathRange w k`.

Then the law.  The first `n` steps of simple random walk are `n` independent
uniform directions, so the law of the first `n` steps is the uniform
probability measure on the finite type of words `Fin n → Dir d`.  Keeping the
horizon finite means every quantity below is a function on a finite type and no
measurability side condition can be silently dropped; `LatticeProb.Walk.Infinite`
carries the same walk on infinite paths and identifies the two.
-/
import Mathlib
import LatticeProb.Walk.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

/-- A direction vector is a unit coordinate vector, hence never zero.  A term of
`Dir d` carries a coordinate `a.1 : Fin d`, so no `0 < d` hypothesis is needed. -/
theorem dirVec_ne_zero {d : ℕ} (a : Dir d) : dirVec a ≠ 0 := by
  intro h
  have h' : dirVec a a.1 = (0 : Fin d → ℤ) a.1 := by rw [h]
  simp [dirVec] at h'
  split at h' <;> norm_num at h'

/-- The two signs of one coordinate give opposite vectors. -/
theorem dirVec_neg {d : ℕ} (c : Fin d) :
    dirVec ((c, false) : Dir d) = -dirVec ((c, true) : Dir d) := by
  funext j
  simp only [dirVec, Pi.neg_apply]
  split <;> norm_num

/-- Every direction vector is `± e_i` for its own coordinate `i`. -/
theorem dirVec_eq_or {d : ℕ} (a : Dir d) :
    dirVec a = dirVec ((a.1, true) : Dir d) ∨ dirVec a = -dirVec ((a.1, true) : Dir d) := by
  rcases a with ⟨c, b⟩
  cases b
  · exact Or.inr (dirVec_neg c)
  · exact Or.inl rfl

/-- The walk starts at the origin: `X_0 = 0`. -/
theorem pos_zero {d n : ℕ} (w : Fin n → Dir d) : pos w 0 = 0 := by
  simp [pos]

/-- One step of the walk moves by the direction vector of the letter just read:
`X_{i+1} = X_i + dirVec (w i)` for `i < n`. -/
theorem pos_succ {d n : ℕ} (w : Fin n → Dir d) (i : ℕ) (hi : i < n) :
    pos w (i + 1) = pos w i + dirVec (w ⟨i, hi⟩) := by
  have key : ∀ t : Fin n, (if (t : ℕ) < i + 1 then dirVec (w t) else 0)
      = (if (t : ℕ) < i then dirVec (w t) else 0)
        + (if t = (⟨i, hi⟩ : Fin n) then dirVec (w t) else 0) := by
    intro t
    by_cases h1 : (t : ℕ) < i
    · have h2 : t ≠ (⟨i, hi⟩ : Fin n) := by
        intro h; rw [h] at h1; simp at h1
      simp [h1, Nat.lt_succ_of_lt h1, h2]
    · by_cases h2 : (t : ℕ) = i
      · have h3 : t = (⟨i, hi⟩ : Fin n) := Fin.ext h2
        simp [h3]
      · have h4 : ¬ ((t : ℕ) < i + 1) := by omega
        have h5 : t ≠ (⟨i, hi⟩ : Fin n) := fun h => h2 (by rw [h])
        simp [h1, h4, h5]
  unfold pos
  rw [Finset.sum_congr rfl (fun t (_ : t ∈ Finset.univ) => key t), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (⟨i, hi⟩ : Fin n) (fun t => dirVec (w t))]
  simp

/-- Past the length of the word the position is frozen at the total displacement.
This is an artefact of the finite-horizon model of `LatticeProb.Walk.Basic`; the paper's
walk is never evaluated past time `n`. -/
theorem pos_of_length_le {d n : ℕ} (w : Fin n → Dir d) {k : ℕ} (hk : n ≤ k) :
    pos w k = ∑ t : Fin n, dirVec (w t) :=
  Finset.sum_congr rfl fun t _ => if_pos (lt_of_lt_of_le t.isLt hk)

/-- Every site visited at or before time `k` lies in `pathRange w k`. "The range at time `n` is the set of sites visited up to time `n`." -/
theorem pos_mem_pathRange {d n : ℕ} (w : Fin n → Dir d) {i k : ℕ} (h : i ≤ k) :
    pos w i ∈ pathRange w k :=
  mem_image_of_mem (pos w) (mem_range.mpr (by omega))

/-- `pathRange w k` always contains the starting site, so it is never empty. -/
theorem pathRange_nonempty {d n : ℕ} (w : Fin n → Dir d) (k : ℕ) : (pathRange w k).Nonempty :=
  ⟨pos w 0, pos_mem_pathRange w (Nat.zero_le k)⟩

/-- No edge has been crossed at time zero. "so that `pathEdges w 0 = ∅`". -/
theorem pathEdges_zero {d n : ℕ} (w : Fin n → Dir d) : pathEdges w 0 = ∅ := by
  simp [pathEdges]

/-- The position at any time `k ≤ n` is unchanged by dropping the last letter. -/
theorem pos_init {d n : ℕ} (w : Fin (n + 1) → Dir d) {k : ℕ} (hk : k ≤ n) :
    pos (Fin.init w) k = pos w k := by
  unfold pos
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.init, Fin.val_last, Nat.not_lt.mpr hk, if_false, add_zero]
  rfl

/-- The traversed-edge set at any time `k ≤ n` is unchanged by dropping the last
letter. -/
theorem pathEdges_init {d n : ℕ} (w : Fin (n + 1) → Dir d) {k : ℕ} (hk : k ≤ n) :
    pathEdges (Fin.init w) k = pathEdges w k := by
  unfold pathEdges
  rw [Nat.min_eq_left hk, Nat.min_eq_left (by omega : k ≤ n + 1)]
  refine Finset.image_congr ?_
  intro i hi
  have hik : i < k := Finset.mem_range.mp (Finset.mem_coe.mp hi)
  unfold edgeAt
  rw [pos_init w (by omega : i ≤ n), pos_init w (by omega : i + 1 ≤ n)]

/-- Both endpoints of a traversed edge are visited sites. -/
theorem mem_pathEdges_endpoint {d n : ℕ} (w : Fin n → Dir d) {k : ℕ} {e : Sym2 (Site d)}
    (he : e ∈ pathEdges w k) {x : Site d} (hx : x ∈ e) : x ∈ pathRange w k := by
  rw [pathEdges, Finset.mem_image] at he
  obtain ⟨i, hi, rfl⟩ := he
  have hik : i < min k n := Finset.mem_range.mp hi
  rw [edgeAt, Sym2.mem_iff] at hx
  rcases hx with rfl | rfl
  · exact pos_mem_pathRange w (by omega)
  · exact pos_mem_pathRange w (by omega)

/-- The positive-direction parametrization of the edges of `ℤ^d`: a site
together with a coordinate.  Each edge of `ℤ^d` is `edgeOf (y, c)` for exactly
one pair, namely its endpoint `y` with the smaller `c`-th coordinate. -/
def edgeOf {d : ℕ} (p : Site d × Fin d) : Sym2 (Site d) :=
  s(p.1, p.1 + dirVec (p.2, true))

/-- Every edge crossed at a time `i` that is a genuine step (`i < n`) is
`edgeOf (y, c)` for a visited site `y` and a coordinate `c`. -/
theorem edgeAt_eq_edgeOf {d n : ℕ} (w : Fin n → Dir d) {i k : ℕ} (hi : i < n) (hik : i < k) :
    ∃ y c, y ∈ pathRange w k ∧ edgeAt w i = edgeOf (y, c) := by
  have hstep : pos w (i + 1) = pos w i + dirVec (w ⟨i, hi⟩) := pos_succ w i hi
  rcases dirVec_eq_or (w ⟨i, hi⟩) with h | h
  · refine ⟨pos w i, (w ⟨i, hi⟩).1, pos_mem_pathRange w (by omega), ?_⟩
    rw [edgeAt, edgeOf, hstep, h]
  · refine ⟨pos w (i + 1), (w ⟨i, hi⟩).1, pos_mem_pathRange w (by omega), ?_⟩
    have h2 : pos w (i + 1) + dirVec (((w ⟨i, hi⟩).1, true) : Dir d) = pos w i := by
      rw [hstep, h]; abel
    rw [edgeAt, edgeOf]
    simp only [h2]
    exact Sym2.eq_swap

/-- `|pathEdges w k| ≤ d |pathRange w k|`. "Every subgraph of `ℤ^d` on `m` vertices has at most `dm` edges, so
`|E_n| ≤ d|R_n|`."

The proof is the injection `e ↦ (lower endpoint, coordinate)` of `pathEdges w k` into
`R_k × Fin d`.  Every index `i` contributing to `pathEdges w k` satisfies `i < min k n`,
hence both `i < n` (so step `i` is a genuine step and `edgeAt w i` is a real edge
of `ℤ^d`, not a loop) and `i < k` (so both its endpoints lie in `pathRange w k`).

No `0 < d` hypothesis is needed.  At `d = 0` the argument is vacuous rather than
special: `i < n` forces `Fin n` to be inhabited, so `w` supplies a term of
`Dir 0 = Fin 0 × Bool`, and the coordinate it names is the `c : Fin d` the
injection asks for.  This is why `pathEdges` must be cut off at
`min k n` for this to be true at all. -/
theorem card_edges_le_card_range {d n : ℕ} (w : Fin n → Dir d) (k : ℕ) :
    (pathEdges w k).card ≤ d * (pathRange w k).card := by
  classical
  have hsub : pathEdges w k ⊆ ((pathRange w k) ×ˢ (univ : Finset (Fin d))).image edgeOf := by
    intro e he
    rw [pathEdges, Finset.mem_image] at he
    obtain ⟨i, hi, rfl⟩ := he
    have hik : i < min k n := Finset.mem_range.mp hi
    obtain ⟨y, c, hy, hyc⟩ := edgeAt_eq_edgeOf w (by omega : i < n) (by omega : i < k)
    exact Finset.mem_image.mpr ⟨(y, c), Finset.mem_product.mpr ⟨hy, Finset.mem_univ _⟩, hyc.symm⟩
  calc (pathEdges w k).card
      ≤ (((pathRange w k) ×ˢ (univ : Finset (Fin d))).image edgeOf).card := Finset.card_le_card hsub
    _ ≤ ((pathRange w k) ×ˢ (univ : Finset (Fin d))).card := Finset.card_image_le
    _ = (pathRange w k).card * d := by rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    _ = d * (pathRange w k).card := Nat.mul_comm _ _

/-- After one step the range is `{0, X_1}` with `X_1 ≠ 0`, so `|R_1| = 2`. -/
theorem card_pathRange_one {d : ℕ} (w : Fin 1 → Dir d) : (pathRange w 1).card = 2 := by
  classical
  have h1 : pos w 1 = dirVec (w 0) := by
    have h := pos_succ w 0 (by omega : (0 : ℕ) < 1)
    rw [pos_zero] at h
    simpa using h
  have hne : pos w 0 ≠ pos w 1 := by
    rw [pos_zero, h1]
    exact fun h => dirVec_ne_zero (w 0) h.symm
  have hR : pathRange w 1 = {pos w 0, pos w 1} := by
    unfold pathRange
    rw [show (Finset.range 2 : Finset ℕ) = {0, 1} from by decide]
    rw [Finset.image_insert, Finset.image_singleton]
  rw [hR, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

/-! ### The law of the first `n` steps -/

/-- The law of the first `n` steps of simple random walk on `ℤ^d`, as a
probability mass function on direction words: the `2d` directions are equally
likely at every step, independently. -/
noncomputable def walkPMF (d n : ℕ) [NeZero d] : PMF (Fin n → Dir d) :=
  PMF.uniformOfFintype (Fin n → Dir d)

/-- The law of the first `n` steps of simple random walk, as a measure on the
finite set of direction words. -/
noncomputable def walkLaw (d n : ℕ) [NeZero d] :
    MeasureTheory.Measure (Fin n → Dir d) :=
  (walkPMF d n).toMeasure

instance walkLaw_isProbabilityMeasure (d n : ℕ) [NeZero d] :
    MeasureTheory.IsProbabilityMeasure (walkLaw d n) := by
  unfold walkLaw
  infer_instance

/-- Every word of `n` steps has the same probability, `(2d)^{-n}`. -/
theorem walkPMF_apply (d n : ℕ) [NeZero d] (w : Fin n → Dir d) :
    walkPMF d n w = (((2 * d) ^ n : ℕ) : ENNReal)⁻¹ := by
  rw [walkPMF, PMF.uniformOfFintype_apply]
  congr 2
  rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Fintype.card_fin]
  ring

end LatticeProb
