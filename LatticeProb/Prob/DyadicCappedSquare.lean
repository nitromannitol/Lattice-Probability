import LatticeProb.Prob.DyadicSystemSquares
import LatticeProb.Euclidean.CappedSquare

/-!
# The largest square of bounded mass in a dyadic system of the plane

For the dyadic system of the plane with scale `s` and compatible offset sequences `o₁`, `o₂`
(`LatticeProb.Prob.DyadicSystemSquares`), this file verifies the hypotheses of the general results
of `LatticeProb.Euclidean.CappedSquare` on the square `Ŝ_m^w` of Gwynne, Miller and Sheffield
(*An invariance principle for ergodic scale-free random environments*, arXiv 1807.07515, (2.1)
and Lemma 2.2):

* two squares of the system are nested or have disjoint interiors (`dyadicSquares_nest`), and each
  square is the closure of its interior (`closure_interior_cornerSquare`);
* for a point `w` lying on no grid line (`IsOffGrid`), the squares of the system containing `w`
  are exactly the squares `squareAt s o₁ o₂ j w`, `j ∈ ℤ`, of the generations `j`, and they
  increase with `j` (`eq_squareAt_of_mem`, `squareAt_mono`); `w` lies in the interior of each.

Consequently, for any mass function `ν` strictly increasing along this chain, `squareAt j w` is
`Ŝ_m^w` exactly for `m ∈ [ν (squareAt j w), ν (squareAt (j + 1) w))`
(`isCappedSquare_squareAt_iff`), and `Ŝ_m^{w'} = Ŝ_m^w` for every `w'` in the interior of
`Ŝ_m^w` (`cappedSquare_eq_of_mem_interior_dyadic`).
-/

open Set Complex
open scoped ENNReal

namespace LatticeProb.DyadicOffset

/-! ### One coordinate -/

/-- The left end of the interval `[a, a + p)` of the progression `c + p ℤ` that contains `x`. -/
noncomputable def latticeFloor (c p x : ℝ) : ℝ := c + ⌊(x - c) / p⌋ * p

theorem latticeFloor_mem (c p x : ℝ) : latticeFloor c p x ∈ shiftedLattice c p :=
  ⟨⌊(x - c) / p⌋, rfl⟩

theorem latticeFloor_le {p : ℝ} (hp : 0 < p) (c x : ℝ) : latticeFloor c p x ≤ x := by
  have h1 := mul_le_mul_of_nonneg_right (Int.floor_le ((x - c) / p)) hp.le
  rw [div_mul_cancel₀ _ hp.ne'] at h1
  unfold latticeFloor
  linarith

theorem lt_latticeFloor_add {p : ℝ} (hp : 0 < p) (c x : ℝ) : x < latticeFloor c p x + p := by
  have h1 := mul_lt_mul_of_pos_right (Int.lt_floor_add_one ((x - c) / p)) hp
  rw [div_mul_cancel₀ _ hp.ne', add_mul, one_mul] at h1
  unfold latticeFloor
  linarith

/-- A point `a` of the progression `c + p ℤ` with `a ≤ x < a + p` is `latticeFloor c p x`. -/
theorem eq_latticeFloor {c p a x : ℝ} (hp : 0 < p) (ha : a ∈ shiftedLattice c p) (h1 : a ≤ x)
    (h2 : x < a + p) : a = latticeFloor c p x := by
  obtain ⟨n, rfl⟩ := ha
  have hfl : ⌊(x - c) / p⌋ = n := by
    rw [Int.floor_eq_iff, le_div_iff₀ hp, div_lt_iff₀ hp, add_mul, one_mul]
    constructor <;> linarith
  rw [latticeFloor, hfl]

theorem exists_eq_add_intMul_of_mem {c p a a' : ℝ} (ha : a ∈ shiftedLattice c p)
    (ha' : a' ∈ shiftedLattice c p) : ∃ n : ℤ, a = a' + n * p := by
  obtain ⟨k, rfl⟩ := ha
  obtain ⟨k', rfl⟩ := ha'
  exact ⟨k - k', by push_cast; ring⟩

theorem add_mem_shiftedLattice {c p a : ℝ} (ha : a ∈ shiftedLattice c p) :
    a + p ∈ shiftedLattice c p := by
  obtain ⟨k, rfl⟩ := ha
  exact ⟨k + 1, by push_cast; ring⟩

/-- Two intervals `[a, a + p]` and `[a', a' + N p]` with ends `a, a'` in the same progression
`c + p ℤ` are nested or have disjoint interiors. -/
theorem Icc_subset_or_disjoint_Ioo {c p a a' : ℝ} (hp : 0 < p) (N : ℕ)
    (ha : a ∈ shiftedLattice c p) (ha' : a' ∈ shiftedLattice c p) :
    Icc a (a + p) ⊆ Icc a' (a' + N * p) ∨ Disjoint (Ioo a (a + p)) (Ioo a' (a' + N * p)) := by
  obtain ⟨n, hn⟩ := exists_eq_add_intMul_of_mem ha ha'
  rcases lt_or_ge n 0 with h0 | h0
  · right
    have h1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    have h2 : a + p ≤ a' := by nlinarith
    exact disjoint_left.2 fun x hx hx' => by linarith [hx.2, hx'.1]
  · rcases lt_or_ge n (N : ℤ) with hN | hN
    · left
      have h1 : (n : ℝ) + 1 ≤ N := by exact_mod_cast (show n + 1 ≤ (N : ℤ) by omega)
      have h0' : (0 : ℝ) ≤ n := by exact_mod_cast h0
      have h2 : a' ≤ a := by nlinarith
      have h3 : a + p ≤ a' + N * p := by nlinarith
      exact Icc_subset_Icc h2 h3
    · right
      have h1 : (N : ℝ) ≤ n := by exact_mod_cast hN
      have h2 : a' + N * p ≤ a := by nlinarith
      exact disjoint_left.2 fun x hx hx' => by linarith [hx.1, hx'.2]

/-- The grid of generation `j + 1` is contained in the grid of generation `j`. -/
theorem gridPoints_succ_subset {o : ℕ → ℝ} (ho : IsCompatible o) (s : ℝ) (j : ℤ) :
    gridPoints s o (j + 1) ⊆ gridPoints s o j := by
  intro x hx
  simp only [gridPoints, mem_shiftedLattice] at hx ⊢
  obtain ⟨n, rfl⟩ := hx
  have hP : (2 : ℝ) ^ (s + ((j + 1 : ℤ) : ℝ)) = 2 * (2 : ℝ) ^ (s + (j : ℝ)) := by
    rw [show s + ((j + 1 : ℤ) : ℝ) = (s + j) + 1 by push_cast; ring, Real.rpow_add two_pos,
      Real.rpow_one]
    ring
  rcases lt_or_ge j 0 with hj | hj
  · have h1 : (j + 1).toNat = j.toNat := by omega
    refine ⟨2 * n, ?_⟩
    rw [h1, hP]
    push_cast
    ring
  · obtain ⟨k, hk⟩ := ho j.toNat
    have h1 : (j + 1).toNat = j.toNat + 1 := by omega
    have h2 : (2 : ℝ) ^ s * 2 ^ j.toNat = (2 : ℝ) ^ (s + (j : ℝ)) := by
      have := two_rpow_mul_two_pow_toNat s j
      rwa [show (-j).toNat = 0 by omega, pow_zero, one_mul] at this
    refine ⟨-k + 2 * n, ?_⟩
    rw [h1, hk, hP]
    push_cast
    linear_combination (-(k : ℝ)) * h2

theorem gridPoints_subset_of_le {o : ℕ → ℝ} (ho : IsCompatible o) (s : ℝ) {j j' : ℤ}
    (h : j ≤ j') : gridPoints s o j' ⊆ gridPoints s o j := by
  obtain ⟨k, rfl⟩ := Int.le.dest h
  clear h
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show j + ((k + 1 : ℕ) : ℤ) = (j + k) + 1 by push_cast; ring]
    exact (gridPoints_succ_subset ho s _).trans ih

theorem two_rpow_add_natCast (s : ℝ) (j : ℤ) (k : ℕ) :
    (2 : ℝ) ^ (s + ((j + k : ℤ) : ℝ)) = ((2 ^ k : ℕ) : ℝ) * (2 : ℝ) ^ (s + (j : ℝ)) := by
  rw [show s + ((j + k : ℤ) : ℝ) = (s + j) + (k : ℝ) by push_cast; ring, Real.rpow_add two_pos,
    Real.rpow_natCast]
  push_cast
  ring

/-- Grid intervals of generations `j ≤ j'` are nested or have disjoint interiors. -/
theorem gridInterval_nest {o : ℕ → ℝ} (ho : IsCompatible o) (s : ℝ) {j j' : ℤ} (hjj : j ≤ j')
    {a a' : ℝ} (ha : a ∈ gridPoints s o j) (ha' : a' ∈ gridPoints s o j') :
    Icc a (a + (2 : ℝ) ^ (s + (j : ℝ))) ⊆ Icc a' (a' + (2 : ℝ) ^ (s + (j' : ℝ))) ∨
      Disjoint (Ioo a (a + (2 : ℝ) ^ (s + (j : ℝ))))
        (Ioo a' (a' + (2 : ℝ) ^ (s + (j' : ℝ)))) := by
  have ha'' := gridPoints_subset_of_le ho s hjj ha'
  obtain ⟨k, rfl⟩ := Int.le.dest hjj
  rw [two_rpow_add_natCast]
  exact Icc_subset_or_disjoint_Ioo (by positivity) (2 ^ k) ha ha''

/-! ### Squares -/

theorem cornerSquare_eq_reProdIm (a b ℓ : ℝ) :
    cornerSquare a b ℓ = Icc a (a + ℓ) ×ℂ Icc b (b + ℓ) := by
  ext z
  simp only [mem_cornerSquare, mem_reProdIm, mem_Icc, and_assoc]

theorem interior_cornerSquare (a b ℓ : ℝ) :
    interior (cornerSquare a b ℓ) = Ioo a (a + ℓ) ×ℂ Ioo b (b + ℓ) := by
  rw [cornerSquare_eq_reProdIm, interior_reProdIm, interior_Icc, interior_Icc]

theorem closure_interior_cornerSquare (a b : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    closure (interior (cornerSquare a b ℓ)) = cornerSquare a b ℓ := by
  rw [interior_cornerSquare, closure_reProdIm, closure_Ioo (lt_add_of_pos_right a hℓ).ne,
    closure_Ioo (lt_add_of_pos_right b hℓ).ne, cornerSquare_eq_reProdIm]

variable {s : ℝ} {o₁ o₂ : ℕ → ℝ}

/-- Squares of generations `j ≤ j'` are nested or have disjoint interiors. -/
theorem generationSquares_nest (h₁ : IsCompatible o₁) (h₂ : IsCompatible o₂) {j j' : ℤ}
    (hjj : j ≤ j') {S S' : Set ℂ} (hS : S ∈ generationSquares s o₁ o₂ j)
    (hS' : S' ∈ generationSquares s o₁ o₂ j') :
    S ⊆ S' ∨ Disjoint (interior S) (interior S') := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hS
  obtain ⟨a', ha', b', hb', rfl⟩ := hS'
  rw [interior_cornerSquare, interior_cornerSquare, cornerSquare_eq_reProdIm,
    cornerSquare_eq_reProdIm]
  rcases gridInterval_nest h₁ s hjj ha ha' with hA | hA
  · rcases gridInterval_nest h₂ s hjj hb hb' with hB | hB
    · exact Or.inl fun z hz => ⟨hA hz.1, hB hz.2⟩
    · exact Or.inr (disjoint_left.2 fun z hz hz' => disjoint_left.1 hB hz.2 hz'.2)
  · exact Or.inr (disjoint_left.2 fun z hz hz' => disjoint_left.1 hA hz.1 hz'.1)

/-- Two squares of a dyadic system with compatible offsets are nested or have disjoint
interiors. -/
theorem dyadicSquares_nest (h₁ : IsCompatible o₁) (h₂ : IsCompatible o₂) :
    ∀ S ∈ dyadicSquares s o₁ o₂, ∀ S' ∈ dyadicSquares s o₁ o₂,
      S ⊆ S' ∨ S' ⊆ S ∨ Disjoint (interior S) (interior S') := by
  intro S hS S' hS'
  simp only [dyadicSquares, mem_iUnion] at hS hS'
  obtain ⟨j, hj⟩ := hS
  obtain ⟨j', hj'⟩ := hS'
  rcases le_total j j' with h | h
  · rcases generationSquares_nest h₁ h₂ h hj hj' with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)
  · rcases generationSquares_nest h₁ h₂ h hj' hj with h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1.symm)

theorem dyadicSquares_subset_closure_interior :
    ∀ S ∈ dyadicSquares s o₁ o₂, S ⊆ closure (interior S) := by
  intro S hS
  simp only [dyadicSquares, mem_iUnion] at hS
  obtain ⟨j, a, -, b, -, rfl⟩ := hS
  rw [closure_interior_cornerSquare a b (by positivity)]

/-! ### The chain of squares containing a point -/

/-- The left end of the grid interval of generation `j` containing `x`. -/
noncomputable def gridFloor (s : ℝ) (o : ℕ → ℝ) (j : ℤ) (x : ℝ) : ℝ :=
  latticeFloor (-((2 : ℝ) ^ s * o j.toNat)) ((2 : ℝ) ^ (s + (j : ℝ))) x

theorem gridFloor_mem (s : ℝ) (o : ℕ → ℝ) (j : ℤ) (x : ℝ) : gridFloor s o j x ∈ gridPoints s o j :=
  latticeFloor_mem _ _ _

/-- The square of generation `j` whose lower left corner is formed by the left ends of the grid
intervals containing `re w` and `im w`; it contains `w`. -/
noncomputable def squareAt (s : ℝ) (o₁ o₂ : ℕ → ℝ) (j : ℤ) (w : ℂ) : Set ℂ :=
  cornerSquare (gridFloor s o₁ j w.re) (gridFloor s o₂ j w.im) ((2 : ℝ) ^ (s + (j : ℝ)))

/-- `w` lies on no grid line of the dyadic system: for every generation, neither coordinate of
`w` is a grid point. -/
def IsOffGrid (s : ℝ) (o₁ o₂ : ℕ → ℝ) (w : ℂ) : Prop :=
  ∀ j : ℤ, w.re ∉ gridPoints s o₁ j ∧ w.im ∉ gridPoints s o₂ j

theorem squareAt_mem_generationSquares (j : ℤ) (w : ℂ) :
    squareAt s o₁ o₂ j w ∈ generationSquares s o₁ o₂ j :=
  ⟨_, gridFloor_mem s o₁ j w.re, _, gridFloor_mem s o₂ j w.im, rfl⟩

theorem squareAt_mem_dyadicSquares (j : ℤ) (w : ℂ) :
    squareAt s o₁ o₂ j w ∈ dyadicSquares s o₁ o₂ :=
  mem_iUnion.2 ⟨j, squareAt_mem_generationSquares j w⟩

theorem mem_squareAt (j : ℤ) (w : ℂ) : w ∈ squareAt s o₁ o₂ j w := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (s + (j : ℝ)) := by positivity
  exact ⟨latticeFloor_le hp _ _, (lt_latticeFloor_add hp _ _).le, latticeFloor_le hp _ _,
    (lt_latticeFloor_add hp _ _).le⟩

theorem mem_interior_squareAt {w : ℂ} (hw : IsOffGrid s o₁ o₂ w) (j : ℤ) :
    w ∈ interior (squareAt s o₁ o₂ j w) := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (s + (j : ℝ)) := by positivity
  rw [squareAt, interior_cornerSquare]
  refine mem_reProdIm.2 ⟨⟨lt_of_le_of_ne (latticeFloor_le hp _ _) fun h => (hw j).1 ?_,
    lt_latticeFloor_add hp _ _⟩, ⟨lt_of_le_of_ne (latticeFloor_le hp _ _) fun h => (hw j).2 ?_,
    lt_latticeFloor_add hp _ _⟩⟩
  · rw [← h]
    exact gridFloor_mem s o₁ j w.re
  · rw [← h]
    exact gridFloor_mem s o₂ j w.im

/-- Every square of the system containing an off-grid point `w` is one of the squares
`squareAt s o₁ o₂ j w`. -/
theorem eq_squareAt_of_mem {w : ℂ} (hw : IsOffGrid s o₁ o₂ w) {S : Set ℂ}
    (hS : S ∈ dyadicSquares s o₁ o₂) (hwS : w ∈ S) : ∃ j, S = squareAt s o₁ o₂ j w := by
  simp only [dyadicSquares, mem_iUnion] at hS
  obtain ⟨j, a, ha, b, hb, rfl⟩ := hS
  have hp : (0 : ℝ) < (2 : ℝ) ^ (s + (j : ℝ)) := by positivity
  obtain ⟨h1, h2, h3, h4⟩ := hwS
  have h2' : w.re < a + (2 : ℝ) ^ (s + (j : ℝ)) :=
    lt_of_le_of_ne h2 fun h => (hw j).1 (h ▸ add_mem_shiftedLattice ha)
  have h4' : w.im < b + (2 : ℝ) ^ (s + (j : ℝ)) :=
    lt_of_le_of_ne h4 fun h => (hw j).2 (h ▸ add_mem_shiftedLattice hb)
  have hA : a = gridFloor s o₁ j w.re := eq_latticeFloor hp ha h1 h2'
  have hB : b = gridFloor s o₂ j w.im := eq_latticeFloor hp hb h3 h4'
  subst hA hB
  exact ⟨j, rfl⟩

/-- For compatible offsets, the squares containing an off-grid point increase with the
generation. -/
theorem squareAt_mono (h₁ : IsCompatible o₁) (h₂ : IsCompatible o₂) {w : ℂ}
    (hw : IsOffGrid s o₁ o₂ w) : Monotone fun j => squareAt s o₁ o₂ j w := by
  intro j j' hjj
  rcases generationSquares_nest h₁ h₂ hjj (squareAt_mem_generationSquares j w)
      (squareAt_mem_generationSquares j' w) with h | h
  · exact h
  · exact absurd (mem_interior_squareAt hw j')
      (disjoint_left.1 h (mem_interior_squareAt hw j))

/-! ### `Ŝ_m^w` in the dyadic system -/

open CappedSquare

/-- IP Lemma 2.2, first part, for the dyadic system: if the mass is strictly increasing along the
squares containing the off-grid point `w`, the square of generation `j` containing `w` is
`Ŝ_m^w` exactly for `m ∈ [ν (squareAt j w), ν (squareAt (j + 1) w))`. -/
theorem isCappedSquare_squareAt_iff (h₁ : IsCompatible o₁) (h₂ : IsCompatible o₂) {w : ℂ}
    (hw : IsOffGrid s o₁ o₂ w) {ν : Set ℂ → ℝ≥0∞} {m : ℝ≥0∞}
    (hν : StrictMono fun j => ν (squareAt s o₁ o₂ j w)) (j : ℤ) :
    IsCappedSquare (dyadicSquares s o₁ o₂) ν m w (squareAt s o₁ o₂ j w) ↔
      m ∈ Ico (ν (squareAt s o₁ o₂ j w)) (ν (squareAt s o₁ o₂ (j + 1) w)) :=
  isCappedSquare_chain_iff (squareAt_mono h₁ h₂ hw) (fun j => squareAt_mem_dyadicSquares j w)
    (fun j => mem_squareAt j w) (fun _ hS hwS => eq_squareAt_of_mem hw hS hwS) hν j

/-- Existence of `Ŝ_m^w` at an off-grid point: if the mass is monotone along the squares
containing `w`, at most `m` for some generation and above `m` for another, then `Ŝ_m^w` is the
square of the largest generation of mass at most `m`. -/
theorem exists_isCappedSquare_squareAt (h₁ : IsCompatible o₁) (h₂ : IsCompatible o₂) {w : ℂ}
    (hw : IsOffGrid s o₁ o₂ w) {ν : Set ℂ → ℝ≥0∞} {m : ℝ≥0∞}
    (hν : Monotone fun j => ν (squareAt s o₁ o₂ j w))
    (hlow : ∃ j, ν (squareAt s o₁ o₂ j w) ≤ m) (hhigh : ∃ j, m < ν (squareAt s o₁ o₂ j w)) :
    ∃ j, ν (squareAt s o₁ o₂ j w) ≤ m ∧ m < ν (squareAt s o₁ o₂ (j + 1) w) ∧
      IsCappedSquare (dyadicSquares s o₁ o₂) ν m w (squareAt s o₁ o₂ j w) :=
  exists_isCappedSquare_chain (squareAt_mono h₁ h₂ hw) (fun j => squareAt_mem_dyadicSquares j w)
    (fun j => mem_squareAt j w) (fun _ hS hwS => eq_squareAt_of_mem hw hS hwS) hν hlow hhigh

/-- IP Lemma 2.2, second part, for the dyadic system: `Ŝ_m^w = Ŝ_m^z` for every `w` in the
interior of `Ŝ_m^z`. -/
theorem cappedSquare_eq_of_mem_interior_dyadic (h₁ : IsCompatible o₁) (h₂ : IsCompatible o₂)
    {ν : Set ℂ → ℝ≥0∞} {m : ℝ≥0∞} {z w : ℂ} {S : Set ℂ}
    (h : IsCappedSquare (dyadicSquares s o₁ o₂) ν m z S)
    (hw : w ∈ interior (cappedSquare (dyadicSquares s o₁ o₂) ν m z)) :
    cappedSquare (dyadicSquares s o₁ o₂) ν m w = cappedSquare (dyadicSquares s o₁ o₂) ν m z :=
  cappedSquare_eq_of_mem_interior (dyadicSquares_nest h₁ h₂) dyadicSquares_subset_closure_interior
    h hw

end LatticeProb.DyadicOffset
