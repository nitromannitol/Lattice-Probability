import LatticeProb.LQG.InternalMetricCrossings
import LatticeProb.LQG.InternalMetricDyadicChaining

/-!
# Internal diameter of a closed square from crossings of the halves of its dyadic subsquares

The deterministic part of the proof of Dubédat-Falconet-Gwynne-Pfeffer-Sun (arXiv:1905.00380, Proposition 3.10,
Step 2). Let `S = [a, a + s] × [b, b + s]` and suppose that every closed dyadic subsquare `S_{n,i,j}` of level `n` of `S`
has short "hard" crossings of its halves: a left-right crossing of its bottom half and of its top half, and a top-bottom
crossing of its left half and of its right half, each of `D`-length at most `L n`. Then any two points of `S` are at
internal distance in `S` at most `3 (L 0 + 2 ∑_{n ≥ 1} L n)`.

The proof applies the multiscale bound `IsEuclideanLengthMetric.internalMetric_le_of_dyadic_chain` to the set
`X n i j` of points on left-right or top-bottom crossings of `S_{n,i,j}` of `D`-length at most `L n`. Two points of this
set are at internal distance at most `3 L n` (the "#"-shape bound
`IsEuclideanLengthMetric.internalMetric_le_of_crossings`), and the left-right crossing of the bottom half of a child
square meets the top-bottom crossing of the half of its parent which contains the child.

## Main statements

* `shortCrossingSet`: the points on left-right or top-bottom crossings of a closed rectangle of `D`-length at most `L`.
* `IsEuclideanLengthMetric.internalMetric_le_of_mem_shortCrossingSet`: its internal diameter is at most `3 L`.
* `HasShortHalfCrossings`: the four hard crossings of the halves of a closed rectangle of `D`-length at most `L`.
* `IsEuclideanLengthMetric.internalMetric_le_of_hasShortHalfCrossings`: the multiscale bound.
-/

namespace LatticeProb.LQG

open Set
open scoped ENNReal unitInterval

/-- A left-right crossing of a rectangle is a left-right crossing of every taller rectangle with the same vertical
sides, written with equalities of the abscissas. -/
theorem IsLeftRightCrossing.of_eq_of_le {x₀ x₁ y₀ y₁ x₀' x₁' y₀' y₁' : ℝ} {u v : ℂ} {P : Path u v}
    (h : IsLeftRightCrossing x₀ x₁ y₀ y₁ P) (hx₀ : x₀ = x₀') (hx₁ : x₁ = x₁') (hy₀ : y₀' ≤ y₀) (hy₁ : y₁ ≤ y₁') :
    IsLeftRightCrossing x₀' x₁' y₀' y₁' P := by
  subst hx₀ hx₁
  exact h.mono hy₀ hy₁

/-- The points on left-right or top-bottom crossings of the closed rectangle `[x₀, x₁] × [y₀, y₁]` of `D`-length at
most `L`. -/
def shortCrossingSet (D : ℂ → ℂ → ℝ) (x₀ x₁ y₀ y₁ : ℝ) (L : ℝ≥0∞) : Set ℂ :=
  {z | ∃ (u v : ℂ) (P : Path u v), (IsLeftRightCrossing x₀ x₁ y₀ y₁ P ∨ IsTopBottomCrossing x₀ x₁ y₀ y₁ P) ∧
    pathLength D P ≤ L ∧ z ∈ range P}

theorem shortCrossingSet_subset (D : ℂ → ℂ → ℝ) (x₀ x₁ y₀ y₁ : ℝ) (L : ℝ≥0∞) :
    shortCrossingSet D x₀ x₁ y₀ y₁ L ⊆ Icc x₀ x₁ ×ℂ Icc y₀ y₁ := by
  rintro _ ⟨u, v, P, hP | hP, -, t, rfl⟩
  · exact hP.1 t
  · exact hP.1 t

/-- If the closed rectangle `R ⊆ U` has a left-right and a top-bottom crossing of `D`-length at most `L`, then any two
points on crossings of `R` of `D`-length at most `L` are at internal distance in `U` at most `3 L`. -/
theorem IsEuclideanLengthMetric.internalMetric_le_of_mem_shortCrossingSet {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {x₀ x₁ y₀ y₁ : ℝ} {U : Set ℂ} (hU : Icc x₀ x₁ ×ℂ Icc y₀ y₁ ⊆ U) {L : ℝ≥0∞}
    {a b c d : ℂ} {P₀ : Path a b} {Q₀ : Path c d} (hP₀ : IsLeftRightCrossing x₀ x₁ y₀ y₁ P₀)
    (hQ₀ : IsTopBottomCrossing x₀ x₁ y₀ y₁ Q₀) (hLP₀ : pathLength D P₀ ≤ L) (hLQ₀ : pathLength D Q₀ ≤ L) {z w : ℂ}
    (hz : z ∈ shortCrossingSet D x₀ x₁ y₀ y₁ L) (hw : w ∈ shortCrossingSet D x₀ x₁ y₀ y₁ L) :
    internalMetric D U z w ≤ 3 * L := by
  obtain ⟨u, v, A, hA | hA, hLA, hzA⟩ := hz <;> obtain ⟨u', v', B, hB | hB, hLB, hwB⟩ := hw
  · exact hD.internalMetric_le_of_crossings hU hA hB hQ₀ hQ₀ hLA hLB hLQ₀ hLQ₀
      (Or.inl (Or.inl (Or.inl hzA))) (Or.inl (Or.inl (Or.inr hwB)))
  · exact hD.internalMetric_le_of_crossings hU hA hA hB hB hLA hLA hLB hLB
      (Or.inl (Or.inl (Or.inl hzA))) (Or.inl (Or.inr hwB))
  · exact hD.internalMetric_le_of_crossings hU hB hB hA hA hLB hLB hLA hLA
      (Or.inl (Or.inr hzA)) (Or.inl (Or.inl (Or.inl hwB)))
  · exact hD.internalMetric_le_of_crossings hU hP₀ hP₀ hA hB hLP₀ hLP₀ hLA hLB
      (Or.inl (Or.inr hzA)) (Or.inr hwB)

/-- The closed rectangle `[x₀, x₁] × [y₀, y₁]` has hard crossings of its four halves of `D`-length at most `L`: a
left-right crossing of its bottom half and of its top half, and a top-bottom crossing of its left half and of its right
half. -/
def HasShortHalfCrossings (D : ℂ → ℂ → ℝ) (x₀ x₁ y₀ y₁ : ℝ) (L : ℝ≥0∞) : Prop :=
  (∃ (u v : ℂ) (P : Path u v), IsLeftRightCrossing x₀ x₁ y₀ ((y₀ + y₁) / 2) P ∧ pathLength D P ≤ L) ∧
  (∃ (u v : ℂ) (P : Path u v), IsLeftRightCrossing x₀ x₁ ((y₀ + y₁) / 2) y₁ P ∧ pathLength D P ≤ L) ∧
  (∃ (u v : ℂ) (P : Path u v), IsTopBottomCrossing x₀ ((x₀ + x₁) / 2) y₀ y₁ P ∧ pathLength D P ≤ L) ∧
  (∃ (u v : ℂ) (P : Path u v), IsTopBottomCrossing ((x₀ + x₁) / 2) x₁ y₀ y₁ P ∧ pathLength D P ≤ L)

/-- Internal diameter of a closed square from the hard crossings of the halves of its closed dyadic subsquares
(Dubédat-Falconet-Gwynne-Pfeffer-Sun, Proposition 3.10, Step 2): if every closed dyadic subsquare of level `n` of
`S = [a, a + s] × [b, b + s]` has hard crossings of its four halves of `D`-length at most `L n`, then any two points of `S`
are at internal distance in `S` at most `3 (L 0 + 2 ∑_{n ≥ 1} L n)`. -/
theorem IsEuclideanLengthMetric.internalMetric_le_of_hasShortHalfCrossings {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {a b s : ℝ} (hs : 0 < s) (L : ℕ → ℝ≥0∞)
    (hcross : ∀ n i j : ℕ, i < 2 ^ n → j < 2 ^ n →
      HasShortHalfCrossings D (a + i * (s / 2 ^ n)) (a + (i + 1) * (s / 2 ^ n)) (b + j * (s / 2 ^ n))
        (b + (j + 1) * (s / 2 ^ n)) (L n))
    {z w : ℂ} (hz : z ∈ Icc a (a + s) ×ℂ Icc b (b + s)) (hw : w ∈ Icc a (a + s) ×ℂ Icc b (b + s)) :
    internalMetric D (Icc a (a + s) ×ℂ Icc b (b + s)) z w ≤ 3 * (L 0 + 2 * ∑' n, L (n + 1)) := by
  set X : ℕ → ℕ → ℕ → Set ℂ := fun n i j => shortCrossingSet D (a + i * (s / 2 ^ n)) (a + (i + 1) * (s / 2 ^ n))
    (b + j * (s / 2 ^ n)) (b + (j + 1) * (s / 2 ^ n)) (L n) with hX
  have hXsub : ∀ n i j, i < 2 ^ n → j < 2 ^ n → X n i j ⊆ closedDyadicSubsquare a b s n i j :=
    fun n i j _ _ => shortCrossingSet_subset _ _ _ _ _ _
  have hpos : ∀ n : ℕ, 0 < s / 2 ^ n := fun n => by positivity
  have hXdiam : ∀ n i j, i < 2 ^ n → j < 2 ^ n → ∀ x ∈ X n i j, ∀ y ∈ X n i j,
      internalMetric D (Icc a (a + s) ×ℂ Icc b (b + s)) x y ≤ 3 * L n := by
    intro n i j hi hj x hx y hy
    obtain ⟨⟨u, v, P, hP, hLP⟩, -, ⟨u', v', Q, hQ, hLQ⟩, -⟩ := hcross n i j hi hj
    have hh := hpos n
    exact hD.internalMetric_le_of_mem_shortCrossingSet (closedDyadicSubsquare_subset hs hi hj)
      (hP.mono le_rfl (by nlinarith)) (hQ.mono le_rfl (by nlinarith)) hLP hLQ hx hy
  have hXmeet : ∀ n i j, i < 2 ^ (n + 1) → j < 2 ^ (n + 1) → (X n (i / 2) (j / 2) ∩ X (n + 1) i j).Nonempty := by
    intro n i j hi hj
    have hi' : i / 2 < 2 ^ n := Nat.div_lt_iff_lt_mul two_pos |>.2 (by rwa [← pow_succ])
    have hj' : j / 2 < 2 ^ n := Nat.div_lt_iff_lt_mul two_pos |>.2 (by rwa [← pow_succ])
    obtain ⟨-, -, ⟨u, v, Ql, hQl, hLQl⟩, ⟨u', v', Qr, hQr, hLQr⟩⟩ := hcross n (i / 2) (j / 2) hi' hj'
    obtain ⟨⟨c, d, P, hP, hLP⟩, -⟩ := hcross (n + 1) i j hi hj
    set h := s / 2 ^ (n + 1) with hhdef
    have hh : 0 < h := hpos (n + 1)
    have hH : s / 2 ^ n = 2 * h := by rw [hhdef, pow_succ]; field_simp
    have hj2 : 2 * ((j / 2 : ℕ) : ℝ) ≤ j := by exact_mod_cast Nat.mul_div_le j 2
    have hj2' : (j : ℝ) + 1 ≤ 2 * ((j / 2 : ℕ) : ℝ) + 2 := by
      have : j + 1 ≤ 2 * (j / 2) + 2 := by omega
      exact_mod_cast this
    have hy₀ : b + ((j / 2 : ℕ) : ℝ) * (s / 2 ^ n) ≤ b + j * h := by
      rw [hH]; nlinarith
    have hy₁ : (b + j * h + (b + (j + 1) * h)) / 2 ≤ b + (((j / 2 : ℕ) : ℝ) + 1) * (s / 2 ^ n) := by
      rw [hH]; nlinarith
    have hmemP : ∀ t, P t ∈ X (n + 1) i j := fun t =>
      ⟨c, d, P, Or.inl (hP.mono le_rfl (by nlinarith)), hLP, t, rfl⟩
    rcases Nat.even_or_odd' i with ⟨k, rfl | rfl⟩
    · have hk : 2 * k / 2 = k := by omega
      rw [hk] at hQl hQr ⊢
      have hP' : IsLeftRightCrossing (a + k * (s / 2 ^ n)) ((a + k * (s / 2 ^ n) + (a + (k + 1) * (s / 2 ^ n))) / 2)
          (b + ((j / 2 : ℕ) : ℝ) * (s / 2 ^ n)) (b + (((j / 2 : ℕ) : ℝ) + 1) * (s / 2 ^ n)) P :=
        hP.of_eq_of_le (by rw [hH]; push_cast; ring) (by rw [hH]; push_cast; ring) hy₀ hy₁
      obtain ⟨t₁, t₂, ht⟩ := hP'.exists_eq hQl
      refine ⟨P t₁, ⟨u, v, Ql, Or.inr (hQl.mono le_rfl ?_), hLQl, t₂, ht.symm⟩, hmemP t₁⟩
      have := hpos n
      nlinarith
    · have hk : (2 * k + 1) / 2 = k := by omega
      rw [hk] at hQl hQr ⊢
      have hP' : IsLeftRightCrossing ((a + k * (s / 2 ^ n) + (a + (k + 1) * (s / 2 ^ n))) / 2) (a + (k + 1) * (s / 2 ^ n))
          (b + ((j / 2 : ℕ) : ℝ) * (s / 2 ^ n)) (b + (((j / 2 : ℕ) : ℝ) + 1) * (s / 2 ^ n)) P :=
        hP.of_eq_of_le (by rw [hH]; push_cast; ring) (by rw [hH]; push_cast; ring) hy₀ hy₁
      obtain ⟨t₁, t₂, ht⟩ := hP'.exists_eq hQr
      refine ⟨P t₁, ⟨u', v', Qr, Or.inr (hQr.mono ?_ le_rfl), hLQr, t₂, ht.symm⟩, hmemP t₁⟩
      have := hpos n
      nlinarith
  have key := hD.internalMetric_le_of_dyadic_chain hs X (fun n => 3 * L n) hXsub hXdiam hXmeet hz hw
  beta_reduce at key
  rw [ENNReal.tsum_mul_left] at key
  calc internalMetric D _ z w ≤ 3 * L 0 + 2 * (3 * ∑' n, L (n + 1)) := key
    _ = 3 * (L 0 + 2 * ∑' n, L (n + 1)) := by ring

end LatticeProb.LQG
