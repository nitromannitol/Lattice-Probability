import Mathlib
import LatticeProb.Site
import LatticeProb.Graph.Boundary

/-!
# Pair-chain maximum principle for harmonic differences

The harmonic difference estimate of Lawler and Limic (*Random Walk: A Modern
Introduction*, Theorem 6.3.8(a)) bounds `f (unit i) - f 0` for a function `f`
that is harmonic on a Euclidean ball, in terms of a bound for `f` on the closure
of the ball. The proof is a maximum principle for a lazy coupled pair `(x, D)`:
the first walker starts at `x`, the second at `x + D e_i`, and in each step
exactly one of the two walkers moves in direction `e_i`, while both move freely
in the other directions. The difference `u (x, D) = f (x + D e_i) - f x` is
harmonic for this pair chain on the states whose walkers lie in the ball, and
the chain satisfies a minimum principle on the finite set of such states.

This file defines the pair chain and proves the two properties used on the
ball: the lazy mean value identity for the difference, and the minimum
principle on the finite pair set.
-/

namespace LatticeProb.HarmonicDifference

variable {d : ℕ}

/-- The Euclidean ball of radius `n` about the origin, as a set of sites. -/
def ball (n : ℕ) : Set (Site d) :=
  {y : Site d | ‖(WithLp.toLp 2 (fun j => (y j : ℝ)) : EuclideanSpace ℝ (Fin d)) -
    WithLp.toLp 2 (fun j => ((0 : Site d) j : ℝ))‖ < (n : ℝ)}

/-- The pair states `(x, D)` with `1 ≤ D ≤ L - 1` whose walkers `x` and
`x + D e_i` both lie in the ball of radius `n`. -/
def pairU (i : Fin d) (n L : ℕ) : Set (Site d × ℤ) :=
  {s | 1 ≤ s.2 ∧ s.2 ≤ (L : ℤ) - 1 ∧ s.1 ∈ ball n ∧ s.1 + s.2 • unit i ∈ ball n}

/-- One step of the lazy coupled pair applied to `h`. The state `s` itself has
weight `(d - 1) / (2 d)`. Each of the `2 (d - 1)` moves in a direction `j ≠ i`
has weight `1 / (4 d)`, and so does each of the four moves in direction `i`,
where exactly one walker moves. -/
noncomputable def pairQ (i : Fin d) (h : Site d × ℤ → ℝ) (s : Site d × ℤ) : ℝ :=
  ((d : ℝ) - 1) / (2 * (d : ℝ)) * h s
    + 1 / (4 * (d : ℝ)) * ∑ j ∈ Finset.univ.erase i,
        (h (s.1 + unit j, s.2) + h (s.1 - unit j, s.2))
    + 1 / (4 * (d : ℝ)) * (h (s.1 + unit i, s.2 - 1) + h (s.1 - unit i, s.2 + 1)
        + h (s.1, s.2 + 1) + h (s.1, s.2 - 1))

/-- The states reached from `s` in one step of `pairQ`, together with `s`. -/
def pairSucc (i : Fin d) (s : Site d × ℤ) : Finset (Site d × ℤ) :=
  (Finset.univ.erase i).biUnion (fun j => {(s.1 + unit j, s.2), (s.1 - unit j, s.2)}) ∪
    {(s.1 + unit i, s.2 - 1), (s.1 - unit i, s.2 + 1), (s.1, s.2 + 1), (s.1, s.2 - 1), s}

theorem coord_abs_lt_of_mem_ball {n : ℕ} {y : Site d} (hy : y ∈ ball n) (j : Fin d) :
    |(y j : ℝ)| < n := by
  have h1 : ‖(WithLp.toLp 2 (fun k => (y k : ℝ)) : EuclideanSpace ℝ (Fin d)) -
      WithLp.toLp 2 (fun k => ((0 : Site d) k : ℝ))‖ < n := hy
  have h2 := PiLp.norm_apply_le ((WithLp.toLp 2 (fun k => (y k : ℝ)) :
    EuclideanSpace ℝ (Fin d)) - WithLp.toLp 2 (fun k => ((0 : Site d) k : ℝ))) j
  have h3 : ((WithLp.toLp 2 (fun k => (y k : ℝ)) : EuclideanSpace ℝ (Fin d)) -
      WithLp.toLp 2 (fun k => ((0 : Site d) k : ℝ))) j = (y j : ℝ) := by
    simp
  rw [h3, Real.norm_eq_abs] at h2
  linarith

theorem ball_finite (n : ℕ) : (ball (d := d) n).Finite := by
  refine (Set.Finite.pi fun _ : Fin d => Set.finite_Icc (-(n : ℤ)) (n : ℤ)).subset ?_
  intro y hy
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
  intro j
  have h := coord_abs_lt_of_mem_ball hy j
  have h' : |y j| < (n : ℤ) := by
    rw [← Int.cast_abs] at h
    exact_mod_cast h
  exact ⟨(abs_lt.mp h').1.le, (abs_lt.mp h').2.le⟩

theorem pairU_finite (i : Fin d) (n L : ℕ) : (pairU i n L).Finite := by
  refine ((ball_finite n).prod (Set.finite_Icc (1 : ℤ) ((L : ℤ) - 1))).subset ?_
  rintro ⟨x, D⟩ ⟨hD1, hDL, hx, -⟩
  exact ⟨hx, hD1, hDL⟩

theorem card_erase_univ (i : Fin d) : ((Finset.univ.erase i).card : ℝ) = (d : ℝ) - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
    Nat.cast_pred i.pos]

/-- The lazy mean value identity: a function harmonic at `z` for the simple random
walk equals the average of its value at `z` and the lazy neighbour average. -/
theorem lazy_mean {f : Site d → ℝ} {z : Site d} (hd : 0 < d)
    (hz : nbrSum f z - 2 * d * f z = 0) :
    f z = f z / 2 + nbrSum f z / (4 * d) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have h2 : nbrSum f z = 2 * d * f z := by linarith
  rw [h2]
  field_simp
  ring

/-- Applied to `u (x, D) = f (x + D e_i) - f x`, the pair operator returns `u` on
the pair states, provided `f` is harmonic at both walkers. -/
theorem pairQ_u (f : Site d → ℝ) (i : Fin d) (n L : ℕ)
    (hharm : ∀ z ∈ ball n, nbrSum f z - 2 * d * f z = 0) {s : Site d × ℤ}
    (hs : s ∈ pairU i n L) :
    pairQ i (fun p => f (p.1 + p.2 • unit i) - f p.1) s = f (s.1 + s.2 • unit i) - f s.1 := by
  obtain ⟨-, -, hx, hy⟩ := hs
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast i.pos.ne'
  have hd1 : (d : ℝ) * (d : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hd
  have hX : nbrSum f s.1 - 2 * d * f s.1 = 0 := hharm _ hx
  have hY : nbrSum f (s.1 + s.2 • unit i) - 2 * d * f (s.1 + s.2 • unit i) = 0 := hharm _ hy
  have e1 : s.1 + unit i + (s.2 - 1) • unit i = s.1 + s.2 • unit i := by
    rw [sub_smul, one_smul]; abel
  have e2 : s.1 - unit i + (s.2 + 1) • unit i = s.1 + s.2 • unit i := by
    rw [add_smul, one_smul]; abel
  have e3 : s.1 + (s.2 + 1) • unit i = s.1 + s.2 • unit i + unit i := by
    rw [add_smul, one_smul]; abel
  have e4 : s.1 + (s.2 - 1) • unit i = s.1 + s.2 • unit i - unit i := by
    rw [sub_smul, one_smul]; abel
  have ej : ∀ j : Fin d, s.1 + unit j + s.2 • unit i = s.1 + s.2 • unit i + unit j :=
    fun j => by abel
  have ej' : ∀ j : Fin d, s.1 - unit j + s.2 • unit i = s.1 + s.2 • unit i - unit j :=
    fun j => by abel
  have hNY : nbrSum f (s.1 + s.2 • unit i) = (f (s.1 + s.2 • unit i + unit i) +
      f (s.1 + s.2 • unit i - unit i)) + ∑ j ∈ Finset.univ.erase i,
        (f (s.1 + s.2 • unit i + unit j) + f (s.1 + s.2 • unit i - unit j)) := by
    unfold nbrSum
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hNX : nbrSum f s.1 = (f (s.1 + unit i) + f (s.1 - unit i)) + ∑ j ∈ Finset.univ.erase i,
      (f (s.1 + unit j) + f (s.1 - unit j)) := by
    unfold nbrSum
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hA : ∑ j ∈ Finset.univ.erase i,
      ((f (s.1 + s.2 • unit i + unit j) - f (s.1 + unit j)) +
        (f (s.1 + s.2 • unit i - unit j) - f (s.1 - unit j))) =
      ∑ j ∈ Finset.univ.erase i, (f (s.1 + s.2 • unit i + unit j) + f (s.1 + s.2 • unit i - unit j))
        - ∑ j ∈ Finset.univ.erase i, (f (s.1 + unit j) + f (s.1 - unit j)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [pairQ, e1, e2, e3, e4, ej, ej']
  rw [hA]
  linear_combination (1 / (4 * (d : ℝ))) * hY - (1 / (4 * (d : ℝ))) * hX
    - (1 / (4 * (d : ℝ))) * hNY + (1 / (4 * (d : ℝ))) * hNX
    + (f (s.1 + s.2 • unit i) - f s.1) * hd1

/-- The pair operator commutes with subtracting a constant, since its weights sum to one. -/
theorem pairQ_sub_const (i : Fin d) (h : Site d × ℤ → ℝ) (c : ℝ) (s : Site d × ℤ) :
    pairQ i (fun t => h t - c) s = pairQ i h s - c := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast i.pos.ne'
  have hsum : ∑ j ∈ Finset.univ.erase i,
      ((h (s.1 + unit j, s.2) - c) + (h (s.1 - unit j, s.2) - c)) =
      ∑ j ∈ Finset.univ.erase i, (h (s.1 + unit j, s.2) + h (s.1 - unit j, s.2))
        - ∑ j ∈ Finset.univ.erase i, (2 * c) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_const, nsmul_eq_mul, card_erase_univ] at hsum
  simp only [pairQ]
  rw [hsum]
  field_simp
  ring


theorem plus_mem_pairSucc (i : Fin d) (s : Site d × ℤ) {j : Fin d}
    (hj : j ∈ Finset.univ.erase i) : (s.1 + unit j, s.2) ∈ pairSucc i s := by
  unfold pairSucc
  exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, hj, by simp⟩)

theorem minus_mem_pairSucc (i : Fin d) (s : Site d × ℤ) {j : Fin d}
    (hj : j ∈ Finset.univ.erase i) : (s.1 - unit j, s.2) ∈ pairSucc i s := by
  unfold pairSucc
  exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, hj, by simp⟩)

/-- Convexity of the ball: if `x` and `x + D e_i` lie in the ball and `D ≥ 1`, then
`x + (D - 1) e_i` lies in the ball, since it is a convex combination of the two. -/
theorem ball_combo {n : ℕ} {x : Site d} {i : Fin d} {D : ℤ} (hD : 0 < D)
    (hx : x ∈ ball n) (hy : x + D • unit i ∈ ball n) :
    x + (D - 1) • unit i ∈ ball n := by
  have hD1 : (1 : ℤ) ≤ D := by omega
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hD1R : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  set c : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun j => ((0 : Site d) j : ℝ)) with hc
  set E : Site d → EuclideanSpace ℝ (Fin d) :=
    fun z => WithLp.toLp 2 (fun j => (z j : ℝ)) with hE
  have hx' : E x ∈ Metric.ball c n := by
    rw [Metric.mem_ball, dist_eq_norm]; exact hx
  have hy' : E (x + D • unit i) ∈ Metric.ball c n := by
    rw [Metric.mem_ball, dist_eq_norm]; exact hy
  have ha : (0 : ℝ) ≤ 1 / (D : ℝ) := (one_div_pos.mpr hDpos).le
  have hb : (0 : ℝ) ≤ ((D : ℝ) - 1) / D := div_nonneg (by linarith) hDpos.le
  have hab : 1 / (D : ℝ) + ((D : ℝ) - 1) / D = 1 := by
    rw [← add_div, div_eq_one_iff_eq hDR]; ring
  have key := (convex_ball c (n : ℝ)) hx' hy' ha hb hab
  have hcoord : ∀ k : Fin d, ((x + (D - 1) • unit i) k : ℝ) =
      1 / (D : ℝ) * ((x k : ℤ) : ℝ) + ((D : ℝ) - 1) / D * ((x + D • unit i) k : ℝ) := by
    intro k
    simp only [Pi.add_apply, Pi.smul_apply]
    simp only [zsmul_eq_mul, Int.cast_id, Int.cast_add, Int.cast_mul, Int.cast_sub,
      Int.cast_one]
    field_simp
    ring
  have heq : E (x + (D - 1) • unit i) =
      (1 / (D : ℝ)) • E x + (((D : ℝ) - 1) / D) • E (x + D • unit i) := by
    ext k
    simp only [hE, PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul]
    exact hcoord k
  have hmem : E (x + (D - 1) • unit i) ∈ Metric.ball c n := by
    rw [heq]; exact key
  rw [Metric.mem_ball, dist_eq_norm] at hmem
  exact hmem

/-- Minimum principle on the pair set. A function that is a supersolution of `pairQ`
on the pair states and nonnegative at every successor outside them is nonnegative
on the pair states. -/
theorem min_principle (i : Fin d) (n L : ℕ) (v : Site d × ℤ → ℝ)
    (hsup : ∀ s ∈ pairU i n L, pairQ i v s ≤ v s)
    (hbd : ∀ s ∈ pairU i n L, ∀ s' ∈ pairSucc i s, s' ∉ pairU i n L → 0 ≤ v s') :
    ∀ s ∈ pairU i n L, 0 ≤ v s := by
  classical
  by_contra hneg
  push Not at hneg
  obtain ⟨s0, hs0, hlt⟩ := hneg
  have hfin := pairU_finite i n L
  have hdR : (0 : ℝ) < d := by exact_mod_cast i.pos
  have hpos : (0 : ℝ) < 1 / (4 * (d : ℝ)) := one_div_pos.mpr (by linarith)
  obtain ⟨s1, hs1, hmin⟩ :=
    hfin.toFinset.exists_min_image v ⟨s0, hfin.mem_toFinset.mpr hs0⟩
  have hmU : ∀ t ∈ pairU i n L, v s1 ≤ v t := fun t ht => hmin t (hfin.mem_toFinset.mpr ht)
  have hm_neg : v s1 < 0 := lt_of_le_of_lt (hmU s0 hs0) hlt
  have hsucc : ∀ s ∈ pairU i n L, ∀ t ∈ pairSucc i s, v s1 ≤ v t := by
    intro s hs t ht
    by_cases htU : t ∈ pairU i n L
    · exact hmU t htU
    · exact le_trans hm_neg.le (hbd s hs t ht htU)
  obtain ⟨s, hsF, hsmin⟩ := ((hfin.toFinset).filter (fun t => v t = v s1)).exists_min_image
    (fun t => t.2) ⟨s1, Finset.mem_filter.mpr ⟨hs1, rfl⟩⟩
  simp only [Finset.mem_filter, hfin.mem_toFinset] at hsF
  obtain ⟨hsU, hsv⟩ := hsF
  have hsmin' : ∀ t ∈ pairU i n L, v t = v s1 → s.2 ≤ t.2 := fun t ht hvt =>
    hsmin t (Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr ht, hvt⟩)
  obtain ⟨hD1, hDL, hx, hy⟩ := hsU
  have hU : s ∈ pairU i n L := ⟨hD1, hDL, hx, hy⟩
  have hle : pairQ i v s ≤ v s := hsup s hU
  have hshift : pairQ i (fun t => v t - v s1) s ≤ 0 := by
    rw [pairQ_sub_const]; linarith
  have hexp := hshift
  simp only [pairQ] at hexp
  rw [hsv, sub_self, mul_zero, zero_add] at hexp
  have hQ : ∀ t ∈ pairSucc i s, 0 ≤ v t - v s1 := fun t ht => sub_nonneg.mpr (hsucc s hU t ht)
  have hS : 0 ≤ ∑ j ∈ Finset.univ.erase i,
      ((v (s.1 + unit j, s.2) - v s1) + (v (s.1 - unit j, s.2) - v s1)) := by
    apply Finset.sum_nonneg
    intro j hj
    have h1 := hQ _ (plus_mem_pairSucc i s hj)
    have h2 := hQ _ (minus_mem_pairSucc i s hj)
    linarith
  have hQ1 := hQ (s.1 + unit i, s.2 - 1) (by simp [pairSucc])
  have hQ2 := hQ (s.1 - unit i, s.2 + 1) (by simp [pairSucc])
  have hQ3 := hQ (s.1, s.2 + 1) (by simp [pairSucc])
  have hP1 := mul_nonneg hpos.le hS
  have hP2 := mul_nonneg hpos.le (add_nonneg (add_nonneg hQ1 hQ2) hQ3)
  have hsplit : 1 / (4 * (d : ℝ)) * ((v (s.1 + unit i, s.2 - 1) - v s1) +
      (v (s.1 - unit i, s.2 + 1) - v s1) + (v (s.1, s.2 + 1) - v s1) +
      (v (s.1, s.2 - 1) - v s1)) = 1 / (4 * (d : ℝ)) * ((v (s.1 + unit i, s.2 - 1) - v s1) +
      (v (s.1 - unit i, s.2 + 1) - v s1) + (v (s.1, s.2 + 1) - v s1)) +
      1 / (4 * (d : ℝ)) * (v (s.1, s.2 - 1) - v s1) := by ring
  have hPQ : 1 / (4 * (d : ℝ)) * (v (s.1, s.2 - 1) - v s1) ≤ 0 := by
    linarith
  have hq4 : v (s.1, s.2 - 1) ≤ v s1 := by
    by_contra hc
    push Not at hc
    have := mul_pos hpos (sub_pos.mpr hc)
    linarith
  by_cases hD : s.2 = 1
  · have hnot : (s.1, s.2 - 1) ∉ pairU i n L := by
      rintro ⟨h1, -⟩
      have h1' : 1 ≤ s.2 - 1 := h1
      omega
    have h0 := hbd s hU (s.1, s.2 - 1) (by simp [pairSucc]) hnot
    linarith
  · have hconv : s.1 + (s.2 - 1) • unit i ∈ ball n := ball_combo (by omega) hx hy
    have hq4U : (s.1, s.2 - 1) ∈ pairU i n L :=
      ⟨by show 1 ≤ s.2 - 1; omega, by show s.2 - 1 ≤ (L : ℤ) - 1; omega, hx, hconv⟩
    have hge : v s1 ≤ v (s.1, s.2 - 1) := hmU _ hq4U
    have heq : v (s.1, s.2 - 1) = v s1 := le_antisymm hq4 hge
    have h' : s.2 ≤ s.2 - 1 := hsmin' _ hq4U heq
    omega

end LatticeProb.HarmonicDifference
