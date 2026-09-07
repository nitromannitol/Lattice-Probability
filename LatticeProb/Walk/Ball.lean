/-
The Euclidean norm on the lattice: the volume of a ball, and the radial series
it controls.

The sup-norm shells of `LatticeProb/Walk/Shells.lean` count the lattice; what
the estimates of the papers are written in is the Euclidean norm of the notation
section.  The sup-norm is at most the Euclidean norm and the Euclidean norm is
at most `√d` times the sup-norm, so a ball of Euclidean radius `R` sits inside
the box of sup-radius `R`, and the volume bound and every radial sum transfer.
The series `∑_y (1+|y|)^{-p}` converges exactly when `p > d`, and that is what a
scenery tail split at a radius needs on each side.
-/
import Mathlib
import LatticeProb.Walk.Shells

noncomputable section

namespace LatticeProb

open Finset

variable {d : ℕ}

/-! ### The Euclidean norm -/

/-- The Euclidean norm `|x|` of a lattice site. -/
def euclidNorm {d : ℕ} (x : Site d) : ℝ := Real.sqrt (∑ i : Fin d, ((x i : ℤ) : ℝ) ^ 2)

theorem euclidNorm_nonneg (x : Site d) : 0 ≤ euclidNorm x := Real.sqrt_nonneg _

@[simp] theorem euclidNorm_zero : euclidNorm (0 : Site d) = 0 := by
  simp [euclidNorm]

/-- The sup-norm is at most the Euclidean norm. -/
theorem supNorm_le_euclidNorm (x : Site d) : (supNorm x : ℝ) ≤ euclidNorm x := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp [supNorm, euclidNorm]
  · have hne : (Finset.univ : Finset (Fin d)).Nonempty := by
      rw [Finset.univ_nonempty_iff]
      exact ⟨⟨0, hd⟩⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ hne (fun i => (x i).natAbs)
    have hsum : ((x i : ℤ) : ℝ) ^ 2 ≤ ∑ j : Fin d, ((x j : ℤ) : ℝ) ^ 2 :=
      Finset.single_le_sum (f := fun j : Fin d => ((x j : ℤ) : ℝ) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hxi : ((supNorm x : ℕ) : ℝ) = |((x i : ℤ) : ℝ)| := by
      rw [supNorm, hi, Nat.cast_natAbs, Int.cast_abs]
    rw [hxi, euclidNorm, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsum

/-- The Euclidean norm is at most `√d` times the sup-norm. -/
theorem euclidNorm_le_sqrt_mul_supNorm (x : Site d) :
    euclidNorm x ≤ Real.sqrt d * (supNorm x : ℝ) := by
  have hb : ∀ j : Fin d, ((x j : ℤ) : ℝ) ^ 2 ≤ ((supNorm x : ℕ) : ℝ) ^ 2 := by
    intro j
    have h1 : |x j| ≤ ((supNorm x : ℕ) : ℤ) := supNorm_le_iff.mp le_rfl j
    have h2 : |((x j : ℤ) : ℝ)| ≤ ((supNorm x : ℕ) : ℝ) := by exact_mod_cast h1
    nlinarith [abs_nonneg ((x j : ℤ) : ℝ), sq_abs ((x j : ℤ) : ℝ)]
  have hsum : ∑ j : Fin d, ((x j : ℤ) : ℝ) ^ 2 ≤ (d : ℝ) * ((supNorm x : ℕ) : ℝ) ^ 2 := by
    calc ∑ j : Fin d, ((x j : ℤ) : ℝ) ^ 2
        ≤ ∑ _j : Fin d, ((supNorm x : ℕ) : ℝ) ^ 2 := Finset.sum_le_sum fun j _ => hb j
      _ = (d : ℝ) * ((supNorm x : ℕ) : ℝ) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc euclidNorm x ≤ Real.sqrt ((d : ℝ) * ((supNorm x : ℕ) : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * ((supNorm x : ℕ) : ℝ) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (Nat.cast_nonneg _)]

/-! ### The ball and its volume -/

open scoped Classical in
/-- The sites at Euclidean distance at most `R` from the origin. -/
def ballFinset (d : ℕ) (R : ℝ) : Finset (Site d) :=
  (boxFinset (0 : Site d) ⌊R⌋₊).filter fun y => euclidNorm y ≤ R

theorem mem_ballFinset_iff {R : ℝ} {y : Site d} :
    y ∈ ballFinset d R ↔ euclidNorm y ≤ R := by
  classical
  rw [ballFinset, Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  refine mem_boxFinset_zero_iff.mpr (Nat.le_floor ?_)
  exact le_trans (supNorm_le_euclidNorm y) h

/-- **The volume of a lattice ball.**  The number of sites within Euclidean
distance `R` of the origin is at most `(2R+1)^d`. -/
theorem card_ballFinset_le (d : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ((ballFinset d R).card : ℝ) ≤ (2 * R + 1) ^ d := by
  classical
  have h1 : (ballFinset d R).card ≤ (boxFinset (0 : Site d) ⌊R⌋₊).card :=
    Finset.card_filter_le _ _
  rw [card_boxFinset_zero] at h1
  have h2 : ((ballFinset d R).card : ℝ) ≤ (2 * ((⌊R⌋₊ : ℕ) : ℝ) + 1) ^ d := by
    have : ((ballFinset d R).card : ℝ) ≤ (((2 * ⌊R⌋₊ + 1) ^ d : ℕ) : ℝ) := by
      exact_mod_cast h1
    refine this.trans (le_of_eq ?_)
    push_cast
    ring
  refine h2.trans ?_
  have h3 : ((⌊R⌋₊ : ℕ) : ℝ) ≤ R := Nat.floor_le hR
  gcongr

/-! ### Radial sums over the lattice -/

theorem sum_box_radial_le (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) (n : ℕ) :
    ∑ y ∈ boxFinset (0 : Site d) n, f (supNorm y)
      ≤ f 0 + ∑ k ∈ Finset.Icc 1 n, 2 * d * (2 * (k : ℝ) + 1) ^ (d - 1) * f k := by
  rw [sum_box_radial]
  have hterm : ∀ k ∈ Finset.Icc 1 n,
      (shellCard d k : ℝ) * f k ≤ 2 * d * (2 * (k : ℝ) + 1) ^ (d - 1) * f k := by
    intro k hk
    exact mul_le_mul_of_nonneg_right (shellCard_le d (Finset.mem_Icc.mp hk).1) (hf k)
  linarith [Finset.sum_le_sum hterm]

/-- A radial function is summable over the lattice as soon as its shell-weighted
sequence is summable over the radii. -/
theorem summable_radial (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    (hs : Summable fun k : ℕ => 2 * d * (2 * (k : ℝ) + 1) ^ (d - 1) * f k) :
    Summable fun y : Site d => f (supNorm y) := by
  refine summable_of_sum_le (c := f 0 + ∑' k : ℕ, 2 * d * (2 * (k : ℝ) + 1) ^ (d - 1) * f k)
    (fun y => hf _) fun u => ?_
  set n := u.sup supNorm with hn
  have hsub : u ⊆ boxFinset (0 : Site d) n := fun y hy =>
    mem_boxFinset_zero_iff.mpr (Finset.le_sup hy)
  calc ∑ y ∈ u, f (supNorm y)
      ≤ ∑ y ∈ boxFinset (0 : Site d) n, f (supNorm y) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun y _ _ => hf _
    _ ≤ f 0 + ∑ k ∈ Finset.Icc 1 n, 2 * d * (2 * (k : ℝ) + 1) ^ (d - 1) * f k :=
        sum_box_radial_le f hf n
    _ ≤ f 0 + ∑' k : ℕ, 2 * d * (2 * (k : ℝ) + 1) ^ (d - 1) * f k := by
        have := Summable.sum_le_tsum (Finset.Icc 1 n)
          (fun k _ => by have := hf k; positivity) hs
        linarith

/-! ### The radial series `∑_y (1+|y|)^{-p}` -/

/-- **The lattice radial series converges above the dimension.**  In the
sup-norm. -/
theorem summable_one_add_supNorm_rpow (d : ℕ) {p : ℝ} (hp : (d : ℝ) < p) :
    Summable fun y : Site d => (1 + (supNorm y : ℝ)) ^ (-p) := by
  have hpp : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg d) hp
  refine summable_radial (fun k => (1 + (k : ℝ)) ^ (-p)) (fun k => by positivity) ?_
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp
  · have hd1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      have : (d - 1 : ℕ) + 1 = d := by omega
      have := congrArg (fun m : ℕ => (m : ℝ)) this
      push_cast at this
      linarith
    have hbase : Summable fun k : ℕ => (1 + (k : ℝ)) ^ ((d : ℝ) - 1 - p) := by
      have h1 : Summable fun n : ℕ => (n : ℝ) ^ ((d : ℝ) - 1 - p) :=
        Real.summable_nat_rpow.mpr (by linarith)
      have h2 := (summable_nat_add_iff 1).mpr h1
      refine h2.congr fun n => ?_
      push_cast
      ring_nf
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((hbase.mul_left (2 * (d : ℝ) * 3 ^ (d - 1))))
    have hk0 : (0 : ℝ) < 1 + (k : ℝ) := by positivity
    have hstep : (2 * (k : ℝ) + 1) ^ (d - 1) ≤ 3 ^ (d - 1) * (1 + (k : ℝ)) ^ (d - 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have hrw : (1 + (k : ℝ)) ^ (d - 1) * (1 + (k : ℝ)) ^ (-p)
        = (1 + (k : ℝ)) ^ ((d : ℝ) - 1 - p) := by
      rw [show ((1 + (k : ℝ)) ^ (d - 1) : ℝ) = (1 + (k : ℝ)) ^ (((d - 1 : ℕ) : ℝ)) from
        (Real.rpow_natCast _ _).symm, ← Real.rpow_add hk0, hd1]
      ring_nf
    calc 2 * (d : ℝ) * (2 * (k : ℝ) + 1) ^ (d - 1) * (1 + (k : ℝ)) ^ (-p)
        ≤ 2 * (d : ℝ) * (3 ^ (d - 1) * (1 + (k : ℝ)) ^ (d - 1)) * (1 + (k : ℝ)) ^ (-p) := by
          have hnn : (0 : ℝ) ≤ (1 + (k : ℝ)) ^ (-p) := by positivity
          refine mul_le_mul_of_nonneg_right ?_ hnn
          exact mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 2 * (d : ℝ) * 3 ^ (d - 1) * ((1 + (k : ℝ)) ^ (d - 1) * (1 + (k : ℝ)) ^ (-p)) := by
          ring
      _ = 2 * (d : ℝ) * 3 ^ (d - 1) * (1 + (k : ℝ)) ^ ((d : ℝ) - 1 - p) := by rw [hrw]

/-- **The lattice radial series converges above the dimension.**  In the
Euclidean norm of the notation section, which is what the scenery tail splits
on. -/
theorem summable_one_add_euclidNorm_rpow (d : ℕ) {p : ℝ} (hp : (d : ℝ) < p) :
    Summable fun y : Site d => (1 + euclidNorm y) ^ (-p) := by
  have hpp : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg d) hp
  refine Summable.of_nonneg_of_le
    (fun y => Real.rpow_nonneg (by linarith [euclidNorm_nonneg y]) _) (fun y => ?_)
    (summable_one_add_supNorm_rpow d hp)
  exact Real.rpow_le_rpow_of_nonpos (by positivity)
    (by linarith [supNorm_le_euclidNorm y]) (by linarith)

end LatticeProb

end
