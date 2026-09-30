import LatticeProb.Site
import LatticeProb.Graph.Zd
import LatticeProb.Graph.ExitDecomp
import LatticeProb.Network.Killed
import LatticeProb.Network.KilledGreen
import LatticeProb.Walk.SRWGaussBound
import LatticeProb.Walk.GreenIdentity
import LatticeProb.Walk.Decomp
import LatticeProb.Walk.LocalCLTOne
import LatticeProb.Walk.SRWOneDim
import LatticeProb.Walk.LocalCLT
import LatticeProb.Walk.ExitBox


/-!
# Kernels on the lattice

Translation invariance of the free and killed heat kernels on `ℤ^d`: `walkOp` commutes with
shifting, summing and scaling, `Graph.heat` reduces to the simple random walk kernel `srwHeat` at
the difference `x - y`, and the killed heat kernel `killedHeat` satisfies the killed
Chapman-Kolmogorov identity and is dominated by `srwHeat`.
-/

open Finset
open scoped Classical

namespace LatticeProb

namespace GreenTwoSided

variable {d : ℕ}

-- unfold LatticeProb.walkOp, nbrSum; Finset.sum_congr; `z + unit i - y = z - y + unit i`
-- (add_sub_right_comm), same with `-`  (sub_right_comm).
/-- The averaging operator commutes with translation: `walkOp` of the `y`-shift of `f` at `x`
equals `walkOp f` at `x - y`. -/
private theorem walkOp_shift (f : Site d → ℝ) (x y : Site d) :
    LatticeProb.walkOp (fun z => f (z - y)) x = LatticeProb.walkOp f (x - y) := by
  simp only [LatticeProb.walkOp, LatticeProb.nbrSum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show x + unit i - y = x - y + unit i from by abel,
      show x - unit i - y = x - y - unit i from by abel]


-- Induction on k generalizing x.  k = 0: Graph.heat def (`if x = y`), srwHeat_zero, sub_eq_zero.
-- k+1: Graph.Zd.heat_succ_walkOp, IH under the binder (funext), walkOp_shift, srwHeat_succ.
/-- The free heat kernel on the lattice is translation invariant: `Graph.heat` from `x` to `y` in
`k` steps equals the simple random walk kernel `srwHeat` at `x - y`. -/
private theorem heat_eq_srwHeat_sub (k : ℕ) (x y : Site d) :
    Graph.heat (lattice d) k x y = srwHeat d k (x - y) := by
  induction k generalizing x with
  | zero =>
    rw [srwHeat_zero]
    dsimp only [Graph.heat]
    by_cases h : x = y
    · subst h; simp
    · simp [h, sub_ne_zero.mpr h]
  | succ k ih =>
    rw [Graph.heat_succ, srwHeat_succ, Graph.Zd.walkOp_eq]
    simp only [ih]
    rw [walkOp_shift]


-- Graph.heat_eq_killedHeat_add_exitHeat C y k x, Graph.exitHeat_nonneg, heat_eq_srwHeat_sub;
-- linarith.
/-- The heat kernel killed on leaving any set `C` is dominated by the free heat kernel:
`killedHeat C k x y ≤ srwHeat d k (x - y)`. -/
theorem killedHeat_le_srwHeat_sub (C : Set (Site d)) (k : ℕ) (x y : Site d) :
    Graph.killedHeat (lattice d) C k x y ≤ srwHeat d k (x - y) := by
  have h := Graph.heat_eq_killedHeat_add_exitHeat (G := lattice d) C y k x
  have hnn := Graph.exitHeat_nonneg (G := lattice d) C y k x
  have h2 := heat_eq_srwHeat_sub k x y
  linarith


-- unfold LatticeProb.walkOp, nbrSum; Finset.sum_div, ← Finset.sum_add_distrib, Finset.sum_comm.
/-- `walkOp` commutes with a finite sum over an index set: the average of a sum of functions is
the sum of the averages. -/
private theorem walkOp_sum {ι : Type*} (s : Finset ι) (F : ι → Site d → ℝ) (x : Site d) :
    LatticeProb.walkOp (fun w => ∑ z ∈ s, F z w) x = ∑ z ∈ s, LatticeProb.walkOp (F z) x := by
  simp only [walkOp, nbrSum_eq_sum_dir, Finset.sum_div]
  rw [Finset.sum_comm]


-- walkOp (c * f) = c * walkOp f:  unfold walkOp, nbrSum; Finset.mul_sum; ring.
/-- `walkOp` commutes with right multiplication by a constant. -/
private theorem walkOp_mul_const (c : ℝ) (f : Site d → ℝ) (x : Site d) :
    LatticeProb.walkOp (fun w => f w * c) x = LatticeProb.walkOp f x * c := by
  unfold LatticeProb.walkOp LatticeProb.nbrSum
  rw [Finset.sum_congr rfl (fun i _ => by ring : ∀ i ∈ Finset.univ,
    ((fun w => f w * c) (x + unit i) + (fun w => f w * c) (x - unit i))
      = (f (x + unit i) + f (x - unit i)) * c)]
  rw [← Finset.sum_mul]
  ring


-- Killed Chapman–Kolmogorov.  Induction on m generalizing x.
-- m = 0: Network.killedHeat_zero; Finset.sum_ite_eq; if x ∉ B the left side is 0 by
--   Network.killedHeat_of_source_not_mem.
-- m+1: rewrite `m + 1 + n = (m + n) + 1` (omega), Graph.Zd.killedHeat_succ_walkOp on both sides,
--   IH under the binder, walkOp_sum, walkOp_mul_const, split `if x ∈ B` (Finset.sum_ite_irrel or
--   by_cases).
/-- Killed Chapman-Kolmogorov: `killedHeat (m + n) x y` factors as a sum over the killing set `B`
of `killedHeat m x z * killedHeat n z y`. -/
private theorem killedHeat_add_eq_sum_mul (B : Finset (Site d)) (m n : ℕ) (x y : Site d) :
    Graph.killedHeat (lattice d) (B : Set (Site d)) (m + n) x y
      = ∑ z ∈ B, Graph.killedHeat (lattice d) (B : Set (Site d)) m x z
          * Graph.killedHeat (lattice d) (B : Set (Site d)) n z y := by
  classical
  induction m generalizing x with
  | zero =>
      rw [Nat.zero_add]
      by_cases hx : x ∈ B
      · have h1 : x ∈ (B : Set (Site d)) := hx
        simp only [Network.killedHeat_zero, if_pos h1, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq, if_pos hx]
      · have h0 : ¬ (x ∈ (B : Set (Site d))) := hx
        rw [Network.killedHeat_of_source_not_mem (G := lattice d) h0 n y]
        exact (Finset.sum_eq_zero (fun z _ => by
          simp only [Network.killedHeat_zero, if_neg h0, zero_mul])).symm
  | succ m ih =>
      rw [Nat.succ_add]
      by_cases hx : x ∈ B
      · have h1 : x ∈ (B : Set (Site d)) := hx
        simp only [Graph.Zd.killedHeat_succ_walkOp, if_pos h1]
        simp only [ih]
        rw [walkOp_sum B (fun z w => Graph.killedHeat (lattice d) (B : Set (Site d)) m w z
              * Graph.killedHeat (lattice d) (B : Set (Site d)) n z y) x]
        exact Finset.sum_congr rfl (fun z _ => walkOp_mul_const _ _ x)
      · have h0 : ¬ (x ∈ (B : Set (Site d))) := hx
        rw [Graph.Zd.killedHeat_succ_walkOp (B : Set (Site d)) (m + n) x y, if_neg h0]
        exact (Finset.sum_eq_zero (fun z _ => by
          rw [Graph.Zd.killedHeat_succ_walkOp (B : Set (Site d)) m x z, if_neg h0,
            zero_mul])).symm


-- killedHeat_add_eq_sum_mul; Finset.sum_le_sum with mul_le_mul_of_nonneg_left
-- (Network.killedHeat_nonneg);
-- ← Finset.sum_mul; unfold Network.survival.
/-- If `killedHeat n z y ≤ S` for every `z ∈ B`, then `killedHeat (k + n) x y ≤ Network.survival
B k x * S`. -/
theorem killedHeat_add_le_survival_mul (B : Finset (Site d)) (k n : ℕ) (x y : Site d)
    (S : ℝ)
    (hS : ∀ z ∈ B, Graph.killedHeat (lattice d) (B : Set (Site d)) n z y ≤ S) :
    Graph.killedHeat (lattice d) (B : Set (Site d)) (k + n) x y
      ≤ Network.survival (lattice d) B k x * S := by
  rw [killedHeat_add_eq_sum_mul B k n x y]
  calc ∑ z ∈ B, Graph.killedHeat (lattice d) (B : Set (Site d)) k x z
          * Graph.killedHeat (lattice d) (B : Set (Site d)) n z y
      ≤ ∑ z ∈ B, Graph.killedHeat (lattice d) (B : Set (Site d)) k x z * S :=
        Finset.sum_le_sum fun z hz =>
          mul_le_mul_of_nonneg_left (hS z hz) (Network.killedHeat_nonneg _ k x z)
    _ = (∑ z ∈ B, Graph.killedHeat (lattice d) (B : Set (Site d)) k x z) * S :=
        (Finset.sum_mul B _ S).symm
    _ = Network.survival (lattice d) B k x * S := rfl

end GreenTwoSided

end LatticeProb
