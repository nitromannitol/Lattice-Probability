/-
The first-passage decomposition of the transition kernel at the exit time of a
set.

A path of length `k` from `x` either has stayed in `C` throughout, which is what
`LatticeProb.Graph.killedHeat` counts, or has left `C` at some time `j ≤ k` and
travelled freely for the remaining `k - j` steps.  The second part is
`exitHeat G C y k x = E_x[p_{k - τ_C}(X_{τ_C}, y)]`, and it is defined here by
its own first-step recursion rather than as a sum over the exit time: inside `C`
it is the average of its previous stage over the neighbours, outside `C` it is
the free kernel.  With that definition the decomposition

    p_k(x,y) = p^C_k(x,y) + exitHeat C y k x

is one induction on `k`, because both sides satisfy the same recursion.

Summing on `k` gives the identity the applications use,

    G(x,y) = g^C(x,y) + E_x[G(X_{τ_C}, y)] ,

with the last term read as `∑_k exitHeat C y k x`.  What makes that reading
usable is `tsum_exitHeat_le`: the exit average of the Green function is bounded
by the supremum of the Green function over the complement of `C`, which is the
form the applications need, and it is proved from the partial sums, whose own
recursion is `sum_range_exitHeat_succ`.
-/
import LatticeProb.Network.Killed
import LatticeProb.Graph.Zd

namespace LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

open scoped Classical
open LatticeProb.Network (killedHeat_zero killedHeat_succ killedHeat_nonneg)

/-- The one-step average of a constant is that constant. -/
theorem walkOp_const_of_deg_pos {x : V} (hx : 0 < G.degree x) (c : ℝ) :
    walkOp G (fun _ => c) x = c := by
  have hd : (G.degree x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  rw [walkOp, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
  field_simp

/-- The one-step average is additive. -/
theorem walkOp_add' (f g : V → ℝ) (x : V) :
    walkOp G (fun z => f z + g z) x = walkOp G f x + walkOp G g x := by
  rw [walkOp, walkOp, walkOp, Finset.sum_add_distrib, add_div]

/-! ### The kernel carried by the paths that have left the set -/

/-- `exitHeat G C y k x = E_x[p_{k - τ_C}(X_{τ_C}, y)]`, the part of the `k`-step
transition probability from `x` to `y` carried by the paths that have already
left `C`.  It is defined by the first-step recursion: inside `C` nothing has
happened yet and the value is the neighbour average of the previous stage;
outside `C` the exit time is zero and the value is the free kernel. -/
noncomputable def exitHeat (G : SimpleGraph V) [G.LocallyFinite] (C : Set V) (y : V) :
    ℕ → V → ℝ
  | 0 => fun x => if x ∈ C then 0 else (if x = y then 1 else 0)
  | k + 1 => fun x => if x ∈ C then walkOp G (exitHeat G C y k) x else heat G (k + 1) x y

theorem exitHeat_zero (C : Set V) (y x : V) :
    exitHeat G C y 0 x = if x ∈ C then 0 else (if x = y then 1 else 0) := rfl

theorem exitHeat_succ (C : Set V) (y : V) (k : ℕ) (x : V) :
    exitHeat G C y (k + 1) x
      = if x ∈ C then walkOp G (exitHeat G C y k) x else heat G (k + 1) x y := rfl

theorem exitHeat_of_notMem {C : Set V} {x : V} (hx : x ∉ C) (y : V) :
    ∀ k : ℕ, exitHeat G C y k x = heat G k x y := by
  intro k
  cases k with
  | zero => rw [exitHeat_zero, if_neg hx]; rfl
  | succ k => rw [exitHeat_succ, if_neg hx]

theorem exitHeat_nonneg (C : Set V) (y : V) : ∀ (k : ℕ) (x : V), 0 ≤ exitHeat G C y k x := by
  intro k
  induction k with
  | zero =>
      intro x
      rw [exitHeat_zero]
      split_ifs <;> norm_num
  | succ k ih =>
      intro x
      rw [exitHeat_succ]
      split_ifs with h
      · exact div_nonneg (Finset.sum_nonneg fun z _ => ih z) (Nat.cast_nonneg _)
      · exact heat_nonneg _ _ _

/-! ### The decomposition -/

/-- **The first-passage decomposition at the exit time.**  A path counted by the
`k`-step transition kernel has either stayed in `C` or left it. -/
theorem heat_eq_killedHeat_add_exitHeat (C : Set V) (y : V) :
    ∀ (k : ℕ) (x : V), heat G k x y = killedHeat G C k x y + exitHeat G C y k x := by
  intro k
  induction k with
  | zero =>
      intro x
      rw [killedHeat_zero, exitHeat_zero]
      by_cases hx : x ∈ C
      · simp [hx, heat]
      · simp [hx, heat]
  | succ k ih =>
      intro x
      by_cases hx : x ∈ C
      · rw [exitHeat_succ, if_pos hx, killedHeat_succ, if_pos hx, heat_succ]
        rw [show (∑ z ∈ G.neighborFinset x, killedHeat G C k z y) / (G.degree x : ℝ)
              = walkOp G (fun z => killedHeat G C k z y) x from rfl]
        rw [← walkOp_add']
        exact congrArg (fun f => walkOp G f x) (funext fun z => ih z)
      · rw [exitHeat_succ, if_neg hx, killedHeat_succ, if_neg hx, zero_add]

/-! ### Summing the decomposition -/

theorem walkOp_sum_range (n : ℕ) (f : ℕ → V → ℝ) (x : V) :
    ∑ k ∈ Finset.range n, walkOp G (f k) x
      = walkOp G (fun z => ∑ k ∈ Finset.range n, f k z) x :=
  (walkOp_sum n f x).symm

/-- The partial sums of `exitHeat` satisfy the same recursion, with the free
Green function of the elapsed time as the value outside `C`. -/
theorem sum_range_exitHeat_succ (C : Set V) (y : V) (n : ℕ) (x : V) :
    ∑ k ∈ Finset.range (n + 1), exitHeat G C y k x
      = if x ∈ C then walkOp G (fun z => ∑ k ∈ Finset.range n, exitHeat G C y k z) x
        else meanLocalTime G (n + 1) x y := by
  by_cases hx : x ∈ C
  · rw [if_pos hx, Finset.sum_range_succ']
    have h0 : exitHeat G C y 0 x = 0 := by rw [exitHeat_zero, if_pos hx]
    rw [h0, add_zero]
    rw [← walkOp_sum_range]
    exact Finset.sum_congr rfl fun k _ => by rw [exitHeat_succ, if_pos hx]
  · rw [if_neg hx, meanLocalTime]
    exact Finset.sum_congr rfl fun k _ => exitHeat_of_notMem hx y k

theorem sum_range_exitHeat_nonneg (C : Set V) (y : V) (n : ℕ) (x : V) :
    0 ≤ ∑ k ∈ Finset.range n, exitHeat G C y k x :=
  Finset.sum_nonneg fun k _ => exitHeat_nonneg C y k x

/-- The exit average of the free Green function is bounded by the supremum of the
free Green function over the complement of `C`. -/
theorem sum_range_exitHeat_le (hdeg : ∀ v : V, 0 < G.degree v) (C : Set V) (y : V)
    {M : ℝ} (hM : 0 ≤ M) (hout : ∀ w ∉ C, ∀ n : ℕ, meanLocalTime G n w y ≤ M) :
    ∀ (n : ℕ) (x : V), ∑ k ∈ Finset.range n, exitHeat G C y k x ≤ M := by
  intro n
  induction n with
  | zero => intro x; simpa using hM
  | succ n ih =>
      intro x
      rw [sum_range_exitHeat_succ]
      by_cases hx : x ∈ C
      · rw [if_pos hx]
        refine le_trans (walkOp_mono (g := fun _ => M) (fun v => ih v) x) ?_
        rw [walkOp_const_of_deg_pos (hdeg x)]
      · rw [if_neg hx]
        exact hout x hx (n + 1)

/-! ### The summed identity -/

theorem meanLocalTime_le_tsum {x y : V} (h : Summable fun k => heat G k x y) (n : ℕ) :
    meanLocalTime G n x y ≤ ∑' k, heat G k x y :=
  Summable.sum_le_tsum _ (fun k _ => heat_nonneg k x y) h

theorem summable_killedHeat_of_heat (C : Set V) {x y : V}
    (h : Summable fun k => heat G k x y) : Summable fun k => killedHeat G C k x y :=
  Summable.of_nonneg_of_le (fun k => killedHeat_nonneg C k x y)
    (fun k => by
      have := heat_eq_killedHeat_add_exitHeat (G := G) C y k x
      have hnn := exitHeat_nonneg (G := G) C y k x
      linarith) h

theorem summable_exitHeat_of_heat (C : Set V) {x y : V}
    (h : Summable fun k => heat G k x y) : Summable fun k => exitHeat G C y k x :=
  Summable.of_nonneg_of_le (fun k => exitHeat_nonneg C y k x)
    (fun k => by
      have := heat_eq_killedHeat_add_exitHeat (G := G) C y k x
      have hnn := killedHeat_nonneg (G := G) C k x y
      linarith) h

/-- **The first-passage decomposition of the Green function.**  The expected
number of visits to `y` splits into the visits before leaving `C` and the exit
average of the Green function,
`G(x,y) = g^C(x,y) + E_x[G(X_{τ_C}, y)]`. -/
theorem tsum_heat_eq_tsum_killedHeat_add_tsum_exitHeat (C : Set V) {x y : V}
    (h : Summable fun k => heat G k x y) :
    ∑' k, heat G k x y
      = (∑' k, killedHeat G C k x y) + ∑' k, exitHeat G C y k x := by
  rw [← Summable.tsum_add (summable_killedHeat_of_heat C h) (summable_exitHeat_of_heat C h)]
  exact tsum_congr fun k => heat_eq_killedHeat_add_exitHeat C y k x

/-- The exit average of the Green function is bounded by the supremum of the
Green function over the complement of `C`. -/
theorem tsum_exitHeat_le (hdeg : ∀ v : V, 0 < G.degree v) (C : Set V) (y : V)
    {M : ℝ} (hM : 0 ≤ M) (hout : ∀ w ∉ C, ∀ n : ℕ, meanLocalTime G n w y ≤ M) (x : V) :
    ∑' k, exitHeat G C y k x ≤ M :=
  Real.tsum_le_of_sum_range_le (fun k => exitHeat_nonneg C y k x)
    (fun n => sum_range_exitHeat_le hdeg C y hM hout n x)

/-! ### On the lattice

The three kernels satisfy their recursions with `LatticeProb.walkOp`, the
average over the `2d` unit vectors, which is the form the lattice papers write
them in. -/

end LatticeProb.Graph

namespace LatticeProb.Graph.Zd

open LatticeProb.Graph
open scoped Classical

variable {d : ℕ}

theorem heat_succ_walkOp (k : ℕ) (x y : Site d) :
    heat (lattice d) (k + 1) x y
      = LatticeProb.walkOp (fun z => heat (lattice d) k z y) x := by
  rw [heat_succ, walkOp_eq]

theorem killedHeat_succ_walkOp (C : Set (Site d)) (k : ℕ) (x y : Site d) :
    killedHeat (lattice d) C (k + 1) x y
      = if x ∈ C then LatticeProb.walkOp (fun z => killedHeat (lattice d) C k z y) x else 0 := by
  rw [show killedHeat (lattice d) C (k + 1) x y
        = if x ∈ C then walkOp (lattice d) (fun z => killedHeat (lattice d) C k z y) x else 0
      from rfl, walkOp_eq]

theorem exitHeat_succ_walkOp (C : Set (Site d)) (y : Site d) (k : ℕ) (x : Site d) :
    exitHeat (lattice d) C y (k + 1) x
      = if x ∈ C then LatticeProb.walkOp (exitHeat (lattice d) C y k) x
        else heat (lattice d) (k + 1) x y := by
  rw [exitHeat_succ, walkOp_eq]

end LatticeProb.Graph.Zd
