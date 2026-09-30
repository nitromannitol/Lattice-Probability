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
# The killed lazy walk

The lazy walk kernel `Q` killed on leaving a finite set `B` (`lazyKilled`), its Chapman-Kolmogorov
identity, its comparison with the free lazy kernel off `B`, and its binomial-mixture
representation in terms of `killedHeat`, used later to avoid parity issues in the lower bound.
-/

open Finset
open scoped Classical

namespace LatticeProb

namespace GreenTwoSided

variable {d : ℕ}

/-- The kernel of the lazy walk (`Q`, library `LatticeProb.Q`) killed on leaving `B`:
`lazyKilled B r x y = P_x(lazy walk stays in B up to time r, X_r = y)`. -/
noncomputable def lazyKilled (B : Finset (Site d)) : ℕ → Site d → Site d → ℝ
  | 0 => fun x y => if x ∈ B then (if x = y then 1 else 0) else 0
  | r + 1 => fun x y => if x ∈ B then
      lazyKilled B r x y / 2 + (∑ a : Dir d, lazyKilled B r (x + dirVec a) y) / (4 * (d : ℝ))
    else 0

-- Induction on r generalizing x; positivity (Finset.sum_nonneg) in both branches.
/-- `lazyKilled B r x y` is nonnegative for every `r`, by induction using positivity of a sum of
nonnegative terms. -/
private theorem lazyKilled_nonneg (B : Finset (Site d)) (r : ℕ) (x y : Site d) : 0 ≤ lazyKilled B r
    x y := by
  induction r generalizing x with
  | zero =>
      simp only [lazyKilled]
      split_ifs <;> norm_num
  | succ n ih =>
      simp only [lazyKilled]
      split_ifs with hx
      · have h1 : 0 ≤ lazyKilled B n x y / 2 := div_nonneg (ih x) (by norm_num)
        have h2 : 0 ≤ (∑ a : Dir d, lazyKilled B n (x + dirVec a) y) / (4 * (d : ℝ)) :=
          div_nonneg (Finset.sum_nonneg fun a _ => ih _) (by positivity)
        linarith
      · exact le_refl 0


-- cases r; unfold lazyKilled; if_neg.
/-- `lazyKilled B r x y = 0` whenever the first argument `x` is not in `B`. -/
private theorem lazyKilled_eq_zero_of_not_mem_left (B : Finset (Site d)) (r : ℕ) {x : Site d}
    (hx : x ∉ B) (y : Site d) :
    lazyKilled B r x y = 0 := by
  cases r with
  | zero => simp [lazyKilled, hx]
  | succ r => simp [lazyKilled, hx]


-- Induction on r generalizing x: r = 0 forces x = y ∈ B; step: every term vanishes by IH.
/-- `lazyKilled B r x y = 0` whenever the second argument `y` is not in `B`. -/
private theorem lazyKilled_eq_zero_of_not_mem_right (B : Finset (Site d)) (r : ℕ) (x : Site d)
    {y : Site d} (hy : y ∉ B) :
    lazyKilled B r x y = 0 := by
  induction r generalizing x with
  | zero =>
      simp only [lazyKilled]
      split_ifs with hx hxy
      · exact absurd (hxy ▸ hx) hy
      · rfl
      · rfl
  | succ r ih =>
      simp only [lazyKilled]
      split_ifs with hx
      · simp [ih]
      · rfl


-- Chapman–Kolmogorov, induction on m generalizing x (as killedHeat_add_eq_sum_mul):
-- m = 0: Finset.sum_ite_eq, lazyKilled_eq_zero_of_not_mem_left when x ∉ B.
-- m+1: `m + 1 + n = (m + n) + 1`, unfold lazyKilled, IH at x and at each x + dirVec a,
-- Finset.sum_div, Finset.sum_comm, Finset.sum_add_distrib, add_mul, Finset.sum_mul.  SPLIT?
/-- Chapman-Kolmogorov for the lazy killed kernel: `lazyKilled B (m+n) x y = ∑_{z ∈ B} lazyKilled
B m x z * lazyKilled B n z y`. -/
private theorem lazyKilled_add_eq_sum_mul (B : Finset (Site d)) (m n : ℕ) (x y : Site d) :
    lazyKilled B (m + n) x y = ∑ z ∈ B, lazyKilled B m x z * lazyKilled B n z y := by
  induction m generalizing x with
  | zero =>
      rw [Nat.zero_add]
      simp only [lazyKilled.eq_1]
      by_cases hx : x ∈ B
      · simp only [if_pos hx, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq]
      · simp only [if_neg hx, zero_mul, Finset.sum_const_zero]
        exact lazyKilled_eq_zero_of_not_mem_left B n hx y
  | succ m ih =>
      rw [Nat.add_right_comm]
      simp only [lazyKilled.eq_2]
      rw [ih x]
      by_cases hx : x ∈ B
      · simp only [if_pos hx]
        simp only [ih]
        rw [Finset.sum_comm, Finset.sum_div, Finset.sum_div]
        have hR :
            (∑ z ∈ B, (lazyKilled B m x z / 2 + (∑ a : Dir d, lazyKilled B m (x + dirVec a) z) / (4
                *
                    (d : ℝ))) * lazyKilled B n z y) = (∑ z ∈ B, (lazyKilled B m x z * lazyKilled B n
                        z y / 2 +
                            (∑ a : Dir d, lazyKilled B m (x + dirVec a) z * lazyKilled B n z y) /
                                (4 * (d : ℝ)))) :=
          Finset.sum_congr rfl (fun z _ => by
            rw [add_mul, div_mul_eq_mul_div, div_mul_eq_mul_div, Finset.sum_mul])
        rw [hR, Finset.sum_add_distrib]
      · simp [hx, Finset.sum_const_zero]


-- lazyKilled_add_eq_sum_mul; ∑ over S = ∑ over S ∩ B (lazyKilled_eq_zero_of_not_mem_right kills z ∉
-- B: Finset.sum_filter /
-- Finset.sum_subset) ≤ ∑ over B (Finset.sum_le_sum_of_subset_of_nonneg, lazyKilled_nonneg).
/-- For any `S`, `∑_{z ∈ S} lazyKilled B m x z * lazyKilled B n z y ≤ lazyKilled B (m+n) x y`,
since restricting the Chapman-Kolmogorov sum to `S` only shrinks it. -/
theorem sum_lazyKilled_mul_le_lazyKilled_add (B : Finset (Site d)) (m n : ℕ) (x y : Site d)
    (S : Finset (Site d)) :
    ∑ z ∈ S, lazyKilled B m x z * lazyKilled B n z y ≤ lazyKilled B (m + n) x y := by
  classical
  rw [lazyKilled_add_eq_sum_mul]
  have h1 : ∑ z ∈ S, lazyKilled B m x z * lazyKilled B n z y
      ≤ ∑ z ∈ S ∪ B, lazyKilled B m x z * lazyKilled B n z y :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      (fun z _ _ => mul_nonneg (lazyKilled_nonneg B m x z) (lazyKilled_nonneg B n z y))
  have h2 : ∑ z ∈ B, lazyKilled B m x z * lazyKilled B n z y
      = ∑ z ∈ S ∪ B, lazyKilled B m x z * lazyKilled B n z y :=
    Finset.sum_subset Finset.subset_union_right (fun z _ hzB => by
      rw [lazyKilled_eq_zero_of_not_mem_left B n hzB y, mul_zero])
  linarith


-- Comparison with the free lazy kernel.  Claim D_r(x) := Q^[r] δ₀(x - y) - lazyKilled r x y ≤ S,
-- induction on r generalizing x.  x ∉ B: lazyKilled = 0 (lazyKilled_eq_zero_of_not_mem_left), use
-- hS at j = r.
-- x ∈ B, r = 0: δ₀ - δ = 0 ≤ S.  x ∈ B, r+1: Function.iterate_succ_apply', unfold Q (library
-- `Q f x = f x/2 + (∑ a, f (x + dirVec a))/(4d)`), `x - y + dirVec a = (x + dirVec a) - y`
-- (add_sub_right_comm), D_{r+1}(x) = D_r(x)/2 + ∑_a D_r(x+a)/(4d) ≤ S/2 + (2d)S/(4d) = S
-- (Fintype.card (Dir d) = 2d: Fintype.card_prod, Fintype.card_fin, Fintype.card_bool).  SPLIT?
/-- Unfolds `lazyKilled B 0 x y` to its defining `if`-expression. -/
private theorem lazyKilled_zero_eq {d : ℕ} (B : Finset (Site d)) (x y : Site d) :
    lazyKilled B 0 x y = (if x ∈ B then (if x = y then (1 : ℝ) else 0) else 0) := rfl

/-- Unfolds `lazyKilled B (r+1) x y` to its defining recursive `if`-expression. -/
private theorem lazyKilled_succ_eq {d : ℕ} (B : Finset (Site d)) (r : ℕ) (x y : Site d) :
    lazyKilled B (r + 1) x y = (if x ∈ B then lazyKilled B r x y / 2
      + (∑ a : Dir d, lazyKilled B r (x + dirVec a) y) / (4 * (d : ℝ)) else 0) := rfl

/-- One step of the lazy walk operator `Q` applied to `delta0`: `Q^[r+1] delta0 x = Q^[r] delta0
x / 2 + (∑_a Q^[r] delta0 (x + dirVec a)) / (4d)`. -/
private theorem iterate_Q_succ_delta0_eq {d : ℕ} (r : ℕ) (x : Site d) :
    Q^[r + 1] (delta0 : Site d → ℝ) x = Q^[r] (delta0 : Site d → ℝ) x / 2
      + (∑ a : Dir d, Q^[r] (delta0 : Site d → ℝ) (x + dirVec a)) / (4 * (d : ℝ)) := by
  rw [Function.iterate_succ_apply']
  rfl

/-- Reindexes the neighbour sum of `Q^[r] delta0` at `(x-y) + dirVec a` as `(x + dirVec a) - y`. -/
private theorem sum_iterate_Q_delta0_sub_add_eq {d : ℕ} (r : ℕ) (x y : Site d) :
    (∑ a : Dir d, Q^[r] (delta0 : Site d → ℝ) ((x - y) + dirVec a))
      = ∑ a : Dir d, Q^[r] (delta0 : Site d → ℝ) ((x + dirVec a) - y) :=
  Finset.sum_congr rfl fun a _ => by rw [← add_sub_right_comm]

/-- Implementation lemma for `le_lazyKilled_of_forall_le`: if `Q^[j] delta0 (z-y) ≤ S` for all `j
≤ r` and `z ∉ B`, then `Q^[r] delta0 (x-y) - S ≤ lazyKilled B r x y`. -/
private theorem le_lazyKilled_of_forall_le' (hd : 1 ≤ d) (B : Finset (Site d)) (y : Site d) (S : ℝ)
    (hS0 : 0 ≤ S) :
    ∀ r : ℕ, (∀ j ≤ r, ∀ z : Site d, z ∉ B → Q^[j] (delta0 : Site d → ℝ) (z - y) ≤ S) →
      ∀ x : Site d, Q^[r] (delta0 : Site d → ℝ) (x - y) - S ≤ lazyKilled B r x y := by
  intro r
  induction r with
  | zero =>
    intro hS' x
    by_cases hx : x ∈ B
    · rw [lazyKilled_zero_eq, if_pos hx]
      simp only [Function.iterate_zero, id_eq]
      have hδ : delta0 (x - y) ≤ (if x = y then (1 : ℝ) else 0) := by
        by_cases hxy : x = y
        · rw [sub_eq_zero.mpr hxy, if_pos hxy]
          simp [delta0]
        · rw [if_neg hxy]
          have hne : x - y ≠ 0 := fun h => hxy (sub_eq_zero.mp h)
          simp [delta0, hne]
      linarith
    · rw [lazyKilled_zero_eq, if_neg hx]
      simp only [Function.iterate_zero, id_eq]
      have h0 : delta0 (x - y) ≤ S := by
        simpa only [Function.iterate_zero, id_eq] using hS' 0 le_rfl x hx
      linarith
  | succ r ih =>
    intro hS' x
    have ih' : ∀ z : Site d, Q^[r] (delta0 : Site d → ℝ) (z - y) - S ≤ lazyKilled B r z y :=
      fun z => ih (fun j hj z hz => hS' j (Nat.le_succ_of_le hj) z hz) z
    by_cases hx : x ∈ B
    · rw [lazyKilled_succ_eq, if_pos hx]
      rw [iterate_Q_succ_delta0_eq, sum_iterate_Q_delta0_sub_add_eq r x y]
      have h1 : Q^[r] (delta0 : Site d → ℝ) (x - y) / 2 - lazyKilled B r x y / 2 ≤ S / 2 := by
        linarith [ih' x]
      have hsum : ∑ a : Dir d, Q^[r] (delta0 : Site d → ℝ) ((x + dirVec a) - y)
          ≤ ∑ a : Dir d, (lazyKilled B r (x + dirVec a) y + S) :=
        Finset.sum_le_sum fun a _ => by linarith [ih' (x + dirVec a)]
      have hsum2 : ∑ a : Dir d, (lazyKilled B r (x + dirVec a) y + S)
          = (∑ a : Dir d, lazyKilled B r (x + dirVec a) y) + 2 * (d : ℝ) * S := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
        push_cast
        ring
      have hpos : (0 : ℝ) < 4 * (d : ℝ) := by
        have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
        positivity
      have h2 : (∑ a : Dir d, Q^[r] (delta0 : Site d → ℝ) ((x + dirVec a) - y))
            / (4 * (d : ℝ))
          - (∑ a : Dir d, lazyKilled B r (x + dirVec a) y) / (4 * (d : ℝ)) ≤ S / 2 := by
        rw [← sub_div, div_le_iff₀ hpos]
        rw [show S / 2 * (4 * (d : ℝ)) = 2 * (d : ℝ) * S by ring]
        linarith
      linarith
    · rw [lazyKilled_succ_eq, if_neg hx]
      have h0 : Q^[r + 1] (delta0 : Site d → ℝ) (x - y) ≤ S := hS' (r + 1) le_rfl x hx
      linarith

/-- Comparison with the free lazy kernel: if the free kernel is at most `S` off `B` up to time
`r`, then `Q^[r] delta0 (x-y) - S ≤ lazyKilled B r x y`. -/
theorem le_lazyKilled_of_forall_le (hd : 1 ≤ d) (B : Finset (Site d)) (y : Site d) (S : ℝ)
    (hS0 : 0 ≤ S)
    (r : ℕ) (hS : ∀ j ≤ r, ∀ z : Site d, z ∉ B → Q^[j] (delta0 : Site d → ℝ) (z - y) ≤ S)
    (x : Site d) :
    Q^[r] (delta0 : Site d → ℝ) (x - y) - S ≤ lazyKilled B r x y := by
  exact le_lazyKilled_of_forall_le' hd B y S hS0 r hS x


-- Binomial mixture.  Induction on r generalizing x, modelled on the library's
-- iterate_delta0_eq_binom (walkOp_binom, pascal_sum_srwHeat): Pascal (Nat.choose_succ_succ,
-- Finset.sum_range_succ'), Graph.Zd.killedHeat_succ_walkOp, LatticeProb.walkOp = nbrSum/(2d)
-- and LocalCLT.sum_dir_eq_sum_unit (Dir-sum = nbrSum); if x ∉ B both sides are 0
-- (Network.killedHeat_of_source_not_mem, lazyKilled_eq_zero_of_not_mem_left).  SPLIT?
/-- `walkOp (c * g) = c * walkOp g`, the scalar-multiplication case of linearity of the averaging
operator. -/
private theorem walkOp_const_mul_eq (c : ℝ) (g : Site d → ℝ) (x : Site d) :
    LatticeProb.walkOp (fun z => c * g z) x = c * LatticeProb.walkOp g x := by
  simp only [walkOp_eq_sum_dir]
  rw [← mul_div_assoc, Finset.mul_sum]

/-- Pascal's rule rewritten as a splitting identity for the weighted sum `∑_{k<r+2} C(r+1,k) f k`
into two sums over `range (r+1)` at `f k` and `f (k+1)`. -/
private theorem sum_range_choose_succ_eq_add (f : ℕ → ℝ) (r : ℕ) :
    ∑ k ∈ Finset.range (r + 1 + 1), ((r + 1).choose k : ℝ) * f k
      = ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * f k
        + ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * f (k + 1) := by
  have h1 : ∑ k ∈ Finset.range (r + 1 + 1), ((r + 1).choose k : ℝ) * f k
      = ∑ k ∈ Finset.range (r + 1), ((r + 1).choose (k + 1) : ℝ) * f (k + 1)
        + ((r + 1).choose 0 : ℝ) * f 0 :=
    Finset.sum_range_succ' (fun k => ((r + 1).choose k : ℝ) * f k) (r + 1)
  have h2 : ∑ k ∈ Finset.range (r + 1), ((r + 1).choose (k + 1) : ℝ) * f (k + 1)
      = ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * f (k + 1)
        + ∑ k ∈ Finset.range (r + 1), (r.choose (k + 1) : ℝ) * f (k + 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.choose_succ_succ]
    push_cast
    ring
  have h3 : ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * f k
      = ∑ k ∈ Finset.range r, (r.choose (k + 1) : ℝ) * f (k + 1) + (r.choose 0 : ℝ) * f 0 :=
    Finset.sum_range_succ' (fun k => (r.choose k : ℝ) * f k) r
  have h4 : ∑ k ∈ Finset.range (r + 1), (r.choose (k + 1) : ℝ) * f (k + 1)
      = ∑ k ∈ Finset.range r, (r.choose (k + 1) : ℝ) * f (k + 1)
        + (r.choose (r + 1) : ℝ) * f (r + 1) :=
    Finset.sum_range_succ (fun k => (r.choose (k + 1) : ℝ) * f (k + 1)) r
  have h5 : (r.choose (r + 1) : ℝ) = 0 := by
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    norm_num
  have h6 : ((r + 1).choose 0 : ℝ) = 1 := by simp
  have h7 : (r.choose 0 : ℝ) = 1 := by simp
  rw [h5, zero_mul, add_zero] at h4
  rw [h6, one_mul] at h1
  rw [h7, one_mul] at h3
  linarith [h1, h2, h3, h4]

/-- The Pascal splitting identity `sum_range_choose_succ_eq_add` specialized to `f = killedHeat`. -/
private theorem sum_range_choose_killedHeat_succ_eq_add (B : Finset (Site d)) (r : ℕ) (x y : Site d)
    :
    ∑ k ∈ Finset.range (r + 1 + 1),
        ((r + 1).choose k : ℝ) * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y
      = ∑ k ∈ Finset.range (r + 1),
          (r.choose k : ℝ) * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y
        + ∑ k ∈ Finset.range (r + 1),
          (r.choose k : ℝ) * Graph.killedHeat (lattice d) (B : Set (Site d)) (k + 1) x y := by
  simpa using sum_range_choose_succ_eq_add
    (fun k => Graph.killedHeat (lattice d) (B : Set (Site d)) k x y) r

/-- For `x ∈ B`, `walkOp` of the binomial mixture `∑_k C(r,k) killedHeat k · y` at `x` equals the
shifted mixture `∑_k C(r,k) killedHeat (k+1) x y`. -/
private theorem walkOp_sum_choose_killedHeat_eq (B : Finset (Site d)) (r : ℕ) (x y : Site d)
    (hxB : x ∈ B) :
    LatticeProb.walkOp (fun z => ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) *
        Graph.killedHeat (lattice d) (B : Set (Site d)) k z y) x
      = ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) *
        Graph.killedHeat (lattice d) (B : Set (Site d)) (k + 1) x y := by
  have hterm : ∀ k ∈ Finset.range (r + 1), (r.choose k : ℝ) *
        Graph.killedHeat (lattice d) (B : Set (Site d)) (k + 1) x y
      = (∑ a : Dir d, (r.choose k : ℝ) *
          Graph.killedHeat (lattice d) (B : Set (Site d)) k (x + dirVec a) y)
        / (2 * (d : ℝ)) := by
    intro k _
    rw [Graph.Zd.killedHeat_succ_walkOp (B : Set (Site d)) k x y, Finset.mem_coe, if_pos hxB]
    simp only [walkOp_eq_sum_dir]
    rw [← Finset.mul_sum, mul_div_assoc]
  have hswap : ∑ a : Dir d, ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) *
        Graph.killedHeat (lattice d) (B : Set (Site d)) k (x + dirVec a) y
      = ∑ k ∈ Finset.range (r + 1), ∑ a : Dir d, (r.choose k : ℝ) *
        Graph.killedHeat (lattice d) (B : Set (Site d)) k (x + dirVec a) y :=
    Finset.sum_comm
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  simp only [walkOp_eq_sum_dir]
  rw [hswap]

/-- Restates `lazyKilled B 0 x y` as the `if x ∈ B then (if x = y then 1 else 0) else 0`
indicator, by `rfl`. -/
private theorem lazyKilled_zero_eq_ite (B : Finset (Site d)) (x y : Site d) :
    lazyKilled B 0 x y = if x ∈ B then (if x = y then 1 else 0) else 0 := rfl

/-- Restates `lazyKilled B (r+1) x y` as its defining `if`-expression, by `rfl`. -/
private theorem lazyKilled_succ_eq_ite (B : Finset (Site d)) (r : ℕ) (x y : Site d) :
    lazyKilled B (r + 1) x y = if x ∈ B then
      lazyKilled B r x y / 2 + (∑ a : Dir d, lazyKilled B r (x + dirVec a) y) / (4 * (d : ℝ))
      else 0 := rfl

/-- `lazyKilled B (r+1) x y` equals `Q (lazyKilled B r · y) x` when `x ∈ B`, and `0` otherwise,
i.e. one step of the lazy operator `Q`. -/
private theorem lazyKilled_succ_eq_Q (B : Finset (Site d)) (r : ℕ) (x y : Site d) :
    lazyKilled B (r + 1) x y = if x ∈ B then Q (fun z => lazyKilled B r z y) x else 0 := by
  rw [lazyKilled_succ_eq_ite]
  by_cases hxB : x ∈ B
  · rw [if_pos hxB, if_pos hxB, Q_eq_walkOp, walkOp_eq_sum_dir]
    rw [add_div, div_div, show (2 * (d : ℝ)) * 2 = 4 * (d : ℝ) by ring]
  · rw [if_neg hxB, if_neg hxB]

/-- The binomial-mixture identity: `lazyKilled B r x y = 2^{-r} ∑_{k ≤ r} C(r,k) killedHeat k x
y`. -/
private theorem lazyKilled_eq_sum_choose_killedHeat (_unused_hd : 1 ≤ d) (B : Finset (Site d))
    (r : ℕ) (x y : Site d) :
    lazyKilled B r x y = (2 : ℝ)⁻¹ ^ r *
      ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * Graph.killedHeat (lattice d) (B : Set (Site d))
          k x y := by
  induction r generalizing x with
  | zero =>
    rw [lazyKilled_zero_eq_ite, Finset.sum_range_one, Network.killedHeat_zero, pow_zero,
      Nat.choose_zero_right, Nat.cast_one, one_mul]
    by_cases h : x ∈ B <;> simp [h]
  | succ r ih =>
    rw [lazyKilled_succ_eq_Q]
    by_cases hxB : x ∈ B
    · rw [if_pos hxB]
      have hfun : (fun z : Site d => lazyKilled B r z y) = fun z => (2 : ℝ)⁻¹ ^ r *
          (∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) *
            Graph.killedHeat (lattice d) (B : Set (Site d)) k z y) := funext ih
      rw [hfun]
      simp only [Q_eq_walkOp, walkOp_const_mul_eq]
      rw
          [walkOp_sum_choose_killedHeat_eq B r x y hxB, sum_range_choose_killedHeat_succ_eq_add B r
              x y, pow_succ]
      ring
    · rw [if_neg hxB, Finset.sum_eq_zero (fun k _ => by
        rw [Network.killedHeat_of_source_not_mem (C := (B : Set (Site d)))
          (by simpa using hxB) k y, mul_zero]), mul_zero]


-- lazyKilled_eq_sum_choose_killedHeat written with binomWeight (binomWeight_of_le /
-- binomWeight_of_lt, extend every
-- inner sum to range (R+1), R := T.sup id); Finset.sum_comm; for each k,
-- ∑_{r ∈ T} binomWeight k r ≤ 2 (sum_le_hasSum with hasSum_binomWeight k, binomWeight_nonneg);
-- then ∑_{k ≤ R} killedHeat k ≤ tsum (Summable.sum_le_tsum, Network.summable_killedHeat with
-- q ∉ B, Graph.Zd.latticeConnected).  SPLIT?
/-- Implementation lemma for `sum_lazyKilled_le_two_mul_tsum_killedHeat`. -/
private theorem sum_lazyKilled_le_two_mul_tsum_killedHeat' (hd : 1 ≤ d) (B : Finset (Site d))
    (x y : Site d) (T : Finset ℕ) :
    ∑ r ∈ T, lazyKilled B r x y
      ≤ 2 * ∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y := by
  haveI : NeZero d := NeZero.of_pos (by omega)
  let R : ℕ := T.sup (id : ℕ → ℕ)
  have hsub : T ⊆ Finset.range (R + 1) := by
    intro r hr
    rw [Finset.mem_range]
    have h1 : r ≤ R := le_sup (f := id) hr
    omega
  have hlazy : ∀ r ∈ T, lazyKilled B r x y
      = ∑ k ∈ Finset.range (R + 1), binomWeight k r
          * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y := by
    intro r hr
    have hmem : r ∈ Finset.range (R + 1) := hsub hr
    have hrle : r + 1 ≤ R + 1 := by
      rw [Finset.mem_range] at hmem
      omega
    have step1 : (∑ k ∈ Finset.range (r + 1), 2⁻¹ ^ r * ((r.choose k : ℝ)
          * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y))
        = ∑ k ∈ Finset.range (r + 1), binomWeight k r
          * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ r := by
        rw [Finset.mem_range] at hk
        omega
      rw [binomWeight_of_le hk']
      ring
    have step2 : (∑ k ∈ Finset.range (r + 1), binomWeight k r
          * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y)
        = ∑ k ∈ Finset.range (R + 1), binomWeight k r
          * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y := by
      apply Finset.sum_subset (Finset.range_subset_range.mpr hrle)
      intro k hk hkr
      rw [Finset.mem_range] at hkr
      rw [binomWeight_of_lt (show r < k by omega)]
      ring
    rw [lazyKilled_eq_sum_choose_killedHeat hd B r x y, Finset.mul_sum, step1, step2]
  have hbw : ∀ k ∈ Finset.range (R + 1), (∑ r ∈ T, binomWeight k r) ≤ 2 := by
    intro k _
    exact sum_le_hasSum T (fun r _ => binomWeight_nonneg k r) (hasSum_binomWeight k)
  have hfin : (∑ r ∈ T, ∑ k ∈ Finset.range (R + 1), binomWeight k r
        * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y)
      ≤ ∑ k ∈ Finset.range (R + 1), 2
        * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro k hk
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hbw k hk)
      (Network.killedHeat_nonneg (B : Set (Site d)) k x y)
  have htsum : (∑ k ∈ Finset.range (R + 1), 2
        * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y)
      ≤ 2 * ∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y := by
    obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset B
    have hsum : Summable (fun k : ℕ => (2 : ℝ)
        * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y) :=
      (Network.summable_killedHeat (Graph.Zd.latticeConnected d) B hq x y).mul_left 2
    have h := Summable.sum_le_tsum (Finset.range (R + 1))
      (fun i _ => mul_nonneg (by norm_num)
        (Network.killedHeat_nonneg (B : Set (Site d)) i x y)) hsum
    rwa [tsum_mul_left] at h
  calc ∑ r ∈ T, lazyKilled B r x y
      ≤ ∑ r ∈ T, ∑ k ∈ Finset.range (R + 1), binomWeight k r
          * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y :=
        Finset.sum_le_sum (fun r hr => le_of_eq (hlazy r hr))
    _ ≤ ∑ k ∈ Finset.range (R + 1), 2
          * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y := hfin
    _ ≤ 2 * ∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y := htsum

/-- For any finite set `T` of times, `∑_{r ∈ T} lazyKilled B r x y ≤ 2 ∑' k, killedHeat k x y`,
since the binomial weights of `lazyKilled` sum to at most `2` at each time `k`. -/
theorem sum_lazyKilled_le_two_mul_tsum_killedHeat (hd : 1 ≤ d) (B : Finset (Site d))
    (x y : Site d) (T : Finset ℕ) :
    ∑ r ∈ T, lazyKilled B r x y
      ≤ 2 * ∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y := by
  exact sum_lazyKilled_le_two_mul_tsum_killedHeat' hd B x y T

end GreenTwoSided

end LatticeProb
