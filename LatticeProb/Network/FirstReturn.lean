/-
The first-passage decomposition of the killed kernel, and the escape
probability.

The walk killed outside `C` reaches `o` at time `k` by first reaching it at some
time `j ≤ k` and then returning to it in the remaining `k - j` steps.  Written on
the kernels that is

  `p^C_k(x, o) = ∑_{j ≤ k} f_j(x) p^C_{k-j}(o, o)`,

with `f_j(x)` the probability of FIRST reaching `o` at time `j`, defined by its
own recursion: it is one at `j = 0, x = o`, zero at `x = o` afterwards, and
otherwise one step of the walk.  Summing on `k` at `x = o` turns the
decomposition into the renewal identity `N = 1 + ρ N`, where `N` is the expected
number of visits to `o` before leaving `C` and `ρ` the probability of returning
to `o` at all.  Hence

  `1 - ρ = 1 / N = 1 / (deg(o) · R_eff)`,

which is the escape probability as the reciprocal of the effective resistance,
now with `1 - ρ` built from the kernel rather than read off a potential.
-/
import LatticeProb.Network.Escape

open Finset
open scoped Classical

namespace LatticeProb.Network

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-! ### The first-passage kernel -/

/-- `firstHit G C o k x` is the probability that the walk from `x`, killed
outside `C`, is at `o` for the FIRST time at step `k`. -/
noncomputable def firstHit (G : SimpleGraph V) [G.LocallyFinite] (C : Set V) (o : V) :
    ℕ → V → ℝ
  | 0 => fun x => if x = o then 1 else 0
  | k + 1 => fun x => if x = o then 0 else
      if x ∈ C then (∑ z ∈ G.neighborFinset x, firstHit G C o k z) / G.degree x else 0

theorem firstHit_zero (C : Set V) (o x : V) :
    firstHit G C o 0 x = if x = o then 1 else 0 := rfl

theorem firstHit_succ (C : Set V) (o : V) (k : ℕ) (x : V) :
    firstHit G C o (k + 1) x = if x = o then 0 else
      if x ∈ C then (∑ z ∈ G.neighborFinset x, firstHit G C o k z) / G.degree x else 0 := rfl

theorem firstHit_succ_source (C : Set V) (o : V) (k : ℕ) :
    firstHit G C o (k + 1) o = 0 := by
  rw [firstHit_succ, if_pos rfl]

theorem firstHit_of_not_mem {C : Set V} {o x : V} (hx : x ∉ C) (hxo : x ≠ o) (k : ℕ) :
    firstHit G C o k x = 0 := by
  cases k with
  | zero => rw [firstHit_zero, if_neg hxo]
  | succ k => rw [firstHit_succ, if_neg hxo, if_neg hx]

theorem firstHit_nonneg (C : Set V) (o : V) : ∀ (k : ℕ) (x : V), 0 ≤ firstHit G C o k x := by
  intro k
  induction k with
  | zero =>
      intro x
      rw [firstHit_zero]
      split <;> norm_num
  | succ k ih =>
      intro x
      rw [firstHit_succ]
      split
      · exact le_rfl
      · split
        · exact div_nonneg (Finset.sum_nonneg fun z _ => ih z) (by positivity)
        · exact le_rfl

/-! ### The decomposition -/

/-- **The first-passage decomposition.**  Reaching `o` at time `k` is reaching it
first at some time `j` and returning in the rest. -/
theorem killedHeat_eq_sum_firstHit {C : Set V} {o : V} (ho : o ∈ C) :
    ∀ (k : ℕ) (x : V), killedHeat G C k x o
      = ∑ j ∈ Finset.range (k + 1), firstHit G C o j x * killedHeat G C (k - j) o o := by
  intro k
  induction k with
  | zero =>
      intro x
      rw [Finset.sum_range_one, Nat.sub_self, firstHit_zero, killedHeat_zero, killedHeat_zero,
        if_pos ho, if_pos rfl, mul_one]
      by_cases hx : x ∈ C
      · rw [if_pos hx]
      · rw [if_neg hx, if_neg (fun h : x = o => hx (by rw [h]; exact ho))]
  | succ k ih =>
      intro x
      by_cases hxo : x = o
      · subst hxo
        rw [Finset.sum_range_succ'
          (fun j => firstHit G C x j x * killedHeat G C (k + 1 - j) x x) (k + 1)]
        have hzero : ∀ i ∈ Finset.range (k + 1),
            firstHit G C x (i + 1) x * killedHeat G C (k + 1 - (i + 1)) x x = 0 := by
          intro i _
          rw [firstHit_succ_source, zero_mul]
        rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, zero_add, firstHit_zero,
          if_pos rfl, one_mul, Nat.sub_zero]
      · by_cases hxC : x ∈ C
        · rw [killedHeat_succ, if_pos hxC]
          have hinner : ∀ z ∈ G.neighborFinset x, killedHeat G C k z o
              = ∑ j ∈ Finset.range (k + 1), firstHit G C o j z * killedHeat G C (k - j) o o :=
            fun z _ => ih z
          rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
          have hstep : ∀ j ∈ Finset.range (k + 1),
              (∑ z ∈ G.neighborFinset x, firstHit G C o j z * killedHeat G C (k - j) o o)
                = (∑ z ∈ G.neighborFinset x, firstHit G C o j z) * killedHeat G C (k - j) o o :=
            fun j _ => (Finset.sum_mul _ _ _).symm
          rw [Finset.sum_congr rfl hstep, Finset.sum_div]
          rw [Finset.sum_range_succ'
            (fun j => firstHit G C o j x * killedHeat G C (k + 1 - j) o o) (k + 1)]
          have h0 : firstHit G C o 0 x * killedHeat G C (k + 1 - 0) o o = 0 := by
            rw [firstHit_zero, if_neg hxo, zero_mul]
          rw [h0, add_zero]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hj' : j < k + 1 := Finset.mem_range.mp hj
          rw [firstHit_succ, if_neg hxo, if_pos hxC, show k + 1 - (j + 1) = k - j by omega]
          ring
        · rw [killedHeat_succ, if_neg hxC]
          refine (Finset.sum_eq_zero fun j _ => ?_).symm
          rw [firstHit_of_not_mem hxC hxo, zero_mul]

/-! ### The first-return probabilities -/

/-- The probability of returning to `o` for the first time at step `k + 1`,
before leaving `C`. -/
noncomputable def firstReturn (G : SimpleGraph V) [G.LocallyFinite] (C : Set V) (o : V)
    (k : ℕ) : ℝ :=
  (∑ z ∈ G.neighborFinset o, firstHit G C o k z) / G.degree o

theorem firstReturn_nonneg (C : Set V) (o : V) (k : ℕ) : 0 ≤ firstReturn G C o k :=
  div_nonneg (Finset.sum_nonneg fun z _ => firstHit_nonneg C o k z) (by positivity)

/-- **The renewal identity.**  A visit to `o` at a positive time is a first
return at some time followed by a visit in the rest. -/
theorem killedHeat_renewal {C : Set V} {o : V} (ho : o ∈ C) (k : ℕ) :
    killedHeat G C (k + 1) o o
      = ∑ j ∈ Finset.range (k + 1), firstReturn G C o j * killedHeat G C (k - j) o o := by
  rw [killedHeat_succ, if_pos ho]
  have hinner : ∀ z ∈ G.neighborFinset o, killedHeat G C k z o
      = ∑ j ∈ Finset.range (k + 1), firstHit G C o j z * killedHeat G C (k - j) o o :=
    fun z _ => killedHeat_eq_sum_firstHit ho k z
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  have hstep : ∀ j ∈ Finset.range (k + 1),
      (∑ z ∈ G.neighborFinset o, firstHit G C o j z * killedHeat G C (k - j) o o)
        = (∑ z ∈ G.neighborFinset o, firstHit G C o j z) * killedHeat G C (k - j) o o :=
    fun j _ => (Finset.sum_mul _ _ _).symm
  rw [Finset.sum_congr rfl hstep, Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by rw [firstReturn]; ring

/-- Each first-return probability is at most the corresponding return
probability, which is what makes the return series converge. -/
theorem firstReturn_le_killedHeat {C : Set V} {o : V} (ho : o ∈ C) (k : ℕ) :
    firstReturn G C o k ≤ killedHeat G C (k + 1) o o := by
  rw [killedHeat_renewal ho k]
  have hself : firstReturn G C o k * killedHeat G C (k - k) o o = firstReturn G C o k := by
    rw [Nat.sub_self, killedHeat_zero, if_pos ho, if_pos rfl, mul_one]
  have hmem : k ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have hle := Finset.single_le_sum
    (f := fun j => firstReturn G C o j * killedHeat G C (k - j) o o)
    (fun j _ => mul_nonneg (firstReturn_nonneg C o j) (killedHeat_nonneg _ _ _ _)) hmem
  rwa [hself] at hle

/-! ### The escape probability -/

/-- The expected number of visits to `o` before leaving `C`. -/
noncomputable def visitCount (G : SimpleGraph V) [G.LocallyFinite] (C : Finset V) (o : V) : ℝ :=
  ∑' k : ℕ, killedHeat G (C : Set V) k o o

/-- The expected number of visits is the degree times the effective resistance:
that is what normalizing the Green function by the degree does. -/
theorem visitCount_eq_degree_mul_effRes (hG : G.Connected) (C : Finset V) {o q : V}
    (ho : o ∈ C) (hq : q ∉ C) :
    visitCount G C o = (G.degree o : ℝ) * effRes G C o := by
  have hne : o ≠ q := fun h => hq (h ▸ ho)
  have hdeg : 0 < G.degree o := degree_pos_of_ne hG hne o
  have hdegR : (0 : ℝ) < (G.degree o : ℝ) := by exact_mod_cast hdeg
  rw [effRes, killedGreenReal_eq_tsum hG C hq, visitCount]
  field_simp

/-- The probability of ever returning to `o` before leaving `C`. -/
noncomputable def returnProb (G : SimpleGraph V) [G.LocallyFinite] (C : Finset V) (o : V) : ℝ :=
  ∑' k : ℕ, firstReturn G (C : Set V) o k

theorem summable_firstReturn (hG : G.Connected) (C : Finset V) {o q : V} (ho : o ∈ C)
    (hq : q ∉ C) : Summable fun k : ℕ => firstReturn G (C : Set V) o k := by
  have hks := summable_killedHeat hG C hq o o
  have hshift : Summable fun k : ℕ => killedHeat G (C : Set V) (k + 1) o o :=
    (summable_nat_add_iff 1).mpr hks
  exact Summable.of_nonneg_of_le (fun k => firstReturn_nonneg _ o k)
    (fun k => firstReturn_le_killedHeat (by exact_mod_cast ho) k) hshift

/-- **The renewal identity, summed.**  Every visit to `o` after time zero is a
first return followed by a visit. -/
theorem visitCount_renewal (hG : G.Connected) (C : Finset V) {o q : V} (ho : o ∈ C)
    (hq : q ∉ C) :
    visitCount G C o - 1 = returnProb G C o * visitCount G C o := by
  have hks := summable_killedHeat hG C hq o o
  have hrs := summable_firstReturn hG C ho hq
  have hnormK : Summable fun k : ℕ => ‖killedHeat G (C : Set V) k o o‖ := by
    refine hks.congr fun k => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (killedHeat_nonneg _ k o o)]
  have hnormR : Summable fun k : ℕ => ‖firstReturn G (C : Set V) o k‖ := by
    refine hrs.congr fun k => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (firstReturn_nonneg _ o k)]
  have hcauchy := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hnormR hnormK
  have hren : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1),
      firstReturn G (C : Set V) o k * killedHeat G (C : Set V) (n - k) o o
        = killedHeat G (C : Set V) (n + 1) o o :=
    fun n => (killedHeat_renewal (by exact_mod_cast ho) n).symm
  rw [tsum_congr hren] at hcauchy
  have htail := hks.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one, killedHeat_zero, if_pos (by exact_mod_cast ho), if_pos rfl] at htail
  rw [returnProb, visitCount, hcauchy]
  linarith [htail]

/-- **The escape probability is the reciprocal of the degree times the effective
resistance.**  Now with the return probability built from the kernel, through the
first-passage decomposition, rather than read off a potential. -/
theorem one_sub_returnProb (hG : G.Connected) (C : Finset V) {o q : V} (ho : o ∈ C)
    (hq : q ∉ C) :
    1 - returnProb G C o = 1 / ((G.degree o : ℝ) * effRes G C o) := by
  have hne : o ≠ q := fun h => hq (h ▸ ho)
  have hdeg : 0 < G.degree o := degree_pos_of_ne hG hne o
  have hdegR : (0 : ℝ) < (G.degree o : ℝ) := by exact_mod_cast hdeg
  have hR : 0 < effRes G C o := effRes_pos hG C ho hq
  have hV : visitCount G C o = (G.degree o : ℝ) * effRes G C o :=
    visitCount_eq_degree_mul_effRes hG C ho hq
  have hVpos : 0 < visitCount G C o := by
    rw [hV]
    positivity
  have hrenew := visitCount_renewal hG C ho hq
  rw [← hV]
  field_simp
  linarith [hrenew]

/-- The return probability is the mean of the equilibrium potential over the
neighbours of the source: the potential form of the escape identity and the
kernel form agree, so the potential does read the hitting probability. -/
theorem returnProb_eq_mean_equilibrium (hG : G.Connected) (C : Finset V) {o q : V}
    (ho : o ∈ C) (hq : q ∉ C) :
    returnProb G C o
      = (∑ y ∈ G.neighborFinset o, equilibrium G C o y) / (G.degree o : ℝ) := by
  have h1 := one_sub_returnProb hG C ho hq
  have h2 := escape_eq_inv hG C ho hq
  linarith

end LatticeProb.Network
