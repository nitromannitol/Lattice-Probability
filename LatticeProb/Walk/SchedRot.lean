/-
The rotated coordinate-schedule decomposition of the simple random walk.

`LatticeProb.srwHeat_eq_sched` averages the product of one-dimensional kernels
`∏_l s_{N_l(c)}(x_l)` over the `d^r` coordinate schedules `c`.  That
decomposition is too fine for the same-parity gradient in a mixed direction
`e_i + e_j`: conditionally on the schedule the two coordinates are independent
one-dimensional walks of FIXED lengths `N_i` and `N_j`, the shift changes the
parity of each of them, and the two kernels have disjoint supports, so the
conditional total-variation distance is `2` and nothing is gained.  The gain
comes from averaging over which of the two coordinates each of the `N_i + N_j`
steps in the pair uses.

Summing that average out first is the content of this file.  For a fixed pair
`i ≠ j`, group the schedules by the coarser datum that records only WHICH times
select the pair `{i,j}`, not which member of the pair.  Over the `2^k` fine
schedules above a coarse one with `k` steps in the pair, the sum of
`s_{N_i}(x_i) s_{N_j}(x_j)` is `2^k` times the two-dimensional kernel of the
pair at time `k`, and that kernel factorizes in the rotated coordinates
(`LatticeProb.srwHeat_two_factor`) as `s_k(x_i + x_j) s_k(x_i - x_j)`.  Since
the number of fine schedules over a coarse one with `k` pair steps is exactly
`2^k`, the result is again an average over the SAME index set:

    p_r(x) = d^{-r} ∑_c s_{K(c)}(x_i + x_j) s_{K(c)}(x_i - x_j) ∏_{l ≠ i,j} s_{N_l(c)}(x_l),

with `K(c) = N_i(c) + N_j(c)`.  That is `LatticeProb.srwHeat_eq_schedRot`.  It is
proved here directly, by the induction of `LatticeProb.srwHeat_eq_sched`: the
only new point is that the one-step identity no longer holds coordinate by
coordinate.  A step in `i` alone would advance one rotated coordinate by `+1`
and the other by `+1`, never by `+1` and `-1`; it is the SUM of the step in `i`
and the step in `j` that reconstitutes the four corners `(±1, ±1)` and advances
both rotated kernels by one, which is `LatticeProb.KR_bump_pair`.

In the shift by `e_i + e_j` the rotated coordinates move by `(2, 0)`, so only
one factor is touched, and the one-dimensional two-step gradient applies with
the RANDOM length `K(c)`.
-/
import Mathlib
import LatticeProb.Walk.SRWDecomp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

variable {d : ℕ}

/-! ### The rotated product kernel -/

/-- The product of one-dimensional kernels in which the pair `i, j` has been
replaced by its two rotated coordinates, both run for `n i + n j` steps. -/
noncomputable def KR (i j : Fin d) (n : Fin d → ℕ) (x : Site d) : ℝ :=
  S1 (n i + n j) (x i + x j) * S1 (n i + n j) (x i - x j) *
    ∏ l ∈ (Finset.univ.erase i).erase j, S1 (n l) (x l)

/-- The rotated kernel is nonnegative. -/
theorem KR_nonneg (i j : Fin d) (n : Fin d → ℕ) (x : Site d) : 0 ≤ KR i j n x :=
  mul_nonneg (mul_nonneg (S1_nonneg _ _) (S1_nonneg _ _))
    (Finset.prod_nonneg fun _ _ => S1_nonneg _ _)

/-- The rotated kernel depends on the site only through the two rotated
coordinates and the coordinates outside the pair. -/
theorem KR_site_congr {i j : Fin d} (n : Fin d → ℕ) (x y : Site d)
    (hi : y i = x i) (hj : y j = x j) :
    KR i j n y = S1 (n i + n j) (x i + x j) * S1 (n i + n j) (x i - x j) *
      ∏ l ∈ (Finset.univ.erase i).erase j, S1 (n l) (y l) := by
  unfold KR
  rw [hi, hj]

/-- One simple step in a coordinate outside the pair advances that coordinate's
factor by one, exactly as in `LatticeProb.KS_bump`. -/
theorem KR_bump_rest {i j : Fin d} (n : Fin d → ℕ) (x : Site d)
    (m : Fin d) (hmi : m ≠ i) (hmj : m ≠ j) :
    KR i j (Function.update n m (n m + 1)) x
      = (KR i j n (x + dirVec ((m, true) : Dir d))
          + KR i j n (x + dirVec ((m, false) : Dir d))) / 2 := by
  classical
  have hi : i ≠ m := Ne.symm hmi
  have hj : j ≠ m := Ne.symm hmj
  set E : Finset (Fin d) := (Finset.univ.erase i).erase j with hE
  have hm : m ∈ E := by
    rw [hE]
    exact Finset.mem_erase.mpr ⟨hmj, Finset.mem_erase.mpr ⟨hmi, Finset.mem_univ m⟩⟩
  have hyi : ∀ b : Bool, (x + dirVec ((m, b) : Dir d)) i = x i := by
    intro b
    cases b
    · rw [add_dirVec_false_apply, if_neg hi]
    · rw [add_dirVec_true_apply, if_neg hi]
  have hyj : ∀ b : Bool, (x + dirVec ((m, b) : Dir d)) j = x j := by
    intro b
    cases b
    · rw [add_dirVec_false_apply, if_neg hj]
    · rw [add_dirVec_true_apply, if_neg hj]
  rw [KR_site_congr n x _ (hyi true) (hyj true), KR_site_congr n x _ (hyi false) (hyj false)]
  unfold KR
  rw [Function.update_of_ne hi, Function.update_of_ne hj]
  have hprod : ∏ l ∈ E, S1 (Function.update n m (n m + 1) l) (x l)
      = (∏ l ∈ E, S1 (n l) ((x + dirVec ((m, true) : Dir d)) l)
          + ∏ l ∈ E, S1 (n l) ((x + dirVec ((m, false) : Dir d)) l)) / 2 := by
    rw [← Finset.mul_prod_erase E (fun l => S1 (Function.update n m (n m + 1) l) (x l)) hm,
        ← Finset.mul_prod_erase E (fun l => S1 (n l) ((x + dirVec ((m, true) : Dir d)) l)) hm,
        ← Finset.mul_prod_erase E (fun l => S1 (n l) ((x + dirVec ((m, false) : Dir d)) l)) hm]
    have h1 : ∀ l ∈ E.erase m, S1 (Function.update n m (n m + 1) l) (x l) = S1 (n l) (x l) := by
      intro l hl
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
    have h2 : ∀ (b : Bool), ∀ l ∈ E.erase m,
        S1 (n l) ((x + dirVec ((m, b) : Dir d)) l) = S1 (n l) (x l) := by
      intro b l hl
      cases b
      · rw [add_dirVec_false_apply, if_neg (Finset.ne_of_mem_erase hl)]
      · rw [add_dirVec_true_apply, if_neg (Finset.ne_of_mem_erase hl)]
    rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl (h2 true),
      Finset.prod_congr rfl (h2 false)]
    rw [Function.update_self, add_dirVec_true_apply, add_dirVec_false_apply, if_pos rfl,
      if_pos rfl, S1_succ]
    ring
  rw [hprod]
  ring

/-- **The paired one-step identity.**  A step in `i` moves both rotated
coordinates the same way and a step in `j` moves them oppositely, so neither
alone advances the two rotated kernels; their SUM does.  This is the identity
that the fine schedule decomposition does not have. -/
theorem KR_bump_pair {i j : Fin d} (hij : i ≠ j) (n : Fin d → ℕ) (x : Site d) :
    KR i j (Function.update n i (n i + 1)) x + KR i j (Function.update n j (n j + 1)) x
      = (KR i j n (x + dirVec ((i, true) : Dir d))
          + KR i j n (x + dirVec ((i, false) : Dir d))
          + KR i j n (x + dirVec ((j, true) : Dir d))
          + KR i j n (x + dirVec ((j, false) : Dir d))) / 2 := by
  classical
  set E : Finset (Fin d) := (Finset.univ.erase i).erase j with hE
  have hne : ∀ l ∈ E, l ≠ i ∧ l ≠ j := by
    intro l hl
    rw [hE] at hl
    exact ⟨Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl),
      Finset.ne_of_mem_erase hl⟩
  have hPi : ∀ b : Bool, ∏ l ∈ E, S1 (n l) ((x + dirVec ((i, b) : Dir d)) l)
      = ∏ l ∈ E, S1 (n l) (x l) := by
    intro b
    refine Finset.prod_congr rfl fun l hl => ?_
    cases b
    · rw [add_dirVec_false_apply, if_neg (hne l hl).1]
    · rw [add_dirVec_true_apply, if_neg (hne l hl).1]
  have hPj : ∀ b : Bool, ∏ l ∈ E, S1 (n l) ((x + dirVec ((j, b) : Dir d)) l)
      = ∏ l ∈ E, S1 (n l) (x l) := by
    intro b
    refine Finset.prod_congr rfl fun l hl => ?_
    cases b
    · rw [add_dirVec_false_apply, if_neg (hne l hl).2]
    · rw [add_dirVec_true_apply, if_neg (hne l hl).2]
  have hUi : ∏ l ∈ E, S1 (Function.update n i (n i + 1) l) (x l)
      = ∏ l ∈ E, S1 (n l) (x l) :=
    Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (hne l hl).1]
  have hUj : ∏ l ∈ E, S1 (Function.update n j (n j + 1) l) (x l)
      = ∏ l ∈ E, S1 (n l) (x l) :=
    Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (hne l hl).2]
  unfold KR
  rw [hPi true, hPi false, hPj true, hPj false, hUi, hUj]
  rw [Function.update_self, Function.update_of_ne (Ne.symm hij), Function.update_self,
    Function.update_of_ne hij]
  rw [add_dirVec_true_apply, add_dirVec_true_apply, add_dirVec_false_apply,
    add_dirVec_false_apply, add_dirVec_true_apply, add_dirVec_true_apply,
    add_dirVec_false_apply, add_dirVec_false_apply]
  rw [if_pos rfl, if_neg (Ne.symm hij), if_pos rfl, if_neg (Ne.symm hij),
    if_pos rfl, if_neg hij, if_pos rfl, if_neg hij]
  have hK1 : n i + 1 + n j = (n i + n j) + 1 := by omega
  have hK2 : n i + (n j + 1) = (n i + n j) + 1 := by omega
  rw [hK1, hK2]
  have e1 : x i + 1 + x j = (x i + x j) + 1 := by ring
  have e2 : x i + 1 - x j = (x i - x j) + 1 := by ring
  have e3 : x i - 1 + x j = (x i + x j) - 1 := by ring
  have e4 : x i - 1 - x j = (x i - x j) - 1 := by ring
  have e5 : x i + (x j + 1) = (x i + x j) + 1 := by ring
  have e6 : x i - (x j + 1) = (x i - x j) - 1 := by ring
  have e7 : x i + (x j - 1) = (x i + x j) - 1 := by ring
  have e8 : x i - (x j - 1) = (x i - x j) + 1 := by ring
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  rw [S1_succ (n i + n j) (x i + x j), S1_succ (n i + n j) (x i - x j)]
  ring

/-! ### The decomposition -/

/-- Running no coordinate at all leaves the indicator of the origin: both
rotated coordinates and every coordinate outside the pair must vanish, and over
the integers `x i + x j = 0` and `x i - x j = 0` force `x i = x j = 0`. -/
theorem KR_zero_fun (i j : Fin d) (x : Site d) :
    KR i j (fun _ => 0) x = if x = 0 then 1 else 0 := by
  classical
  unfold KR
  dsimp only
  by_cases hb : x i = 0 ∧ x j = 0
  · obtain ⟨hxi, hxj⟩ := hb
    have h1 : x i + x j = 0 := by omega
    have h2 : x i - x j = 0 := by omega
    rw [h1, h2]
    simp only [S1_zero]
    by_cases hx : x = 0
    · subst hx
      simp [S1_zero]
    · rw [if_neg hx]
      obtain ⟨l, hl⟩ : ∃ l : Fin d, x l ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hx (funext hc)
      have hli : l ≠ i := fun h => hl (h ▸ hxi)
      have hlj : l ≠ j := fun h => hl (h ▸ hxj)
      have hmem : l ∈ (Finset.univ.erase i).erase j :=
        Finset.mem_erase.mpr ⟨hlj, Finset.mem_erase.mpr ⟨hli, Finset.mem_univ l⟩⟩
      rw [Finset.prod_eq_zero hmem (by simp [hl])]
      simp [S1_zero]
  · have hx : x ≠ 0 := by
      intro hc
      exact hb ⟨by rw [hc]; rfl, by rw [hc]; rfl⟩
    rw [if_neg hx]
    by_cases hs : x i + x j = 0
    · have ht : x i - x j ≠ 0 := by
        intro hc
        exact hb ⟨by omega, by omega⟩
      simp only [add_zero, S1_zero]
      rw [if_neg ht]
      ring
    · simp only [add_zero, S1_zero]
      rw [if_neg hs]
      ring


/-- Splitting a sum over the coordinates into the pair and the rest. -/
theorem sum_split_pair {i j : Fin d} (hij : i ≠ j) (G : Fin d → ℝ) :
    ∑ m : Fin d, G m = G i + G j + ∑ m ∈ (Finset.univ.erase i).erase j, G m := by
  classical
  rw [← Finset.add_sum_erase Finset.univ G (Finset.mem_univ i),
    ← Finset.add_sum_erase (Finset.univ.erase i) G
      (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
  ring

/-- **The rotated coordinate-schedule decomposition.**  For a pair `i ≠ j` of
coordinates the `r`-step kernel is the average over the `d^r` schedules of the
product in which the pair has been replaced by its two rotated coordinates, both
run for the number of steps the schedule gives to the pair. -/
theorem srwHeat_eq_schedRot (hd : 0 < d) {i j : Fin d} (hij : i ≠ j) (r : ℕ) (x : Site d) :
    srwHeat d r x = (∑ c : Fin r → Fin d, KR i j (cnt c) x) / (d : ℝ) ^ r := by
  classical
  induction r generalizing x with
  | zero =>
    have hu : (Finset.univ : Finset (Fin 0 → Fin d)) = {fun i => i.elim0} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨Finset.mem_univ _, fun c _ => ?_⟩
      funext t; exact t.elim0
    rw [hu, Finset.sum_singleton, pow_zero, div_one, cnt_zero, srwHeat_zero, KR_zero_fun]
  | succ r ih =>
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    rw [srwHeat_succ_eq_sum_dir]
    have hsum : ∀ a : Dir d, srwHeat d r (x + dirVec a)
        = (∑ c : Fin r → Fin d, KR i j (cnt c) (x + dirVec a)) / (d : ℝ) ^ r :=
      fun a => ih _
    rw [Finset.sum_congr rfl fun a _ => hsum a]
    have hdir : ∀ f : Dir d → ℝ, (∑ a : Dir d, f a)
        = ∑ m : Fin d, (f (m, true) + f (m, false)) := by
      intro f
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun m _ => by rw [Fintype.sum_bool]
    rw [hdir]
    have hL : ∑ m : Fin d,
          ((∑ c : Fin r → Fin d, KR i j (cnt c) (x + dirVec ((m, true) : Dir d))) / (d : ℝ) ^ r
          + (∑ c : Fin r → Fin d, KR i j (cnt c) (x + dirVec ((m, false) : Dir d)))
              / (d : ℝ) ^ r)
        = (∑ m : Fin d, ∑ c : Fin r → Fin d,
            (KR i j (cnt c) (x + dirVec ((m, true) : Dir d))
              + KR i j (cnt c) (x + dirVec ((m, false) : Dir d)))) / (d : ℝ) ^ r := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.sum_add_distrib, ← add_div]
    rw [hL]
    have hre : ∑ c' : Fin (r + 1) → Fin d, KR i j (cnt c') x
        = ∑ m : Fin d, ∑ c : Fin r → Fin d,
            KR i j (Function.update (cnt c) m (cnt c m + 1)) x := by
      rw [← (snocEquiv r d).sum_comp (fun c' => KR i j (cnt c') x), Fintype.sum_prod_type,
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun c _ => ?_
      show KR i j (cnt (Fin.snoc c m : Fin (r + 1) → Fin d)) x = _
      rw [cnt_snoc]
    have hR : ∑ m : Fin d, ∑ c : Fin r → Fin d,
          KR i j (Function.update (cnt c) m (cnt c m + 1)) x
        = (∑ m : Fin d, ∑ c : Fin r → Fin d,
            (KR i j (cnt c) (x + dirVec ((m, true) : Dir d))
              + KR i j (cnt c) (x + dirVec ((m, false) : Dir d)))) / 2 := by
      rw [sum_split_pair hij (fun m => ∑ c : Fin r → Fin d,
            KR i j (Function.update (cnt c) m (cnt c m + 1)) x),
        sum_split_pair hij (fun m => ∑ c : Fin r → Fin d,
            (KR i j (cnt c) (x + dirVec ((m, true) : Dir d))
              + KR i j (cnt c) (x + dirVec ((m, false) : Dir d))))]
      have hpair : (∑ c : Fin r → Fin d, KR i j (Function.update (cnt c) i (cnt c i + 1)) x)
            + ∑ c : Fin r → Fin d, KR i j (Function.update (cnt c) j (cnt c j + 1)) x
          = ((∑ c : Fin r → Fin d,
                (KR i j (cnt c) (x + dirVec ((i, true) : Dir d))
                  + KR i j (cnt c) (x + dirVec ((i, false) : Dir d))))
              + ∑ c : Fin r → Fin d,
                (KR i j (cnt c) (x + dirVec ((j, true) : Dir d))
                  + KR i j (cnt c) (x + dirVec ((j, false) : Dir d)))) / 2 := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [KR_bump_pair hij (cnt c) x]
        ring
      have hrest : ∀ m ∈ (Finset.univ.erase i).erase j,
          (∑ c : Fin r → Fin d, KR i j (Function.update (cnt c) m (cnt c m + 1)) x)
            = (∑ c : Fin r → Fin d,
                (KR i j (cnt c) (x + dirVec ((m, true) : Dir d))
                  + KR i j (cnt c) (x + dirVec ((m, false) : Dir d)))) / 2 := by
        intro m hm
        have hmi : m ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hm)
        have hmj : m ≠ j := Finset.ne_of_mem_erase hm
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun c _ => KR_bump_rest (cnt c) x m hmi hmj
      rw [Finset.sum_congr rfl hrest, ← Finset.sum_div]
      rw [hpair]
      ring
    rw [hre, hR]
    have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdR
    have hpne : ((d : ℝ)) ^ r ≠ 0 := pow_ne_zero _ hdne
    field_simp
    ring

end LatticeProb
