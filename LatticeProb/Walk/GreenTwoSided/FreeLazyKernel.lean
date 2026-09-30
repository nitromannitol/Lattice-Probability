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
import LatticeProb.Walk.GreenTwoSided.PointwiseBounds

/-!
# The free lazy kernel

The free lazy kernel's near-diagonal lower bound `Q^[n] delta0 w ≥ c₀ / s ^ d` for `s^2 ≤ n ≤
2s^2` and `graphNorm w ≤ s`, obtained from the coordinate-schedule binomial-mixture formula for
`Q^[n] delta0`, the one-dimensional local central limit theorem, and a Chebyshev estimate on how
many coordinates of a schedule are balanced.
-/

open Finset
open scoped Classical

namespace LatticeProb

namespace GreenTwoSided

variable {d : ℕ}

-- iterate_delta0_eq_binom j w; every srwHeat d k w ≤ C / r^d (srwHeat_le_div_pow_of_le_graphNorm);
-- the weights sum to 1
-- (Nat.sum_range_choose: ∑ choose = 2^j, (2⁻¹)^j * 2^j = 1); Finset.sum_le_sum, ← Finset.mul_sum.
/-- The free lazy kernel inherits the off-diagonal Gaussian bound: `Q^[j] delta0 w ≤ C / r ^ d`
whenever `1 ≤ r ≤ graphNorm w`, as a binomial mixture of the corresponding `srwHeat` bound. -/
theorem iterate_Q_delta0_le_div_pow_of_le_graphNorm (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (w : Site d) (r : ℕ), 1 ≤ r → r ≤ graphNorm w →
      Q^[j] (delta0 : Site d → ℝ) w ≤ C / (r : ℝ) ^ d := by
  obtain ⟨C, hCpos, hC⟩ := srwHeat_le_div_pow_of_le_graphNorm hd
  refine ⟨C, hCpos, ?_⟩
  intro j w r hr hrw
  rw [iterate_delta0_eq_binom]
  have hchoose : (∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ)) = (2 : ℝ) ^ j :=
    (by rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring)
  have hstep : ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * srwHeat d k w
      ≤ (2 : ℝ) ^ j * (C / (r : ℝ) ^ d) := (by
    rw [← hchoose, Finset.sum_mul]
    exact Finset.sum_le_sum
        (fun k _ => mul_le_mul_of_nonneg_left (hC k w r hr hrw) (Nat.cast_nonneg _)))
  have hmul : (2 : ℝ)⁻¹ ^ j * ((2 : ℝ) ^ j * (C / (r : ℝ) ^ d)) = C / (r : ℝ) ^ d :=
    (by rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow, one_mul])
  exact le_trans (mul_le_mul_of_nonneg_left hstep (pow_nonneg (by norm_num) _)) (le_of_eq hmul)


-- 1D lazy local CLT lower bound.  P1 m k = srwHeat 1 (2m) ![2k] (srwHeat_one_two_mul, reversed);
-- exists_srwHeat_one_sub_gauss_le_int with ε := exp(-A²)/2: √(πm) P1 m k ≥ exp(-k²/m) - ε
-- ≥ exp(-A²)/2 (k² ≤ A² m, Real.exp_le_exp); c := exp(-A²)/(2√π); Real.sqrt_mul.
/-- The 1D lazy local CLT lower bound: for every `A > 0` there are `c > 0` and `m₀` such that `c
/ √m ≤ P1 m k` whenever `m ≥ m₀` and `|k| ≤ A√m`. -/
private theorem exists_const_le_P1_of_le_sqrt_mul (A : ℝ) (hA : 0 < A) :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∀ k : ℤ,
      |(k : ℝ)| ≤ A * Real.sqrt (m : ℝ) → c / Real.sqrt (m : ℝ) ≤ P1 m k := by
  have hε : 0 < Real.exp (-(A ^ 2)) / 2 := div_pos (Real.exp_pos _) two_pos
  obtain ⟨m₀, hm₀, H⟩ := exists_srwHeat_one_sub_gauss_le_int hA hε
  refine ⟨Real.exp (-(A ^ 2)) / (2 * Real.sqrt Real.pi),
    div_pos (Real.exp_pos _) (mul_pos two_pos (Real.sqrt_pos.mpr Real.pi_pos)), m₀, hm₀, ?_⟩
  intro m hm k hk
  have hm1 : 1 ≤ m := le_trans hm₀ hm
  have hmpos : 0 < (m : ℝ) := (by exact_mod_cast hm1)
  have hk2 : (k : ℝ) ^ 2 ≤ (A * Real.sqrt (m : ℝ)) ^ 2 :=
    sq_le_sq.mpr (by rw [abs_of_nonneg (mul_nonneg hA.le (Real.sqrt_nonneg _))]; exact hk)
  have hsq : (k : ℝ) ^ 2 ≤ A ^ 2 * (m : ℝ) := (by
    rwa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)] at hk2)
  have hdiv : (k : ℝ) ^ 2 / (m : ℝ) ≤ A ^ 2 := (by
    rw [div_le_iff₀ hmpos]
    linarith)
  have hexp : Real.exp (-(A ^ 2)) ≤ Real.exp (-((k : ℝ) ^ 2 / (m : ℝ))) := (by
    rw [Real.exp_le_exp]
    exact neg_le_neg hdiv)
  have hkey : |Real.sqrt (Real.pi * (m : ℝ)) * P1 m k - Real.exp (-((k : ℝ) ^ 2 / (m : ℝ)))|
      ≤ Real.exp (-(A ^ 2)) / 2 := (by
    have h := H m hm k hk
    rwa [srwHeat_one_two_mul] at h)
  have h2 : Real.exp (-(A ^ 2)) / 2 ≤ Real.sqrt (Real.pi * (m : ℝ)) * P1 m k := (by
    have h4 := (abs_le.mp hkey).1
    linarith only [h4, hexp])
  have hsqrt : 0 < Real.sqrt (Real.pi * (m : ℝ)) :=
    Real.sqrt_pos.mpr (mul_pos Real.pi_pos hmpos)
  have h3 : Real.exp (-(A ^ 2)) / 2 / Real.sqrt (Real.pi * (m : ℝ)) ≤ P1 m k := (by
    rw [div_le_iff₀ hsqrt]
    calc Real.exp (-(A ^ 2)) / 2 ≤ Real.sqrt (Real.pi * (m : ℝ)) * P1 m k := h2
      _ = P1 m k * Real.sqrt (Real.pi * (m : ℝ)) := mul_comm _ _)
  have heq : Real.exp (-(A ^ 2)) / (2 * Real.sqrt Real.pi) / Real.sqrt (m : ℝ)
      = Real.exp (-(A ^ 2)) / 2 / Real.sqrt (Real.pi * (m : ℝ)) := (by
    rw [Real.sqrt_mul Real.pi_nonneg, div_div, div_div]
    ring)
  rw [heq]
  exact h3


-- Counting: {c : Fin r → Fin d | c t = i} has d^r / d elements.  Sum over c of the indicator
-- via Fintype.sum_pow / Finset.prod_univ_sum style factorisation, or by the equivalence
-- Equiv.piSplitAt t; Fintype.card_pi, Fintype.card_fin.
/-- The fibre `{c : Fin r → Fin d // c t = i}` of a fixed coordinate has exactly `d^{r-1}`
elements. -/
private theorem card_fiber_eq_pow_sub_one {d r : ℕ} (t : Fin r) (i : Fin d) :
    Fintype.card {c : Fin r → Fin d // c t = i} = d ^ (r - 1) := by
  have hr : 1 ≤ r := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le (t : ℕ)) t.isLt)
  have e : {c : Fin r → Fin d // c t = i} ≃ ({j : Fin r // j ≠ t} → Fin d) :=
    { toFun := fun c j => c.1 j.1
      invFun := fun g => ⟨fun j => if h : j = t then i else g ⟨j, h⟩, by simp⟩
      left_inv := by
        intro c
        apply Subtype.ext
        funext j
        by_cases h : j = t
        · simp [h, c.2]
        · simp [h]
      right_inv := by
        intro g
        funext j
        simp [j.2] }
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin]
  have h1 : Fintype.card {j : Fin r // j ≠ t} = r - 1 := by
    rw [Fintype.card_subtype_compl (fun j : Fin r => j = t),
      Fintype.card_subtype_eq t, Fintype.card_fin]
  rw [h1]

/-- The indicator sum `∑_c (if c t = i then 1 else 0)` equals the cardinality of the fibre `{c //
c t = i}`. -/
private theorem sum_ite_eq_fiber_eq_card {d r : ℕ} (t : Fin r) (i : Fin d) :
    (∑ c : Fin r → Fin d, (if c t = i then (1 : ℝ) else 0))
      = ((Fintype.card {c : Fin r → Fin d // c t = i} : ℕ) : ℝ) := by
  rw [Fintype.card_subtype]
  exact Finset.sum_boole (fun c : Fin r → Fin d => c t = i) Finset.univ

/-- For `r ≥ 1` and `d > 0`, `(d^{r-1} : ℝ) = d^r / d`. -/
private theorem cast_pow_sub_one_eq_pow_div {d r : ℕ} (hr : 1 ≤ r) (hd0 : (0 : ℝ) < (d : ℝ)) :
    ((d ^ (r - 1) : ℕ) : ℝ) = (d : ℝ) ^ r / (d : ℝ) := by
  rw [Nat.cast_pow, eq_div_iff (ne_of_gt hd0), ← pow_succ, Nat.sub_add_cancel hr]

/-- The one-coordinate fibre count as a real number: `∑_c (if c t = i then 1 else 0) = d^r / d`. -/
private theorem sum_ite_eq_eq_pow_div (hd : 1 ≤ d) (r : ℕ) (t : Fin r) (i : Fin d) :
    ∑ c : Fin r → Fin d, (if c t = i then (1 : ℝ) else 0) = (d : ℝ) ^ r / d := by
  have hr : 1 ≤ r := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le (t : ℕ)) t.isLt)
  have hd0 : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  rw
      [sum_ite_eq_fiber_eq_card t i, card_fiber_eq_pow_sub_one t i, cast_pow_sub_one_eq_pow_div hr
          hd0]


-- Same with two distinct coordinates t ≠ t' fixed: d^r / d^2.
/-- Implementation lemma for `sum_ite_eq_eq_pow_div_sq`. -/
private theorem sum_ite_eq_eq_pow_div_sq' (hd : 1 ≤ d) (r : ℕ) {t t' : Fin r} (htt : t ≠ t')
    (i : Fin d) :
    (∑ c : Fin r → Fin d, (if c t = i ∧ c t' = i then (1 : ℝ) else 0)) = (d : ℝ) ^ r / d ^ 2 := by
  have hr2 : 2 ≤ r := by
    by_contra hcon
    push Not at hcon
    have h1 := t.isLt
    have h2 := t'.isLt
    exact htt (Fin.ext (by omega))
  have hne : (d : ℝ) ≠ 0 := by
    have hd0 : 0 < d := by omega
    exact_mod_cast (ne_of_gt hd0)
  have hidx : Fintype.card {x : Fin r // x ≠ t ∧ x ≠ t'} = r - 2 := by
    rw [Fintype.card_subtype]
    have h1 : (Finset.univ.filter (fun x : Fin r => x ≠ t ∧ x ≠ t'))
        = Finset.univ \ ({t, t'} : Finset (Fin r)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
        Finset.mem_insert, Finset.mem_singleton, not_or]
    have hpair : ({t, t'} : Finset (Fin r)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using htt), Finset.card_singleton]
    rw [h1, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hpair]
  have hcard : Fintype.card {c : Fin r → Fin d // c t = i ∧ c t' = i} = d ^ (r - 2) := by
    let e : {c : Fin r → Fin d // c t = i ∧ c t' = i} ≃
        ({x : Fin r // x ≠ t ∧ x ≠ t'} → Fin d) :=
      { toFun := fun c x => c.1 x.1
        invFun := fun f => ⟨fun x => if h : x ≠ t ∧ x ≠ t' then f ⟨x, h⟩ else i,
          ⟨by change (if h : t ≠ t ∧ t ≠ t' then f ⟨t, h⟩ else i) = i
              rw [dif_neg (fun h => h.1 rfl)],
           by change (if h : t' ≠ t ∧ t' ≠ t' then f ⟨t', h⟩ else i) = i
              rw [dif_neg (fun h => h.2 rfl)]⟩⟩
        left_inv := fun c => by
          apply Subtype.ext
          funext x
          change (if h : x ≠ t ∧ x ≠ t' then c.1 x else i) = c.1 x
          by_cases h : x ≠ t ∧ x ≠ t'
          · rw [dif_pos h]
          · rw [dif_neg h]
            rcases not_and_or.mp h with h1 | h1
            · rw [not_not.mp h1]
              exact c.2.1.symm
            · rw [not_not.mp h1]
              exact c.2.2.symm
        right_inv := fun f => by
          funext y
          change (if h : (y : Fin r) ≠ t ∧ (y : Fin r) ≠ t' then f ⟨(y : Fin r), h⟩ else i) = f y
          rw [dif_pos y.2] }
    rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin, hidx]
  rw [Finset.sum_boole]
  rw [← Fintype.card_subtype (fun c : Fin r → Fin d => c t = i ∧ c t' = i), hcard,
    Nat.cast_pow, pow_sub₀ (d : ℝ) hne hr2, div_eq_mul_inv]

/-- The two-coordinate fibre count: for distinct `t ≠ t'`, `∑_c (if c t = i ∧ c t' = i then 1
else 0) = d^r / d^2`. -/
private theorem sum_ite_eq_eq_pow_div_sq (hd : 1 ≤ d) (r : ℕ) {t t' : Fin r} (htt : t ≠ t')
    (i : Fin d) :
    ∑ c : Fin r → Fin d, (if c t = i ∧ c t' = i then (1 : ℝ) else 0) = (d : ℝ) ^ r / d ^ 2 := by
  exact sum_ite_eq_eq_pow_div_sq' hd r htt i


-- Chebyshev input: expand (cnt - r/d)^2 with cnt = ∑_t 1{c t = i} (unfold cnt, Nat.cast_sum),
-- Finset.sum_comm, sum_ite_eq_eq_pow_div, sum_ite_eq_eq_pow_div_sq (diagonal t = t' separately:
-- ite_and, Finset.sum_ite_eq);
-- result d^r (r/d)(1 - 1/d) ≤ d^r r/d.  SPLIT?
/-- A Chebyshev-type second-moment bound: `∑_c (cnt c i - r/d)^2 ≤ d^r * r / d`, from the one-
and two-coordinate fibre counts. -/
private theorem sum_sq_cnt_sub_div_le (hd : 1 ≤ d) (r : ℕ) (i : Fin d) :
    ∑ c : Fin r → Fin d, ((cnt c i : ℝ) - r / d) ^ 2 ≤ (d : ℝ) ^ r * r / d := by
  have hdR : (0 : ℝ) < (d : ℝ) := (by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd))
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdR
  have hcard : (Fintype.card (Fin r → Fin d) : ℝ) = (d : ℝ) ^ r := (by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring)
  set X : (Fin r → Fin d) → Fin r → ℝ := (fun c t => if c t = i then (1 : ℝ) else 0) with hX
  have hcnt : ∀ c : Fin r → Fin d, (cnt c i : ℝ) = ∑ t : Fin r, X c t := (by
    intro c
    unfold cnt
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases h : c t = i <;> simp [hX, h])
  have hterm : ∀ c : Fin r → Fin d, ((cnt c i : ℝ) - r / d) = ∑ t : Fin r, (X c t - 1 / d) := (by
    intro c
    rw [hcnt c, Finset.sum_sub_distrib]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring)
  have hS1 : ∀ t : Fin r, ∑ c : Fin r → Fin d, X c t = (d : ℝ) ^ r / d := (by
    intro t
    simp only [hX]
    exact sum_ite_eq_eq_pow_div hd r t i)
  have hXX : ∀ (t t' : Fin r) (c : Fin r → Fin d),
      X c t * X c t' = (if c t = i ∧ c t' = i then (1 : ℝ) else 0) := (by
    intro t t' c
    by_cases h1 : c t = i <;> by_cases h2 : c t' = i <;> simp [hX, h1, h2])
  have hZ2off : ∀ t t' : Fin r, t' ≠ t →
      ∑ c : Fin r → Fin d, (X c t - 1 / d) * (X c t' - 1 / d) = 0 := (by
    intro t t' hne
    have hexp : ∀ c : Fin r → Fin d,
        (X c t - 1 / d) * (X c t' - 1 / d)
          = X c t * X c t' - (1 / d) * X c t - (1 / d) * X c t' + (1 / d) ^ 2 := (by
      intro c
      ring)
    have hsum1 : ∑ c : Fin r → Fin d, (X c t - 1 / d) * (X c t' - 1 / d)
        = ∑ c : Fin r → Fin d,
            (X c t * X c t' - (1 / d) * X c t - (1 / d) * X c t' + (1 / d) ^ 2) :=
      Finset.sum_congr rfl (fun c _ => hexp c)
    rw [hsum1, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    have hsum2 : ∑ c : Fin r → Fin d, X c t * X c t'
        = ∑ c : Fin r → Fin d, (if c t = i ∧ c t' = i then (1 : ℝ) else 0) :=
      Finset.sum_congr rfl (fun c _ => hXX t t' c)
    rw
        [hsum2, sum_ite_eq_eq_pow_div_sq (t := t) (t' := t') hd r (fun h => hne h.symm) i, hS1 t,
            hS1 t']
    field_simp
    ring)
  have hZd : ∀ t : Fin r, ∑ c : Fin r → Fin d, (X c t - 1 / d) * (X c t - 1 / d)
      = (d : ℝ) ^ r * ((d : ℝ) - 1) / d ^ 2 := (by
    intro t
    have hpt : ∀ c : Fin r → Fin d,
        (X c t - 1 / d) * (X c t - 1 / d) = (1 - 2 / d) * X c t + (1 / d) ^ 2 := (by
      intro c
      by_cases h : c t = i <;> simp [hX, h] <;> ring)
    have hsum1 : ∑ c : Fin r → Fin d, (X c t - 1 / d) * (X c t - 1 / d)
        = ∑ c : Fin r → Fin d, ((1 - 2 / d) * X c t + (1 / d) ^ 2) :=
      Finset.sum_congr rfl (fun c _ => hpt c)
    rw [hsum1, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hS1 t, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    field_simp
    ring)
  have hfinal : (r : ℝ) * ((d : ℝ) ^ r * ((d : ℝ) - 1) / d ^ 2) ≤ (d : ℝ) ^ r * r / d := (by
    have h1 : ((d : ℝ) - 1) / d ^ 2 ≤ 1 / d := (by
      field_simp
      nlinarith [hdR, pow_pos hdR 2])
    calc (r : ℝ) * ((d : ℝ) ^ r * ((d : ℝ) - 1) / d ^ 2)
        = ((r : ℝ) * (d : ℝ) ^ r) * (((d : ℝ) - 1) / d ^ 2) := (by ring)
      _ ≤ ((r : ℝ) * (d : ℝ) ^ r) * (1 / d) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg (Nat.cast_nonneg r) (le_of_lt (pow_pos hdR r)))
      _ = (d : ℝ) ^ r * r / d := (by ring))
  have e1 : ∑ c : Fin r → Fin d, ((cnt c i : ℝ) - r / d) ^ 2
      = ∑ c : Fin r → Fin d, (∑ t : Fin r, (X c t - 1 / d)) ^ 2 := (by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hterm c])
  have e2 : ∑ c : Fin r → Fin d, (∑ t : Fin r, (X c t - 1 / d)) ^ 2
      = ∑ c : Fin r → Fin d, ∑ t : Fin r, ∑ t' : Fin r,
          (X c t - 1 / d) * (X c t' - 1 / d) := (by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [pow_two]
    exact Finset.sum_mul_sum Finset.univ Finset.univ
      (fun t => (X c t - 1 / d)) (fun t' => (X c t' - 1 / d)))
  have e3 : ∑ c : Fin r → Fin d, ∑ t : Fin r, ∑ t' : Fin r,
          (X c t - 1 / d) * (X c t' - 1 / d)
      = ∑ t : Fin r, ∑ t' : Fin r, ∑ c : Fin r → Fin d,
          (X c t - 1 / d) * (X c t' - 1 / d) := (by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun t _ => Finset.sum_comm))
  have e4 : ∑ t : Fin r, ∑ t' : Fin r, ∑ c : Fin r → Fin d,
          (X c t - 1 / d) * (X c t' - 1 / d)
      = ∑ t : Fin r, (d : ℝ) ^ r * ((d : ℝ) - 1) / d ^ 2 := (by
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have hkey : ∀ t' : Fin r, (∑ c : Fin r → Fin d,
          (X c t - 1 / d) * (X c t' - 1 / d))
        = if t' = t then (d : ℝ) ^ r * ((d : ℝ) - 1) / d ^ 2 else 0 := (by
      intro t'
      by_cases h : t' = t
      · rw [h, if_pos rfl]; exact hZd t
      · rw [if_neg h]; exact hZ2off t t' h)
    have hsum : ∑ t' : Fin r, ∑ c : Fin r → Fin d,
          (X c t - 1 / d) * (X c t' - 1 / d)
        = ∑ t' : Fin r, (if t' = t then (d : ℝ) ^ r * ((d : ℝ) - 1) / d ^ 2 else 0) :=
      Finset.sum_congr rfl (fun t' _ => hkey t')
    rw [hsum, Finset.sum_ite_eq']
    simp)
  have e5 : ∑ t : Fin r, (d : ℝ) ^ r * ((d : ℝ) - 1) / d ^ 2
      = (r : ℝ) * ((d : ℝ) ^ r * ((d : ℝ) - 1) / d ^ 2) := (by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])
  rw [e1, e2, e3, e4, e5]
  exact hfinal


-- Balanced schedules carry at least half the mass for r ≥ 8 d^2:
-- 1{∃ i, cnt c i < r/(2d)} ≤ ∑_i (cnt c i - r/d)^2 / (r/(2d))^2 (for such i, r/d - cnt ≥ r/(2d));
-- sum over c with sum_sq_cnt_sub_div_le: ≤ d · d^r (r/d) (2d/r)^2 = 4 d^2 d^r / r ≤ d^r/2.  SPLIT?
/-- For `r ≥ 8d^2`, at most half the schedules `c : Fin r → Fin d` have some coordinate count
`cnt c i` below `r/(2d)`, by Chebyshev's inequality applied to `sum_sq_cnt_sub_div_le`. -/
private theorem sum_ite_exists_cnt_lt_le_half_pow (hd : 1 ≤ d) (r : ℕ) (hr : 8 * d ^ 2 ≤ r) :
    ∑ c : Fin r → Fin d, (if ∃ i, (cnt c i : ℝ) < r / (2 * d) then (1 : ℝ) else 0)
      ≤ (d : ℝ) ^ r / 2 := by
  have hd0 : 0 < d := (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  have hdR : (0 : ℝ) < (d : ℝ) := (Nat.cast_pos.mpr hd0)
  have hr0 : 0 < r := (lt_of_lt_of_le (Nat.mul_pos (by norm_num) (pow_pos hd0 2)) hr)
  have hrR : (0 : ℝ) < (r : ℝ) := (Nat.cast_pos.mpr hr0)
  have h2d : (0 : ℝ) < 2 * (d : ℝ) := (by linarith)
  have hden : (0 : ℝ) < r / (2 * d) := (div_pos hrR h2d)
  have hden2 : (0 : ℝ) < (r / (2 * d)) ^ 2 := (pow_pos hden 2)
  have h8 : 8 * (d : ℝ) ^ 2 ≤ (r : ℝ) := (by
    have hcast : ((8 * d ^ 2 : ℕ) : ℝ) ≤ ((r : ℕ) : ℝ) := (Nat.cast_le.mpr hr)
    have hpush : ((8 * d ^ 2 : ℕ) : ℝ) = 8 * (d : ℝ) ^ 2 := (by push_cast; ring)
    rw [hpush] at hcast
    exact hcast)
  have hs2 : ∑ i : Fin d, ∑ c : Fin r → Fin d, ((cnt c i : ℝ) - r / d) ^ 2 / (r / (2 * d)) ^ 2
      ≤ (d : ℝ) * (((d : ℝ) ^ r * (r : ℝ) / (d : ℝ)) / (r / (2 * d)) ^ 2) := (by
    have hY : ∀ i : Fin d,
        ∑ c : Fin r → Fin d, ((cnt c i : ℝ) - r / d) ^ 2 / (r / (2 * d)) ^ 2
          ≤ ((d : ℝ) ^ r * (r : ℝ) / (d : ℝ)) / (r / (2 * d)) ^ 2 := (by
      intro i
      rw [← Finset.sum_div]
      exact div_le_div_of_nonneg_right (sum_sq_cnt_sub_div_le hd r i) (le_of_lt hden2))
    calc ∑ i : Fin d, ∑ c : Fin r → Fin d, ((cnt c i : ℝ) - r / d) ^ 2 / (r / (2 * d)) ^ 2
        ≤ ∑ _i : Fin d, ((d : ℝ) ^ r * (r : ℝ) / (d : ℝ)) / (r / (2 * d)) ^ 2 :=
          Finset.sum_le_sum (fun i _ => hY i)
      _ = (d : ℝ) * (((d : ℝ) ^ r * (r : ℝ) / (d : ℝ)) / (r / (2 * d)) ^ 2) :=
          (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]))
  have hs3 : (d : ℝ) * (((d : ℝ) ^ r * (r : ℝ) / (d : ℝ)) / (r / (2 * d)) ^ 2)
      ≤ (d : ℝ) ^ r / 2 := (by
    have hnum : (d : ℝ) * (((d : ℝ) ^ r * (r : ℝ) / (d : ℝ)) / (r / (2 * d)) ^ 2)
        = 4 * (d : ℝ) ^ 2 * (d : ℝ) ^ r / (r : ℝ) := (by field_simp; ring)
    rw [hnum, div_le_iff₀ hrR]
    have h4 : 4 * (d : ℝ) ^ 2 ≤ (r : ℝ) / 2 := (by
      calc 4 * (d : ℝ) ^ 2 = (8 * (d : ℝ) ^ 2) / 2 := (by ring)
        _ ≤ (r : ℝ) / 2 := div_le_div_of_nonneg_right h8 (by norm_num))
    have h5 : 4 * (d : ℝ) ^ 2 * (d : ℝ) ^ r ≤ ((r : ℝ) / 2) * (d : ℝ) ^ r :=
      mul_le_mul_of_nonneg_right h4 (pow_nonneg (le_of_lt hdR) r)
    have h6 : ((r : ℝ) / 2) * (d : ℝ) ^ r = (d : ℝ) ^ r / 2 * (r : ℝ) := (by ring)
    rw [← h6]
    exact h5)
  calc ∑ c : Fin r → Fin d, (if ∃ i, (cnt c i : ℝ) < r / (2 * d) then (1 : ℝ) else 0)
      ≤ ∑ c : Fin r → Fin d, ∑ i : Fin d, ((cnt c i : ℝ) - r / d) ^ 2 / (r / (2 * d)) ^ 2 := (by
        apply Finset.sum_le_sum
        intro c _
        by_cases h : ∃ i, (cnt c i : ℝ) < r / (2 * d)
        · obtain ⟨i₀, hi₀⟩ := h
          rw [if_pos ⟨i₀, hi₀⟩]
          have hsingle := Finset.single_le_sum (s := Finset.univ)
            (f := fun i : Fin d => ((cnt c i : ℝ) - r / d) ^ 2 / (r / (2 * d)) ^ 2)
            (fun i _ => div_nonneg (sq_nonneg _) (le_of_lt hden2)) (Finset.mem_univ i₀)
          have h1 : (1 : ℝ) ≤ ((cnt c i₀ : ℝ) - r / d) ^ 2 / (r / (2 * d)) ^ 2 := (by
            rw [le_div_iff₀ hden2, one_mul]
            have hsum : r / (2 * d) + (cnt c i₀ : ℝ) ≤ r / d := (by
              calc r / (2 * d) + (cnt c i₀ : ℝ) ≤ r / (2 * d) + r / (2 * d) :=
                    add_le_add_right (le_of_lt hi₀) _
                _ = 2 * (r / (2 * d)) := (two_mul _).symm
                _ = r / d := (by field_simp))
            have hb : r / (2 * d) ≤ r / d - (cnt c i₀ : ℝ) := ((le_sub_iff_add_le).mpr hsum)
            have h2 : (r / (2 * d)) ^ 2 ≤ (r / d - (cnt c i₀ : ℝ)) ^ 2 :=
              pow_le_pow_left₀ (le_of_lt hden) hb 2
            rw [show ((cnt c i₀ : ℝ) - r / d) ^ 2 = (r / d - (cnt c i₀ : ℝ)) ^ 2 by ring]
            exact h2)
          exact le_trans h1 hsingle
        · rw [if_neg h]
          exact Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (le_of_lt hden2)))
    _ = ∑ i : Fin d, ∑ c : Fin r → Fin d, ((cnt c i : ℝ) - r / d) ^ 2 / (r / (2 * d)) ^ 2 :=
        (by rw [Finset.sum_comm])
    _ ≤ (d : ℝ) * (((d : ℝ) ^ r * (r : ℝ) / (d : ℝ)) / (r / (2 * d)) ^ 2) := hs2
    _ ≤ (d : ℝ) ^ r / 2 := hs3


-- Per-schedule bound: K (cnt c) w = ∏_i P1 (cnt c i) (w i) (unfold K); each factor
-- ≥ c/√(cnt c i) ≥ c/(√2 s) by the 1D bound (hP1) since cnt c i ≥ m₀,
-- |w i| ≤ graphNorm w ≤ s ≤ A √(cnt c i) (A = √(2d), cnt ≥ n/(2d) ≥ s²/(2d)), cnt ≤ n ≤ 2 s²;
-- Finset.prod_le_prod, Finset.prod_const, card_univ.  SPLIT?
/-- For a schedule `c` whose every coordinate count is balanced (at least `n/(2d)` and at least
`m₀`), the product kernel `K (cnt c) w` is at least `(c₁/(√2 s))^d`, from the 1D bound
applied to each coordinate. -/
private theorem const_div_pow_le_prod_P1 (hd : 1 ≤ d) (c₁ : ℝ) (hc₁ : 0 < c₁) (m₀ : ℕ)
    (hP1 : ∀ m : ℕ, m₀ ≤ m → ∀ k : ℤ, |(k : ℝ)| ≤ Real.sqrt (2 * d) * Real.sqrt (m : ℝ) →
      c₁ / Real.sqrt (m : ℝ) ≤ P1 m k)
    (s n : ℕ) (hs : 1 ≤ s) (hn1 : s ^ 2 ≤ n) (hn2 : n ≤ 2 * s ^ 2) (w : Site d)
    (hw : graphNorm w ≤ s) (c : Fin n → Fin d)
    (hc : ∀ i, (n : ℝ) / (2 * d) ≤ cnt c i) (hm₀ : ∀ i, m₀ ≤ cnt c i) :
    (c₁ / (Real.sqrt 2 * s)) ^ d ≤ K (cnt c) w := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have h2d : (0 : ℝ) < 2 * (d : ℝ) := by positivity
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by
    have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    have hs21 : (1 : ℝ) ≤ (s : ℝ) ^ 2 := by
      have h1 : (0 : ℝ) ≤ (s : ℝ) - 1 := by linarith
      have h2 : (0 : ℝ) ≤ (s : ℝ) + 1 := by linarith
      nlinarith [mul_nonneg h1 h2]
    have hs2n : (s : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hbase : (0 : ℝ) < (n : ℝ) / (2 * (d : ℝ)) := by
    have h1 : (1 : ℝ) / (2 * (d : ℝ)) ≤ (n : ℝ) / (2 * (d : ℝ)) :=
      div_le_div_of_nonneg_right hn1R h2d.le
    have hpos : (0 : ℝ) < 1 / (2 * (d : ℝ)) := by positivity
    linarith
  have hprod : ∀ i : Fin d, c₁ / (Real.sqrt 2 * (s : ℝ)) ≤ P1 (cnt c i) (w i) := by
    intro i
    have hcnt_ub : (cnt c i : ℝ) ≤ 2 * (s : ℝ) ^ 2 := by
      have h1 : (cnt c i : ℝ) ≤ (n : ℝ) := by exact_mod_cast cnt_le c i
      have h2 : (n : ℝ) ≤ 2 * (s : ℝ) ^ 2 := by exact_mod_cast hn2
      linarith
    have hsqrt_ub : Real.sqrt (cnt c i : ℝ) ≤ Real.sqrt 2 * (s : ℝ) := by
      have h := Real.sqrt_le_sqrt hcnt_ub
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) ((s : ℝ) ^ 2), Real.sqrt_sq hsR.le] at h
      exact h
    have hcnt_pos : 0 < (cnt c i : ℝ) := lt_of_lt_of_le hbase (hc i)
    have hsqr : 0 < Real.sqrt (cnt c i : ℝ) := by
      rw [Real.sqrt_pos]; exact hcnt_pos
    have hnle : (n : ℝ) ≤ 2 * (d : ℝ) * (cnt c i : ℝ) :=
      calc (n : ℝ) ≤ (cnt c i : ℝ) * (2 * (d : ℝ)) := (div_le_iff₀ h2d).mp (hc i)
        _ = 2 * (d : ℝ) * (cnt c i : ℝ) := by ring
    have h2dcnt : (s : ℝ) ^ 2 ≤ 2 * (d : ℝ) * (cnt c i : ℝ) := by
      have hs2n : (s : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hn1
      linarith
    have hs_le : (s : ℝ) ≤ Real.sqrt (2 * d) * Real.sqrt (cnt c i : ℝ) := by
      have h := Real.sqrt_le_sqrt h2dcnt
      rw [Real.sqrt_sq hsR.le,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ)) (cnt c i : ℝ)] at h
      exact h
    have hwi : |((w i : ℤ) : ℝ)| ≤ Real.sqrt (2 * d) * Real.sqrt (cnt c i : ℝ) := by
      have hsingle_nat : (w i).natAbs ≤ graphNorm w := by
        rw [graphNorm]
        exact Finset.single_le_sum (f := fun j : Fin d => (w j).natAbs) (fun j _ => Nat.zero_le _)
          (Finset.mem_univ i)
      have hwabs : ((w i).natAbs : ℝ) ≤ (s : ℝ) := by
        exact_mod_cast le_trans hsingle_nat hw
      have hAbs : ((w i).natAbs : ℝ) = |((w i : ℤ) : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      calc |((w i : ℤ) : ℝ)| = ((w i).natAbs : ℝ) := hAbs.symm
        _ ≤ (s : ℝ) := hwabs
        _ ≤ Real.sqrt (2 * d) * Real.sqrt (cnt c i : ℝ) := hs_le
    have h1 : c₁ / (Real.sqrt 2 * (s : ℝ)) ≤ c₁ / Real.sqrt (cnt c i : ℝ) :=
      div_le_div_of_nonneg_left hc₁.le hsqr hsqrt_ub
    exact le_trans h1 (hP1 (cnt c i) (hm₀ i) (w i) hwi)
  have hconst : (∏ _i : Fin d, (c₁ / (Real.sqrt 2 * (s : ℝ))))
      = (c₁ / (Real.sqrt 2 * (s : ℝ))) ^ d := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold K
  rw [← hconst]
  refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => hprod i)
  exact div_nonneg hc₁.le (le_of_lt (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hsR))


-- Pointwise: by_cases on the `∃ i, ...` (if_pos: sub_self, mul_zero, hF0 c; if_neg: sub_zero,
-- mul_one, push_neg gives ∀ i, n/(2d) ≤ cnt c i, then hβ c).
/-- Pointwise comparison used to restrict a nonnegative-weighted sum to balanced schedules: `β *
(1 - indicator of unbalanced) ≤ F c`. -/
private theorem le_of_forall_cnt_ge_of_nonneg (n : ℕ) (F : (Fin n → Fin d) → ℝ) (hF0 : ∀ c, 0 ≤ F c)
    (β : ℝ)
    (hβ : ∀ c : Fin n → Fin d, (∀ i, (n : ℝ) / (2 * d) ≤ cnt c i) → β ≤ F c)
    (c : Fin n → Fin d) :
    β * (1 - if ∃ i, (cnt c i : ℝ) < n / (2 * d) then (1 : ℝ) else 0) ≤ F c := by
  by_cases h : ∃ i, (cnt c i : ℝ) < n / (2 * d)
  · rw [if_pos h, sub_self, mul_zero]
    exact hF0 c
  · rw [if_neg h, sub_zero, mul_one]
    exact hβ c (fun i => le_of_not_gt (fun hi => h ⟨i, hi⟩))

-- Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
-- nsmul_eq_mul, Nat.cast_pow (∑ 1 = d^n); sum_ite_exists_cnt_lt_le_half_pow hd n hn; linarith.
/-- At least half the mass `d^n/2` is carried by balanced schedules, for `n ≥ 8d^2`. -/
private theorem pow_div_two_le_sum_one_sub_ite (hd : 1 ≤ d) (n : ℕ) (hn : 8 * d ^ 2 ≤ n) :
    (d : ℝ) ^ n / 2 ≤ ∑ c : Fin n → Fin d,
      (1 - if ∃ i, (cnt c i : ℝ) < n / (2 * d) then (1 : ℝ) else 0) := by
  have hsum : ∑ c : Fin n → Fin d,
      (1 - (if ∃ i, (cnt c i : ℝ) < n / (2 * d) then (1 : ℝ) else 0))
      = (d : ℝ) ^ n - ∑ c : Fin n → Fin d,
          (if ∃ i, (cnt c i : ℝ) < n / (2 * d) then (1 : ℝ) else 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin]
    simp [nsmul_eq_mul]
  rw [hsum]
  linarith [sum_ite_exists_cnt_lt_le_half_pow hd n hn]

-- mul_le_mul_of_nonneg_left (pow_div_two_le_sum_one_sub_ite) hβ0, Finset.mul_sum,
-- Finset.sum_le_sum with le_of_forall_cnt_ge_of_nonneg.
/-- Combines `pow_div_two_le_sum_one_sub_ite` with the pointwise bound
`le_of_forall_cnt_ge_of_nonneg` to lower-bound `∑_c F c` by `β * (d^n/2)`. -/
private theorem mul_pow_div_two_le_sum (hd : 1 ≤ d) (n : ℕ) (hn : 8 * d ^ 2 ≤ n)
    (F : (Fin n → Fin d) → ℝ) (hF0 : ∀ c, 0 ≤ F c) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ∀ c : Fin n → Fin d, (∀ i, (n : ℝ) / (2 * d) ≤ cnt c i) → β ≤ F c) :
    β * ((d : ℝ) ^ n / 2) ≤ ∑ c : Fin n → Fin d, F c := by
  have h2 := mul_le_mul_of_nonneg_left (pow_div_two_le_sum_one_sub_ite hd n hn) hβ0
  rw [Finset.mul_sum] at h2
  exact le_trans h2 (Finset.sum_le_sum (fun c _ => le_of_forall_cnt_ge_of_nonneg n F hF0 β hβ c))

-- iterate_delta0_eq (0 < d), le_div_iff₀ (pow_pos), mul_pow_div_two_le_sum with
-- F := fun c => K (cnt c) w (K_nonneg); linarith / ring.
/-- Applies `mul_pow_div_two_le_sum` to `F c = K (cnt c) w` to lower-bound `Q^[n] delta0 w` by
`β/2`. -/
private theorem div_two_le_iterate_Q_delta0 (hd : 1 ≤ d) (n : ℕ) (hn : 8 * d ^ 2 ≤ n) (w : Site d)
    (β : ℝ)
    (hβ0 : 0 ≤ β)
    (hβ : ∀ c : Fin n → Fin d, (∀ i, (n : ℝ) / (2 * d) ≤ cnt c i) → β ≤ K (cnt c) w) :
    β / 2 ≤ Q^[n] (delta0 : Site d → ℝ) w := by
  rw [iterate_delta0_eq (by omega : 0 < d) n w]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) ^ n)]
  have h := mul_pow_div_two_le_sum hd n hn (fun c => K (cnt c) w)
    (fun c => K_nonneg (cnt c) w) β hβ0 hβ
  nlinarith

-- s ≤ s ^ 2 (Nat.le_self_pow two_ne_zero s); omega / le_trans.
/-- If `s ≥ 2dm₀ + 8d^2 + 1` and `s^2 ≤ n`, then `8d^2 ≤ n`. -/
private theorem le_of_sq_le_sq_add (m₀ s n : ℕ) (hs : 2 * d * m₀ + 8 * d ^ 2 + 1 ≤ s)
    (hn : s ^ 2 ≤ n) :
    8 * d ^ 2 ≤ n := by
  have h1 : 8 * d ^ 2 ≤ s := by omega
  have h2 : s ≤ s ^ 2 := by
    cases s with
    | zero => simp
    | succ k => nlinarith
  omega

-- 2 d m₀ ≤ s ≤ s ^ 2 ≤ n (Nat.le_self_pow), cast (Nat.cast_le, push_cast):
-- m₀ ≤ n/(2d) (le_div_iff₀) ≤ k; Nat.cast_le.mp.
/-- Under the scale hypotheses `s^2 ≤ n` and `s` large, a coordinate count `k` with `n/(2d) ≤ k`
satisfies `m₀ ≤ k`. -/
private theorem le_cnt_of_sq_le (hd : 1 ≤ d) (m₀ s n k : ℕ) (hs : 2 * d * m₀ + 8 * d ^ 2 + 1 ≤ s)
    (hn : s ^ 2 ≤ n) (hk : (n : ℝ) / (2 * d) ≤ (k : ℝ)) : m₀ ≤ k := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  have h2d : (0 : ℝ) < 2 * (d : ℝ) := by linarith
  have hs1 : 2 * d * m₀ ≤ s := by omega
  have hs2 : s ≤ s ^ 2 := by nlinarith [Nat.zero_le s]
  have hmn : (2 * d * m₀ : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (le_trans hs1 (le_trans hs2 hn))
  have hm : (m₀ : ℝ) ≤ (n : ℝ) / (2 * d) := by
    rw [le_div_iff₀ h2d]
    linarith
  exact_mod_cast le_trans hm hk

-- div_mul_eq_div_div, div_pow; ring.
/-- Algebraic identity rewriting `(c₁/(√2 s))^d / 2` as `(c₁/√2)^d / 2 / s^d`. -/
private theorem div_sq_mul_pow_eq_div_pow (c₁ s : ℝ) :
    (c₁ / (Real.sqrt 2 * s)) ^ d / 2 = (c₁ / Real.sqrt 2) ^ d / 2 / s ^ d := by
  rw [div_pow, div_pow, mul_pow]
  rw [div_div, div_div]
  ring_nf

-- Free lazy near-diagonal lower bound.  iterate_delta0_eq; restrict the sum to balanced c
-- (Finset.sum_le_sum_of_subset_of_nonneg, K_nonneg), const_div_pow_le_prod_P1 on each, count ≥
-- d^n/2 by
-- sum_ite_exists_cnt_lt_le_half_pow (complement), s₀ large so that n ≥ 8d² and s²/(2d) ≥ m₀
-- (exists_const_le_P1_of_le_sqrt_mul, A = √(2d)).
-- c₀ := (c₁/√2)^d / 2.  SPLIT?
/-- The free lazy near-diagonal lower bound: there are `c₀ > 0` and `s₀` such that `c₀ / s^d ≤
Q^[n] delta0 w` whenever `s ≥ s₀`, `s^2 ≤ n ≤ 2s^2`, and `graphNorm w ≤ s`. -/
theorem exists_const_le_iterate_Q_delta0_div_pow (hd : 1 ≤ d) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ s₀ : ℕ, 1 ≤ s₀ ∧ ∀ s : ℕ, s₀ ≤ s → ∀ n : ℕ, s ^ 2 ≤ n → n ≤ 2 * s ^ 2 →
      ∀ w : Site d, graphNorm w ≤ s → c₀ / (s : ℝ) ^ d ≤ Q^[n] (delta0 : Site d → ℝ) w := by
  have hd0 : 0 < d := hd
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hA : 0 < Real.sqrt (2 * (d : ℝ)) := Real.sqrt_pos.mpr (by linarith)
  obtain ⟨c₁, hc₁, m₀, _, hP1⟩ := exists_const_le_P1_of_le_sqrt_mul (Real.sqrt (2 * (d : ℝ))) hA
  have hsq2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  refine ⟨(c₁ / Real.sqrt 2) ^ d / 2, div_pos (pow_pos (div_pos hc₁ hsq2) d) two_pos,
    2 * d * m₀ + 8 * d ^ 2 + 1, Nat.le_add_left 1 _, ?_⟩
  intro s hs n hn1 hn2 w hw
  have hs1 : 1 ≤ s := le_trans (Nat.le_add_left 1 _) hs
  have hn8 : 8 * d ^ 2 ≤ n := le_of_sq_le_sq_add m₀ s n hs hn1
  have hβ : ∀ c : Fin n → Fin d, (∀ i, (n : ℝ) / (2 * d) ≤ cnt c i) →
      (c₁ / (Real.sqrt 2 * s)) ^ d ≤ K (cnt c) w := fun c hc =>
    const_div_pow_le_prod_P1 hd c₁ hc₁ m₀ hP1 s n hs1 hn1 hn2 w hw c hc
      (fun i => le_cnt_of_sq_le hd m₀ s n (cnt c i) hs hn1 (hc i))
  have hβ0 : 0 ≤ (c₁ / (Real.sqrt 2 * (s : ℝ))) ^ d :=
    pow_nonneg (div_nonneg hc₁.le (mul_nonneg hsq2.le (Nat.cast_nonneg s))) d
  have h4 := div_two_le_iterate_Q_delta0 hd n hn8 w _ hβ0 hβ
  rw [div_sq_mul_pow_eq_div_pow] at h4
  exact h4

end GreenTwoSided

end LatticeProb
