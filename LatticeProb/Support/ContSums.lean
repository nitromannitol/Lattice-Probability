/-
Elementary real and finite-sum inequalities (radial power sums, Boolean
corner weights, square counting by shells), the piecewise-linear
interpolation on the integer mesh, and transport of integrals along a
measure-preserving map: the small self-contained lemmas that the
multi-parameter moment and modulus arguments of the programme need,
offered by the divisible-sandpile repository and lifted here so that
every paper can use them.
-/
import Mathlib

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal

namespace LatticeProb

/-- The tangent-line step of a concave power: for `0 < p ≤ 1` and `x ≥ 1`,
`p (x+1)^{p-1} ≤ (x+1)^p - x^p`. -/
theorem rpow_concave_step (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (x : ℝ) (hx : 1 ≤ x) :
    p * (x + 1) ^ (p - 1) ≤ (x + 1) ^ p - x ^ p := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  set t : ℝ := x / (x + 1) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have hs : (-1 : ℝ) ≤ t - 1 := by
    have : 0 < t := ht0
    linarith
  have hbern : (1 + (t - 1)) ^ p ≤ 1 + p * (t - 1) :=
    _root_.rpow_one_add_le_one_add_mul_self hs hp0.le hp1
  have htp : t ^ p ≤ 1 + p * (t - 1) := by simpa using hbern
  have hmul : (x + 1) ^ p * t ^ p ≤ (x + 1) ^ p * (1 + p * (t - 1)) :=
    mul_le_mul_of_nonneg_left htp (Real.rpow_nonneg hx1.le _)
  have hleft : (x + 1) ^ p * t ^ p = x ^ p := by
    rw [← Real.mul_rpow hx1.le ht0.le, ht]
    congr 1
    field_simp
  have hsub : t - 1 = -(1 / (x + 1)) := by rw [ht]; field_simp; ring
  have hright : (x + 1) ^ p * (1 + p * (t - 1)) = (x + 1) ^ p - p * (x + 1) ^ (p - 1) := by
    rw [hsub, Real.rpow_sub hx1, Real.rpow_one]
    field_simp
    ring
  rw [hleft, hright] at hmul
  linarith

/-- `(b+1)∑_{k=1}^{n} (1+k)^b ≤ (1+n)^{b+1}` for `-1 < b ≤ 0`, by telescoping the
tangent-line step. -/
theorem mul_sum_rpow_neg_le (b : ℝ) (hb : -1 < b) (hb0 : b ≤ 0) (n : ℕ) :
    (b + 1) * ∑ k ∈ Finset.Icc 1 n, (1 + (k : ℝ)) ^ b ≤ (1 + (n : ℝ)) ^ (b + 1) := by
  have hp0 : 0 < b + 1 := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
      have hN : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hstep := rpow_concave_step (b + 1) hp0 (by linarith) (1 + (n : ℝ)) (by linarith)
      rw [show b + 1 - 1 = b from by ring] at hstep
      have e1 : (1 : ℝ) + ((n + 1 : ℕ) : ℝ) = 1 + (n : ℝ) + 1 := by push_cast; ring
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), e1, mul_add]
      linarith

/-- `∑_{k=1}^{n} (1+k)^b ≤ (1+n)^{b+1}/(b+1)` for `-1 < b ≤ 0`. -/
theorem sum_rpow_neg_le (b : ℝ) (hb : -1 < b) (hb0 : b ≤ 0) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (1 + (k : ℝ)) ^ b ≤ (1 + (n : ℝ)) ^ (b + 1) / (b + 1) := by
  have hp0 : 0 < b + 1 := by linarith
  rw [le_div_iff₀ hp0]
  have := mul_sum_rpow_neg_le b hb hb0 n
  linarith

/-- `∑_{k=1}^{n} (1+k)^b ≤ (1+n)^{b+1}` for `0 ≤ b`. -/
theorem sum_rpow_nonneg_le (b : ℝ) (hb : 0 ≤ b) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (1 + (k : ℝ)) ^ b ≤ (1 + (n : ℝ)) ^ (b + 1) := by
  have hbound : ∀ k ∈ Finset.Icc 1 n, (1 + (k : ℝ)) ^ b ≤ (1 + (n : ℝ)) ^ b := by
    intro k hk
    have hkn : (k : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hk).2
    exact Real.rpow_le_rpow (by positivity) (by linarith) hb
  have hcard : (Finset.Icc 1 n).card = n := by simp
  have hsum : ∑ k ∈ Finset.Icc 1 n, (1 + (k : ℝ)) ^ b ≤ (n : ℝ) * (1 + (n : ℝ)) ^ b := by
    calc ∑ k ∈ Finset.Icc 1 n, (1 + (k : ℝ)) ^ b
        ≤ ∑ _k ∈ Finset.Icc 1 n, (1 + (n : ℝ)) ^ b := Finset.sum_le_sum hbound
      _ = (n : ℝ) * (1 + (n : ℝ)) ^ b := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
  refine le_trans hsum ?_
  have hn1 : (0 : ℝ) < 1 + (n : ℝ) := by positivity
  rw [Real.rpow_add_one (ne_of_gt hn1) b]
  have hpow : (0 : ℝ) ≤ (1 + (n : ℝ)) ^ b := Real.rpow_nonneg hn1.le _
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- The two cases together, with one constant. -/
theorem sum_rpow_bound (b : ℝ) (hb : -1 < b) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (1 + (k : ℝ)) ^ b ≤ (1 / (b + 1) + 1) * (1 + (n : ℝ)) ^ (b + 1) := by
  have hp0 : 0 < b + 1 := by linarith
  have hn1 : (0 : ℝ) < 1 + (n : ℝ) := by positivity
  have hpow : (0 : ℝ) ≤ (1 + (n : ℝ)) ^ (b + 1) := Real.rpow_nonneg hn1.le _
  rcases le_or_gt b 0 with hb0 | hb0
  · have := sum_rpow_neg_le b hb hb0 n
    have hdiv : (1 + (n : ℝ)) ^ (b + 1) / (b + 1)
        = (1 / (b + 1)) * (1 + (n : ℝ)) ^ (b + 1) := by ring
    nlinarith
  · have := sum_rpow_nonneg_le b hb0.le n
    nlinarith [one_div_pos.mpr hp0]

/-- The expansion of a product of two-term sums over the Boolean choices. -/
theorem prod_ite_sum (d : ℕ) (a b : Fin d → ℝ) :
    ∑ ε : Fin d → Bool, (∏ i : Fin d, if ε i then a i else b i)
      = ∏ i : Fin d, (a i + b i) := by
  classical
  rw [← Fintype.prod_sum (fun (i : Fin d) (c : Bool) => if c then a i else b i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  simp

/-- The multilinear weights of one cell sum to one, as a function of the
fractional parts.  (`ContGreenFubini.sum_cornerWeight` is the same statement for
the weights read off a point; this form takes the fractional parts directly.) -/
theorem sum_prod_ite (d : ℕ) (t : Fin d → ℝ) :
    ∑ ε : Fin d → Bool, (∏ i : Fin d, if ε i then t i else 1 - t i) = 1 := by
  rw [prod_ite_sum d t (fun i => 1 - t i)]
  simp

/-- A sum over the Boolean corners of a cell, split on the value at one coordinate:
the corners with `ε j = false` index the pairs. -/
theorem sum_pi_bool_split {d : ℕ} (j : Fin d) (g : (Fin d → Bool) → ℝ) :
    ∑ ε : Fin d → Bool, g ε
      = ∑ ε ∈ Finset.univ.filter (fun ε : Fin d → Bool => ε j = false),
          (g ε + g (Function.update ε j true)) := by
  classical
  rw [Finset.sum_add_distrib,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ε : Fin d → Bool => ε j = false) g]
  congr 1
  refine Finset.sum_nbij' (fun ε => Function.update ε j false)
    (fun ε => Function.update ε j true) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp
  · intro a ha
    simp at ha ⊢
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have : a j = true := by
      cases h : a j with
      | false => exact absurd h ha
      | true => rfl
    rw [Function.update_idem, ← this, Function.update_eq_self]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [Function.update_idem, ← ha, Function.update_eq_self]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have : a j = true := by
      cases h : a j with
      | false => exact absurd h ha
      | true => rfl
    rw [Function.update_idem, ← this, Function.update_eq_self]

/-- Subadditivity of the square root. -/
theorem sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have h2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have h : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt a + Real.sqrt b :=
        Real.sqrt_sq (by positivity)

/-- A power with a larger exponent on a bounded range, in terms of the power with
the smaller exponent. -/
theorem rpow_le_mul_rpow_of_le {x D s t : ℝ} (hx : 0 ≤ x) (hxD : x ≤ D)
    (ht : 0 < t) (hts : t ≤ s) : x ^ s ≤ D ^ (s - t) * x ^ t := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · rw [← hx0, Real.zero_rpow (by linarith), Real.zero_rpow (by linarith), mul_zero]
  · have hst : (0:ℝ) ≤ s - t := by linarith
    have h1 : x ^ (s - t) ≤ D ^ (s - t) := Real.rpow_le_rpow hx hxD hst
    have h2 : x ^ s = x ^ t * x ^ (s - t) := by
      rw [← Real.rpow_add hx0]; ring_nf
    rw [h2, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hx _)

/-- Two integer floors differ by at most the distance of their arguments plus one. -/
theorem abs_intFloor_sub_le (u v : ℝ) :
    |((⌊u⌋ : ℤ) : ℝ) - ((⌊v⌋ : ℤ) : ℝ)| ≤ |u - v| + 1 := by
  have h1 : ((⌊u⌋ : ℤ) : ℝ) ≤ u := Int.floor_le u
  have h2 : u < ((⌊u⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one u
  have h3 : ((⌊v⌋ : ℤ) : ℝ) ≤ v := Int.floor_le v
  have h4 : v < ((⌊v⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one v
  have h5 : u - v ≤ |u - v| := le_abs_self _
  have h6 : -(u - v) ≤ |u - v| := neg_le_abs _
  rw [abs_le]
  constructor <;> linarith

/-- Two natural floors of nonnegative reals differ by at most the distance of
their arguments plus one. -/
theorem abs_natFloor_sub_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |((⌊u⌋₊ : ℕ) : ℝ) - ((⌊v⌋₊ : ℕ) : ℝ)| ≤ |u - v| + 1 := by
  have h1 : ((⌊u⌋₊ : ℕ) : ℝ) ≤ u := Nat.floor_le hu
  have h2 : u < ((⌊u⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one u
  have h3 : ((⌊v⌋₊ : ℕ) : ℝ) ≤ v := Nat.floor_le hv
  have h4 : v < ((⌊v⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one v
  have h5 : u - v ≤ |u - v| := le_abs_self _
  have h6 : -(u - v) ≤ |u - v| := neg_le_abs _
  rw [abs_le]
  constructor <;> linarith

/-- The square root of a real power. -/
theorem sqrt_rpow_eq {z : ℝ} (hz : 0 ≤ z) (s : ℝ) : Real.sqrt (z ^ s) = z ^ (s / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz]
  congr 1
  ring

/-- A real power of a square. -/
theorem rpow_sq_eq {R : ℝ} (hR : 0 ≤ R) (s : ℝ) : (R ^ 2) ^ s = R ^ (2 * s) := by
  rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR]
  norm_num

/-- Splitting a power at a product that is at most one. -/
theorem rpow_one_sub_mul_le {M y p : ℝ} (hM : 0 ≤ M) (hy : 0 ≤ y) (hp1 : p ≤ 1)
    (h : M * y ≤ 1) : M ^ (1 - p) * y ≤ y ^ p := by
  rcases eq_or_lt_of_le hy with hy0 | hy0
  · rw [← hy0, mul_zero]
    exact Real.rpow_nonneg le_rfl p
  · have hsplit : y ^ (1 - p) * y ^ p = y := by
      rw [← Real.rpow_add hy0]
      norm_num
    calc M ^ (1 - p) * y = M ^ (1 - p) * (y ^ (1 - p) * y ^ p) := by rw [hsplit]
      _ = (M * y) ^ (1 - p) * y ^ p := by rw [Real.mul_rpow hM hy]; ring
      _ ≤ 1 ^ (1 - p) * y ^ p :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (by positivity) h (by linarith)) (Real.rpow_nonneg hy _)
      _ = y ^ p := by rw [Real.one_rpow, one_mul]

/-- A bound on the `p`-th root is a bound on the quantity. -/
theorem rpow_le_of_rpow_inv_le {A B p : ℝ} (hp : 0 < p) (hA : 0 ≤ A)
    (h : A ^ (1 / p) ≤ B) : A ≤ B ^ p := by
  have hid : (A ^ (1 / p)) ^ p = A := by
    rw [← Real.rpow_mul hA, one_div_mul_cancel hp.ne', Real.rpow_one]
  calc A = (A ^ (1 / p)) ^ p := hid.symm
    _ ≤ B ^ p := Real.rpow_le_rpow (Real.rpow_nonneg hA _) h hp.le

/-- Counting the square by the larger index. -/
theorem sum_sum_max (g : ℕ → ℝ) (k : ℕ) :
    ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, g (max a b)
      = ∑ s ∈ Finset.range k, (2 * (s : ℝ) + 1) * g s := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hinner : ∀ a ∈ Finset.range k, ∑ b ∈ Finset.range (k+1), g (max a b)
        = (∑ b ∈ Finset.range k, g (max a b)) + g k := by
      intro a ha
      rw [Finset.sum_range_succ]
      have hak : a ≤ k := le_of_lt (Finset.mem_range.mp ha)
      rw [max_eq_right hak]
    have hlast : ∑ b ∈ Finset.range (k+1), g (max k b) = ((k:ℝ)+1) * g k := by
      have hc : ∀ b ∈ Finset.range (k+1), g (max k b) = g k := by
        intro b hb
        have hbk : b ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
        rw [max_eq_left hbk]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    rw [Finset.sum_range_succ, Finset.sum_congr rfl hinner, hlast, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, ih, Finset.sum_range_succ]
    ring

/-- The power sum over an initial range, in the shifted form. -/
theorem sum_range_one_add_rpow_le {b : ℝ} (hb : -1 < b) (k : ℕ) :
    ∑ s ∈ Finset.range k, (1 + (s : ℝ)) ^ b
      ≤ (1 / (b + 1) + 2) * (1 + (k : ℝ)) ^ (b + 1) := by
  have hp0 : 0 < b + 1 := by linarith
  cases k with
  | zero =>
    simp
    positivity
  | succ n =>
    have hset : Finset.range (n+1) = insert 0 (Finset.Icc 1 n) := by
      ext x
      simp [Finset.mem_Icc, Finset.mem_range]
      omega
    have hnot : (0 : ℕ) ∉ Finset.Icc 1 n := by simp
    have hsum : ∑ s ∈ Finset.range (n+1), (1 + (s : ℝ)) ^ b
        = 1 + ∑ s ∈ Finset.Icc 1 n, (1 + (s : ℝ)) ^ b := by
      rw [hset, Finset.sum_insert hnot]
      norm_num
    have hb2 := sum_rpow_bound b hb n
    have h1 : (0:ℝ) < 1 + (n : ℝ) := by positivity
    have h2 : (1 : ℝ) + (n : ℝ) ≤ 1 + ((n : ℝ) + 1) := by linarith
    have hmono : (1 + (n : ℝ)) ^ (b + 1) ≤ (1 + ((n : ℝ) + 1)) ^ (b + 1) :=
      Real.rpow_le_rpow h1.le h2 hp0.le
    have hone : (1 : ℝ) ≤ (1 + ((n : ℝ) + 1)) ^ (b + 1) := by
      apply Real.one_le_rpow (by linarith) hp0.le
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hsum, hcast]
    have hc : (0:ℝ) ≤ 1 / (b + 1) := by positivity
    nlinarith [hb2, hmono, hone]

/-- **The double time sum, counted by the larger index.**  Every cell of the
square `[0,k) × [0,m)` contributes a power of `1 + a + 2j`, which is at most the
same power of `1 + max(a,j)`; the shell `max(a,j) = s` has `2s+1` cells, and the
telescoping power sum finishes. -/
theorem sum_sum_shift_rpow_le {e : ℝ} (he : e ≤ 0) (he2 : -2 < e) (k m : ℕ)
    (hm : m ≤ k) :
    ∑ a ∈ Finset.range k, ∑ j ∈ Finset.range m, (1 + ((a + 2 * j : ℕ) : ℝ)) ^ e
      ≤ 2 * (1 / (e + 2) + 2) * (1 + (k : ℝ)) ^ (e + 2) := by
  have he1 : (-1:ℝ) < 1 + e := by linarith
  have hterm : ∀ a ∈ Finset.range k, ∑ j ∈ Finset.range m, (1 + ((a + 2 * j : ℕ) : ℝ)) ^ e
      ≤ ∑ j ∈ Finset.range k, (1 + ((max a j : ℕ) : ℝ)) ^ e := by
    intro a _
    calc ∑ j ∈ Finset.range m, (1 + ((a + 2 * j : ℕ) : ℝ)) ^ e
        ≤ ∑ j ∈ Finset.range m, (1 + ((max a j : ℕ) : ℝ)) ^ e := by
          refine Finset.sum_le_sum ?_
          intro j _
          have hnat : max a j ≤ a + 2 * j := by omega
          have hle : ((max a j : ℕ) : ℝ) ≤ ((a + 2 * j : ℕ) : ℝ) := by exact_mod_cast hnat
          exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) he
      _ ≤ ∑ j ∈ Finset.range k, (1 + ((max a j : ℕ) : ℝ)) ^ e := by
          have hsub : Finset.range m ⊆ Finset.range k := fun x hx =>
            Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hm)
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
          intro j _ _
          positivity
  have hsum1 : ∑ a ∈ Finset.range k, ∑ j ∈ Finset.range m, (1 + ((a + 2 * j : ℕ) : ℝ)) ^ e
      ≤ ∑ a ∈ Finset.range k, ∑ j ∈ Finset.range k, (1 + ((max a j : ℕ) : ℝ)) ^ e :=
    Finset.sum_le_sum hterm
  have hmax := sum_sum_max (fun s : ℕ => (1 + ((s : ℕ) : ℝ)) ^ e) k
  have hshell : ∑ s ∈ Finset.range k, (2 * (s : ℝ) + 1) * (1 + (s : ℝ)) ^ e
      ≤ 2 * ∑ s ∈ Finset.range k, (1 + (s : ℝ)) ^ (1 + e) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro s _
    have hpos : (0:ℝ) < 1 + (s : ℝ) := by positivity
    have hsp : (1 + (s : ℝ)) ^ (1 + e) = (1 + (s : ℝ)) * (1 + (s : ℝ)) ^ e := by
      rw [Real.rpow_add hpos, Real.rpow_one]
    rw [hsp]
    have hnn : (0:ℝ) ≤ (1 + (s : ℝ)) ^ e := Real.rpow_nonneg hpos.le e
    have hs0 : (0:ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    nlinarith [hnn, hs0]
  have hpow := sum_range_one_add_rpow_le (b := 1 + e) he1 k
  have hfin : (1:ℝ) + e + 1 = e + 2 := by ring
  rw [hfin] at hpow
  linarith [hsum1, hmax.le, hmax.ge, hshell, hpow]

/-- The double power sum over a square, counted by shells: the shell
`max(a,b) = s` has `2s+1` cells, and `2s+1 ≤ 3(1+s)`. -/
theorem sum_sum_max_rpow_le {e : ℝ} (he2 : -2 < e) (k : ℕ) :
    ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, (1 + ((max a b : ℕ) : ℝ)) ^ e
      ≤ 3 * (1 / (e + 2) + 2) * (1 + (k : ℝ)) ^ (e + 2) := by
  rw [sum_sum_max (fun s => (1 + (s : ℝ)) ^ e) k]
  have hstep : ∀ s ∈ Finset.range k,
      (2 * (s : ℝ) + 1) * (1 + (s : ℝ)) ^ e ≤ 3 * (1 + (s : ℝ)) ^ (e + 1) := by
    intro s _
    have hpos : (0:ℝ) < 1 + (s : ℝ) := by positivity
    have hsplit : (1 + (s : ℝ)) ^ (e + 1) = (1 + (s : ℝ)) ^ e * (1 + (s : ℝ)) := by
      rw [Real.rpow_add hpos, Real.rpow_one]
    have hnn : (0:ℝ) ≤ (1 + (s : ℝ)) ^ e := Real.rpow_nonneg hpos.le e
    have hs0 : (0:ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    rw [hsplit]
    nlinarith [hnn, hs0]
  have hexp : e + 1 + 1 = e + 2 := by ring
  calc ∑ s ∈ Finset.range k, (2 * (s : ℝ) + 1) * (1 + (s : ℝ)) ^ e
      ≤ ∑ s ∈ Finset.range k, 3 * (1 + (s : ℝ)) ^ (e + 1) := Finset.sum_le_sum hstep
    _ = 3 * ∑ s ∈ Finset.range k, (1 + (s : ℝ)) ^ (e + 1) := by rw [Finset.mul_sum]
    _ ≤ 3 * ((1 / (e + 1 + 1) + 2) * (1 + (k : ℝ)) ^ (e + 1 + 1)) :=
        mul_le_mul_of_nonneg_left (sum_range_one_add_rpow_le (by linarith) k) (by norm_num)
    _ = 3 * (1 / (e + 2) + 2) * (1 + (k : ℝ)) ^ (e + 2) := by rw [hexp]; ring

/-- **The `ℓ^p` norm is at most the `ℓ²` norm for `p ≥ 2`**, in the form the
weighted concentration lemma's second sum needs. -/
theorem sum_abs_rpow_le (p : ℝ) (hp : 2 ≤ p) {N : ℕ} (c : Fin N → ℝ) :
    ∑ i, |c i| ^ p ≤ Real.sqrt (∑ i, c i ^ 2) ^ p := by
  have hS0 : (0:ℝ) ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hSq : Real.sqrt (∑ i, c i ^ 2) ^ 2 = ∑ i, c i ^ 2 := Real.sq_sqrt hS0
  have hSnn : (0:ℝ) ≤ Real.sqrt (∑ i, c i ^ 2) := Real.sqrt_nonneg _
  have hr2 : ∀ x : ℝ, x ^ (2:ℝ) = x ^ 2 := fun x => by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hne : (2:ℝ) + (p - 2) ≠ 0 := by linarith
  have hsplit : ∀ x : ℝ, 0 ≤ x → x ^ p = x ^ 2 * x ^ (p - 2) := by
    intro x hx
    have h : x ^ p = x ^ ((2:ℝ) + (p - 2)) := by congr 1; ring
    rw [h, Real.rpow_add' hx hne, hr2 x]
  have hle : ∀ i : Fin N, |c i| ≤ Real.sqrt (∑ i, c i ^ 2) := by
    intro i
    have h1 : c i ^ 2 ≤ ∑ j, c j ^ 2 :=
      Finset.single_le_sum (f := fun j => c j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq_eq_abs] at h2
  have hterm : ∀ i : Fin N, |c i| ^ p ≤ c i ^ 2 * Real.sqrt (∑ i, c i ^ 2) ^ (p - 2) := by
    intro i
    rw [hsplit (|c i|) (abs_nonneg _), sq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    exact Real.rpow_le_rpow (abs_nonneg _) (hle i) (by linarith)
  calc ∑ i, |c i| ^ p
      ≤ ∑ i, c i ^ 2 * Real.sqrt (∑ i, c i ^ 2) ^ (p - 2) := Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i, c i ^ 2) * Real.sqrt (∑ i, c i ^ 2) ^ (p - 2) := by rw [← Finset.sum_mul]
    _ = Real.sqrt (∑ i, c i ^ 2) ^ p := by rw [hsplit _ hSnn, hSq]

/-- A linear functional is Lipschitz in each coordinate with the absolute value
of the coefficient as its constant. -/
theorem abs_linear_sub_update_le {N : ℕ} (c ξ : Fin N → ℝ) (j : Fin N) (y : ℝ) :
    |(∑ i, c i * ξ i) - ∑ i, c i * Function.update ξ j y i| ≤ |c j| * |ξ j - y| := by
  classical
  have hsum : ∑ i, (c i * ξ i - c i * Function.update ξ j y i) = c j * (ξ j - y) := by
    rw [Finset.sum_eq_single j]
    · rw [Function.update_self]; ring
    · intro i _ hij
      rw [Function.update_of_ne hij]
      ring
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [← Finset.sum_sub_distrib, hsum, abs_mul]

/-- The multilinear weight of a corner with `j`-th entry `false` factors as
`1 - t j` times the product over the other coordinates. -/
theorem prod_ite_erase_false {d : ℕ} (t : Fin d → ℝ) (j : Fin d) (c : Fin d → Bool)
    (hc : c j = false) :
    (∏ i : Fin d, if c i then t i else 1 - t i)
      = (1 - t j) * ∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ (fun i => if c i then t i else 1 - t i)
    (Finset.mem_univ j), hc]
  simp

/-- The multilinear weight of the partner corner, with `j`-th entry `true`,
factors as `t j` times the same product over the other coordinates. -/
theorem prod_ite_erase_true {d : ℕ} (t : Fin d → ℝ) (j : Fin d) (c : Fin d → Bool) :
    (∏ i : Fin d, if (Function.update c j true) i then t i else 1 - t i)
      = t j * ∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ
    (fun i => if (Function.update c j true) i then t i else 1 - t i) (Finset.mem_univ j)]
  have hj : (Function.update c j true) j = true := Function.update_self j true c
  rw [hj]
  have hrest : ∏ i ∈ Finset.univ.erase j,
      (if (Function.update c j true) i then t i else 1 - t i)
      = ∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    rw [Function.update_of_ne hij]
  rw [hrest]
  simp

/-- The weights of the `2^{d-1}` corners of the other coordinates sum to one. -/
theorem sum_filter_prod_ite_erase {d : ℕ} (t : Fin d → ℝ) (j : Fin d) :
    ∑ c ∈ Finset.univ.filter (fun c : Fin d → Bool => c j = false),
      (∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i)) = 1 := by
  classical
  calc ∑ c ∈ Finset.univ.filter (fun c : Fin d → Bool => c j = false),
        (∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i))
      = ∑ c ∈ Finset.univ.filter (fun c : Fin d → Bool => c j = false),
        ((∏ i : Fin d, if c i then t i else 1 - t i)
          + (∏ i : Fin d, if (Function.update c j true) i then t i else 1 - t i)) := by
        refine Finset.sum_congr rfl fun c hc => ?_
        have hcj : c j = false := (Finset.mem_filter.mp hc).2
        rw [prod_ite_erase_false t j c hcj, prod_ite_erase_true t j c]
        ring
    _ = ∑ ε : Fin d → Bool, (∏ i : Fin d, if ε i then t i else 1 - t i) :=
        (sum_pi_bool_split j (fun ε : Fin d → Bool => ∏ i : Fin d, if ε i then t i else 1 - t i)).symm
    _ = 1 := sum_prod_ite d t

/-- The piecewise-linear interpolation of a bi-infinite family of reals from the
integer mesh: at `u` it is the affine combination of the values at `⌊u⌋` and
`⌊u⌋+1` with the weights given by the fractional part of `u`. -/
noncomputable def interp1 (F : ℤ → ℝ) (u : ℝ) : ℝ :=
  (1 - Int.fract u) * F ⌊u⌋ + Int.fract u * F (⌊u⌋ + 1)

/-- At an integer the interpolation returns the mesh value. -/
theorem interp1_intCast (F : ℤ → ℝ) (m : ℤ) : interp1 F ((m : ℝ)) = F m := by
  rw [interp1, Int.fract_intCast, Int.floor_intCast]
  ring

/-- Inside one cell the interpolation is affine with slope the mesh increment,
so its increment is at most the largest mesh increment times the displacement. -/
theorem abs_interp1_sub_le_same_incr (F : ℤ → ℝ) (K : ℝ)
    (hK : ∀ n : ℤ, |F (n + 1) - F n| ≤ K) {u v : ℝ} (h : ⌊u⌋ = ⌊v⌋) :
    |interp1 F u - interp1 F v| ≤ K * |u - v| := by
  have hfr : Int.fract u - Int.fract v = u - v := by
    rw [Int.fract, Int.fract, h]
    ring
  have hkey : interp1 F u - interp1 F v = (u - v) * (F (⌊u⌋ + 1) - F ⌊u⌋) := by
    rw [interp1, interp1, h, ← hfr]
    ring
  have hdiff : |F (⌊u⌋ + 1) - F ⌊u⌋| ≤ K := hK ⌊u⌋
  have hK0 : (0:ℝ) ≤ K := le_trans (abs_nonneg _) (hK 0)
  rw [hkey, abs_mul]
  calc |u - v| * |F (⌊u⌋ + 1) - F ⌊u⌋| ≤ |u - v| * K :=
        mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
    _ = K * |u - v| := by ring

/-- The interpolation at `u` differs from the mesh value at the right endpoint of
its cell by at most the largest mesh increment times the distance to that
endpoint. -/
theorem abs_interp1_sub_succ_incr (F : ℤ → ℝ) (K : ℝ)
    (hK : ∀ n : ℤ, |F (n + 1) - F n| ≤ K) (u : ℝ) :
    |interp1 F u - F (⌊u⌋ + 1)| ≤ K * ((⌊u⌋ : ℝ) + 1 - u) := by
  have hkey : interp1 F u - F (⌊u⌋ + 1) = (1 - Int.fract u) * (F ⌊u⌋ - F (⌊u⌋ + 1)) := by
    rw [interp1]
    ring
  have hf1 : Int.fract u < 1 := Int.fract_lt_one u
  have hfr : 1 - Int.fract u = (⌊u⌋ : ℝ) + 1 - u := by
    rw [Int.fract]
    ring
  have hdiff : |F ⌊u⌋ - F (⌊u⌋ + 1)| ≤ K := by
    rw [abs_sub_comm]
    exact hK ⌊u⌋
  rw [hkey, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - Int.fract u), hfr]
  have hnn : (0:ℝ) ≤ (⌊u⌋ : ℝ) + 1 - u := by rw [← hfr]; linarith
  calc ((⌊u⌋ : ℝ) + 1 - u) * |F ⌊u⌋ - F (⌊u⌋ + 1)| ≤ ((⌊u⌋ : ℝ) + 1 - u) * K :=
        mul_le_mul_of_nonneg_left hdiff hnn
    _ = K * ((⌊u⌋ : ℝ) + 1 - u) := by ring

/-- The interpolation is `K`-Lipschitz for the largest mesh increment `K`, by
induction on the number of mesh cells separating the two points. -/
theorem abs_interp1_sub_le_incr_aux (F : ℤ → ℝ) (K : ℝ) (hK : ∀ n : ℤ, |F (n + 1) - F n| ≤ K) :
    ∀ m : ℕ, ∀ u v : ℝ, u ≤ v → (⌊v⌋ - ⌊u⌋).toNat ≤ m →
      |interp1 F u - interp1 F v| ≤ K * (v - u) := by
  intro m
  induction m with
  | zero =>
      intro u v huv hk
      have hle : ⌊u⌋ ≤ ⌊v⌋ := Int.floor_le_floor huv
      have hfl : ⌊u⌋ = ⌊v⌋ := by omega
      have hsame := abs_interp1_sub_le_same_incr F K hK hfl
      rw [abs_of_nonpos (by linarith : u - v ≤ 0), neg_sub] at hsame
      exact hsame
  | succ m ih =>
      intro u v huv hk
      have hle : ⌊u⌋ ≤ ⌊v⌋ := Int.floor_le_floor huv
      by_cases hfl : ⌊u⌋ = ⌊v⌋
      · have hsame := abs_interp1_sub_le_same_incr F K hK hfl
        rw [abs_of_nonpos (by linarith : u - v ≤ 0), neg_sub] at hsame
        exact hsame
      · have hlt : ⌊u⌋ < ⌊v⌋ := lt_of_le_of_ne hle hfl
        set y : ℝ := ((⌊u⌋ + 1 : ℤ) : ℝ) with hy
        have hfw : ⌊y⌋ = ⌊u⌋ + 1 := by rw [hy, Int.floor_intCast]
        have huw : u ≤ y := by
          have h0 := Int.lt_floor_add_one u
          rw [hy]
          push_cast
          linarith
        have hwv : y ≤ v := by
          have h1 : ((⌊u⌋ + 1 : ℤ) : ℝ) ≤ ((⌊v⌋ : ℤ) : ℝ) := by
            exact_mod_cast (by omega : (⌊u⌋ + 1 : ℤ) ≤ ⌊v⌋)
          have h2 : ((⌊v⌋ : ℤ) : ℝ) ≤ v := Int.floor_le v
          rw [hy]
          linarith
        have h1 : |interp1 F u - interp1 F y| ≤ K * (y - u) := by
          have hval : interp1 F y = F (⌊u⌋ + 1) := by rw [hy, interp1_intCast]
          have hwu : (⌊u⌋ : ℝ) + 1 - u = y - u := by rw [hy]; push_cast; ring
          rw [hval, ← hwu]
          exact abs_interp1_sub_succ_incr F K hK u
        have h2 : |interp1 F y - interp1 F v| ≤ K * (v - y) :=
          ih y v hwv (by rw [hfw]; omega)
        calc |interp1 F u - interp1 F v|
            ≤ |interp1 F u - interp1 F y| + |interp1 F y - interp1 F v| :=
              abs_sub_le _ _ _
          _ ≤ K * (y - u) + K * (v - y) := add_le_add h1 h2
          _ = K * (v - u) := by ring

/-- **The interpolation is `K`-Lipschitz**, `K` the largest mesh increment.  This
is sharper than `abs_interp1_sub_le`, whose constant is twice the largest mesh
value; at the mesh scale the increment is the quantity that is small. -/
theorem abs_interp1_sub_le_incr (F : ℤ → ℝ) (K : ℝ) (hK : ∀ n : ℤ, |F (n + 1) - F n| ≤ K)
    (u v : ℝ) : |interp1 F u - interp1 F v| ≤ K * |u - v| := by
  rcases le_total u v with h | h
  · rw [abs_of_nonpos (by linarith : u - v ≤ 0), neg_sub]
    exact abs_interp1_sub_le_incr_aux F K hK (⌊v⌋ - ⌊u⌋).toNat u v h le_rfl
  · rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ u - v)]
    exact abs_interp1_sub_le_incr_aux F K hK (⌊u⌋ - ⌊v⌋).toNat v u h le_rfl

theorem integral_comp_mp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μa : Measure α} {μb : Measure β} {g : α → β} (hg : MeasurePreserving g μa μb)
    (f : β → ℝ) (hf : AEStronglyMeasurable f μb) :
    ∫ y, f y ∂μb = ∫ x, f (g x) ∂μa := by
  conv_lhs => rw [← hg.map_eq]
  exact integral_map hg.measurable.aemeasurable (by rwa [hg.map_eq])

theorem integrable_comp_mp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μa : Measure α} {μb : Measure β} {g : α → β} (hg : MeasurePreserving g μa μb)
    (f : β → ℝ) (hf : AEStronglyMeasurable f μb) (h : Integrable f μb) :
    Integrable (fun x => f (g x)) μa :=
  (integrable_map_measure (by rwa [hg.map_eq]) hg.measurable.aemeasurable).mp
    (by rwa [hg.map_eq])

theorem integral_linear_pi_eq_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hνint : Integrable (fun z : ℝ => z) ν) {N : ℕ} (c : Fin N → ℝ) :
    ∫ ξ, (∑ i, c i * ξ i) ∂(Measure.pi fun _ : Fin N => ν) = 0 := by
  classical
  have hcoord : ∀ i : Fin N, MeasurePreserving (fun ξ : Fin N → ℝ => ξ i)
      (Measure.pi fun _ : Fin N => ν) ν := fun i => measurePreserving_eval _ i
  have hxi : ∀ i : Fin N,
      Integrable (fun ξ : Fin N → ℝ => ξ i) (Measure.pi fun _ : Fin N => ν) := fun i =>
    integrable_comp_mp (hcoord i) (fun z => z)
      measurable_id.aestronglyMeasurable hνint
  have hximean : ∀ i : Fin N, ∫ ξ, ξ i ∂(Measure.pi fun _ : Fin N => ν) = 0 := by
    intro i
    rw [← integral_comp_mp (hcoord i) (fun z => z)
      measurable_id.aestronglyMeasurable]
    exact hmean
  rw [integral_finsetSum _ fun i _ => (hxi i).const_mul (c i)]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_const_mul, hximean i, mul_zero]

end LatticeProb
