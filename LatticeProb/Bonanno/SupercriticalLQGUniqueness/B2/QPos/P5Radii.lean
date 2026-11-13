/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5Radii at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5PathCost
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5GridCount
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5AnnulusNonempty

 
















set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P5

open P4

theorem dgffOuterRadius_pow (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℝ) ^ ((n : ℝ) - 1 / 2) = ((2 ^ (n - 1) : ℕ) : ℝ) * Real.sqrt 2 := by
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hcast : (n : ℝ) - 1 / 2 = ((n - 1 : ℕ) : ℝ) + 1 / 2 := by
    have hh : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by exact_mod_cast hn1
    linarith
  rw [hcast, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  norm_cast

 
theorem outer_gap_large (n : ℕ) (hn : 5 ≤ n) :
    dgffInnerRadius n + 1 + 2 ^ (n - 3) < dgffOuterRadius n := by
  have hsqrt : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hp : (16 : ℝ) ≤ ((2 ^ (n - 1) : ℕ) : ℝ) := by
    have : 16 ≤ 2 ^ (n - 1) := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast this
  have h3 : ((2 ^ (n - 3) : ℕ) : ℝ) * 4 = ((2 ^ (n - 1) : ℕ) : ℝ) := by
    have : 2 ^ (n - 3) * 4 = 2 ^ (n - 1) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    exact_mod_cast this
  have hbound : (((2 ^ (n - 1) : ℕ) : ℝ) + 2 + ((2 ^ (n - 3) : ℕ) : ℝ)) ≤
      (2 : ℝ) ^ ((n : ℝ) - 1 / 2) := by
    rw [dgffOuterRadius_pow n (by omega)]
    have hmul := mul_le_mul_of_nonneg_left hsqrt
      (show (0 : ℝ) ≤ ((2 ^ (n - 1) : ℕ) : ℝ) by positivity)
    nlinarith
  have hfloor : 2 ^ (n - 1) + 2 + 2 ^ (n - 3) ≤ dgffOuterRadius n := by
    unfold dgffOuterRadius
    apply Nat.le_floor
    exact_mod_cast hbound
  unfold dgffInnerRadius
  omega

 
theorem outer_le_three_quarters (n : ℕ) : 4 * dgffOuterRadius n ≤ 3 * 2 ^ n := by
  have hsqrt : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hle : (2 : ℝ) ^ ((n : ℝ) - 1 / 2) ≤ (3 / 4) * 2 ^ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, zero_sub, pow_zero, mul_one]
      have : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (by norm_num)
      have h2 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt 2 := by
        rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, one_div]
      rw [h2, div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
      have : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      nlinarith
    · rw [dgffOuterRadius_pow n hn]
      have h2 : ((2 ^ (n - 1) : ℕ) : ℝ) * 2 = (2 : ℝ) ^ n := by
        have : 2 ^ (n - 1) * 2 = 2 ^ n := by
          rw [← pow_succ]; congr 1; omega
        exact_mod_cast this
      have h0 : (0 : ℝ) ≤ ((2 ^ (n - 1) : ℕ) : ℝ) := by positivity
      nlinarith
  have hfl : (dgffOuterRadius n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) - 1 / 2) :=
    Nat.floor_le (by positivity)
  have : (4 * dgffOuterRadius n : ℝ) ≤ 3 * 2 ^ n := by linarith
  exact_mod_cast this

 

theorem latticeRadius_add_le (a b : ℤ × ℤ) :
    latticeRadius (a + b) ≤ latticeRadius a + latticeRadius b := by
  unfold latticeRadius
  simp only [Prod.fst_add, Prod.snd_add]
  have h1 := Int.natAbs_add_le a.1 b.1
  have h2 := Int.natAbs_add_le a.2 b.2
  omega

theorem latticeRadius_neg (a : ℤ × ℤ) : latticeRadius (-a) = latticeRadius a := by
  unfold latticeRadius
  simp

theorem latticeRadius_sub_comm (a b : ℤ × ℤ) : latticeRadius (a - b) = latticeRadius (b - a) := by
  rw [← latticeRadius_neg, neg_sub]

theorem latticeRadius_sub_le (a b c : ℤ × ℤ) :
    latticeRadius (a - c) ≤ latticeRadius (a - b) + latticeRadius (b - c) := by
  have := latticeRadius_add_le (a - b) (b - c)
  rwa [show a - b + (b - c) = a - c by abel] at this

theorem fst_natAbs_le_latticeRadius (a : ℤ × ℤ) : a.1.natAbs ≤ latticeRadius a :=
  le_max_left _ _

theorem snd_natAbs_le_latticeRadius (a : ℤ × ℤ) : a.2.natAbs ≤ latticeRadius a :=
  le_max_right _ _

 
theorem far_endpoint (n : ℕ) (hn : 5 ≤ n) (z : ℤ × ℤ) {γ : List (DGFFSite n)}
    (hγ : IsDGFFAnnulusPath n γ) (hne : 0 < γ.length) :
    2 ^ (n - 4) ≤ latticeRadius ((γ[γ.length - 1]'(by omega)).1 - z) ∨
      2 ^ (n - 4) ≤ latticeRadius ((γ[0]'hne).1 - z) := by
  obtain ⟨-, -, a, b, ha, hb, hra, hrb⟩ := hγ
  have ha' : γ[0]'hne = a := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hne] at ha
    exact Option.some_injective _ ha
  have hb' : γ[γ.length - 1]'(by omega) = b := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hb
    exact Option.some_injective _ hb
  rw [ha', hb']
  by_contra hc
  push_neg at hc
  obtain ⟨h1, h2⟩ := hc
  have hgap := outer_gap_large n hn
  have htri : latticeRadius b.1 ≤ latticeRadius (b.1 - a.1) + latticeRadius a.1 := by
    have := latticeRadius_add_le (b.1 - a.1) a.1
    rwa [sub_add_cancel] at this
  have htri2 := latticeRadius_sub_le b.1 z a.1
  rw [latticeRadius_sub_comm z a.1] at htri2
  have hpow : 2 ^ (n - 4) + 2 ^ (n - 4) = 2 ^ (n - 3) := by
    rw [← two_mul, ← pow_succ']; congr 1; omega
  omega

 

theorem grid_round (n K : ℕ) (hK : K + 3 ≤ n) (v : DGFFSite n) :
    ∃ z ∈ dgffGridCenters n K, latticeRadius (v.1 - z) ≤ 2 ^ (n - K - 2) := by
  set s : ℤ := 2 ^ (n - (K + 1))
  set hs : ℤ := 2 ^ (n - K - 2)
  have hss : s = 2 * hs := by
    simp only [s, hs]; rw [← pow_succ']; congr 1; omega
  have hhs : 0 < hs := by positivity
  have hv := v.2
  rw [mem_interiorSites_iff] at hv
  unfold interiorRadius at hv
  have h2n : (2 : ℤ) ^ n = s * 2 ^ (K + 1) := by
    simp only [s]; rw [← pow_add]; congr 1; omega
  have hround : ∀ x : ℤ, -(2 ^ n - 1) ≤ x → x ≤ 2 ^ n - 1 →
      ∃ w : ℤ, |s * w| ≤ 2 ^ n ∧ |x - s * w| ≤ hs := by
    intro x hx1 hx2
    refine ⟨(x + hs) / s, ?_, ?_⟩
    · have hs0 : 0 < s := by omega
      have e := Int.mul_ediv_add_emod (x + hs) s
      have r0 := Int.emod_nonneg (x + hs) hs0.ne'
      have r1 := Int.emod_lt_of_pos (x + hs) hs0
      set w := (x + hs) / s
      have hup : w ≤ 2 ^ (K + 1) := by
        by_contra hc
        push_neg at hc
        have : s * (2 ^ (K + 1) + 1) ≤ s * w := by
          exact mul_le_mul_of_nonneg_left (by omega) hs0.le
        nlinarith
      have hlo : -(2 ^ (K + 1)) ≤ w := by
        by_contra hc
        push_neg at hc
        have : s * w ≤ s * (-(2 ^ (K + 1)) - 1) := by
          exact mul_le_mul_of_nonneg_left (by omega) hs0.le
        nlinarith
      rw [abs_le]
      constructor
      · have := mul_le_mul_of_nonneg_left hlo hs0.le
        nlinarith
      · have := mul_le_mul_of_nonneg_left hup hs0.le
        nlinarith
    · have hs0 : 0 < s := by omega
      have e := Int.mul_ediv_add_emod (x + hs) s
      have r0 := Int.emod_nonneg (x + hs) hs0.ne'
      have r1 := Int.emod_lt_of_pos (x + hs) hs0
      rw [abs_le]
      constructor <;> linarith
  obtain ⟨w1, hw1, hd1⟩ := hround v.1.1 (by omega) (by omega)
  obtain ⟨w2, hw2, hd2⟩ := hround v.1.2 (by omega) (by omega)
  refine ⟨(s * w1, s * w2), dgffGridCenters_mem_of_center_bounds n K (by omega) (w1, w2) hw1 hw2,
    ?_⟩
  unfold latticeRadius
  simp only [Prod.fst_sub, Prod.snd_sub]
  have : ((max (v.1.1 - s * w1).natAbs (v.1.2 - s * w2).natAbs : ℕ) : ℤ) ≤
      ((2 ^ (n - K - 2) : ℕ) : ℤ) := by
    push_cast; exact max_le hd1 hd2
  exact_mod_cast this

 
theorem goodScale_of_near (n K k : ℕ) (hK : 8 ≤ K) (hn : K + 3 ≤ n) (hk1 : 4 ≤ k)
    (hk2 : k + 1 ≤ K) {v : DGFFSite n} (hv : latticeRadius v.1 ≤ dgffOuterRadius n)
    {z : ℤ × ℤ} (hz : latticeRadius (v.1 - z) ≤ 2 ^ (n - K - 2)) : GoodScale n z k := by
  refine ⟨by omega, ?_⟩
  intro c hc
  rw [mem_sqBox] at hc
  rw [mem_interiorSites_iff]
  unfold interiorRadius
  have hq := outer_le_three_quarters n
  have hzr : latticeRadius z ≤ latticeRadius v.1 + latticeRadius (v.1 - z) := by
    have := latticeRadius_add_le v.1 (-(v.1 - z))
    rw [latticeRadius_neg] at this
    rwa [show v.1 + -(v.1 - z) = z by abel] at this
  have hp1 : 2 ^ (n - K - 2) * 16 ≤ 2 ^ n := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp2 : 2 ^ (n - k) * 16 ≤ 2 ^ n := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpos : 0 < 2 ^ n := Nat.pos_of_ne_zero (by positivity)
  have hzb : latticeRadius z + 2 ^ (n - k) < 2 ^ n := by omega
  have hz1n : z.1.natAbs + 2 ^ (n - k) < 2 ^ n := by
    have := fst_natAbs_le_latticeRadius z; omega
  have hz2n : z.2.natAbs + 2 ^ (n - k) < 2 ^ n := by
    have := snd_natAbs_le_latticeRadius z; omega
  have hz1z : |z.1| + 2 ^ (n - k) < (2 : ℤ) ^ n := by
    have h' : ((z.1.natAbs + 2 ^ (n - k) : ℕ) : ℤ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast hz1n
    push_cast at h'
    exact h'
  have hz2z : |z.2| + 2 ^ (n - k) < (2 : ℤ) ^ n := by
    have h' : ((z.2.natAbs + 2 ^ (n - k) : ℕ) : ℤ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast hz2n
    push_cast at h'
    exact h'
  obtain ⟨hc1, hc2⟩ := hc
  have hcz1 : |c.1| < (2 : ℤ) ^ n := by
    have := abs_sub_abs_le_abs_sub c.1 z.1
    linarith
  have hcz2 : |c.2| < (2 : ℤ) ^ n := by
    have := abs_sub_abs_le_abs_sub c.2 z.2
    linarith
  rw [abs_lt] at hcz1 hcz2
  omega

end SupercriticalLQGUniqueness.B2.QPos.P5
