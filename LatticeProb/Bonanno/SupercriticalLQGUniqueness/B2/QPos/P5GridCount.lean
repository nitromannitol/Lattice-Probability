/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5GridCount at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

 




set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

 

def dgffGridParameterBox (K : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(2 ^ (K + 1) : ℤ)) (2 ^ (K + 1) : ℤ)).product
    (Finset.Icc (-(2 ^ (K + 1) : ℤ)) (2 ^ (K + 1) : ℤ))

 

theorem dgffGridParameterBox_mem_of_center_bounds
    (n K : ℕ) (hK : K + 1 ≤ n) (w : ℤ × ℤ)
    (hx : |(2 ^ (n - (K + 1)) : ℤ) * w.1| ≤ (2 ^ n : ℤ))
    (hy : |(2 ^ (n - (K + 1)) : ℤ) * w.2| ≤ (2 ^ n : ℤ)) :
    w ∈ dgffGridParameterBox K := by
  let s : ℤ := (2 ^ (n - (K + 1)) : ℤ)
  let M : ℤ := (2 ^ (K + 1) : ℤ)
  have hs : 0 < s := by dsimp [s]; positivity
  have hscale_nat : 2 ^ n = 2 ^ (n - (K + 1)) * 2 ^ (K + 1) := by
    rw [← pow_add, Nat.sub_add_cancel hK]
  have hscale : (2 ^ n : ℤ) = s * M := by
    dsimp [s, M]
    exact_mod_cast hscale_nat
  have hcoord (x : ℤ) (h : |s * x| ≤ (2 ^ n : ℤ)) :
      -M ≤ x ∧ x ≤ M := by
    have hbounds := abs_le.mp h
    constructor
    · by_contra hn
      have hlt : x ≤ -M - 1 := by omega
      have hh := mul_le_mul_of_nonneg_left hlt hs.le
      nlinarith [hh]
    · by_contra hn
      have hgt : M + 1 ≤ x := by omega
      have hh := mul_le_mul_of_nonneg_left hgt hs.le
      nlinarith [hh]
  obtain ⟨hxl, hxu⟩ := hcoord w.1 hx
  obtain ⟨hyl, hyu⟩ := hcoord w.2 hy
  simpa [dgffGridParameterBox, M] using
    (show (-M ≤ w.1 ∧ w.1 ≤ M) ∧ (-M ≤ w.2 ∧ w.2 ≤ M) from
      ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩)

 
theorem dgffGridParameterBox_card_le (K : ℕ) :
    (dgffGridParameterBox K).card ≤ 25 * 4 ^ K := by
  let a : ℕ := 2 ^ K
  have ha : 1 ≤ a := by dsimp [a]; exact one_le_pow₀ (by norm_num)
  have hpow : (2 : ℤ) ^ (K + 1) = (2 * a : ℕ) := by
    simp [a, pow_succ, mul_comm]
  have hc : (Finset.Icc (-(2 ^ (K + 1) : ℤ))
      (2 ^ (K + 1) : ℤ)).card = 4 * a + 1 := by
    rw [Int.card_Icc, hpow]
    omega
  have hfour : 4 ^ K = a ^ 2 := by
    dsimp [a]
    calc
      4 ^ K = (2 ^ 2) ^ K := by norm_num
      _ = (2 ^ K) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  have hside : 4 * a + 1 ≤ 5 * a := by omega
  calc
    (dgffGridParameterBox K).card = (4 * a + 1) ^ 2 := by
      simp [dgffGridParameterBox, Finset.card_product, hc, pow_two]
    _ ≤ (5 * a) ^ 2 := by gcongr
    _ = 25 * 4 ^ K := by rw [hfour]; ring

 

def dgffGridCenters (n K : ℕ) : Finset (ℤ × ℤ) :=
  (dgffGridParameterBox K).image fun w =>
    ((2 ^ (n - (K + 1)) : ℤ) * w.1,
      (2 ^ (n - (K + 1)) : ℤ) * w.2)

 
theorem dgffGridCenters_card_le (n K : ℕ) :
    (dgffGridCenters n K).card ≤ 25 * 4 ^ K :=
  (Finset.card_image_le).trans (dgffGridParameterBox_card_le K)

 

theorem dgffGridCenters_mem_of_center_bounds
    (n K : ℕ) (hK : K + 1 ≤ n) (w : ℤ × ℤ)
    (hx : |(2 ^ (n - (K + 1)) : ℤ) * w.1| ≤ (2 ^ n : ℤ))
    (hy : |(2 ^ (n - (K + 1)) : ℤ) * w.2| ≤ (2 ^ n : ℤ)) :
    ((2 ^ (n - (K + 1)) : ℤ) * w.1,
      (2 ^ (n - (K + 1)) : ℤ) * w.2) ∈ dgffGridCenters n K := by
  apply Finset.mem_image.mpr
  exact ⟨w, dgffGridParameterBox_mem_of_center_bounds n K hK w hx hy, rfl⟩

end SupercriticalLQGUniqueness.B2.QPos
