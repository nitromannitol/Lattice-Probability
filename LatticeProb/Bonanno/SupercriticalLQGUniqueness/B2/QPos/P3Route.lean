/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P3Route at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P3Walk2D
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P3Loop

 










set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P3

 
def lerpZ (a b : ℤ) (m r : ℕ) : ℤ := a + (b - a) * r / m

theorem lerpZ_zero (a b : ℤ) (m : ℕ) : lerpZ a b m 0 = a := by simp [lerpZ]

theorem lerpZ_self (a b : ℤ) {m : ℕ} (hm : 0 < m) : lerpZ a b m m = b := by
  unfold lerpZ
  rw [Int.mul_ediv_cancel _ (by exact_mod_cast hm.ne')]
  ring

theorem lerpZ_mem (a b : ℤ) {m r : ℕ} (hm : 0 < m) (hr : r ≤ m) :
    min a b ≤ lerpZ a b m r ∧ lerpZ a b m r ≤ max a b := by
  unfold lerpZ
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hr' : (r : ℤ) ≤ m := by exact_mod_cast hr
  have h1 := Int.ediv_mul_le ((b - a) * r) hm'.ne'
  have h2 := Int.lt_ediv_add_one_mul_self ((b - a) * r) hm'
  set q := (b - a) * r / m
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab]
    have hc : 0 ≤ (b - a) * r := mul_nonneg (by omega) (by positivity)
    have hc' : (b - a) * r ≤ (b - a) * m := mul_le_mul_of_nonneg_left hr' (by omega)
    constructor
    · by_contra h
      have : q ≤ -1 := by omega
      nlinarith
    · by_contra h
      have : b - a + 1 ≤ q := by omega
      nlinarith
  · rw [min_eq_right hab, max_eq_left hab]
    have hc : (b - a) * r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) (by positivity)
    have hc' : (b - a) * m ≤ (b - a) * r := mul_le_mul_of_nonpos_left hr' (by omega)
    constructor
    · by_contra h
      have : q ≤ b - a - 1 := by omega
      nlinarith
    · by_contra h
      have : 1 ≤ q := by omega
      nlinarith

theorem lerpZ_step (a b : ℤ) {m : ℕ} (hm : 0 < m) (J : ℤ) (hab : |b - a| ≤ m * J) (r : ℕ) :
    |lerpZ a b m (r + 1) - lerpZ a b m r| ≤ J := by
  unfold lerpZ
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have h1 := Int.ediv_mul_le ((b - a) * r) hm'.ne'
  have h2 := Int.lt_ediv_add_one_mul_self ((b - a) * r) hm'
  have h3 := Int.ediv_mul_le ((b - a) * ((r + 1 : ℕ) : ℤ)) hm'.ne'
  have h4 := Int.lt_ediv_add_one_mul_self ((b - a) * ((r + 1 : ℕ) : ℤ)) hm'
  set q1 := (b - a) * r / m
  set q2 := (b - a) * ((r + 1 : ℕ) : ℤ) / m
  push_cast at h3 h4
  have hab' := abs_le.mp hab
  rw [abs_le]
  constructor
  · by_contra h
    have : q2 - q1 + 1 ≤ -J := by omega
    nlinarith
  · by_contra h
    have : J + 1 ≤ q2 - q1 := by omega
    nlinarith

 
def lerp (A B : ℤ × ℤ) (m r : ℕ) : ℤ × ℤ := (lerpZ A.1 B.1 m r, lerpZ A.2 B.2 m r)

 
def routeW (ℓ : ℤ) (z : ℤ × ℤ) : ℕ → ℤ × ℤ
  | 0 => z
  | 1 => (36 * ℓ, 0)
  | 2 => (36 * ℓ, 36 * ℓ)
  | 3 => (-36 * ℓ, 36 * ℓ)
  | 4 => (-36 * ℓ, -36 * ℓ)
  | 5 => (39 * ℓ, -36 * ℓ)
  | _ => (39 * ℓ, 6 * ℓ)

 
def routeP (ℓ : ℤ) (z : ℤ × ℤ) (m i : ℕ) : ℤ × ℤ :=
  lerp (routeW ℓ z (i / m)) (routeW ℓ z (i / m + 1)) m (i % m)

theorem routeP_seg (ℓ : ℤ) (z : ℤ × ℤ) {m : ℕ} (hm : 0 < m) (q r : ℕ) (hr : r < m) :
    routeP ℓ z m (q * m + r) = lerp (routeW ℓ z q) (routeW ℓ z (q + 1)) m r := by
  unfold routeP
  have h1 : (q * m + r) / m = q := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hr, zero_add]
  have h2 : (q * m + r) % m = r := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  rw [h1, h2]

theorem routeP_node (ℓ : ℤ) (z : ℤ × ℤ) {m : ℕ} (hm : 0 < m) (q : ℕ) :
    routeP ℓ z m (q * m) = routeW ℓ z q := by
  have := routeP_seg ℓ z hm q 0 hm
  rw [add_zero] at this
  rw [this]
  simp [lerp, lerpZ_zero]

 
theorem routeW_step_bound (ℓ : ℤ) (hℓ : 0 ≤ ℓ) (z : ℤ × ℤ)
    (hz : 41 * ℓ ≤ z.1 ∧ z.1 ≤ 43 * ℓ ∧ |z.2| ≤ ℓ) (q : ℕ) :
    |(routeW ℓ z (q + 1)).1 - (routeW ℓ z q).1| ≤ 75 * ℓ ∧
      |(routeW ℓ z (q + 1)).2 - (routeW ℓ z q).2| ≤ 75 * ℓ := by
  obtain ⟨h1, h2, h3⟩ := hz
  have h3' := abs_le.mp h3
  rcases q with _ | _ | _ | _ | _ | _ | q <;>
    simp only [routeW, abs_le] <;> constructor <;> constructor <;> omega

theorem routeP_step (ℓ : ℤ) (hℓ : 0 ≤ ℓ) (z : ℤ × ℤ)
    (hz : 41 * ℓ ≤ z.1 ∧ z.1 ≤ 43 * ℓ ∧ |z.2| ≤ ℓ) {m : ℕ} (hm : 0 < m) (J : ℤ)
    (hJ : 75 * ℓ ≤ m * J) (i : ℕ) :
    |(routeP ℓ z m (i + 1)).1 - (routeP ℓ z m i).1| ≤ J ∧
      |(routeP ℓ z m (i + 1)).2 - (routeP ℓ z m i).2| ≤ J := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < m ∧ i = q * m + r :=
    ⟨i / m, i % m, Nat.mod_lt _ hm, (Nat.div_add_mod' i m).symm⟩
  obtain ⟨hb1, hb2⟩ := routeW_step_bound ℓ hℓ z hz q
  rw [routeP_seg ℓ z hm q r hr]
  rcases Nat.lt_or_ge (r + 1) m with h | h
  · rw [show q * m + r + 1 = q * m + (r + 1) by ring, routeP_seg ℓ z hm q (r + 1) h]
    simp only [lerp]
    exact ⟨lerpZ_step _ _ hm J (hb1.trans hJ) _, lerpZ_step _ _ hm J (hb2.trans hJ) _⟩
  · have hmeq : r + 1 = m := by omega
    rw [show q * m + r + 1 = (q + 1) * m by rw [add_mul, one_mul]; omega, routeP_node ℓ z hm]
    have k1 := lerpZ_step (routeW ℓ z q).1 (routeW ℓ z (q + 1)).1 hm J (hb1.trans hJ) r
    have k2 := lerpZ_step (routeW ℓ z q).2 (routeW ℓ z (q + 1)).2 hm J (hb2.trans hJ) r
    rw [hmeq, lerpZ_self _ _ hm] at k1 k2
    simp only [lerp]
    exact ⟨k1, k2⟩

 
theorem routeP_mem_box (ℓ : ℤ) (z : ℤ × ℤ) {m : ℕ} (hm : 0 < m) (i : ℕ) :
    min (routeW ℓ z (i / m)).1 (routeW ℓ z (i / m + 1)).1 ≤ (routeP ℓ z m i).1 ∧
    (routeP ℓ z m i).1 ≤ max (routeW ℓ z (i / m)).1 (routeW ℓ z (i / m + 1)).1 ∧
    min (routeW ℓ z (i / m)).2 (routeW ℓ z (i / m + 1)).2 ≤ (routeP ℓ z m i).2 ∧
    (routeP ℓ z m i).2 ≤ max (routeW ℓ z (i / m)).2 (routeW ℓ z (i / m + 1)).2 := by
  have hr : i % m ≤ m := (Nat.mod_lt _ hm).le
  obtain ⟨a1, a2⟩ := lerpZ_mem (routeW ℓ z (i / m)).1 (routeW ℓ z (i / m + 1)).1 hm hr
  obtain ⟨b1, b2⟩ := lerpZ_mem (routeW ℓ z (i / m)).2 (routeW ℓ z (i / m + 1)).2 hm hr
  unfold routeP lerp
  exact ⟨a1, a2, b1, b2⟩

end SupercriticalLQGUniqueness.B2.QPos.P3
