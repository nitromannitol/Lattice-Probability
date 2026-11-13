/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P3TubeGeom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P3Route

 











set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P3

 
def mB : ℕ := 2 ^ 18

theorem mB_pos : 0 < mB := by unfold mB; positivity

 
theorem tube_seg_near {j t m : ℕ} (ht : 0 < t) (hm : 0 < m) {P : ℕ → ℤ × ℤ} {z : ℤ × ℤ}
    {ω : Fin (t * (6 * m)) → Bool × Bool} (hT : TubeGood j t P z (6 * m) ω)
    (q : ℕ) (hq : q < 6) (k : ℕ) (hk1 : q * m * t ≤ k) (hk2 : k ≤ (q + 1) * m * t) :
    ∃ i, i / m = q ∧ |(wpos z ω k).1 - (P i).1| ≤ 129 * j ∧
      |(wpos z ω k).2 - (P i).2| ≤ 129 * j := by
  rcases Nat.lt_or_ge k ((q + 1) * m * t) with hlt | hge
  · refine ⟨k / t, ?_, ?_⟩
    · apply Nat.div_eq_of_lt_le
      · rw [Nat.le_div_iff_mul_le ht]; linarith
      · rw [Nat.div_lt_iff_lt_mul ht]; linarith
    · have hi : k / t < 6 * m := by
        rw [Nat.div_lt_iff_lt_mul ht]
        calc k < (q + 1) * m * t := hlt
          _ ≤ 6 * m * t := by
            apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; omega
      have h := (hT (k / t) hi).1 (k % t) (Nat.mod_lt _ ht).le
      rw [Nat.div_add_mod] at h
      exact h
  · have hk : k = (q + 1) * m * t := le_antisymm hk2 hge
    have e : (q + 1) * m = q * m + m := by ring
    have hm1 : 1 ≤ m := hm
    refine ⟨(q + 1) * m - 1, ?_, ?_⟩
    · apply Nat.div_eq_of_lt_le
      · rw [e]; omega
      · rw [Nat.succ_mul, ← e]; omega
    · have hi : (q + 1) * m - 1 < 6 * m := by
        have : (q + 1) * m ≤ 6 * m := Nat.mul_le_mul_right _ (by omega)
        omega
      have h := (hT _ hi).1 t le_rfl
      have e2 : t * ((q + 1) * m - 1) + t = k := by
        rw [hk]
        have h1 : 1 ≤ (q + 1) * m := by rw [e]; omega
        calc t * ((q + 1) * m - 1) + t = t * ((q + 1) * m - 1 + 1) := by ring
          _ = t * ((q + 1) * m) := by rw [Nat.sub_add_cancel h1]
          _ = (q + 1) * m * t := by ring
      rw [e2] at h
      exact h

 
theorem tube_node {j t m : ℕ} (hm : 0 < m) {ℓ : ℤ} {z : ℤ × ℤ}
    {ω : Fin (t * (6 * m)) → Bool × Bool} (hT : TubeGood j t (routeP ℓ z m) z (6 * m) ω)
    (q : ℕ) (hq1 : 1 ≤ q) (hq : q ≤ 6) :
    |(wpos z ω (q * m * t)).1 - (routeW ℓ z q).1| ≤ j ∧
      |(wpos z ω (q * m * t)).2 - (routeW ℓ z q).2| ≤ j := by
  have hi : q * m - 1 < 6 * m := by
    have : q * m ≤ 6 * m := Nat.mul_le_mul_right _ hq
    have : 0 < q * m := by positivity
    omega
  have h := (hT (q * m - 1) hi).2
  have e1 : q * m - 1 + 1 = q * m := by
    have : 0 < q * m := by positivity
    omega
  rw [e1, routeP_node ℓ z hm, show t * (q * m) = q * m * t by ring] at h
  exact h

 
def SegBox (ℓ δ : ℤ) (z : ℤ × ℤ) (q : ℕ) (v : ℤ × ℤ) : Prop :=
  min (routeW ℓ z q).1 (routeW ℓ z (q + 1)).1 - δ ≤ v.1 ∧
  v.1 ≤ max (routeW ℓ z q).1 (routeW ℓ z (q + 1)).1 + δ ∧
  min (routeW ℓ z q).2 (routeW ℓ z (q + 1)).2 - δ ≤ v.2 ∧
  v.2 ≤ max (routeW ℓ z q).2 (routeW ℓ z (q + 1)).2 + δ

theorem tube_segBox {j t m : ℕ} (ht : 0 < t) (hm : 0 < m) {ℓ : ℤ} {z : ℤ × ℤ}
    {ω : Fin (t * (6 * m)) → Bool × Bool} (hT : TubeGood j t (routeP ℓ z m) z (6 * m) ω)
    (q : ℕ) (hq : q < 6) (k : ℕ) (hk1 : q * m * t ≤ k) (hk2 : k ≤ (q + 1) * m * t) :
    SegBox ℓ (129 * j) z q (wpos z ω k) := by
  obtain ⟨i, hiq, h1, h2⟩ := tube_seg_near ht hm hT q hq k hk1 hk2
  obtain ⟨b1, b2, b3, b4⟩ := routeP_mem_box ℓ z hm i
  rw [hiq] at b1 b2 b3 b4
  rw [abs_le] at h1 h2
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end SupercriticalLQGUniqueness.B2.QPos.P3
