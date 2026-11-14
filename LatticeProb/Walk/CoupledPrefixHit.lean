import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.HitTime

/-!
# Coupled paths up to a hitting time

Paths driven by the same updates agree through the first hit of a set when the
update rules agree outside that set. In particular their hitting times agree,
including the cases of an initial hit and an infinite hitting time.
-/

set_option autoImplicit false

open MatedCRTHarmonic.Markov

namespace LatticeProb

variable {S U : Type*} (B : Set S) (F G : S → U → S)
  (u : ℕ → U) (x y : ℕ → S)

/-- Common updates preserve equality through the first hit. -/
theorem coupled_eq_of_le_hitTime
    (h0 : x 0 = y 0)
    (hx : ∀ n, x (n + 1) = F (x n) (u n))
    (hy : ∀ n, y (n + 1) = G (y n) (u n))
    (hFG : ∀ z, z ∉ B → ∀ v, F z v = G z v)
    (n : ℕ) (hn : (n : ℕ∞) ≤ hitTime B x) : x n = y n := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    have hlt : (n : ℕ∞) < hitTime B x :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hn
    have heq := ih hlt.le
    rw [hx, hy, ← heq, hFG (x n) (notMem_of_lt_hitTime hlt)]

/-- Common updates yield the same first hitting time. -/
theorem coupled_hitTime_eq
    (h0 : x 0 = y 0)
    (hx : ∀ n, x (n + 1) = F (x n) (u n))
    (hy : ∀ n, y (n + 1) = G (y n) (u n))
    (hFG : ∀ z, z ∉ B → ∀ v, F z v = G z v) :
    hitTime B x = hitTime B y := by
  have hp : ∀ n : ℕ, (n : ℕ∞) ≤ hitTime B x → x n = y n :=
    coupled_eq_of_le_hitTime B F G u x y h0 hx hy hFG
  have hle : hitTime B x ≤ hitTime B y := by
    apply le_hitTime_iff.mpr
    intro n hn
    by_cases h : (n : ℕ∞) ≤ hitTime B x
    · exact hitTime_le_of_mem ((hp n h).symm ▸ hn)
    · exact (lt_of_not_ge h).le
  apply le_antisymm hle
  by_cases htop : hitTime B x = ⊤
  · rw [htop]
    exact le_top
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    have hxhit : x n ∈ B := (hitTime_eq_coe_iff.mp hn.symm).1
    have heq := hp n (by rw [← hn])
    rw [← hn]
    exact hitTime_le_of_mem (heq ▸ hxhit)

end LatticeProb
