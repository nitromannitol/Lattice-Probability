/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.OneSidedAlternation at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic

/-! Recurrent low and high values immediately to the right of a point produce
arbitrarily long finite increasing alternating samples. This is the deterministic
oscillation step used before applying finite-grid crossing bounds. -/

set_option autoImplicit false

open Set

namespace ReflectedGMS

variable {α : Type*} [LinearOrder α] {S : Set α} {f : α → ℝ}
  {t R : α} {a b : ℝ}

theorem exists_alternatingSamples_right
    (hR : t < R)
    (hlow : ∀ r, t < r → ∃ x ∈ S, t < x ∧ x < r ∧ f x < a)
    (hhigh : ∀ r, t < r → ∃ x ∈ S, t < x ∧ x < r ∧ b < f x)
    (n : ℕ) :
    ∃ p : ℕ → α, p (2 * n) = R ∧ StrictMonoOn p (Iic (2 * n)) ∧
      (∀ i < 2 * n, p i ∈ S ∧ t < p i) ∧
      (∀ i < n, f (p (2 * i)) < a) ∧
      (∀ i < n, b < f (p (2 * i + 1))) := by
  induction n with
  | zero =>
    refine ⟨fun _ => R, rfl, ?_, ?_, ?_, ?_⟩
    · apply strictMonoOn_Iic_of_lt_succ
      intro k hk
      omega
    · intro i hi; omega
    · intro i hi; omega
    · intro i hi; omega
  | succ n ih =>
    obtain ⟨p, hpR, hp, hmem, hlo, hhi⟩ := ih
    have htp : t < p 0 := by
      by_cases hn : n = 0
      · subst n
        simpa only [mul_zero, hpR] using hR
      · exact (hmem 0 (by omega)).2
    obtain ⟨v, hvS, htv, hvp, hfv⟩ := hhigh (p 0) htp
    obtain ⟨u, huS, htu, huv, hfu⟩ := hlow v htv
    let q : ℕ → α
      | 0 => u
      | 1 => v
      | k + 2 => p k
    refine ⟨q, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [show 2 * (n + 1) = 2 * n + 2 by omega, q] using hpR
    · apply strictMonoOn_Iic_of_lt_succ
      intro k hk
      cases k with
      | zero => exact huv
      | succ k =>
        cases k with
        | zero => exact hvp
        | succ k =>
          exact hp (by change k ≤ 2 * n; omega)
            (by change k + 1 ≤ 2 * n; omega) (by omega)
    · intro i hi
      cases i with
      | zero => exact ⟨huS, htu⟩
      | succ i =>
        cases i with
        | zero => exact ⟨hvS, htv⟩
        | succ i => exact hmem i (by omega)
    · intro i hi
      cases i with
      | zero => exact hfu
      | succ i =>
        simpa only [show 2 * (i + 1) = 2 * i + 2 by omega, q] using hlo i (by omega)
    · intro i hi
      cases i with
      | zero => exact hfv
      | succ i =>
        simpa only [show 2 * (i + 1) + 1 = (2 * i + 1) + 2 by omega, q] using
          hhi i (by omega)

end ReflectedGMS
