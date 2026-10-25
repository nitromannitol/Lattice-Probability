import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push

/-!
# Uniform bounds from bounds along every choice sequence

For a family antitone in a scale index, eventual bounds along every dependent choice
sequence imply a uniform eventual bound over all choices. The proof selects one
sequence along increasing bad indices and uses antitonicity to compare scales.
-/

namespace LatticeProb

/-- A bound at a fixed tolerance along every choice sequence gives a uniform eventual
bound, provided increasing the scale index decreases the family. -/
theorem exists_eventually_forall_of_forall_choices_at
    {S : ℕ → Type*} [∀ n, Nonempty (S n)]
    (p : (n : ℕ) → ℕ → S n → ℝ)
    (hanti : ∀ n (s : S n), Antitone (fun k => p n k s))
    (η : ℝ)
    (hchoices : ∀ σ : (n : ℕ) → S n,
      ∃ k N : ℕ, ∀ n, N ≤ n → p n k (σ n) < η) :
    ∃ k N : ℕ, ∀ n, N ≤ n → ∀ s : S n, p n k s < η := by
  classical
  by_contra h
  push Not at h
  choose next hnext hwitness using h
  let index : ℕ → ℕ := fun k =>
    Nat.rec (next 0 0) (fun j previous => next (j + 1) (previous + 1)) k
  have hindex : StrictMono index := by
    apply strictMono_nat_of_lt_succ
    intro k
    exact lt_of_lt_of_le (Nat.lt_succ_self (index k)) (hnext (k + 1) (index k + 1))
  have hbad : ∀ k, ∃ s : S (index k), η ≤ p (index k) k s := by
    intro k
    cases k with
    | zero => exact hwitness 0 0
    | succ k => exact hwitness (k + 1) (index k + 1)
  have hfill : ∀ n, ∃ s : S n, ∀ k, index k = n → η ≤ p n k s := by
    intro n
    by_cases hn : ∃ k, index k = n
    · obtain ⟨k, rfl⟩ := hn
      obtain ⟨s, hs⟩ := hbad k
      refine ⟨s, ?_⟩
      intro j hj
      have hjk : j = k := hindex.injective hj
      subst j
      exact hs
    · refine ⟨Classical.ofNonempty, ?_⟩
      intro k hk
      exact (hn ⟨k, hk⟩).elim
  choose σ hσ using hfill
  obtain ⟨K, N, hbound⟩ := hchoices σ
  have hindex_ge : ∀ k, k ≤ index k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k hk => exact Nat.succ_le_of_lt (lt_of_le_of_lt hk (hindex (Nat.lt_succ_self k)))
  let k := max K N
  have hNk : N ≤ index k := le_trans (le_max_right K N) (hindex_ge k)
  have hlarge : η ≤ p (index k) K (σ (index k)) :=
    le_trans (hσ (index k) k rfl) (hanti (index k) (σ (index k)) (le_max_left K N))
  exact (not_lt_of_ge hlarge) (hbound (index k) hNk)

/-- Bounds for every tolerance along every choice sequence are eventually uniform over
all choices, with the scale and tail chosen after the tolerance. -/
theorem exists_eventually_forall_of_forall_choices
    {S : ℕ → Type*} [∀ n, Nonempty (S n)]
    (p : (n : ℕ) → ℕ → S n → ℝ)
    (hanti : ∀ n (s : S n), Antitone (fun k => p n k s))
    (hchoices : ∀ σ : (n : ℕ) → S n, ∀ η : ℝ, 0 < η →
      ∃ k N : ℕ, ∀ n, N ≤ n → p n k (σ n) < η) :
    ∀ η : ℝ, 0 < η → ∃ k N : ℕ,
      ∀ n, N ≤ n → ∀ s : S n, p n k s < η := by
  intro η hη
  exact exists_eventually_forall_of_forall_choices_at p hanti η (fun σ => hchoices σ η hη)

/-- The constant zero family on the inhabited choice spaces `Unit` satisfies the
uniform conclusion by the choice-sequence theorem. -/
theorem zero_unit_exists_eventually_forall :
    ∀ η : ℝ, 0 < η → ∃ k N : ℕ,
      ∀ n, N ≤ n → ∀ s : Unit,
        (fun (_ : ℕ) (_ : ℕ) (_ : Unit) => (0 : ℝ)) n k s < η := by
  apply exists_eventually_forall_of_forall_choices
    (S := fun _ => Unit) (p := fun _ _ _ => 0)
  · intro n s k l hkl
    exact le_refl 0
  · intro σ η hη
    exact ⟨0, 0, fun _ _ => hη⟩

end LatticeProb
