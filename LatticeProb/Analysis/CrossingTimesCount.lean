import Mathlib
import LatticeProb.Analysis.CrossingTimes

/-!
# The crossing count in terms of the crossing times

For a continuous path `f` and `ε > 0` the number `crossCount ε f u` of `ε`-crossings in `[0, u]` is
finite, and `M ≤ crossCount ε f u` holds exactly when the `M`-th crossing time `crossTime ε f M` is at
most `u`.  Consequently, if the crossing times `σ_{M₁}`, `σ_{M₂}` are finite and within `δ` of the
values `M₁ c`, `M₂ c`, with `M₁ c + δ ≤ u ≤ M₂ c - δ`, then the integer part of the count lies in
`[M₁, M₂)`.  This is the deterministic half of the law of large numbers for the crossing clock.

* `le_crossCount_iff`: `(M : ℕ∞) ≤ crossCount ε f u ↔ crossTime ε f M ≤ u`;
* `crossCount_toNat_bounds`: bounds on `(crossCount ε f u).toNat` from two good crossing times;
* `monotone_toNat_crossCount`: monotonicity of `u ↦ (crossCount ε f u).toNat` for continuous `f`.
-/

open Filter Topology
open scoped NNReal ENNReal

namespace LatticeProb

section CrossingCount

variable {E : Type*} [PseudoMetricSpace E]

/-- `M` crossings occur in `[0, u]` exactly when the `M`-th crossing time is at most `u`. -/
theorem le_crossCount_iff (ε : ℝ) (f : ℝ≥0 → E) (u : ℝ≥0) (M : ℕ) :
    (M : ℕ∞) ≤ crossCount ε f u ↔ crossTime ε f M ≤ u := by
  constructor
  · intro h
    by_contra hM
    have hM' := not_le.1 hM
    have hM0 : M ≠ 0 := by
      rintro rfl
      simp [crossTime_zero] at hM'
    have hk : ∀ k : ℕ, crossTime ε f k ≤ u → (k : ℕ∞) ≤ ((M - 1 : ℕ) : ℕ∞) := by
      intro k hk
      have hkM : k < M := by
        by_contra hkM
        exact absurd (hM'.trans_le (crossTime_mono ε f (not_lt.1 hkM))) (not_lt.2 hk)
      exact_mod_cast Nat.le_sub_one_of_lt hkM
    have h2 : crossCount ε f u ≤ ((M - 1 : ℕ) : ℕ∞) := iSup₂_le hk
    have h3 : (M : ℕ∞) ≤ ((M - 1 : ℕ) : ℕ∞) := h.trans h2
    have h4 : M ≤ M - 1 := by exact_mod_cast h3
    omega
  · intro h
    exact le_iSup₂ (f := fun (k : ℕ) (_ : crossTime ε f k ≤ u) => (k : ℕ∞)) M h

/-- If the crossing times `σ_{M₁}` and `σ_{M₂}` are finite and within `δ` of `M₁ c` and `M₂ c`, where
`M₁ c + δ ≤ u ≤ M₂ c - δ`, then `M₁ ≤ crossCount ε f u < M₂`. -/
theorem crossCount_toNat_bounds {f : ℝ≥0 → E} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) (u : ℝ≥0)
    {c δ : ℝ} {M₁ M₂ : ℕ} (h₁ : M₁ * c + δ ≤ u) (h₂ : (u : ℝ) ≤ M₂ * c - δ)
    (hg₁ : crossTime ε f M₁ ≠ ⊤ ∧ |(crossTime ε f M₁).toReal - M₁ * c| < δ)
    (hg₂ : crossTime ε f M₂ ≠ ⊤ ∧ |(crossTime ε f M₂).toReal - M₂ * c| < δ) :
    M₁ ≤ (crossCount ε f u).toNat ∧ (crossCount ε f u).toNat < M₂ := by
  have hfin : crossCount ε f u ≠ ⊤ := (crossCount_lt_top hf hε u).ne
  have hcast : ((crossCount ε f u).toNat : ℕ∞) = crossCount ε f u := ENat.natCast_toNat hfin
  constructor
  · have h1 : (crossTime ε f M₁).toReal ≤ u := by
      have := (abs_lt.1 hg₁.2).2
      linarith
    have h : crossTime ε f M₁ ≤ u := by
      have := (ENNReal.toReal_le_toReal hg₁.1 ENNReal.coe_ne_top).1 (by simpa using h1)
      exact this
    have h' := (le_crossCount_iff ε f u M₁).2 h
    rw [← hcast] at h'
    exact_mod_cast h'
  · by_contra hlt
    have hlt' := not_lt.1 hlt
    have h : (M₂ : ℕ∞) ≤ crossCount ε f u := by
      rw [← hcast]
      exact_mod_cast hlt'
    have h' := (le_crossCount_iff ε f u M₂).1 h
    have h1 : (crossTime ε f M₂).toReal ≤ u := by
      have := (ENNReal.toReal_le_toReal hg₂.1 ENNReal.coe_ne_top).2 h'
      simpa using this
    have := (abs_lt.1 hg₂.2).1
    linarith

/-- For a continuous path the integer-valued crossing count is monotone in the time. -/
theorem monotone_toNat_crossCount {f : ℝ≥0 → E} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    Monotone fun u => (crossCount ε f u).toNat := fun _ v huv =>
  ENat.toNat_le_toNat (crossCount_mono ε f huv) (crossCount_lt_top hf hε v).ne

end CrossingCount

end LatticeProb
