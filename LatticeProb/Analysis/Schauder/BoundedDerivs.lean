import LatticeProb.Analysis.Schauder.SineCoeff

/-!
# Functions with bounded derivatives on `ℝ^d`

The regularity predicate used throughout the Schauder-free proof of the Hessian bound: a function
is `C^n` and every derivative of order `≤ n` is bounded. Every integration by parts downstream
needs "bounded, continuous, with bounded continuous derivative", and those facts are read off from
this predicate, which is closed under taking a directional derivative (at the cost of one order of
regularity).
-/

namespace LatticeProb.Analysis.Schauder

noncomputable section

variable {d : ℕ}

/-- `v` is `C^n` on `ℝ^d` and its derivatives of every order `≤ n` are bounded. -/
def BoundedDerivs (n : ℕ) (v : Euc d → ℝ) : Prop :=
  ContDiff ℝ n v ∧ ∀ k ≤ n, ∃ M : ℝ, ∀ y, ‖iteratedFDeriv ℝ k v y‖ ≤ M

/-- Having bounded derivatives up to order `n` implies having them up to any lower order `m`. -/
theorem BoundedDerivs.mono {m n : ℕ} {v : Euc d → ℝ} (hmn : m ≤ n) (h : BoundedDerivs n v) :
    BoundedDerivs m v :=
  ⟨h.1.of_le (by exact_mod_cast hmn), fun k hk => h.2 k (hk.trans hmn)⟩

/-- A function with bounded derivatives is continuous. -/
theorem BoundedDerivs.continuous {n : ℕ} {v : Euc d → ℝ} (h : BoundedDerivs n v) : Continuous v :=
  h.1.continuous

/-- A function with bounded derivatives is bounded. -/
theorem BoundedDerivs.exists_abs_le {n : ℕ} {v : Euc d → ℝ} (h : BoundedDerivs n v) :
    ∃ A : ℝ, ∀ y, |v y| ≤ A := by
  obtain ⟨M, hM⟩ := h.2 0 (Nat.zero_le n)
  refine ⟨M, fun y => ?_⟩
  have := hM y
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

/-- A function with bounded derivatives up to order `n + 1` is differentiable. -/
theorem BoundedDerivs.differentiable {n : ℕ} {v : Euc d → ℝ} (h : BoundedDerivs (n + 1) v) :
    Differentiable ℝ v :=
  h.1.differentiable (by exact_mod_cast Nat.succ_ne_zero n)

/-- A function with bounded derivatives up to order `n + 1` has continuous derivative. -/
theorem BoundedDerivs.continuous_fderiv {n : ℕ} {v : Euc d → ℝ} (h : BoundedDerivs (n + 1) v) :
    Continuous (fderiv ℝ v) :=
  h.1.continuous_fderiv (by exact_mod_cast Nat.succ_ne_zero n)

/-- A function with bounded derivatives up to order `n + 1` has bounded derivative. -/
theorem BoundedDerivs.exists_norm_fderiv_le {n : ℕ} {v : Euc d → ℝ} (h : BoundedDerivs (n + 1) v) :
    ∃ B : ℝ, ∀ y, ‖fderiv ℝ v y‖ ≤ B := by
  obtain ⟨M, hM⟩ := h.2 1 (Nat.succ_le_succ (Nat.zero_le n))
  refine ⟨M, fun y => ?_⟩
  have := hM y
  rwa [norm_iteratedFDeriv_one] at this

/-- The derivative in a fixed direction of a function with bounded derivatives up to order `n + 1`
has bounded derivatives up to order `n`. -/
theorem BoundedDerivs.dirDeriv {n : ℕ} {v : Euc d → ℝ} (h : BoundedDerivs (n + 1) v) (e : Euc d) :
    BoundedDerivs n (dirDeriv e v) := by
  have hf : ContDiff ℝ n (fderiv ℝ v) := h.1.fderiv_right (by exact_mod_cast le_rfl)
  refine ⟨hf.clm_apply contDiff_const, fun k hk => ?_⟩
  obtain ⟨M, hM⟩ := h.2 (k + 1) (Nat.succ_le_succ hk)
  refine ⟨‖e‖ * M, fun y => ?_⟩
  have h1 : ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ v z e) y‖
      ≤ ‖e‖ * ‖iteratedFDeriv ℝ k (fderiv ℝ v) y‖ :=
    norm_iteratedFDeriv_clm_apply_const (hf.contDiffAt) (by exact_mod_cast hk)
  rw [norm_iteratedFDeriv_fderiv] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (hM y) (norm_nonneg e))

end

end LatticeProb.Analysis.Schauder
