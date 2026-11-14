import LatticeProb.Topology.KnotReparametrization

/-!
# Reparametrizing affine paths

Two paths with the same sequence of vertices and affine interpolation between
corresponding knots agree after the increasing knot reparametrization.
-/

open scoped NNReal

namespace LatticeProb.KnotReparam

/-- Affine interpolations through the same vertices agree under the knot order isomorphism. -/
theorem exists_orderIso_eq_of_affine_knots
    {E : Type*} [AddCommGroup E] [Module ℝ E] {f g : ℝ≥0 → E}
    {τ σ : ℕ → ℝ≥0} (hτ : StrictMono τ) (hσ : StrictMono σ)
    (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0)
    (hτu : ∀ b, ∃ n, b < τ n) (hσu : ∀ b, ∃ n, b < σ n)
    (p : ℕ → E)
    (hf : ∀ n t, τ n ≤ t → t < τ (n + 1) →
      f t = AffineMap.lineMap (p n) (p (n + 1))
        (((t : ℝ) - τ n) / ((τ (n + 1) : ℝ) - τ n)))
    (hg : ∀ n t, σ n ≤ t → t < σ (n + 1) →
      g t = AffineMap.lineMap (p n) (p (n + 1))
        (((t : ℝ) - σ n) / ((σ (n + 1) : ℝ) - σ n))) :
    ∃ φ : ℝ≥0 ≃o ℝ≥0, (∀ n, φ (τ n) = σ n) ∧ ∀ t, f t = g (φ t) := by
  refine ⟨knotOrderIso hτ hσ hτ0 hσ0 hτu hσu, ?_, ?_⟩
  · intro n
    exact knotMap_knot hτ hσ n
  · intro t
    change f t = g (knotMap τ σ t)
    obtain ⟨n, h1, h2⟩ := exists_knot_bracket hτ0 hτu t
    obtain ⟨hval, h3, h4⟩ := coe_knotMap_of_mem hτ hσ h1 h2
    rw [hf n t h1 h2, hg n _ h3 h4]
    congr 1
    rw [hval]
    have hne : (σ (n + 1) : ℝ) - σ n ≠ 0 := by
      have h := NNReal.coe_lt_coe.2 (hσ (Nat.lt_succ_self n))
      linarith
    field_simp
    ring

end LatticeProb.KnotReparam
