import LatticeProb.Walk.ConstantStepGraphExit

/-! # Physical clocks for constant-step graph walks -/

set_option autoImplicit false
noncomputable section

open Set Metric MatedCRTHarmonic.Markov
open scoped NNReal

namespace LatticeProb.ConstantStepInterpolation

/-- A finite graph exit is preceded by the first inner-boundary hit in both
index and physical time. The interpolated path reaches that boundary vertex
at the corresponding knot and stays close to the embedded set before exit. -/
theorem graph_boundary_and_exit_clocks
    {V E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : SimpleGraph V) (A : Set V) (C : Set E) (x : ℕ → V) (p : V → E)
    {m : ℝ≥0} (hm : 0 < m) {N : ℕ}
    (hexit : hitTime Aᶜ x = N)
    (hstart : x 0 ∈ A)
    (hstep : ∀ n, x (n + 1) = x n ∨ G.Adj (x n) (x (n + 1)))
    (hinside : ∀ v ∈ A, p v ∈ C) {δ : ℝ}
    (hedge : ∀ j < N, dist (p (x j)) (p (x (j + 1))) ≤ δ) :
    let H := hitTime (Graph.innerBoundary G A) x
    H ≠ ⊤ ∧
      knot m H.toNat < knot m N ∧
      x H.toNat ∈ Graph.innerBoundary G A ∧
      path m (p ∘ x) (knot m H.toNat) = p (x H.toNat) ∧
      ∀ t < knot m N, infDist (path m (p ∘ x) t) C ≤ δ := by
  dsimp only
  have hlt := innerBoundary_hitTime_lt_vertex_exit G A x hstart hstep hexit
  have hfin : hitTime (Graph.innerBoundary G A) x ≠ ⊤ :=
    ne_top_of_lt (lt_of_lt_of_le hlt le_top)
  have hidx : (hitTime (Graph.innerBoundary G A) x).toNat < N := by
    have h := hlt
    rw [← coe_toNat_hitTime hfin] at h
    exact_mod_cast h
  refine ⟨hfin, knot_strictMono hm hidx, (hitTime_eq_coe_iff.mp (coe_toNat_hitTime hfin).symm).1, ?_, ?_⟩
  · exact path_knot hm (p ∘ x) _
  · intro t ht
    exact infDist_path_le_before_vertex_exit A C x p hm hexit hinside hedge ht

end LatticeProb.ConstantStepInterpolation
end
