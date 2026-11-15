import LatticeProb.Walk.ConstantStepInterpolation
import LatticeProb.Walk.BoundaryUnionHit

/-! # Constant-step paths before a graph exit -/

set_option autoImplicit false
noncomputable section

open Set Metric MatedCRTHarmonic.Markov
open scoped NNReal

namespace LatticeProb.ConstantStepInterpolation

/-- Before a finite vertex exit, an affine interpolation remains within the
maximum length of the edges begun before exit from the embedded vertex set. -/
theorem infDist_path_le_before_vertex_exit
    {V E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Set V) (C : Set E) (x : ℕ → V) (p : V → E)
    {m : ℝ≥0} (hm : 0 < m) {N : ℕ}
    (hexit : MatedCRTHarmonic.Markov.hitTime Aᶜ x = N)
    (hinside : ∀ v ∈ A, p v ∈ C) {δ : ℝ}
    (hedge : ∀ j < N, dist (p (x j)) (p (x (j + 1))) ≤ δ)
    {t : ℝ≥0} (ht : t < knot m N) :
    infDist (path m (p ∘ x) t) C ≤ δ := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have ht' : (m : ℝ) * t < N := by
    have h := NNReal.coe_lt_coe.mpr ht
    simp only [knot, NNReal.coe_div, NNReal.coe_natCast] at h
    simpa only [mul_comm] using (lt_div_iff₀ hm').mp h
  let j := ⌊(m : ℝ) * t⌋₊
  have hnonneg : 0 ≤ (m : ℝ) * t := mul_nonneg hm'.le t.2
  have hj : j < N := (Nat.floor_lt hnonneg).2 ht'
  have hjin : x j ∈ A := by
    have hlt : (j : ℕ∞) < MatedCRTHarmonic.Markov.hitTime Aᶜ x := by
      rw [hexit]
      exact_mod_cast hj
    simpa only [mem_compl_iff, not_not] using
      (MatedCRTHarmonic.Markov.notMem_of_lt_hitTime hlt)
  have h0 : 0 ≤ (m : ℝ) * t - j := sub_nonneg.mpr (Nat.floor_le hnonneg)
  have h1 : (m : ℝ) * t - j ≤ 1 := by
    have h := Nat.lt_floor_add_one ((m : ℝ) * t)
    dsimp [j]
    linarith
  calc
    infDist (path m (p ∘ x) t) C ≤ dist (path m (p ∘ x) t) (p (x j)) :=
      infDist_le_dist_of_mem (hinside _ hjin)
    _ ≤ dist (p (x j)) (p (x (j + 1))) := by
      change dist (AffineMap.lineMap (p (x j)) (p (x (j + 1)))
        ((m : ℝ) * t - j)) (p (x j)) ≤ _
      rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg h0]
      exact mul_le_of_le_one_left dist_nonneg h1
    _ ≤ δ := hedge j hj

/-- An adjacent graph path started inside reaches the inner boundary strictly
before its first exterior vertex. -/
theorem innerBoundary_hitTime_lt_vertex_exit
    {V : Type*} (G : SimpleGraph V) (A : Set V) (x : ℕ → V)
    (hstart : x 0 ∈ A)
    (hstep : ∀ n, x (n + 1) = x n ∨ G.Adj (x n) (x (n + 1)))
    {N : ℕ} (hexit : MatedCRTHarmonic.Markov.hitTime Aᶜ x = N) :
    MatedCRTHarmonic.Markov.hitTime (Graph.innerBoundary G A) x < (N : ℕ∞) := by
  have hn : x N ∉ A := (MatedCRTHarmonic.Markov.hitTime_eq_coe_iff.mp hexit).1
  obtain ⟨j, hj, hjmem⟩ := exists_innerBoundary_before_compl G A x hstart hstep N hn
  exact lt_of_le_of_lt (MatedCRTHarmonic.Markov.hitTime_le_of_mem hjmem) (by exact_mod_cast hj)

end LatticeProb.ConstantStepInterpolation
end
