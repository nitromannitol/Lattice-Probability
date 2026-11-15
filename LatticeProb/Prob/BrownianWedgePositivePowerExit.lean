import LatticeProb.Prob.BrownianPositivePowerCutExit

/-! # Brownian exit identity on a truncated symmetric wedge -/

set_option autoImplicit false

open MeasureTheory Set InnerProductSpace
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- Every positive power profile satisfies the Brownian exit identity on the
intersection of a bounded open set and a symmetric wedge of opening less than π. -/
theorem integral_openExit_symmetricWedge_re_cpow_of_pos {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {x : Euc 2} {B : ℝ≥0 → Ω → Euc 2}
    (hB : IsBrownianSpace 2 x B P) {U : Set (Euc 2)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {θ p : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) (hp : 0 < p) :
    let J : Euc 2 → ℂ := Complex.orthonormalBasisOneI.repr.symm
    let W : Set (Euc 2) := {y | ( (J y).re, (J y).im) ∈
      CorrelatedBM.openSymmetricWedge (Real.sin (θ / 2)) (Real.cos (θ / 2))}
    ∫ ω, (J (B (openExitTime B (U ∩ W) ω).toNNReal ω) ^
      (p : ℂ)).re ∂P = (J x ^ (p : ℂ)).re := by
  dsimp only
  let J : Euc 2 → ℂ := Complex.orthonormalBasisOneI.repr.symm
  let W : Set (Euc 2) := {y | ((J y).re, (J y).im) ∈
    CorrelatedBM.openSymmetricWedge (Real.sin (θ / 2)) (Real.cos (θ / 2))}
  have hs : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hJ : Continuous J := Complex.orthonormalBasisOneI.repr.symm.continuous
  have hW : IsOpen W := by
    apply (CorrelatedBM.isOpen_openSymmetricWedge _ _).preimage
    exact (Complex.continuous_re.comp hJ).prodMk
      (Complex.continuous_im.comp hJ)
  have hWpos : ∀ y ∈ W, 0 < (J y).re := by
    intro y hy
    change |Real.cos (θ / 2) * (J y).im| < Real.sin (θ / 2) * (J y).re at hy
    exact (mul_pos_iff_of_pos_left hs).1 (lt_of_le_of_lt (abs_nonneg _) hy)
  have heq : (U ∩ W) ∩ {y | 0 < (J y).re} = U ∩ W := by
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h => h.1, fun h => ⟨h, hWpos y h.2⟩⟩
  have h := integral_openExit_positive_re_cpow hB (hU.inter hW)
    (hUb.subset inter_subset_left) hp
  change (∫ ω, (J (B (openExitTime B ((U ∩ W) ∩ {y | 0 < (J y).re}) ω).toNNReal ω) ^
    (p : ℂ)).re ∂P) = _ at h
  rw [heq] at h
  exact h

end LatticeProb
