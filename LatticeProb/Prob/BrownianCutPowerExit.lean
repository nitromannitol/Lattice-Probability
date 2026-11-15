import LatticeProb.Prob.BrownianWedgePowerExit

/-! # Brownian exit from a domain cut by a half-plane -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace LatticeProb

/-- Cutting a bounded open set at a positive real-coordinate threshold gives an
actual Brownian exit identity for every real power. -/
theorem integral_openExit_cut_euclidean_re_cpow {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {x : Euc 2} {B : ℝ≥0 → Ω → Euc 2}
    (hB : IsBrownianSpace 2 x B P) {U : Set (Euc 2)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {ε p : ℝ} (hε : 0 < ε) :
    ∫ ω, ((Complex.orthonormalBasisOneI.repr.symm
      (B (openExitTime B (U ∩ {y | ε <
        (Complex.orthonormalBasisOneI.repr.symm y).re}) ω).toNNReal ω)) ^
          (p : ℂ)).re ∂P =
      ((Complex.orthonormalBasisOneI.repr.symm x) ^ (p : ℂ)).re := by
  have hc : Continuous (fun y : Euc 2 => (Complex.orthonormalBasisOneI.repr.symm y).re) :=
    Complex.continuous_re.comp Complex.orthonormalBasisOneI.repr.symm.continuous
  apply integral_openExit_euclidean_re_cpow hB
    (hU.inter (isOpen_lt continuous_const hc)) (hUb.subset inter_subset_left)
  intro y hy
  have h : ε ≤ (Complex.orthonormalBasisOneI.repr.symm y).re :=
    closure_minimal (fun z hz => show ε ≤ (Complex.orthonormalBasisOneI.repr.symm z).re from
      hz.2.le) (isClosed_le continuous_const hc) hy
  exact lt_of_lt_of_le hε h

/-- Positive reciprocal cuts exhaust the part of a set in the open right half-plane. -/
theorem iUnion_positive_re_cuts (U : Set (Euc 2)) :
    (⋃ n : ℕ, U ∩ {y | (1 : ℝ) / (n + 1) <
      (Complex.orthonormalBasisOneI.repr.symm y).re}) =
      U ∩ {y | 0 < (Complex.orthonormalBasisOneI.repr.symm y).re} := by
  ext y
  simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨n, hyU, hy⟩
    exact ⟨hyU, lt_trans (by positivity) hy⟩
  · rintro ⟨hyU, hy⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hy
    exact ⟨n, hyU, hn⟩

end LatticeProb
