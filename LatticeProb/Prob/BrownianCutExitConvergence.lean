import LatticeProb.Prob.BrownianCutPowerExit
import LatticeProb.Prob.OpenExitExhaustion

/-! # Brownian exit positions under reciprocal half-plane cuts -/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- The exit positions from reciprocal cuts converge almost surely to the exit
position from the portion of a bounded open set in the right half-plane. -/
theorem ae_tendsto_openExitPosition_positive_re_cuts
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {x : Euc 2}
    {B : ℝ≥0 → Ω → Euc 2} (hB : IsBrownianSpace 2 x B P)
    {U : Set (Euc 2)} (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => B (openExitTime B (U ∩ {y | (1 : ℝ) / (n + 1) <
        (Complex.orthonormalBasisOneI.repr.symm y).re}) ω).toNNReal ω) atTop
      (𝓝 (B (openExitTime B (U ∩ {y | 0 <
        (Complex.orthonormalBasisOneI.repr.symm y).re}) ω).toNNReal ω)) := by
  let V : ℕ → Set (Euc 2) := fun n => U ∩ {y | (1 : ℝ) / (n + 1) <
    (Complex.orthonormalBasisOneI.repr.symm y).re}
  have hc : Continuous (fun y : Euc 2 => (Complex.orthonormalBasisOneI.repr.symm y).re) :=
    Complex.continuous_re.comp Complex.orthonormalBasisOneI.repr.symm.continuous
  have hV : ∀ n, IsOpen (V n) := fun n => hU.inter (isOpen_lt continuous_const hc)
  have hm : Monotone V := by
    intro n m hnm y hy
    change y ∈ U ∧ (1 : ℝ) / (n + 1) <
      (Complex.orthonormalBasisOneI.repr.symm y).re at hy
    change y ∈ U ∧ (1 : ℝ) / (m + 1) <
      (Complex.orthonormalBasisOneI.repr.symm y).re
    exact ⟨hy.1, lt_of_le_of_lt (Nat.one_div_le_one_div hnm) hy.2⟩
  have hu : (⋃ n, V n) = U ∩ {y | 0 <
      (Complex.orthonormalBasisOneI.repr.symm y).re} := iUnion_positive_re_cuts U
  have hb : Bornology.IsBounded (⋃ n, V n) := by
    rw [hu]
    exact hUb.subset inter_subset_left
  filter_upwards [hB.cont, ae_openExitTime_ne_top (by norm_num) hB hb] with ω hcω hfω
  have h := tendsto_openExitPosition_of_iUnion hV hm hcω hfω
  simpa only [hu] using h

end LatticeProb
