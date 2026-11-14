import LatticeProb.Prob.BrownianParentBlockActiveClockBound
import LatticeProb.Prob.ParentBlockDyadicFiniteSelector

/-!
# Dyadic parent-block clock estimates

The active clock estimate holds uniformly for dyadic descendants of a parent block.
-/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped NNReal ENNReal

universe u

namespace BouRabeeGwynne

/-- A scale-uniform bound for the active clock of a dyadic parent-block chain. -/
theorem measure_active_dyadic_parentBlock_clock_le
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → Euc 2), LatticeProb.IsBrownianSpace 2 0 B P →
      ∀ (path : Ω → BrownianPath 2), (∀ t ω, path ω t = B t ω) →
      ∀ (n : ℕ), 1 ≤ n →
      ∀ [MeasurableSpace (Option (LatticeProb.ParentBlock.ParentDyadicIndex n))]
        [MeasurableSingletonClass (Option (LatticeProb.ParentBlock.ParentDyadicIndex n))]
        (c : ℂ) (S : ℝ≥0), 0 < S →
      ∀ (z : Euc 2),
      Complex.orthonormalBasisOneI.repr.symm z ∈ LatticeProb.ParentBlock.closedSquare c S →
      ∀ (j₀ : LatticeProb.ParentBlock.ParentDyadicIndex n),
      Complex.orthonormalBasisOneI.repr.symm z ∈
        LatticeProb.ParentBlock.closedSquare
          (LatticeProb.ParentBlock.parentDyadicCentre c S n j₀) (2 * (S : ℝ) / (2 : ℝ) ^ n) →
      ∀ (selector : ℕ → Euc 2 → Option (LatticeProb.ParentBlock.ParentDyadicIndex n)),
      (∀ k x j, selector k x = some j →
        Complex.orthonormalBasisOneI.repr.symm x ∈ LatticeProb.ParentBlock.parentBlock c S ∧
        Complex.orthonormalBasisOneI.repr.symm x ∈
          LatticeProb.ParentBlock.closedSquare
            (LatticeProb.ParentBlock.parentDyadicCentre c S n j) (2 * (S : ℝ) / (2 : ℝ) ^ n)) →
      ∀ K : ℕ, ⌊((((2 * S / (2 : ℝ≥0) ^ n) / (18 * S) : ℝ≥0) : ℝ) ^ (-(2 + ζ)))⌋₊ ≤ K + 1 →
      P {ω | let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
          interior (LatticeProb.ParentBlock.parentBlock
            (LatticeProb.ParentBlock.parentDyadicCentre c S n j) (2 * (S : ℝ) / (2 : ℝ) ^ n))
        let clock := brownianSkeletonClock U z j₀ selector
        (clock K (path ω)).1 = false} ≤
        ENNReal.ofReal (C * (((((2 * S / (2 : ℝ≥0) ^ n) / (18 * S) : ℝ≥0) : ℝ) ^ p))) := by
  obtain ⟨C, hC⟩ := measure_active_parentBlock_clock_le_without_finiteness.{u} hζ0 hζ1 p
  refine ⟨C, ?_⟩
  intro Ω _ P _ B hB path hpath n hn _ _ c S hS z hz j₀ hz₀ selector hselector K hK
  have hpow : (2 : ℝ≥0) ≤ 2 ^ n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [pow_succ]
    have hm : (1 : ℝ≥0) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    nlinarith
  have hs : (0 : ℝ≥0) < 2 * S / 2 ^ n := by positivity
  have hsS : 2 * S / (2 : ℝ≥0) ^ n ≤ S := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  apply hC Ω P B hB path hpath (LatticeProb.ParentBlock.parentDyadicCentre c S n)
    z c S (2 * S / 2 ^ n) hS hs hsS hz j₀
  · simpa only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat] using hz₀
  · intro k x j hj
    have h := hselector k x j hj
    simpa only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat] using h
  · exact hK

end BouRabeeGwynne
