import LatticeProb.Prob.BrownianParentBlockDyadicClockBound

/-!
# Selected dyadic parent-block clock estimates

A measurable dyadic selector supplies an initial square for every start in the outer square.
-/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped NNReal ENNReal

universe u

namespace BouRabeeGwynne

/-- A measurable selector and its selected initial square satisfy the scale-uniform
active-clock estimate for every start in the outer square. -/
theorem exists_selector_measure_active_dyadic_parentBlock_clock_le
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (n : ℕ), 1 ≤ n →
      ∀ [MeasurableSpace (Option ℕ)] [MeasurableSingletonClass (Option ℕ)]
        [MeasurableSpace (Option (LatticeProb.ParentBlock.ParentDyadicIndex n))]
        [MeasurableSingletonClass (Option (LatticeProb.ParentBlock.ParentDyadicIndex n))]
        (c : ℂ) (S : ℝ≥0), 0 < S →
      ∃ f : Euc 2 → Option (LatticeProb.ParentBlock.ParentDyadicIndex n),
        Measurable f ∧
        (∀ x j, f x = some j →
          Complex.orthonormalBasisOneI.repr.symm x ∈ LatticeProb.ParentBlock.parentBlock c S ∧
          Complex.orthonormalBasisOneI.repr.symm x ∈
            LatticeProb.ParentBlock.closedSquare
              (LatticeProb.ParentBlock.parentDyadicCentre c S n j) (2 * (S : ℝ) / (2 : ℝ) ^ n) ∧
          ball x (2 * (S : ℝ) / (2 : ℝ) ^ n) ⊆
            Complex.orthonormalBasisOneI.repr.symm ⁻¹'
              interior (LatticeProb.ParentBlock.parentBlock
                (LatticeProb.ParentBlock.parentDyadicCentre c S n j) (2 * (S : ℝ) / (2 : ℝ) ^ n))) ∧
        (∀ x, f x = none ↔
          Complex.orthonormalBasisOneI.repr.symm x ∉ LatticeProb.ParentBlock.parentBlock c S) ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (B : ℝ≥0 → Ω → Euc 2), LatticeProb.IsBrownianSpace 2 0 B P →
        ∀ (path : Ω → BrownianPath 2), (∀ t ω, path ω t = B t ω) →
        ∀ (z : Euc 2),
          Complex.orthonormalBasisOneI.repr.symm z ∈ LatticeProb.ParentBlock.closedSquare c S →
        ∃ j₀, f z = some j₀ ∧
          ∀ K : ℕ, ⌊((((2 * S / (2 : ℝ≥0) ^ n) / (18 * S) : ℝ≥0) : ℝ) ^ (-(2 + ζ)))⌋₊ ≤ K + 1 →
          P {ω | let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
              interior (LatticeProb.ParentBlock.parentBlock
                (LatticeProb.ParentBlock.parentDyadicCentre c S n j) (2 * (S : ℝ) / (2 : ℝ) ^ n))
            let clock := brownianSkeletonClock U z j₀ (fun _ => f)
            (clock K (path ω)).1 = false} ≤
            ENNReal.ofReal (C * (((((2 * S / (2 : ℝ≥0) ^ n) / (18 * S) : ℝ≥0) : ℝ) ^ p))) := by
  obtain ⟨C, hC⟩ := measure_active_dyadic_parentBlock_clock_le.{u} hζ0 hζ1 p
  refine ⟨C, ?_⟩
  intro n hn _ _ _ _ c S hS
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  obtain ⟨f, hf, hsome, hnone⟩ :=
    LatticeProb.ParentBlock.exists_measurable_finite_dyadic_selector_margin c hS' n
  refine ⟨f, hf, hsome, hnone, ?_⟩
  intro Ω _ P _ B hB path hpath z hz
  have hzParent : Complex.orthonormalBasisOneI.repr.symm z ∈
      LatticeProb.ParentBlock.parentBlock c S := by
    apply interior_subset (LatticeProb.ParentBlock.ball_subset_interior_parentBlock hS'.le hz ?_)
    simpa using hS'
  have hne : f z ≠ none := by
    intro h
    exact (hnone z).1 h hzParent
  cases h : f z with
  | none => exact (hne h).elim
  | some j₀ =>
    refine ⟨j₀, rfl, ?_⟩
    intro K hK
    exact hC Ω P B hB path hpath n hn c S hS z hz j₀ (hsome z j₀ h).2.1
      (fun _ => f) (fun _ x j hj => ⟨(hsome x j hj).1, (hsome x j hj).2.1⟩) K hK

end BouRabeeGwynne
