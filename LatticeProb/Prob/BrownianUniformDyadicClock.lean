import LatticeProb.Prob.BrownianSelectedEnlargedClockBound
import LatticeProb.Prob.BrownianDyadicClockParameters

/-!
# Uniform bounds for selected dyadic clocks

A selector family can be fixed before the tolerance, with a uniform clock cutoff.
-/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped NNReal ENNReal

universe u

namespace BouRabeeGwynne

/-- A fixed family of measurable selectors has a clock cutoff uniform in the
scale, Brownian law, and starting point. -/
theorem exists_selector_family_uniform_active_dyadic_clock
    (n : ℕ) (hn : 1 ≤ n)
    [MeasurableSpace (Option ℕ)] [MeasurableSingletonClass (Option ℕ)]
    [MeasurableSpace (Option (LatticeProb.ParentBlock.ParentDyadicIndex n))]
    [MeasurableSingletonClass (Option (LatticeProb.ParentBlock.ParentDyadicIndex n))] :
    ∃ f : ∀ (_c : ℂ) (S : ℝ≥0), 0 < S →
        Euc 2 → Option (LatticeProb.ParentBlock.ParentDyadicIndex n),
      (∀ c S hS, Measurable (f c S hS) ∧
        (∀ x j, f c S hS x = some j →
          Complex.orthonormalBasisOneI.repr.symm x ∈ LatticeProb.ParentBlock.parentBlock c S ∧
          Complex.orthonormalBasisOneI.repr.symm x ∈
            LatticeProb.ParentBlock.closedSquare
              (LatticeProb.ParentBlock.parentDyadicCentre c S n j) (2 * (S : ℝ) / (2 : ℝ) ^ n) ∧
          ball x (2 * (S : ℝ) / (2 : ℝ) ^ n) ⊆
            Complex.orthonormalBasisOneI.repr.symm ⁻¹'
              interior (LatticeProb.ParentBlock.parentBlock
                (LatticeProb.ParentBlock.parentDyadicCentre c S n j) (2 * (S : ℝ) / (2 : ℝ) ^ n))) ∧
        (∀ x, f c S hS x = none ↔
          Complex.orthonormalBasisOneI.repr.symm x ∉ LatticeProb.ParentBlock.parentBlock c S)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ,
        ∀ (c : ℂ) (S : ℝ≥0) (hS : 0 < S)
          (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (B : ℝ≥0 → Ω → Euc 2), LatticeProb.IsBrownianSpace 2 0 B P →
        ∀ (path : Ω → BrownianPath 2), (∀ t ω, path ω t = B t ω) →
        ∀ (z : Euc 2),
          Complex.orthonormalBasisOneI.repr.symm z ∈ LatticeProb.ParentBlock.parentBlock c S →
        ∃ j₀, f c S hS z = some j₀ ∧
          P {ω | let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
              interior (LatticeProb.ParentBlock.parentBlock
                (LatticeProb.ParentBlock.parentDyadicCentre c S n j) (2 * (S : ℝ) / (2 : ℝ) ^ n))
            let clock := brownianSkeletonClock U z j₀ (fun _ => f c S hS)
            (clock K (path ω)).1 = false} ≤ ENNReal.ofReal ε := by
  classical
  obtain ⟨C, hC⟩ :=
    exists_selector_measure_active_dyadic_clock_le_of_enlargement.{u}
      (ζ := (1 / 2 : ℝ)) (by norm_num) (by norm_num) 1
  let f := fun (c : ℂ) (S : ℝ≥0) (hS : 0 < S) =>
    Classical.choose (hC n hn c S hS)
  have hf := fun (c : ℂ) (S : ℝ≥0) (hS : 0 < S) =>
    Classical.choose_spec (hC n hn c S hS)
  refine ⟨f, ?_, ?_⟩
  · intro c S hS
    exact ⟨(hf c S hS).1, (hf c S hS).2.1, (hf c S hS).2.2.1⟩
  · intro ε hε
    obtain ⟨R, hR, K, hK⟩ := exists_uniform_dyadic_clock_parameters C n hε
    refine ⟨K, ?_⟩
    intro c S hS Ω _ P _ B hB path hpath z hz
    obtain ⟨j₀, hj₀, hj⟩ := (hf c S hS).2.2.2 Ω P B hB path hpath z hz
    refine ⟨j₀, hj₀, ?_⟩
    calc
      _ ≤ ENNReal.ofReal (C * (((((2 * S / (2 : ℝ≥0) ^ n) /
          (18 * (R * S)) : ℝ≥0) : ℝ) ^ (1 : ℕ)))) := hj R hR K (hK S hS).1
      _ ≤ ENNReal.ofReal ε := by
        apply ENNReal.ofReal_le_ofReal
        simpa only [pow_one] using (hK S hS).2

end BouRabeeGwynne
