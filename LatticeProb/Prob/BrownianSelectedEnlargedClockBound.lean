import LatticeProb.Prob.BrownianParentBlockDyadicClockBound

/-!
# Selected dyadic clocks with enlarged outer blocks

A fixed dyadic selector admits an active-clock bound for every larger outer block.
-/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped NNReal ENNReal

universe u

namespace BouRabeeGwynne

/-- A measurable selector and its selected initial square satisfy the scale-uniform
active-clock estimate for every start and every enlarged outer block. -/
theorem exists_selector_measure_active_dyadic_clock_le_of_enlargement
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
          Complex.orthonormalBasisOneI.repr.symm z ∈ LatticeProb.ParentBlock.parentBlock c S →
        ∃ j₀, f z = some j₀ ∧
          ∀ (R : ℝ≥0), 3 ≤ R → ∀ K : ℕ, ⌊((((2 * S / (2 : ℝ≥0) ^ n) / (18 * (R * S)) : ℝ≥0) : ℝ) ^ (-(2 + ζ)))⌋₊ ≤ K + 1 →
          P {ω | let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
              interior (LatticeProb.ParentBlock.parentBlock
                (LatticeProb.ParentBlock.parentDyadicCentre c S n j) (2 * (S : ℝ) / (2 : ℝ) ^ n))
            let clock := brownianSkeletonClock U z j₀ (fun _ => f)
            (clock K (path ω)).1 = false} ≤
            ENNReal.ofReal (C * (((((2 * S / (2 : ℝ≥0) ^ n) / (18 * (R * S)) : ℝ≥0) : ℝ) ^ p))) := by
  obtain ⟨C, hC⟩ := measure_active_parentBlock_clock_le_without_finiteness.{u} hζ0 hζ1 p
  refine ⟨C, ?_⟩
  intro n hn _ _ _ _ c S hS
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  obtain ⟨f, hf, hsome, hnone⟩ :=
    LatticeProb.ParentBlock.exists_measurable_finite_dyadic_selector_margin c hS' n
  refine ⟨f, hf, hsome, hnone, ?_⟩
  intro Ω _ P _ B hB path hpath z hz
  have hne : f z ≠ none := by
    intro h
    exact (hnone z).1 h hz
  have hpow : (2 : ℝ≥0) ≤ 2 ^ n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [pow_succ]
    have hm : (1 : ℝ≥0) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    nlinarith
  have hs : (0 : ℝ≥0) < 2 * S / 2 ^ n := by positivity
  cases h : f z with
  | none => exact (hne h).elim
  | some j₀ =>
    refine ⟨j₀, rfl, ?_⟩
    intro R hR K hK
    have hsS : 2 * S / (2 : ℝ≥0) ^ n ≤ R * S := by
      calc
        2 * S / (2 : ℝ≥0) ^ n ≤ 3 * S := by
          apply (div_le_iff₀ (by positivity)).2
          nlinarith
        _ ≤ R * S := mul_le_mul_of_nonneg_right hR (zero_le : 0 ≤ S)
    have hR' : (3 : ℝ) ≤ R := by exact_mod_cast hR
    have hzLarge : Complex.orthonormalBasisOneI.repr.symm z ∈
        LatticeProb.ParentBlock.closedSquare c (R * S) := by
      rw [LatticeProb.ParentBlock.parentBlock_eq hS'.le c] at hz
      change |(Complex.orthonormalBasisOneI.repr.symm z).re - c.re| ≤ 3 * (S : ℝ) / 2 ∧
        |(Complex.orthonormalBasisOneI.repr.symm z).im - c.im| ≤ 3 * (S : ℝ) / 2 at hz
      change |(Complex.orthonormalBasisOneI.repr.symm z).re - c.re| ≤ (R : ℝ) * S / 2 ∧
        |(Complex.orthonormalBasisOneI.repr.symm z).im - c.im| ≤ (R : ℝ) * S / 2
      constructor <;> nlinarith [hz.1, hz.2]
    have hcontain : LatticeProb.ParentBlock.parentBlock c S ⊆
        LatticeProb.ParentBlock.parentBlock c (R * S) := by
      rw [LatticeProb.ParentBlock.parentBlock_eq hS'.le,
        LatticeProb.ParentBlock.parentBlock_eq (by positivity : (0 : ℝ) ≤ (R : ℝ) * S)]
      intro x hx
      change |x.re - c.re| ≤ 3 * (S : ℝ) / 2 ∧
        |x.im - c.im| ≤ 3 * (S : ℝ) / 2 at hx
      change |x.re - c.re| ≤ 3 * ((R : ℝ) * S) / 2 ∧
        |x.im - c.im| ≤ 3 * ((R : ℝ) * S) / 2
      constructor <;> nlinarith [hx.1, hx.2]
    apply hC Ω P B hB path hpath (LatticeProb.ParentBlock.parentDyadicCentre c S n)
      z c (R * S) (2 * S / 2 ^ n) (by positivity) hs hsS hzLarge j₀
    · simpa only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat] using
        (hsome z j₀ h).2.1
    · intro k x j hj
      have hx := hsome x j hj
      constructor
      · exact hcontain hx.1
      · simpa only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat] using hx.2.1
    · exact hK

end BouRabeeGwynne
