import LatticeProb.Prob.BrownianBufferedParentBlockChain

/-!
# Scale-normalized bounds for Brownian parent-block chains

The probability bound depends on the ratio of the two side lengths, uniformly in their scale.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal

universe u

namespace LatticeProb.ParentBlock

private theorem ratio_identity (S s : ℝ) (hS : 0 < S) :
    2 * ((9 * S) * (s / (18 * S))) = s := by
  field_simp [ne_of_gt hS]; ring

/-- A buffered chain of small parent-block exits has a superpolynomial bound in the ratio
of its side length to the outer side length. -/
theorem measure_buffered_parentBlock_chain_ratio_superpoly {ζ : ℝ}
    (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)), IsBrownianSpace 2 0 B P →
      ∀ (z c : ℂ) (S s : ℝ≥0), 0 < S → 0 < s → s ≤ S →
      z ∈ closedSquare c S →
      let r : ℝ≥0 := s / (18 * S)
      P {ω | ∃ (τ : ℕ → ℝ≥0) (centres : ℕ → ℂ), Monotone τ ∧ τ 0 = 0 ∧
          z + Complex.orthonormalBasisOneI.repr.symm (B 0 ω) = z ∧
          (∀ n < ⌊(r : ℝ) ^ (-(2 + ζ))⌋₊,
            z + Complex.orthonormalBasisOneI.repr.symm (B (τ n) ω) ∈ closedSquare (centres n) s ∧
            z + Complex.orthonormalBasisOneI.repr.symm (B (τ (n + 1)) ω) ∉
              interior (parentBlock (centres n) s)) ∧
          (∀ n < ⌊(r : ℝ) ^ (-(2 + ζ))⌋₊,
            z + Complex.orthonormalBasisOneI.repr.symm (B (τ n) ω) ∈ parentBlock c S) ∧
          ∀ n < ⌊(r : ℝ) ^ (-(2 + ζ))⌋₊, ∀ t ∈ Icc (τ n) (τ (n + 1)),
            ‖(z + Complex.orthonormalBasisOneI.repr.symm (B t ω)) -
              (z + Complex.orthonormalBasisOneI.repr.symm (B (τ n) ω))‖ ≤ 4 * (s : ℝ)}
        ≤ ENNReal.ofReal (C * (r : ℝ) ^ p) := by
  obtain ⟨C, hC⟩ := measure_buffered_parentBlock_chain_superpoly.{u} hζ0 hζ1 p
  refine ⟨C, fun Ω _ P _ B hB z c S s hS hs hsS hz => ?_⟩
  let a : ℝ≥0 := 9 * S
  let r : ℝ≥0 := s / (18 * S)
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hsS' : (s : ℝ) ≤ S := by exact_mod_cast hsS
  have ha : 0 < a := by dsimp [a]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    apply (div_lt_one (by positivity : 0 < 18 * S)).2
    nlinarith
  have hbig : 4 * (S : ℝ) + 4 * (s : ℝ) < (a : ℝ) := by
    dsimp [a]
    nlinarith
  have hsmall : 2 * ((a : ℝ) * r) ≤ (s : ℝ) := by
    dsimp [a, r]
    exact (ratio_identity S s hS').le
  exact hC Ω P B hB z c S s (by positivity) (by positivity) hz a ha r hr hr1 hbig hsmall

end LatticeProb.ParentBlock
