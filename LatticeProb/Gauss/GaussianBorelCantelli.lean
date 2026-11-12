import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Borel-Cantelli for centred Gaussians with linearly growing variance

If `G j` is a centred real Gaussian of variance at most `v j + c`, then almost surely
`|G j| < η j` for all large `j`, whatever `η > 0`.  The proof is the Chernoff bound for
the two tails, `P(|G j| ≥ η j) ≤ 2 exp(-η² j/(2v) + c η²/(2v²))`, followed by the
Borel-Cantelli lemma for the summable geometric majorant.  No independence between the
`G j` is used.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb.GaussBC

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Two-sided Chernoff bound for a centred Gaussian.**  For `t ≥ 0` and any `a`,
`P(|G| ≥ a) ≤ 2 exp(-t a + σ t²/2)` when `G ∼ N(0, σ)`. -/
theorem measureReal_le_abs_le {G : Ω → ℝ} {σ : ℝ≥0}
    (hG : HasLaw G (gaussianReal 0 σ) P) {t a : ℝ} (ht : 0 ≤ t) :
    P.real {ω | a ≤ |G ω|} ≤ 2 * Real.exp (-t * a + (σ : ℝ) * t ^ 2 / 2) := by
  have hint : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * G ω)) P := fun s =>
    hG.integrable_comp (f := fun x : ℝ => Real.exp (s * x)) (integrable_exp_mul_gaussianReal s)
  have hupper : P.real {ω | a ≤ G ω} ≤ Real.exp (-t * a + (σ : ℝ) * t ^ 2 / 2) := by
    refine (measure_ge_le_exp_mul_mgf a ht (hint t)).trans ?_
    rw [mgf_gaussianReal hG t, ← Real.exp_add]
    apply le_of_eq
    congr 1
    ring
  have hlower : P.real {ω | G ω ≤ -a} ≤ Real.exp (-t * a + (σ : ℝ) * t ^ 2 / 2) := by
    have h := measure_le_le_exp_mul_mgf (μ := P) (X := G) (t := -t) (-a) (by linarith)
      (hint (-t))
    refine h.trans ?_
    rw [mgf_gaussianReal hG (-t), ← Real.exp_add]
    apply le_of_eq
    congr 1
    ring
  have hsub : {ω | a ≤ |G ω|} ⊆ {ω | a ≤ G ω} ∪ {ω | G ω ≤ -a} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    rcases le_abs'.mp hω with h | h
    · exact Or.inr h
    · exact Or.inl h
  calc P.real {ω | a ≤ |G ω|} ≤ P.real ({ω | a ≤ G ω} ∪ {ω | G ω ≤ -a}) :=
        measureReal_mono hsub
    _ ≤ P.real {ω | a ≤ G ω} + P.real {ω | G ω ≤ -a} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-t * a + (σ : ℝ) * t ^ 2 / 2) := by linarith

/-- **Gaussian Borel-Cantelli, fixed rate.**  Let `G j ∼ N(0, σ j)` with `σ j ≤ v j + c`
(`v > 0`, `c` any real).  Then for every `η > 0`, almost surely `|G j| < η j` for all large `j`. -/
theorem ae_eventually_abs_lt {G : ℕ → Ω → ℝ} {σ : ℕ → ℝ≥0} {v c : ℝ}
    (hv : 0 < v)
    (hG : ∀ j, HasLaw (G j) (gaussianReal 0 (σ j)) P)
    (hσ : ∀ j : ℕ, (σ j : ℝ) ≤ v * j + c) {η : ℝ} (hη : 0 < η) :
    ∀ᵐ ω ∂P, ∀ᶠ j : ℕ in atTop, |G j ω| < η * j := by
  set r : ℝ := Real.exp (-(η ^ 2 / (2 * v))) with hr
  set K : ℝ := 2 * Real.exp (c * η ^ 2 / (2 * v ^ 2)) with hK
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    have : 0 < η ^ 2 / (2 * v) := by positivity
    calc r < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hbound : ∀ j : ℕ, P {ω | η * j ≤ |G j ω|} ≤ ENNReal.ofReal (K * r ^ j) := by
    intro j
    have h := measureReal_le_abs_le (hG j) (t := η / v) (a := η * j) (by positivity)
    have hexp : -(η / v) * (η * j) + (σ j : ℝ) * (η / v) ^ 2 / 2
        ≤ -(η ^ 2 / (2 * v)) * j + c * η ^ 2 / (2 * v ^ 2) := by
      have h1 : (σ j : ℝ) * (η / v) ^ 2 / 2 ≤ (v * j + c) * (η / v) ^ 2 / 2 := by
        have := hσ j
        have h2 : 0 ≤ (η / v) ^ 2 := sq_nonneg _
        nlinarith
      have h3 : (v * j + c) * (η / v) ^ 2 / 2
          = η ^ 2 / (2 * v) * j + c * η ^ 2 / (2 * v ^ 2) := by
        field_simp
      have h4 : -(η / v) * (η * j) = -(η ^ 2 / v) * j := by ring
      have h5 : η ^ 2 / (2 * v) = η ^ 2 / v / 2 := by field_simp
      nlinarith
    have h' : P.real {ω | η * j ≤ |G j ω|} ≤ K * r ^ j := by
      refine h.trans ?_
      have : 2 * Real.exp (-(η / v) * (η * j) + (σ j : ℝ) * (η / v) ^ 2 / 2)
          ≤ 2 * Real.exp (-(η ^ 2 / (2 * v)) * j + c * η ^ 2 / (2 * v ^ 2)) := by
        gcongr
      refine this.trans (le_of_eq ?_)
      rw [hK, hr, ← Real.exp_nat_mul, Real.exp_add]
      ring_nf
    calc P {ω | η * j ≤ |G j ω|} = ENNReal.ofReal (P.real {ω | η * j ≤ |G j ω|}) := by
          rw [ofReal_measureReal]
      _ ≤ ENNReal.ofReal (K * r ^ j) := ENNReal.ofReal_le_ofReal h'
  have hsum : (∑' j : ℕ, P {ω | η * j ≤ |G j ω|}) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    have hs : Summable fun j : ℕ => K * r ^ j :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left K
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun j => mul_nonneg (by positivity) (pow_nonneg hr0 j)) hs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with j hj
  simpa using hj

/-- **Gaussian Borel-Cantelli, all rates at once.**  Under the same hypotheses, almost
surely `|G j| ≤ η j` eventually, simultaneously for every `η > 0`. -/
theorem ae_forall_eventually_abs_le {G : ℕ → Ω → ℝ} {σ : ℕ → ℝ≥0} {v c : ℝ}
    (hv : 0 < v)
    (hG : ∀ j, HasLaw (G j) (gaussianReal 0 (σ j)) P)
    (hσ : ∀ j : ℕ, (σ j : ℝ) ≤ v * j + c) :
    ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η → ∀ᶠ j : ℕ in atTop, |G j ω| ≤ η * j := by
  have h : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ᶠ j : ℕ in atTop, |G j ω| < (1 / ((n : ℝ) + 1)) * j :=
    fun n => ae_eventually_abs_lt hv hG hσ (by positivity)
  filter_upwards [ae_all_iff.mpr h] with ω hω η hη
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
  filter_upwards [hω n] with j hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  exact hj.le.trans (by nlinarith)

/-- **Exponential form.**  Under the same hypotheses, for every `γ`, almost surely for
every `η > 0`, `exp (γ G j) ≤ exp (|γ| η j)` eventually. -/
theorem ae_forall_eventually_exp_le {G : ℕ → Ω → ℝ} {σ : ℕ → ℝ≥0} {v c : ℝ}
    (hv : 0 < v)
    (hG : ∀ j, HasLaw (G j) (gaussianReal 0 (σ j)) P)
    (hσ : ∀ j : ℕ, (σ j : ℝ) ≤ v * j + c) (γ : ℝ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η → ∀ᶠ j : ℕ in atTop,
      Real.exp (γ * G j ω) ≤ Real.exp (η * j) := by
  filter_upwards [ae_forall_eventually_abs_le hv hG hσ] with ω hω η hη
  by_cases hγ : γ = 0
  · filter_upwards with j
    simp [hγ]
    positivity
  · have hγ' : 0 < |γ| := abs_pos.mpr hγ
    filter_upwards [hω (η / |γ|) (by positivity)] with j hj
    refine Real.exp_le_exp.mpr ?_
    calc γ * G j ω ≤ |γ * G j ω| := le_abs_self _
      _ = |γ| * |G j ω| := abs_mul _ _
      _ ≤ |γ| * (η / |γ| * j) := by gcongr
      _ = η * j := by field_simp

end LatticeProb.GaussBC
