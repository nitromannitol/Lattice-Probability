/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.VaryingContradiction at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import Mathlib

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos

theorem exponent_lower_bound_varying_laws
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (hP : ∀ n, IsProbabilityMeasure (P n))
    (X : ∀ n, Ω n → ℝ) (hX : ∀ n, Measurable (X n))
    (ξ Q β : ℝ)
    (hlo : ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ≥0∞) ≤ P n {ω | (2 : ℝ) ^ (β * (n : ℝ)) ≤ X n ω})
    (hhi : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ =>
        P n {ω | X n ω ≤ (2 : ℝ) ^ ((ξ * Q + ε) * (n : ℝ))})
        atTop (𝓝 1)) :
    β ≤ ξ * Q := by
  by_contra hbound
  have hlt : ξ * Q < β := lt_of_not_ge hbound
  let ε : ℝ := (β - ξ * Q) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hgap : ξ * Q + ε < β := by dsimp [ε]; linarith
  have hlarge : ∀ᶠ n : ℕ in atTop,
      (3 / 4 : ℝ≥0∞) <
        P n {ω | X n ω ≤ (2 : ℝ) ^ ((ξ * Q + ε) * (n : ℝ))} :=
    (hhi ε hε).eventually (eventually_gt_nhds (show (3 / 4 : ℝ≥0∞) < 1 by
      rw [show (3 / 4 : ℝ≥0∞) = ENNReal.ofReal (3 / 4 : ℝ) by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat,
          ENNReal.ofReal_ofNat]]
      exact ENNReal.ofReal_lt_one.mpr (by norm_num)))
  obtain ⟨n, hlow, hhigh, hn⟩ :=
    (hlo.and (hlarge.and (eventually_gt_atTop (0 : ℕ)))).exists
  letI := hP n
  let A : Set (Ω n) := {ω | (2 : ℝ) ^ (β * (n : ℝ)) ≤ X n ω}
  let B : Set (Ω n) := {ω | X n ω ≤ (2 : ℝ) ^ ((ξ * Q + ε) * (n : ℝ))}
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (2 : ℝ) ^ ((ξ * Q + ε) * (n : ℝ)) <
      (2 : ℝ) ^ (β * (n : ℝ)) := by
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
    exact mul_lt_mul_of_pos_right hgap hnpos
  have hsubset : A ⊆ Bᶜ := by
    intro ω hω
    exact not_le.mpr (lt_of_lt_of_le hpow hω)
  have hB : NullMeasurableSet B (P n) := by
    have hm : MeasurableSet B := (hX n) measurableSet_Iic
    exact hm.nullMeasurableSet
  have hsum : P n Bᶜ + P n B = 1 := by
    simpa [add_comm] using measure_add_measure_compl₀ hB
  have hA : (1 / 2 : ℝ≥0∞) ≤ P n Bᶜ := hlow.trans (measure_mono hsubset)
  have htot : (1 / 2 : ℝ≥0∞) + (3 / 4 : ℝ≥0∞) ≤ 1 := by
    calc
      _ ≤ P n Bᶜ + P n B := add_le_add hA hhigh.le
      _ = 1 := hsum
  have hhalf : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have hthree : (3 / 4 : ℝ≥0∞) = ENNReal.ofReal (3 / 4 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [hhalf, hthree, ← ENNReal.ofReal_add (by norm_num) (by norm_num)] at htot
  have hr : (1 / 2 : ℝ) + 3 / 4 ≤ 1 :=
    (ENNReal.ofReal_le_one).mp htot
  linarith

theorem exponent_positive_varying_laws
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (hP : ∀ n, IsProbabilityMeasure (P n))
    (X : ∀ n, Ω n → ℝ) (hX : ∀ n, Measurable (X n))
    (ξ Q β : ℝ) (hξ : 0 < ξ) (hβ : 0 < β)
    (hlo : ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ≥0∞) ≤ P n {ω | (2 : ℝ) ^ (β * (n : ℝ)) ≤ X n ω})
    (hhi : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ =>
        P n {ω | X n ω ≤ (2 : ℝ) ^ ((ξ * Q + ε) * (n : ℝ))})
        atTop (𝓝 1)) :
    0 < Q := by
  have hbound := exponent_lower_bound_varying_laws Ω P hP X hX ξ Q β hlo hhi
  exact (pos_of_mul_pos_left (by simpa [mul_comm] using hβ.trans_le hbound) hξ.le)

end SupercriticalLQGUniqueness.B2.QPos
