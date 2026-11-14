import LatticeProb.Analysis.CorrelatedBMHolder
import LatticeProb.Analysis.FactorialMesh
import LatticeProb.Analysis.ShellRadiusMargins

/-!
# Factorial-scale modulus of correlated Brownian coordinates

On a fixed compact interval, every subcritical power controls increments at
factorial scales, simultaneously for both coordinates and time orientations.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- Almost surely, both orientations and both coordinates have every
subcritical factorial-scale modulus on `[-2, 2]`. -/
theorem ae_factorial_modulus {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, ∀ α : ℝ≥0, (α : ℝ) < 1 / 2 → ∀ C : ℝ, 0 < C →
      ∀ᶠ n : ℕ in atTop, ∀ (i : Fin 2) (d : ℝ), d = 1 ∨ d = -1 →
        ∀ x ∈ Icc (-2 : ℝ) 2, ∀ y ∈ Icc (-2 : ℝ) 2,
          |x - y| ≤ 1 / ((n.factorial ^ 6 : ℕ) : ℝ) →
          |lrCoord i (d * x) ω - lrCoord i (d * y) ω| ≤
            C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ (α : ℝ) := by
  filter_upwards [ae_all_iff.2 (fun i : Fin 2 => hμ.ae_forall_holderOnWith i)] with ω hω
  intro α hα C hC
  let β : ℝ≥0 := (α + 1 / 2) / 2
  have hαβ : (α : ℝ) < β := by
    dsimp [β]
    linarith
  have hβ : (β : ℝ) < 1 / 2 := by
    dsimp [β]
    linarith
  obtain ⟨K₀, hK₀⟩ := hω 0 β hβ 2
  obtain ⟨K₁, hK₁⟩ := hω 1 β hβ 2
  let K : ℝ≥0 := max K₀ K₁
  have hK (i : Fin 2) : HolderOnWith K β (fun t => lrCoord i t ω) (Icc (-2 : ℝ) 2) := by
    fin_cases i
    · exact hK₀.mono_const (le_max_left _ _)
    · exact hK₁.mono_const (le_max_right _ _)
  let δ : ℕ → ℝ := fun n => 1 / ((n.factorial ^ 6 : ℕ) : ℝ)
  have hδpos (n : ℕ) : 0 < δ n := by
    dsimp [δ]
    positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, Nat.cast_pow] using tendsto_one_div_factorial_pow 6 (by norm_num)
  have hδgt : Tendsto δ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hδlim, Eventually.of_forall hδpos⟩
  have hsmall := hδgt.eventually
    (ShellRadiusMargins.eventually_mul_rpow_lt_mul_rpow (A := (K : ℝ)) hαβ hC)
  filter_upwards [hsmall] with n hn i d hd x hx y hy hxy
  have hx' : d * x ∈ Icc (-2 : ℝ) 2 := by
    rcases hd with rfl | rfl <;> simp only [one_mul, neg_one_mul] <;> constructor <;>
      linarith [hx.1, hx.2]
  have hy' : d * y ∈ Icc (-2 : ℝ) 2 := by
    rcases hd with rfl | rfl <;> simp only [one_mul, neg_one_mul] <;> constructor <;>
      linarith [hy.1, hy.2]
  have hdist : dist (d * x) (d * y) ≤ δ n := by
    rw [Real.dist_eq, ← mul_sub, abs_mul]
    have hdabs : |d| = 1 := by rcases hd with rfl | rfl <;> norm_num
    simpa only [hdabs, one_mul, δ] using hxy
  have hbound := (hK i).dist_le_of_le hx' hy' hdist
  rw [Real.dist_eq] at hbound
  exact hbound.trans hn.le

end LatticeProb.CorrelatedBM
