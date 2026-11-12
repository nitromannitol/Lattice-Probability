import LatticeProb.LQG.WeylScalingLogShellSummable
import LatticeProb.LQG.InternalMetricUnitSquareTail
import LatticeProb.LQG.LQGMetricXiPos
import LatticeProb.Gauss.CircleAverageGeometricShellSum

/-!
# Summability of the weighted shell diameters for `α₀ < Q`

Let `𝔇` be a γ-LQG metric with `0 < γ < 2` and `h` a whole-plane GFF. For the exponential shells
`Aₖ = {e^{-(k+1)} ≤ |x| ≤ e^{-k}}` and `α₀ < Q`, we show that almost surely
`∑ₖ e^{ξ α₀ k} · diam(Aₖ; D_h restricted to the e^{-(k+2)}-neighbourhood of Aₖ) < ∞`
(Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, Proposition 3.17, last paragraph of the proof).

We apply the tail form `IsLQGMetric.ae_tsum_expShell_internalDiam_ne_top_of_tails` with
`η = ξ (α₀ + Q) / 2` and `ε = ξ (Q - α₀) / 4`. The circle-average tails at the grid corners are the one-point tails
along geometric radii `s e^{-ρ k}` with `s = 1/32`, `ρ = 1` and `A = Q`; they are summable because `η < ξ Q`.

* `LatticeProb.LQG.IsLQGMetric.ae_tsum_expShell_internalDiam_ne_top`: the summability, given a uniform summable
  unit-square tail at every threshold `e^{ε k}`, `ε > 0`.
* `LatticeProb.LQG.IsLQGMetric.ae_tsum_expShell_internalDiam_ne_top_of_halfCrossings`: the same, given the uniform
  bound on the probability that `[0, 1]²` has no half crossings of length at most `e^{δ n}`, for some
  `δ < ξ (Q - 2) log 2` (the input of the union bound of loc. cit., Proposition 3.10).
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal Topology

namespace LatticeProb.LQG

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- `Q > 2` for `0 < γ < 2`. -/
theorem two_lt_lqgQ (hγ : 0 < γ) (hγ2 : γ < 2) : 2 < lqgQ γ := by
  have h : lqgQ γ - 2 = (2 - γ) ^ 2 / (2 * γ) := by
    unfold lqgQ
    field_simp
    ring
  have : 0 < (2 - γ) ^ 2 / (2 * γ) := div_pos (pow_pos (sub_pos.2 hγ2) 2) (by positivity)
  linarith

/-- The grid corners `tₖ p`, `p ∈ [-33, 32]²`, of mesh `tₖ = e^{-k} / 32` lie within `66 tₖ` of the origin. -/
theorem norm_expShellMesh_mul_le {p : ℤ × ℤ} (hp : p ∈ expShellSquareIndex) (k : ℕ) :
    ‖(⟨expShellMesh k * p.1, expShellMesh k * p.2⟩ : ℂ)‖ ≤ 66 * expShellMesh k := by
  have ht := (expShellMesh_pos k).le
  have hp' := mem_expShellSquareIndex.1 hp
  rw [Finset.mem_Icc, Finset.mem_Icc] at hp'
  have h1 : |(p.1 : ℝ)| ≤ 33 := abs_le.2 ⟨by exact_mod_cast hp'.1.1,
    by exact_mod_cast (show p.1 ≤ 33 by omega)⟩
  have h2 : |(p.2 : ℝ)| ≤ 33 := abs_le.2 ⟨by exact_mod_cast hp'.2.1,
    by exact_mod_cast (show p.2 ≤ 33 by omega)⟩
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  dsimp only
  rw [abs_mul, abs_mul, abs_of_nonneg ht]
  nlinarith [mul_le_mul_of_nonneg_left h1 ht, mul_le_mul_of_nonneg_left h2 ht]

/-- **Almost sure summability of the weighted shell diameters for `α₀ < Q`.** Let `𝔇` be a γ-LQG metric,
`0 < γ < 2`, `h` a whole-plane GFF and `α₀ < Q`. Suppose that for every `ε > 0` there is `ψ` with `∑ ψₖ < ∞` such that
for every whole-plane GFF the internal diameter of the closed unit square exceeds `e^{ε k}` with probability at most
`ψₖ`. Then almost surely `∑ₖ e^{ξ α₀ k} · diam(Aₖ; D_h on the e^{-(k+2)}-neighbourhood of Aₖ) < ∞`. -/
theorem IsLQGMetric.ae_tsum_expShell_internalDiam_ne_top (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2) {α₀ : ℝ} (hα : α₀ < lqgQ γ)
    (hunit : ∀ ε : ℝ, 0 < ε → ∃ ψ : ℕ → ℝ≥0∞, ∑' k, ψ k ≠ ⊤ ∧
      ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' → ∀ k : ℕ,
        P {ω | ¬ ∀ u ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
          internalMetric (𝔇 (hC' ω)) (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) u v ≤
            ENNReal.ofReal (Real.exp (ε * k))} ≤ ψ k) :
    ∀ᵐ ω ∂P, ∑' k : ℕ, ENNReal.ofReal (Real.exp (ξ * α₀ * (k : ℝ))) *
      internalDiam (𝔇 (hC ω)) (Real.exp (-((k : ℝ) + 2))) (expShell k) ≠ ∞ := by
  have hξ := h𝔇.xi_pos hγ hγ2
  have hQα : 0 < ξ * (lqgQ γ - α₀) := mul_pos hξ (by linarith)
  obtain ⟨ψ, hψ, htail⟩ := hunit (ξ * (lqgQ γ - α₀) / 4) (by positivity)
  refine h𝔇.ae_tsum_expShell_internalDiam_ne_top_of_tails hG (η := ξ * (α₀ + lqgQ γ) / 2)
    (by nlinarith) hψ htail fun p hp => ?_
  have hm : ∀ k : ℕ, expShellMesh k = 1 / 32 * Real.exp (-(1 * (k : ℝ))) := fun k => by
    unfold expShellMesh
    rw [one_mul]
    ring
  have hc : ∀ k : ℕ, ‖(⟨expShellMesh k * p.1, expShellMesh k * p.2⟩ : ℂ)‖ ≤
      66 * (1 / 32 * Real.exp (-(1 * (k : ℝ)))) := fun k => by
    rw [← hm k]
    exact norm_expShellMesh_mul_le hp k
  have h := hG.tsum_measure_geometric_circle_exp_ne_top (s := 1 / 32) (ρ := 1) (A := lqgQ γ)
    (η := ξ * (α₀ + lqgQ γ) / 2) (by norm_num) one_pos hξ (by nlinarith)
    (c := fun k => ⟨expShellMesh k * p.1, expShellMesh k * p.2⟩) hc
  simpa only [← hm] using h

/-- **Almost sure summability of the weighted shell diameters from short half crossings.** Let `𝔇` be a γ-LQG metric,
`0 < γ < 2`, `h` a whole-plane GFF, `α₀ < Q` and `δ < ξ (Q - 2) log 2`. Suppose that for every whole-plane GFF `h'`
and every `n` the probability that `[0, 1]²` has no half crossings of `D_{h'}`-length at most `e^{δ n}` is at most
`p n`, where `∑ₙ 4ⁿ p n < ∞`. Then almost surely
`∑ₖ e^{ξ α₀ k} · diam(Aₖ; D_h on the e^{-(k+2)}-neighbourhood of Aₖ) < ∞`. -/
theorem IsLQGMetric.ae_tsum_expShell_internalDiam_ne_top_of_halfCrossings (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2) {α₀ : ℝ} (hα : α₀ < lqgQ γ) {δ : ℝ}
    (hδ : δ < ξ * (lqgQ γ - 2) * Real.log 2) {p : ℕ → ℝ≥0∞}
    (huniv : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hp : ∑' n, 4 ^ n * p n ≠ ⊤) :
    ∀ᵐ ω ∂P, ∑' k : ℕ, ENNReal.ofReal (Real.exp (ξ * α₀ * (k : ℝ))) *
      internalDiam (𝔇 (hC ω)) (Real.exp (-((k : ℝ) + 2))) (expShell k) ≠ ∞ := by
  have hξ := h𝔇.xi_pos hγ hγ2
  have hc : 0 < ξ * (lqgQ γ - 2) * Real.log 2 :=
    mul_pos (mul_pos hξ (sub_pos.2 (two_lt_lqgQ hγ hγ2))) (Real.log_pos one_lt_two)
  set c := ξ * (lqgQ γ - 2) * Real.log 2 with hcdef
  set δ' := max δ (c / 3) with hδ'
  have hδ'c : δ' < c := max_lt hδ (by linarith)
  have hδδ' : δ ≤ δ' := le_max_left _ _
  have hδ'0 : 0 < δ' := lt_of_lt_of_le (by linarith) (le_max_right δ (c / 3))
  -- the half-crossing input at the positive level `δ'`
  have huniv' : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ' * n)))} ≤
        p n := by
    intro hC' hcirc' hG' n
    refine le_trans (measure_mono ?_) (huniv hC' hcirc' hG' n)
    intro ω hω
    exact fun h => hω (HasShortHalfCrossings.mono h (ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hδδ' (Nat.cast_nonneg n)))))
  refine h𝔇.ae_tsum_expShell_internalDiam_ne_top hG hγ hγ2 hα fun ε hε => ?_
  exact h𝔇.exists_unitSquare_internalMetric_tail hG hξ (θ := (δ' + c) / 2) (by linarith) (by linarith) hδ'0 hε
    huniv' hp

end LatticeProb.LQG
