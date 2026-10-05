import Mathlib
import LatticeProb.Prob.MvbeRegularClass
import LatticeProb.Prob.MvbePerimeter
import LatticeProb.Prob.GaussDensity

/-!
# The Gaussian perimeter of the rounded-orthant regular class

Packet P11 of the staged formalisation of Raic's Theorem 1.3 (arXiv:1802.06475), orthant case:
the assembly of P1 (`MvbeRegularClass`: the class `mvbeRoundedRegularClass m` of rounded orthants
`O_{h,s} = {ρ_h ≤ s}`, `s ≥ 0`, with `ρ_A = δ_A`) and P2 (`MvbePerimeter`: the linear-in-`m`
Gaussian layer bound `mvbe_perim_stdGaussian_layer_le`).

* `mvbe_stdGaussian_ac`: the standard Gaussian on `ℝ^m` is absolutely continuous w.r.t. Lebesgue
  measure (from the product density representation), hence `mvbeUnitGradAE (mvbeRho h) γ`
  (`mvbe_unitGradAE_stdGaussian`) for every corner `h`.
* `mvbe_stdGaussian_rho_band_le`: `γ{a < ρ_h ≤ b} ≤ (m/√(2π)) (b - a)` for every `a < b`
  (no sign condition on `a`: `ρ_h` takes negative values on `{x ≤ h}`).
* `mvbe_outer_layer_orthant`, `mvbe_inner_layer_orthant`: for `s ≥ 0` the two layers of
  `O_{h,s}` are the bands `{s < ρ_h ≤ s + ε}` and `{s - ε < ρ_h ≤ s}`.  The inner identity holds
  for *every* `ε > 0`, also for `ε > s` where `A^{-ε|ρ}` is the shifted orthant `{x ≤ h + (s-ε)}`:
  `ρ_h` is defined on all of `E` and `{ρ_h ≤ s - ε}` is that shifted orthant, so no translation
  argument is needed.
* `mvbe_gammaStarOf_orthant_le`: `γ*(O_{h,s} | δ) ≤ m/√(2π)` for `s ≥ 0`.
* `mvbeRoundedRegularClass_gammaStar_le`: `γ*(mvbeRoundedRegularClass m) ≤ m/√(2π)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb

section OrthantPerimeter

variable {m : ℕ}

/-- **The standard Gaussian on `ℝ^m` is absolutely continuous w.r.t. Lebesgue measure.** -/
theorem mvbe_stdGaussian_ac :
    stdGaussian (EuclideanSpace ℝ (Fin m)) ≪ (volume : Measure (EuclideanSpace ℝ (Fin m))) := by
  rw [stdGaussian_euclidean_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

variable [NeZero m]

/-- `ρ_h` is `γ`-a.e. differentiable with unit-length gradient for the standard Gaussian `γ`. -/
theorem mvbe_unitGradAE_stdGaussian (h : Fin m → ℝ) :
    mvbeUnitGradAE (mvbeRho h) (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
  mvbeUnitGradAE_of_ac h mvbe_stdGaussian_ac

/-- **Gaussian mass of a band of `ρ_h`.**  For all `a < b`,
`γ{a < ρ_h ≤ b} ≤ (m/√(2π)) (b - a)`.  Hypotheses H1-H3 of `mvbe_perim_stdGaussian_layer_le`
are `mvbeRho_lipschitz`, `mvbeRho_coordMono`, `mvbe_unitGradAE_stdGaussian`. -/
theorem mvbe_stdGaussian_rho_band_le (h : Fin m → ℝ) {a b : ℝ} (hab : a < b) :
    stdGaussian (EuclideanSpace ℝ (Fin m)) {x | a < mvbeRho h x ∧ mvbeRho h x ≤ b} ≤
      ENNReal.ofReal ((m / Real.sqrt (2 * Real.pi)) * (b - a)) :=
  mvbe_perim_stdGaussian_layer_le (mvbeRho_lipschitz h) (mvbeRho_coordMono h)
    (mvbe_unitGradAE_stdGaussian h) hab

/-- The outer layer `A^{ε|ρ} \ A` of the rounded orthant `A = O_{h,s}` (`s ≥ 0`) in the regular
class is the band `{s < ρ_h ≤ s + ε}`. -/
theorem mvbe_outer_layer_orthant (h : Fin m → ℝ) {s : ℝ} (hs : 0 ≤ s) (ε : ℝ) :
    mvbeLayer (mvbeRoundedRegularClass m).rho (mvbeOrthant h s) ε \ mvbeOrthant h s
      = {x | s < mvbeRho h x ∧ mvbeRho h x ≤ s + ε} := by
  have hl : mvbeLayer (mvbeRoundedRegularClass m).rho (mvbeOrthant h s) ε
      = mvbeOrthant h (s + ε) := mvbeLayer_orthant hs ε
  rw [hl]
  ext x
  simp only [Set.mem_sdiff, mvbe_mem_orthant, Set.mem_setOf_eq, not_le]
  exact and_comm

/-- The inner layer `A \ A^{-ε|ρ}` of the rounded orthant `A = O_{h,s}` (`s ≥ 0`) in the regular
class is the band `{s - ε < ρ_h ≤ s}`; this holds for every `ε`, in particular also for `ε > s`
(where `A^{-ε|ρ} = O_{h,s-ε}` is the shifted orthant `{x ≤ h + (s - ε)}`). -/
theorem mvbe_inner_layer_orthant (h : Fin m → ℝ) {s : ℝ} (hs : 0 ≤ s) (ε : ℝ) :
    mvbeOrthant h s \ mvbeLayer (mvbeRoundedRegularClass m).rho (mvbeOrthant h s) (-ε)
      = {x | s - ε < mvbeRho h x ∧ mvbeRho h x ≤ s} := by
  have hl : mvbeLayer (mvbeRoundedRegularClass m).rho (mvbeOrthant h s) (-ε)
      = mvbeOrthant h (s + -ε) := mvbeLayer_orthant hs (-ε)
  rw [hl]
  ext x
  simp only [Set.mem_sdiff, mvbe_mem_orthant, Set.mem_setOf_eq, not_le, ← sub_eq_add_neg]
  exact and_comm

/-- **Outer layer mass.**  For `s ≥ 0`, `ε > 0`:
`γ(A^{ε|ρ} \ A) ≤ (m/√(2π)) ε` for `A = O_{h,s}`. -/
theorem mvbe_outer_layer_stdGaussian_le (h : Fin m → ℝ) {s : ℝ} (hs : 0 ≤ s) {ε : ℝ}
    (hε : 0 < ε) :
    stdGaussian (EuclideanSpace ℝ (Fin m))
        (mvbeLayer (mvbeRoundedRegularClass m).rho (mvbeOrthant h s) ε \ mvbeOrthant h s) ≤
      ENNReal.ofReal ((m / Real.sqrt (2 * Real.pi)) * ε) := by
  rw [mvbe_outer_layer_orthant h hs]
  have := mvbe_stdGaussian_rho_band_le h (a := s) (b := s + ε) (by linarith)
  rwa [add_sub_cancel_left] at this

/-- **Inner layer mass.**  For `s ≥ 0`, `ε > 0` (any `ε`, including `ε > s`):
`γ(A \ A^{-ε|ρ}) ≤ (m/√(2π)) ε` for `A = O_{h,s}`. -/
theorem mvbe_inner_layer_stdGaussian_le (h : Fin m → ℝ) {s : ℝ} (hs : 0 ≤ s) {ε : ℝ}
    (hε : 0 < ε) :
    stdGaussian (EuclideanSpace ℝ (Fin m))
        (mvbeOrthant h s \ mvbeLayer (mvbeRoundedRegularClass m).rho (mvbeOrthant h s) (-ε)) ≤
      ENNReal.ofReal ((m / Real.sqrt (2 * Real.pi)) * ε) := by
  rw [mvbe_inner_layer_orthant h hs]
  have := mvbe_stdGaussian_rho_band_le h (a := s - ε) (b := s) (by linarith)
  rwa [sub_sub_cancel] at this

/-- **Perimeter of a single rounded orthant.**  For `s ≥ 0`,
`γ*(O_{h,s} | δ) ≤ m/√(2π)`. -/
theorem mvbe_gammaStarOf_orthant_le (h : Fin m → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    mvbeGammaStarOf (stdGaussian (EuclideanSpace ℝ (Fin m)))
        (mvbeRoundedRegularClass m).rho (mvbeOrthant h s) ≤
      ENNReal.ofReal ((m : ℝ) / Real.sqrt (2 * Real.pi)) := by
  refine iSup₂_le fun ε hε => ?_
  have hε0 : ENNReal.ofReal ε ≠ 0 := by simpa using hε
  rw [ENNReal.div_le_iff' hε0 ENNReal.ofReal_ne_top]
  have hc : 0 ≤ (m : ℝ) / Real.sqrt (2 * Real.pi) := by positivity
  have key : ENNReal.ofReal (((m : ℝ) / Real.sqrt (2 * Real.pi)) * ε)
      = ENNReal.ofReal ε * ENNReal.ofReal ((m : ℝ) / Real.sqrt (2 * Real.pi)) := by
    rw [ENNReal.ofReal_mul hc, mul_comm]
  refine max_le ?_ ?_
  · rw [← key]
    exact mvbe_outer_layer_stdGaussian_le h hs hε
  · rw [← key]
    exact mvbe_inner_layer_stdGaussian_le h hs hε

/-- **The generalised Gaussian perimeter of the rounded-orthant regular class is at most
`m/√(2π)`**: `γ*(A | ρ) ≤ m/√(2π)` for the standard Gaussian `γ` on `ℝ^m`. -/
theorem mvbeRoundedRegularClass_gammaStar_le :
    (mvbeRoundedRegularClass m).gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m))) ≤
      ENNReal.ofReal ((m : ℝ) / Real.sqrt (2 * Real.pi)) := by
  refine iSup₂_le fun A hA => ?_
  obtain ⟨h, s, hs, rfl⟩ := hA
  exact mvbe_gammaStarOf_orthant_le h hs

end OrthantPerimeter

end LatticeProb
