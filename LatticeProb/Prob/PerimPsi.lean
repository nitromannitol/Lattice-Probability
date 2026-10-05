import Mathlib
import LatticeProb.Prob.PerimStein
import LatticeProb.Prob.PerimTilt
import LatticeProb.Prob.PerimCoord
import LatticeProb.Prob.PerimRegimeI
import LatticeProb.Prob.PerimRegimeII

/-!
# The Gaussian perimeter bound for orthant layers: final glue (packet Q9b)

Glue between the Stein vocabulary (`perimN2`, `perimV`, `perimK`, module `PerimStein`) and the
tilt vocabulary (`perimTN2`, `perimTV`, `perimTK`, `perimTilt`, `perimPsi`, module `PerimTilt`),
and the two regime bounds (`PerimRegimeI`, `PerimRegimeII`).  With `H = √(2 log m)` and
`μ = Measure.pi (fun _ : Fin m => gaussianReal 0 1)`, we prove for `m ≥ 2`, `t > 0`:
```
∫ x in {x | perimN2 h x < t ^ 2}, |perimV h x| ∂μ ≤ 1000 * (1 + H) * t ≤ 1000 * (1 + H) ^ 2 * t.
```
-/

open MeasureTheory ProbabilityTheory Set Finset

namespace LatticeProb

/-! ### Bridges between the two vocabularies -/

section Bridges

variable {m : ℕ}

/-- `perimTN2 = perimN2`. -/
theorem perimP_TN2_eq (h x : Fin m → ℝ) : perimTN2 h x = perimN2 h x := rfl

/-- `perimTV = perimV`. -/
theorem perimP_TV_eq (h x : Fin m → ℝ) : perimTV h x = perimV h x := rfl

/-- `perimTK = perimK`. -/
theorem perimP_TK_eq (h x : Fin m → ℝ) : perimTK h x = perimK h x := rfl

/-- The tilt in the form used by `perim_G3`: `exp (-(1 / t ^ 2) * N2)`. -/
theorem perimP_tilt_eq (h : Fin m → ℝ) (t : ℝ) (x : Fin m → ℝ) :
    perimTilt h t x = Real.exp (-(1 / t ^ 2) * perimN2 h x) := by
  unfold perimTilt
  rw [perimP_TN2_eq]
  congr 1
  ring

/-- `perimPsi` in the Stein vocabulary. -/
theorem perimP_psi_eq (h : Fin m → ℝ) (t : ℝ) :
    perimPsi h t = ∫ x in {x : Fin m → ℝ | perimN2 h x < t ^ 2}, |perimV h x|
      ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := rfl

end Bridges

/-! ### The hypothesis (G3) of the tilt chain, from `perim_G3` -/

/-- The second-moment hypothesis `hG3` of `perim_tilt_chain`, for every `t > 0`, obtained from
`perim_G3` with `lam = 1 / t ^ 2`. -/
theorem perimP_hG3 {m : ℕ} (h : Fin m → ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ x, perimTV h x ^ 2 * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      ≤ 2 * ∫ x, perimTK h x * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
        + 2 * ∫ x, perimTN2 h x * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
        + 4 * ∫ x, (perimTN2 h x / t ^ 2) ^ 2 * perimTilt h t x
            ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  have hlam : (0 : ℝ) < 1 / t ^ 2 := by positivity
  have hG := (perim_G3 h hlam).2
  have e1 : (fun x => perimTV h x ^ 2 * perimTilt h t x)
      = fun x => perimV h x ^ 2 * Real.exp (-(1 / t ^ 2) * perimN2 h x) := by
    funext x; rw [perimP_tilt_eq, perimP_TV_eq]
  have e2 : (fun x => perimTK h x * perimTilt h t x)
      = fun x => perimK h x * Real.exp (-(1 / t ^ 2) * perimN2 h x) := by
    funext x; rw [perimP_tilt_eq, perimP_TK_eq]
  have e3 : (fun x => perimTN2 h x * perimTilt h t x)
      = fun x => perimN2 h x * Real.exp (-(1 / t ^ 2) * perimN2 h x) := by
    funext x; rw [perimP_tilt_eq, perimP_TN2_eq]
  have e4 : (fun x => (perimTN2 h x / t ^ 2) ^ 2 * perimTilt h t x)
      = fun x => (1 / t ^ 2 * perimN2 h x) ^ 2 * Real.exp (-(1 / t ^ 2) * perimN2 h x) := by
    funext x; rw [perimP_tilt_eq, perimP_TN2_eq]; congr 2; ring
  rw [e1, e2, e3, e4]
  exact hG

/-! ### The tilted chain in the Stein vocabulary -/

/-- The tilt chain with `hG3` discharged: `Psi t ≤ e² e^{-U} √(min 1 Q) √(…)`. -/
theorem perimP_chain {m : ℕ} (h : Fin m → ℝ) {t : ℝ} (ht : 0 < t) :
    perimPsi h t ≤ perimR1Rhs h t :=
  perim_tilt_chain h ht (perimP_hG3 h ht)

/-! ### The final bounds -/

/-- Regime I and Regime II combined: `Psi h t ≤ 1000 (1 + H) t` for every `t > 0`. -/
theorem perimP_psi_le {m : ℕ} (hm : 2 ≤ m) (h : Fin m → ℝ) {t : ℝ} (ht : 0 < t) :
    perimPsi h t ≤ 1000 * (1 + √(2 * Real.log m)) * t := by
  by_cases ht0 : t ≤ perimR1T0 m
  · exact perimR1_psi_le hm h ht ht0 (perimP_hG3 h ht)
  · have ht1 : 1 / (2 * (1 + √(2 * Real.log m))) ≤ t := (not_le.mp ht0).le
    have hH : 0 ≤ √(2 * Real.log m) := Real.sqrt_nonneg _
    have hD : 0 ≤ (1 + √(2 * Real.log m)) * t := by positivity
    have := perimR2_psi_le hm h ht1 (perimP_hG3 h ht)
    nlinarith

/-- **The Gaussian perimeter bound for orthant layers (sharp form).**  For `m ≥ 2`, `h : Fin m → ℝ`
and `t > 0`: `∫_{N2 < t²} |V| dμ ≤ 1000 (1 + √(2 log m)) t`. -/
theorem perimP_psi_bound_sharp {m : ℕ} (hm : 2 ≤ m) (h : Fin m → ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ x in {x : Fin m → ℝ | perimN2 h x < t ^ 2}, |perimV h x|
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      ≤ 1000 * (1 + √(2 * Real.log m)) * t := by
  rw [← perimP_psi_eq]
  exact perimP_psi_le hm h ht

/-- **The Gaussian perimeter bound for orthant layers.**  For `m ≥ 2`, `h : Fin m → ℝ` and
`t > 0`: `∫_{N2 < t²} |V| dμ ≤ 1000 (1 + √(2 log m))² t`. -/
theorem perimP_psi_bound : ∀ (m : ℕ), 2 ≤ m → ∀ (h : Fin m → ℝ) (t : ℝ), 0 < t →
    ∫ x in {x : Fin m → ℝ | perimN2 h x < t ^ 2}, |perimV h x|
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      ≤ 1000 * (1 + √(2 * Real.log m)) ^ 2 * t := by
  intro m hm h t ht
  refine (perimP_psi_bound_sharp hm h ht).trans ?_
  have hH1 : 1 ≤ √(2 * Real.log m) := perimCBigLevel_ge_one hm
  have h1 : 1 + √(2 * Real.log m) ≤ (1 + √(2 * Real.log m)) ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_right h1 ht.le
  nlinarith

end LatticeProb
