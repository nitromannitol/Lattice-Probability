import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsASource
import LatticeProb.LQG.Prop210BallAdmissible

/-!
# [18] Proposition 2.10 on Euclidean balls in the source's quantifier order

Gwynne, Miller and Sheffield ([18] = GMS19, *The Tutte embedding of the mated-CRT map converges to Liouville quantum
gravity*, Proposition 2.10) bound the localized integral `∫_D f u^ε` of the cell density
`u^ε = ∑_x deg(x) diam(H_x)² / area(H_x) 1_{H_x}` of the mated-CRT map by `A ∫_D f + ε^α`, with polynomially high
probability, uniformly over the admissible pairs `(D, f)`. In the source's quantifier order
(`MatedCRTHarmonic.GMSMain.EpsAProp210Source`) the exponent `α` is chosen before the radius `ρ` of the ambient ball
`B_ρ(0)`, the threshold `A` depends on `ρ` only, and the rate `Cfail` on `ρ` and the test constant `C`.

This file specializes it to the Euclidean balls `B_s(z) ⊆ B_ρ(0)` and the test function `1`, at the test constant
`C = 8 π + 1` (`MatedCRTHarmonic.GMS4.prop210Admissible_ball_one`).

## Main result

* `MatedCRTHarmonic.GMSMain.exists_epsAProp210Bad_ball_one_source`: from `EpsAProp210Source P bm η`, there is
  `α > 0` such that for every `ρ ∈ (0, 1)` there are `A > 0` and `Cfail ≥ 0` with
  `P (EpsAProp210Bad bm η ε (B_s(z)) 1 A ε^α) ≤ Cfail ε^α` for every `ε ∈ (0, 1)` and every ball
  `B_s(z) ⊆ B_ρ(0)` with `s > 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMSMain

/-- **[18] Proposition 2.10 on balls with the test function one, source order**: from the source-order
Proposition 2.10 `EpsAProp210Source P bm η`, there is `α > 0` (chosen before the radius `ρ`) such that for every
`ρ ∈ (0, 1)` there are `A > 0` and `Cfail ≥ 0` with
`P (EpsAProp210Bad bm η ε (B_s(z)) 1 A ε^α) ≤ Cfail ε^α` for every `ε ∈ (0, 1)` and every ball `B_s(z) ⊆ B_ρ(0)`
with `s > 0`. The test constant is `C = 8 π + 1`. -/
theorem exists_epsAProp210Bad_ball_one_source {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {bm : Ω → MatedCRT.Path2} {η : Ω → C(ℝ, ℂ)} (h : EpsAProp210Source P bm η) :
    ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ A : ℝ, 0 < A ∧ ∃ Cfail : ℝ, 0 ≤ Cfail ∧
      ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ (z : ℂ) (s : ℝ), 0 < s → ball z s ⊆ ball 0 ρ →
        P (EpsAProp210Bad bm η ε (ball z s) (fun _ => 1) A (ε ^ α)) ≤ ENNReal.ofReal (Cfail * ε ^ α) := by
  obtain ⟨α, hα, β, hβ, h⟩ := h
  refine ⟨α, hα, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨A, hA, hC⟩ := h ρ hρ0 hρ1
  obtain ⟨Cfail, hCfail, hbound⟩ :=
    hC (GMS4.prop210BallConst + 1) (by linarith [GMS4.one_lt_prop210BallConst])
  exact ⟨A, hA, Cfail, hCfail, fun ε hε z s hs hsub =>
    hbound ε hε _ _ (GMS4.prop210Admissible_ball_one hε.1 hε.2 hρ0 hρ1 hβ hs hsub (lt_add_one _))⟩

end MatedCRTHarmonic.GMSMain
