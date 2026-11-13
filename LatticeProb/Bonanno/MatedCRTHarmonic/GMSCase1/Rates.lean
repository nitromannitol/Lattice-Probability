/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCase1.Rates at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase1.ZeroConeBridge

/-!
# Cases 1–2 of [18] Proposition 4.10 in rate form

Source: [18] : "(4.40) for `h = h₁` … follows from
(4.40) for `h = h₀` (note that here the value of `α` corresponding to `h₁` is equal to `1 − 1/p`
times the value of `α` corresponding to `h₀`). In fact, for small enough `ξ = ξ(γ) > 0`, we have
`P[z ∈ B_{ε^ξ}(0)] ≍ ε^{α/2}` … Hence, (4.40) also holds with `h` sampled from the conditional law
of `h₁` given `{z ∈ B_{ε^ξ}(0)}`."

With Hölder conjugates `p, q` (`1 − 1/p = 1/q`) and the choice `ξ = α/(4q)`
(`P[z ∈ B_{ε^ξ}(0)] = ε^{α/(2q)}`), a Case 0 rate `P[(h₀, aux) ∈ G] ≤ C ε^α` gives

`P⊗λ[(h₁, aux) ∈ G | z ∈ B_{ε^ξ}(0)] ≤ case1Moment^{1/p} · C^{1/q} ε^{α/(2q)}`

(`case1_smallRoot_rate`), and the same for local events of the Case 2 field `h₂`, with the Case 0
input on the whole-plane field or on the 0-cone (`case2_smallRoot_local_rate`,
`case2_smallRoot_local_rate_of_zeroCone`). The constant `case1Moment D hγ p` is finite for
`p < 4/γ²` and depends on neither the event nor `ε`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSCase1

open LQGMetric MatedCRTHarmonic.MatedCRT

/-- The rate bookkeeping: `(C ε^α)^{1/q} / (ε^{α/(4q)})² = C^{1/q} ε^{α/(2q)}`. -/
theorem case1_rate_div_eq {C α ε q : ℝ} (hC : 0 ≤ C) (hε0 : 0 < ε) (hq : 0 < q) :
    (ENNReal.ofReal (C * ε ^ α)) ^ (1 / q) / ENNReal.ofReal ((ε ^ (α / (4 * q))) ^ 2) =
      ENNReal.ofReal (C ^ (1 / q) * ε ^ (α / (2 * q))) := by
  have hεα : 0 ≤ ε ^ α := (Real.rpow_pos_of_pos hε0 α).le
  rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC hεα) (by positivity),
    ← ENNReal.ofReal_div_of_pos (pow_pos (Real.rpow_pos_of_pos hε0 _) 2)]
  congr 1
  rw [Real.mul_rpow hC hεα, ← Real.rpow_mul hε0.le, ← Real.rpow_natCast,
    ← Real.rpow_mul hε0.le, mul_div_assoc]
  congr 1
  rw [div_eq_iff (Real.rpow_pos_of_pos hε0 _).ne', ← Real.rpow_add hε0]
  congr 1
  field_simp
  ring

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

end Coupling

end MatedCRTHarmonic.GMSCase1
