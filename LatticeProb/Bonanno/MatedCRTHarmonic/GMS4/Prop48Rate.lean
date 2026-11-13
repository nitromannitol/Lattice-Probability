/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48Rate at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48SecondMoment
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48NearMeasure

/-!
# A common exponent for Proposition 4.8

The spatial near contribution has exponent `2q-10ζ` in [18] (4.34); the
far contribution has exponent `ζ` in (4.37). Both parameters are chosen from
`γ` before the test radius `ρ`, so their minimum is a radius-independent
positive exponent.
-/

set_option autoImplicit false
noncomputable section

namespace MatedCRTHarmonic.GMS4

/-- The common Proposition 4.8 exponent, selected before `ρ`. -/
def prop48RateAlpha (q ζ : ℝ) : ℝ := min (2 * q - 10 * ζ) ζ

theorem prop48RateAlpha_pos {q ζ : ℝ}
    (hq : 0 < q) (hζ : 0 < ζ) (hζq : ζ < q / 100) :
    0 < prop48RateAlpha q ζ := by
  unfold prop48RateAlpha
  apply lt_min
  · linarith
  · exact hζ

end MatedCRTHarmonic.GMS4

