/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48Statement at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop210
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.ProducersCellCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop410Rooting
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.SmallRootMass
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Consumers

/-!
# Uniform fixed-test statement for [18] Proposition 4.8

Source: Gwynne--Miller--Sheffield, *Harmonic functions on mated-CRT maps*, Proposition 4.8.

The proof of Proposition 4.8 first treats the whole-plane GFF whose circle average on the unit
circle is zero. The 0-quantum-cone branch is obtained from equality in law of restrictions to the
unit disk. The gamma-quantum-cone conclusion belongs to Proposition 4.10. The rooted-law wrapper
below is a legacy interface consumed by the existing Case 0 adapter; its carrier has no IG phase
or area-time curve. `Prop48CanonicalStatement` supplies the coupling-based realization interface.

The far input is the corrected unrestricted contribution. There is no global-event indicator
inside the exterior conditional expectation, since that event is not exterior measurable (the corrected argument
section 3.13(c7)). The theorem composes the named inputs through the checked
`GMSAWholePlaneProp48Base.bad_probability_le` estimate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4

/-- Pointwise `L-infinity` norm of a test function on `B_rho(0)`. -/
def prop48TestSupNorm (rho : ℝ) (f : ℂ → ℝ) : ℝ :=
  sSup (insert 0 ((fun z => |f z|) '' Metric.ball 0 rho))

theorem prop48TestSupNorm_bddAbove {rho : ℝ} {f : ℂ → ℝ}
    (hbounded : ∃ B : ℝ, ∀ z ∈ Metric.ball 0 rho, |f z| ≤ B) :
    BddAbove (insert 0 ((fun z => |f z|) '' Metric.ball 0 rho)) := by
  rcases hbounded with ⟨B, hB⟩
  refine ⟨max 0 B, ?_⟩
  intro x hx
  rcases Set.mem_insert_iff.mp hx with hx | hx
  · rw [hx]
    exact le_max_left _ _
  · rcases hx with ⟨z, hz, rfl⟩
    exact (hB z hz).trans (le_max_right _ _)

theorem abs_le_prop48TestSupNorm {rho : ℝ} {f : ℂ → ℝ}
    (hbounded : ∃ B : ℝ, ∀ z ∈ Metric.ball 0 rho, |f z| ≤ B)
    {z : ℂ} (hz : z ∈ Metric.ball 0 rho) :
    |f z| ≤ prop48TestSupNorm rho f := by
  apply le_csSup (prop48TestSupNorm_bddAbove hbounded)
  exact Set.mem_insert_iff.mpr (Or.inr ⟨z, hz, rfl⟩)

/-- Admissibility of a fixed `(D,f)` in [18] Proposition 4.8. -/
structure Prop48TestPairAdmissible (rho : ℝ) (domain : Set ℂ) (f : ℂ → ℝ) : Prop where
  domain_borel : MeasurableSet domain
  domain_subset_ball : domain ⊆ Metric.ball 0 rho
  test_measurable : Measurable (fun z : Metric.ball (0 : ℂ) rho => f z)
  test_nonnegative : ∀ z ∈ Metric.ball 0 rho, 0 ≤ f z
  test_bounded : ∃ B : ℝ, ∀ z ∈ Metric.ball 0 rho, |f z| ≤ B

end MatedCRTHarmonic.GMS4

