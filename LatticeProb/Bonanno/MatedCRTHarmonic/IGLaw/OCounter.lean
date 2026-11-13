/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.IGLaw.OCounter at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.ORotLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.WPCirc

/-!
# The dilated IG input is not a shift of the IG input in law (counterexample)

The bundle's imaginary-geometry map `Φ` reads the **full** circle-average process
`H = circleAvg hIG₀ + U : ℝ → ℂ → ℝ`, including the radius `0`, where `circleAvg h 0 w` is the junk limit of
the mollified point values: a.s. `H(0, w) = limJunk + U` at every fixed `w` (`ODiverge`). The dilated input
`igPullback γ 0 s 0 H = H(s ·, s ·)` keeps that slice, `H(0, 0)`, but its positive radii see the field at the new
scale. So the coordinate functional `junkGap K = K(0,0) − K(1,0)` is

* a.s. equal to the constant `limJunk` for every constant shift `H + k` (`junkGap_addIn`), but
* a.s. equal to `limJunk − circleAvg hIG₀ s 0` for the dilated input, which has no atoms when `s ≠ 1`
  (a centred Gaussian of variance `|log s|`, the `hasLaw_cInc_same`).

Hence `law(igPullback γ 0 s 0 H) ≠ law(H + k)` for **every** random shift `k`
(`map_igPullback_dilation_ne_shift`); in particular the input-law identity
`P.map (igPullback γ 0 s 0 ∘ H) = P.map H` that `IGLaw.map_eq_of_coordinate_change` (and the adapter
`igcFixedAffineRerootInvariant_of_coordinateChange`) would need is false for `s ≠ 1`
(`IsMatingOfTreesCoupling.map_igPullback_dilation_ne_input`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace MatedCRTHarmonic.IGLaw

open LQGMetric MatedCRTHarmonic.MatedCRT

lemma measurable_igPullback (γ : ℝ) (z₀ : ℂ) (s φ : ℝ) : Measurable (igPullback γ z₀ s φ) :=
  measurable_pi_iff.2 fun ρ => measurable_pi_iff.2 fun w => by
    show Measurable fun K : ℝ → ℂ → ℝ =>
      K (s * ρ) (z₀ + (s : ℂ) * Complex.exp (φ * Complex.I) * w) - igChi γ * φ
    have h1 : Measurable fun K : ℝ → ℂ → ℝ => K (s * ρ) := measurable_pi_apply (s * ρ)
    have h2 : Measurable fun f : ℂ → ℝ => f (z₀ + (s : ℂ) * Complex.exp (φ * Complex.I) * w) :=
      measurable_pi_apply _
    exact (h2.comp h1).sub_const _

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → Field}

end MatedCRTHarmonic.IGLaw
