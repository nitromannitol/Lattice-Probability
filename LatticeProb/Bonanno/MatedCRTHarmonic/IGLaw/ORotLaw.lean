/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.IGLaw.ORotLaw at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OBase
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OInterfaces
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgAffine
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OProcLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.CircleAvgCovariance

/-!
# Rotation invariance of the whole-plane space-filling curve and the Lemma 4.9 identity

From the bundle's imaginary-geometry map `Φ` (`igMap`: `ηL = Φ(H)` a.s. and the coordinate change
`Φ(igPullback γ z₀ s φ H) = affineReroot z₀ s φ ηL` a.s.), where `H = circleAvg hIG₀ + U` is the full circle-average
process of the IG field, we prove:

* `map_rotIn_igInput`: the law of `H` is invariant under rotating the centres, `H ↦ H(·, e^{iθ}·)`, on the
  whole product space `ℝ → ℂ → ℝ`, including the junk radius `0` (where both sides are a.s. `limJunk + U`,
  `ODiverge`) and negative radii (`circleAvg_neg_radius`); positive radii userotation
  covariance `rotCircleAvgCovariance_holds`;
* `map_rotCurve_of_cc` / `IsMatingOfTreesCoupling.map_rotCurve_ηL`: `law(e^{iθ} ηL) = law(ηL)`, and
  `IsMatingOfTreesCoupling.map_affineReroot_rotation_ηL`: `law(affineReroot 0 1 φ ηL) = law(ηL)`;
* `ae_lemma49_of_cc` / `IsMatingOfTreesCoupling.exists_igMap_package`: the Lemma 4.9 identity of the imaginary-geometry covariance statement,
  `Φ(H + c) = e^{ic/χ} · Φ(H(·, e^{ic/χ}·))` a.s. for every real `c` (the coordinate clause transferred to the
  rotated input, whose law is that of `H`), together with the factorization, the integer-period invariance and
  the rotation rule for the same `Φ`.

The generic results take `Φ` and the two `igMap` clauses as hypotheses, so they apply verbatim to the mating-of-trees bundle (only `FirstHit`'s import changes).

Dilations and translations are **not** covered: for `(s, z₀) ≠ (1, 0)` the transformed input
`igPullback γ z₀ s φ H` has a law mutually singular to that of every constant shift of `H` (its radius-`0` slice
is shifted by `−circleAvg hIG₀ s z₀` relative to the positive radii; see `OCounter`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace MatedCRTHarmonic.IGLaw

open LQGMetric MatedCRTHarmonic.MatedCRT

/-! ## Operations on circle-average processes -/

/-- Rotating the centres of a circle-average process: `K ↦ K(·, e^{iθ}·)`. -/
def rotIn (θ : ℝ) (K : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun ρ w => K ρ (Complex.exp (θ * Complex.I) * w)

/-- Adding a constant to a circle-average process. -/
def addIn (c : ℝ) (K : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ := fun ρ w => K ρ w + c

lemma measurable_addIn (c : ℝ) : Measurable (addIn c) :=
  measurable_pi_iff.2 fun ρ => measurable_pi_iff.2 fun w => by
    show Measurable fun K : ℝ → ℂ → ℝ => K ρ w + c
    have h1 : Measurable fun K : ℝ → ℂ → ℝ => K ρ := measurable_pi_apply ρ
    have h2 : Measurable fun f : ℂ → ℝ => f w := measurable_pi_apply w
    exact (h2.comp h1).add_const c

lemma igPullback_rot (γ θ : ℝ) (K : ℝ → ℂ → ℝ) :
    igPullback γ 0 1 θ K = addIn (-(igChi γ * θ)) (rotIn θ K) := by
  funext ρ w
  simp [igPullback, addIn, rotIn, sub_eq_add_neg]

lemma igCircleAvgInput_add (x : Field) (u c : ℝ) :
    igCircleAvgInput (x, u + c) = addIn c (igCircleAvgInput (x, u)) := by
  funext ρ w
  simp only [igCircleAvgInput, addIn]
  ring

lemma igPullback_period_neg (γ : ℝ) (K : ℝ → ℂ → ℝ) (k : ℤ) :
    igPullback γ 0 1 (2 * Real.pi * ((-k : ℤ) : ℝ)) K =
      addIn (2 * Real.pi * igChi γ * k) K := by
  rw [igPullback_full_turn]
  funext ρ w
  simp only [addIn]
  push_cast
  ring

/-! ## Rotation invariance of the law of the IG input process -/

/-! ## The generic core: any measurable `Φ` with the two `igMap` clauses -/

section Core

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → Field} {U : Ω → ℝ} {ηL : Ω → C(ℝ, ℂ)} {Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ)}

omit [IsProbabilityMeasure P] in
/-- Integer-period invariance of `Φ` on the actual input, from the coordinate clause at full turns. -/
theorem ae_periodic_of_cc
    (hroot : ∀ᵐ ω ∂P, ηL ω = Φ (igCircleAvgInput (h ω, U ω)))
    (hcc : ∀ (z₀ : ℂ) (s φ : ℝ), 0 < s → ∀ᵐ ω ∂P,
      Φ (igPullback γ z₀ s φ (igCircleAvgInput (h ω, U ω))) = affineReroot z₀ s φ (ηL ω))
    (hτ : ∀ᵐ ω ∂P, firstHit (ηL ω) 0 = 0) :
    ∀ᵐ ω ∂P, ∀ k : ℤ, Φ (addIn (2 * Real.pi * igChi γ * k) (igCircleAvgInput (h ω, U ω))) =
      Φ (igCircleAvgInput (h ω, U ω)) := by
  refine ae_all_iff.2 fun k => ?_
  filter_upwards [hroot, hcc 0 1 (2 * Real.pi * ((-k : ℤ) : ℝ)) one_pos, hτ] with ω hr hc ht
  rw [igPullback_period_neg, affineReroot_zero_one_of_firstHit _ _ ht,
    show -(2 * Real.pi * ((-k : ℤ) : ℝ)) = 2 * Real.pi * (k : ℝ) by push_cast; ring,
    rotCurve_two_pi_int] at hc
  rw [hc, hr]

omit [IsProbabilityMeasure P] in
/-- The rotation rule for the actual input: `Φ(H(·, e^{iθ}·) − χθ) = e^{−iθ} ηL` a.s. -/
theorem ae_rotation_rule_of_cc
    (hcc : ∀ (z₀ : ℂ) (s φ : ℝ), 0 < s → ∀ᵐ ω ∂P,
      Φ (igPullback γ z₀ s φ (igCircleAvgInput (h ω, U ω))) = affineReroot z₀ s φ (ηL ω))
    (hτ : ∀ᵐ ω ∂P, firstHit (ηL ω) 0 = 0) (θ : ℝ) :
    ∀ᵐ ω ∂P, Φ (addIn (-(igChi γ * θ)) (rotIn θ (igCircleAvgInput (h ω, U ω)))) =
      rotCurve (-θ) (ηL ω) := by
  filter_upwards [hcc 0 1 θ one_pos, hτ] with ω hc ht
  rw [igPullback_rot, affineReroot_zero_one_of_firstHit _ _ ht] at hc
  exact hc

/-- The measurable set of inputs (as pairs of a field and a scalar) on which `Φ` is invariant under every
integer period. -/
lemma measurableSet_periodic (hΦ : Measurable Φ) (r : ℝ) :
    MeasurableSet {x : Field × ℝ | ∀ k : ℤ, Φ (addIn (r * k) (igCircleAvgInput x)) =
      Φ (igCircleAvgInput x)} := by
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun k => measurableSet_eq_curve
    (hΦ.comp ((measurable_addIn _).comp measurable_igCircleAvgInput))
    (hΦ.comp measurable_igCircleAvgInput)

end Core

/-! ## The bundle statements -/

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
  {B B' B₀ B₀' : NNReal → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}

end Bundle

end MatedCRTHarmonic.IGLaw
