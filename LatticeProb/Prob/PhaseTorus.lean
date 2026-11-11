import Mathlib

/-!
# Phase torus: the circle, the two-dimensional torus, the doubling map and a product ergodicity statement

Definitions, and one statement (a hypothesis, not proved here):

* `PhaseCircle := AddCircle (1 : ℝ)`, the circle `ℝ / ℤ` with its Haar (Lebesgue) probability measure;
* `PhaseTorus := PhaseCircle × PhaseCircle`, the two-dimensional torus;
* `phaseTorusDouble`, the doubling map `(θ, θ') ↦ (2θ, 2θ')` on the torus;
* `phaseTorusFieldMeasure P`, the product `(Leb ⊗ Leb) ⊗ P` on `PhaseTorus × Ω`;
* `PhaseTorusDoublingProductErgodic`, the statement that the doubling map on the torus times a measure-preserving
  ergodic map is ergodic for the product of the Haar measure with the ergodic measure.

Sources for the ergodicity statement. The doubling map on the torus is mixing, hence weakly mixing, and the product of
a weakly mixing map with an ergodic map is ergodic: Walters, *An Introduction to Ergodic Theory* (GTM 79), Section 1.6
and Theorem 1.27; Sarig, *Lecture Notes on Ergodic Theory*, Proposition 1.5 and Proposition 1.9; Einsiedler and Ward,
*Ergodic Theory with a View towards Number Theory*, Theorem 2.36, (1) ⇔ (4).
-/

universe u

namespace LatticeProb.Prob

open MeasureTheory

/-- The circle `ℝ / ℤ` (period `1`), used for one coordinate of a phase. -/
abbrev PhaseCircle := AddCircle (1 : ℝ)

/-- The two-dimensional phase torus `PhaseCircle × PhaseCircle`. -/
abbrev PhaseTorus := PhaseCircle × PhaseCircle

/-- The doubling map on the phase torus, `(θ, θ') ↦ (2θ, 2θ')`. -/
def phaseTorusDouble (p : PhaseTorus) : PhaseTorus := (2 • p.1, 2 • p.2)

/-- The product of the Haar probability measure on the phase torus with a probability measure `P` on `Ω`:
`(Leb ⊗ Leb) ⊗ P` on `PhaseTorus × Ω`. -/
noncomputable abbrev phaseTorusFieldMeasure {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) :
    Measure (PhaseTorus × Ω) :=
  ((volume : Measure PhaseCircle).prod (volume : Measure PhaseCircle)).prod P

/-- Ergodicity of the doubling product: for every probability space `(Y, ν)` and every measure-preserving ergodic map
`T : Y → Y`, the map `(θ, y) ↦ (2θ, T y)` on `PhaseTorus × Y` is ergodic for `phaseTorusFieldMeasure ν`.
Sources as cited in the module header. -/
def PhaseTorusDoublingProductErgodic : Prop :=
  ∀ (Y : Type u) [MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν] (T : Y → Y),
    MeasurePreserving T ν ν → Ergodic T ν →
    Ergodic (fun p : PhaseTorus × Y => (phaseTorusDouble p.1, T p.2)) (phaseTorusFieldMeasure ν)

end LatticeProb.Prob
