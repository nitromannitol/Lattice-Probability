/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.Transfer at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalConfiguration
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop410

/-!
# The local field-law transfer in [18] Lemma 4.6

The source's (4.16) compares the pair of field restrictions to a disk under the
gamma-cone law and the whole-plane/zero-cone law. `LocalFieldLawComparison` is the
single named Cameron–Martin comparison input: the target law has a density with
an `L^p` moment. Its producer is GMSCM, not DMS Lemma A.10.
The Hölder step reuses `GMS4.withDensity_event_le_holder`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LQGMetric
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4c

/-- The two field restrictions used by [18] (4.16), on a common open disk. -/
abbrev LocalFieldPair (V : TopologicalSpace.Opens ℂ) : Type := DistOn V × DistOn V

/-- The observable `(h|_V, h^IG|_V)`. -/
def localFieldPair {Ω : Type*} (V : TopologicalSpace.Opens ℂ)
    (h hIG : Ω → DistC) (ω : Ω) : LocalFieldPair V :=
  (restrictTo V (h ω), restrictTo V (hIG ω))

theorem measurable_localFieldPair {Ω : Type*} [MeasurableSpace Ω]
    (V : TopologicalSpace.Opens ℂ) {h hIG : Ω → DistC}
    (hh : Measurable h) (hhIG : Measurable hIG) :
    Measurable (localFieldPair V h hIG) :=
  ((measurable_restrictTo V).comp hh).prodMk ((measurable_restrictTo V).comp hhIG)

/-- The local Radon–Nikodym comparison required by [18] (4.16), for the specified
pair of restricted fields under the gamma-cone and target laws. Producer: GMSCM
(Cameron–Martin), together with independence of the IG field. This does not quantify over arbitrary
unrelated `CellModel`s. -/
structure LocalFieldLawComparison {Ωγ Ω₀ : Type*}
    [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    (V : TopologicalSpace.Opens ℂ)
    (Pγ : Measure Ωγ) (P₀ : Measure Ω₀)
    (hγ hIGγ : Ωγ → DistC) (h₀ hIG₀ : Ω₀ → DistC)
    (p q : ℝ) where
  gamma_measurable : Measurable (localFieldPair V hγ hIGγ)
  target_measurable : Measurable (localFieldPair V h₀ hIG₀)
  density : LocalFieldPair V → ℝ≥0∞
  density_measurable : Measurable density
  law_eq : P₀.map (localFieldPair V h₀ hIG₀) =
    (Pγ.map (localFieldPair V hγ hIGγ)).withDensity density
  moment_finite : ∫⁻ x, density x ^ p ∂(Pγ.map (localFieldPair V hγ hIGγ)) < ⊤
  conjugate : p.HolderConjugate q

end MatedCRTHarmonic.GMS4c
