/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.Section4BallExitLevyProkhorov at commit fdb5cad; selected declarations; the local imports are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.Section4BallHarmonicMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical BoundedContinuousFunction

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d) (U : Set (Euc d))

/-- Finite geometric graph closure and structural access to its boundary. -/
def HasFiniteAccessibleRegion : Prop :=
  ∃ hfin : (T.closedVertices U).Finite,
    letI : Fintype (T.closedVertices U) := hfin.fintype
    (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U)

/-- The actual exit probability, with its finite presentation chosen from
the proved structural well-posedness of the region. -/
noncomputable def spatialExitProbability (hg : T.HasFiniteAccessibleRegion U)
    (v : T.V) (hv : v ∈ T.closedVertices U) : ProbabilityMeasure (Euc d) := by
  letI : Fintype (T.closedVertices U) := hg.choose.fintype
  letI : MeasurableSpace (T.closedVertices U) := ⊤
  exact ⟨T.spatialHarmonicMeasure U hg.choose_spec ⟨v, hv⟩, inferInstance⟩

/-- The chosen presentation is the same actual spatial exit measure as any
finite presentation obtained in the convergence estimates. -/
theorem spatialExitProbability_eq (hg : T.HasFiniteAccessibleRegion U)
    (hfin : (T.closedVertices U).Finite)
    (v : T.V) (hv : v ∈ T.closedVertices U) :
    letI : Fintype (T.closedVertices U) := hfin.fintype
    letI : MeasurableSpace (T.closedVertices U) := ⊤
    ∀ ha : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U),
      (T.spatialExitProbability U hg v hv : Measure (Euc d)) =
        T.spatialHarmonicMeasure U ha ⟨v, hv⟩ := by
  intro ha
  rfl

end BouRabeeGwynne.OrthogonalTiling

