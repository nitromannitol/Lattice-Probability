/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.ScaledGridControl at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateMeasurableSpace
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VertexPath
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VerticesMeeting
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.AnnularEvent
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.CellularEmbedding

/-!
# Frozen definition: `CellularEmbedding.ScaledGridControl`

The annulus-disconnection good event at scale `R`, expressed using `AnnularEvent`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace CellularEmbedding

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-- **The annulus-disconnection event on a grid** transported to the unit-mesh
configuration at scale `R` by the cone scaling identity (the mesh-`ε` configuration of `(h_b, η^b)` is the
unit configuration scaled by `R_b⁻¹`): (1) every cell meeting `B_{ρR}(0)` has diameter `≤ R ε^q`; (2) for every grid
centre `z ∈ R (ε^χ ℤ²) ∩ B_{ρR}(0)` and radius `r ∈ R ((ε^χ ℤ) ∩ [ε^β, ρ])` with `B_{2r}(z) ⊆ B_{ρR}(0)`, from every
vertex whose cell meets `∂B_r(z)` the annular event (frozen `AnnularEvent`) has
probability `≥ p`. -/
def ScaledGridControl (R ε χ β q ρ p : ℝ) : Prop :=
  (∀ x, (H.cell x ∩ ball 0 (ρ * R)).Nonempty → diam (H.cell x) ≤ R * ε ^ q) ∧
    ∀ m n k : ℤ, (((R * ε ^ χ : ℝ) : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)) ∈ ball (0 : ℂ) (ρ * R) →
      R * ε ^ β ≤ R * ε ^ χ * k → R * ε ^ χ * k ≤ ρ * R →
      ball (((R * ε ^ χ : ℝ) : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)) (2 * (R * ε ^ χ * k)) ⊆
        ball (0 : ℂ) (ρ * R) →
      ∀ x ∈ verticesMeeting H.cell
          (sphere (((R * ε ^ χ : ℝ) : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)) (R * ε ^ χ * k)),
        ENNReal.ofReal p ≤ G.walkLaw x {ω | G.AnnularEvent H.cell
          (((R * ε ^ χ : ℝ) : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)) (R * ε ^ χ * k) (G.vertexPath ω)}

end CellularEmbedding

end MatedCRTHarmonic
