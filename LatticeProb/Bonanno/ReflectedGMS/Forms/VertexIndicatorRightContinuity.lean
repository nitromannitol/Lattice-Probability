/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.VertexIndicatorRightContinuity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.UniquenessSkeleton
import Mathlib.Topology.Order.Cadlag

/-!
# Right continuity of the vertex-indicator coordinates

The existing reflected-walk regularity theorem already gives local constancy
of membership in any admissible target. This converts it to mathlib's
`IsRightContinuous`, as needed for the compact-space indicator coordinates.
Left limits are a separate obligation.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal
open ReflectedWalk ReflectedWalk.Theorem16

namespace ReflectedGMS

universe u
variable {V Ω : Type u} {X : ℝ≥0 → Ω → Option V} {ω : Ω}

theorem isRightContinuous_admissibleIndicator
    (hω : RightRegularAt X ω) {S : Set (Option V)} (hS : AdmissibleTarget S) :
    IsRightContinuous (fun t => S.indicator (fun _ => (1 : ℝ)) (X t ω)) := by
  classical
  intro t
  obtain ⟨ε, hε, heq⟩ := exists_Ico_iff_mem_of_rightRegular hω hS t
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT (lt_add_of_pos_right t hε)] with s hs
  simp only [Set.indicator, heq s ⟨hs.1.le, hs.2⟩]

theorem isRightContinuous_vertexIndicator [DecidableEq V]
    (hω : RightRegularAt X ω) (y : V) :
    IsRightContinuous (fun t => if X t ω = some y then (1 : ℝ) else 0) := by
  classical
  have hS : AdmissibleTarget ({some y} : Set (Option V)) := by
    simpa using admissibleTarget_image ({y} : Finset V)
  simpa only [Set.indicator, Set.mem_singleton_iff] using
    isRightContinuous_admissibleIndicator hω hS

variable [MeasurableSpace V]

/-- One event of full probability controls every vertex-indicator coordinate. -/
theorem reflected_vertexIndicators_ae_isRightContinuous [DecidableEq V]
    {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V} (h : IsReflectedWalk G w hmin PF) (z : V) :
    ∀ᵐ ω ∂PF.P z, ∀ y : V,
      IsRightContinuous (fun t => if PF.X t ω = some y then (1 : ℝ) else 0) := by
  filter_upwards [ae_rightRegularAt (h z).2.2.1 (h z).2.2.2.1] with ω hω y
  exact isRightContinuous_vertexIndicator hω y

end ReflectedGMS
