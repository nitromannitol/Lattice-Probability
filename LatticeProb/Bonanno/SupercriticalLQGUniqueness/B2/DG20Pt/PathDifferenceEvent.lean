/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PathDifferenceEvent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.CouplingGluing
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffLaw

 


set_option autoImplicit false
noncomputable section

open Set Topology

namespace SupercriticalLQGUniqueness.B2.DG20Pt

def dg20PathDiffEvent (K : Set ℂ) (M : ℝ) : Set (C(ℂ, ℝ) × C(ℂ, ℝ)) :=
  {p | ∃ z ∈ K, M < |p.1 z - p.2 z|}

theorem dg20PathDiffEvent_isOpen (K : Set ℂ) (M : ℝ) :
    IsOpen (dg20PathDiffEvent K M) := by
  have he : dg20PathDiffEvent K M =
      ⋃ z ∈ K, {p : C(ℂ, ℝ) × C(ℂ, ℝ) | M < |p.1 z - p.2 z|} := by
    ext p
    simp [dg20PathDiffEvent]
  rw [he]
  refine isOpen_iUnion (fun z => isOpen_iUnion (fun _ => ?_))
  have hcont : Continuous (fun p : C(ℂ, ℝ) × C(ℂ, ℝ) => |p.1 z - p.2 z|) :=
    ((continuous_eval_const z).comp continuous_fst |>.sub
      ((continuous_eval_const z).comp continuous_snd)).abs
  exact isOpen_lt continuous_const hcont

end SupercriticalLQGUniqueness.B2.DG20Pt
