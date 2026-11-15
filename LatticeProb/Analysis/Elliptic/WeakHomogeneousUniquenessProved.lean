import LatticeProb.Analysis.Elliptic.H10Friedrichs
import LatticeProb.Analysis.Elliptic.WeakHomogeneousEnergy

/-!
# Uniqueness of homogeneous weak solutions

The energy identity and the Friedrichs inequality imply uniqueness for the
zero-boundary homogeneous weak equation, including at zero mass.
-/

namespace LatticeProb.External

open LatticeProb.Elliptic.WeakDirichlet

/-- The homogeneous zero-boundary weak equation has only the zero solution. -/
theorem gilbargTrudingerWeakHomogeneousUniqueness_holds :
    GilbargTrudingerWeakHomogeneousUniqueness := by
  intro d hd U _ _ hU a₀ μ ha₀ hμ u hu
  have hg := hu.grad_eq_zero_of_homogeneous hμ ha₀ u
  apply PiLp.ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact u.coord_zero_eq_zero_of_grad_eq_zero hd hU hg
  · exact hg i

end LatticeProb.External
