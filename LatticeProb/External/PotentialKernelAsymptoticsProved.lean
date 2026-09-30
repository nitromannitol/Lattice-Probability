import Mathlib
import LatticeProb.External.PotentialKernelAsymptotics
import LatticeProb.Walk.GreenAsymptotic
import LatticeProb.Walk.PotentialKernel

/-!
# The lattice Green function and potential kernel asymptotics, proved

The proposition `LatticeProb.External.PotentialKernelAsymptotics d` holds in every
dimension: for `d = 2` with the potential kernel `LatticeProb.potentialKernel`, by
`LatticeProb.tendsto_potentialKernel` and `LatticeProb.exists_abs_potentialKernel_sub_log_le`,
and for `d ≥ 3` by `LatticeProb.exists_abs_srwGreenInf_sub_le`. A formalization that carries
the proposition as a hypothesis can discharge it with `potentialKernelAsymptotics_holds`.
-/

namespace LatticeProb.External

/-- **The lattice Green function and potential kernel asymptotics hold** in every
dimension `d`: the planar clause with the potential kernel `potentialKernel`, and the clause
for `d ≥ 3` with the Green function `srwGreenInf`. -/
theorem potentialKernelAsymptotics_holds (d : ℕ) : PotentialKernelAsymptotics d :=
  ⟨fun _ => ⟨potentialKernel, tendsto_potentialKernel, exists_abs_potentialKernel_sub_log_le⟩,
    fun hd => exists_abs_srwGreenInf_sub_le hd⟩

end LatticeProb.External
