/- Compatibility with the finite partition coupling kernel from Leonardo Bonanno's
   lean-formalizations, source module BouRabeeGwynne.FinitePartitionCouplingKernel
   at commit fdb5cad. The construction is provided by LatticeProb. -/
import LatticeProb.Bonanno.BouRabeeGwynne.FinitePartitionCoupling
import LatticeProb.Prob.FinitePartitionCouplingKernel

namespace BouRabeeGwynne
export LatticeProb (finitePartitionCouplingKernel finitePartitionCouplingKernel_apply
  finitePartitionCouplingKernel_spec)
end BouRabeeGwynne
