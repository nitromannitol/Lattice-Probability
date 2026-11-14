/- Compatibility with Leonardo Bonanno's lean-formalizations
   (https://github.com/leobon12/lean-formalizations), source module
   BouRabeeGwynne.FinitePartitionCouplingKernel at commit fdb5cad.
   The underlying finite partition coupling is provided by LatticeProb. -/
import LatticeProb.Bonanno.BouRabeeGwynne.FinitePartitionCoupling

namespace BouRabeeGwynne

export LatticeProb (balancedProduct completeSubcoupling cappedRestrict cappedRestrict_le
  matchedCellCoupling finiteMatchedCoupling finiteMatchedCoupling_univ
  finiteMatchedCoupling_fst_le finiteMatchedCoupling_snd_le)

end BouRabeeGwynne
