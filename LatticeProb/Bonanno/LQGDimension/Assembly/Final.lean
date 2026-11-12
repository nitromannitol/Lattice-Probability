/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Assembly.Final at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Assembly.Main
import LatticeProb.Bonanno.LQGDimension.Assembly.AStarProved
import LatticeProb.Bonanno.LQGDimension.LFPP.UpperAssembly
import LatticeProb.Bonanno.LQGDimension.LFPP.LowerAssembly
import LatticeProb.Bonanno.LQGDimension.LFPP.SegCombLaw
import LatticeProb.Bonanno.LQGDimension.LFPP.Oscillation
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordMeanTransfer
import LatticeProb.Bonanno.LQGDimension.LFPP.PathTree
import LatticeProb.Bonanno.LQGDimension.LFPP.TreeInequality
import LatticeProb.Bonanno.LQGDimension.LFPP.Records
import LatticeProb.Bonanno.LQGDimension.LFPP.ChainUnion
import LatticeProb.Bonanno.LQGDimension.LFPP.ZLimit
import LatticeProb.Bonanno.LQGDimension.LFPP.ExponentFromProb
import LatticeProb.Bonanno.LQGDimension.LFPP.Coupling
import LatticeProb.Bonanno.LQGDimension.LFPP.PolygonRiemann
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordMeanLimit
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordVariance
import LatticeProb.Bonanno.LQGDimension.LFPP.ConstrainedCov
import LatticeProb.Bonanno.LQGDimension.LFPP.TwoScale
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordMeanCrude
import LatticeProb.Bonanno.LQGDimension.LFPP.BlockConstruction
import LatticeProb.Bonanno.LQGDimension.LFPP.Conversions

/-!
# Final assembly of Theorem 1.1

Theorem 1.1 is reduced here to the Proposition 1.2 nodes that are not yet proved.  Every
other node is supplied by its proof.
-/

namespace LQGDimension

open Blueprint

/-- Proposition 1.2, upper bound (1.7), from the three remaining Section 4 mean/variance nodes. -/
theorem prop12Upper_of (hM45 : Draft.RecordMeanCrude) (hM46 : Draft.RecordMeanLimit)
    (hV47 : Draft.RecordVariance) : Prop12Upper :=
  upperAssembly aOneFinite aSubadditiveE segCombLaw oscillation37 hM45 hM46 hV47
    recordMeanTransfer LFPPTree.pathTreeExists LFPPTree.chainLengthBounds treeInequality
    LFPPRecords.recordAssignment (chainUnionBound_of segCombLaw) zLimitBound exponentFromProb

/-- Proposition 1.2, lower bound (1.8), from the block construction of Section 5.2. -/
theorem prop12Lower_of (hB57 : Draft.DiscreteBlockConstruction) : Prop12Lower :=
  lowerAssembly aOneFinite aSubadditiveE segCombLaw oscillation37 hB57 couplingAtPoints
    polygonRiemannBound exponentFromProb

/-- **Proposition 1.2, upper bound (1.7)**, unconditionally. -/
theorem prop12Upper : Prop12Upper :=
  prop12Upper_of recordMeanCrude
    (recordMeanLimit_of_constrainedCovLimit (constrainedCovLimit twoScaleCovBound))
    recordVariance

/-- **Proposition 1.2, lower bound (1.8)**, from Lemma 5.1. -/
theorem prop12Lower_of_lemma51 (hL51 : Draft.Lemma51) : Prop12Lower :=
  prop12Lower_of (discreteBlockConstruction_of draftLemma23 hL51)

/-- **Theorem 1.1**, conditional only on Lemma 5.1 (the last node not yet proved). -/
theorem theorem11_of_lemma51 (hL51 : Draft.Lemma51) : Theorem11 :=
  theorem11_of aOneFinite aSubadditiveE aLinearLowerBound prop12Upper
    (prop12Lower_of_lemma51 hL51)

end LQGDimension
