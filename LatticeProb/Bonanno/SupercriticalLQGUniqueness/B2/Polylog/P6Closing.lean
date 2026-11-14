/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P6Closing at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P6CompareSubset
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P11Assembly

 










set_option autoImplicit false

namespace SupercriticalLQGUniqueness.B2.Polylog

 

theorem plCompareSubset_of_dg20 (hPerc : Iface.DG20PercEstimate')
    (hExp : Iface.DG20ExponentRelation) (hPos : Iface.DG20ExponentPositive) :
    PLCompareSubset :=
  plCompareSubset_of_inputs hPerc (DG20Pt.dg20Section4_of_inputs hPerc hExp hPos)

 

theorem iface_plThm19Limit_of_dg20 (hPerc : Iface.DG20PercEstimate')
    (hExp : Iface.DG20ExponentRelation) (hPos : Iface.DG20ExponentPositive) :
    Iface.PLThm19Limit :=
  iface_plThm19Limit_of_inputs hPerc hExp hPos (plCompareSubset_of_dg20 hPerc hExp hPos)

 

theorem iface_plThm19_of_dg20 (hPerc : Iface.DG20PercEstimate')
    (hExp : Iface.DG20ExponentRelation) (hPos : Iface.DG20ExponentPositive)
    (hNorm : LFPPNormalizerExists) : Iface.PLThm19 :=
  iface_plThm19_of_inputs hPerc hExp hPos (plCompareSubset_of_dg20 hPerc hExp hPos) hNorm

end SupercriticalLQGUniqueness.B2.Polylog
