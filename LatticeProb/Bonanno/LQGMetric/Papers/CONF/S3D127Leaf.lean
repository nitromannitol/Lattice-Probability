/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127Leaf at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127F1
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127I5

/-!
# CONF Lemma 2.10 at the domains `confU` (decision D127)

Gwynne–Miller arXiv:1905.00381, `confluence-final.tex`, Lemma 2.10 (C:712–742), at every domain
`confU r δ z T` (the only domains CONF uses, DV-D127-3): `confLem2_10AtConfU_of` (S3D127I5,
P2-HEATI: the coarse/fine model on `(ℕ → ℝ, stdP)` from (L2) `coarseKer_holder_confU` and (L3)
`exists_zbDistU_filt`) with (L1) `zbHeatRepr_confU` (S3D127F1, P2-HEATF: `G_U = π∫p_U`, BP
arXiv:2404.16642 §1.5, from N1–N4 in S3D127A–E).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric.CONF.ZBM

/-- **CONF Lemma 2.10 at every `confU r δ z T`.** -/
theorem confLem2_10AtConfU_holds : CONF.CONFLem2_10AtConfU :=
  confLem2_10AtConfU_of fun _ _ hr hδ z T => zbHeatRepr_confU hr hδ z T

end LQGMetric.CONF.ZBM
