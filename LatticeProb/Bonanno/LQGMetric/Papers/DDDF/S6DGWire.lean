/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6DGWire at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DGUp2
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DGFree
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6T20Done

/-!
# DDDF (6.99) and (1.3) from the DG results (task P2-DDDFDG)

`Blueprint.DDDFEq6_99` (DDDF l. 1615–1638) and `Blueprint.DDDFEq1_3` (DDDF l. 162–166) from
DDDF's DG inputs (5.54) (l. 1004–1010) and (5.78) (l. 1276–1281), which are proved in
`S6DGLow` / `S6DGUp2` from
* `Blueprint.DGThm1_5KU` (DG Thm 1.5, (1.5b) second half, DG:343–346) — for (5.54);
* `Blueprint.DGProp3_21` (DG Prop 3.21, DG:1603–1610, through DFGPS Lemma 3.6) — for (5.78);
* `S6DG.WPPhiCompare` (the comparison of `φ_δ` with the whole-plane circle average, DG Lemma 3.7's
  form; the role of DGo Prop 3.3 in DDDF l. 1004), which is proved in `S6DGCmp`/`S6DGFree` from
  DG Lemma 3.1 (proved), DDDF (2.17) (proved) and DGo (3.9)–(3.10) for the free kernel
  (`S6DG.FreeKerBounds`, deterministic kernel estimates, open).

`dddfEq6_99_of_DG`, `dddfEq1_3_of_DG` take the open leaves `DGThm1_5KU`, `DGProp3_21` (cited
Blueprint items, already leaves of the main theorem) and `FreeKerBounds`;
`dddfEq6_99_of_cmp`, `dddfEq1_3_of_cmp` take `WPPhiCompare` instead.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric
namespace DDDF
namespace S6DG

open Blueprint

/-- **DDDF (6.99)** = `Blueprint.DDDFEq6_99` from DG Thm 1.5 (1.5b) and the comparison. -/
theorem dddfEq6_99_of_cmp (hKU : DGThm1_5KU) (hcmp : WPPhiCompare) : Blueprint.DDDFEq6_99 :=
  dddfEq6_99_of_554 fun _ hγ hγ2 _ _ _ _ hW => s6Eq5_54_of_DG hKU hcmp hγ hγ2 hW

/-- **DDDF (1.3)** = `Blueprint.DDDFEq1_3` from DG Thm 1.5 (1.5b), DG Prop 3.21 and the
comparison. -/
theorem dddfEq1_3_of_cmp (hKU : DGThm1_5KU) (hP3 : DGProp3_21) (hcmp : WPPhiCompare) :
    Blueprint.DDDFEq1_3 :=
  dddfEq1_3_of_554 fun _ hγ hγ2 _ _ _ _ hW =>
    ⟨s6Eq5_54_of_DG hKU hcmp hγ hγ2 hW, s6Eq5_78_of_DG hP3 hcmp hγ hγ2 hW⟩

/-- **DDDF (6.99)** from DG Thm 1.5 (1.5b) and DGo (3.9)–(3.10) for the free kernel. -/
theorem dddfEq6_99_of_DG (hKU : DGThm1_5KU) (hB : FreeKerBounds) : Blueprint.DDDFEq6_99 :=
  dddfEq6_99_of_cmp hKU (wpPhiCompare_of_kerBounds hB)

/-- **DDDF (1.3)** from DG Thm 1.5 (1.5b), DG Prop 3.21 and DGo (3.9)–(3.10) for the free
kernel. -/
theorem dddfEq1_3_of_DG (hKU : DGThm1_5KU) (hP3 : DGProp3_21) (hB : FreeKerBounds) :
    Blueprint.DDDFEq1_3 :=
  dddfEq1_3_of_cmp hKU hP3 (wpPhiCompare_of_kerBounds hB)

end S6DG
end DDDF
end LQGMetric
