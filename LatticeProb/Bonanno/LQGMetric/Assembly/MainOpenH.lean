/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Assembly.MainOpenH at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Assembly.MainOpenG
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6XiQ
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28U1Fin

/-!
# Theorems 1.1 and 1.2 with the DDDF Step-1 leaves proved (task P2-DDDFW)

`theorem11_openG`/`theorem12_openG` (Assembly/MainOpenG.lean) with `DDDFStep1Leaves` discharged:
the upper half is `DDDF.S6P28U.upper_step1` (DDDF tightness.tex l. 1414–1436, 1648) and the lower
half is `DDDF.S6XiQ.s6_lowerStep1'` (l. 1455–1481; the restriction `α ≥ 1` removed through
`1 − ξQ ≤ 2ξ`, l. 1480). The inputs (5.54) and (5.78) come from the DG leaves
(`dddf554_of_DG`, `DDDF.S6DG.s6Eq5_78_of_DG` with the proved kernel bounds). The remaining
hypotheses are the cited DG results and the CONF §3 package.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric

open Blueprint MeasureTheory WhiteNoise

/-- **`DDDFStep1Leaves`** (DDDF Prop 28 Step 1, both parts) from the DG leaves. -/
theorem dddfStep1Leaves_of_DG (hKU : DGThm1_5KU) (hP321 : DGProp3_21) : DDDFStep1Leaves :=
  fun γ hγ hγ2 _ _ P W hW =>
    ⟨fun _ hβ0 hβ => DDDF.S6P28U.upper_step1 hγ hγ2 hW (dddf554_of_DG hKU γ hγ hγ2 P W hW) hβ0 hβ,
      fun _ hα => DDDF.S6XiQ.s6_lowerStep1' hγ hγ2 hW (dddf554_of_DG hKU γ hγ hγ2 P W hW)
        (DDDF.S6DG.s6Eq5_78_of_DG hP321
          (DDDF.S6DG.wpPhiCompare_of_kerBounds DDDF.S6DGKer.freeKerBounds) hγ hγ2 hW) hα⟩

/-- **Theorem 1.2** from the cited DG results and the CONF §3 package. -/
theorem theorem12_openH (hDG : DG.DGThm1_5) (hKU : DGThm1_5KU) (hP321 : DGProp3_21)
    (hC3 : CONFSection3) : Theorem12 :=
  theorem12_openG hDG hKU hP321 hC3 (dddfStep1Leaves_of_DG hKU hP321)

/-- **Theorem 1.1** from the cited DG results and the CONF §3 package. -/
theorem theorem11_openH (hDG : DG.DGThm1_5) (hKU : DGThm1_5KU) (hP321 : DGProp3_21)
    (hC3 : CONFSection3) : Theorem11 :=
  theorem11_openG hDG hKU hP321 hC3 (dddfStep1Leaves_of_DG hKU hP321)

end LQGMetric
