/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43cFinal at commit fdb5cad; only the module paths of local imports are changed. -/
/-
GM Proposition 4.3 (`P4_3`, l. 1582–1593) from the assembly `gm_P4_3_core` (P2-M2N3), after
decision D91 (`νs < 1`, GM l. 1586).
-/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43cMain

set_option autoImplicit false

namespace LQGMetric.GM
open Blueprint

/-- **GM Proposition 4.3** from GM Prop 2.2, Prop 3.5, Lemma 5.5, Prop 5.2 and DFGPS Lemma 3.8. -/
theorem gm_P4_3 (h22 : P2_2) (h35 : P3_5) (h55 : L5_5) (h52 : P5_2) (h38 : DFGPSLem3_8) :
    P4_3 := by
  intro γ D D' c cs Cs hPS hRat hlt sel hgeo hinv hmeas νs μ ν c₁ c₂ hμ hμν hννs hνs1 hc₁ hc₁₂ hc₂
  exact gm_P4_3_core h22 h35 h55 h52 h38 hPS hRat hlt sel hgeo hinv hmeas μ ν c₁ c₂ hμ hμν
    (hννs.trans_lt hνs1) hc₁ hc₁₂ hc₂

end LQGMetric.GM
