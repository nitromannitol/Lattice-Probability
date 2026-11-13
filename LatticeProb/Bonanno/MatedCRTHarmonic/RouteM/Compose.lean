/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.RouteM.Compose at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.RSeparation
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.DInstance
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.BPointConnected

/-!
# Route M: template separation for the mated-CRT cells

Composition of the three Route M results: the explicit
monotone drawing (`matedCRTDrawing`), Theorem B (`pointConnected_of_peanosphere_holds`) and the
separation lemma (`templateSeparation_of_monotoneDrawing`). The remaining inputs are the `Peanosphere`
bundle with G0 (`SideStrict`), produced by the mating-of-trees layer, and the small-cell bound at the annulus
(from [18] Lemma 2.7).
-/

open Set Metric

namespace MatedCRTHarmonic.RouteM

variable {ε : ℝ} {ω : MatedCRT.Path2} {η : ℝ → ℂ} {h : MatedCRT.IsLocallyFinite ε ω}

/-- `TemplateSeparation` for the cells `η '' [ε(x−1), εx]` of a `Peanosphere`, given G0 and small cells near the
annulus. -/
theorem templateSeparation_matedCRT (P : Peanosphere ω η) (hG : SideStrict ε ω)
    (H : CellularEmbedding (MatedCRT.graph ε ω h) 0)
    (hcell : H.cell = fun x : ℤ => η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ x, (H.cell x ∩ closedBall z (2 * r)).Nonempty → diam (H.cell x) ≤ r / 1000) :
    H.TemplateSeparation z r :=
  templateSeparation_of_monotoneDrawing (matedCRTDrawing P hG H hcell)
    (pointConnected_of_peanosphere_holds P H hcell) hr hsmall

end MatedCRTHarmonic.RouteM
