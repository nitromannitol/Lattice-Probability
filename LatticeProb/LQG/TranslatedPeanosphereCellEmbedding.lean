import LatticeProb.LQG.PeanosphereTimeTranslation
import LatticeProb.LQG.ShiftedRootCellEmbedding

/-! # Cellular embeddings from translated Peanospheres -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT

/-- An in-mesh time translation of a Peanosphere gives a rooted cellular embedding
when the translated graph is locally finite and satisfies the strict side condition. -/
def translatedPeanosphereCellularEmbedding {w : Path2} {η ηL : C(ℝ, ℂ)} {ε c : ℝ}
    (hε : 0 < ε) (hc0 : 0 ≤ c) (hcε : c ≤ ε) (hη0 : η 0 = 0)
    (P : RouteM.Peanosphere w η)
    (hlf : IsLocallyFinite ε ⟨fun t => w (t + c), w.continuous.comp (by fun_prop)⟩)
    (hs : RouteM.SideStrict ε ⟨fun t => w (t + c), w.continuous.comp (by fun_prop)⟩)
    (hi : ∀ a b : ℝ, a < b → (interior (η '' Icc a b)).Nonempty)
    (φ : ℝ ≃o ℝ) (hη : ∀ t, η t = ηL (φ t))
    (hvol : ∀ s t : ℝ, s ≤ t → volume (ηL '' Icc s t) = ENNReal.ofReal (t - s)) :
    CellularEmbedding (MatedCRT.graph ε
      ⟨fun t => w (t + c), w.continuous.comp (by fun_prop)⟩ hlf) 0 :=
  shiftedRootCellularEmbedding hε hc0 hcε hη0 hlf (P.time_translate c) hs hi φ hη hvol

end MatedCRTHarmonic.MoTInput
