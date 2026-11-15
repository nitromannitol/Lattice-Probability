import LatticeProb.LQG.PeanosphereLocalFiniteness
import LatticeProb.LQG.TranslatedPeanosphereCellEmbedding

/-! # Cellular embeddings of Peanosphere graphs -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT

/-- A time translation within one mesh interval of a Peanosphere gives a rooted
cellular embedding, provided the translated path satisfies the strict side condition. -/
def peanosphereCellularEmbedding {w : Path2} {η ηL : C(ℝ, ℂ)} {ε c : ℝ}
    (hε : 0 < ε) (hc0 : 0 ≤ c) (hcε : c ≤ ε) (hη0 : η 0 = 0)
    (P : RouteM.Peanosphere w η)
    (hs : RouteM.SideStrict ε ⟨fun t => w (t + c), w.continuous.comp (by fun_prop)⟩)
    (hi : ∀ a b : ℝ, a < b → (interior (η '' Icc a b)).Nonempty)
    (φ : ℝ ≃o ℝ) (hη : ∀ t, η t = ηL (φ t))
    (hvol : ∀ s t : ℝ, s ≤ t → volume (ηL '' Icc s t) = ENNReal.ofReal (t - s)) :
    CellularEmbedding (MatedCRT.graph ε
      ⟨fun t => w (t + c), w.continuous.comp (by fun_prop)⟩
      (P.locallyFinite_time_translate hε c)) 0 :=
  translatedPeanosphereCellularEmbedding hε hc0 hcε hη0 P
    (P.locallyFinite_time_translate hε c) hs hi φ hη hvol

end MatedCRTHarmonic.MoTInput
