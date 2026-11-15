import LatticeProb.LQG.MatedCRTRealTailLocalFiniteness
import LatticeProb.LQG.PeanosphereTimeTranslation

/-! # Local finiteness of Peanosphere graphs -/

set_option autoImplicit false

namespace MatedCRTHarmonic.RouteM

/-- Both coordinate tail conditions in a Peanosphere imply local finiteness
of its graph at every positive mesh. -/
theorem Peanosphere.locallyFinite {ω : MatedCRT.Path2} {η : ℝ → ℂ}
    (P : Peanosphere ω η) {ε : ℝ} (hε : 0 < ε) :
    MatedCRT.IsLocallyFinite ε ω :=
  MatedCRT.locallyFinite_of_realTailLows hε
    (fun M T => (P.liminf_L M T).1) (fun M T => (P.liminf_L M T).2)
    (fun M T => (P.liminf_R M T).1) (fun M T => (P.liminf_R M T).2)

/-- Local finiteness also holds after every simultaneous time translation. -/
theorem Peanosphere.locallyFinite_time_translate {ω : MatedCRT.Path2} {η : ℝ → ℂ}
    (P : Peanosphere ω η) {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    MatedCRT.IsLocallyFinite ε
      ⟨fun t => ω (t + c), ω.continuous.comp (by fun_prop)⟩ :=
  (P.time_translate c).locallyFinite hε

end MatedCRTHarmonic.RouteM
