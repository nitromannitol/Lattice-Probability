import LatticeProb.LQG.DirectRelTimeChange
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.PsiBundle

/-! # Increasing time changes of Peanosphere relations -/

set_option autoImplicit false

namespace MatedCRTHarmonic.RouteM

open Filter MatedCRTHarmonic.MatedCRT

/-- A common increasing time isomorphism preserves the Peanosphere structure. -/
theorem Peanosphere.comp_orderIso {w : Path2} {η : ℝ → ℂ}
    (P : Peanosphere w η) (e : ℝ ≃o ℝ) :
    Peanosphere ⟨fun t => w (e t), w.continuous.comp e.continuous⟩ (fun t => η (e t)) := by
  constructor
  · exact P.cont.comp e.continuous
  · intro z
    obtain ⟨t, ht⟩ := P.surj z
    exact ⟨e.symm t, by simpa only [e.apply_symm_apply] using ht⟩
  · exact P.transient.comp e.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  · intro s t h
    exact LatticeProb.merge_comp_orderIso (fun u => (w u).1) (fun u => (w u).2)
      η e P.merge s t h
  · intro s t h
    exact LatticeProb.onlyMerge_comp_orderIso (fun u => (w u).1) (fun u => (w u).2)
      η e P.onlyMerge s t h
  · intro M T
    obtain ⟨⟨u, hu, hlu⟩, _⟩ := P.liminf_L M (e T)
    obtain ⟨_, ⟨v, hv, hlv⟩⟩ := P.liminf_L M (-e (-T))
    refine ⟨⟨e.symm u, ?_, ?_⟩, ⟨e.symm v, ?_, ?_⟩⟩
    · simpa only [e.symm_apply_apply] using e.symm.monotone hu
    · change (w (e (e.symm u))).1 < M
      simpa only [e.apply_symm_apply] using hlu
    · have hv' : v ≤ e (-T) := by simpa only [neg_neg] using hv
      simpa only [e.symm_apply_apply] using e.symm.monotone hv'
    · change (w (e (e.symm v))).1 < M
      simpa only [e.apply_symm_apply] using hlv
  · intro M T
    obtain ⟨⟨u, hu, hru⟩, _⟩ := P.liminf_R M (e T)
    obtain ⟨_, ⟨v, hv, hrv⟩⟩ := P.liminf_R M (-e (-T))
    refine ⟨⟨e.symm u, ?_, ?_⟩, ⟨e.symm v, ?_, ?_⟩⟩
    · simpa only [e.symm_apply_apply] using e.symm.monotone hu
    · change (w (e (e.symm u))).2 < M
      simpa only [e.apply_symm_apply] using hru
    · have hv' : v ≤ e (-T) := by simpa only [neg_neg] using hv
      simpa only [e.symm_apply_apply] using e.symm.monotone hv'
    · change (w (e (e.symm v))).2 < M
      simpa only [e.apply_symm_apply] using hrv
  · intro i a b hab ha hb
    have hmin (x : ℝ) (hx : IsLocalMin
        (fun t => lrCoord i t ⟨fun u => w (e u), w.continuous.comp e.continuous⟩) x) :
        IsLocalMin (lrCoord i · w) (e x) := by
      change IsLocalMin ((lrCoord i · w) ∘ e) x at hx
      have hx₀ : IsLocalMin ((lrCoord i · w) ∘ e) (e.symm (e x)) := by
        simpa only [e.symm_apply_apply] using hx
      have h := hx₀.comp_continuous (e.symm.continuous.continuousAt (x := e x))
      simpa only [Function.comp_def, e.apply_symm_apply] using h
    exact P.locMinDistinct i (e a) (e b) (fun h => hab (e.injective h)) (hmin a ha) (hmin b hb)

end MatedCRTHarmonic.RouteM
