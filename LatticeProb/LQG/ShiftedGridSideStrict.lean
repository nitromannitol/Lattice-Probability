import LatticeProb.LQG.GridSideStrict
import LatticeProb.Analysis.GridValueCollisions
import LatticeProb.Analysis.GridLocalMinLevels
import LatticeProb.LQG.PeanosphereTimeTranslation

/-! # Strict side conditions for almost every grid phase -/

set_option autoImplicit false

open MeasureTheory Set Filter

namespace MatedCRTHarmonic.RouteM

/-- For a fixed positive mesh, almost every time translation satisfies the strict
side condition if each coordinate has null nonzero grid-lag increment zero sets
and null level sets at local minima. -/
theorem Peanosphere.ae_sideStrict_time_translate
    {ω : MatedCRT.Path2} {η : ℝ → ℂ} (P : Peanosphere ω η) {ε : ℝ} (hε : 0 < ε)
    (hinc : ∀ i : Fin 2, ∀ n : ℤ, n ≠ 0 →
      volume {t : ℝ | MatedCRT.lrCoord i t ω = MatedCRT.lrCoord i (t + ε * n) ω} = 0)
    (hlevel : ∀ i : Fin 2, ∀ t, IsLocalMin (MatedCRT.lrCoord i · ω) t →
      volume {s : ℝ | MatedCRT.lrCoord i s ω = MatedCRT.lrCoord i t ω} = 0) :
    ∀ᵐ c : ℝ ∂volume, SideStrict ε
      ⟨fun t => ω (t + c), ω.continuous.comp (by fun_prop)⟩ := by
  have hgrid : ∀ᵐ c : ℝ ∂volume, ∀ i : Fin 2, ∀ k l : ℤ, k ≠ l →
      MatedCRT.lrCoord i (c + ε * k) ω ≠ MatedCRT.lrCoord i (c + ε * l) ω := by
    apply ae_all_iff.mpr
    intro i
    have h := LatticeProb.measure_grid_value_collisions_eq_zero
      (MatedCRT.lrCoord i · ω) ε (hinc i)
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h] with c hc k l hkl heq
    exact hc ⟨k, l, hkl, heq⟩
  have havoid : ∀ᵐ c : ℝ ∂volume, ∀ i : Fin 2, ∀ k : ℤ, ∀ t,
      IsLocalMin (MatedCRT.lrCoord i · ω) t →
      MatedCRT.lrCoord i (c + ε * k) ω ≠ MatedCRT.lrCoord i t ω := by
    apply ae_all_iff.mpr
    intro i
    have hcount := LatticeProb.countable_localMin_of_distinct_values _ (P.locMinDistinct i)
    have h := LatticeProb.measure_grid_localMin_levels_eq_zero
      (MatedCRT.lrCoord i · ω) ε hcount (hlevel i)
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h] with c hc k t ht heq
    exact hc ⟨k, t, ht, heq⟩
  filter_upwards [hgrid, havoid] with c hg ha
  let w : MatedCRT.Path2 := ⟨fun t => ω (t + c), ω.continuous.comp (by fun_prop)⟩
  have hp := P.time_translate c
  have hlocal (i : Fin 2) (t : ℝ) (ht : IsLocalMin (MatedCRT.lrCoord i · w) t) :
      IsLocalMin (MatedCRT.lrCoord i · ω) (t + c) := by
    have h := IsLocalMin.comp_continuous
      (f := fun u => MatedCRT.lrCoord i u w) (g := fun u : ℝ => u - c)
      (b := t + c) (by simpa using ht) (by fun_prop)
    simpa [w, MatedCRT.lrCoord, Function.comp_def] using h
  apply sideStrict_of_grid_exclusions hε w
  · intro b s t hst hs ht
    have h := hp.locMinDistinct (if b then 1 else 0) s t hst
    cases b <;> simpa [w, MatedCRT.lrCoord] using h hs ht
  · intro b k l hkl
    have h := hg (if b then 1 else 0) k l hkl
    cases b <;> simpa [w, MatedCRT.lrCoord, add_comm] using h
  · intro b k t ht
    have ht' : IsLocalMin (MatedCRT.lrCoord (if b then 1 else 0) · w) t := by
      cases b <;> simpa [MatedCRT.lrCoord] using ht
    have h := ha (if b then 1 else 0) k (t + c) (hlocal _ _ ht')
    cases b <;> simpa [w, MatedCRT.lrCoord, add_comm] using h
  · intro b k ht
    have ht' : IsLocalMin (MatedCRT.lrCoord (if b then 1 else 0) · w) (ε * k) := by
      cases b <;> simpa [MatedCRT.lrCoord] using ht
    have h := ha (if b then 1 else 0) k (ε * k + c) (hlocal _ _ ht')
    apply h
    simp only [add_comm]

end MatedCRTHarmonic.RouteM
