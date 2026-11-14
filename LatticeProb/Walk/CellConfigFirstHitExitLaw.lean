import LatticeProb.Walk.CellConfigInnerExitRestart
import LatticeProb.Walk.CellConfigRestartObservableAE
import LatticeProb.Walk.CellConfigRestartMeasurable

/-!
# Exit positions after the first boundary cell

A first boundary-cell restart preserves the exit position from a larger domain.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov MatedCRTHarmonic.HarmonicInfinity
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigSRW

/-- The exit position is unchanged by restarting at the first inner boundary cell. -/
theorem exitPosition_stopShift_hit_frontier (H : CellConfig)
    (hH : H.IsCellConfiguration) {U V W : Set Plane}
    (hV : IsOpen V) (hVU : V ⊆ U) (hconv : Convex ℝ U) (hW : IsOpen W)
    (p : H.cells → Plane) (hp : ∀ K, p K ∈ (K.1 : Set Plane))
    (ω : ℕ → H.cells) (hstart : (((ω 0).1 : Set Plane) ∩ V).Nonempty)
    (hadj : ∀ n, H.Adj (ω n) (ω (n + 1))) (hpos : ∀ K, 0 < H.holding K)
    (hunb : H.JumpTimesUnbounded ω)
    (hlast : ∀ K : H.cells, ((K.1 : Set Plane) ∩ frontier V).Nonempty →
      (K.1 : Set Plane) ⊆ U)
    {ε : ℝ≥0} (hε : 0 < ε) (hscale : ∀ z ∈ U, (ε : ℝ) • z ∈ W)
    (hhit : hitTime {K : H.cells | ((K.1 : Set Plane) ∩ frontier V).Nonempty} ω ≠ ⊤)
    (hfin : continuousExitTime W 0 (H.interpolatedWalk p ε ω) ≠ ∞) :
    (H.interpolatedWalk p ε ω)
        (continuousExitTime W 0 (H.interpolatedWalk p ε ω)).toNNReal =
      (H.interpolatedWalk p ε (stopShift
        (hitTime {K : H.cells | ((K.1 : Set Plane) ∩ frontier V).Nonempty}) ω))
        (continuousExitTime W 0 (H.interpolatedWalk p ε (stopShift
          (hitTime {K : H.cells | ((K.1 : Set Plane) ∩ frontier V).Nonempty}) ω))).toNNReal := by
  let I : Set H.cells := {K | ((K.1 : Set Plane) ∩ frontier V).Nonempty}
  let k := (hitTime I ω).toNat
  have hk : hitTime I ω = k := (coe_toNat_hitTime hhit).symm
  have hfirst := hitTime_eq_coe_iff.mp hk
  let t : ℝ≥0 := ⟨(ε : ℝ) ^ 2 * H.jumpTime ω k,
    mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos k)⟩
  have h := LatticeProb.CellConfigInterpolation.exitPosition_restart_of_inner_boundary
    H hH hV hVU hconv hW p hp ω hstart hadj hpos hunb k hfirst.2
    (hlast (ω k) hfirst.1) hε hscale t rfl hfin
  rw [stopShift_eq_of_eq hk]
  exact h.symm

/-- Separation controls the distance between exit-position laws when the
first boundary cell is reached before the finite outer exit almost surely. -/
theorem levyProkhorovEDist_exitPosition_le_of_set_separation
    (H : CellConfig) [Countable H.cells] (hH : H.IsCellConfiguration)
    (hne : ∀ K : H.cells, ∃ K' : H.cells, H.Adj K K') (hrec : H.Recurrent)
    {U V W : Set Plane} (hV : IsOpen V) (hVU : V ⊆ U)
    (hconv : Convex ℝ U) (hW : IsOpen W)
    (p : H.cells → Plane) (hp : ∀ K, p K ∈ (K.1 : Set Plane))
    (hlast : ∀ K : H.cells, ((K.1 : Set Plane) ∩ frontier V).Nonempty →
      (K.1 : Set Plane) ⊆ U)
    {ε : ℝ≥0} (hε : 0 < ε) (hscale : ∀ z ∈ U, (ε : ℝ) • z ∈ W)
    (B : Set H.cells) {x y : H.cells} {Qx Qy : Measure (ℕ → H.cells)}
    (hQx : H.IsSRWLaw x Qx) (hQy : H.IsSRWLaw y Qy) (hyB : y ∈ B)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hD : 1 - δ ≤ (Qx {ω | GraphSeparates H.graph
      (traceBefore id {K : H.cells | ((K.1 : Set Plane) ∩ frontier V).Nonempty} ω) B
      {K : H.cells | ((K.1 : Set Plane) ∩ frontier V).Nonempty}}).toReal)
    (hx : Qx {ω | hitTime {K : H.cells | ((K.1 : Set Plane) ∩ frontier V).Nonempty} ω ≠ ⊤} = 1)
    (hy : Qy {ω | hitTime {K : H.cells | ((K.1 : Set Plane) ∩ frontier V).Nonempty} ω ≠ ⊤} = 1)
    (hgoodx : ∀ᵐ ω ∂Qx, (((ω 0).1 : Set Plane) ∩ V).Nonempty ∧
      (∀ n, H.Adj (ω n) (ω (n + 1))) ∧ H.JumpTimesUnbounded ω ∧
      hitTime {K : H.cells | ((K.1 : Set Plane) ∩ frontier V).Nonempty} ω ≠ ⊤ ∧
      continuousExitTime W 0 (H.interpolatedWalk p ε ω) ≠ ∞)
    (hgoody : ∀ᵐ ω ∂Qy, (((ω 0).1 : Set Plane) ∩ V).Nonempty ∧
      (∀ n, H.Adj (ω n) (ω (n + 1))) ∧ H.JumpTimesUnbounded ω ∧
      hitTime {K : H.cells | ((K.1 : Set Plane) ∩ frontier V).Nonempty} ω ≠ ⊤ ∧
      continuousExitTime W 0 (H.interpolatedWalk p ε ω) ≠ ∞) :
    levyProkhorovEDist
      (Qx.map (fun ω => (H.interpolatedWalk p ε ω)
        (continuousExitTime W 0 (H.interpolatedWalk p ε ω)).toNNReal))
      (Qy.map (fun ω => (H.interpolatedWalk p ε ω)
        (continuousExitTime W 0 (H.interpolatedWalk p ε ω)).toNNReal)) ≤ ENNReal.ofReal δ := by
  let I : Set H.cells := {K | ((K.1 : Set Plane) ∩ frontier V).Nonempty}
  let f : (ℕ → H.cells) → Plane := fun ω => (H.interpolatedWalk p ε ω)
    (continuousExitTime W 0 (H.interpolatedWalk p ε ω)).toNNReal
  have hpos : ∀ K, 0 < H.holding K :=
    CellConfigWalk.holding_pos_of_forall_exists_adj hH hne
  have hfx : ∀ᵐ ω ∂Qx, f ω = f (stopShift (hitTime I) ω) := by
    filter_upwards [hgoodx] with ω hω
    exact exitPosition_stopShift_hit_frontier H hH hV hVU hconv hW p hp ω hω.1
      hω.2.1 hpos hω.2.2.1 hlast hε hscale hω.2.2.2.1 hω.2.2.2.2
  have hfy : ∀ᵐ ω ∂Qy, f ω = f (stopShift (hitTime I) ω) := by
    filter_upwards [hgoody] with ω hω
    exact exitPosition_stopShift_hit_frontier H hH hV hVU hconv hW p hp ω hω.1
      hω.2.1 hpos hω.2.2.1 hlast hε hscale hω.2.2.2.1 hω.2.2.2.2
  have hfinx : ∀ᵐ ω ∂Qx, hitTime I ω < ⊤ := by
    filter_upwards [hgoodx] with ω hω
    exact lt_top_iff_ne_top.mpr hω.2.2.2.1
  have hfiny : ∀ᵐ ω ∂Qy, hitTime I ω < ⊤ := by
    filter_upwards [hgoody] with ω hω
    exact lt_top_iff_ne_top.mpr hω.2.2.2.1
  exact levyProkhorovEDist_observable_le_of_set_separation_ae H hH I B hQx hQy
    hyB hδ hD hx hy f f f
    (aemeasurable_exitPosition_stopShift_hit H hH hne hrec I hQx hfinx p ε hW)
    (aemeasurable_exitPosition_stopShift_hit H hH hne hrec I hQy hfiny p ε hW) hfx hfy

end LatticeProb.CellConfigSRW
end
