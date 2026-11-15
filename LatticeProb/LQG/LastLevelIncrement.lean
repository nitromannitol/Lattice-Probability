import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.LastLevel

/-! # Increments of last-level times -/

open MeasureTheory Set

namespace MatedCRTHarmonic.ConeScaling

/-- Re-centring at one level translates the last time of another level. -/
theorem lastLevel_radShift_eq_sub (Q a b : ℝ) (w : C(ℝ, ℝ))
    (ha : IsGreatest {s : ℝ | w (-s) + Q * s = a} (lastLevel Q a w)) :
    lastLevel Q (a - b) (radShift Q b w) = lastLevel Q a w - lastLevel Q b w := by
  set ℓ := lastLevel Q b w
  have hY : ∀ s, radShift Q b w (-s) + Q * s =
      (w (-(s + ℓ)) + Q * (s + ℓ)) - b := by
    intro s
    simp only [radShift_apply, ← show ℓ = lastLevel Q b w from rfl]
    ring_nf
  unfold lastLevel at ⊢
  apply IsGreatest.csSup_eq
  constructor
  · change radShift Q b w (-(lastLevel Q a w - ℓ)) +
      Q * (lastLevel Q a w - ℓ) = a - b
    rw [hY]
    have h := ha.1
    simp only [Set.mem_ofPred_eq] at h
    simpa only [sub_add_cancel] using congrArg (fun x : ℝ => x - b) h
  · intro s hs
    have hs' : w (-(s + ℓ)) + Q * (s + ℓ) = a := by
      change radShift Q b w (-s) + Q * s = a - b at hs
      rw [hY] at hs
      linarith
    have h := ha.2 hs'
    change s ≤ lastLevel Q a w - ℓ
    linarith

/-- A shift-invariant radial law makes a last-level increment equal in law to
its recentered last-level time. -/
theorem map_lastLevel_sub_eq_of_radShift_invariant {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : Ω → C(ℝ, ℝ)} (hW : Measurable W) (Q a b : ℝ)
    (ha : ∀ᵐ ω ∂P, IsGreatest {s : ℝ | W ω (-s) + Q * s = a}
      (lastLevel Q a (W ω)))
    (hshift : P.map (fun ω => radShift Q b (W ω)) = P.map W) :
    P.map (fun ω => lastLevel Q a (W ω) - lastLevel Q b (W ω)) =
      P.map (fun ω => lastLevel Q (a - b) (W ω)) := by
  calc
    _ = P.map (fun ω => lastLevel Q (a - b) (radShift Q b (W ω))) := by
      apply Measure.map_congr
      filter_upwards [ha] with ω hω
      exact (lastLevel_radShift_eq_sub Q a b (W ω) hω).symm
    _ = (P.map (fun ω => radShift Q b (W ω))).map (lastLevel Q (a - b)) :=
      (Measure.map_map (measurable_lastLevel Q (a - b))
        ((measurable_radShift Q b).comp hW)).symm
    _ = (P.map W).map (lastLevel Q (a - b)) := by rw [hshift]
    _ = P.map (fun ω => lastLevel Q (a - b) (W ω)) :=
      Measure.map_map (measurable_lastLevel Q (a - b)) hW

end MatedCRTHarmonic.ConeScaling
