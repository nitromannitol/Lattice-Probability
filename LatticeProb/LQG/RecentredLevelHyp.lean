import LatticeProb.LQG.RecentredCircleLaw
import LatticeProb.LQG.CircleIncrementTripleIndependence
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.NegMoment
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea6

/-! # Two-radius hypotheses for recentred circle averages -/

open MeasureTheory ProbabilityTheory Set
open MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort
open LatticeProb.GaussIndep QuantumZipper

namespace LatticeProb.LQG

/-- The same coordinate-measurable circle process satisfies the two-radius
hypotheses on a set contained in the normalizing half-disk. -/
theorem levelHyp_recentred_circle {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {ε : ℝ} (hε : 0 < ε)
    (z : ℂ) {S : Set ℂ} {k : ℕ} (hk : radius k ≤ ε / 2)
    (hS : ∀ t ∈ S, ‖t - z‖ ≤ ε / 2) :
    ConeArea6.LevelHyp P S ε 0
      (fun j t ω => H (radius j) t ω - H ε z ω) k := by
  let := hH.isProbabilityMeasure
  have hr := radius_pos k
  have hr1 := radius_pos (k + 1)
  have hsucc : radius (k + 1) = radius k / 2 := AreaExist.aradius_succ k
  have hle : radius (k + 1) ≤ radius k := by rw [hsucc]; linarith
  have hlog : 0 ≤ Real.log (ε / radius k) :=
    Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith)
  have hm (j : ℕ) : Measurable (fun p : ℂ × Ω => H (radius j) p.1 p.2 - H ε z p.2) :=
    (measurable_uncurry_coord hH hHm (radius_pos j)).sub ((hHm ε z).comp measurable_snd)
  have heq (t : ℂ) :
      (fun ω => (H (radius (k + 1)) t ω - H ε z ω) -
        (H (radius k) t ω - H ε z ω)) =
      (fun ω => H (radius (k + 1)) t ω - H (radius k) t ω) := by
    funext ω; ring
  refine ⟨by linarith, fun _ => (Real.log (ε / radius k)).toNNReal, ?_⟩
  refine { measU := hm k
           measΔ := (hm (k + 1)).sub (hm k)
           measL := measurable_const
           measw := measurable_const
           lawU := fun t ht => hasLaw_recentred_circle hH hε hr hk (hS t ht)
           lawΔ := ?_
           varU := ?_
           varΔ := ?_
           indep := ?_
           decor := ?_ }
  · intro t ht
    rw [heq t]
    have h := hasLaw_recentred_circle hH hr hr1 (by rw [hsucc])
      (z := t) (w := t) (by simp; linarith)
    have he : radius k / radius (k + 1) = 2 := by rw [hsucc]; field_simp
    simpa only [he] using h
  · intro t ht
    rw [Real.coe_toNNReal _ hlog]
    linarith
  · intro t ht
    exact (Real.coe_toNNReal _ (Real.log_nonneg one_le_two)).le
  · intro t ht
    rw [heq t]
    let X : Ioi (0 : ℝ) × ℂ → Ω → ℝ := fun p => H p.1 p.2
    have hD : (fun ω => H (radius (k + 1)) t ω - H (radius k) t ω) ∈
        Submodule.span ℝ (Set.range X) :=
      fun_sub_mem_span_range X (⟨radius (k + 1), hr1⟩, t) (⟨radius k, hr⟩, t)
    have hB : (fun ω => H (radius k) t ω - H ε z ω) ∈
        Submodule.span ℝ (Set.range X) :=
      fun_sub_mem_span_range X (⟨radius k, hr⟩, t) (⟨ε, hε⟩, z)
    have hin : ‖t - z‖ + max (radius (k + 1)) (radius k) ≤ ε := by
      rw [max_eq_right hle]; linarith [hS t ht]
    have hi := indepFun_real_of_mem_span_of_covariance_eq_zero hH.isGaussianProcess hD
      (B := fun _ : Unit => fun ω => H (radius k) t ω - H ε z ω)
      (fun _ => hB) (fun _ => covariance_increment_recentred_same_center hH hr1 hr hr hε hle le_rfl hin)
    exact hi.comp measurable_id (measurable_pi_apply ())
  · intro t ht u hu htu
    rw [heq t]
    have hin : ‖t - z‖ + max (radius (k + 1)) (radius k) ≤ ε := by
      rw [max_eq_right hle]; linarith [hS t ht]
    have hfar : radius k + max (radius (k + 1)) (radius k) ≤ ‖t - u‖ := by
      rw [max_eq_right hle]; linarith
    have hfar' : max (radius (k + 1)) (radius k) +
        max (radius (k + 1)) (radius k) ≤ ‖t - u‖ := by
      rw [max_eq_right hle]; linarith
    have hi := indepFun_increment_recentred_triple hH hr1 hr hr1 hr hr hε hle le_rfl hin hfar hfar'
    have htriple : (fun ω => (H (radius k) t ω - H ε z ω,
        H (radius k) u ω - H ε z ω,
        (H (radius (k + 1)) u ω - H ε z ω) - (H (radius k) u ω - H ε z ω))) =
        (fun ω => (H (radius k) t ω - H ε z ω, H (radius k) u ω - H ε z ω,
          H (radius (k + 1)) u ω - H (radius k) u ω)) := by
      funext ω
      congr 1
      ring
    rw [htriple]
    exact hi

end LatticeProb.LQG
