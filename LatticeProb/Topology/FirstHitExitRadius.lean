import LatticeProb.Topology.FirstHitExitEuclidean

/-! # First-hit exit traces at arbitrary radii -/

set_option autoImplicit false

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- The finite shifted exit trace in planar coordinates contains an open ball
exactly when the original first-hit exit trace contains one of the same radius. -/
theorem firstHit_forwardExit_ball_iff
    (f : C(ℝ, EuclideanSpace ℝ (Fin 2))) (η : ℝ → ℂ) (z : ℂ) (r R : ℝ)
    (hη : Continuous η) (hproper : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hshift : ∀ s, f s = Complex.orthonormalBasisOneI.repr
      (η (MatedCRTHarmonic.GMS4b.hitTime η z + s) - z)) :
    (openExitTime (fun s (_ : Unit) => f (0 + (s : ℝ))) (ball 0 r) () ≠ ⊤ ∧
      ∃ w, ball w R ⊆ f '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ f t ∉ ball 0 r})) ↔
    ∃ w, ball w R ⊆ η '' Icc (MatedCRTHarmonic.GMS4b.hitTime η z)
      (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime η z ≤ t ∧ η t ∉ ball z r}) := by
  let i := Complex.orthonormalBasisOneI.repr
  let t₀ := MatedCRTHarmonic.GMS4b.hitTime η z
  have hout (t : ℝ) : i (η t) ∉ ball (i z) r ↔ η t ∉ ball z r := by
    simp only [mem_ball, i.dist_map]
  have hclock : openExitTime (fun s (_ : Unit) => i (η (t₀ + (s : ℝ))))
      (ball (i z) r) () =
      openExitTime (fun s (_ : Unit) => η (t₀ + (s : ℝ))) (ball z r) () := by
    unfold openExitTime
    apply le_antisymm
    · refine le_iInf fun t => ?_
      exact iInf_le_of_le ⟨t.1, (hout _).mpr t.2⟩ le_rfl
    · refine le_iInf fun t => ?_
      exact iInf_le_of_le ⟨t.1, (hout _).mp t.2⟩ le_rfl
  have hfin : openExitTime (fun s (_ : Unit) => i (η (t₀ + (s : ℝ))))
      (ball (i z) r) () ≠ ⊤ := by
    rw [hclock]
    exact (openExitTime_ball_ne_top_of_tendsto_cocompact η hproper t₀ z r).1
  have hshift' : ∀ s, f s = i (η (t₀ + s)) - i z := by
    intro s
    simpa only [map_sub] using hshift s
  have hclock' : openExitTime (fun s (_ : Unit) => f (0 + (s : ℝ))) (ball 0 r) () =
      openExitTime (fun s (_ : Unit) => i (η (t₀ + (s : ℝ)))) (ball (i z) r) () := by
    simp only [zero_add, hshift']
    exact openExitTime_shift_sub_ball (fun t => i (η t)) t₀ (i z) r
  have hfin' : openExitTime (fun s (_ : Unit) => f (0 + (s : ℝ))) (ball 0 r) () ≠ ⊤ := by
    rw [hclock']
    exact hfin
  have hend := sInf_outside_eq_forward_openExitTime (fun s => f s)
    (ball 0 r) 0 f.continuous isOpen_ball hfin'
  simp only [zero_add] at hend
  have hset : {t : ℝ | t₀ ≤ t ∧ i (η t) ∉ ball (i z) r} =
      {t : ℝ | t₀ ≤ t ∧ η t ∉ ball z r} := by
    ext t
    simp only [mem_ofPred_eq, hout]
  have htr := exists_ball_subset_firstExitTrace_iff_shifted
    (fun t => i (η t)) t₀ (i z) r R (i.continuous.comp hη) hfin
  have hg : (fun s : ℝ => f s) = (fun s => i (η (t₀ + s)) - i z) := funext hshift'
  rw [hend]
  constructor
  · rintro ⟨_, h⟩
    have h' := htr.mpr (by simpa only [hg, zero_add] using h)
    rw [hset, ← image_image] at h'
    exact (exists_ball_subset_image_isometry_iff i.toIsometryEquiv _ _).mp h'
  · intro h
    refine ⟨hfin', ?_⟩
    have h' := (exists_ball_subset_image_isometry_iff i.toIsometryEquiv _ _).mpr h
    rw [image_image, ← hset] at h'
    have h'' := htr.mp h'
    simpa only [hg, zero_add] using h''

/-- Almost-sure first-hit path identification transfers the failure probability
at every fixed radius. -/
theorem measure_firstHit_forwardExit_failure_eq
    {β : Type*} [MeasurableSpace β] (μ : Measure β)
    (f : β → C(ℝ, EuclideanSpace ℝ (Fin 2))) (η : β → ℝ → ℂ)
    (z : ℂ) (r R : ℝ)
    (hpath : ∀ᵐ ω ∂μ, Continuous (η ω) ∧
      Tendsto (η ω) (cocompact ℝ) (cocompact ℂ) ∧ z ∈ range (η ω) ∧
      ∀ s, f ω s = Complex.orthonormalBasisOneI.repr
        (η ω (MatedCRTHarmonic.GMS4b.hitTime (η ω) z + s) - z)) :
    μ {ω | ¬ (openExitTime (fun s (_ : Unit) => f ω (0 + (s : ℝ))) (ball 0 r) () ≠ ⊤ ∧
      ∃ w, ball w R ⊆ f ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ f ω t ∉ ball 0 r}))} =
    μ {ω | ¬ ∃ w, ball w R ⊆ η ω '' Icc (MatedCRTHarmonic.GMS4b.hitTime (η ω) z)
      (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (η ω) z ≤ t ∧ η ω t ∉ ball z r})} := by
  apply measure_congr
  filter_upwards [hpath] with ω hω
  apply propext
  simpa only [mem_ofPred_eq] using
    not_congr (firstHit_forwardExit_ball_iff (f ω) (η ω) z r R hω.1 hω.2.1 hω.2.2.2)

end LatticeProb
