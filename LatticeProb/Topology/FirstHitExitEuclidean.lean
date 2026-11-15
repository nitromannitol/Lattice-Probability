import LatticeProb.Topology.FirstHitExitTrace

/-! # First-hit exit traces in Euclidean coordinates -/

set_option autoImplicit false

open Set Filter Metric
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- A surjective isometry preserves existence of an open ball in a set. -/
theorem exists_ball_subset_image_isometry_iff {E F : Type*} [MetricSpace E] [MetricSpace F]
    (i : E ≃ᵢ F) (A : Set E) (R : ℝ) :
    (∃ w, ball w R ⊆ i '' A) ↔ ∃ w, ball w R ⊆ A := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨i.symm w, ?_⟩
    intro x hx
    have h : i x ∈ ball w R := by
      simpa only [mem_ball, ← i.dist_eq, i.apply_symm_apply] using hx
    obtain ⟨y, hy, hxy⟩ := hw h
    exact i.injective hxy ▸ hy
  · rintro ⟨w, hw⟩
    refine ⟨i w, ?_⟩
    intro x hx
    refine ⟨i.symm x, hw ?_, i.apply_symm_apply x⟩
    simpa only [mem_ball, ← i.dist_eq, i.apply_symm_apply] using hx

/-- Planar coordinates identify a first-hit exit trace with the corresponding forward event. -/
theorem firstHit_not_mem_forwardExitOpenBallFailure_iff
    {β : Type*} (f : β → C(ℝ, EuclideanSpace ℝ (Fin 2))) (ω : β)
    (η : ℝ → ℂ) (z : ℂ) (ε : ℝ) (k : ℤ)
    (hη : Continuous η) (hproper : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hz : z ∈ range η)
    (hshift : ∀ s, f ω s = Complex.orthonormalBasisOneI.repr
      (η (MatedCRTHarmonic.GMS4b.hitTime η z + s) - z)) :
    η (MatedCRTHarmonic.GMS4b.hitTime η z) = z ∧
    (ω ∉ forwardExitOpenBallFailure f ε k ↔
      ∃ w, ball w (ε * Real.exp (k : ℝ)) ⊆
        η '' Icc (MatedCRTHarmonic.GMS4b.hitTime η z)
          (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime η z ≤ t ∧
            η t ∉ ball z (Real.exp (k : ℝ))})) := by
  let i := Complex.orthonormalBasisOneI.repr
  let t₀ := MatedCRTHarmonic.GMS4b.hitTime η z
  have hout (t : ℝ) : i (η t) ∉ ball (i z) (Real.exp (k : ℝ)) ↔
      η t ∉ ball z (Real.exp (k : ℝ)) := by
    simp only [mem_ball, i.dist_map]
  have hclock : openExitTime (fun s (_ : Unit) => i (η (t₀ + (s : ℝ))))
      (ball (i z) (Real.exp (k : ℝ))) () =
      openExitTime (fun s (_ : Unit) => η (t₀ + (s : ℝ)))
        (ball z (Real.exp (k : ℝ))) () := by
    unfold openExitTime
    apply le_antisymm
    · refine le_iInf fun t => ?_
      exact iInf_le_of_le ⟨t.1, (hout _).mpr t.2⟩ le_rfl
    · refine le_iInf fun t => ?_
      exact iInf_le_of_le ⟨t.1, (hout _).mp t.2⟩ le_rfl
  have hfin : openExitTime (fun s (_ : Unit) => i (η (t₀ + (s : ℝ))))
      (ball (i z) (Real.exp (k : ℝ))) () ≠ ⊤ := by
    rw [hclock]
    exact (openExitTime_ball_ne_top_of_tendsto_cocompact η hproper t₀ z _).1
  have hshift' : ∀ s, f ω s = i (η (t₀ + s)) - i z := by
    intro s
    simpa only [map_sub] using hshift s
  have hevents := not_mem_forwardExitOpenBallFailure_iff f ω (fun t => i (η t)) t₀
    (i z) ε k (i.continuous.comp hη) hshift' hfin
  have hset : {t : ℝ | t₀ ≤ t ∧ i (η t) ∉ ball (i z) (Real.exp (k : ℝ))} =
      {t : ℝ | t₀ ≤ t ∧ η t ∉ ball z (Real.exp (k : ℝ))} := by
    ext t
    simp only [mem_ofPred_eq, hout]
  refine ⟨MatedCRTHarmonic.GMS4b.hitTime_spec hη hproper hz, ?_⟩
  rw [hevents, hset, ← image_image]
  exact exists_ball_subset_image_isometry_iff i.toIsometryEquiv _ _

end LatticeProb
