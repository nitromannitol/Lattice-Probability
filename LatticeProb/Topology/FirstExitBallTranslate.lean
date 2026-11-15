import LatticeProb.Topology.FirstExitTraceTranslate
import LatticeProb.Topology.FirstExitBallOpen

/-! # Translation of first-exit ball containment -/

set_option autoImplicit false

open Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- Translations preserve the existence of a ball of a specified radius in a set. -/
theorem exists_ball_subset_image_add_iff {E : Type*} [NormedAddCommGroup E]
    (A : Set E) (z : E) (R : ℝ) :
    (∃ w, ball w R ⊆ (fun x : E => x + z) '' A) ↔
      ∃ w, ball w R ⊆ A := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w - z, ?_⟩
    intro x hx
    have hx' : x + z ∈ ball w R := by
      simp only [mem_ball, dist_eq_norm] at hx ⊢
      convert hx using 1; congr 1; abel
    obtain ⟨y, hy, heq⟩ := hw hx'
    have : y = x := add_right_cancel heq
    simpa only [this] using hy
  · rintro ⟨w, hw⟩
    refine ⟨w + z, ?_⟩
    intro x hx
    refine ⟨x - z, hw ?_, sub_add_cancel x z⟩
    simp only [mem_ball, dist_eq_norm] at hx ⊢
    convert hx using 1; congr 1; abel

/-- Ball containment in a finite first-exit trace is preserved by translating the path. -/
theorem exists_ball_subset_firstExitTrace_iff_shifted {E : Type*} [NormedAddCommGroup E]
    (η : ℝ → E) (t₀ : ℝ) (z : E) (r R : ℝ) (hη : Continuous η)
    (hfin : openExitTime (fun s (_ : Unit) => η (t₀ + (s : ℝ))) (ball z r) () ≠ ⊤) :
    (∃ w, ball w R ⊆ η '' Icc t₀ (sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ ball z r})) ↔
      ∃ w, ball w R ⊆ (fun s : ℝ => η (t₀ + s) - z) ''
        Icc 0 ((openExitTime (fun s (_ : Unit) => η (t₀ + (s : ℝ)) - z)
          (ball 0 r) ()).toNNReal : ℝ) := by
  rw [image_Icc_sInf_outside_eq_shifted η t₀ z r hη hfin]
  exact exists_ball_subset_image_add_iff _ z R

/-- The shifted finite-exit event agrees with ball containment in the original trace. -/
theorem not_mem_forwardExitOpenBallFailure_iff {β : Type*} {d : ℕ}
    (f : β → C(ℝ, EuclideanSpace ℝ (Fin d))) (ω : β)
    (η : ℝ → EuclideanSpace ℝ (Fin d)) (t₀ : ℝ)
    (z : EuclideanSpace ℝ (Fin d)) (ε : ℝ) (k : ℤ)
    (hη : Continuous η) (hshift : ∀ s, f ω s = η (t₀ + s) - z)
    (hfin : openExitTime (fun s (_ : Unit) => η (t₀ + (s : ℝ)))
      (ball z (Real.exp (k : ℝ))) () ≠ ⊤) :
    ω ∉ forwardExitOpenBallFailure f ε k ↔
      ∃ w, ball w (ε * Real.exp (k : ℝ)) ⊆
        η '' Icc t₀ (sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ ball z (Real.exp (k : ℝ))}) := by
  have hg : (fun s : ℝ => f ω s) = (fun s => η (t₀ + s) - z) := funext hshift
  have hclock : openExitTime (fun s (_ : Unit) => f ω (0 + (s : ℝ)))
      (ball 0 (Real.exp (k : ℝ))) () =
      openExitTime (fun s (_ : Unit) => η (t₀ + (s : ℝ)))
        (ball z (Real.exp (k : ℝ))) () := by
    simp only [zero_add, hshift]
    exact openExitTime_shift_sub_ball η t₀ z _
  have hfin' : openExitTime (fun s (_ : Unit) => f ω (0 + (s : ℝ)))
      (ball 0 (Real.exp (k : ℝ))) () ≠ ⊤ := by rw [hclock]; exact hfin
  have hend := sInf_outside_eq_forward_openExitTime (fun s => f ω s)
    (ball 0 (Real.exp (k : ℝ))) 0 (f ω).continuous isOpen_ball hfin'
  simp only [zero_add] at hend
  simp only [forwardExitOpenBallFailure, mem_ofPred_eq, not_not]
  rw [hend]
  constructor
  · rintro ⟨_, h⟩
    apply (exists_ball_subset_firstExitTrace_iff_shifted η t₀ z _ _ hη hfin).mpr
    simpa only [hshift, zero_add, hg] using h
  · intro h
    refine ⟨hfin', ?_⟩
    have h' := (exists_ball_subset_firstExitTrace_iff_shifted η t₀ z _ _ hη hfin).mp h
    simpa only [hshift, zero_add, hg] using h'

end LatticeProb
