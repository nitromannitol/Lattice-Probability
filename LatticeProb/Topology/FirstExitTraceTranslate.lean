import LatticeProb.Topology.RealFirstExitClock

/-! # Translation of forward first-exit traces -/

set_option autoImplicit false

open Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- Time and space translation preserve the forward exit clock from a ball. -/
theorem openExitTime_shift_sub_ball {E : Type*} [NormedAddCommGroup E]
    (η : ℝ → E) (t₀ : ℝ) (z : E) (r : ℝ) :
    openExitTime (fun s (_ : Unit) => η (t₀ + (s : ℝ)) - z) (ball 0 r) () =
      openExitTime (fun s (_ : Unit) => η (t₀ + (s : ℝ))) (ball z r) () := by
  apply le_antisymm
  · apply le_iInf
    intro t
    apply openExitTime_le_of_not_mem
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using t.property
  · apply le_iInf
    intro t
    apply openExitTime_le_of_not_mem
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using t.property

/-- A time-shifted trace, translated by its spatial center, is the original trace. -/
theorem image_Icc_shift_sub_add {E : Type*} [AddCommGroup E]
    (η : ℝ → E) (t₀ δ : ℝ) (z : E) :
    (fun x : E => x + z) '' ((fun s : ℝ => η (t₀ + s) - z) '' Icc 0 δ) =
      η '' Icc t₀ (t₀ + δ) := by
  ext x
  constructor
  · rintro ⟨y, ⟨s, ⟨hs0, hsδ⟩, rfl⟩, rfl⟩
    refine ⟨t₀ + s, ⟨?_, ?_⟩, ?_⟩
    · linarith
    · linarith
    · simp only [sub_add_cancel]
  · rintro ⟨t, ⟨ht₀, htδ⟩, rfl⟩
    refine ⟨η t - z, ⟨t - t₀, ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · linarith
    · linarith
    · change η (t₀ + (t - t₀)) - z = η t - z
      have heq : t₀ + (t - t₀) = t := by linarith
      rw [heq]
    · simp only [sub_add_cancel]

/-- At a finite exit, the first outside real-time trace is the translated shifted trace. -/
theorem image_Icc_sInf_outside_eq_shifted {E : Type*} [NormedAddCommGroup E]
    (η : ℝ → E) (t₀ : ℝ) (z : E) (r : ℝ) (hη : Continuous η)
    (hfin : openExitTime (fun s (_ : Unit) => η (t₀ + (s : ℝ))) (ball z r) () ≠ ⊤) :
    η '' Icc t₀ (sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ ball z r}) =
      (fun x : E => x + z) ''
        ((fun s : ℝ => η (t₀ + s) - z) ''
          Icc 0 ((openExitTime (fun s (_ : Unit) => η (t₀ + (s : ℝ)) - z)
            (ball 0 r) ()).toNNReal : ℝ)) := by
  rw [sInf_outside_eq_forward_openExitTime η (ball z r) t₀ hη isOpen_ball hfin]
  rw [openExitTime_shift_sub_ball]
  exact (image_Icc_shift_sub_add η t₀ _ z).symm

end LatticeProb
