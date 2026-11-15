import LatticeProb.Topology.NestedExitTrial

/-! # Restarted nested first-exit traces -/

set_option autoImplicit false

open Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- Restarting no later than a finite first exit leaves its real endpoint unchanged. -/
theorem sInf_outside_restart_eq {E : Type*} [TopologicalSpace E]
    (η : ℝ → E) (U : Set E) (t₀ t₁ : ℝ) (hη : Continuous η) (hU : IsOpen U)
    (hfin : openExitTime (fun s (_ : Unit) => η (t₀ + (s : ℝ))) U () ≠ ⊤)
    (hstart : t₀ ≤ t₁)
    (hbefore : t₁ ≤ sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ U}) :
    sInf {t : ℝ | t₁ ≤ t ∧ η t ∉ U} =
      sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ U} := by
  let τ := sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ U}
  have hout : η τ ∉ U := by
    dsimp [τ]
    rw [sInf_outside_eq_forward_openExitTime η U t₀ hη hU hfin]
    exact openExitTime_not_mem (B := fun s (_ : Unit) => η (t₀ + (s : ℝ)))
      (ω := ()) hU (hη.comp (continuous_const.add NNReal.continuous_coe)) hfin
  have hbdd₀ : BddBelow {t : ℝ | t₀ ≤ t ∧ η t ∉ U} := ⟨t₀, fun _ ht => ht.1⟩
  have hbdd₁ : BddBelow {t : ℝ | t₁ ≤ t ∧ η t ∉ U} := ⟨t₁, fun _ ht => ht.1⟩
  apply le_antisymm
  · exact csInf_le hbdd₁ ⟨hbefore, hout⟩
  · refine le_csInf ?_ ?_
    · exact ⟨τ, hbefore, hout⟩
    · intro t ht
      exact csInf_le hbdd₀ ⟨hstart.trans ht.1, ht.2⟩

/-- A restarted exit from an intermediate ball gives a subtrace of the trial
between exits from the inner and outer balls. -/
theorem restarted_nested_exit_trace_subset {E : Type*} [PseudoMetricSpace E]
    (η : ℝ → E) (t₀ : ℝ) (z : E) {r s R : ℝ} (hrs : r ≤ s) (hsR : s ≤ R)
    (hη : Continuous η)
    (hfin : openExitTime (fun u (_ : Unit) => η (t₀ + (u : ℝ))) (ball z R) () ≠ ⊤) :
    let τ := sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ ball z r}
    η '' Icc τ (sInf {t : ℝ | τ ≤ t ∧ η t ∉ ball z s}) ⊆
      η '' Icc τ (sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ ball z R}) := by
  dsimp only
  let B := fun u : ℝ≥0 => fun _ : Unit => η (t₀ + (u : ℝ))
  have hfinS : openExitTime B (ball z s) () ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (monotone_openExitTime_ball B () z hsR)
  have hstart := (firstExitEndpoint_le_of_radius_le η t₀ z (hrs.trans hsR) hη hfin).1
  have hbefore := (firstExitEndpoint_le_of_radius_le η t₀ z hrs hη hfinS).2
  rw [sInf_outside_restart_eq η (ball z s) t₀ _ hη isOpen_ball hfinS hstart hbefore]
  exact image_mono (Icc_subset_Icc le_rfl
    (firstExitEndpoint_le_of_radius_le η t₀ z hsR hη hfin).2)

end LatticeProb
