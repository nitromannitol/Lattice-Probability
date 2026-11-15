import LatticeProb.LQG.ContourWindowInfiniteContact
import LatticeProb.LQG.PeanosphereTimeTranslation
import LatticeProb.LQG.CoupledAreaClockCells

/-! # Infinite contact for shifted cells -/

set_option autoImplicit false

noncomputable section

open Set MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.RouteM

namespace LatticeProb

/-- A strict window of either translated contour coordinate gives infinitely
many common points of two nonconsecutive shifted cells. -/
theorem infinite_shifted_cell_inter_of_strict_window
    {w : Path2} {η : C(ℝ, ℂ)} {ε θ : ℝ} {i j : ℤ}
    (hε : 0 < ε) (hij : i + 1 < j) (hp : Peanosphere w η)
    (hfinite : ∀ z : ℂ, (η ⁻¹' {z}).Finite) (b : Bool)
    (hwin : dWinLo ε (fun t => if b then (w (t + ε * θ)).2 else (w (t + ε * θ)).1) i j <
      dWinHi ε (fun t => if b then (w (t + ε * θ)).2 else (w (t + ε * θ)).1) i j) :
    ((shiftedCompactCell η ε θ i : Set ℂ) ∩ shiftedCompactCell η ε θ j).Infinite := by
  let X : ℝ → ℝ := fun t => if b then (w t).2 else (w t).1
  let Y : ℝ → ℂ := fun t => η (t + ε * θ)
  have hX : Continuous (fun t => X (t + ε * θ)) := by
    dsimp [X]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  have hmerge : ∀ s t, directRel (fun u => X (u + ε * θ)) s t → Y s = Y t := by
    intro s t h
    have h' := (directRel_time_translate X (ε * θ) s t).mp h
    change η (s + ε * θ) = η (t + ε * θ)
    apply hp.merge
    cases b <;> simp only [X, Bool.false_eq_true, ↓reduceIte] at h'
    · exact Or.inl h'
    · exact Or.inr h'
  have hf : ∀ z : ℂ, (Y ⁻¹' {z}).Finite := by
    intro z
    change ((fun t : ℝ => t + ε * θ) ⁻¹' (η ⁻¹' {z})).Finite
    exact (hfinite z).preimage (fun _ _ _ _ h => add_right_cancel h)
  have hc (k : ℤ) :
      Y '' Icc (ε * ((k : ℝ) - 1)) (ε * k) = shiftedCompactCell η ε θ k := by
    rw [coe_shiftedCompactCell, uIcc_of_le (by
      apply mul_le_mul_of_nonneg_left _ hε.le
      linarith)]
    ext z
    simp only [mem_image, mem_Icc, Y]
    constructor
    · rintro ⟨t, ⟨ht₁, ht₂⟩, rfl⟩
      exact ⟨t + ε * θ, ⟨by nlinarith, by nlinarith⟩, rfl⟩
    · rintro ⟨t, ⟨ht₁, ht₂⟩, rfl⟩
      refine ⟨t - ε * θ, ⟨by nlinarith, by nlinarith⟩, ?_⟩
      simp only [sub_add_cancel]
  have h := infinite_cell_inter_of_strict_contour_window hX hε hij hmerge hf hwin
  rwa [hc i, hc j] at h

/-- The same contact conclusion holds for the actual endpoints of any increasing
time change, without assuming equal increments of the clock. -/
theorem infinite_clocked_cell_inter_of_strict_window
    {w : Path2} {η ζ : C(ℝ, ℂ)} {ε θ : ℝ} {i j : ℤ}
    (ψ : ℝ ≃o ℝ) (hη : ∀ t, η t = ζ (ψ t))
    (hε : 0 < ε) (hij : i + 1 < j) (hp : Peanosphere w η)
    (hfinite : ∀ z : ℂ, (η ⁻¹' {z}).Finite) (b : Bool)
    (hwin : dWinLo ε (fun t => if b then (w (t + ε * θ)).2 else (w (t + ε * θ)).1) i j <
      dWinHi ε (fun t => if b then (w (t + ε * θ)).2 else (w (t + ε * θ)).1) i j) :
    (ζ '' Icc (ψ (ε * ((i : ℝ) - 1 + θ))) (ψ (ε * ((i : ℝ) + θ))) ∩
      ζ '' Icc (ψ (ε * ((j : ℝ) - 1 + θ))) (ψ (ε * ((j : ℝ) + θ)))).Infinite := by
  have h := infinite_shifted_cell_inter_of_strict_window hε hij hp hfinite b hwin
  rw [shifted_cell_eq_image_reparam η ζ ψ hη hε θ i,
    shifted_cell_eq_image_reparam η ζ ψ hη hε θ j] at h
  exact h

end LatticeProb
