import LatticeProb.LQG.MatedCRTSideBarriers
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite

/-! # Local finiteness from real-time lower excursions -/

set_option autoImplicit false

noncomputable section

open Set

namespace MatedCRTHarmonic.MatedCRT

/-- Lower excursions of both coordinates on both time tails imply local finiteness
for every positive mesh. -/
theorem locallyFinite_of_realTailLows {ε : ℝ} {ω : Path2} (hε : 0 < ε)
    (hLplus : ∀ M T : ℝ, ∃ t ≥ T, (ω t).1 < M)
    (hLminus : ∀ M T : ℝ, ∃ t ≤ -T, (ω t).1 < M)
    (hRplus : ∀ M T : ℝ, ∃ t ≥ T, (ω t).2 < M)
    (hRminus : ∀ M T : ℝ, ∃ t ≤ -T, (ω t).2 < M) :
    IsLocallyFinite ε ω := by
  intro x
  obtain ⟨a, ha⟩ := eventually_not_sideCond_right
    (continuous_fst.comp ω.continuous) hε x hLplus
  obtain ⟨b, hb⟩ := eventually_not_sideCond_right
    (continuous_snd.comp ω.continuous) hε x hRplus
  obtain ⟨c, hc⟩ := eventually_not_sideCond_left
    (continuous_fst.comp ω.continuous) hε x hLminus
  obtain ⟨d, hd⟩ := eventually_not_sideCond_left
    (continuous_snd.comp ω.continuous) hε x hRminus
  let lo : ℤ := min (min (-(c : ℤ)) (-(d : ℤ))) (x - 1)
  let hi : ℤ := max (max (a : ℤ) (b : ℤ)) (x + 1)
  have hbounds : ∀ e : Edge ε ω, e.1.1 = x ∨ e.1.2.1 = x →
      e.1.1 ∈ Icc lo hi ∧ e.1.2.1 ∈ Icc lo hi := by
    intro e he
    rcases e.2 with ⟨horder, hsucc | ⟨_, hside⟩⟩
    · rcases he with he | he <;> simp only [mem_Icc] <;> dsimp [lo, hi] <;> omega
    · by_cases htag : e.1.2.2
      · simp only [htag, ↓reduceIte] at hside
        rcases he with he | he
        · have hh : e.1.2.1 ≤ (b : ℤ) := by
            by_contra hn
            exact hb e.1.2.1 (by omega) (by simpa only [he, Function.comp_def] using hside)
          simp only [mem_Icc]
          dsimp [lo, hi]
          omega
        · have hh : -(d : ℤ) ≤ e.1.1 := by
            by_contra hn
            exact hd e.1.1 (by omega) (by simpa only [he, Function.comp_def] using hside)
          simp only [mem_Icc]
          dsimp [lo, hi]
          omega
      · simp only [htag, Bool.false_eq_true, ↓reduceIte] at hside
        rcases he with he | he
        · have hh : e.1.2.1 ≤ (a : ℤ) := by
            by_contra hn
            exact ha e.1.2.1 (by omega) (by simpa only [he, Function.comp_def] using hside)
          simp only [mem_Icc]
          dsimp [lo, hi]
          omega
        · have hh : -(c : ℤ) ≤ e.1.1 := by
            by_contra hn
            exact hc e.1.1 (by omega) (by simpa only [he, Function.comp_def] using hside)
          simp only [mem_Icc]
          dsimp [lo, hi]
          omega
  have hprod : (Icc lo hi ×ˢ (Icc lo hi ×ˢ (univ : Set Bool))).Finite :=
    (finite_Icc lo hi).prod ((finite_Icc lo hi).prod finite_univ)
  have himage : (Subtype.val '' {e : Edge ε ω | e.1.1 = x ∨ e.1.2.1 = x}).Finite :=
    hprod.subset (by
      rintro _ ⟨e, he, rfl⟩
      obtain ⟨h₁, h₂⟩ := hbounds e he
      exact ⟨h₁, h₂, trivial⟩)
  exact himage.of_finite_image (fun _ _ _ _ h => Subtype.val_injective h)

end MatedCRTHarmonic.MatedCRT
