/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.CaraR3Conn at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CaraR3Hyp

/-!
# EXT-CA node R3: connectedness of `E \ {q}` in the bounded model

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3.R, R3/R6 (input of C6). For the bounded model
`E = sphere 0 1 ∪ cayley '' γ [0,1]` (`CaraR3Hyp.lean`):

* `isPreconnected_modelE_diff_real`: removing the image of a real point `p ≠ γ 0` leaves a
  connected set (the circle minus a point, i.e. two arcs through `1 = cayley ∞`, plus the arc
  attached at `cayley (γ 0)`);
* `isPreconnected_modelE_diff_tip`: removing the tip `cayley (γ 1)` leaves the circle plus a
  half-open arc attached to it.

Own elementary proofs.
-/

noncomputable section

open Set Metric Filter Topology Complex

namespace QuantumZipper

namespace CaraR

open CA CA.Topo CA.Car

variable {γ : ℝ → ℂ}

theorem continuous_cayley_ofReal : Continuous fun x : ℝ => cayley (x : ℂ) :=
  continuousOn_cayley.comp_continuous continuous_ofReal fun x =>
    ne_neg_I_of_Hbar (show (0 : ℝ) ≤ ((x : ℂ)).im by simp)

theorem tendsto_cayley_ofReal_atTop :
    Tendsto (fun x : ℝ => cayley (x : ℂ)) atTop (𝓝 1) := by
  refine tendsto_cayley_cobounded.comp ?_
  rw [← tendsto_norm_atTop_iff_cobounded]
  simp only [norm_real, Real.norm_eq_abs]
  exact tendsto_abs_atTop_atTop

theorem tendsto_cayley_ofReal_atBot :
    Tendsto (fun x : ℝ => cayley (x : ℂ)) atBot (𝓝 1) := by
  refine tendsto_cayley_cobounded.comp ?_
  rw [← tendsto_norm_atTop_iff_cobounded]
  simp only [norm_real, Real.norm_eq_abs]
  exact tendsto_abs_atBot_atTop

theorem ofReal_re_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : ((z.re : ℝ) : ℂ) = z :=
  Complex.ext (by simp) (by simp [hz])

theorem cayley_injOn_Hbar {z w : ℂ} (hz : z ∈ Hbar) (hw : w ∈ Hbar)
    (h : cayley z = cayley w) : z = w :=
  bijOn_cayley_Hbar.injOn hz hw h

theorem ofReal_mem_Hbar' (x : ℝ) : ((x : ℝ) : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((x : ℂ)).im by simp

/-- `E \ {cayley p}` is connected for a real `p` other than the base `γ 0`. -/
theorem isPreconnected_modelE_diff_real (hγc : ContinuousOn γ (Icc 0 1)) (hγ0 : (γ 0).im = 0)
    (hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H) {p : ℝ} (hp : (p : ℂ) ≠ γ 0) :
    IsPreconnected (modelE γ \ {cayley (p : ℂ)}) := by
  set f : ℝ → ℂ := fun x => cayley (x : ℂ) with hf
  set S₁ := insert (1 : ℂ) (f '' Ioi p) with hS₁
  set S₂ := insert (1 : ℂ) (f '' Iio p) with hS₂
  set A := cayley '' (γ '' Icc 0 1) with hA
  have P₁ : IsPreconnected S₁ := by
    refine (isPreconnected_Ioi.image f continuous_cayley_ofReal.continuousOn).subset_closure
      (subset_insert _ _) (insert_subset_iff.2 ⟨?_, subset_closure⟩)
    exact mem_closure_of_tendsto tendsto_cayley_ofReal_atTop
      ((eventually_gt_atTop p).mono fun x hx => mem_image_of_mem f hx)
  have P₂ : IsPreconnected S₂ := by
    refine (isPreconnected_Iio.image f continuous_cayley_ofReal.continuousOn).subset_closure
      (subset_insert _ _) (insert_subset_iff.2 ⟨?_, subset_closure⟩)
    exact mem_closure_of_tendsto tendsto_cayley_ofReal_atBot
      ((eventually_lt_atBot p).mono fun x hx => mem_image_of_mem f hx)
  have P₁₂ : IsPreconnected (S₁ ∪ S₂) := P₁.union 1 (mem_insert _ _) (mem_insert _ _) P₂
  have PA : IsPreconnected A := by
    rw [hA, ← image_comp]
    exact isPreconnected_Icc.image _ (continuousOn_cayley_arc hγc hγ0 hγH)
  have hγ0' : (((γ 0).re : ℝ) : ℂ) = γ 0 := ofReal_re_of_im_eq_zero hγ0
  have hne : (γ 0).re ≠ p := by
    intro h; apply hp; rw [← hγ0', h]
  have hmem : cayley (γ 0) ∈ S₁ ∪ S₂ := by
    rcases lt_or_gt_of_ne hne with h | h
    · right; exact mem_insert_of_mem _ ⟨(γ 0).re, h, by simp only [hf, hγ0']⟩
    · left; exact mem_insert_of_mem _ ⟨(γ 0).re, h, by simp only [hf, hγ0']⟩
  have hmemA : cayley (γ 0) ∈ A := ⟨γ 0, ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩, rfl⟩
  have P := P₁₂.union (cayley (γ 0)) hmem hmemA PA
  convert P using 1
  have hfsph : ∀ x : ℝ, f x ∈ sphere (0 : ℂ) 1 := fun x => cayley_ofReal_mem_sphere x
  have hfne : ∀ x : ℝ, x ≠ p → f x ≠ cayley (p : ℂ) := fun x hx h =>
    hx (by exact_mod_cast cayley_injOn_Hbar (ofReal_mem_Hbar' x) (ofReal_mem_Hbar' p) h)
  have h1ne : (1 : ℂ) ≠ cayley (p : ℂ) := fun h =>
    cayley_ne_one (add_I_ne_zero_of_im_nonneg (ofReal_mem_Hbar' p)) h.symm
  have h1sph : (1 : ℂ) ∈ sphere (0 : ℂ) 1 := by simp
  ext w; constructor
  · rintro ⟨hwE, hwp⟩
    rw [mem_singleton_iff] at hwp
    rcases hwE with hs | hwA
    · left
      by_cases hw1 : w = 1
      · left; rw [hw1]; exact mem_insert _ _
      · have hz := im_cayleyInv_of_mem_sphere hs
        have hw : f (cayleyInv w).re = w := by
          simp only [hf]; rw [ofReal_re_of_im_eq_zero hz, cayley_cayleyInv hw1]
        have hx : (cayleyInv w).re ≠ p := by
          intro h; apply hwp; rw [← hw, h]
        rcases lt_or_gt_of_ne hx with h | h
        · right; exact mem_insert_of_mem _ ⟨_, h, hw⟩
        · left; exact mem_insert_of_mem _ ⟨_, h, hw⟩
    · right; exact hwA
  · rintro ((h | h) | h)
    · rcases h with rfl | ⟨x, hx, rfl⟩
      · exact ⟨Or.inl h1sph, h1ne⟩
      · exact ⟨Or.inl (hfsph x), hfne x (ne_of_gt hx)⟩
    · rcases h with rfl | ⟨x, hx, rfl⟩
      · exact ⟨Or.inl h1sph, h1ne⟩
      · exact ⟨Or.inl (hfsph x), hfne x (ne_of_lt hx)⟩
    · refine ⟨Or.inr h, ?_⟩
      obtain ⟨z, ⟨s, hs, rfl⟩, rfl⟩ := h
      intro hzp
      rw [mem_singleton_iff] at hzp
      have h2 := cayley_injOn_Hbar (arc_subset_Hbar hγ0 hγH ⟨s, hs, rfl⟩) (ofReal_mem_Hbar' p) hzp
      rcases eq_or_lt_of_le hs.1 with h0 | h0
      · subst h0; exact hp h2.symm
      · have := hγH s ⟨h0, hs.2⟩
        rw [h2] at this
        exact not_mem_H_of_im_eq_zero (by simp) this

/-- `E \ {cayley (γ 1)}` (the tip removed) is connected. -/
theorem isPreconnected_modelE_diff_tip (hγc : ContinuousOn γ (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1)) (hγ0 : (γ 0).im = 0) (hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H) :
    IsPreconnected (modelE γ \ {cayley (γ 1)}) := by
  have PS : IsPreconnected (sphere (0 : ℂ) 1) :=
    isPreconnected_sphere (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) _ _
  have PA : IsPreconnected (cayley '' (γ '' Ico 0 1)) := by
    rw [← image_comp]
    exact isPreconnected_Ico.image _
      ((continuousOn_cayley_arc hγc hγ0 hγH).mono Ico_subset_Icc_self)
  have hγ0' : (((γ 0).re : ℝ) : ℂ) = γ 0 := ofReal_re_of_im_eq_zero hγ0
  have hs0 : cayley (γ 0) ∈ sphere (0 : ℂ) 1 := by
    rw [← hγ0']; exact cayley_ofReal_mem_sphere _
  have hA0 : cayley (γ 0) ∈ cayley '' (γ '' Ico 0 1) :=
    ⟨γ 0, ⟨0, ⟨le_rfl, zero_lt_one⟩, rfl⟩, rfl⟩
  have P := PS.union (cayley (γ 0)) hs0 hA0 PA
  convert P using 1
  have h1H : γ 1 ∈ H := hγH 1 ⟨zero_lt_one, le_rfl⟩
  have htip_ball : cayley (γ 1) ∈ ball (0 : ℂ) 1 := cayley_mem_ball h1H
  ext w; constructor
  · rintro ⟨hs | ⟨z, ⟨s, hs, rfl⟩, rfl⟩, hwp⟩
    · left; exact hs
    · right
      rw [mem_singleton_iff] at hwp
      refine ⟨γ s, ⟨s, ⟨hs.1, lt_of_le_of_ne hs.2 ?_⟩, rfl⟩, rfl⟩
      rintro rfl; exact hwp rfl
  · rintro (hs | ⟨z, ⟨s, hs, rfl⟩, rfl⟩)
    · refine ⟨Or.inl hs, ?_⟩
      rintro h; rw [mem_singleton_iff] at h; rw [h] at hs
      rw [mem_sphere] at hs; rw [mem_ball] at htip_ball; linarith
    · refine ⟨Or.inr ⟨γ s, ⟨s, Ico_subset_Icc_self hs, rfl⟩, rfl⟩, ?_⟩
      intro h; rw [mem_singleton_iff] at h
      have hsI : s ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hs
      have h2 := cayley_injOn_Hbar (arc_subset_Hbar hγ0 hγH ⟨s, hsI, rfl⟩) (H_subset_Hbar h1H) h
      have := hγi hsI ⟨zero_le_one, le_rfl⟩ h2
      exact absurd this (ne_of_lt hs.2)

end CaraR

end QuantumZipper
