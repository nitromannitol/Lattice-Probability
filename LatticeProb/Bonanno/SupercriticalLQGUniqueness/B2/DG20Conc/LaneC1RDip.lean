/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RDip at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RDeg

 










set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Complex Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
theorem laneC1R_eq_of_int_mul_two_pi_I {x y : ℂ}
    (hx : ∃ n : ℤ, x = n * (2 * Real.pi * I)) (hy : ∃ n : ℤ, y = n * (2 * Real.pi * I))
    (hxy : dist x y < 1) : x = y := by
  obtain ⟨n, rfl⟩ := hx
  obtain ⟨n', rfl⟩ := hy
  by_contra hne
  have hnn : n ≠ n' := by
    intro h
    exact hne (by rw [h])
  have hd : dist ((n : ℂ) * (2 * Real.pi * I)) ((n' : ℂ) * (2 * Real.pi * I)) =
      |((n : ℝ) - n')| * (2 * Real.pi) := by
    rw [dist_eq_norm, ← sub_mul, norm_mul]
    have h1 : ‖((n : ℂ) - n')‖ = |((n : ℝ) - n')| := by
      rw [show ((n : ℂ) - n') = (((n : ℝ) - n' : ℝ) : ℂ) by push_cast; ring]
      exact Complex.norm_real _
    have h2 : ‖(2 * Real.pi * I : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      norm_num
    rw [h1, h2]
  have hge : (1 : ℝ) ≤ |((n : ℝ) - n')| := by
    have : (n : ℝ) - n' = ((n - n' : ℤ) : ℝ) := by push_cast; ring
    rw [this]
    have hz : n - n' ≠ 0 := sub_ne_zero.mpr hnn
    exact_mod_cast Int.one_le_abs hz
  have hpi : (1 : ℝ) < 2 * Real.pi := by nlinarith [Real.two_le_pi]
  rw [hd] at hxy
  nlinarith [abs_nonneg ((n : ℝ) - n')]

 
theorem laneC1R_exists_jump_gap {σ Λ : ℝ → ℂ} {B : ℂ → ℂ} {p : ℂ} {E : Set ℂ}
    (hE : IsClosed E) (hσ : ContinuousOn σ (Icc (0 : ℝ) 1))
    (hΛ : ContinuousOn Λ (Icc (0 : ℝ) 1))
    (hΛexp : ∀ u ∈ Icc (0 : ℝ) 1, Complex.exp (Λ u) = σ u - p)
    (hB : ContinuousOn B E) (hBexp : ∀ z ∈ E, Complex.exp (B z) = z - p)
    (hσp : ∀ u ∈ Icc (0 : ℝ) 1, σ u ≠ p)
    (hσ0 : σ 0 ∈ E) (hσ1 : σ 1 = σ 0) (hjump : Λ 1 - Λ 0 ≠ 0) :
    ∃ l u : ℝ, 0 ≤ l ∧ l < u ∧ u ≤ 1 ∧ σ l ∈ E ∧ σ u ∈ E ∧
      (∀ s ∈ Ioo l u, σ s ∉ E) ∧ Λ u - Λ l ≠ B (σ u) - B (σ l) := by
  set F : Set ℝ := Icc (0 : ℝ) 1 ∩ σ ⁻¹' E with hFdef
  have hFc : IsClosed F := hσ.preimage_isClosed_of_isClosed isClosed_Icc hE
  set f : ℝ → ℂ := fun u => Λ u - B (σ u) with hfdef
  have hf : ContinuousOn f F :=
    (hΛ.mono inter_subset_left).sub
      (hB.comp (hσ.mono inter_subset_left) (fun u hu => hu.2))
  have hfint : ∀ u ∈ F, ∃ n : ℤ, f u = n * (2 * Real.pi * I) := by
    intro u hu
    apply Complex.exp_eq_one_iff.mp
    have hne : σ u - p ≠ 0 := sub_ne_zero.mpr (hσp u hu.1)
    simp only [hfdef, Complex.exp_sub, hΛexp u hu.1, hBexp _ hu.2, div_self hne]
  have h0F : (0 : ℝ) ∈ F := ⟨by simp, hσ0⟩
  have h1F : (1 : ℝ) ∈ F := ⟨by simp, by simpa [hσ1] using hσ0⟩
  set G : Set ℝ := F ∩ f ⁻¹' {f 0} with hGdef
  have hGc : IsClosed G := hf.preimage_isClosed_of_isClosed hFc isClosed_singleton
  have h0G : (0 : ℝ) ∈ G := ⟨h0F, rfl⟩
  have hGsub : G ⊆ Icc (0 : ℝ) 1 := fun u hu => hu.1.1
  have hGbdd : BddAbove G := ⟨1, fun u hu => (hGsub hu).2⟩
  set l : ℝ := sSup G with hldef
  have hlG : l ∈ G := hGc.csSup_mem ⟨0, h0G⟩ hGbdd
  have hle : ∀ u ∈ G, u ≤ l := fun u hu => le_csSup hGbdd hu
  have hf1 : f 1 ≠ f 0 := by
    intro h
    apply hjump
    have : Λ 1 - B (σ 1) = Λ 0 - B (σ 0) := h
    rw [hσ1] at this
    linear_combination this
  have hfl : f l = f 0 := hlG.2
  
  obtain ⟨δ, hδ, hloc⟩ : ∃ δ > 0, ∀ u ∈ F, dist u l < δ → f u = f l := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousWithinAt_iff.mp (hf l hlG.1) 1 one_pos
    exact ⟨δ, hδ, fun u hu hd =>
      laneC1R_eq_of_int_mul_two_pi_I (hfint u hu) (hfint l hlG.1) (h hu hd)⟩
  have hl1 : l + δ ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have hl1' : l ≤ 1 := (hGsub hlG).2
    have hd : dist (1 : ℝ) l < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith
    exact hf1 ((hloc 1 h1F hd).trans hfl)
  set K' : Set ℝ := F ∩ Icc (l + δ / 2) 1 with hK'def
  have hK'c : IsClosed K' := hFc.inter isClosed_Icc
  have h1K' : (1 : ℝ) ∈ K' := ⟨h1F, by linarith, le_rfl⟩
  have hK'bdd : BddBelow K' := ⟨l + δ / 2, fun u hu => hu.2.1⟩
  set u : ℝ := sInf K' with hudef
  have huK' : u ∈ K' := hK'c.csInf_mem ⟨1, h1K'⟩ hK'bdd
  have hge : ∀ s ∈ K', u ≤ s := fun s hs => csInf_le hK'bdd hs
  have hl0 : 0 ≤ l := (hGsub hlG).1
  have hlu : l < u := by linarith [huK'.2.1]
  refine ⟨l, u, hl0, hlu, huK'.2.2, hlG.1.2, huK'.1.2, ?_, ?_⟩
  · intro s hs hsE
    have hsF : s ∈ F := ⟨⟨by linarith [hs.1], by linarith [hs.2, huK'.2.2]⟩, hsE⟩
    by_cases hsd : s < l + δ
    · have hd : dist s l < δ := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
        linarith
      have : s ∈ G := ⟨hsF, (hloc s hsF hd).trans hfl⟩
      linarith [hle s this, hs.1]
    · push Not at hsd
      have : s ∈ K' := ⟨hsF, by linarith, by linarith [hs.2, huK'.2.2]⟩
      linarith [hge s this, hs.2]
  · intro h
    have hfu : f u = f l := by
      simp only [hfdef]
      linear_combination h
    have : u ∈ G := ⟨huK'.1, hfu.trans hfl⟩
    linarith [hle u this]

end SupercriticalLQGUniqueness.B2.DG20Conc
