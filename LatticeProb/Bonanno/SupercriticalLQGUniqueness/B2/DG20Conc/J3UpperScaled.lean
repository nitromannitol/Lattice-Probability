/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J3UpperScaled at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J3UpperGeom
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.ConnectedDomain
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Scale

 










set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

 
theorem j3_far_point {K : Set ℂ} (hK : K.Nontrivial) (z : ℂ) :
    ∃ η > 0, ∃ y ∈ K, η ≤ dist z y ∧ ∀ z' : ℂ, ∃ y' ∈ K, η ≤ dist z' y' := by
  obtain ⟨x, hx, x', hx', hne⟩ := hK
  have hd : 0 < dist x x' := dist_pos.mpr hne
  have key : ∀ z' : ℂ, ∃ y' ∈ K, dist x x' / 2 ≤ dist z' y' := by
    intro z'
    by_cases h : dist x x' / 2 ≤ dist z' x
    · exact ⟨x, hx, h⟩
    · refine ⟨x', hx', ?_⟩
      push_neg at h
      have := dist_triangle_left x x' z'
      linarith
  obtain ⟨y, hy, hzy⟩ := key z
  exact ⟨dist x x' / 2, by positivity, y, hy, hzy, key⟩

 
theorem j3_upper_geometry {U K₁ K₂ : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hc₁ : IsConnected K₁) (hc₂ : IsConnected K₂) (hnt₁ : K₁.Nontrivial) (hnt₂ : K₂.Nontrivial)
    (hsub₁ : K₁ ⊆ U) (hsub₂ : K₂ ⊆ U) :
    ∃ (K : ℕ) (S : Finset (ℤ × ℤ)), ∀ (ξ : ℝ) (f : ℂ → ℝ), Continuous f → ∀ t : ℝ, 0 < t →
      (∀ b ∈ S, ∀ i : Fin 4,
        T20B.mrectLen ξ f K (S6U.siteJ K b i).1 (S6U.siteJ K b i).2 3 1 ≤ t) →
      crossLenIn ξ f U K₁ K₂ ≤ ENNReal.ofReal ((2 * S.card + 1) * 8 * t) := by
  classical
  obtain ⟨q, hq⟩ := exists_admPath_of_open_connected hU hUc hnt₁.nonempty hnt₂.nonempty
    hsub₁ hsub₂
  obtain ⟨δ₀, hδ₀, htube⟩ := exists_uniform_tube_of_admPath hU hq
  obtain ⟨z, hz, w, hw, hpath, -⟩ := hq
  have hqc : ContinuousOn q (Icc 0 1) := hpath.continuousOn
  have hq0 : q 0 = z := hpath.source
  have hq1 : q 1 = w := hpath.target
  obtain ⟨η₁, hη₁, y₁, hy₁, hzy₁, -⟩ := j3_far_point hnt₁ (q 0)
  obtain ⟨η₂, hη₂, y₂, hy₂, hzy₂, -⟩ := j3_far_point hnt₂ (q 1)
  set m : ℝ := min δ₀ (min η₁ η₂) with hm
  have hm0 : 0 < m := lt_min hδ₀ (lt_min hη₁ hη₂)
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (5 / m) (by norm_num : (1 : ℝ) < 2)
  set ρ : ℝ := (2 : ℝ)⁻¹ ^ K with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ2 : ρ * 2 ^ K = 1 := by rw [hρ, ← mul_pow]; norm_num
  have h5ρ : 5 * ρ ≤ m := by
    have : 5 < m * 2 ^ K := by rw [mul_comm]; exact (div_lt_iff₀ hm0).mp hK
    have h2 : (0 : ℝ) < 2 ^ K := by positivity
    have e : 5 * ρ * 2 ^ K = 5 := by rw [mul_assoc, hρ2, mul_one]
    nlinarith
  
  let sc : ℂ → ℂ := fun x => ((ρ⁻¹ : ℝ) : ℂ) * x
  let q' : ℝ → ℂ := fun t => sc (q t)
  have hsc_cont : Continuous sc := continuous_const.mul continuous_id
  have hq'c : ContinuousOn q' (Icc 0 1) := hsc_cont.comp_continuousOn hqc
  have hnorm_sc : ∀ x y : ℂ, dist (sc x) (sc y) = ρ⁻¹ * dist x y := by
    intro x y
    simp only [sc, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hρ0)]
  have hsc_inv : ∀ x : ℂ, ((ρ : ℝ) : ℂ) * sc x = x := by
    intro x; simp only [sc]
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hρ0.ne', Complex.ofReal_one, one_mul]
  have hinv_sc : ∀ x : ℂ, sc (((ρ : ℝ) : ℂ) * x) = x := by
    intro x; simp only [sc]
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hρ0.ne', Complex.ofReal_one, one_mul]
  set U' := sc '' U with hU'
  set K₁' := sc '' K₁ with hK₁'
  set K₂' := sc '' K₂ with hK₂'
  have htube' : ∀ t ∈ Icc (0 : ℝ) 1, closedBall (q' t) 5 ⊆ U' := by
    intro t ht x hx
    refine ⟨((ρ : ℝ) : ℂ) * x, htube t ht ?_, hinv_sc x⟩
    rw [mem_closedBall] at hx ⊢
    have h := hnorm_sc (((ρ : ℝ) : ℂ) * x) (q t)
    rw [hinv_sc x] at h
    have : dist (((ρ : ℝ) : ℂ) * x) (q t) = ρ * dist x (q' t) := by
      have e : dist x (q' t) = ρ⁻¹ * dist (((ρ : ℝ) : ℂ) * x) (q t) := h
      rw [e, ← mul_assoc, mul_inv_cancel₀ hρ0.ne', one_mul]
    rw [this]
    have : ρ * dist x (q' t) ≤ ρ * 5 := mul_le_mul_of_nonneg_left hx hρ0.le
    have hmδ : m ≤ δ₀ := min_le_left _ _
    linarith
  
  have hfar : ∀ {a y : ℂ} {η : ℝ}, η ≤ dist a y → m ≤ η → 5 ≤ dist (sc a) (sc y) := by
    intro a y η h1 h2
    rw [hnorm_sc]
    have : 5 * ρ ≤ dist a y := by linarith
    rw [le_inv_mul_iff₀ hρ0]
    linarith
  have h5₁ : 5 ≤ dist (q' 0) (sc y₁) :=
    hfar hzy₁ ((min_le_right _ _).trans (min_le_left _ _))
  have h5₂ : 5 ≤ dist (q' 1) (sc y₂) :=
    hfar hzy₂ ((min_le_right _ _).trans (min_le_right _ _))
  
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hq'c).isBounded.subset_closedBall 0
  set N : ℤ := ⌈M⌉ + 1 with hN
  set box : Finset (ℤ × ℤ) := Finset.Icc (-N) N ×ˢ Finset.Icc (-N) N with hbox
  set S : Finset (ℤ × ℤ) := box.filter fun b => ∃ t ∈ Icc (0 : ℝ) 1, q' t ∈ T20.dyBlock 0 b
    with hS
  have hSmem : ∀ t ∈ Icc (0 : ℝ) 1, ∀ b, q' t ∈ T20.dyBlock 0 b → b ∈ S := by
    intro t ht b hb
    refine Finset.mem_filter.2 ⟨?_, t, ht, hb⟩
    have hqM : ‖q' t‖ ≤ M := by simpa using hM ⟨t, ht, rfl⟩
    obtain ⟨b1, b2, b3, b4⟩ := S6.mem_dyBlock hb
    simp only [pow_zero, mul_one] at b1 b2 b3 b4
    have hre : |(q' t).re| ≤ M := (Complex.abs_re_le_norm _).trans hqM
    have him : |(q' t).im| ≤ M := (Complex.abs_im_le_norm _).trans hqM
    have hc : M ≤ (⌈M⌉ : ℝ) := Int.le_ceil M
    rw [abs_le] at hre him
    have k1 : -(N : ℝ) ≤ b.1 := by push_cast [hN]; linarith
    have k2 : (b.1 : ℝ) ≤ N := by push_cast [hN]; linarith
    have k3 : -(N : ℝ) ≤ b.2 := by push_cast [hN]; linarith
    have k4 : (b.2 : ℝ) ≤ N := by push_cast [hN]; linarith
    simp only [hbox, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨by exact_mod_cast k1, by exact_mod_cast k2⟩, by exact_mod_cast k3,
      by exact_mod_cast k4⟩
  have hSv : ∀ b ∈ S, ∃ t ∈ Icc (0 : ℝ) 1, q' t ∈ T20.dyBlock 0 b := fun b hb =>
    (Finset.mem_filter.1 hb).2
  refine ⟨K, S, fun ξ f hf t ht hall => ?_⟩
  
  set g : ℂ → ℝ := fun x => f (((ρ : ℝ) : ℂ) * x) with hg
  have hℓ : ENNReal.ofReal ((2 : ℝ) ^ K * t) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hℓ0 : 0 < ENNReal.ofReal ((2 : ℝ) ^ K * t) := ENNReal.ofReal_pos.mpr (by positivity)
  have hR : ∀ b ∈ S, ∀ i : Fin 4, rectLen ξ g (S6U.siteR b i) ≤
      ENNReal.ofReal ((2 : ℝ) ^ K * t) := by
    intro b hb i
    rw [hg, hρ, S6U.rectLen_siteR hf K b i, ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hall b hb i))
  have hunit := j3_upper_geometry_unit hq'c htube' (hc₁.image sc hsc_cont.continuousOn)
    (mem_image_of_mem sc (hq0 ▸ hz)) (mem_image_of_mem sc hy₁) h5₁
    (hc₂.image sc hsc_cont.continuousOn) (mem_image_of_mem sc (hq1 ▸ hw))
    (mem_image_of_mem sc hy₂) h5₂ S hSmem hSv (ξ := ξ) (g := g) hℓ hℓ0 hR
  have hback : ∀ X : Set ℂ, (fun z => ((ρ : ℝ) : ℂ) * z) '' (sc '' X) = X := by
    intro X
    rw [Set.image_image]
    conv_rhs => rw [← Set.image_id X]
    exact Set.image_congr fun x _ => hsc_inv x
  have hscale := crossLenIn_image_mul ξ f U' K₁' K₂' hρ0
  rw [hback U, hback K₁, hback K₂] at hscale
  rw [hscale]
  have hA : (2 * (S.card : ℝ≥0∞) + 1) = ENNReal.ofReal (2 * S.card + 1) := by
    rw [show (2 * (S.card : ℝ) + 1) = ((2 * S.card + 1 : ℕ) : ℝ) by push_cast; ring,
      ENNReal.ofReal_natCast]
    push_cast; ring
  have h8 : (8 : ℝ≥0∞) = ENNReal.ofReal 8 := by norm_num
  refine (mul_le_mul' le_rfl hunit).trans (le_of_eq ?_)
  rw [hA, h8, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul hρ0.le]
  congr 1
  have : ρ * (2 ^ K * t) = t := by rw [← mul_assoc, hρ2, one_mul]
  calc ρ * ((2 * S.card + 1) * (8 * (2 ^ K * t)))
      = (2 * S.card + 1) * 8 * (ρ * (2 ^ K * t)) := by ring
    _ = (2 * S.card + 1) * 8 * t := by rw [this]

end SupercriticalLQGUniqueness.B2.DG20Conc
