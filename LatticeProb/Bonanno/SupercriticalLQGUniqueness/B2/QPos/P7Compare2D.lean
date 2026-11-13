/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P7Compare2D at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P7Compare1D
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePhi

 









set_option autoImplicit false
noncomputable section

open MeasureTheory Real Finset
open scoped RealInnerProductSpace
open LQGMetric LQGMetric.HeatSq LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.QPos.P7

 
def siteZ (n : ℕ) (v : DGFFSite n) : ℂ := ⟨(v.1.1 : ℝ) / Nn n, (v.1.2 : ℝ) / Nn n⟩

lemma integrable_complex_re_mul_im {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun y : ℂ => f y.re * g y.im) := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm).integrable_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding (g := fun y : ℂ => f y.re * g y.im)
  rw [← h, Measure.volume_eq_prod]
  exact hf.mul_prod hg

 
lemma norm_toLp_sub_smul_sq {f g : ℝ × ℂ → ℝ} (hf : MemLp f 2 (volume : Measure (ℝ × ℂ)))
    (hg : MemLp g 2 (volume : Measure (ℝ × ℂ))) (c : ℝ) :
    ‖hf.toLp f - c • hg.toLp g‖ ^ 2 = ∫ p, (f p - c * g p) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (c • hg.toLp g), Lp.coeFn_smul c (hg.toLp g),
    hf.coeFn_toLp, hg.coeFn_toLp] with p h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4, real_inner_self_eq_norm_sq, Real.norm_eq_abs,
    sq_abs, smul_eq_mul]

 
def cSlice : ℝ := 2 * π * cmp1Const * (Real.sqrt π + (Real.sqrt π)⁻¹)

lemma cSlice_nonneg : 0 ≤ cSlice := by
  unfold cSlice; have := cmp1Const_nonneg; positivity

lemma sqrt_factor' {r : ℝ} (hr : 0 < r) :
    (Real.sqrt (r ^ 2))⁻¹ * (Real.sqrt (π / r ^ 2) / 2 + (Real.sqrt (2 * π * (2 * r ^ 2)))⁻¹) =
      (Real.sqrt π + (Real.sqrt π)⁻¹) / (2 * r ^ 2) := by
  have hπ := Real.pi_pos
  have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
  rw [Real.sqrt_sq hr.le, Real.sqrt_div' π (sq_nonneg r), Real.sqrt_sq hr.le,
    show 2 * π * (2 * r ^ 2) = (2 * r) ^ 2 * π by ring, Real.sqrt_mul (sq_nonneg _) π,
    Real.sqrt_sq (by positivity)]
  field_simp

 
theorem slice_mid_le {n : ℕ} (hn : 4 ≤ n) (v : DGFFSite n)
    (hv1 : |(v.1.1 : ℝ)| ≤ 4 / 5 * Nn n) (hv2 : |(v.1.2 : ℝ)| ≤ 4 / 5 * Nn n)
    {t : ℝ} (ht1 : ((2 : ℝ)⁻¹ ^ n) ^ 2 ≤ t) (ht2 : t ≤ 1) :
    ∫ y : ℂ, (fKer n v (t, y) - Real.sqrt π * phiKernel ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0)
        (siteZ n v) (t, y)) ^ 2 ≤
      cSlice * (4 * (((Nn n : ℝ) ^ 4) * t ^ 3)⁻¹ + 2 * (((Nn n : ℝ) ^ 2) * t ^ 2)⁻¹ + 1 / 2) := by
  set N := Nn n with hNdef
  have hN0 : 0 < N := Nn_pos n
  have hN16 : 16 ≤ N := by
    simp only [N, Nn]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hNp : (0 : ℝ) < N := by linarith
  have hπ := Real.pi_pos
  have hNinv : ((2 : ℝ)⁻¹ ^ n) ^ 2 = 1 / (N : ℝ) ^ 2 := by
    simp only [N, Nn]; push_cast; rw [inv_pow, inv_pow, ← one_div]
  rw [hNinv] at ht1
  have ht : 0 < t := lt_of_lt_of_le (by positivity) ht1
  set s := t / 2 with hsdef
  have hs : 0 < s := by positivity
  have hs1 : 1 / (2 * (N : ℝ) ^ 2) ≤ s := by
    rw [hsdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    rw [div_le_iff₀ (by positivity)] at ht1; linarith
  have hs2 : s ≤ 1 / 2 := by linarith
  have hN10 : 10 ≤ N := by omega
  set x := siteZ n v
  have hxre : x.re = (v.1.1 : ℝ) / N := rfl
  have hxim : x.im = (v.1.2 : ℝ) / N := rfl
  
  have hslice : ∀ y : ℂ, fKer n v (t, y) - Real.sqrt π * phiKernel ((2 : ℝ)⁻¹ ^ n)
      ((2 : ℝ)⁻¹ ^ 0) x (t, y) = Real.sqrt π * (prof N s v.1.1 y.re * prof N s v.1.2 y.im -
        gauss1 s ((v.1.1 : ℝ) / N - y.re) * gauss1 s ((v.1.2 : ℝ) / N - y.im)) := by
    intro y
    have hmem1 : ((t, y) : ℝ × ℂ) ∈ {q : ℝ × ℂ | 0 < q.1} := ht
    have hmem2 : ((t, y) : ℝ × ℂ) ∈ Set.Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ 0) ^ 2) ×ˢ
        (Set.univ : Set ℂ) := by
      refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
      · rw [hNinv]; exact ht1
      · simp only [pow_zero, one_pow]; exact ht2
    unfold fKer phiKernel
    rw [Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem2]
    simp only
    rw [← gauss1_mul_gauss1 (t / 2) (by positivity) x y, hxre, hxim]
    ring
  simp_rw [hslice]
  set A1 := prof N s v.1.1
  set A2 := prof N s v.1.2
  set B1 : ℝ → ℝ := fun r => gauss1 s ((v.1.1 : ℝ) / N - r)
  set B2 : ℝ → ℝ := fun r => gauss1 s ((v.1.2 : ℝ) / N - r)
  have hpt : ∀ y : ℂ, (Real.sqrt π * (A1 y.re * A2 y.im - B1 y.re * B2 y.im)) ^ 2 ≤
      2 * π * ((A1 y.re - B1 y.re) ^ 2 * A2 y.im ^ 2) +
        2 * π * (B1 y.re ^ 2 * (A2 y.im - B2 y.im) ^ 2) := by
    intro y
    rw [mul_pow, Real.sq_sqrt hπ.le]
    have e : A1 y.re * A2 y.im - B1 y.re * B2 y.im =
        (A1 y.re - B1 y.re) * A2 y.im + B1 y.re * (A2 y.im - B2 y.im) := by ring
    rw [e]
    nlinarith [sq_nonneg ((A1 y.re - B1 y.re) * A2 y.im - B1 y.re * (A2 y.im - B2 y.im))]
  
  have hmA1 : Measurable A1 := measurable_prof_comp N v.1.1 measurable_const measurable_id
  have hmA2 : Measurable A2 := measurable_prof_comp N v.1.2 measurable_const measurable_id
  have hA2sq : Integrable (fun r => A2 r ^ 2) := by
    have := (integrable_pc N (fun c => ((N : ℝ) * qker N s v.1.2 c) ^ 2))
    refine this.congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [A2, prof_eq_pc]; rw [sq, pc_mul_pc hN0]; simp [sq]
  have hB1sq : Integrable (fun r => B1 r ^ 2) := integrable_gauss1_sub_sq hs _
  have hdiff : ∀ (A B : ℝ → ℝ), Measurable A → Measurable B → Integrable (fun r => A r ^ 2) →
      Integrable (fun r => B r ^ 2) → Integrable (fun r => (A r - B r) ^ 2) := by
    intro A B hA hB hA2 hB2
    refine Integrable.mono' ((hA2.add hB2).const_mul 2) ((hA.sub hB).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (A r + B r)]
  have hA1sq : Integrable (fun r => A1 r ^ 2) := by
    have := (integrable_pc N (fun c => ((N : ℝ) * qker N s v.1.1 c) ^ 2))
    refine this.congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [A1, prof_eq_pc]; rw [sq, pc_mul_pc hN0]; simp [sq]
  have hB2sq : Integrable (fun r => B2 r ^ 2) := integrable_gauss1_sub_sq hs _
  have hmB1 : Measurable B1 := by
    unfold gauss1 at *; simp only [B1]; unfold gauss1; fun_prop
  have hmB2 : Measurable B2 := by
    simp only [B2]; unfold gauss1; fun_prop
  have hD1 := hdiff A1 B1 hmA1 hmB1 hA1sq hB1sq
  have hD2 := hdiff A2 B2 hmA2 hmB2 hA2sq hB2sq
  have hI1 : Integrable (fun y : ℂ => 2 * π * ((A1 y.re - B1 y.re) ^ 2 * A2 y.im ^ 2)) :=
    (integrable_complex_re_mul_im hD1 hA2sq).const_mul _
  have hI2 : Integrable (fun y : ℂ => 2 * π * (B1 y.re ^ 2 * (A2 y.im - B2 y.im) ^ 2)) :=
    (integrable_complex_re_mul_im hB1sq hD2).const_mul _
  have hmono : ∫ y : ℂ, (Real.sqrt π * (A1 y.re * A2 y.im - B1 y.re * B2 y.im)) ^ 2 ≤
      ∫ y : ℂ, (2 * π * ((A1 y.re - B1 y.re) ^ 2 * A2 y.im ^ 2) +
        2 * π * (B1 y.re ^ 2 * (A2 y.im - B2 y.im) ^ 2)) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _) (hI1.add hI2)
      (Filter.Eventually.of_forall hpt)
  refine hmono.trans ?_
  rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul,
    integral_complex_re_mul_im (fun r => (A1 r - B1 r) ^ 2) (fun r => A2 r ^ 2),
    integral_complex_re_mul_im (fun r => B1 r ^ 2) (fun r => (A2 r - B2 r) ^ 2)]
  
  have hc1 := integral_prof_sub_gauss_sq_le hN10 hv1 hs1 hs2
  have hc2 := integral_prof_sub_gauss_sq_le hN10 hv2 hs1 hs2
  have hA2v : ∫ r, A2 r ^ 2 ≤ Real.sqrt (π / (t / 2)) / 2 := by
    have e : ∫ r, A2 r ^ 2 = N * qker N t v.1.2 v.1.2 := by
      simp only [A2, sq]; rw [integral_prof_mul N hN0, show s + s = t by simp [hsdef]]
    rw [e]
    refine (mul_qker_diag_le N hN0 ht.le v.1.2).trans ?_
    refine le_trans (le_of_eq ?_) (sum_modes_exp_le N (show 0 < t / 2 by positivity))
    exact sum_congr rfl fun k _ => by ring_nf
  have hB1v : ∫ r, B1 r ^ 2 = (Real.sqrt (2 * π * t))⁻¹ := by
    simp only [B1]; rw [integral_gauss1_sub_sq hs]
    unfold gauss1; simp [hsdef]; ring_nf
  have hX : 0 ≤ ((N : ℝ) ^ 4 * s ^ 2)⁻¹ + ((N : ℝ) ^ 2 * s)⁻¹ + s := by positivity
  have hcm := cmp1Const_nonneg
  have hD1v : ∫ r, (A1 r - B1 r) ^ 2 ≤
      cmp1Const * (Real.sqrt s)⁻¹ * (((N : ℝ) ^ 4 * s ^ 2)⁻¹ + ((N : ℝ) ^ 2 * s)⁻¹ + s) := hc1
  have hD2v : ∫ r, (A2 r - B2 r) ^ 2 ≤
      cmp1Const * (Real.sqrt s)⁻¹ * (((N : ℝ) ^ 4 * s ^ 2)⁻¹ + ((N : ℝ) ^ 2 * s)⁻¹ + s) := hc2
  set E := cmp1Const * (Real.sqrt s)⁻¹ * (((N : ℝ) ^ 4 * s ^ 2)⁻¹ + ((N : ℝ) ^ 2 * s)⁻¹ + s)
  have hE0 : 0 ≤ E := by positivity
  have hA20 : 0 ≤ ∫ r, A2 r ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hB10 : 0 ≤ ∫ r, B1 r ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hstep : 2 * π * ((∫ r, (A1 r - B1 r) ^ 2) * ∫ r, A2 r ^ 2) +
      2 * π * ((∫ r, B1 r ^ 2) * ∫ r, (A2 r - B2 r) ^ 2) ≤
      2 * π * E * (Real.sqrt (π / (t / 2)) / 2 + (Real.sqrt (2 * π * t))⁻¹) := by
    have h1 : (∫ r, (A1 r - B1 r) ^ 2) * ∫ r, A2 r ^ 2 ≤ E * (Real.sqrt (π / (t / 2)) / 2) :=
      mul_le_mul hD1v hA2v hA20 hE0
    have h2 : (∫ r, B1 r ^ 2) * ∫ r, (A2 r - B2 r) ^ 2 ≤ (Real.sqrt (2 * π * t))⁻¹ * E := by
      rw [hB1v]; exact mul_le_mul_of_nonneg_left hD2v (by positivity)
    nlinarith
  refine hstep.trans (le_of_eq ?_)
  
  obtain ⟨r, hr, hsr⟩ : ∃ r : ℝ, 0 < r ∧ s = r ^ 2 :=
    ⟨Real.sqrt s, Real.sqrt_pos.mpr hs, (Real.sq_sqrt hs.le).symm⟩
  have htr : t = 2 * r ^ 2 := by rw [← hsr, hsdef]; ring
  have key := sqrt_factor' hr
  simp only [E]
  rw [hsr, htr, show 2 * r ^ 2 / 2 = r ^ 2 by ring]
  calc 2 * π * (cmp1Const * (Real.sqrt (r ^ 2))⁻¹ *
        (((N : ℝ) ^ 4 * (r ^ 2) ^ 2)⁻¹ + ((N : ℝ) ^ 2 * r ^ 2)⁻¹ + r ^ 2)) *
        (Real.sqrt (π / r ^ 2) / 2 + (Real.sqrt (2 * π * (2 * r ^ 2)))⁻¹)
      = 2 * π * cmp1Const * (((N : ℝ) ^ 4 * (r ^ 2) ^ 2)⁻¹ + ((N : ℝ) ^ 2 * r ^ 2)⁻¹ + r ^ 2) *
          ((Real.sqrt (r ^ 2))⁻¹ * (Real.sqrt (π / r ^ 2) / 2 +
            (Real.sqrt (2 * π * (2 * r ^ 2)))⁻¹)) := by ring
    _ = 2 * π * cmp1Const * (((N : ℝ) ^ 4 * (r ^ 2) ^ 2)⁻¹ + ((N : ℝ) ^ 2 * r ^ 2)⁻¹ + r ^ 2) *
          ((Real.sqrt π + (Real.sqrt π)⁻¹) / (2 * r ^ 2)) := by rw [key]
    _ = _ := by unfold cSlice; field_simp; ring

lemma phiKernel_eq_zero_of_not_mem {n : ℕ} {x : ℂ} {t : ℝ}
    (ht : t ∉ Set.Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ 0) ^ 2)) (y : ℂ) :
    phiKernel ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0) x (t, y) = 0 := by
  unfold phiKernel
  exact Set.indicator_of_notMem (fun h => ht h.1) _

 
lemma slice_fKer_only {n : ℕ} (v : DGFFSite n) {t : ℝ}
    (ht : t ∉ Set.Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ 0) ^ 2)) :
    ∫ y : ℂ, (fKer n v (t, y) - Real.sqrt π * phiKernel ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0)
        (siteZ n v) (t, y)) ^ 2 =
      if 0 < t then π * (((Nn n : ℝ) * qker (Nn n) t v.1.1 v.1.1) *
        ((Nn n : ℝ) * qker (Nn n) t v.1.2 v.1.2)) else 0 := by
  simp_rw [phiKernel_eq_zero_of_not_mem ht, mul_zero, sub_zero, sq]
  exact integral_fKer_mul_slice n v v t

 
lemma slice_short_le {n : ℕ} (v : DGFFSite n) {t : ℝ} (ht0 : 0 < t)
    (ht : t ∉ Set.Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ 0) ^ 2)) :
    ∫ y : ℂ, (fKer n v (t, y) - Real.sqrt π * phiKernel ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0)
        (siteZ n v) (t, y)) ^ 2 ≤ π * (Nn n : ℝ) ^ 2 := by
  rw [slice_fKer_only v ht, if_pos ht0]
  have hN0 := Nn_pos n
  have hNp : (0 : ℝ) < Nn n := by exact_mod_cast hN0
  have h1 := qker_diag_le_one (Nn n) hN0 ht0.le (site_fst_mem n v)
  have h2 := qker_diag_le_one (Nn n) hN0 ht0.le (site_snd_mem n v)
  have h1' := qker_diag_nonneg (Nn n) hN0 t v.1.1
  have h2' := qker_diag_nonneg (Nn n) hN0 t v.1.2
  have hπ := Real.pi_pos
  have : ((Nn n : ℝ) * qker (Nn n) t v.1.1 v.1.1) * ((Nn n : ℝ) * qker (Nn n) t v.1.2 v.1.2) ≤
      (Nn n : ℝ) * (Nn n : ℝ) :=
    mul_le_mul (by nlinarith) (by nlinarith) (by positivity) (by positivity)
  nlinarith

 
lemma mul_qker_diag_le_exp (N : ℕ) (hN : 0 < N) {t : ℝ} (ht : 1 ≤ t) (a : ℤ) :
    (N : ℝ) * qker N t a a ≤ Real.sqrt π * Real.exp (-t / 4) := by
  refine (mul_qker_diag_le N hN (by linarith) a).trans ?_
  have hb : ∀ k ∈ modes N, Real.exp (-t * ((k : ℝ) ^ 2 / 2)) ≤
      Real.exp (-t / 4) * Real.exp (-(1 / 4) * (k : ℝ) ^ 2) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by simp only [modes, mem_Icc] at hk; exact_mod_cast hk.1
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hk2 (by linarith : (0 : ℝ) ≤ t),
      mul_le_mul_of_nonneg_right ht (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2)]
  refine (sum_le_sum hb).trans ?_
  rw [← mul_sum]
  have h := sum_modes_exp_le N (show (0 : ℝ) < 1 / 4 by norm_num)
  have e : Real.sqrt (π / (1 / 4)) / 2 = Real.sqrt π := by
    rw [show π / (1 / 4) = 2 ^ 2 * π by ring, Real.sqrt_mul (by norm_num), Real.sqrt_sq
      (by norm_num)]
    ring
  rw [e] at h
  calc Real.exp (-t / 4) * ∑ k ∈ modes N, Real.exp (-(1 / 4) * (k : ℝ) ^ 2)
      ≤ Real.exp (-t / 4) * Real.sqrt π := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := mul_comm _ _

 
lemma slice_long_le {n : ℕ} (v : DGFFSite n) {t : ℝ} (ht1 : 1 < t) :
    ∫ y : ℂ, (fKer n v (t, y) - Real.sqrt π * phiKernel ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0)
        (siteZ n v) (t, y)) ^ 2 ≤ π ^ 2 * Real.exp (-t / 2) := by
  have hnot : t ∉ Set.Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ 0) ^ 2) := by
    intro h; have := h.2; simp at this; linarith
  rw [slice_fKer_only v hnot, if_pos (by linarith)]
  have hN0 := Nn_pos n
  have h1 := mul_qker_diag_le_exp (Nn n) hN0 ht1.le v.1.1
  have h2 := mul_qker_diag_le_exp (Nn n) hN0 ht1.le v.1.2
  have h1' : 0 ≤ (Nn n : ℝ) * qker (Nn n) t v.1.1 v.1.1 :=
    mul_nonneg (by positivity) (qker_diag_nonneg (Nn n) hN0 t v.1.1)
  have h2' : 0 ≤ (Nn n : ℝ) * qker (Nn n) t v.1.2 v.1.2 :=
    mul_nonneg (by positivity) (qker_diag_nonneg (Nn n) hN0 t v.1.2)
  have hπ := Real.pi_pos
  have hp : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt hπ.le
  have hprod := mul_le_mul h1 h2 h2' (by positivity)
  have he : Real.exp (-t / 4) * Real.exp (-t / 4) = Real.exp (-t / 2) := by
    rw [← Real.exp_add]; ring_nf
  calc π * (((Nn n : ℝ) * qker (Nn n) t v.1.1 v.1.1) * ((Nn n : ℝ) * qker (Nn n) t v.1.2 v.1.2))
      ≤ π * ((Real.sqrt π * Real.exp (-t / 4)) * (Real.sqrt π * Real.exp (-t / 4))) :=
        mul_le_mul_of_nonneg_left hprod hπ.le
    _ = π ^ 2 * Real.exp (-t / 2) := by
        rw [show (Real.sqrt π * Real.exp (-t / 4)) * (Real.sqrt π * Real.exp (-t / 4)) =
          (Real.sqrt π * Real.sqrt π) * (Real.exp (-t / 4) * Real.exp (-t / 4)) by ring, hp, he]
        ring

 
def timeMaj (N : ℕ) (t : ℝ) : ℝ :=
  (Set.Ioo (0 : ℝ) (1 / (N : ℝ) ^ 2)).indicator (fun _ => π * (N : ℝ) ^ 2) t +
  (Set.Icc (1 / (N : ℝ) ^ 2) 1).indicator
    (fun t => cSlice * (4 * (((N : ℝ) ^ 4) * t ^ 3)⁻¹ + 2 * (((N : ℝ) ^ 2) * t ^ 2)⁻¹ + 1 / 2)) t +
  (Set.Ioi (1 : ℝ)).indicator (fun t => π ^ 2 * Real.exp (-t / 2)) t

lemma timeMaj_nonneg (N : ℕ) (t : ℝ) : 0 ≤ timeMaj N t := by
  have hπ := Real.pi_pos
  have hc := cSlice_nonneg
  unfold timeMaj
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · apply Set.indicator_nonneg; intro _ _; positivity
  · apply Set.indicator_nonneg; intro t ht
    have : 0 ≤ t := le_trans (by positivity) ht.1
    positivity
  · apply Set.indicator_nonneg; intro _ _; positivity

lemma continuousOn_mid {N : ℕ} (hN : 1 ≤ N) {a : ℝ} (ha0 : 0 < a) :
    ContinuousOn (fun t => 4 * (((N : ℝ) ^ 4) * t ^ 3)⁻¹ + 2 * (((N : ℝ) ^ 2) * t ^ 2)⁻¹ + 1 / 2)
      (Set.Icc a 1) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
  refine ContinuousAt.continuousWithinAt ?_
  have hc1 : ContinuousAt (fun t : ℝ => (((N : ℝ) ^ 4) * t ^ 3)⁻¹) t :=
    ((continuous_const.mul (continuous_pow 3)).continuousAt).inv₀
      (mul_pos (pow_pos hNp 4) (pow_pos ht0 3)).ne'
  have hc2 : ContinuousAt (fun t : ℝ => (((N : ℝ) ^ 2) * t ^ 2)⁻¹) t :=
    ((continuous_const.mul (continuous_pow 2)).continuousAt).inv₀
      (mul_pos (pow_pos hNp 2) (pow_pos ht0 2)).ne'
  exact ((hc1.const_mul 4).add (hc2.const_mul 2)).add continuousAt_const

 
lemma integral_mid {N : ℕ} (hN : 1 ≤ N) :
    ∫ t in (1 / (N : ℝ) ^ 2)..1,
      (4 * (((N : ℝ) ^ 4) * t ^ 3)⁻¹ + 2 * (((N : ℝ) ^ 2) * t ^ 2)⁻¹ + 1 / 2) ≤ 9 / 2 := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := pow_pos hNp 2
  have hN4 : (0 : ℝ) < (N : ℝ) ^ 4 := pow_pos hNp 4
  set a := 1 / (N : ℝ) ^ 2 with ha
  have ha0 : 0 < a := by rw [ha]; exact div_pos one_pos hN2
  have ha1 : a ≤ 1 := by rw [ha, div_le_one hN2]; nlinarith
  set F : ℝ → ℝ := fun t => -2 * ((N : ℝ) ^ 4)⁻¹ * (t ^ 2)⁻¹ - 2 * ((N : ℝ) ^ 2)⁻¹ * t⁻¹ + t / 2
  have hderiv : ∀ t ∈ Set.uIcc a 1, HasDerivAt F
      (4 * (((N : ℝ) ^ 4) * t ^ 3)⁻¹ + 2 * (((N : ℝ) ^ 2) * t ^ 2)⁻¹ + 1 / 2) t := by
    intro t ht
    rw [Set.uIcc_of_le ha1] at ht
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
    have h1 : HasDerivAt (fun t : ℝ => (t ^ 2)⁻¹) (-((2 : ℕ) * t ^ (2 - 1)) / (t ^ 2) ^ 2) t :=
      (hasDerivAt_pow 2 t).inv (pow_pos ht0 2).ne'
    have h2 : HasDerivAt (fun t : ℝ => t⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv ht0.ne'
    have h3 := ((h1.const_mul (-2 * ((N : ℝ) ^ 4)⁻¹)).sub
      (h2.const_mul (2 * ((N : ℝ) ^ 2)⁻¹))).add ((hasDerivAt_id t).div_const 2)
    refine h3.congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable (fun t => 4 * (((N : ℝ) ^ 4) * t ^ 3)⁻¹ +
      2 * (((N : ℝ) ^ 2) * t ^ 2)⁻¹ + 1 / 2) volume a 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le ha1]
    exact continuousOn_mid hN ha0
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [F, ha]
  have e1 : ((1 / (N : ℝ) ^ 2) ^ 2)⁻¹ = (N : ℝ) ^ 4 := by field_simp
  have e2 : (1 / (N : ℝ) ^ 2)⁻¹ = (N : ℝ) ^ 2 := by field_simp
  rw [e1, e2]
  have h4 : ((N : ℝ) ^ 4)⁻¹ * (N : ℝ) ^ 4 = 1 := inv_mul_cancel₀ hN4.ne'
  have h5 : ((N : ℝ) ^ 2)⁻¹ * (N : ℝ) ^ 2 = 1 := inv_mul_cancel₀ hN2.ne'
  have h6 : 0 ≤ ((N : ℝ) ^ 4)⁻¹ := inv_nonneg.mpr hN4.le
  have h7 : 0 ≤ ((N : ℝ) ^ 2)⁻¹ := inv_nonneg.mpr hN2.le
  have h8 : 0 ≤ 1 / (N : ℝ) ^ 2 := div_nonneg zero_le_one hN2.le
  simp only [one_pow, inv_one, mul_one]
  nlinarith

 
def cKer : ℝ := π + cSlice * (9 / 2) + 2 * π ^ 2

lemma integrable_timeMaj {N : ℕ} (hN : 1 ≤ N) : Integrable (timeMaj N) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hπ := Real.pi_pos
  have ha0 : 0 < 1 / (N : ℝ) ^ 2 := div_pos one_pos (pow_pos hNp 2)
  have i1 : Integrable ((Set.Ioo (0 : ℝ) (1 / (N : ℝ) ^ 2)).indicator
      (fun _ => π * (N : ℝ) ^ 2)) :=
    (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).integrable_indicator
      measurableSet_Ioo
  have i2 : Integrable ((Set.Icc (1 / (N : ℝ) ^ 2) 1).indicator
      (fun t => cSlice * (4 * (((N : ℝ) ^ 4) * t ^ 3)⁻¹ + 2 * (((N : ℝ) ^ 2) * t ^ 2)⁻¹ + 1 / 2))) :=
    IntegrableOn.integrable_indicator
      (((continuousOn_mid hN ha0).integrableOn_Icc).const_mul cSlice) measurableSet_Icc
  have i3 : Integrable ((Set.Ioi (1 : ℝ)).indicator (fun t => π ^ 2 * Real.exp (-t / 2))) := by
    have e : (fun t : ℝ => π ^ 2 * Real.exp (-t / 2)) = fun t => π ^ 2 * Real.exp (-1 / 2 * t) := by
      funext t; ring_nf
    rw [e]
    exact IntegrableOn.integrable_indicator ((integrableOn_exp_mul_Ioi
      (by norm_num : (-1 / 2 : ℝ) < 0) 1).const_mul (π ^ 2)) measurableSet_Ioi
  exact (i1.add i2).add i3

lemma integral_timeMaj_le {N : ℕ} (hN : 1 ≤ N) : ∫ t, timeMaj N t ≤ cKer := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hπ := Real.pi_pos
  have hc := cSlice_nonneg
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := pow_pos hNp 2
  have ha0 : 0 < 1 / (N : ℝ) ^ 2 := div_pos one_pos hN2
  have ha1 : 1 / (N : ℝ) ^ 2 ≤ 1 := by rw [div_le_one hN2]; nlinarith
  have i1 : Integrable ((Set.Ioo (0 : ℝ) (1 / (N : ℝ) ^ 2)).indicator
      (fun _ => π * (N : ℝ) ^ 2)) :=
    (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).integrable_indicator
      measurableSet_Ioo
  have i2 : Integrable ((Set.Icc (1 / (N : ℝ) ^ 2) 1).indicator
      (fun t => cSlice * (4 * (((N : ℝ) ^ 4) * t ^ 3)⁻¹ + 2 * (((N : ℝ) ^ 2) * t ^ 2)⁻¹ + 1 / 2))) :=
    IntegrableOn.integrable_indicator
      (((continuousOn_mid hN ha0).integrableOn_Icc).const_mul cSlice) measurableSet_Icc
  have e3 : (fun t : ℝ => π ^ 2 * Real.exp (-t / 2)) = fun t => π ^ 2 * Real.exp (-1 / 2 * t) := by
    funext t; ring_nf
  have i3 : Integrable ((Set.Ioi (1 : ℝ)).indicator (fun t => π ^ 2 * Real.exp (-t / 2))) := by
    rw [e3]
    exact IntegrableOn.integrable_indicator ((integrableOn_exp_mul_Ioi
      (by norm_num : (-1 / 2 : ℝ) < 0) 1).const_mul (π ^ 2)) measurableSet_Ioi
  unfold timeMaj
  rw [integral_add (by exact i1.add i2) (by exact i3), integral_add (by exact i1) (by exact i2),
    integral_indicator measurableSet_Ioo, integral_indicator measurableSet_Icc,
    integral_indicator measurableSet_Ioi]
  rw [setIntegral_const, Real.volume_real_Ioo_of_le ha0.le, smul_eq_mul]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha1,
    intervalIntegral.integral_const_mul]
  have hexp : ∫ t in Set.Ioi (1 : ℝ), π ^ 2 * Real.exp (-t / 2) =
      π ^ 2 * (2 * Real.exp (-1 / 2)) := by
    rw [e3, integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 1]
    ring_nf
  rw [hexp]
  have hmid := integral_mid hN
  have hNa : (1 / (N : ℝ) ^ 2 - 0) * (π * (N : ℝ) ^ 2) = π := by field_simp; ring
  have he : Real.exp (-1 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  unfold cKer
  rw [hNa]
  nlinarith [mul_le_mul_of_nonneg_left hmid hc, mul_le_mul_of_nonneg_left he (sq_nonneg π)]

 

theorem norm_fKer_sub_phi_sq_le {n : ℕ} (hn : 4 ≤ n) (v : DGFFSite n)
    (hv1 : |(v.1.1 : ℝ)| ≤ 4 / 5 * Nn n) (hv2 : |(v.1.2 : ℝ)| ≤ 4 / 5 * Nn n) :
    ‖fKerL2 n v - Real.sqrt π • phiKernelL2 ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0) (siteZ n v)‖ ^ 2 ≤
      cKer := by
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  have hg := memLp_phiKernel ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0) ha (siteZ n v)
  have hf := memLp_fKer n v
  have hN0 := Nn_pos n
  have hN1 : 1 ≤ Nn n := hN0
  rw [show phiKernelL2 ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0) (siteZ n v) = hg.toLp _ by
    rw [phiKernelL2, dif_pos ha]]
  rw [show fKerL2 n v = hf.toLp _ from rfl, norm_toLp_sub_smul_sq hf hg]
  have hint : Integrable (fun p : ℝ × ℂ => (fKer n v p - Real.sqrt π *
      phiKernel ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0) (siteZ n v) p) ^ 2) := by
    have := (hf.sub (hg.const_mul (Real.sqrt π))).integrable_sq
    exact this
  rw [Measure.volume_eq_prod, integral_prod _ (by rw [← Measure.volume_eq_prod]; exact hint)]
  have hNinv : ((2 : ℝ)⁻¹ ^ n) ^ 2 = 1 / (Nn n : ℝ) ^ 2 := by
    simp only [Nn]; push_cast; rw [inv_pow, inv_pow, ← one_div]
  have hpt : ∀ t : ℝ, ∫ y : ℂ, (fKer n v (t, y) - Real.sqrt π * phiKernel ((2 : ℝ)⁻¹ ^ n)
      ((2 : ℝ)⁻¹ ^ 0) (siteZ n v) (t, y)) ^ 2 ≤ timeMaj (Nn n) t := by
    intro t
    have hπ := Real.pi_pos
    have hc := cSlice_nonneg
    unfold timeMaj
    by_cases ht0 : 0 < t
    · by_cases hmid : t ∈ Set.Icc (1 / (Nn n : ℝ) ^ 2) 1
      · have := slice_mid_le hn v hv1 hv2 (by rw [hNinv]; exact hmid.1) hmid.2
        rw [Set.indicator_of_mem hmid]
        have h1 : 0 ≤ (Set.Ioo (0 : ℝ) (1 / (Nn n : ℝ) ^ 2)).indicator
            (fun _ => π * (Nn n : ℝ) ^ 2) t := by
          apply Set.indicator_nonneg; intro _ _; positivity
        have h3 : 0 ≤ (Set.Ioi (1 : ℝ)).indicator (fun t => π ^ 2 * Real.exp (-t / 2)) t := by
          apply Set.indicator_nonneg; intro _ _; positivity
        linarith
      · have hnot : t ∉ Set.Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ 0) ^ 2) := by
          rw [hNinv]; simpa using hmid
        rw [Set.indicator_of_notMem hmid]
        by_cases h1 : 1 < t
        · rw [Set.indicator_of_mem (show t ∈ Set.Ioi (1 : ℝ) from h1)]
          have := slice_long_le v h1
          have h0 : 0 ≤ (Set.Ioo (0 : ℝ) (1 / (Nn n : ℝ) ^ 2)).indicator
              (fun _ => π * (Nn n : ℝ) ^ 2) t := by
            apply Set.indicator_nonneg; intro _ _; positivity
          linarith
        · have hlt : t < 1 / (Nn n : ℝ) ^ 2 := by
            by_contra hge; push_neg at hge
            exact hmid ⟨hge, by linarith⟩
          rw [Set.indicator_of_mem (show t ∈ Set.Ioo (0 : ℝ) (1 / (Nn n : ℝ) ^ 2) from ⟨ht0, hlt⟩),
            Set.indicator_of_notMem (show t ∉ Set.Ioi (1 : ℝ) from h1)]
          have := slice_short_le v ht0 hnot
          linarith
    · have hnot : t ∉ Set.Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ 0) ^ 2) := by
        intro h; exact ht0 (lt_of_lt_of_le (by positivity) h.1)
      rw [slice_fKer_only v hnot, if_neg ht0]
      have := timeMaj_nonneg (Nn n) t
      unfold timeMaj at this
      exact this
  calc ∫ t, ∫ y : ℂ, (fKer n v (t, y) - Real.sqrt π * phiKernel ((2 : ℝ)⁻¹ ^ n)
        ((2 : ℝ)⁻¹ ^ 0) (siteZ n v) (t, y)) ^ 2
      ≤ ∫ t, timeMaj (Nn n) t := by
        exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun t =>
          integral_nonneg fun _ => sq_nonneg _) (integrable_timeMaj hN1)
          (Filter.Eventually.of_forall hpt)
    _ ≤ cKer := integral_timeMaj_le hN1

end SupercriticalLQGUniqueness.B2.QPos.P7
