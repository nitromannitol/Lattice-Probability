/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSquareWinding at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSquareLog
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.Glue

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set QuantumZipper.CA.Topo

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_four_side_winding (c : ℂ) (top left bot right : ℝ → ℂ)
    (htc : ContinuousOn top (Icc (0 : ℝ) 1))
    (hlc : ContinuousOn left (Icc (0 : ℝ) 1))
    (hbc : ContinuousOn bot (Icc (0 : ℝ) 1))
    (hrc : ContinuousOn right (Icc (0 : ℝ) 1))
    (htu : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (top t - c).im)
    (hll : ∀ t ∈ Icc (0 : ℝ) 1, (left t - c).re < 0)
    (hbd : ∀ t ∈ Icc (0 : ℝ) 1, (bot t - c).im < 0)
    (hrr : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (right t - c).re)
    (h01 : top 1 = left 0) (h12 : left 1 = bot 0)
    (h23 : bot 1 = right 0) (h30 : right 1 = top 0) :
    let P := Strong.glue4 top left bot right
    loopDeg
      ⟨fun u : unitInterval => P (4 * (u : ℝ)) - c,
        ((Strong.continuousOn_glue4 top left bot right
          htc hlc hbc hrc h01 h12 h23).comp_continuous
          (by fun_prop : Continuous (fun u : unitInterval => 4 * (u : ℝ)))
          (fun u => Strong.mem_Icc_mul (by norm_num) u)).sub continuous_const⟩
      (by
        intro u hz
        have hr : 4 * (u : ℝ) ∈ Icc (0 : ℝ) 4 :=
          Strong.mem_Icc_mul (by norm_num) u
        have hside : P (4 * (u : ℝ)) ≠ c := by
          simp only [P, Strong.glue4]
          split_ifs with h₀ h₁ h₂
          · have h := htu _ ⟨by linarith [hr.1], h₀⟩
            intro heq; rw [heq, sub_self, Complex.zero_im] at h; linarith
          · have h := hll (4 * (u : ℝ) - 1) ⟨by linarith [h₀], by linarith [h₁]⟩
            intro heq; rw [heq, sub_self, Complex.zero_re] at h; linarith
          · have h := hbd (4 * (u : ℝ) - 2) ⟨by linarith [h₁], by linarith [h₂]⟩
            intro heq; rw [heq, sub_self, Complex.zero_im] at h; linarith
          · have h := hrr (4 * (u : ℝ) - 3)
              ⟨by linarith [h₂], by linarith [hr.2]⟩
            intro heq; rw [heq, sub_self, Complex.zero_re] at h; linarith
        exact (sub_ne_zero.mpr hside) hz) = 1 := by
  let P := Strong.glue4 top left bot right
  let tlog : ℝ → ℂ := fun t => Complex.log (top t - c)
  let llog : ℝ → ℂ := fun t => Complex.log (-(left t - c)) + (Real.pi : ℂ) * Complex.I
  let blog : ℝ → ℂ := fun t => Complex.log (-(bot t - c)) + (Real.pi : ℂ) * Complex.I
  let rlog : ℝ → ℂ := fun t => Complex.log (right t - c) + (2 * Real.pi : ℂ) * Complex.I
  let Λ := Strong.glue4 tlog llog blog rlog
  have htlog : ContinuousOn tlog (Icc (0 : ℝ) 1) :=
    laneC_continuousOn_log_upper (htc.sub continuousOn_const) htu
  have hllog : ContinuousOn llog (Icc (0 : ℝ) 1) := by
    apply ContinuousOn.add _ continuousOn_const
    exact laneC_continuousOn_log_right ((hlc.sub continuousOn_const).neg)
      (fun t ht => by have h := hll t ht; simpa using (neg_pos.mpr h))
  have hblog : ContinuousOn blog (Icc (0 : ℝ) 1) := by
    apply ContinuousOn.add _ continuousOn_const
    exact laneC_continuousOn_log_upper ((hbc.sub continuousOn_const).neg)
      (fun t ht => by have h := hbd t ht; simpa using (neg_pos.mpr h))
  have hrlog : ContinuousOn rlog (Icc (0 : ℝ) 1) := by
    apply ContinuousOn.add _ continuousOn_const
    exact laneC_continuousOn_log_right (hrc.sub continuousOn_const) hrr
  have hm01 : tlog 1 = llog 0 := by
    have h := laneC_log_neg_add_pi_of_im_pos (htu 1 (by norm_num))
    simpa only [tlog, llog, h01] using h.symm
  have hm12 : llog 1 = blog 0 := by simp [llog, blog, h12]
  have hm23 : blog 1 = rlog 0 := by
    have h := laneC_log_neg_add_pi_of_im_neg (hbd 1 (by norm_num))
    simpa only [blog, rlog, h23] using h
  have hΛc : ContinuousOn Λ (Icc (0 : ℝ) 4) :=
    Strong.continuousOn_glue4 tlog llog blog rlog htlog hllog hblog hrlog hm01 hm12 hm23
  have hPc : ContinuousOn P (Icc (0 : ℝ) 4) :=
    Strong.continuousOn_glue4 top left bot right htc hlc hbc hrc h01 h12 h23
  have hPΛ : ∀ t ∈ Icc (0 : ℝ) 4, P t - c = Complex.exp (Λ t) := by
    intro t ht
    simp only [P, Λ, Strong.glue4]
    split_ifs with h₀ h₁ h₂
    · have hz : top t - c ≠ 0 := by
        intro heq
        have h := htu t ⟨by linarith [ht.1], h₀⟩
        rw [heq, Complex.zero_im] at h
        linarith
      simp [tlog, Complex.exp_log hz]
    · have hz : -(left (t - 1) - c) ≠ 0 := by
        intro heq
        have h := hll (t - 1) ⟨by linarith [h₀], by linarith [h₁]⟩
        rw [neg_eq_zero.mp heq, Complex.zero_re] at h
        linarith
      have hz' : c - left (t - 1) ≠ 0 := by simpa only [neg_sub] using hz
      simp [llog, Complex.exp_add, Complex.exp_pi_mul_I]
      rw [Complex.exp_log hz']
      ring
    · have hz : -(bot (t - 2) - c) ≠ 0 := by
        intro heq
        have h := hbd (t - 2) ⟨by linarith [h₁], by linarith [h₂]⟩
        rw [neg_eq_zero.mp heq, Complex.zero_im] at h
        linarith
      have hz' : c - bot (t - 2) ≠ 0 := by simpa only [neg_sub] using hz
      simp [blog, Complex.exp_add, Complex.exp_pi_mul_I]
      rw [Complex.exp_log hz']
      ring
    · have hz : right (t - 3) - c ≠ 0 := by
        intro heq
        have h := hrr (t - 3) ⟨by linarith [h₂], by linarith [ht.2]⟩
        rw [heq, Complex.zero_re] at h
        linarith
      simp [rlog, Complex.exp_add, Complex.exp_two_pi_mul_I, Complex.exp_log hz]
  have hΛend : Λ 4 = Λ 0 + 2 * Real.pi * Complex.I := by
    have h4 : Λ 4 = rlog 1 := by norm_num [Λ, Strong.glue4]
    have h0 : Λ 0 = tlog 0 := by norm_num [Λ, Strong.glue4]
    rw [h4, h0]
    simp [rlog, tlog, h30]
  let γ : C(unitInterval, ℂ) :=
    ⟨fun u => P (4 * (u : ℝ)) - c,
      (hPc.comp_continuous (by fun_prop)
        (fun u => Strong.mem_Icc_mul (by norm_num) u)).sub continuous_const⟩
  have hγne : ∀ u, γ u ≠ 0 := by
    intro u hz
    have hp := hPΛ (4 * (u : ℝ)) (Strong.mem_Icc_mul (by norm_num) u)
    change P (4 * (u : ℝ)) - c = 0 at hz
    rw [hp] at hz
    exact Complex.exp_ne_zero _ hz
  have hγclosed : γ 0 = γ 1 := by
    simp only [γ, ContinuousMap.coe_mk]
    norm_num [P, Strong.glue4, h30]
  apply loopDeg_unique γ hγne hγclosed
    (L := fun u => Λ (4 * (u : ℝ)))
    (hΛc.comp_continuous (by fun_prop)
      (fun u => Strong.mem_Icc_mul (by norm_num) u))
  · intro u
    exact (hPΛ _ (Strong.mem_Icc_mul (by norm_num) u)).symm
  · simp only [Set.Icc.coe_one, Set.Icc.coe_zero, mul_one, mul_zero]
    rw [hΛend]
    ring

end SupercriticalLQGUniqueness.B2.DG20Conc
