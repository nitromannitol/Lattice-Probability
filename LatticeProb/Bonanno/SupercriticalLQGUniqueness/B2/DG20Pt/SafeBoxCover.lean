/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.SafeBoxCover at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.BoxExitCross
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_1Geom

 





set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Pt

private theorem mem_outer_sq_dist_le {c z : ℂ} {ρ : ℝ} (_hρ : 0 ≤ ρ)
    (hz : z ∈ Icc (c.re - 3 * ρ) (c.re + 3 * ρ) ×ℂ
      Icc (c.im - 3 * ρ) (c.im + 3 * ρ)) :
    dist z c ≤ 6 * ρ := by
  rw [Complex.mem_reProdIm] at hz
  have hre : |(z - c).re| ≤ 3 * ρ := by
    rw [Complex.sub_re]
    exact abs_le.mpr ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  have him : |(z - c).im| ≤ 3 * ρ := by
    rw [Complex.sub_im]
    exact abs_le.mpr ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  calc
    dist z c = ‖z - c‖ := by simp only [dist_eq_norm]
    _ ≤ |(z - c).re| + |(z - c).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 6 * ρ := by linarith

 




theorem exists_finite_safe_box_cover
    (U : TopologicalSpace.Opens ℂ) (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hK₁U : K₁ ⊆ U) (hdisj : Disjoint K₁ K₂) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ F : Finset ℂ,
      (∀ c ∈ F, c ∈ K₁) ∧
      (∀ z ∈ K₁, ∃ c ∈ F,
        z ∈ Icc (c.re - ρ) (c.re + ρ) ×ℂ
          Icc (c.im - ρ) (c.im + ρ)) ∧
      (∀ c ∈ F,
        Icc (c.re - 3 * ρ) (c.re + 3 * ρ) ×ℂ
          Icc (c.im - 3 * ρ) (c.im + 3 * ρ) ⊆ U ∧
        Disjoint (Icc (c.re - 3 * ρ) (c.re + 3 * ρ) ×ℂ
          Icc (c.im - 3 * ρ) (c.im + 3 * ρ)) K₂) := by
  classical
  obtain ⟨δU, hδU, hδUU⟩ := hK₁.exists_thickening_subset_open U.isOpen hK₁U
  obtain ⟨δD, hδD, hδdisj⟩ := hdisj.exists_thickenings hK₁ hK₂.isClosed
  let ρ : ℝ := min δU δD / 16
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have h6U : 6 * ρ < δU := by
    dsimp [ρ]
    have := min_le_left δU δD
    nlinarith [hδU]
  have h6D : 6 * ρ < δD := by
    dsimp [ρ]
    have := min_le_right δU δD
    nlinarith [hδD]
  obtain ⟨F, hFsub, hFcover⟩ := hK₁.elim_nhds_subcover
    (fun c => ball c ρ) (fun c _ => isOpen_ball.mem_nhds (mem_ball_self hρ))
  refine ⟨ρ, hρ, F, hFsub, ?_, ?_⟩
  · intro z hz
    obtain ⟨c, hcF, hzc⟩ := by simpa only [mem_iUnion] using hFcover hz
    refine ⟨c, hcF, ?_⟩
    have hd : ‖z - c‖ < ρ := by simpa only [mem_ball, dist_eq_norm] using hzc
    have hre := (Complex.abs_re_le_norm (z - c)).trans_lt hd
    have him := (Complex.abs_im_le_norm (z - c)).trans_lt hd
    rw [Complex.mem_reProdIm]
    constructor
    · rw [Complex.sub_re] at hre
      rcases abs_lt.mp hre with ⟨hlo, hhi⟩
      exact ⟨by linarith, by linarith⟩
    · rw [Complex.sub_im] at him
      rcases abs_lt.mp him with ⟨hlo, hhi⟩
      exact ⟨by linarith, by linarith⟩
  · intro c hcF
    have hcK : c ∈ K₁ := hFsub c hcF
    constructor
    · intro z hz
      have hd : dist z c < δU := (mem_outer_sq_dist_le hρ.le hz).trans_lt h6U
      exact hδUU (mem_thickening_iff.mpr ⟨c, hcK, by simpa only [dist_comm] using hd⟩)
    · apply Set.disjoint_left.mpr
      intro z hz hzK₂
      have hd : dist z c < δD := (mem_outer_sq_dist_le hρ.le hz).trans_lt h6D
      have hzD : z ∈ thickening δD K₁ :=
        mem_thickening_iff.mpr ⟨c, hcK, by simpa only [dist_comm] using hd⟩
      have hzK₂D : z ∈ thickening δD K₂ :=
        self_subset_thickening hδD K₂ hzK₂
      exact hδdisj.ne_of_mem hzD hzK₂D rfl

end SupercriticalLQGUniqueness.B2.DG20Pt
