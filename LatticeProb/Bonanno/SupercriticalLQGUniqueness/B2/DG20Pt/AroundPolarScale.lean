/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.AroundPolarScale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.AroundBoxTail

 




set_option autoImplicit false
noncomputable section

open Set Complex

namespace SupercriticalLQGUniqueness.B2.DG20Pt

private def shiftBox (B : Strong.Box) (a : ℝ) : Strong.Box :=
  ⟨B.x₀ + a, B.x₁ + a, B.y₀, B.y₁⟩

private theorem shiftBox_openSet (B : Strong.Box) (a : ℝ) :
    (shiftBox B a).openSet =
      (fun w : ℂ => w + (a : ℂ)) '' B.openSet := by
  ext w
  constructor
  · intro hw
    refine ⟨w - (a : ℂ), ?_, by ring⟩
    simp only [Strong.Box.openSet, shiftBox, Set.mem_setOf_eq,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      sub_zero] at hw ⊢
    exact ⟨by linarith [hw.1], by linarith [hw.2.1],
      by linarith [hw.2.2.1], by linarith [hw.2.2.2]⟩
  · rintro ⟨v, hv, rfl⟩
    simp only [Strong.Box.openSet, shiftBox, Set.mem_setOf_eq,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      add_zero] at hv ⊢
    exact ⟨by linarith [hv.1], by linarith [hv.2.1],
      by linarith [hv.2.2.1], by linarith [hv.2.2.2]⟩

private theorem shiftBox_closedSet (B : Strong.Box) (a : ℝ) :
    (shiftBox B a).closedSet =
      (fun w : ℂ => w + (a : ℂ)) '' B.closedSet := by
  ext w
  constructor
  · intro hw
    refine ⟨w - (a : ℂ), ?_, by ring⟩
    simp only [Strong.Box.closedSet, LQGMetric.RectCross.rect, shiftBox,
      Set.mem_setOf_eq, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, sub_zero] at hw ⊢
    constructor <;> constructor <;> linarith [hw.1.1, hw.1.2, hw.2.1, hw.2.2]
  · rintro ⟨v, hv, rfl⟩
    simp only [Strong.Box.closedSet, LQGMetric.RectCross.rect, shiftBox,
      Set.mem_setOf_eq, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, add_zero] at hv ⊢
    constructor <;> constructor <;> linarith [hv.1.1, hv.1.2, hv.2.1, hv.2.2]

private theorem cfgU_shift (L Δ a : ℝ) (j : Fin 4) :
    Strong.cfgU (L + a) Δ j = shiftBox (Strong.cfgU L Δ j) a := by
  fin_cases j <;> simp [Strong.cfgU, Strong.boxR, Strong.boxA, shiftBox] <;>
    ring <;> simp

private theorem cfgK₁_shift (L Δ a : ℝ) (j : Fin 4) :
    Strong.cfgK₁ (L + a) Δ j = shiftBox (Strong.cfgK₁ L Δ j) a := by
  fin_cases j <;> simp [Strong.cfgK₁, Strong.segR, Strong.segA, shiftBox] <;>
    ring <;> simp

private theorem cfgK₂_shift (L Δ a : ℝ) (j : Fin 4) :
    Strong.cfgK₂ (L + a) Δ j = shiftBox (Strong.cfgK₂ L Δ j) a := by
  fin_cases j <;> simp [Strong.cfgK₂, Strong.segR, Strong.segA, shiftBox] <;>
    ring <;> simp

private theorem annL_annulus48_scale (x : ℂ) {r : ℝ} (hr : 0 < r) :
    Strong.annL (Inputs.annulus48 x r hr) =
      Strong.annL (Inputs.annulus48 0 1 one_pos) + Real.log r := by
  simp only [Strong.annL, Inputs.annulus48]
  have hlog := Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hr.ne'
  norm_num at hlog ⊢
  exact hlog

private theorem annΔ_annulus48_scale (x : ℂ) {r : ℝ} (hr : 0 < r) :
    Strong.annΔ (Inputs.annulus48 x r hr) =
      Strong.annΔ (Inputs.annulus48 0 1 one_pos) := by
  change (Real.log (8 * r) - Real.log (4 * r)) / 16 =
    (Real.log (8 * 1) - Real.log (4 * 1)) / 16
  rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hr.ne',
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hr.ne']
  norm_num

private theorem polarOpen_shift (B : Strong.Box) (x : ℂ) {r : ℝ} (hr : 0 < r) :
    Strong.polarOpen x (shiftBox B (Real.log r)) =
      (fun z : ℂ => x + (r : ℂ) * z) '' Strong.polarOpen 0 B := by
  rw [Strong.polarOpen, Strong.polarOpen, shiftBox_openSet]
  ext z
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨Strong.expChart 0 v, ⟨v, hv, rfl⟩, ?_⟩
    simp [Strong.expChart, Complex.exp_add, ← Complex.ofReal_exp,
      Real.exp_log hr, mul_comm]
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨v + (Real.log r : ℂ), ⟨v, hv, rfl⟩, ?_⟩
    simp [Strong.expChart, Complex.exp_add, ← Complex.ofReal_exp,
      Real.exp_log hr, mul_comm]

private theorem polarClosed_shift (B : Strong.Box) (x : ℂ) {r : ℝ} (hr : 0 < r) :
    Strong.polarClosed x (shiftBox B (Real.log r)) =
      (fun z : ℂ => x + (r : ℂ) * z) '' Strong.polarClosed 0 B := by
  rw [Strong.polarClosed, Strong.polarClosed, shiftBox_closedSet]
  ext z
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨Strong.expChart 0 v, ⟨v, hv, rfl⟩, ?_⟩
    simp [Strong.expChart, Complex.exp_add, ← Complex.ofReal_exp,
      Real.exp_log hr, mul_comm]

  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨v + (Real.log r : ℂ), ⟨v, hv, rfl⟩, ?_⟩
    simp [Strong.expChart, Complex.exp_add, ← Complex.ofReal_exp,
      Real.exp_log hr, mul_comm]

 

theorem around_cfgOpens_scale (x : ℂ) {r : ℝ} (hr : 0 < r) (j : Fin 4) :
    (Strong.cfgOpens (Inputs.annulus48 x r hr) j : Set ℂ) =
      (fun z : ℂ => x + (r : ℂ) * z) ''
        (Strong.cfgOpens (Inputs.annulus48 0 1 one_pos) j : Set ℂ) := by
  change Strong.polarOpen x
      (Strong.cfgU (Strong.annL (Inputs.annulus48 x r hr))
        (Strong.annΔ (Inputs.annulus48 x r hr)) j) =
    (fun z : ℂ => x + (r : ℂ) * z) ''
      Strong.polarOpen 0
        (Strong.cfgU (Strong.annL (Inputs.annulus48 0 1 one_pos))
          (Strong.annΔ (Inputs.annulus48 0 1 one_pos)) j)
  rw [annL_annulus48_scale x hr, annΔ_annulus48_scale x hr,
    cfgU_shift, polarOpen_shift _ x hr]

 
theorem around_cfgSet₁_scale (x : ℂ) {r : ℝ} (hr : 0 < r) (j : Fin 4) :
    Strong.cfgSet₁ (Inputs.annulus48 x r hr) j =
      (fun z : ℂ => x + (r : ℂ) * z) ''
        Strong.cfgSet₁ (Inputs.annulus48 0 1 one_pos) j := by
  change Strong.polarClosed x
      (Strong.cfgK₁ (Strong.annL (Inputs.annulus48 x r hr))
        (Strong.annΔ (Inputs.annulus48 x r hr)) j) =
    (fun z : ℂ => x + (r : ℂ) * z) ''
      Strong.polarClosed 0
        (Strong.cfgK₁ (Strong.annL (Inputs.annulus48 0 1 one_pos))
          (Strong.annΔ (Inputs.annulus48 0 1 one_pos)) j)
  rw [annL_annulus48_scale x hr, annΔ_annulus48_scale x hr,
    cfgK₁_shift, polarClosed_shift _ x hr]

 
theorem around_cfgSet₂_scale (x : ℂ) {r : ℝ} (hr : 0 < r) (j : Fin 4) :
    Strong.cfgSet₂ (Inputs.annulus48 x r hr) j =
      (fun z : ℂ => x + (r : ℂ) * z) ''
        Strong.cfgSet₂ (Inputs.annulus48 0 1 one_pos) j := by
  change Strong.polarClosed x
      (Strong.cfgK₂ (Strong.annL (Inputs.annulus48 x r hr))
        (Strong.annΔ (Inputs.annulus48 x r hr)) j) =
    (fun z : ℂ => x + (r : ℂ) * z) ''
      Strong.polarClosed 0
        (Strong.cfgK₂ (Strong.annL (Inputs.annulus48 0 1 one_pos))
          (Strong.annΔ (Inputs.annulus48 0 1 one_pos)) j)
  rw [annL_annulus48_scale x hr, annΔ_annulus48_scale x hr,
    cfgK₂_shift, polarClosed_shift _ x hr]

 
theorem around_cfgOpens_translate (x : ℂ) {r : ℝ} (hr : 0 < r) (j : Fin 4) :
    (Strong.cfgOpens (Inputs.annulus48 x r hr) j : Set ℂ) =
      (fun z : ℂ => z + x) ''
        (Strong.cfgOpens (Inputs.annulus48 0 r hr) j : Set ℂ) := by
  rw [around_cfgOpens_scale x hr j, around_cfgOpens_scale 0 hr j, image_image]
  congr 1
  funext z
  simp [Function.comp_def, add_comm]

 
theorem around_cfgSet₁_translate (x : ℂ) {r : ℝ} (hr : 0 < r) (j : Fin 4) :
    Strong.cfgSet₁ (Inputs.annulus48 x r hr) j =
      (fun z : ℂ => z + x) '' Strong.cfgSet₁ (Inputs.annulus48 0 r hr) j := by
  rw [around_cfgSet₁_scale x hr j, around_cfgSet₁_scale 0 hr j, image_image]
  congr 1
  funext z
  simp [Function.comp_def, add_comm]

 
theorem around_cfgSet₂_translate (x : ℂ) {r : ℝ} (hr : 0 < r) (j : Fin 4) :
    Strong.cfgSet₂ (Inputs.annulus48 x r hr) j =
      (fun z : ℂ => z + x) '' Strong.cfgSet₂ (Inputs.annulus48 0 r hr) j := by
  rw [around_cfgSet₂_scale x hr j, around_cfgSet₂_scale 0 hr j, image_image]
  congr 1
  funext z
  simp [Function.comp_def, add_comm]

end SupercriticalLQGUniqueness.B2.DG20Pt
