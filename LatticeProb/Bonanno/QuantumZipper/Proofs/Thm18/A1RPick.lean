/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.A1RPick at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.Analysis.Complex.Schwarz

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1R (pick): a linear lower bound for holomorphic self-maps of `ℍ` (Schwarz–Pick)

For `Φ : ℍ → ℍ` holomorphic and `u ∈ ℍ`,
`Im Φ(u) ≥ Im Φ(i) · Im u / |u + i|²`.
Proof: Schwarz's lemma (`Complex.norm_le_norm_of_mapsTo_ball`) for
`G(ζ) = (Φ(z(ζ)) − p)/(Φ(z(ζ)) − p̄)`, `z(ζ) = i(1+ζ)/(1−ζ)`, `p = Φ(i)`, and the identity
`|w − p̄|² − |w − p|² = 4 Im w Im p`. This is the Schwarz–Pick lemma (Ahlfors, *Complex
Analysis*, 3rd ed., §4.3.4, pp. 135–136) in the upper half-plane. Used for the D90 mass node
(`R18.A1RMassStmt`): pushed side circles give small mass to strips along `ℝ`.
-/

noncomputable section

open Complex Metric Set

namespace QuantumZipper
namespace R18
namespace A1R

theorem normSq_sub_conj_sub_sub (w p : ℂ) :
    normSq (w - (starRingEnd ℂ) p) - normSq (w - p) = 4 * w.im * p.im := by
  simp only [normSq_apply, sub_re, sub_im, conj_re, conj_im]
  ring

theorem norm_sub_lt_norm_sub_conj {w p : ℂ} (hw : 0 < w.im) (hp : 0 < p.im) :
    ‖w - p‖ < ‖w - (starRingEnd ℂ) p‖ := by
  have h := normSq_sub_conj_sub_sub w p
  have h1 : normSq (w - p) < normSq (w - (starRingEnd ℂ) p) := by nlinarith [mul_pos hw hp]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h1
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1

/-- The inverse Cayley map `ζ ↦ i(1+ζ)/(1−ζ)`. -/
def cay (ζ : ℂ) : ℂ := I * (1 + ζ) / (1 - ζ)

theorem cay_im (ζ : ℂ) : (cay ζ).im = (1 - normSq ζ) / normSq (1 - ζ) := by
  unfold cay
  rw [div_im]
  simp only [mul_re, mul_im, I_re, I_im, add_re, add_im, one_re, one_im, sub_re, sub_im,
    normSq_apply]
  field_simp
  ring

theorem cay_mem_H {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) : cay ζ ∈ H := by
  have h1 : ‖ζ‖ < 1 := by simpa using hζ
  have hne : (1 : ℂ) - ζ ≠ 0 := by
    intro h
    have : ζ = 1 := by linear_combination -h
    rw [this] at h1; simp at h1
  show 0 < (cay ζ).im
  rw [cay_im]
  refine div_pos ?_ (normSq_pos.2 hne)
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg ζ]

theorem differentiableOn_cay : DifferentiableOn ℂ cay (ball (0 : ℂ) 1) := by
  intro ζ hζ
  have h1 : ‖ζ‖ < 1 := by simpa using hζ
  have hne : (1 : ℂ) - ζ ≠ 0 := by
    intro h
    have : ζ = 1 := by linear_combination -h
    rw [this] at h1; simp at h1
  unfold cay
  exact (((differentiableAt_const _).mul ((differentiableAt_const _).add differentiableAt_id)).div
    ((differentiableAt_const _).sub differentiableAt_id) hne).differentiableWithinAt

/-- **Schwarz–Pick lower bound in `ℍ`.** -/
theorem im_ge_of_mapsTo_H {Φ : ℂ → ℂ} (hd : DifferentiableOn ℂ Φ H) (hm : MapsTo Φ H H)
    {u : ℂ} (hu : u ∈ H) : (Φ I).im * u.im / ‖u + I‖ ^ 2 ≤ (Φ u).im := by
  have hIH : I ∈ H := by show 0 < I.im; simp
  set p := Φ I with hp
  have hpH : 0 < p.im := hm hIH
  have hpc : ∀ w ∈ H, w - (starRingEnd ℂ) p ≠ 0 := by
    intro w hw h
    have := congrArg Complex.im h
    simp only [sub_im, conj_im, zero_im] at this
    have hw' : 0 < w.im := hw
    linarith
  set G : ℂ → ℂ := fun ζ => (Φ (cay ζ) - p) / (Φ (cay ζ) - (starRingEnd ℂ) p) with hG
  have hGd : DifferentiableOn ℂ G (ball 0 1) := by
    have hc : DifferentiableOn ℂ (fun ζ => Φ (cay ζ)) (ball 0 1) :=
      hd.comp differentiableOn_cay fun ζ hζ => cay_mem_H hζ
    exact (hc.sub_const _).div (hc.sub_const _) fun ζ hζ => hpc _ (hm (cay_mem_H hζ))
  have hG0 : G 0 = 0 := by
    show (Φ (cay 0) - p) / (Φ (cay 0) - (starRingEnd ℂ) p) = 0
    rw [show cay 0 = I by simp [cay], ← hp, sub_self, zero_div]
  have hGm : MapsTo G (ball 0 1) (closedBall 0 1) := by
    intro ζ hζ
    have hw : 0 < (Φ (cay ζ)).im := hm (cay_mem_H hζ)
    rw [mem_closedBall, dist_zero_right, hG]
    simp only
    rw [norm_div, div_le_one (norm_pos_iff.2 (hpc _ (hm (cay_mem_H hζ))))]
    exact (norm_sub_lt_norm_sub_conj hw hpH).le
  -- the Cayley coordinate of `u`
  have huI : u + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [add_im, I_im, zero_im] at this
    have hu' : 0 < u.im := hu
    linarith
  set ζ := (u - I) / (u + I) with hζ
  have hnormζ : ‖u - I‖ < ‖u + I‖ := by
    have := norm_sub_lt_norm_sub_conj (w := u) (p := I) hu (by simp)
    simpa using this
  have hζb : ‖ζ‖ < 1 := by
    rw [hζ, norm_div, div_lt_one (norm_pos_iff.2 huI)]
    exact hnormζ
  have hcay : cay ζ = u := by
    unfold cay
    rw [hζ]
    have h2 : (1 : ℂ) - (u - I) / (u + I) = 2 * I / (u + I) := by
      field_simp; ring
    have h3 : (1 : ℂ) + (u - I) / (u + I) = 2 * u / (u + I) := by
      field_simp; ring
    rw [h2, h3]
    field_simp
  have hS := Complex.norm_le_norm_of_mapsTo_ball hGd hGm hG0 hζb
  have hS' : ‖(Φ u - p) / (Φ u - (starRingEnd ℂ) p)‖ ≤ ‖ζ‖ := by
    have e : G ζ = (Φ u - p) / (Φ u - (starRingEnd ℂ) p) := by
      simp only [hG, hcay]
    rw [← e]; exact hS
  clear hS
  have hS := hS'
  -- turn `|G| ≤ |ζ|` into the lower bound
  set w := Φ u with hwdef
  have hw : 0 < w.im := hm hu
  have hu' : 0 < u.im := hu
  have hden : 0 < ‖w - (starRingEnd ℂ) p‖ := norm_pos_iff.2 (hpc _ (hm hu))
  have hden' : 0 < ‖u + I‖ := norm_pos_iff.2 huI
  rw [norm_div, hζ, norm_div, div_le_div_iff₀ hden hden'] at hS
  -- squares
  have hsq : ‖w - p‖ ^ 2 * ‖u + I‖ ^ 2 ≤ ‖u - I‖ ^ 2 * ‖w - (starRingEnd ℂ) p‖ ^ 2 := by
    have := mul_le_mul hS hS (by positivity) (by positivity)
    nlinarith [this]
  have e1 := normSq_sub_conj_sub_sub w p
  have e2 := normSq_sub_conj_sub_sub u (-I)
  simp only [map_neg, conj_I, neg_neg, sub_neg_eq_add, neg_im, I_im] at e2
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at e1 e2
  -- `|w − p̄| ≥ Im p`
  have hlow : p.im ≤ ‖w - (starRingEnd ℂ) p‖ := by
    have := Complex.abs_im_le_norm (w - (starRingEnd ℂ) p)
    simp only [sub_im, conj_im, sub_neg_eq_add] at this
    rw [abs_of_pos (by linarith)] at this
    linarith
  -- `4 Im w Im p |u+i|² ≥ 4 Im u |w − p̄|²`
  have key : u.im * ‖w - (starRingEnd ℂ) p‖ ^ 2 ≤ w.im * p.im * ‖u + I‖ ^ 2 := by
    nlinarith [hsq, e1, e2]
  have hp2 : p.im ^ 2 ≤ ‖w - (starRingEnd ℂ) p‖ ^ 2 := by
    exact pow_le_pow_left₀ hpH.le hlow 2
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hp2 hu'.le]

end A1R
end R18
end QuantumZipper
