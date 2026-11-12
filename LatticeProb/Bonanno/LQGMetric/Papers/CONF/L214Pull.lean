/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L214Pull at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L214Sep
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L214Harm
import LatticeProb.Bonanno.LQGMetric.Complex.CircleArcBall

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 2.14, R5 step 4: transporting the disc separation to `U`

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), proof of Lemma 2.14,
confluence-final.tex 866–870: the separation found in disc coordinates gives
(2.13) "`I` is disconnected from 0 in `U`". `l214_pull`: if `Φ` is continuous and injective on
the closed unit disc with `Φ 0 = 0`, then under the hypotheses of `l214_sep` the set
`Φ(closure W)` disconnects `0` from `Φ(A)` in `U = Φ(𝔻)` (`DisconnectsIn`). Paths in `U ∪ Φ(A)`
are pulled back by `Φ⁻¹`, continuous since `Φ` is a closed embedding of the compact disc
(mathlib `Continuous.isClosedEmbedding`). Own elementary step (the paper works in `U` directly).
-/

namespace LQGMetric
namespace CONF

open Set Metric Complex
open scoped ComplexConjugate Real

/-- **CONF Lemma 2.14, R5 step 4**: the disc separation `l214_sep` transported to `U = Φ(𝔻)`. -/
theorem l214_pull {Φ : ℂ → ℂ} (hc : ContinuousOn Φ (closedBall 0 1))
    (hinj : InjOn Φ (closedBall 0 1)) (h0 : Φ 0 = 0) {W : Set ℂ} (hWo : IsOpen W)
    (hWc : IsPreconnected W) (hW : ∀ z ∈ W, ‖z‖ < 1 ∧ 0 < z.im) {a b : ℂ}
    (ha : a ∈ closure W) (hb : b ∈ closure W) (ha1 : ‖a‖ = 1) (hb1 : ‖b‖ = 1) {A : Set ℂ}
    (hA : ∀ q' ∈ A, ‖q'‖ = 1 ∧ 0 < q'.im ∧ (a * conj q').im < 0 ∧ 0 < (b * conj q').im) :
    DisconnectsIn (Φ '' ball 0 1) (Φ '' closure W) {0} (Φ '' A) := by
  intro x y γ hx hy hrange
  rw [mem_singleton_iff] at hx
  subst hx
  obtain ⟨q, hqA, rfl⟩ := hy
  have hAB : ∀ z ∈ A, z ∈ closedBall (0 : ℂ) 1 := fun z hz =>
    mem_closedBall_zero_iff.2 (hA z hz).1.le
  have hpre : ∀ t, ∃ z ∈ closedBall (0 : ℂ) 1, Φ z = γ t ∧ (‖z‖ < 1 ∨ z ∈ A) := by
    intro t
    rcases hrange (mem_range_self t) with ⟨z, hz, hzt⟩ | ⟨z, hz, hzt⟩
    · exact ⟨z, ball_subset_closedBall hz, hzt, Or.inl (mem_ball_zero_iff.1 hz)⟩
    · exact ⟨z, hAB z hz, hzt, Or.inr hz⟩
  choose G hGB hGΦ hGA using hpre
  -- `Φ` restricted to the closed disc is a closed embedding
  let ι : closedBall (0 : ℂ) 1 → ℂ := fun z => Φ z
  have hιc : Continuous ι := hc.comp_continuous continuous_subtype_val fun z => z.2
  have hιi : Function.Injective ι := fun z w h => Subtype.ext (hinj z.2 w.2 h)
  haveI : CompactSpace (closedBall (0 : ℂ) 1) := isCompact_iff_compactSpace.1 (isCompact_closedBall 0 1)
  have hemb := (hιc.isClosedEmbedding hιi).isEmbedding
  let G' : unitInterval → closedBall (0 : ℂ) 1 := fun t => ⟨G t, hGB t⟩
  have hG'c : Continuous G' := by
    rw [hemb.continuous_iff]
    have : ι ∘ G' = γ := funext fun t => hGΦ t
    rw [this]; exact γ.continuous
  have hG0 : G 0 = 0 := hinj (hGB 0) (mem_closedBall_self zero_le_one) (by rw [hGΦ, h0]; simp)
  have hG1 : G 1 = q := hinj (hGB 1) (hAB q hqA) (by rw [hGΦ]; simp)
  let γ' : Path (0 : ℂ) q :=
    { toFun := fun t => G t
      continuous_toFun := continuous_subtype_val.comp hG'c
      source' := hG0
      target' := hG1 }
  obtain ⟨z, ⟨t, rfl⟩, hz⟩ := l214_sep hWo hWc hW ha hb ha1 hb1 hA γ' hqA hGA
  exact ⟨γ t, mem_range_self t, G t, hz, hGΦ t⟩

/-- Centre `c⁺ = e^{i(π/2 + ℓ)}` of the arc `J⁺` (normalized coordinates). -/
noncomputable def l214CenterP (ℓ : ℝ) : ℂ := exp (((π / 2 + ℓ : ℝ) : ℂ) * I)

theorem l214_conj_exp (x ψ : ℝ) :
    exp ((x : ℂ) * I) * conj (exp ((ψ : ℂ) * I)) = exp (((x - ψ : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, conj_ofReal, conj_I]
  push_cast; ring

/-- **R5 step 3** (sign conditions of `l214_sep`): in normalized coordinates, a point `a` of the
cap at `c⁻`, a point `b` of the cap at `c⁺` and a point `q'` of the arc
`circArc (π/2 − ℓ/2) ℓ` (CONF's `φ⁻¹(I)` rotated to centre `i`) satisfy
`Im q' > 0` and `Im(a q̄') < 0 < Im(b q̄')`. Own elementary computation (Jordan's inequality). -/
theorem l214_signs {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1 / 10) {a b q' : ℂ}
    (ha : ‖a - l214CenterM ℓ‖ < ℓ / 4) (hb : ‖b - l214CenterP ℓ‖ < ℓ / 4)
    (hq : q' ∈ circArc (π / 2 - ℓ / 2) ℓ) :
    0 < q'.im ∧ (a * conj q').im < 0 ∧ 0 < (b * conj q').im := by
  obtain ⟨ψ, ⟨hψ1, hψ2⟩, rfl⟩ := hq
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  have hq1 : ‖exp ((ψ : ℂ) * I)‖ = 1 := norm_exp_ofReal_mul_I ψ
  have herr : ∀ e : ℂ, |(e * conj (exp ((ψ : ℂ) * I))).im| ≤ ‖e‖ := fun e => by
    refine (abs_im_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj, hq1, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [exp_ofReal_mul_I_im]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  · have e : a * conj (exp ((ψ : ℂ) * I)) = (a - l214CenterM ℓ) * conj (exp ((ψ : ℂ) * I)) +
        exp (((π / 2 - ℓ - ψ : ℝ) : ℂ) * I) := by
      rw [← l214_conj_exp, l214CenterM]; ring
    rw [e, add_im, exp_ofReal_mul_I_im]
    have h1 := herr (a - l214CenterM ℓ)
    -- `sin x ≤ (2/π) x` for `x ∈ [−π/2, 0]`
    have hx : Real.sin (π / 2 - ℓ - ψ) ≤ -(2 / π * (ψ - π / 2 + ℓ)) := by
      have := Real.mul_le_sin (x := ψ - π / 2 + ℓ) (by linarith) (by linarith)
      rw [show π / 2 - ℓ - ψ = -(ψ - π / 2 + ℓ) by ring, Real.sin_neg]; linarith
    have h2 : ℓ / 4 < 2 / π * (ψ - π / 2 + ℓ) := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ (by linarith)]; nlinarith
    linarith [(abs_le.1 h1).2]
  · have e : b * conj (exp ((ψ : ℂ) * I)) = (b - l214CenterP ℓ) * conj (exp ((ψ : ℂ) * I)) +
        exp (((π / 2 + ℓ - ψ : ℝ) : ℂ) * I) := by
      rw [← l214_conj_exp, l214CenterP]; ring
    rw [e, add_im, exp_ofReal_mul_I_im]
    have h1 := herr (b - l214CenterP ℓ)
    have hx := Real.mul_le_sin (x := π / 2 + ℓ - ψ) (by linarith) (by linarith)
    have h2 : ℓ / 4 < 2 / π * (π / 2 + ℓ - ψ) := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ (by linarith)]; nlinarith
    linarith [(abs_le.1 h1).1]

end CONF
end LQGMetric
