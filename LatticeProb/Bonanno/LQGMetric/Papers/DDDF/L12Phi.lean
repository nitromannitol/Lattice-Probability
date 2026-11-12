/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L12Phi at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L12Strip
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L12Mob
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DDDF Lemma 12′: the conjugated map `Φ = G ∘ M ∘ G⁻¹` on a neighbourhood of `S_ρ`

For `ρ ∈ (0,1)` and a Möbius automorphism `M(ζ) = ρ · mob β κ (ζ/ρ)` of `D_ρ`, the map
`Φ = G ∘ M ∘ T` (`T = G⁻¹`) is injective and holomorphic on an open bounded neighbourhood `U₀` of
`S_ρ = G(D̄_ρ)`, with `C⁻¹ ≤ |Φ'| ≤ C` and `|Φ''| ≤ C` on `U₀`. This replaces the Schwarz
reflection step of DF Thm 3.1 Step 1 (arXiv:1809.02607, l. 655–656): `U₀` is the image under `G`
of a slightly larger disc, and the bounds come from compactness of `G(D̄_{r₁})` inside the
domain of holomorphy (decision D-B4, D-DDDF-14). The nonvanishing of `Φ'` uses
`QuantumZipper.CA.deriv_ne_zero_of_injOn` (injective holomorphic maps have `f' ≠ 0`).
-/

namespace LQGMetric.DDDF.L12

open Set Real Metric

/-- The scaled automorphism `M(ζ) = ρ · mob β κ (ζ/ρ)` of the disc `D_ρ`. -/
noncomputable def mobR (ρ β κ : ℝ) (ζ : ℂ) : ℂ := (ρ : ℂ) * mob β κ (ζ / ρ)

/-- The conjugated map `Φ = G ∘ M ∘ G⁻¹`. -/
noncomputable def phiM (ρ β κ : ℝ) (w : ℂ) : ℂ := sG (mobR ρ β κ (sT w))

lemma continuousOn_sT : ContinuousOn sT {w : ℂ | |w.im| < π / 2} :=
  fun _ hw => (differentiableAt_sT hw).continuousAt.continuousWithinAt

lemma isOpen_strip : IsOpen {w : ℂ | |w.im| < π / 2} :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem exists_nbhd_phiM {ρ β κ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hβ : |Real.sin β| < Real.cos β) :
    ∃ U₀ : Set ℂ, IsOpen U₀ ∧ Bornology.IsBounded U₀ ∧ sG '' closedBall 0 ρ ⊆ U₀ ∧
      U₀ ⊆ {w : ℂ | |w.im| < π / 2} ∧
      DifferentiableOn ℂ (phiM ρ β κ) U₀ ∧ InjOn (phiM ρ β κ) U₀ ∧
      ∃ C > 0, ∀ w ∈ U₀, C⁻¹ ≤ ‖deriv (phiM ρ β κ) w‖ ∧ ‖deriv (phiM ρ β κ) w‖ ≤ C ∧
        ‖deriv (deriv (phiM ρ β κ)) w‖ ≤ C := by
  have hρc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ0.ne'
  -- the open set `W` of good points of the disc
  set O1 := {ζ : ℂ | mobDen β κ (ζ / ρ) ≠ 0} with hO1
  have hO1o : IsOpen O1 :=
    isOpen_ne_fun (by unfold mobDen; fun_prop) continuous_const
  have hmc : ContinuousOn (fun ζ => ‖mobR ρ β κ ζ‖) O1 := by
    intro ζ hζ
    have hc : ContinuousAt (fun ζ : ℂ => mob β κ (ζ / ρ)) ζ :=
      ContinuousAt.comp (f := fun ζ : ℂ => ζ / (ρ : ℂ)) (differentiableAt_mob hζ).continuousAt
        (by fun_prop)
    exact ((continuousAt_const.mul hc).norm).continuousWithinAt
  set W := (O1 ∩ ball 0 1) ∩ (fun ζ => ‖mobR ρ β κ ζ‖) ⁻¹' Iio 1 with hW
  have hWo : IsOpen W :=
    (hmc.mono inter_subset_left).isOpen_inter_preimage (hO1o.inter isOpen_ball) isOpen_Iio
  have hmob_le : ∀ ζ : ℂ, ‖ζ‖ ≤ ρ → ‖ζ / ρ‖ ≤ 1 := by
    intro ζ hζ
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hρ0.le, div_le_one hρ0]; exact hζ
  have hKW : closedBall (0 : ℂ) ρ ⊆ W := by
    intro ζ hζ
    rw [mem_closedBall, dist_zero_right] at hζ
    refine ⟨⟨mobDen_ne hβ (hmob_le ζ hζ), ?_⟩, ?_⟩
    · rw [mem_ball, dist_zero_right]; linarith
    · show ‖mobR ρ β κ ζ‖ < 1
      rw [mobR, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
      have := norm_mob_le_one (κ := κ) hβ (hmob_le ζ hζ)
      nlinarith
  obtain ⟨δ, hδ0, hδ⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_thickening_subset_open hWo hKW
  rw [thickening_closedBall hδ0 hρ0.le] at hδ
  set r₁ := ρ + δ / 2 with hr₁
  have hr₁W : closedBall (0 : ℂ) r₁ ⊆ W := fun ζ hζ => hδ (by
    rw [mem_closedBall] at hζ; rw [mem_ball]; linarith)
  have hW1 : ∀ ζ ∈ W, ‖ζ‖ < 1 := fun ζ hζ => by
    have := hζ.1.2; rwa [mem_ball, dist_zero_right] at this
  -- the sets
  set U₁ := {w : ℂ | |w.im| < π / 2} ∩ sT ⁻¹' ball 0 (δ + ρ) with hU₁
  set U₀ := {w : ℂ | |w.im| < π / 2} ∩ sT ⁻¹' ball 0 r₁ with hU₀
  have hU₁o : IsOpen U₁ := continuousOn_sT.isOpen_inter_preimage isOpen_strip isOpen_ball
  have hU₀o : IsOpen U₀ := continuousOn_sT.isOpen_inter_preimage isOpen_strip isOpen_ball
  set C₀ := sG '' closedBall 0 r₁ with hC₀
  have hsGc : ContinuousOn sG (closedBall 0 r₁) := fun ζ hζ =>
    (differentiableAt_sG (hW1 ζ (hr₁W hζ))).continuousAt.continuousWithinAt
  have hC₀c : IsCompact C₀ := (isCompact_closedBall _ _).image_of_continuousOn hsGc
  have hU₀C₀ : U₀ ⊆ C₀ := fun w hw =>
    ⟨sT w, ball_subset_closedBall hw.2, sG_sT hw.1⟩
  have hC₀U₁ : C₀ ⊆ U₁ := by
    rintro _ ⟨ζ, hζ, rfl⟩
    have h1 := hW1 ζ (hr₁W hζ)
    refine ⟨abs_im_sG_lt h1, ?_⟩
    show sT (sG ζ) ∈ ball 0 (δ + ρ)
    rw [sT_sG h1, mem_ball]; rw [mem_closedBall] at hζ; linarith
  have hKU₀ : sG '' closedBall 0 ρ ⊆ U₀ := by
    rintro _ ⟨ζ, hζ, rfl⟩
    have h1 := hW1 ζ (hKW hζ)
    refine ⟨abs_im_sG_lt h1, ?_⟩
    show sT (sG ζ) ∈ ball 0 r₁
    rw [sT_sG h1, mem_ball]; rw [mem_closedBall] at hζ; linarith
  -- holomorphy and injectivity on `U₁`
  have hU₁W : ∀ w ∈ U₁, sT w ∈ W := fun w hw => hδ hw.2
  have hdiff : DifferentiableOn ℂ (phiM ρ β κ) U₁ := by
    intro w hw
    have hW := hU₁W w hw
    have hM : DifferentiableAt ℂ (mobR ρ β κ) (sT w) :=
      (differentiableAt_const _).mul (DifferentiableAt.comp (f := fun ζ : ℂ => ζ / (ρ : ℂ))
        (x := sT w) (differentiableAt_mob hW.1.1) (by fun_prop))
    have hG : DifferentiableAt ℂ sG (mobR ρ β κ (sT w)) := by
      apply differentiableAt_sG; exact hW.2
    have he : phiM ρ β κ = sG ∘ (mobR ρ β κ ∘ sT) := rfl
    rw [he]
    exact (hG.comp w (hM.comp w (differentiableAt_sT hw.1))).differentiableWithinAt
  have hinj : InjOn (phiM ρ β κ) U₁ := by
    intro x hx y hy hxy
    have hWx := hU₁W x hx
    have hWy := hU₁W y hy
    have h1 : mobR ρ β κ (sT x) = mobR ρ β κ (sT y) := by
      refine injOn_sG ?_ ?_ hxy
      · rw [mem_ball, dist_zero_right]; exact hWx.2
      · rw [mem_ball, dist_zero_right]; exact hWy.2
    have h2 : sT x / ρ = sT y / ρ := by
      refine injOn_mob hβ hWx.1.1 hWy.1.1 ?_
      have := h1; unfold mobR at this; exact mul_left_cancel₀ hρc this
    have h3 : sT x = sT y := by
      have := congrArg (· * (ρ : ℂ)) h2; simpa [div_mul_cancel₀ _ hρc] using this
    exact injOn_sT hx.1 hy.1 h3
  -- bounds by compactness
  have hd1 : DifferentiableOn ℂ (deriv (phiM ρ β κ)) U₁ := hdiff.deriv hU₁o
  have hd2 : DifferentiableOn ℂ (deriv (deriv (phiM ρ β κ))) U₁ := hd1.deriv hU₁o
  have hne : ∀ w ∈ U₁, deriv (phiM ρ β κ) w ≠ 0 := fun w hw =>
    QuantumZipper.CA.deriv_ne_zero_of_injOn hU₁o hdiff hinj hw
  obtain ⟨C1, hC1⟩ := hC₀c.exists_bound_of_continuousOn (hd1.continuousOn.mono hC₀U₁)
  obtain ⟨C2, hC2⟩ := hC₀c.exists_bound_of_continuousOn (hd2.continuousOn.mono hC₀U₁)
  obtain ⟨C3, hC3⟩ := hC₀c.exists_bound_of_continuousOn
    ((hd1.continuousOn.mono hC₀U₁).inv₀ fun w hw => hne w (hC₀U₁ hw))
  refine ⟨U₀, hU₀o, hC₀c.isBounded.subset hU₀C₀, hKU₀, fun w hw => hw.1,
    hdiff.mono (fun w hw => hC₀U₁ (hU₀C₀ hw)), hinj.mono (fun w hw => hC₀U₁ (hU₀C₀ hw)),
    max 1 (max C1 (max C2 C3)), by positivity, fun w hw => ?_⟩
  have hwC := hU₀C₀ hw
  have hpos : 0 < ‖deriv (phiM ρ β κ) w‖ := norm_pos_iff.2 (hne w (hC₀U₁ hwC))
  refine ⟨?_, (hC1 w hwC).trans (by simp), (hC2 w hwC).trans (by simp)⟩
  apply inv_le_of_inv_le₀ hpos
  have := hC3 w hwC
  rw [Pi.inv_apply, norm_inv] at this
  exact this.trans (by simp)

end LQGMetric.DDDF.L12
