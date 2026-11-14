import Mathlib
import LatticeProb.Analysis.W2pApprox

/-!
# The gradients of the smooth approximations are uniformly Cauchy

Let `E` be a finite-dimensional real inner product space of dimension `d`, `μ` an additive Haar
measure and `d < p < ∞`. Suppose `uε n` are smooth approximations of `u` on an open set `U`
(`IsW2pApprox`): `uε n → u` uniformly on compact subsets of `U`, and the Hessians `D² (uε n)`
converge in `L^p` on compact subsets of `U` to a measurable `G`.

Granted the sup bound for the gradient of a `C²` function on a ball in terms of its sup norm and the
`L^p` norm of its Hessian, the gradients `D (uε n)` are uniformly Cauchy on every compact subset of
`U`.

## Main result

* `LatticeProb.PegdenSmart.gradientUniformCauchy_of_supBound`: the sup bound for the gradient
  implies that `fun n => fderiv ℝ (uε n)` is `UniformCauchySeqOn` on every compact `C ⊆ U`.

## Proof outline

A compact `C ⊆ U` has a closed thickening `K' = cthickening δ C ⊆ U`, which is compact. For `z ∈ C`
and `n` large, `uε n` is smooth on `ball z (δ / 2)`, which lies in `K'`. The sup bound applied to
`w = uε m - uε n` on `ball z (δ / 2)` with `ρ = δ / 4` controls `‖D w z‖` by the sup norm of `w`,
which tends to `0` by uniform convergence on `K'`, plus a constant times the `L^p` norm of
`D² w`, which tends to `0` through `G` by the triangle inequality.
-/

open MeasureTheory Metric Filter Topology Asymptotics Set
open scoped InnerProductSpace ContDiff ENNReal NNReal

namespace LatticeProb.PegdenSmart

section Auxiliary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of a difference of two `C²` functions on an open set is the difference of the
derivatives. -/
private lemma fderiv_sub_of_contDiffOn {f g : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 2 f s) (hg : ContDiffOn ℝ 2 g s) :
    ∀ y ∈ s, fderiv ℝ (fun x => f x - g x) y = fderiv ℝ f y - fderiv ℝ g y := fun y hy =>
  fderiv_sub ((hf.differentiableOn (by norm_num)).differentiableAt (hs.mem_nhds hy))
    ((hg.differentiableOn (by norm_num)).differentiableAt (hs.mem_nhds hy))

/-- The second derivative of a difference of two `C²` functions on an open set is the difference of
the second derivatives. -/
private lemma fderiv_fderiv_sub_of_contDiffOn {f g : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 2 f s) (hg : ContDiffOn ℝ 2 g s) :
    ∀ y ∈ s, fderiv ℝ (fderiv ℝ (fun x => f x - g x)) y =
      fderiv ℝ (fderiv ℝ f) y - fderiv ℝ (fderiv ℝ g) y := by
  intro y hy
  have h1 : fderiv ℝ (fun x => f x - g x) =ᶠ[𝓝 y] fun x => fderiv ℝ f x - fderiv ℝ g x :=
    Filter.eventually_of_mem (hs.mem_nhds hy) (fderiv_sub_of_contDiffOn hs hf hg)
  rw [h1.fderiv_eq]
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) y :=
    ((hf.fderiv_of_isOpen hs (m := 1) (by norm_num)).differentiableOn one_ne_zero).differentiableAt
      (hs.mem_nhds hy)
  have hg' : DifferentiableAt ℝ (fderiv ℝ g) y :=
    ((hg.fderiv_of_isOpen hs (m := 1) (by norm_num)).differentiableOn one_ne_zero).differentiableAt
      (hs.mem_nhds hy)
  exact fderiv_sub hf' hg'

end Auxiliary

section HessianNorm

/-- The `L^p` seminorm on a measurable subset of a measurable set `S` is bounded by that of the
indicator of `S`. -/
private lemma eLpNorm_restrict_le_indicator {α F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup F] {p : ℝ≥0∞} {S B : Set α} (hS : MeasurableSet S) (hBS : B ⊆ S)
    (f : α → F) : eLpNorm f p (μ.restrict B) ≤ eLpNorm (S.indicator f) p μ := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hS]
  exact eLpNorm_mono_measure f (Measure.restrict_mono hBS le_rfl)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E]

/-- The `L^p` norm on a ball of the Hessian of a difference of two `C²` functions is bounded by the
`L^p` norms on a larger measurable set `S` of the deviations of the two Hessians from a measurable
`G`. -/
private lemma eLpNorm_fderiv_fderiv_sub_le {μ : Measure E} {p : ℝ≥0∞} (hp1 : 1 ≤ p) {f g : E → ℝ}
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : MeasurableSet S) {z : E}
    {R : ℝ} (hf : ContDiffOn ℝ 2 f (ball z R)) (hg : ContDiffOn ℝ 2 g (ball z R))
    (hSR : ball z R ⊆ S) :
    eLpNorm (fderiv ℝ (fderiv ℝ fun x => f x - g x)) p (μ.restrict (ball z R)) ≤
      eLpNorm (S.indicator fun x => fderiv ℝ (fderiv ℝ f) x - G x) p μ +
        eLpNorm (S.indicator fun x => fderiv ℝ (fderiv ℝ g) x - G x) p μ := by
  have hae : (fderiv ℝ (fderiv ℝ fun x => f x - g x)) =ᵐ[μ.restrict (ball z R)]
      (fun x => fderiv ℝ (fderiv ℝ f) x - G x) - fun x => fderiv ℝ (fderiv ℝ g) x - G x := by
    refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun y hy => ?_)
    simp only [Pi.sub_apply]
    rw [fderiv_fderiv_sub_of_contDiffOn isOpen_ball hf hg y hy]
    abel
  have h1 := eLpNorm_restrict_le_indicator (μ := μ) (p := p) (F := E →L[ℝ] E →L[ℝ] ℝ) hS hSR
    (fun x => fderiv ℝ (fderiv ℝ f) x - G x)
  have h2 := eLpNorm_restrict_le_indicator (μ := μ) (p := p) (F := E →L[ℝ] E →L[ℝ] ℝ) hS hSR
    (fun x => fderiv ℝ (fderiv ℝ g) x - G x)
  have h3 := eLpNorm_sub_le (μ := μ.restrict (ball z R)) (p := p)
    (f := fun x => fderiv ℝ (fderiv ℝ f) x - G x) (g := fun x => fderiv ℝ (fderiv ℝ g) x - G x) hp1
  rw [eLpNorm_congr_ae hae]
  exact h3.trans (add_le_add h1 h2)

end HessianNorm

/-- The sup bound for the gradient of a `C²` function on a ball, in terms of its sup norm and the
`L^p` norm of its Hessian, implies that the gradients of smooth approximations `uε n` are uniformly
Cauchy on every compact subset of `U`. -/
theorem gradientUniformCauchy_of_supBound
    (h4 : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]
      (p : ℝ≥0∞),
      (Module.finrank ℝ E : ℝ≥0∞) < p → p ≠ ⊤ →
      ∃ C : ℝ≥0, ∀ (w : E → ℝ) (a : E) (R ρ K : ℝ), 0 < ρ → ρ < R → 0 ≤ K →
        ContDiffOn ℝ 2 w (ball a R) → (∀ y ∈ ball a R, |w y| ≤ K) →
        ∀ z ∈ ball a (R - ρ),
          ‖fderiv ℝ w z‖ₑ ≤ ENNReal.ofReal (2 * K / ρ) +
            (C : ℝ≥0∞) * ENNReal.ofReal R ^ (1 - (Module.finrank ℝ E : ℝ) / p.toReal) *
              eLpNorm (fderiv ℝ (fderiv ℝ w)) p (μ.restrict (ball a R))) :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]
      (p : ℝ≥0∞),
      (Module.finrank ℝ E : ℝ≥0∞) < p → p ≠ ⊤ →
      ∀ (U : Set E) (u : E → ℝ) (uε : ℕ → E → ℝ) (ε : ℕ → ℝ) (G : E → E →L[ℝ] E →L[ℝ] ℝ),
        IsW2pApprox μ p U u uε ε G →
        ∀ C : Set E, IsCompact C → C ⊆ U →
          UniformCauchySeqOn (fun n => fderiv ℝ (uε n)) atTop C := by
  intro E _ _ _ _ _ _ μ _ p hp hpt U u uε ε G hA C hC hCU
  obtain ⟨hU, -, hε, hsm, hconv, -, hlp⟩ := hA
  obtain ⟨C₀, hC₀⟩ := h4 E μ p hp hpt
  have hd : (Module.finrank ℝ E : ℝ) < p.toReal := by
    have := (ENNReal.toReal_lt_toReal (ENNReal.natCast_ne_top _) hpt).2 hp
    simpa using this
  have hd0 : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos
  have hp1 : 1 ≤ p := by
    have h1 : (1 : ℝ≥0∞) ≤ (Module.finrank ℝ E : ℝ≥0∞) := by exact_mod_cast Module.finrank_pos
    exact h1.trans hp.le
  have hexp : 0 ≤ 1 - (Module.finrank ℝ E : ℝ) / p.toReal := by
    rw [sub_nonneg]
    exact (div_le_one (hd0.trans hd)).2 hd.le
  obtain ⟨δ, hδ, hδU⟩ := hC.exists_cthickening_subset_open hU hCU
  have hK'c : IsCompact (cthickening δ C) := hC.cthickening
  have hK'meas : MeasurableSet (cthickening δ C) := isClosed_cthickening.measurableSet
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ≥0∞, κ = (C₀ : ℝ≥0∞) * ENNReal.ofReal (δ / 2) ^
      (1 - (Module.finrank ℝ E : ℝ) / p.toReal) := ⟨_, rfl⟩
  have hκtop : κ ≠ ⊤ := hκ ▸ ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hexp ENNReal.ofReal_ne_top)
  obtain ⟨Eh, hEh⟩ : ∃ Eh : ℕ → ℝ≥0∞, Eh = fun k => eLpNorm ((cthickening δ C).indicator fun x =>
      fderiv ℝ (fderiv ℝ (uε k)) x - G x) p μ := ⟨_, rfl⟩
  have hEt : Tendsto Eh atTop (𝓝 0) := by
    rw [hEh]
    exact hlp (cthickening δ C) hK'c hδU
  rw [Metric.uniformCauchySeqOn_iff]
  intro η hη
  have hρ : 0 < δ / 4 := by positivity
  have hK : 0 < δ / 4 * η / 4 := by positivity
  obtain ⟨N₁, hN₁⟩ := Metric.uniformCauchySeqOn_iff.1
    (hconv (cthickening δ C) hK'c hδU).uniformCauchySeqOn _ hK
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 ((tendsto_order.1 hε).2 (δ / 2) (half_pos hδ))
  have hη4 : (0 : ℝ≥0∞) < ENNReal.ofReal (η / 4) := ENNReal.ofReal_pos.2 (by positivity)
  have hκE : Tendsto (fun k => κ * Eh k) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hEt (Or.inr hκtop)
    rwa [mul_zero] at this
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 ((tendsto_order.1 hκE).2 _ hη4)
  refine ⟨max N₁ (max N₂ N₃), fun m hm n hn z hz => ?_⟩
  have hm₁ : N₁ ≤ m := (le_max_left _ _).trans hm
  have hm₂ : N₂ ≤ m := ((le_max_left _ _).trans (le_max_right _ _)).trans hm
  have hm₃ : N₃ ≤ m := ((le_max_right _ _).trans (le_max_right _ _)).trans hm
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn₃ : N₃ ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have hzK : ball z (δ / 2) ⊆ cthickening δ C := fun y hy =>
    mem_cthickening_of_dist_le y z δ C hz
      ((mem_ball.1 hy).le.trans (half_le_self hδ.le))
  have hdom : ∀ k, ε k < δ / 2 → ball z (δ / 2) ⊆ {x | closedBall x (ε k) ⊆ U} := by
    intro k hk x hx y hy
    refine hδU (mem_cthickening_of_dist_le y z δ C hz ?_)
    have h1 := mem_closedBall.1 hy
    have h2 := mem_ball.1 hx
    calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
      _ ≤ δ := by linarith
  have hsm2 : ∀ k, ε k < δ / 2 → ContDiffOn ℝ 2 (uε k) (ball z (δ / 2)) := fun k hk =>
    ((hsm k).mono (hdom k hk)).of_le (by simp)
  have hum := hsm2 m (hN₂ m hm₂)
  have hun := hsm2 n (hN₂ n hn₂)
  have hsup : ∀ y ∈ ball z (δ / 2), |uε m y - uε n y| ≤ δ / 4 * η / 4 := fun y hy => by
    have := hN₁ m hm₁ n hn₁ y (hzK hy)
    rw [Real.dist_eq] at this
    exact this.le
  have hmain := hC₀ (fun y => uε m y - uε n y) z (δ / 2) (δ / 4) (δ / 4 * η / 4) hρ
    (by linarith) hK.le (hum.sub hun) hsup z
    (mem_ball_self (by linarith))
  rw [fderiv_sub_of_contDiffOn isOpen_ball hum hun z (mem_ball_self (half_pos hδ))] at hmain
  have hhess : eLpNorm (fderiv ℝ (fderiv ℝ fun y => uε m y - uε n y)) p
      (μ.restrict (ball z (δ / 2))) ≤ Eh m + Eh n := by
    rw [hEh]
    exact eLpNorm_fderiv_fderiv_sub_le (μ := μ) hp1 hK'meas hum hun hzK
  have h2K : 2 * (δ / 4 * η / 4) / (δ / 4) = η / 2 := by field_simp; ring
  rw [h2K] at hmain
  have hstep : ‖fderiv ℝ (uε m) z - fderiv ℝ (uε n) z‖ₑ ≤
      ENNReal.ofReal (η / 2) + (κ * Eh m + κ * Eh n) := by
    rw [← mul_add, hκ]
    exact hmain.trans (by gcongr)
  have hlt : ‖fderiv ℝ (uε m) z - fderiv ℝ (uε n) z‖ₑ < ENNReal.ofReal η := by
    refine hstep.trans_lt ?_
    calc _ < ENNReal.ofReal (η / 2) + (ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4)) :=
          ENNReal.add_lt_add_left ENNReal.ofReal_ne_top
            (ENNReal.add_lt_add (hN₃ m hm₃) (hN₃ n hn₃))
      _ = ENNReal.ofReal η := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  show dist (fderiv ℝ (uε m) z) (fderiv ℝ (uε n) z) < η
  rw [dist_eq_norm]
  rwa [← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff hη] at hlt

end LatticeProb.PegdenSmart
