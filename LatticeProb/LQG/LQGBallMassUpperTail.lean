import Mathlib
import LatticeProb.LQG.LQGCircleTail
import LatticeProb.LQG.LQGBallMassLowerTail

/-! # Upper tail of the mass of a small ball: the Chernoff and Markov assembly

For the γ-LQG measure `μ` of a whole-plane GFF and a ball `B(z, r)`, the mass is bounded, up to the factor
`μ'(B(0, 1/4))`-type mass of the recentred field, by
  `r^{γQ} e^{γ h_r(z)} M'`,  `h_r(z) = h_1(z) + X`,  `X = h_r(z) - h_1(z)`,
where `X ∼ N(0, log (1/r))` is independent of `M'`. The upper tail of the mass is obtained by splitting off the
event `{γ h_1(z) > δ log (1/r)}` (Chernoff bound for the Gaussian `h_1(z)`) and applying Markov's inequality of
order `p` to `e^{γ X} M'` on the complement: independence factors the moment, `E[e^{pγX}] = r^{-p²γ²/2}`.

Main results:
* `IsWholePlaneGFF.measure_circle_one_gt_le`: Chernoff upper tail of `h_1(z)`, `‖z‖ ≤ 2`.
* `upperTail_single`: the elementary estimate at one ball, for generic masses and exponents.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace LatticeProb.Gauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Upper tail of the unit circle average.** For `‖z‖ ≤ 2`, `0 < r ≤ 1`, `γ > 0`, `δ, t ≥ 0`:
`P(γ h_1(z) > δ log (1/r)) ≤ 2 · 3^{t²} · r^{tδ/γ}`. -/
theorem IsWholePlaneGFF.measure_circle_one_gt_le (hh : IsWholePlaneGFF P hC hcirc) {z : ℂ}
    (hz : ‖z‖ ≤ 2) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {γ δ t : ℝ} (hγ : 0 < γ) (ht : 0 ≤ t) :
    P {ω | δ * -Real.log r < γ * hcirc ω 1 z} ≤
      ENNReal.ofReal (2 * (3 : ℝ) ^ (t ^ 2) * r ^ (t * δ / γ)) := by
  have hP := hh.isProbabilityMeasure
  have hL : 0 ≤ -Real.log r := neg_nonneg.2 (Real.log_nonpos hr.le hr1)
  have hV := hh.variance_circle_le one_pos le_rfl hz
  rw [Real.log_one, neg_zero, zero_add] at hV
  have hvar0 : 0 ≤ Var[fun ω => hcirc ω 1 z; P] := variance_nonneg _ _
  have hlaw := hh.hasLaw_circle one_pos z
  have hsub : {ω | δ * -Real.log r < γ * hcirc ω 1 z} ⊆
      {ω | δ * -Real.log r / γ ≤ |hcirc ω 1 z|} := by
    intro ω hω
    have hω' : δ * -Real.log r < γ * hcirc ω 1 z := hω
    show δ * -Real.log r / γ ≤ |hcirc ω 1 z|
    have : δ * -Real.log r / γ ≤ hcirc ω 1 z := by
      rw [div_le_iff₀ hγ]; linarith
    exact this.trans (le_abs_self _)
  have hcher := GaussBC.measureReal_le_abs_le hlaw (a := δ * -Real.log r / γ) ht
  rw [Real.coe_toNNReal _ hvar0] at hcher
  have hexp : Real.exp (-t * (δ * -Real.log r / γ) + Var[fun ω => hcirc ω 1 z; P] * t ^ 2 / 2) ≤
      (3 : ℝ) ^ (t ^ 2) * r ^ (t * δ / γ) := by
    have h1 : -t * (δ * -Real.log r / γ) + Var[fun ω => hcirc ω 1 z; P] * t ^ 2 / 2 ≤
        Real.log 3 * t ^ 2 + Real.log r * (t * δ / γ) := by
      have h2 : -t * (δ * -Real.log r / γ) = Real.log r * (t * δ / γ) := by
        field_simp
      rw [h2]
      nlinarith [mul_le_mul_of_nonneg_right hV (sq_nonneg t)]
    calc _ ≤ Real.exp (Real.log 3 * t ^ 2 + Real.log r * (t * δ / γ)) := Real.exp_le_exp.2 h1
      _ = _ := by
        rw [Real.exp_add, ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
          ← Real.rpow_def_of_pos hr]
  calc P {ω | δ * -Real.log r < γ * hcirc ω 1 z}
      ≤ P {ω | δ * -Real.log r / γ ≤ |hcirc ω 1 z|} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | δ * -Real.log r / γ ≤ |hcirc ω 1 z|}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (2 * (3 : ℝ) ^ (t ^ 2) * r ^ (t * δ / γ)) := by
        refine ENNReal.ofReal_le_ofReal (hcher.trans ?_)
        calc _ ≤ 2 * ((3 : ℝ) ^ (t ^ 2) * r ^ (t * δ / γ)) := by gcongr
          _ = _ := by ring

end LatticeProb.Gauss

namespace LatticeProb.LQG

/-- **Upper tail at one ball, from the scaling relation.** Let `0 < r ≤ 1`, `γ, p > 0`. Suppose
`X ∼ N(0, v)` with `v ≤ log (1/r)` is independent of `M'` and `E[M'^p] ≤ C`, and almost surely the mass satisfies
`Mass ≤ r^a e^{γ (Y + X)} M'`. If `P(γ Y > δ log (1/r)) ≤ T` then
`P(Mass > r^b) ≤ T + C r^{p (a - b - δ) - p² γ²/2}`. -/
theorem upperTail_single {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}
    {Mass M' : Ω → ℝ≥0∞} {γ r a b δ p : ℝ} {v : ℝ≥0} {C T : ℝ≥0∞} (hr0 : 0 < r) (hp : 0 < p) (hXlaw : HasLaw X (gaussianReal 0 v) P) (hv : (v : ℝ) ≤ -Real.log r)
    (hM' : AEMeasurable M' P) (hind : IndepFun X M' P) (hmom : ∫⁻ ω, M' ω ^ p ∂P ≤ C)
    (hmass : ∀ᵐ ω ∂P, Mass ω ≤ ENNReal.ofReal (r ^ a * Real.exp (γ * (Y ω + X ω))) * M' ω)
    (hY : P {ω | δ * -Real.log r < γ * Y ω} ≤ T) :
    P {ω | ENNReal.ofReal (r ^ b) < Mass ω} ≤
      T + C * ENNReal.ofReal (r ^ (p * (a - b - δ) - p ^ 2 * γ ^ 2 / 2)) := by
  obtain ⟨W, hW⟩ : ∃ W : Ω → ℝ≥0∞, W = fun ω => ENNReal.ofReal (Real.exp (γ * X ω)) * M' ω :=
    ⟨_, rfl⟩
  have hWω : ∀ ω, W ω = ENNReal.ofReal (Real.exp (γ * X ω)) * M' ω := fun ω => by rw [hW]
  have hs0 : 0 < r ^ (b - a + δ) := Real.rpow_pos_of_pos hr0 _
  have hsub : {ω | ENNReal.ofReal (r ^ b) < Mass ω} ≤ᵐ[P]
      ({ω | δ * -Real.log r < γ * Y ω} ∪ {ω | ENNReal.ofReal (r ^ (b - a + δ)) < W ω} : Set Ω) := by
    filter_upwards [hmass] with ω hω hev
    by_contra hnot
    rw [Set.mem_union, not_or] at hnot
    have hY' : γ * Y ω ≤ δ * -Real.log r := not_lt.1 hnot.1
    have hnW : ¬ ENNReal.ofReal (r ^ (b - a + δ)) < W ω := hnot.2
    have hev' : ENNReal.ofReal (r ^ b) < Mass ω := hev
    have hexpY : Real.exp (γ * Y ω) ≤ r ^ (-δ) := by
      rw [Real.rpow_def_of_pos hr0]
      apply Real.exp_le_exp.2
      linarith
    have h1 : r ^ a * Real.exp (γ * (Y ω + X ω)) ≤ r ^ (a - δ) * Real.exp (γ * X ω) := by
      calc r ^ a * Real.exp (γ * (Y ω + X ω))
          = r ^ a * Real.exp (γ * Y ω) * Real.exp (γ * X ω) := by
            rw [mul_add, Real.exp_add]; ring
        _ ≤ r ^ a * r ^ (-δ) * Real.exp (γ * X ω) := by gcongr
        _ = r ^ (a - δ) * Real.exp (γ * X ω) := by
            rw [← Real.rpow_add hr0, ← sub_eq_add_neg]
    have h2 : Mass ω ≤ ENNReal.ofReal (r ^ (a - δ)) * W ω := by
      calc Mass ω ≤ ENNReal.ofReal (r ^ a * Real.exp (γ * (Y ω + X ω))) * M' ω := hω
        _ ≤ ENNReal.ofReal (r ^ (a - δ) * Real.exp (γ * X ω)) * M' ω :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal h1) le_rfl
        _ = ENNReal.ofReal (r ^ (a - δ)) * W ω := by
            rw [hWω, ENNReal.ofReal_mul (Real.rpow_nonneg hr0.le _), mul_assoc]
    have h3 : ENNReal.ofReal (r ^ b) =
        ENNReal.ofReal (r ^ (a - δ)) * ENNReal.ofReal (r ^ (b - a + δ)) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr0.le _), ← Real.rpow_add hr0]
      congr 2
      ring
    have h4 : ENNReal.ofReal (r ^ (a - δ)) * ENNReal.ofReal (r ^ (b - a + δ)) <
        ENNReal.ofReal (r ^ (a - δ)) * W ω := by
      rw [← h3]; exact lt_of_lt_of_le hev' h2
    have h5 := mul_le_mul' (le_refl (ENNReal.ofReal (r ^ (a - δ)))) (not_lt.1 hnW)
    exact absurd h4 (not_lt.2 h5)
  -- the moment of `W`
  have hfm : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (p * γ * x))) := by fun_prop
  have hWmeas : AEMeasurable W P := by
    rw [hW]
    exact ((ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul measurable_id))).comp_aemeasurable hXlaw.aemeasurable).mul hM'
  have hmom_f : ∫⁻ ω, ENNReal.ofReal (Real.exp (p * γ * X ω)) ∂P ≤
      ENNReal.ofReal (r ^ (-(p ^ 2 * γ ^ 2 / 2))) := by
    have hint : Integrable (fun ω => Real.exp (p * γ * X ω)) P :=
      hXlaw.integrable_comp (f := fun x : ℝ => Real.exp ((p * γ) * x))
        (integrable_exp_mul_gaussianReal (p * γ))
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => (Real.exp_pos _).le)]
    apply ENNReal.ofReal_le_ofReal
    have hmgf := mgf_gaussianReal hXlaw (p * γ)
    change ∫ ω, Real.exp (p * γ * X ω) ∂P ≤ _
    have : ∫ ω, Real.exp (p * γ * X ω) ∂P = mgf X P (p * γ) := rfl
    rw [this, hmgf, Real.rpow_def_of_pos hr0]
    apply Real.exp_le_exp.2
    have hv' : (v : ℝ) * (p * γ) ^ 2 ≤ -Real.log r * (p * γ) ^ 2 :=
      mul_le_mul_of_nonneg_right hv (sq_nonneg _)
    nlinarith
  have hind' : IndepFun (fun ω => ENNReal.ofReal (Real.exp (p * γ * X ω))) (fun ω => M' ω ^ p) P :=
    hind.comp hfm (ENNReal.continuous_rpow_const.measurable)
  have hmomW : ∫⁻ ω, W ω ^ p ∂P ≤ ENNReal.ofReal (r ^ (-(p ^ 2 * γ ^ 2 / 2))) * C := by
    have hpt : ∀ ω, W ω ^ p = ENNReal.ofReal (Real.exp (p * γ * X ω)) * M' ω ^ p := fun ω => by
      rw [hWω, ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
        ← Real.exp_mul, mul_comm (γ * X ω) p, mul_assoc]
    simp_rw [hpt]
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
      (f := fun ω => ENNReal.ofReal (Real.exp (p * γ * X ω))) (g := fun ω => M' ω ^ p)
      (hfm.comp_aemeasurable hXlaw.aemeasurable) (hM'.pow_const p) hind']
    exact mul_le_mul' hmom_f hmom
  -- Markov
  have hmk := mul_meas_ge_le_lintegral₀ (hWmeas.pow_const p) (ENNReal.ofReal (r ^ (b - a + δ)) ^ p)
  have hsubM : {ω | ENNReal.ofReal (r ^ (b - a + δ)) < W ω} ⊆
      {ω | ENNReal.ofReal (r ^ (b - a + δ)) ^ p ≤ W ω ^ p} := fun ω hω =>
    ENNReal.rpow_le_rpow (le_of_lt hω) hp.le
  have hcancel : ENNReal.ofReal ((r ^ (b - a + δ)) ^ (-p)) *
      ENNReal.ofReal (r ^ (b - a + δ)) ^ p = 1 := by
    rw [ENNReal.ofReal_rpow_of_pos hs0, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _),
      ← Real.rpow_add hs0, neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one]
  have hB : P {ω | ENNReal.ofReal (r ^ (b - a + δ)) < W ω} ≤
      C * ENNReal.ofReal (r ^ (p * (a - b - δ) - p ^ 2 * γ ^ 2 / 2)) := by
    calc P {ω | ENNReal.ofReal (r ^ (b - a + δ)) < W ω}
        = ENNReal.ofReal ((r ^ (b - a + δ)) ^ (-p)) *
            (ENNReal.ofReal (r ^ (b - a + δ)) ^ p *
              P {ω | ENNReal.ofReal (r ^ (b - a + δ)) < W ω}) := by
          rw [← mul_assoc, hcancel, one_mul]
      _ ≤ ENNReal.ofReal ((r ^ (b - a + δ)) ^ (-p)) *
            (ENNReal.ofReal (r ^ (b - a + δ)) ^ p *
              P {ω | ENNReal.ofReal (r ^ (b - a + δ)) ^ p ≤ W ω ^ p}) := by
          gcongr
      _ ≤ ENNReal.ofReal ((r ^ (b - a + δ)) ^ (-p)) *
            (ENNReal.ofReal (r ^ (-(p ^ 2 * γ ^ 2 / 2))) * C) :=
          mul_le_mul_right (hmk.trans hmomW) _
      _ = C * (ENNReal.ofReal ((r ^ (b - a + δ)) ^ (-p)) *
            ENNReal.ofReal (r ^ (-(p ^ 2 * γ ^ 2 / 2)))) := by ring
      _ = C * ENNReal.ofReal (r ^ (p * (a - b - δ) - p ^ 2 * γ ^ 2 / 2)) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _), ← Real.rpow_mul hr0.le,
            ← Real.rpow_add hr0]
          congr 3
          ring
  calc P {ω | ENNReal.ofReal (r ^ b) < Mass ω}
      ≤ P ({ω | δ * -Real.log r < γ * Y ω} ∪ {ω | ENNReal.ofReal (r ^ (b - a + δ)) < W ω}) :=
        measure_mono_ae hsub
    _ ≤ P {ω | δ * -Real.log r < γ * Y ω} + P {ω | ENNReal.ofReal (r ^ (b - a + δ)) < W ω} :=
        measure_union_le _ _
    _ ≤ T + C * ENNReal.ofReal (r ^ (p * (a - b - δ) - p ^ 2 * γ ^ 2 / 2)) := add_le_add hY hB

end LatticeProb.LQG
