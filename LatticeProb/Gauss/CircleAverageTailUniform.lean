import LatticeProb.Gauss.CircleAverageRadialBrownian
import LatticeProb.Gauss.GaussianBorelCantelli

/-!
# One-point tail bound for circle averages of the whole-plane Gaussian free field

For a whole-plane Gaussian free field `h`, a centre `w` with `‖w‖ ≤ R r̄`, and `0 < ε < 1`, we bound
the probability that a circle average `h_r(w)` with `r ∈ [ε^{1+ν} r̄, ε r̄]` differs from the
circle average `h_{r̄}(0)` by at least `q log (1/ε)`.  The bound is
`2 ε^{s²/(2ν)} + 2 (1+R)^{(q-s)²} ε^{(q-s)²/2}` for every `0 < s < q`: it combines the Brownian
supremum bound for the radial increment `h_r(w) - h_{ε r̄}(w)` with the Gaussian tail of the centred
Gaussian `h_{ε r̄}(w) - h_{r̄}(0)`, whose variance is at most `log (1/ε) + 2 log (1+R)`.

* `LatticeProb.Gauss.circlePairPotential_le_log`: upper bound of the averaged logarithmic potential;
* `IsWholePlaneGFF.variance_circle_sub_start_le`: the variance bound above;
* `IsWholePlaneGFF.measure_circle_sub_ge_le`: Gaussian tail of a difference of two circle averages;
* `IsWholePlaneGFF.measure_exists_circle_sub_start_ge_le`: the one-point bound.
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb.Gauss

/-- If the circle `∂B_r(z)` lies in the closed disc of radius `t` about `w` and `0 < s ≤ t`, then the
averaged potential with cut-off `s` is at most `log t`. -/
theorem circlePairPotential_le_log {z w : ℂ} {r s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (h : ∀ x ∈ sphere z |r|, ‖x - w‖ ≤ t) : circlePairPotential z r w s ≤ Real.log t := by
  unfold circlePairPotential
  refine Real.circleAverage_mono_on_of_le_circle
    (continuous_log_max_norm_sub hs w).continuousOn.circleIntegrable' fun x hx => ?_
  exact Real.log_le_log (lt_of_lt_of_le hs (le_max_left _ _)) (max_le hst (h x hx))

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Variance of the starting increment.** For `0 < ε ≤ 1`, `r̄ > 0`, `R ≥ 0` and `‖w‖ ≤ R r̄`,
`Var[h_{ε r̄}(w) - h_{r̄}(0)] ≤ log (1/ε) + 2 log (1 + R)`. -/
theorem variance_circle_sub_start_le (hh : IsWholePlaneGFF P hC hcirc) {ε R rbar : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (hr : 0 < rbar) (hR : 0 ≤ R) {w : ℂ} (hw : ‖w‖ ≤ R * rbar) :
    Var[fun ω => hcirc ω (ε * rbar) w - hcirc ω rbar 0; P] ≤
      -Real.log ε + 2 * Real.log (1 + R) := by
  have hρ : 0 < ε * rbar := mul_pos hε0 hr
  have hρle : ε * rbar ≤ rbar := by nlinarith
  have hbig : 0 < (1 + R) * rbar := mul_pos (by linarith) hr
  have e1 : circlePairPotential w (ε * rbar) 0 rbar ≤ Real.log ((1 + R) * rbar) :=
    circlePairPotential_le_log hr (by nlinarith) fun x hx => by
      have hx' : ‖x - w‖ = ε * rbar := (mem_sphere_iff_norm.1 hx).trans (abs_of_pos hρ)
      have := norm_sub_norm_le x w
      rw [sub_zero]
      nlinarith
  have e2 : circlePairPotential 0 rbar w (ε * rbar) ≤ Real.log ((1 + R) * rbar) :=
    circlePairPotential_le_log hρ (by nlinarith) fun x hx => by
      have hx' : ‖x - 0‖ = rbar := (mem_sphere_iff_norm.1 hx).trans (abs_of_pos hr)
      have := norm_sub_le x w
      rw [sub_zero] at hx'
      nlinarith
  rw [hh.variance_circle_sub_eq hρ hr w 0, circlePairPotential_self_center hρ.le,
    circlePairPotential_self_center hr.le, max_self (ε * rbar), max_self rbar,
    Real.log_mul hε0.ne' hr.ne']
  rw [Real.log_mul (by linarith : (1 + R) ≠ 0) hr.ne'] at e1 e2
  linarith

/-- **Gaussian tail of a difference of two circle averages.** If the variance of
`h_r(z) - h_s(w)` is at most `V > 0`, then `P(a ≤ |h_r(z) - h_s(w)|) ≤ 2 exp (-a² / (2 V))`. -/
theorem measure_circle_sub_ge_le (hh : IsWholePlaneGFF P hC hcirc) {r s : ℝ} (hr : 0 < r)
    (hs : 0 < s) (z w : ℂ) {V a : ℝ} (hV : 0 < V)
    (hvar : Var[fun ω => hcirc ω r z - hcirc ω s w; P] ≤ V) (ha : 0 ≤ a) :
    P {ω | a ≤ |hcirc ω r z - hcirc ω s w|} ≤ ENNReal.ofReal (2 * Real.exp (-(a ^ 2 / (2 * V)))) := by
  have hP := hh.isProbabilityMeasure
  have hG := hh.hasGaussianLaw_circle_sub hr hs z w
  have hmean := hh.integral_circle_sub hr hs z w
  have hlaw : HasLaw (fun ω => hcirc ω r z - hcirc ω s w)
      (gaussianReal 0 (Var[fun ω => hcirc ω r z - hcirc ω s w; P]).toNNReal) P :=
    ⟨hG.aemeasurable, by rw [hG.map_eq_gaussianReal, hmean]⟩
  have hvar0 : 0 ≤ Var[fun ω => hcirc ω r z - hcirc ω s w; P] := variance_nonneg _ _
  have hcher := GaussBC.measureReal_le_abs_le hlaw (a := a) (div_nonneg ha hV.le)
  rw [Real.coe_toNNReal _ hvar0] at hcher
  have hexp : -(a / V) * a + Var[fun ω => hcirc ω r z - hcirc ω s w; P] * (a / V) ^ 2 / 2 ≤
      -(a ^ 2 / (2 * V)) := by
    have h1 : Var[fun ω => hcirc ω r z - hcirc ω s w; P] * (a / V) ^ 2 / 2 ≤ V * (a / V) ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_right hvar (sq_nonneg (a / V))
      linarith
    have h2 : -(a / V) * a + V * (a / V) ^ 2 / 2 = -(a ^ 2 / (2 * V)) := by
      field_simp
      ring
    linarith
  calc P {ω | a ≤ |hcirc ω r z - hcirc ω s w|}
      = ENNReal.ofReal (P.real {ω | a ≤ |hcirc ω r z - hcirc ω s w|}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hcher.trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) (by norm_num)))

/-- **One-point bound.** Let `0 < ε < 1`, `r̄ > 0`, `R ≥ 0`, `ν > 0`, `0 < s < q` and `‖w‖ ≤ R r̄`.  Then
`P {∃ r ∈ [ε^{1+ν} r̄, ε r̄], q log (1/ε) ≤ |h_r(w) - h_{r̄}(0)|}
  ≤ 2 ε^{s²/(2ν)} + 2 (1+R)^{(q-s)²} ε^{(q-s)²/2}`. -/
theorem measure_exists_circle_sub_start_ge_le (hh : IsWholePlaneGFF P hC hcirc) {ε R rbar ν q s : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hr : 0 < rbar) (hR : 0 ≤ R) (hν : 0 < ν) (hs : 0 < s)
    (hsq : s < q) {w : ℂ} (hw : ‖w‖ ≤ R * rbar) :
    P {ω | ∃ r ∈ Icc (ε ^ (1 + ν) * rbar) (ε * rbar),
        q * -Real.log ε ≤ |hcirc ω r w - hcirc ω rbar 0|} ≤
      ENNReal.ofReal (2 * ε ^ (s ^ 2 / (2 * ν)) +
        2 * Real.exp ((q - s) ^ 2 * Real.log (1 + R)) * ε ^ ((q - s) ^ 2 / 2)) := by
  set L : ℝ := -Real.log ε with hL
  have hL0 : 0 < L := neg_pos.2 (Real.log_neg hε0 hε1)
  set c : ℝ := 2 * Real.log (1 + R) with hc
  have hc0 : 0 ≤ c := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + R by linarith)
    linarith
  have hρ : 0 < ε * rbar := mul_pos hε0 hr
  have hlogε : Real.log ε = -L := by rw [hL]; ring
  -- radial part
  have hA := hh.measure_exists_circle_sub_ge_le hρ w (T := ν * L) (a := s * L) (mul_pos hν hL0)
    (mul_pos hs hL0)
  -- starting part
  have hvar := hh.variance_circle_sub_start_le hε0 hε1.le hr hR hw
  have hB := hh.measure_circle_sub_ge_le (mul_pos hε0 hr) hr w 0 (V := L + c) (by linarith)
    (by rw [← hL] at hvar; linarith) (a := (q - s) * L) (mul_nonneg (by linarith) hL0.le)
  have hexpε : ∀ x : ℝ, ε ^ x = Real.exp (-(x * L)) := fun x => by
    rw [Real.rpow_def_of_pos hε0, hlogε]
    congr 1
    ring
  have hsub : {ω | ∃ r ∈ Icc (ε ^ (1 + ν) * rbar) (ε * rbar),
        q * L ≤ |hcirc ω r w - hcirc ω rbar 0|} ⊆
      {ω | ∃ r ∈ Icc (ε * rbar * Real.exp (-(ν * L))) (ε * rbar),
        s * L ≤ |hcirc ω r w - hcirc ω (ε * rbar) w|} ∪
      {ω | (q - s) * L ≤ |hcirc ω (ε * rbar) w - hcirc ω rbar 0|} := by
    rintro ω ⟨r, ⟨hr1, hr2⟩, hω⟩
    have hr1' : ε * rbar * Real.exp (-(ν * L)) ≤ r := by
      refine le_trans (le_of_eq ?_) hr1
      rw [Real.rpow_add hε0, Real.rpow_one, hexpε ν]
      ring
    by_cases h1 : s * L ≤ |hcirc ω r w - hcirc ω (ε * rbar) w|
    · exact Or.inl ⟨r, ⟨hr1', hr2⟩, h1⟩
    · have h1' := not_le.1 h1
      refine Or.inr ?_
      have htri : |hcirc ω r w - hcirc ω rbar 0| ≤
          |hcirc ω r w - hcirc ω (ε * rbar) w| + |hcirc ω (ε * rbar) w - hcirc ω rbar 0| := by
        have := abs_add_le (hcirc ω r w - hcirc ω (ε * rbar) w)
          (hcirc ω (ε * rbar) w - hcirc ω rbar 0)
        rwa [sub_add_sub_cancel] at this
      show (q - s) * L ≤ _
      linarith
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
  have hA' : P {ω | ∃ r ∈ Icc (ε * rbar * Real.exp (-(ν * L))) (ε * rbar),
      s * L ≤ |hcirc ω r w - hcirc ω (ε * rbar) w|} ≤ ENNReal.ofReal (2 * ε ^ (s ^ 2 / (2 * ν))) := by
    have e : Real.exp (-((s * L) ^ 2 / (2 * (ν * L)))) = ε ^ (s ^ 2 / (2 * ν)) := by
      rw [hexpε]
      congr 1
      have hLne := hL0.ne'
      have hνne := hν.ne'
      field_simp
    refine hA.trans (le_of_eq ?_)
    rw [e, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hB' : P {ω | (q - s) * L ≤ |hcirc ω (ε * rbar) w - hcirc ω rbar 0|} ≤
      ENNReal.ofReal (2 * Real.exp ((q - s) ^ 2 * Real.log (1 + R)) * ε ^ ((q - s) ^ 2 / 2)) := by
    refine hB.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hexpε, mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
    have h1 : (q - s) ^ 2 * Real.log (1 + R) = (q - s) ^ 2 * c / 2 := by rw [hc]; ring
    have h2 : ((q - s) * L) ^ 2 / (2 * (L + c)) ≥ (q - s) ^ 2 * (L - c) / 2 := by
      rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith [sq_nonneg (q - s), mul_nonneg (sq_nonneg (q - s)) (sq_nonneg c)]
    rw [h1]
    nlinarith
  calc _ ≤ ENNReal.ofReal (2 * ε ^ (s ^ 2 / (2 * ν))) +
        ENNReal.ofReal (2 * Real.exp ((q - s) ^ 2 * Real.log (1 + R)) * ε ^ ((q - s) ^ 2 / 2)) :=
        add_le_add hA' hB'
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]

end IsWholePlaneGFF

end LatticeProb.Gauss
