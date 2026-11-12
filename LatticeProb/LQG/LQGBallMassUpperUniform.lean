import Mathlib
import LatticeProb.LQG.LQGBallMassUpperDyadic
import LatticeProb.LQG.LQGBallMassGrid
import LatticeProb.LQG.LQGMeasureNonatomicMassPoly
import LatticeProb.LQG.LQGMassFatou

/-!
# Uniform upper bound for the LQG mass of small balls on a disc

For the γ-LQG measure `μ` of a whole-plane Gaussian free field, `0 < γ < 2`, and any radius `R`, there are `β, q > 0`
such that, outside an event of probability `O(s^q)`, every ball of radius `s` centred in `B(0, R)` has mass at most
`s^β` (Rhodes-Vargas 2014, Theorem 2.6; Berestycki-Gwynne, arXiv:2003.10320, eq. (A.2)). Only the upper tail of the
ball masses is used; it follows from the positive moments of the quarter-ball mass (`ballMassPosMoment_of_lt`).

* `IsWholePlaneGFF.variance_circle_le_of_norm_le`, `IsWholePlaneGFF.measure_circle_one_gt_le_of_norm_le`: the
  variance bound `Var h_r(z) ≤ log (1/r) + 2 log (R + 1)` and the Chernoff tail of `h_1(z)` for `‖z‖ ≤ R`.
* `upperTail_dyadic_single_of_norm_le`: the upper tail at one ball for a centre with `‖z‖ ≤ R`.
* `ballMassUpperTail_map_sub_of_posMoment`: the single-ball upper tail of the translate `μ(· + c)`.
* `polyHighProb_biInter_finset`: a finite intersection of events of polynomially high probability.
* `IsWholePlaneGFF.polyHighProb_ballMass_upper_ball`, `IsWholePlaneGFF.exists_ballMass_le_rpow_on_ball`: the uniform
  upper bound on `B(0, R)`, obtained by covering the disc with the unit squares `m + i n + [0,1]²`.
-/

universe u

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace LatticeProb.Gauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Variance bound for circle averages.** For `0 < r ≤ 1` and `‖z‖ ≤ R`,
`Var h_r(z) ≤ log (1/r) + 2 log (R + 1)`. -/
theorem IsWholePlaneGFF.variance_circle_le_of_norm_le (hh : IsWholePlaneGFF P hC hcirc) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) :
    Var[fun ω => hcirc ω r z; P] ≤ -Real.log r + 2 * Real.log (R + 1) := by
  have hP := hh.isProbabilityMeasure
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  rw [← covariance_self (hh.hasGaussianLaw_circle hr z).aemeasurable,
    hh.covariance_circle_circle hr hr, wholePlaneGFFCov_circle_circle_eq hr,
    circlePairPotential_self_center hr.le, max_self]
  have hA : Real.circleAverage logMaxAbs z r ≤ Real.log (R + 1) := by
    refine Real.circleAverage_mono_on_of_le_circle
      logMaxAbs_continuous.continuousOn.circleIntegrable' fun x hx => ?_
    have hx' : ‖x - z‖ = r := (mem_sphere_iff_norm.1 hx).trans (abs_of_pos hr)
    have h3 : ‖x‖ ≤ R + 1 := by linarith [norm_sub_norm_le x z]
    unfold logMaxAbs
    exact Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _))
      (max_le h3 (by linarith))
  linarith

/-- **Upper tail of the unit circle average.** For `‖z‖ ≤ R`, `0 < r ≤ 1`, `γ > 0`, `δ, t ≥ 0`:
`P(γ h_1(z) > δ log (1/r)) ≤ 2 (R + 1)^{t²} r^{tδ/γ}`. -/
theorem IsWholePlaneGFF.measure_circle_one_gt_le_of_norm_le (hh : IsWholePlaneGFF P hC hcirc) {z : ℂ}
    {R : ℝ} (hz : ‖z‖ ≤ R) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {γ δ t : ℝ} (hγ : 0 < γ) (ht : 0 ≤ t) :
    P {ω | δ * -Real.log r < γ * hcirc ω 1 z} ≤
      ENNReal.ofReal (2 * (R + 1) ^ (t ^ 2) * r ^ (t * δ / γ)) := by
  have hP := hh.isProbabilityMeasure
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  have hL : 0 ≤ -Real.log r := neg_nonneg.2 (Real.log_nonpos hr.le hr1)
  have hV := hh.variance_circle_le_of_norm_le one_pos le_rfl hz
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
      (R + 1) ^ (t ^ 2) * r ^ (t * δ / γ) := by
    have h1 : -t * (δ * -Real.log r / γ) + Var[fun ω => hcirc ω 1 z; P] * t ^ 2 / 2 ≤
        Real.log (R + 1) * t ^ 2 + Real.log r * (t * δ / γ) := by
      have h2 : -t * (δ * -Real.log r / γ) = Real.log r * (t * δ / γ) := by
        field_simp
      rw [h2]
      nlinarith [mul_le_mul_of_nonneg_right hV (sq_nonneg t)]
    calc _ ≤ Real.exp (Real.log (R + 1) * t ^ 2 + Real.log r * (t * δ / γ)) := Real.exp_le_exp.2 h1
      _ = _ := by
        rw [Real.exp_add, ← Real.rpow_def_of_pos (by linarith : (0 : ℝ) < R + 1),
          ← Real.rpow_def_of_pos hr]
  calc P {ω | δ * -Real.log r < γ * hcirc ω 1 z}
      ≤ P {ω | δ * -Real.log r / γ ≤ |hcirc ω 1 z|} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | δ * -Real.log r / γ ≤ |hcirc ω 1 z|}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (2 * (R + 1) ^ (t ^ 2) * r ^ (t * δ / γ)) := by
        refine ENNReal.ofReal_le_ofReal (hcher.trans ?_)
        calc _ ≤ 2 * ((R + 1) ^ (t ^ 2) * r ^ (t * δ / γ)) := by gcongr
          _ = _ := by ring

end LatticeProb.Gauss

namespace LatticeProb.LQG

open LatticeProb.Gauss LatticeProb.LQG.LQGDyadicScaling LatticeProb.LQG.LQGMeasureNonatomicMass

/-- **The upper tail at one ball, centre in `B̄(0, R)`.** For `‖z‖ ≤ R`, `r = 2^{-j}`, and a moment bound
`E[μ'(B(0,1/4))^p] ≤ C` for the LQG measure of the recentred field,
`P(μ(B(z, r/4)) > r^b) ≤ 2 (R + 1)^{t²} r^{tδ/γ} + C r^{p(2+γ²/2-b-δ) - p²γ²/2}`. -/
theorem upperTail_dyadic_single_of_norm_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ)
    {p : ℝ} (hp : 0 < p) {C : ℝ≥0∞} (j : ℕ) {z : ℂ} {R : ℝ}
    (hmom : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (μ' : Ω → Measure ℂ),
      IsWholePlaneGFF P hC' (recentredField hcirc j z) →
      IsLQGMeasure P γ (recentredField hcirc j z) μ' → ∫⁻ ω, (μ' ω (ball 0 (1 / 4))) ^ p ∂P ≤ C)
    (hz : ‖z‖ ≤ R) {b δ t : ℝ} (ht : 0 ≤ t) :
    P {ω | ENNReal.ofReal (dyadicScale j ^ b) < μ ω (ball z (dyadicScale j * (1 / 4)))} ≤
      ENNReal.ofReal (2 * (R + 1) ^ (t ^ 2) * dyadicScale j ^ (t * δ / γ)) +
        C * ENNReal.ofReal (dyadicScale j ^ (p * (2 + γ ^ 2 / 2 - b - δ) - p ^ 2 * γ ^ 2 / 2)) := by
  obtain ⟨hC', hh'⟩ := isWholePlaneGFF_recentredField hh j z
  obtain ⟨μ', hμ'⟩ := hh'.exists_isLQGMeasure hγ0 hγ2
  have hr0 : 0 < dyadicScale j := dyadicScale_pos' j
  have hr1 : dyadicScale j ≤ 1 := dyadicScale_le_one' j
  have hα : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hM' : AEMeasurable (fun ω => μ' ω (ball 0 (1 / 4))) P :=
    aemeasurable_lqgMeasure_borel hγ0 hγ2 hα hh' (isLQGMeasureOfField_zero hμ')
      (lqgLocality_of_gff P γ 0 hC' (recentredField hcirc j z)) _ measurableSet_ball
  have hind : IndepFun (fun ω => hcirc ω (dyadicScale j) z - hcirc ω 1 z)
      (fun ω => μ' ω (ball 0 (1 / 4))) P := by
    have h0 := hh'.indepFun_circle_measure_open hγ0 hγ2 hμ' (R := (dyadicScale j)⁻¹)
      ((one_le_inv₀ hr0).2 hr1) (U := ball 0 (1 / 4)) isOpen_ball
      (ball_subset_ball (by norm_num))
    have e : (fun ω => hcirc ω (dyadicScale j) z - hcirc ω 1 z) =
        (fun x : ℝ => -x) ∘ (fun ω => recentredField hcirc j z ω (dyadicScale j)⁻¹ 0) := by
      funext ω
      simp only [Function.comp, recentredField, mul_inv_cancel₀ hr0.ne', mul_zero, zero_add]
      ring
    rw [e]
    exact h0.comp (φ := fun x : ℝ => -x) (ψ := id) measurable_neg measurable_id
  have hmass : ∀ᵐ ω ∂P, μ ω (ball z (dyadicScale j * (1 / 4))) ≤
      ENNReal.ofReal (dyadicScale j ^ (2 + γ ^ 2 / 2) *
        Real.exp (γ * (hcirc ω 1 z + (hcirc ω (dyadicScale j) z - hcirc ω 1 z)))) *
        μ' ω (ball 0 (1 / 4)) := by
    filter_upwards [ae_measure_ball_eq hγ0 hμ j z hμ'] with ω hω
    rw [hω _ (by norm_num), add_sub_cancel]
    exact le_rfl
  have hv : (((Real.log (1 / dyadicScale j)).toNNReal : ℝ≥0) : ℝ) ≤ -Real.log (dyadicScale j) := by
    rw [Real.coe_toNNReal', one_div, Real.log_inv]
    exact max_le le_rfl (neg_nonneg.2 (Real.log_nonpos hr0.le hr1))
  exact upperTail_single (X := fun ω => hcirc ω (dyadicScale j) z - hcirc ω 1 z)
    (Y := fun ω => hcirc ω 1 z) (Mass := fun ω => μ ω (ball z (dyadicScale j * (1 / 4))))
    (M' := fun ω => μ' ω (ball 0 (1 / 4))) hr0 hp (hh.hasLaw_incr_le hr0 hr1 z) hv hM' hind
    (hmom hC' μ' hh' hμ') hmass (hh.measure_circle_one_gt_le_of_norm_le hz hr0 hr1 hγ0 ht)

/-- The translate `A ↦ μ(A + c)` charges `B(z, r)` with the mass of `B(z + c, r)`. -/
theorem map_sub_ball (ν : Measure ℂ) (c z : ℂ) (r : ℝ) :
    ν.map (fun x => x - c) (ball z r) = ν (ball (z + c) r) := by
  rw [Measure.map_apply (by fun_prop : Measurable fun x : ℂ => x - c) measurableSet_ball]
  congr 1
  ext x
  simp only [Set.mem_preimage, mem_ball, dist_eq_norm]
  rw [sub_sub, add_comm c z]

/-- **Single-ball upper tail of a translate.** For the γ-LQG measure `μ` of a whole-plane GFF, `0 < γ < 2`, a
positive moment `E[μ(B(0,1/4))^{2/γ}] ≤ C` (uniform over models) gives the single-ball upper tail of
`A ↦ μ(A + c)`, for every `c ∈ ℂ`: balls centred in `c + [0,1]²`. -/
theorem ballMassUpperTail_map_sub_of_posMoment.{v} {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ)
    (hPos : BallMassPosMoment.{v} γ (2 / γ)) (c : ℂ) :
    BallMassUpperTail P γ (fun ω => (μ ω).map (fun x => x - c)) := by
  obtain ⟨C, hCm⟩ := hPos
  refine ballMassUpperTail_of_dyadic fun b hb => ?_
  simp only [map_sub_ball]
  obtain ⟨b'', hb''⟩ : ∃ b'' : ℝ, b'' = (b + (2 - γ) ^ 2 / 2) / 2 := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ((2 - γ) ^ 2 / 2 - b) / 4 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hp0 : 0 < 2 / γ := by positivity
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = 2 + 2 * δ / γ := ⟨_, rfl⟩
  have hE2 : 2 < E := by
    have : 0 < 2 * δ / γ := by positivity
    rw [hE]; linarith
  have hE0 : 0 < E := by linarith
  have hexp : (2 / γ) * (2 + γ ^ 2 / 2 - b'' - δ) - (2 / γ) ^ 2 * γ ^ 2 / 2 = E := by
    rw [hb'', hE]; exact upper_exponent_eq hγ0 hδ
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = γ * E / δ := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have htE : t * δ / γ = E := by rw [ht]; field_simp
  have hbb : 0 < b'' - b := by rw [hb'']; linarith
  obtain ⟨r₁, hr₁, H1⟩ :=
    exists_pos_forall_of_eventually_nhdsGT (eventually_mul_rpow_lt_one ((4 : ℝ) ^ b) hbb)
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, dyadicScale k₀ < r₁ :=
    exists_pow_lt_of_lt_one hr₁ (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨E, hE2, (2 * (‖c‖ + 2 + 1) ^ (t ^ 2) + C) * (4 : ℝ) ^ E, k₀ + 2, ?_⟩
  intro z hz j hj
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  have hr : dyadicScale k < r₁ := lt_of_le_of_lt (dyadicScale_le_of_le (by omega : k₀ ≤ k)) hk₀
  have hr0 : 0 < dyadicScale k := dyadicScale_pos' k
  have hz2 : ‖z + c‖ ≤ ‖c‖ + 2 := by
    obtain ⟨h1, h2⟩ := Complex.mem_reProdIm.1 hz
    have a1 : |z.re| ≤ 1 := abs_le.2 ⟨by linarith [h1.1], h1.2⟩
    have a2 : |z.im| ≤ 1 := abs_le.2 ⟨by linarith [h2.1], h2.2⟩
    linarith [Complex.norm_le_abs_re_add_abs_im z, norm_add_le z c]
  have h4 : (0 : ℝ) < (4 : ℝ) ^ b := by positivity
  have h41 : (4 : ℝ) ^ b * (1 / 4 : ℝ) ^ b = 1 := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have hsmall : dyadicScale k ^ (b'' - b) ≤ (1 / 4 : ℝ) ^ b := by
    refine le_of_mul_le_mul_left ?_ h4
    rw [h41]
    exact (H1 _ hr0 hr).le
  have hsub : {ω | ENNReal.ofReal (dyadicScale (k + 2) ^ b) < μ ω (ball (z + c) (dyadicScale (k + 2)))} ⊆
      {ω | ENNReal.ofReal (dyadicScale k ^ b'') <
        μ ω (ball (z + c) (dyadicScale k * (1 / 4)))} := by
    intro ω hω
    have hω' : ENNReal.ofReal (dyadicScale (k + 2) ^ b) < μ ω (ball (z + c) (dyadicScale (k + 2))) := hω
    rw [dyadicScale_add_two] at hω'
    show ENNReal.ofReal (dyadicScale k ^ b'') < μ ω (ball (z + c) (dyadicScale k * (1 / 4)))
    refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hω'
    calc dyadicScale k ^ b'' = dyadicScale k ^ b * dyadicScale k ^ (b'' - b) := by
          rw [← Real.rpow_add hr0]; congr 1; ring
      _ ≤ dyadicScale k ^ b * (1 / 4 : ℝ) ^ b :=
          mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hr0.le _)
      _ = (dyadicScale k * (1 / 4)) ^ b := (Real.mul_rpow hr0.le (by norm_num)).symm
  refine (measure_mono hsub).trans ?_
  refine (upperTail_dyadic_single_of_norm_le hγ0 hγ2 hh hμ hp0 k (C := (C : ℝ≥0∞))
    (fun hC' μ' h h' => hCm Ω P hC' _ μ' h h') hz2 (b := b'') (δ := δ) ht0).trans ?_
  rw [htE, hexp, dyadicScale_add_two]
  have h41E : (4 : ℝ) ^ E * (1 / 4 : ℝ) ^ E = 1 := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have e1 : (2 * (‖c‖ + 2 + 1) ^ (t ^ 2) + C) * (4 : ℝ) ^ E * (dyadicScale k * (1 / 4)) ^ E =
      2 * (‖c‖ + 2 + 1) ^ (t ^ 2) * dyadicScale k ^ E + C * dyadicScale k ^ E := by
    calc (2 * (‖c‖ + 2 + 1) ^ (t ^ 2) + C) * (4 : ℝ) ^ E * (dyadicScale k * (1 / 4)) ^ E
        = (2 * (‖c‖ + 2 + 1) ^ (t ^ 2) + C) * dyadicScale k ^ E * ((4 : ℝ) ^ E * (1 / 4 : ℝ) ^ E) := by
          rw [Real.mul_rpow hr0.le (by norm_num)]; ring
      _ = _ := by rw [h41E]; ring
  rw [e1, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul C.coe_nonneg,
    ENNReal.ofReal_coe_nnreal]

/-- A finite intersection of event families of polynomially high probability has polynomially high
probability. -/
theorem polyHighProb_biInter_finset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*}
    {E : ι → ℝ → Set Ω} (s : Finset ι) (h : ∀ i ∈ s, PolyHighProb P (E i)) :
    PolyHighProb P fun r => ⋂ i ∈ s, E i r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, 0, 1, one_pos, fun r _ _ => by simp⟩
  | insert a s ha ih =>
    refine polyHighProb_mono (polyHighProb_inter (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))) fun r ω hω => ?_
    rw [Finset.set_biInter_insert]
    exact hω

/-- The integer lattice point `⌊Re z⌋ + i ⌊Im z⌋` puts `z` in its unit square. -/
theorem sub_floor_mem_unitSquare (z : ℂ) :
    z - ((⌊z.re⌋ : ℂ) + (⌊z.im⌋ : ℂ) * Complex.I) ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1 := by
  refine Complex.mem_reProdIm.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im] <;>
    norm_num <;> exact (Int.fract_lt_one _).le

/-- **Uniform upper bound on a disc, polynomially high probability form.** For the γ-LQG measure `μ` of a
whole-plane GFF, `0 < γ < 2`, `R ∈ ℝ` and `β_upper > 2/(2-γ)²`: with polynomially high probability as `ε → 0`, every
ball of radius `ε^{β_upper}` centred in `B(0, R)` has mass at most `ε`. -/
theorem _root_.LatticeProb.Gauss.IsWholePlaneGFF.polyHighProb_ballMass_upper_ball {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {γ : ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (R : ℝ)
    {βu : ℝ} (hβu : 2 / (2 - γ) ^ 2 < βu) :
    PolyHighProb P fun ε => {ω | ∀ z ∈ ball (0 : ℂ) R, μ ω (ball z (ε ^ βu)) ≤ ENNReal.ofReal ε} := by
  have hPos : BallMassPosMoment.{u} γ (2 / γ) := by
    refine ballMassPosMoment_of_lt hγ0.ne' ?_ ?_
    · rw [le_div_iff₀ hγ0]; linarith
    · rw [div_mul_eq_mul_div, div_lt_iff₀ hγ0]; nlinarith
  set N : ℕ := ⌈R⌉₊ with hN
  set G : Finset ℂ := ((Finset.Icc (-(N : ℤ)) N) ×ˢ (Finset.Icc (-(N : ℤ)) N)).image
    (fun m : ℤ × ℤ => (m.1 : ℂ) + (m.2 : ℂ) * Complex.I) with hG
  have hall := polyHighProb_biInter_finset (P := P) G (E := fun c ε => {ω | ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
      (μ ω).map (fun x => x - c) (ball z (ε ^ βu)) ≤ ENNReal.ofReal ε})
    fun c _ => polyHighProb_ballMass_upper (ballMassUpperTail_map_sub_of_posMoment hγ0 hγ2 hh hμ hPos c) hγ2 hβu
  refine polyHighProb_mono hall fun ε ω hω z hz => ?_
  set c : ℂ := (⌊z.re⌋ : ℂ) + (⌊z.im⌋ : ℂ) * Complex.I with hc
  have hzR : ‖z‖ < R := mem_ball_zero_iff.1 hz
  have hRN : R ≤ (N : ℝ) := Nat.le_ceil R
  have hre : |z.re| < N := lt_of_le_of_lt (Complex.abs_re_le_norm z) (hzR.trans_le hRN)
  have him : |z.im| < N := lt_of_le_of_lt (Complex.abs_im_le_norm z) (hzR.trans_le hRN)
  have hmem : ∀ x : ℝ, |x| < N → ⌊x⌋ ∈ Finset.Icc (-(N : ℤ)) N := by
    intro x hx
    rw [Finset.mem_Icc]
    obtain ⟨h1, h2⟩ := abs_lt.1 hx
    constructor
    · exact Int.le_floor.2 (by push_cast; linarith)
    · have : (⌊x⌋ : ℝ) ≤ N := (Int.floor_le x).trans h2.le
      exact_mod_cast this
  have hcG : c ∈ G := Finset.mem_image.2 ⟨(⌊z.re⌋, ⌊z.im⌋), Finset.mem_product.2 ⟨hmem _ hre, hmem _ him⟩, rfl⟩
  have hωc := Set.mem_iInter₂.1 hω c hcG
  have key := hωc (z - c) (sub_floor_mem_unitSquare z)
  rwa [map_sub_ball, sub_add_cancel] at key

/-- **Uniform upper bound for the LQG mass of small balls on a disc** (Rhodes-Vargas 2014, Theorem 2.6). For the
γ-LQG measure `μ` of a whole-plane GFF, `0 < γ < 2` and `R ∈ ℝ`, there are `β, q, r₀ > 0` and `K` such that for
`0 < s < r₀`, with probability at least `1 - K s^q`, every ball of radius `s` centred in `B(0, R)` has mass at most
`s^β`. -/
theorem _root_.LatticeProb.Gauss.IsWholePlaneGFF.exists_ballMass_le_rpow_on_ball {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {γ : ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (R : ℝ) :
    ∃ β q K r₀ : ℝ, 0 < β ∧ 0 < q ∧ 0 < r₀ ∧ ∀ s : ℝ, 0 < s → s < r₀ →
      P {ω | ∀ z ∈ ball (0 : ℂ) R, μ ω (ball z s) ≤ ENNReal.ofReal (s ^ β)}ᶜ ≤
        ENNReal.ofReal (K * s ^ q) := by
  have hβu : 2 / (2 - γ) ^ 2 < 2 / (2 - γ) ^ 2 + 1 := lt_add_one _
  have hβu0 : 0 < 2 / (2 - γ) ^ 2 + 1 := by positivity
  obtain ⟨q, hq, K, r₀, hr₀, hb⟩ := polyHighProb_comp_rpow
    (hh.polyHighProb_ballMass_upper_ball hμ hγ0 hγ2 R hβu) (inv_pos.2 hβu0)
  refine ⟨(2 / (2 - γ) ^ 2 + 1)⁻¹, q, K, r₀, inv_pos.2 hβu0, hq, hr₀, fun s hs hsr => ?_⟩
  have h := hb s hs hsr
  beta_reduce at h
  rwa [Real.rpow_inv_rpow hs.le hβu0.ne'] at h

end LatticeProb.LQG
