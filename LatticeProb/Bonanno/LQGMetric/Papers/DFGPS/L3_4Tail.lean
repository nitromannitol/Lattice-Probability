/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_4Tail at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Defs
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldMax
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Oscillation

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 3.4, ingredients: the two Gaussian tail bounds (task P2-DFA0)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), proof of Lemma 3.4,
T:1495–1507:

* (3.6), `eqn-gaussian-tail-inc`: `t ↦ h_{e^{−t} ε𝕣}(w) − h_{ε𝕣}(w)` is a standard Brownian
  motion (DS arXiv:0808.1560 §3.1), so `sup_{r ∈ [ε^{1+ν}𝕣, ε𝕣]} |h_r(w) − h_{ε𝕣}(w)|` has a
  Gaussian tail (`tail_bm_part`). The process `B_t = h_{ρe^{−t}}(w) − h_ρ(w)` is a
  pre-Brownian motion (`isPreBrownianReal_cInc_base`, mathlib
  `IsGaussianProcess.isPreBrownianReal_of_covariance`, covariance from `covariance_cInc`), and
  the maximal tail along a countable set of times is QuantumZipper's Doob bound
  `BMOsc.tail_abs` on sorted finite grids plus monotone limits (`preBM_countable_tail`).
* (3.7), `eqn-gaussian-tail-start`: `h_{ε𝕣}(w) − h_𝕣(0)` is centered Gaussian with variance
  `≤ log ε⁻¹ + 2 log(R+1)` for `w ∈ B_{R𝕣}(0)` (`incCov_far_le`, `tail_far_part`); the Gaussian
  tail is `DDDF.tail_abs_of_hasLaw`.

Radii range over a countable set `S` (DEVIATIONS: DFA0-1): `circleAvg` is the a.s. defined
limit of mollified averages, not the continuous version, so only countably many radii are
controlled simultaneously; every use of L3.4 (P3.1, L3.11) involves countably many radii.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace LQGMetric.DFGPS
namespace L34

open CircleAvg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## Maximal tail of a pre-Brownian motion along a countable set of times -/

theorem preBM_finite_tail {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hBm : ∀ r, Measurable (B r)) {D : Set ℝ≥0} (hD : D.Finite) {T : ℝ} (hT : 0 < T)
    (hDT : ∀ t ∈ D, (t : ℝ) ≤ T) {a : ℝ} (ha : 0 < a) :
    P {ω | ∃ t ∈ D, a < |B t ω - B 0 ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-(a ^ 2) / (2 * T))) := by
  classical
  set F := hD.toFinset
  set e := F.orderEmbOfFin rfl
  set u : ℕ → ℝ≥0 := fun k => if hk : k < F.card then e ⟨k, hk⟩ else T.toNNReal with hu_def
  have hu : Monotone u := by
    intro i j hij
    simp only [hu_def]
    split_ifs with hi hj hj
    · exact e.monotone (Fin.mk_le_mk.2 hij)
    · exact (Real.le_toNNReal_iff_coe_le hT.le).2
        (hDT _ (hD.mem_toFinset.1 (F.orderEmbOfFin_mem rfl _)))
    · omega
    · exact le_rfl
  have hun : ((u F.card - 0 : ℝ≥0) : ℝ) ≤ T := by
    simp [hu_def, hT.le]
  refine le_trans (measure_mono ?_)
    (QuantumZipper.BMOsc.tail_abs hB hBm hu (by simp) F.card ha hT hun)
  rintro ω ⟨t, ht, hlt⟩
  have htF : t ∈ Set.range e := by
    rw [Finset.range_orderEmbOfFin]; exact hD.mem_toFinset.2 ht
  obtain ⟨i, rfl⟩ := htF
  have hui : u i.1 = e i := by simp [hu_def, i.2]
  exact ⟨i.1, i.2.le, by rw [hui]; exact hlt⟩

theorem preBM_countable_tail {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hBm : ∀ r, Measurable (B r)) {D : Set ℝ≥0} (hD : D.Countable) {T : ℝ} (hT : 0 < T)
    (hDT : ∀ t ∈ D, (t : ℝ) ≤ T) {a : ℝ} (ha : 0 < a) :
    P {ω | ∃ t ∈ D, a < |B t ω - B 0 ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-(a ^ 2) / (2 * T))) := by
  rcases D.eq_empty_or_nonempty with hDe | hDne
  · subst hDe; simp
  obtain ⟨f, rfl⟩ := hD.exists_eq_range hDne
  set S : ℕ → Set ℝ≥0 := fun m => f '' Set.Iio m
  have hmono : Monotone fun m => {ω | ∃ t ∈ S m, a < |B t ω - B 0 ω|} := by
    intro m m' hmm' ω hω
    obtain ⟨t, ht, h⟩ := hω
    exact ⟨t, Set.image_mono (Set.Iio_subset_Iio hmm') ht, h⟩
  have hsub : {ω | ∃ t ∈ Set.range f, a < |B t ω - B 0 ω|} ⊆
      ⋃ m, {ω | ∃ t ∈ S m, a < |B t ω - B 0 ω|} := by
    rintro ω ⟨t, ⟨k, rfl⟩, h⟩
    exact Set.mem_iUnion.2 ⟨k + 1, f k, ⟨k, Nat.lt_succ_self k, rfl⟩, h⟩
  refine (measure_mono hsub).trans ?_
  rw [hmono.measure_iUnion]
  exact iSup_le fun m => preBM_finite_tail hB hBm ((Set.finite_Iio m).image f) hT
    (fun t ht => hDT t (Set.image_subset_range _ _ ht)) ha

/-! ## `t ↦ h_{ρe^{−t}}(w) − h_ρ(w)` is a pre-Brownian motion -/

lemma posLog_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.posLog (Real.exp x) = x := by
  rw [Real.posLog_eq_log (by rw [abs_of_pos (Real.exp_pos x)]; exact Real.one_le_exp hx),
    Real.log_exp]

lemma posLog_exp_of_nonpos {x : ℝ} (hx : x ≤ 0) : Real.posLog (Real.exp x) = 0 :=
  (Real.posLog_eq_zero_iff _).mpr (by
    rw [abs_of_pos (Real.exp_pos x)]; exact Real.exp_le_one_iff.mpr hx)

lemma incCov_brownian_base (w : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (s t : ℝ≥0) (hst : s ≤ t) :
    incCov w (ρ * Real.exp (-(s : ℝ))) w ρ w (ρ * Real.exp (-(t : ℝ))) w ρ = s := by
  have ha : 0 < ρ * Real.exp (-(s : ℝ)) := by positivity
  have hc : 0 < ρ * Real.exp (-(t : ℝ)) := by positivity
  have hs0 : (0 : ℝ) ≤ s := s.2
  have hst' : (s : ℝ) ≤ t := hst
  simp only [incCov]
  rw [circCov_center w ha _ hc, circCov_center w ha ρ hρ, circCov_center w hρ _ hc,
    circCov_center w hρ ρ hρ, inv_mul_cancel₀ hρ.ne', Real.posLog_one]
  have e1 : (ρ * Real.exp (-(t : ℝ)))⁻¹ * (ρ * Real.exp (-(s : ℝ))) =
      Real.exp ((t : ℝ) - s) := by
    rw [Real.exp_sub, Real.exp_neg, Real.exp_neg]; field_simp
  have e2 : ρ⁻¹ * (ρ * Real.exp (-(s : ℝ))) = Real.exp (-(s : ℝ)) := by field_simp
  have e3 : (ρ * Real.exp (-(t : ℝ)))⁻¹ * ρ = Real.exp (t : ℝ) := by
    rw [Real.exp_neg]; field_simp
  have e4 : Real.log (ρ * Real.exp (-(t : ℝ))) = Real.log ρ - t := by
    rw [Real.log_mul hρ.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
  rw [e1, e2, e3, e4, posLog_exp_of_nonneg (by linarith), posLog_exp_of_nonpos (by linarith),
    posLog_exp_of_nonneg (show (0 : ℝ) ≤ t from t.2)]
  ring

variable {h : Ω → DistC}

theorem isPreBrownianReal_cInc_base (hh : IsWholePlaneGFF h P) (w : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    IsPreBrownianReal (fun t : ℝ≥0 => cInc h (ρ * Real.exp (-(t : ℝ))) w ρ w) P := by
  have := hh.gaussian.isProbabilityMeasure
  have hGP : IsGaussianProcess (fun t : ℝ≥0 => cInc h (ρ * Real.exp (-(t : ℝ))) w ρ w) P :=
    (isGaussianProcess_incProc hh).comp_right fun t : ℝ≥0 =>
      (((⟨ρ * Real.exp (-(t : ℝ)), mul_pos hρ (Real.exp_pos _)⟩ : Ioi (0 : ℝ)), w),
        ((⟨ρ, hρ⟩ : Ioi (0 : ℝ)), w))
  refine hGP.isPreBrownianReal_of_covariance (fun t => ?_) fun s t hst => ?_
  · exact integral_cInc hh (by positivity) hρ w w
  · rw [covariance_cInc hh (by positivity) hρ (by positivity) hρ,
      incCov_brownian_base w hρ s t hst]

/-- (3.6): the maximal tail of `|h_r(w) − h_ρ(w)|` over a countable set of radii
`S ⊆ [ρ₀, ρ]`. -/
theorem tail_bm_part (hh : IsWholePlaneGFF h P) (w : ℂ) {ρ₀ ρ : ℝ} (hρ₀ : 0 < ρ₀)
    (hρ₀ρ : ρ₀ < ρ) {S : Set ℝ} (hS : S.Countable) (hSI : S ⊆ Icc ρ₀ ρ) {b : ℝ} (hb : 0 < b) :
    P {ω | ∃ r ∈ S, b < |cInc h r w ρ w ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-(b ^ 2) / (2 * Real.log (ρ / ρ₀)))) := by
  have hρ : 0 < ρ := hρ₀.trans hρ₀ρ
  set B : ℝ≥0 → Ω → ℝ := fun t => cInc h (ρ * Real.exp (-(t : ℝ))) w ρ w
  set τ : ℝ → ℝ≥0 := fun r => (Real.log (ρ / r)).toNNReal
  have hT : 0 < Real.log (ρ / ρ₀) := Real.log_pos ((one_lt_div hρ₀).2 hρ₀ρ)
  have hτ : ∀ r ∈ S, B (τ r) = cInc h r w ρ w := by
    intro r hr
    have hr0 : 0 < r := hρ₀.trans_le (hSI hr).1
    have hl : 0 ≤ Real.log (ρ / r) := Real.log_nonneg ((one_le_div hr0).2 (hSI hr).2)
    simp only [B, τ, Real.coe_toNNReal _ hl]
    rw [Real.exp_neg, Real.exp_log (div_pos hρ hr0)]
    congr 1; field_simp
  have hB0 : ∀ ω, B 0 ω = 0 := fun ω => by simp [B, cInc]
  have hsub : {ω | ∃ r ∈ S, b < |cInc h r w ρ w ω|} ⊆
      {ω | ∃ t ∈ τ '' S, b < |B t ω - B 0 ω|} := by
    rintro ω ⟨r, hr, hlt⟩
    exact ⟨τ r, ⟨r, hr, rfl⟩, by rw [hB0, sub_zero, hτ r hr]; exact hlt⟩
  refine (measure_mono hsub).trans (preBM_countable_tail (isPreBrownianReal_cInc_base hh w hρ)
    (fun t => measurable_cInc hh _ _ _ _) (hS.image τ) hT ?_ hb)
  rintro _ ⟨r, hr, rfl⟩
  have hr0 : 0 < r := hρ₀.trans_le (hSI hr).1
  have hl : 0 ≤ Real.log (ρ / r) := Real.log_nonneg ((one_le_div hr0).2 (hSI hr).2)
  simp only [τ, Real.coe_toNNReal _ hl]
  exact Real.log_le_log (div_pos hρ hr0) (div_le_div_of_nonneg_left hρ.le hρ₀ (hSI hr).1)

/-! ## (3.7): the far increment `h_a(w) − h_ρ(0)` -/

/-- `Var(h_a(w) − h_ρ(0)) ≤ log(ρ/a) + 2 log(R+1)` for `a ≤ ρ`, `‖w‖ ≤ Rρ`. -/
lemma incCov_far_le (w : ℂ) {a ρ R : ℝ} (ha : 0 < a) (haρ : a ≤ ρ) (hR : 0 ≤ R)
    (hw : ‖w‖ ≤ R * ρ) :
    incCov w a 0 ρ w a 0 ρ ≤ Real.log (ρ / a) + 2 * Real.log (R + 1) := by
  have hρ : 0 < ρ := ha.trans_le haρ
  have hb : circCov w a 0 ρ ≤ Real.log ρ + Real.log (R + 1) := by
    unfold circCov
    refine Real.circleAverage_mono_on_of_le_circle
      ((continuous_circLog hρ.ne' 0).continuousOn.circleIntegrable') fun x hx => ?_
    rw [Metric.mem_sphere, abs_of_pos ha, dist_eq_norm] at hx
    rw [circLog_eq hρ.ne', zero_sub, norm_neg]
    have hx' : ‖x‖ ≤ (R + 1) * ρ := by
      have := norm_le_norm_add_norm_sub' x w
      have : ‖x‖ ≤ ‖w‖ + ‖x - w‖ := by
        calc ‖x‖ = ‖w + (x - w)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      nlinarith
    have hpl : Real.posLog (ρ⁻¹ * ‖x‖) ≤ Real.log (R + 1) := by
      rw [Real.posLog_def]
      refine max_le (Real.log_nonneg (by linarith)) ?_
      rcases (mul_nonneg (inv_nonneg.2 hρ.le) (norm_nonneg x)).eq_or_lt with h0 | h0
      · rw [← h0]; simp only [Real.log_zero]; exact Real.log_nonneg (by linarith)
      · refine Real.log_le_log h0 ?_
        rw [inv_mul_le_iff₀ hρ]; linarith
    linarith
  have hb' : circCov 0 ρ w a = circCov w a 0 ρ := circCov_comm hρ ha 0 w
  simp only [incCov]
  rw [circCov_center w ha a ha, circCov_center 0 hρ ρ hρ, hb', inv_mul_cancel₀ ha.ne',
    inv_mul_cancel₀ hρ.ne', Real.posLog_one, Real.log_div hρ.ne' ha.ne']
  linarith

/-- (3.7): the Gaussian tail of `h_a(w) − h_ρ(0)`. -/
theorem tail_far_part [IsProbabilityMeasure P] (hh : IsWholePlaneGFF h P) {w : ℂ} {a ρ R : ℝ}
    (ha : 0 < a) (haρ : a ≤ ρ) (hR : 0 ≤ R) (hw : ‖w‖ ≤ R * ρ) {y : ℝ} (hy : 0 < y) :
    P {ω | y ≤ |cInc h a w ρ 0 ω|} ≤ ENNReal.ofReal (2 * Real.exp (-y ^ 2 /
      (2 * (Real.log (ρ / a) + 2 * Real.log (R + 1))))) := by
  have hρ : 0 < ρ := ha.trans_le haρ
  obtain ⟨hmap, -⟩ := map_cInc hh ha hρ w 0
  set v := incCov w a 0 ρ w a 0 ρ with hv_def
  have hV := incCov_far_le w ha haρ hR hw
  have hmeas := measurable_cInc hh a w ρ 0
  have hlaw : HasLaw (cInc h a w ρ 0) (gaussianReal 0 v.toNNReal) P :=
    ⟨hmeas.aemeasurable, hmap⟩
  by_cases hv : 0 < v
  · have hv' : (0 : ℝ) < (v.toNNReal : ℝ) := by simpa using hv
    have := DDDF.tail_abs_of_hasLaw hv' hlaw hy.le
    rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
    refine ENNReal.ofReal_le_ofReal (this.trans ?_)
    rw [Real.coe_toNNReal _ hv.le]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg y) (by positivity) (by linarith)
  · have h0 : v.toNNReal = 0 := Real.toNNReal_eq_zero.2 (not_lt.1 hv)
    rw [h0, gaussianReal_zero_var] at hmap
    have hm : MeasurableSet {x : ℝ | y ≤ |x|} := measurableSet_le measurable_const continuous_abs.measurable
    have : P {ω | y ≤ |cInc h a w ρ 0 ω|} = 0 := by
      rw [show {ω | y ≤ |cInc h a w ρ 0 ω|} = cInc h a w ρ 0 ⁻¹' {x : ℝ | y ≤ |x|} from rfl,
        ← Measure.map_apply hmeas hm, hmap, Measure.dirac_apply' _ hm]
      simp [hy.not_ge]
    rw [this]; exact bot_le

end L34
end LQGMetric.DFGPS
