/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_11 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Fix `R > 0`, `q > 2`. For `C > 1` and `𝕣 > 0`, with probability `1 − C^{−q−√(q²−4)+o_C(1)}`
uniformly in `𝕣`, `|h_{2^{−n}𝕣}(w) − h_𝕣(0)| ≤ log(C 2^{qn})` for all `n ∈ ℕ₀` and
`w ∈ B_{R𝕣}(0) ∩ 2^{−n−1}𝕣ℤ²` (`lem3_11`).

Proof (DFGPS T:1797–1840): for each `n`, the Gaussian tail of `h_{2^{−n}𝕣}(w) − h_𝕣(0)`
(variance `≤ n log 2 + 2 log(R+1)`, `L34.tail_far_part`, i.e. L3.4 with `ν = 0`) and a union bound
over the `≤ (4R+1)² 4ⁿ` grid points give
`P[(E^n)^c] ≤ 2(4R+1)² exp(2t − (log C + qt)²/(2(t+c)))`, `t = n log 2`. DFGPS then maximize
`2α − (qα+1)²/(2α)` over `α = t/log C` (maximum `−(q+√(q²−4))`) on a partition of
`α ∈ [ζ, 1/ζ]` plus the two end ranges. We do the same optimization in closed form, for each
`n` separately: completing the square (`(ℓ' − σu)² ≥ 0`, the AM–GM step behind DFGPS's
maximization) gives `2t − (ℓ+qt)²/(2(t+c)) ≤ −(q+σ)ℓ + (q+σ)qc − δt` with
`σ² = q² − 4 − 2δ` (`l311_exponent`), and the factor `2^{−δn}` makes the sum over `n` converge
(`l311_sum`). DEVIATIONS DFA0-3 (bookkeeping of the optimization over `α`, same estimate).
The `o_C(1)` is formalized as: for every `ζ > 0` there is `C₀` with the bound `C^{−q−√(q²−4)+ζ}`
for all `C > C₀` and all `𝕣 > 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace LQGMetric.DFGPS
namespace L311

open CircleAvg L34

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- the event `E^n_𝕣` fails (T:1790) -/
def badLevel (h : Ω → DistC) (R q C 𝕣 : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∃ w ∈ Metric.ball (0 : ℂ) (R * 𝕣) ∩ Blueprint.gridPts (((2 : ℝ) ^ (n + 1))⁻¹ * 𝕣),
    Real.log (C * (2 : ℝ) ^ (q * n)) <
      |circleAvg (h ω) (((2 : ℝ) ^ n)⁻¹ * 𝕣) w - circleAvg (h ω) 𝕣 0|}

/-- the bound at level `n`: Gaussian tail and union bound -/
theorem l311_level [IsProbabilityMeasure P] (hh : IsWholePlaneGFF h P) {R q C 𝕣 : ℝ}
    (hR : 0 < R) (hq : 0 < q) (hC : 1 < C) (h𝕣 : 0 < 𝕣) (n : ℕ) :
    P (badLevel h R q C 𝕣 n) ≤ ENNReal.ofReal ((4 * R + 1) ^ 2 * (4 : ℝ) ^ n *
      (2 * Real.exp (-(Real.log C + q * (n * Real.log 2)) ^ 2 /
        (2 * (n * Real.log 2 + 2 * Real.log (R + 1)))))) := by
  classical
  set m := ((2 : ℝ) ^ (n + 1))⁻¹ * 𝕣 with hm_def
  have hm : 0 < m := by positivity
  set a := ((2 : ℝ) ^ n)⁻¹ * 𝕣 with ha_def
  have ha : 0 < a := by positivity
  have ha𝕣 : a ≤ 𝕣 := by
    rw [ha_def]
    exact mul_le_of_le_one_left h𝕣.le (inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two))
  set y := Real.log C + q * (n * Real.log 2) with hy_def
  have hy : 0 < y := by
    have : 0 ≤ q * (n * Real.log 2) := by positivity
    have := Real.log_pos hC
    linarith
  have hlogC : Real.log (C * (2 : ℝ) ^ (q * n)) = y := by
    rw [Real.log_mul (by linarith) (by positivity), Real.log_rpow two_pos]; ring
  have hlog : Real.log (𝕣 / a) = n * Real.log 2 := by
    rw [show 𝕣 / a = (2 : ℝ) ^ n by rw [ha_def]; field_simp, Real.log_pow]
  set G := (LQGDimension.LFPPRecords.gridBox m 0 (R * 𝕣)).filter
    fun b => ‖LQGDimension.LFPPRecords.gridPt m b‖ ≤ R * 𝕣
  have hsub : badLevel h R q C 𝕣 n ⊆
      ⋃ b ∈ G, {ω | y ≤ |cInc h a (LQGDimension.LFPPRecords.gridPt m b) 𝕣 0 ω|} := by
    rintro ω ⟨w, ⟨hwb, i, j, rfl⟩, hω⟩
    have hpt : LQGDimension.LFPPRecords.gridPt m (i, j) = ⟨i * m, j * m⟩ := rfl
    have hn : ‖LQGDimension.LFPPRecords.gridPt m (i, j)‖ ≤ R * 𝕣 := by
      rw [hpt]; exact (mem_ball_zero_iff.1 hwb).le
    refine Set.mem_biUnion (x := (i, j)) ?_ ?_
    · refine Finset.mem_filter.2 ⟨LQGDimension.LFPPRecords.mem_gridBox hm ?_, hn⟩
      rwa [sub_zero]
    · rw [hpt]
      rw [hlogC] at hω
      exact hω.le
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hterm : ∀ b ∈ G, P {ω | y ≤ |cInc h a (LQGDimension.LFPPRecords.gridPt m b) 𝕣 0 ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-y ^ 2 /
        (2 * (n * Real.log 2 + 2 * Real.log (R + 1))))) := fun b hb => by
    have := tail_far_part hh ha ha𝕣 hR.le (Finset.mem_filter.1 hb).2 hy
    rwa [hlog] at this
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
  refine (Nat.cast_le.2 (Finset.card_filter_le _ _)).trans
    ((LQGDimension.LFPPRecords.card_gridBox_le hm (by positivity) 0).trans ?_)
  have h8 : 2 * (R * 𝕣) / m = 4 * R * (2 : ℝ) ^ n := by
    rw [hm_def, pow_succ]; field_simp; ring
  rw [h8, show (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
    ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  nlinarith

/-- completing the square (the maximization over `α` in DFGPS T:1836) -/
lemma l311_exponent {ℓ t c q σ δ : ℝ} (ht : 0 ≤ t) (hc : 0 < c) (hδ : 0 ≤ δ)
    (hσ : σ ^ 2 = q ^ 2 - 4 - 2 * δ) :
    2 * t - (ℓ + q * t) ^ 2 / (2 * (t + c)) ≤ -(q + σ) * ℓ + (q + σ) * q * c - δ * t := by
  have hu : 0 < 2 * (t + c) := by positivity
  have key : 0 ≤ (ℓ + q * t) ^ 2 - 2 * (t + c) * (2 * t + (q + σ) * ℓ - (q + σ) * q * c + δ * t) :=
    by
    have e : (ℓ + q * t) ^ 2 - 2 * (t + c) * (2 * t + (q + σ) * ℓ - (q + σ) * q * c + δ * t) =
        (ℓ - q * c - σ * (t + c)) ^ 2 + (q ^ 2 - 4 - 2 * δ - σ ^ 2) * (t + c) ^ 2 +
          2 * (2 + δ) * (t + c) * c := by ring
    have h0 : q ^ 2 - 4 - 2 * δ - σ ^ 2 = 0 := by linarith
    rw [e, h0, zero_mul, add_zero]
    positivity
  have : (2 * t + (q + σ) * ℓ - (q + σ) * q * c + δ * t) ≤ (ℓ + q * t) ^ 2 / (2 * (t + c)) := by
    rw [le_div_iff₀ hu]; nlinarith
  linarith

/-- the level bound in the form `M rⁿ` with `r = 2^{−δ}` (T:1797–1830) -/
theorem l311_level_geom [IsProbabilityMeasure P] (hh : IsWholePlaneGFF h P) {R q C 𝕣 σ δ : ℝ}
    (hR : 0 < R) (hq : 0 < q) (hC : 1 < C) (h𝕣 : 0 < 𝕣) (hδ : 0 ≤ δ)
    (hσ : σ ^ 2 = q ^ 2 - 4 - 2 * δ) (n : ℕ) :
    P (badLevel h R q C 𝕣 n) ≤ ENNReal.ofReal (2 * (4 * R + 1) ^ 2 *
      Real.exp ((q + σ) * q * (2 * Real.log (R + 1))) * C ^ (-(q + σ)) *
        Real.exp (-δ * Real.log 2) ^ n) := by
  refine (l311_level hh hR hq hC h𝕣 n).trans (ENNReal.ofReal_le_ofReal ?_)
  set t : ℝ := n * Real.log 2
  set c := 2 * Real.log (R + 1)
  have hc : 0 < c := mul_pos two_pos (Real.log_pos (by linarith))
  have ht : 0 ≤ t := by positivity
  have h4 : Real.exp (2 * t) = (4 : ℝ) ^ n := by
    rw [show 2 * t = n * ((2 : ℕ) * Real.log 2) by simp only [t]; push_cast; ring,
      Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log two_pos]; norm_num
  have hr : Real.exp (-δ * Real.log 2) ^ n = Real.exp (-δ * t) := by
    rw [← Real.exp_nat_mul]; congr 1; simp only [t]; ring
  have hCp : C ^ (-(q + σ)) = Real.exp (-(q + σ) * Real.log C) := by
    rw [Real.rpow_def_of_pos (by linarith)]; ring_nf
  have hexp := l311_exponent (ℓ := Real.log C) ht hc hδ hσ
  rw [hr, hCp, ← h4]
  calc (4 * R + 1) ^ 2 * Real.exp (2 * t) *
        (2 * Real.exp (-(Real.log C + q * t) ^ 2 / (2 * (t + c))))
      = 2 * (4 * R + 1) ^ 2 * Real.exp (2 * t - (Real.log C + q * t) ^ 2 / (2 * (t + c))) := by
        rw [sub_eq_add_neg, Real.exp_add, neg_div]; ring
    _ ≤ 2 * (4 * R + 1) ^ 2 *
        Real.exp (-(q + σ) * Real.log C + (q + σ) * q * c - δ * t) := by
        gcongr
    _ = _ := by
        rw [show -(q + σ) * Real.log C + (q + σ) * q * c - δ * t =
          (q + σ) * q * c + -(q + σ) * Real.log C + -δ * t by ring, Real.exp_add, Real.exp_add]
        ring

end L311

open L311 in
/-- **DFGPS Lemma 3.11** (`lem-circle-avg-all`, T:1783–1789): for `R > 0`, `q > 2`, every
`ζ > 0` there is `C₀` such that for all `C > C₀` and `𝕣 > 0`, with probability at least
`1 − C^{−q−√(q²−4)+ζ}`, `|h_{2^{−n}𝕣}(w) − h_𝕣(0)| ≤ log(C 2^{qn})` for all `n ∈ ℕ₀` and
`w ∈ B_{R𝕣}(0) ∩ 2^{−n−1}𝕣ℤ²`. -/
theorem lem3_11 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {R q : ℝ} (hR : 0 < R) (hq : 2 < q) :
    ∀ ζ : ℝ, 0 < ζ → ∃ C₀ : ℝ, ∀ C : ℝ, C₀ < C → ∀ 𝕣 : ℝ, 0 < 𝕣 →
      P {ω | ∃ n : ℕ, ∃ w ∈ Metric.ball (0 : ℂ) (R * 𝕣) ∩
          Blueprint.gridPts (((2 : ℝ) ^ (n + 1))⁻¹ * 𝕣),
          Real.log (C * (2 : ℝ) ^ (q * n)) <
            |circleAvg (h ω) (((2 : ℝ) ^ n)⁻¹ * 𝕣) w - circleAvg (h ω) 𝕣 0|} ≤
        ENNReal.ofReal (C ^ (-(q + Real.sqrt (q ^ 2 - 4)) + ζ)) := by
  intro ζ hζ
  set s0 := Real.sqrt (q ^ 2 - 4) with hs0_def
  have hq4 : 0 < q ^ 2 - 4 := by nlinarith
  have hs0 : 0 < s0 := Real.sqrt_pos.2 hq4
  have hs0sq : s0 ^ 2 = q ^ 2 - 4 := Real.sq_sqrt hq4.le
  set z := min (ζ / 2) s0 with hz_def
  have hz0 : 0 < z := lt_min (by linarith) hs0
  have hzζ : z ≤ ζ / 2 := min_le_left _ _
  have hzs : z ≤ s0 := min_le_right _ _
  set σ := s0 - z with hσ_def
  set δ := z * (2 * s0 - z) / 2 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; have : 0 < 2 * s0 - z := by linarith
                        positivity
  have hσsq : σ ^ 2 = q ^ 2 - 4 - 2 * δ := by rw [hσ_def, hδ_def]; nlinarith
  have hσ0 : 0 ≤ σ := by rw [hσ_def]; linarith
  set r := Real.exp (-δ * Real.log 2) with hr_def
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by
    have := Real.log_pos one_lt_two
    nlinarith)
  set A := 2 * (4 * R + 1) ^ 2 * Real.exp ((q + σ) * q * (2 * Real.log (R + 1))) / (1 - r)
    with hA_def
  have hA : 0 < A := by
    rw [hA_def]; have : 0 < 1 - r := by linarith
    positivity
  refine ⟨max 1 (A ^ (2 / ζ)), fun C hC 𝕣 h𝕣 => ?_⟩
  have hC1 : 1 < C := lt_of_le_of_lt (le_max_left _ _) hC
  have hCA : A ^ (2 / ζ) < C := lt_of_le_of_lt (le_max_right _ _) hC
  have hsub : {ω | ∃ n : ℕ, ∃ w ∈ Metric.ball (0 : ℂ) (R * 𝕣) ∩
      Blueprint.gridPts (((2 : ℝ) ^ (n + 1))⁻¹ * 𝕣),
      Real.log (C * (2 : ℝ) ^ (q * n)) <
        |circleAvg (h ω) (((2 : ℝ) ^ n)⁻¹ * 𝕣) w - circleAvg (h ω) 𝕣 0|} =
      ⋃ n : ℕ, badLevel h R q C 𝕣 n := by
    ext ω; simp only [mem_iUnion, badLevel, mem_ofPred_eq]
  set M := 2 * (4 * R + 1) ^ 2 * Real.exp ((q + σ) * q * (2 * Real.log (R + 1))) *
    C ^ (-(q + σ)) with hM_def
  have hM : 0 ≤ M := by rw [hM_def]; have := Real.rpow_pos_of_pos (by linarith : 0 < C) (-(q + σ))
                        positivity
  have hsum : Summable fun n : ℕ => M * r ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left M
  rw [hsub]
  calc P (⋃ n : ℕ, badLevel h R q C 𝕣 n) ≤ ∑' n, P (badLevel h R q C 𝕣 n) :=
        measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (M * r ^ n) := ENNReal.tsum_le_tsum fun n =>
        l311_level_geom hh hR (by linarith) hC1 h𝕣 hδ.le hσsq n
    _ = ENNReal.ofReal (∑' n : ℕ, M * r ^ n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum).symm
    _ ≤ ENNReal.ofReal (C ^ (-(q + s0) + ζ)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
        have hAC : A ≤ C ^ (ζ / 2) := by
          have e : A = (A ^ (2 / ζ)) ^ (ζ / 2) := by
            rw [← Real.rpow_mul hA.le, show 2 / ζ * (ζ / 2) = 1 by field_simp, Real.rpow_one]
          rw [e]
          exact Real.rpow_le_rpow (by positivity) hCA.le (by positivity)
        have hMA : M * (1 - r)⁻¹ = A * C ^ (-(q + σ)) := by
          rw [hM_def, hA_def]; ring
        rw [hMA]
        calc A * C ^ (-(q + σ)) ≤ C ^ (ζ / 2) * C ^ (-(q + σ)) :=
              mul_le_mul_of_nonneg_right hAC (by positivity)
          _ = C ^ (ζ / 2 + -(q + σ)) := (Real.rpow_add (by linarith) _ _).symm
          _ ≤ C ^ (-(q + s0) + ζ) := Real.rpow_le_rpow_of_exponent_le hC1.le (by
              rw [hσ_def]; linarith)
end LQGMetric.DFGPS
