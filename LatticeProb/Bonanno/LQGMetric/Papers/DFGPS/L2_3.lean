/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_3Tail
import Mathlib.Analysis.PSeries

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.3 (`lem-gff-tail`): growth of the circle averages at large radii

Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380, `lqg-metric-estimates-final.tex`
T:751–781: for a whole-plane GFF `h`, `R > 0`, `ζ > 0`, a.s.
`lim_{r → ∞} sup_{z ∈ B_R(0)} |h_r(z)| / (log r)^{1/2+ζ} = 0` (`lem2_3`), for the jointly
continuous version `H` of the circle-average process (DS Prop. 3.1, `IsCircleAvgVersion`).

Proof (T:757–781): the Gaussian tails of `L2_3Tail` (`blk_tail`, `pt_tail`) at the levels
`M + √(4σ² log(k+1))` and `√(4(k+1) log(k+1))` are `≤ 2/(k+1)²`; Borel–Cantelli gives a.s.,
for all large `k`, `|H(r, z) − H(2^k, 0)| ≤ M + O(√log k)` on `[2^{k−1}, 2^k] × B̄_R` and
`|H(2^k, 0) − H(1, 0)| ≤ √(4(k+1) log(k+1))` (the paper uses the law of `t ↦ h_{e^t}(0)`, a
Brownian motion, at this point; we use its Gaussian marginals at `t = k log 2` plus Borel–Cantelli,
and the block suprema cover the `r`-oscillation; DEV-DFGPS-B2a). Since
`√(k log k) = o(k^{1/2+ζ})` and `k ≍ log r`, the ratio tends to `0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace LQGMetric.DFGPS

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}

/-- Borel–Cantelli with summable bounds `2/(k+1)²`. -/
lemma ae_eventually_of_le_inv_sq [IsProbabilityMeasure P] {E : ℕ → Set Ω}
    (hE : ∀ k : ℕ, P.real (E k) ≤ 2 * (((k : ℝ) + 1) ^ 2)⁻¹) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∉ E k := by
  apply ae_eventually_notMem
  have hs : Summable fun k : ℕ => 2 * (((k : ℝ) + 1) ^ 2)⁻¹ := by
    have := (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)
    simpa using this.mul_left 2
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (∑' k : ℕ, 2 * (((k : ℝ) + 1) ^ 2)⁻¹))
    ENNReal.ofReal_ne_top ?_
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs]
  refine ENNReal.tsum_le_tsum fun k => ?_
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (hE k)

lemma exp_tail_eq {a : ℝ} (ha : 0 < a) (k : ℕ) :
    2 * Real.exp (-Real.sqrt (4 * a * Real.log ((k : ℝ) + 1)) ^ 2 / (2 * Real.sqrt a ^ 2)) =
      2 * (((k : ℝ) + 1) ^ 2)⁻¹ := by
  have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [k.cast_nonneg (α := ℝ)]
  have hl : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg hk
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt ha.le]
  have e : -(4 * a * Real.log ((k : ℝ) + 1)) / (2 * a) = -Real.log (((k : ℝ) + 1) ^ 2) := by
    rw [Real.log_pow]; field_simp; push_cast; ring
  rw [e, Real.exp_neg, Real.exp_log (by positivity)]

/-- the level for the block suprema -/
def blkLev (R : NNReal) (k : ℕ) : ℝ := blkM R + Real.sqrt (4 * (2 + 4 * R) * Real.log (k + 1))
/-- the level for the centre -/
def ptLev (k : ℕ) : ℝ := Real.sqrt (4 * ((k : ℝ) + 1) * Real.log (k + 1))

/-- **Borel–Cantelli step** (T:769–772): a.s., for all large `k`, the block field is
`≤ blkLev R k` and the centre increment is `≤ ptLev k`. -/
theorem ae_eventually_blk (hh : IsWholePlaneGFF h P) (hH : IsCircleAvgVersion h P H)
    (R : NNReal) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, (∀ t : BlkIdx R, |blk H k t ω| ≤ blkLev R k) ∧
      |H (2 ^ k) 0 ω - H 1 0 ω| ≤ ptLev k := by
  have := hh.gaussian.isProbabilityMeasure
  have h1 := ae_eventually_of_le_inv_sq (P := P)
    (E := fun k => {ω | blkLev R k ≤ ⨆ t : BlkIdx R, |blk H k t ω|}) fun k => by
      have := blk_tail R k hh hH (u := Real.sqrt (4 * (2 + 4 * R) * Real.log (k + 1)))
        (Real.sqrt_nonneg _)
      rw [exp_tail_eq (by positivity)] at this
      exact this
  have h2 := ae_eventually_of_le_inv_sq (P := P)
    (E := fun k => {ω | ptLev k ≤ |H (2 ^ k) 0 ω - H 1 0 ω|}) fun k => by
      have := pt_tail k hh hH (u := ptLev k) (Real.sqrt_nonneg _)
      rw [ptLev, exp_tail_eq (by positivity)] at this
      exact this
  filter_upwards [h1, h2] with ω e1 e2
  filter_upwards [e1, e2] with k k1 k2
  simp only [not_le] at k1 k2
  refine ⟨fun t => ?_, k2.le⟩
  have hb := SupTail.bddAbove_range_of_continuous (X := fun (t : BlkIdx R) ω => |blk H k t ω|)
    (fun ω => (blk_cont R k hH ω).abs) ω
  exact (le_ciSup hb t).trans k1.le

/-! ## The deterministic asymptotics -/

lemma sqrt_mul_le' {c X m : ℝ} (hX : 0 ≤ X) (hm : 0 ≤ m) (hc : c ≤ m ^ 2) :
    Real.sqrt (c * X) ≤ m * Real.sqrt X := by
  rw [show m * Real.sqrt X = Real.sqrt (m ^ 2 * X) by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hm]]
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hc hX)

lemma tendsto_aux (A B : ℝ) {ζ : ℝ} (hζ : 0 < ζ) :
    Tendsto (fun L : ℝ => (A + B * Real.sqrt (L * Real.log (6 * L))) / L ^ (1 / 2 + ζ)) atTop
      (𝓝 0) := by
  have h2ζ : 0 < 2 * ζ := by linarith
  have hlog : Tendsto (fun L : ℝ => Real.log (6 * L) / L ^ (2 * ζ)) atTop (𝓝 0) := by
    have a := (isLittleO_log_rpow_atTop h2ζ).tendsto_div_nhds_zero
    have b := (tendsto_const_nhds (x := Real.log 6)).div_atTop (tendsto_rpow_atTop h2ζ)
    have := b.add a
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with L hL
    rw [Real.log_mul (by norm_num) hL.ne', add_div]
  have hsq := ((Real.continuous_sqrt.tendsto 0).comp hlog).const_mul B
  rw [Real.sqrt_zero, mul_zero] at hsq
  have hA := (tendsto_const_nhds (x := A)).div_atTop (tendsto_rpow_atTop (by linarith : 0 < 1 / 2 + ζ))
  have := hA.add hsq
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with L hL
  simp only [Function.comp]
  have hp : L ^ (1 / 2 + ζ) = Real.sqrt (L * L ^ (2 * ζ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hL.le (by linarith), ← Real.rpow_mul hL.le]
    ring_nf
  rw [add_div, hp, mul_div_assoc, ← Real.sqrt_div' _ (by positivity),
    mul_div_mul_left _ _ hL.ne']

/-- **DFGPS Lemma 2.3** (`lem-gff-tail`, T:751–756). Let `h` be a whole-plane GFF (any additive
constant) and `H` a jointly continuous version of its circle-average process. For each `R` and
`ζ > 0`, a.s. `sup_{z ∈ B_R(0)} |h_r(z)| / (log r)^{1/2+ζ} → 0` as `r → ∞`. -/
theorem lem2_3 (hh : IsWholePlaneGFF h P) (hH : IsCircleAvgVersion h P H) (R : ℝ) {ζ : ℝ}
    (hζ : 0 < ζ) :
    ∀ᵐ ω ∂P, Tendsto (fun r : ℝ => (⨆ z : ball (0 : ℂ) R, |H r z ω|) / Real.log r ^ (1 / 2 + ζ))
      atTop (𝓝 0) := by
  set R' : NNReal := R.toNNReal
  filter_upwards [ae_eventually_blk hh hH R'] with ω hω
  obtain ⟨K, hK⟩ := eventually_atTop.1 hω
  set σ2 : ℝ := 4 * (2 + 4 * R')
  set A : ℝ := blkM R' + |H 1 0 ω|
  set B : ℝ := 2 * Real.sqrt σ2 + 5
  have hT := (tendsto_aux A B hζ).comp Real.tendsto_log_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with r hr
    exact div_nonneg (Real.iSup_nonneg fun _ => abs_nonneg _)
      (Real.rpow_nonneg (Real.log_nonneg hr.le) _)
  filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ (K + 2)), eventually_gt_atTop 1] with r hr hr1
  have hL0 : 0 < Real.log r := Real.log_pos hr1
  simp only [Function.comp]
  refine div_le_div_of_nonneg_right ?_ (Real.rpow_nonneg hL0.le _)
  have hM0 : 0 ≤ blkM R' := by unfold blkM; positivity
  refine Real.iSup_le (fun z => ?_) (by positivity)
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hr1.le (by norm_num : (1 : ℝ) < 2)
  set k := n + 1
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hkK : K ≤ k := by
    by_contra hc
    have : (2 : ℝ) ^ k ≤ 2 ^ (K + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  obtain ⟨hb, hp⟩ := hK k hkK
  have hz : ‖(z : ℂ)‖ ≤ R' := by
    have := z.2; rw [mem_ball, dist_zero_right] at this
    exact this.le.trans (Real.le_coe_toNNReal R)
  have hmem : (r / 2 ^ k, (z : ℂ)) ∈ Icc (1 / 2 : ℝ) 1 ×ˢ closedBall (0 : ℂ) R' := by
    refine ⟨⟨?_, ?_⟩, by simpa using hz⟩
    · rw [le_div_iff₀ h2k, pow_succ]; linarith
    · rw [div_le_one h2k]; exact hn2.le
  have hbt := hb ⟨_, hmem⟩
  simp only [blk, mul_div_cancel₀ _ h2k.ne'] at hbt
  -- the bound in terms of `k`
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(k : ℕ).cast_nonneg (α := ℝ)]
  -- `k + 1 ≤ 3 log r`
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hnL : (n : ℝ) * Real.log 2 ≤ Real.log r := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hn1
  have hL1 : Real.log 2 ≤ Real.log r := by
    have : (2 : ℝ) ≤ r := le_trans (by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (K + 2) := pow_le_pow_right₀ (by norm_num) (by omega)) hr
    exact Real.log_le_log (by norm_num) this
  have hkL : (k : ℝ) + 1 ≤ 6 * Real.log r := by
    have : (n : ℝ) ≤ 2 * Real.log r := by nlinarith [(n : ℕ).cast_nonneg (α := ℝ)]
    push_cast [k]; linarith
  have hL : (1 / 2 : ℝ) ≤ Real.log r := hlog2.trans hL1
  set X : ℝ := Real.log r * Real.log (6 * Real.log r)
  have hl6 : 0 ≤ Real.log (6 * Real.log r) := Real.log_nonneg (by linarith)
  have hX : 0 ≤ X := mul_nonneg hL0.le hl6
  have hlk0 : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg hk1
  have hlk : Real.log ((k : ℝ) + 1) ≤ Real.log (6 * Real.log r) :=
    Real.log_le_log (by linarith) hkL
  have hlkX : Real.log ((k : ℝ) + 1) ≤ 2 * X := by
    have : Real.log (6 * Real.log r) ≤ 2 * X := by
      simp only [X]; nlinarith
    linarith
  have hσ : 0 ≤ σ2 := by positivity
  have e1 : Real.sqrt (4 * (2 + 4 * R') * Real.log (k + 1)) ≤ 2 * Real.sqrt σ2 * Real.sqrt X := by
    refine le_trans (Real.sqrt_le_sqrt (?_ : _ ≤ (2 * σ2) * X)) (sqrt_mul_le' hX
      (by positivity) ?_)
    · push_cast; simp only [σ2] at *; nlinarith
    · rw [mul_pow, Real.sq_sqrt hσ]; nlinarith
  have e2 : ptLev k ≤ 5 * Real.sqrt X := by
    refine le_trans (Real.sqrt_le_sqrt (?_ : _ ≤ 24 * X)) (sqrt_mul_le' hX (by norm_num)
      (by norm_num))
    push_cast
    have : ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1) ≤ (6 * Real.log r) * Real.log (6 * Real.log r) :=
      mul_le_mul hkL hlk hlk0 (by linarith)
    simp only [X]; nlinarith
  have htri : |H r z ω| ≤ |H r z ω - H (2 ^ k) 0 ω| + |H (2 ^ k) 0 ω - H 1 0 ω| + |H 1 0 ω| := by
    have := abs_add_three (H r z ω - H (2 ^ k) 0 ω) (H (2 ^ k) 0 ω - H 1 0 ω) (H 1 0 ω)
    simpa using this
  simp only [blkLev] at hbt
  simp only [A, B]
  nlinarith [Real.sqrt_nonneg X]

end LQGMetric.DFGPS
