/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_4 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_4Tail
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordsAux1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
For `ν ≥ 0`, `q > 0`, `R > 0` there is `C` such that for all `𝕣 > 0`, `ε ∈ (0,1)` and every
countable set `S ⊆ [ε^{1+ν}𝕣, ε𝕣]` of radii,
`P[∃ w ∈ B_{R𝕣}(0) ∩ (ε^{1+ν}𝕣/4)ℤ², r ∈ S : |h_r(w) − h_𝕣(0)| > q log ε⁻¹]
  ≤ C ε^{q²/(2(1+√ν)²) − 2 − 2ν}` (`lem3_4`).

Proof as in DFGPS T:1495–1507: with `s = q√ν/(1+√ν)`, split
`|h_r(w) − h_𝕣(0)| ≤ |h_r(w) − h_{ε𝕣}(w)| + |h_{ε𝕣}(w) − h_𝕣(0)|`, bound the first by the
Brownian maximal tail (3.6) (`tail_bm_part`) and the second by the Gaussian tail (3.7)
(`tail_far_part`); both give `ε^{q²/(2(1+√ν)²)}` up to constants (3.8), then a union bound over
the `≤ (8R+1)² ε^{−2−2ν}` grid points (LQGDimension `card_gridBox_le`).

Differences from the paper (DEVIATIONS DFA0-1, DFA0-2): radii in a countable `S` (see
`L3_4Tail`); the bound holds for all `ε ∈ (0,1)` with an explicit constant (the paper's
`O_ε(·)`); `ν = 0` is allowed (DFGPS applies the lemma with `ν = 0` in L3.11, T:1803, 1818);
`q > 0` replaces `q > 2 + 2ν` (only needed for the exponent to be positive); `h` is any
whole-plane GFF (the normalization `h_1(0) = 0` is not used).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace LQGMetric.DFGPS
namespace L34

open CircleAvg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- the exponent `q²/(2(1+√ν)²)` of DFGPS (3.8) -/
def kap (ν q : ℝ) : ℝ := q ^ 2 / (2 * (1 + Real.sqrt ν) ^ 2)

/-- (3.8): the bound at a single grid point `w`. -/
theorem tail_point [IsProbabilityMeasure P] (hh : IsWholePlaneGFF h P) {ν q R : ℝ}
    (hν : 0 ≤ ν) (hq : 0 < q) (hR : 0 ≤ R) {𝕣 ε : ℝ} (h𝕣 : 0 < 𝕣) (hε : ε ∈ Ioo (0 : ℝ) 1)
    {S : Set ℝ} (hS : S.Countable) (hSI : S ⊆ Icc (ε ^ (1 + ν) * 𝕣) (ε * 𝕣)) {w : ℂ}
    (hw : ‖w‖ ≤ R * 𝕣) :
    P {ω | ∃ r ∈ S, q * Real.log ε⁻¹ < |circleAvg (h ω) r w - circleAvg (h ω) 𝕣 0|} ≤
      ENNReal.ofReal ((2 + 2 * Real.exp (kap ν q * (2 * Real.log (R + 1)))) *
        ε ^ kap ν q) := by
  obtain ⟨hε0, hε1⟩ := hε
  set L := Real.log ε⁻¹ with hL_def
  have hL : 0 < L := Real.log_pos (one_lt_inv_iff₀.2 ⟨hε0, hε1⟩)
  set c := 2 * Real.log (R + 1) with hc_def
  have hc : 0 ≤ c := mul_nonneg zero_le_two (Real.log_nonneg (by linarith))
  set κ := kap ν q with hκ_def
  have hsq : 0 ≤ Real.sqrt ν := Real.sqrt_nonneg ν
  have h1s : 0 < 1 + Real.sqrt ν := by linarith
  set s := q * Real.sqrt ν / (1 + Real.sqrt ν) with hs_def
  have hs0 : 0 ≤ s := by positivity
  have hqs : q - s = q / (1 + Real.sqrt ν) := by
    rw [hs_def]; field_simp; ring
  have hqs0 : 0 < q - s := by rw [hqs]; positivity
  have hκ0 : 0 ≤ κ := by rw [hκ_def, kap]; positivity
  have hκq : (q - s) ^ 2 = 2 * κ := by
    rw [hqs, hκ_def, kap]; field_simp
  have hεκ : ε ^ κ = Real.exp (-(κ * L)) := by
    rw [Real.rpow_def_of_pos hε0, hL_def, Real.log_inv]; ring_nf
  set ρ := ε * 𝕣
  have hρ : 0 < ρ := mul_pos hε0 h𝕣
  -- the splitting of the event (T:1505)
  have hsplit : {ω | ∃ r ∈ S, q * L < |circleAvg (h ω) r w - circleAvg (h ω) 𝕣 0|} ⊆
      {ω | ∃ r ∈ S, s * L < |cInc h r w ρ w ω|} ∪ {ω | (q - s) * L ≤ |cInc h ρ w 𝕣 0 ω|} := by
    rintro ω ⟨r, hr, hlt⟩
    by_cases hA : s * L < |cInc h r w ρ w ω|
    · exact Or.inl ⟨r, hr, hA⟩
    · refine Or.inr ?_
      simp only [mem_ofPred_eq, cInc] at hA ⊢
      have := abs_sub_le (circleAvg (h ω) r w) (circleAvg (h ω) ρ w) (circleAvg (h ω) 𝕣 0)
      nlinarith
  -- the Brownian part (3.6)
  have hA : P {ω | ∃ r ∈ S, s * L < |cInc h r w ρ w ω|} ≤ ENNReal.ofReal (2 * ε ^ κ) := by
    rcases hν.eq_or_lt with hν0 | hνpos
    · subst hν0
      have hempty : {ω | ∃ r ∈ S, s * L < |cInc h r w ρ w ω|} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 fun ω ⟨r, hr, hlt⟩ => ?_
        have hrI := hSI hr
        rw [add_zero, Real.rpow_one] at hrI
        have hrρ : r = ρ := le_antisymm hrI.2 hrI.1
        rw [hrρ] at hlt
        simp [cInc, hs_def] at hlt
      rw [hempty, measure_empty]; exact bot_le
    · have hεν : ε ^ ν < 1 := Real.rpow_lt_one hε0.le hε1 hνpos
      have hενpos : 0 < ε ^ ν := Real.rpow_pos_of_pos hε0 ν
      have hρ₀ : ε ^ (1 + ν) * 𝕣 = ε ^ ν * ρ := by
        rw [Real.rpow_add hε0, Real.rpow_one]; ring
      have hρ₀pos : 0 < ε ^ (1 + ν) * 𝕣 := by rw [hρ₀]; positivity
      have hρ₀ρ : ε ^ (1 + ν) * 𝕣 < ρ := by rw [hρ₀]; nlinarith
      have hb : 0 < s * L := by
        have : 0 < Real.sqrt ν := Real.sqrt_pos.2 hνpos
        rw [hs_def]; positivity
      refine (tail_bm_part hh w hρ₀pos hρ₀ρ hS hSI hb).trans (ENNReal.ofReal_le_ofReal ?_)
      have hlog : Real.log (ρ / (ε ^ (1 + ν) * 𝕣)) = ν * L := by
        rw [hρ₀, div_mul_cancel_right₀ hρ.ne', Real.log_inv, Real.log_rpow hε0, hL_def,
          Real.log_inv]; ring
      rw [hlog, hεκ]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (le_of_eq ?_)) zero_le_two
      have hs2 : s ^ 2 = 2 * ν * κ := by
        rw [hs_def, hκ_def, kap]
        field_simp
        rw [Real.sq_sqrt hν]
      field_simp
      rw [hs2]
  -- the far part (3.7)
  have hB : P {ω | (q - s) * L ≤ |cInc h ρ w 𝕣 0 ω|} ≤
      ENNReal.ofReal (2 * Real.exp (κ * c) * ε ^ κ) := by
    have hρ𝕣 : ρ ≤ 𝕣 := by
      show ε * 𝕣 ≤ 𝕣; nlinarith
    refine (tail_far_part hh hρ hρ𝕣 (hR) hw (mul_pos hqs0 hL)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hlog : Real.log (𝕣 / ρ) = L := by
      rw [show 𝕣 / ρ = ε⁻¹ by show 𝕣 / (ε * 𝕣) = ε⁻¹; field_simp]
    rw [hlog, ← hc_def, hεκ, mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) zero_le_two
    have hLc : 0 < 2 * (L + c) := by positivity
    rw [div_le_iff₀ hLc, mul_pow, hκq]
    nlinarith [mul_nonneg hκ0 (sq_nonneg c)]
  calc _ ≤ _ := measure_mono hsplit
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * ε ^ κ) + ENNReal.ofReal (2 * Real.exp (κ * c) * ε ^ κ) :=
        add_le_add hA hB
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end L34

open L34 in
/-- **DFGPS Lemma 3.4** (`lem-circle-avg-tail`, T:1485–1508), for a countable set `S` of radii in
`[ε^{1+ν}𝕣, ε𝕣]`: the event that `|h_r(w) − h_𝕣(0)| > q log ε⁻¹` for some
`w ∈ B_{R𝕣}(0) ∩ (ε^{1+ν}𝕣/4)ℤ²` and `r ∈ S` has probability `≤ C ε^{q²/(2(1+√ν)²) − 2 − 2ν}`,
with `C` depending only on `ν, q, R`. -/
theorem lem3_4 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {ν q R : ℝ} (hν : 0 ≤ ν) (hq : 0 < q)
    (hR : 0 < R) :
    ∃ C : ℝ, ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ S : Set ℝ, S.Countable →
      S ⊆ Icc (ε ^ (1 + ν) * 𝕣) (ε * 𝕣) →
      P {ω | ∃ w ∈ Metric.ball (0 : ℂ) (R * 𝕣) ∩ Blueprint.gridPts (ε ^ (1 + ν) * 𝕣 / 4), ∃ r ∈ S,
          q * Real.log ε⁻¹ < |circleAvg (h ω) r w - circleAvg (h ω) 𝕣 0|} ≤
        ENNReal.ofReal (C * ε ^ (q ^ 2 / (2 * (1 + Real.sqrt ν) ^ 2) - 2 - 2 * ν)) := by
  classical
  set K := 2 + 2 * Real.exp (kap ν q * (2 * Real.log (R + 1))) with hK_def
  have hK : 0 ≤ K := by positivity
  refine ⟨(8 * R + 1) ^ 2 * K, fun 𝕣 h𝕣 ε hε S hS hSI => ?_⟩
  obtain ⟨hε0, hε1⟩ := hε
  set m := ε ^ (1 + ν) * 𝕣 / 4 with hm_def
  have hx : 0 < ε ^ (1 + ν) := Real.rpow_pos_of_pos hε0 _
  have hx1 : ε ^ (1 + ν) ≤ 1 := Real.rpow_le_one hε0.le hε1.le (by linarith)
  have hm : 0 < m := by positivity
  set E : ℂ → Set Ω := fun w =>
    {ω | ∃ r ∈ S, q * Real.log ε⁻¹ < |circleAvg (h ω) r w - circleAvg (h ω) 𝕣 0|}
  set G := (LQGDimension.LFPPRecords.gridBox m 0 (R * 𝕣)).filter
    fun a => ‖LQGDimension.LFPPRecords.gridPt m a‖ ≤ R * 𝕣
  have hsub : {ω | ∃ w ∈ Metric.ball (0 : ℂ) (R * 𝕣) ∩ Blueprint.gridPts m, ∃ r ∈ S,
      q * Real.log ε⁻¹ < |circleAvg (h ω) r w - circleAvg (h ω) 𝕣 0|} ⊆
      ⋃ a ∈ G, E (LQGDimension.LFPPRecords.gridPt m a) := by
    rintro ω ⟨w, ⟨hwb, a, b, rfl⟩, hω⟩
    have hpt : LQGDimension.LFPPRecords.gridPt m (a, b) = ⟨a * m, b * m⟩ := rfl
    have hn : ‖LQGDimension.LFPPRecords.gridPt m (a, b)‖ ≤ R * 𝕣 := by
      rw [hpt]; exact (mem_ball_zero_iff.1 hwb).le
    refine Set.mem_biUnion (x := (a, b)) ?_ ?_
    · refine Finset.mem_filter.2 ⟨LQGDimension.LFPPRecords.mem_gridBox hm ?_, hn⟩
      rwa [sub_zero]
    · rw [hpt]; exact hω
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hterm : ∀ a ∈ G, P (E (LQGDimension.LFPPRecords.gridPt m a)) ≤
      ENNReal.ofReal (K * ε ^ kap ν q) := fun a ha =>
    tail_point hh hν hq hR.le h𝕣 ⟨hε0, hε1⟩ hS hSI (Finset.mem_filter.1 ha).2
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcard : (G.card : ℝ) ≤ ((8 * R + 1) / ε ^ (1 + ν)) ^ 2 := by
    refine (Nat.cast_le.2 (Finset.card_filter_le _ _)).trans
      ((LQGDimension.LFPPRecords.card_gridBox_le hm (by positivity) 0).trans ?_)
    have h8 : 2 * (R * 𝕣) / m = 8 * R / ε ^ (1 + ν) := by
      rw [hm_def]; field_simp; ring
    rw [h8]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    rw [add_div]
    gcongr
    exact (one_le_div hx).2 hx1
  have hexp : ε ^ (q ^ 2 / (2 * (1 + Real.sqrt ν) ^ 2) - 2 - 2 * ν) =
      ε ^ kap ν q / (ε ^ (1 + ν)) ^ 2 := by
    rw [kap, show q ^ 2 / (2 * (1 + Real.sqrt ν) ^ 2) - 2 - 2 * ν =
      q ^ 2 / (2 * (1 + Real.sqrt ν) ^ 2) - (1 + ν) * 2 by ring, Real.rpow_sub hε0,
      Real.rpow_mul hε0.le, Real.rpow_two]
  rw [hexp]
  have hεk : 0 ≤ ε ^ kap ν q := (Real.rpow_pos_of_pos hε0 _).le
  calc (G.card : ℝ) * (K * ε ^ kap ν q) ≤ ((8 * R + 1) / ε ^ (1 + ν)) ^ 2 * (K * ε ^ kap ν q) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp
end LQGMetric.DFGPS
