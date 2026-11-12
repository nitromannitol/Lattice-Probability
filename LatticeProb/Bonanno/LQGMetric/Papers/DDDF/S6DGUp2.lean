/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6DGUp2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DGLow
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DGUp1
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36UpperFinal

/-!
# DDDF (5.78) from DG Proposition 3.21 (task P2-DDDFDG)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1276–1281 (`eq:DGupperQuantile`): "for each fixed
small `δ > 0`, for `k` large enough we have `λ_k ≤ 2^{−k(1−ξQ−δ)}`. The proof … follows the same
lines as the one of (5.54)", i.e. DG's LFPP upper bound (DG Prop 3.21/3.22) and the comparison of
`φ_δ` with the circle average.

Route: the upper half of DFGPS Lemma 3.6 at `𝕣 = 1` (`DFGPS.L36.lem3_6_upperOne`, proved from
`Blueprint.DGProp3_21` = DG Prop 3.21, DG:1603–1610, via the boundary layer of DFGPS T:1645):
with probability `≥ 7/8`, a graph path `π` of `(0,1)² ∩ δℤ²` from a leftmost to a rightmost
vertex has `Σ_{x∈π} e^{ξ h_δ(x)} ≤ 2δ^{−ξQ−ζ/3}`; by `rectLen_le_graph` and the comparison
`WPPhiCompare` (with `C = 2`), `L^{(K)}_{1,1}(φ) ≤ 12 δ^{1−ξQ−ζ/3} e^{(ζ/3) K log 2}
≤ 2^{−K(1−ξQ−ζ)}` (`δ = 2^{-K}`, `K` large), with probability `> 1/2`; hence the median
`λ_K ≤ 2^{−K(1−ξQ−ζ)}`. The law of `L^{(K)}_{1,1}` does not depend on the white noise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6DG

open WhiteNoise Blueprint DG DFGPS

variable {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂] {P : Measure Ω}
  {P₂ : Measure Ω₂} {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ}

/-- if `P(L > c) < 1/2` then the (lower) median `λ_K ≤ c` -/
theorem lambdaN_le_of_prob_lt (hW : IsWhiteNoise P W) {ξ : ℝ} {K : ℕ} {c : ℝ}
    (h : P {ω | c < lenObs ξ (phiMN W P 0 K) (rectAB 1 1) ω} < 2⁻¹) :
    lambdaN ξ W P K ≤ c := by
  have := hW.isProbabilityMeasure
  have hv := isPhiVersion_phiMN hW (Nat.zero_le K)
  have hm : Measurable (lenN ξ W P 1 1 K) := measurable_lenObs hv.cont hv.meas _
  by_contra hlt
  push_neg at hlt
  have hmed := (isMedian_iff.1 (isMedian_lowerMedianLaw (μ := P.map (lenN ξ W P 1 1 K)))).2
  rw [Measure.map_apply hm measurableSet_Ici] at hmed
  exact absurd (hmed.trans (measure_mono fun ω hω => lt_of_lt_of_le hlt hω)) (not_le.2 h)

/-- `P(L^{(K)}_{1,1} > c)` does not depend on the white noise -/
theorem prob_lenObs_gt_eq (hW : IsWhiteNoise P W) (hV : IsWhiteNoise P₂ V) (ξ : ℝ) (K : ℕ)
    (c : ℝ) :
    P {ω | c < lenObs ξ (phiMN W P 0 K) (rectAB 1 1) ω} =
      P₂ {ω | c < lenObs ξ (phiMN V P₂ 0 K) (rectAB 1 1) ω} :=
  measure_crossLenIn_phiVer_eq (rectAB 1 1).isCompact_toSet hW hV (by positivity)
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.zero_le K))
    (S := {x : ℝ≥0∞ | c < x.toReal}) (measurableSet_lt measurable_const ENNReal.measurable_toReal)

/-- exponent bookkeeping for the upper bound -/
lemma up_arith {ξ q ζ : ℝ} (hξ : 0 < ξ) (K : ℕ)
    (hK : 12 * Real.exp (-((K : ℝ) * Real.log 2 * (ζ / 3))) ≤ 1) :
    12 * (2 : ℝ)⁻¹ ^ K * Real.exp (ξ * (ζ / 3 * Real.log 2 / ξ * K)) *
        ((2 : ℝ)⁻¹ ^ K) ^ (-ξ * q - ζ / 3) ≤ (2 : ℝ) ^ (-((K : ℝ) * (1 - ξ * q - ζ))) := by
  have hδ : (2 : ℝ)⁻¹ ^ K = Real.exp (-((K : ℝ) * Real.log 2)) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K), Real.log_pow, Real.log_inv]
    ring_nf
  rw [hδ, ← Real.exp_mul, Real.rpow_def_of_pos two_pos]
  have e1 : ξ * (ζ / 3 * Real.log 2 / ξ * K) = (K : ℝ) * Real.log 2 * (ζ / 3) := by
    field_simp
  rw [e1]
  have e2 : 12 * Real.exp (-((K : ℝ) * Real.log 2)) * Real.exp ((K : ℝ) * Real.log 2 * (ζ / 3)) *
      Real.exp (-((K : ℝ) * Real.log 2) * (-ξ * q - ζ / 3)) =
      (12 * Real.exp (-((K : ℝ) * Real.log 2 * (ζ / 3)))) *
        Real.exp (Real.log 2 * -((K : ℝ) * (1 - ξ * q - ζ))) := by
    rw [mul_assoc 12, ← Real.exp_add, mul_assoc 12, ← Real.exp_add, mul_assoc 12, ← Real.exp_add]
    congr 2
    ring
  rw [e2]
  exact mul_le_of_le_one_left (Real.exp_pos _).le hK

/-- **DDDF (5.78) on the coupling**: for `K` large, `P(L^{(K)}_{1,1} > 2^{−K(1−ξQ−ζ)}) < 1/2`. -/
theorem prob_lenObs_gt_lt_half (hP3 : DGProp3_21) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {h : Ω → DistC}
    {hc : ℝ → ℂ → Ω → ℝ} (hW : IsWhiteNoise P W) (hh : IsNormalizedWPGFF h P)
    (hver : ∀ r : ℝ, 0 < r → ∀ z : ℂ, (fun ω => hc r z ω) =ᵐ[P] fun ω => circleAvg (h ω) r z)
    (hcmp : ∀ ζ : ℝ, 0 < ζ → Tendsto (fun K : ℕ => P {ω | ¬ ∀ z ∈ (rectAB 1 1).toSet,
      ∀ w ∈ (rectAB 1 1).toSet, ‖z - w‖ ≤ 2 * (2 : ℝ)⁻¹ ^ K →
        |hc ((2 : ℝ)⁻¹ ^ K) z ω - phiMN W P 0 K w ω| ≤ ζ * K}) atTop (𝓝 0))
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      P {ω | (2 : ℝ) ^ (-((K : ℝ) * (1 - xiGamma γ * Q γ - ζ))) <
        lenObs (xiGamma γ) (phiMN W P 0 K) (rectAB 1 1) ω} < 2⁻¹ := by
  have := hW.isProbabilityMeasure
  set ξ := xiGamma γ with hξdef
  have hξ : 0 < ξ := by
    have := DG.dGamma_pos γ
    simp only [hξdef, xiGamma]; positivity
  set ζ₂ := ζ / 3 with hζ₂
  have hζ₂0 : 0 < ζ₂ := by positivity
  set ζ₁ := ζ₂ * Real.log 2 / ξ with hζ₁
  have hζ₁0 : 0 < ζ₁ := div_pos (mul_pos hζ₂0 (Real.log_pos one_lt_two)) hξ
  obtain ⟨δ₀, hδ₀, H36⟩ := L36.lem3_6_upperOne hP3 γ hγ hγ2 P h hh ζ₂
    (show ζ₂ ∈ Ioo (0 : ℝ) 1 from ⟨hζ₂0, by linarith⟩) (1 / 8) (by norm_num)
  have hA := (tendsto_order.1 (hcmp ζ₁ hζ₁0)).2 (ENNReal.ofReal (1 / 8)) (by norm_num)
  have hδK := (tendsto_order.1 (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num))).2 δ₀ hδ₀
  have hexp : Tendsto (fun K : ℕ => 12 * Real.exp (-((K : ℝ) * Real.log 2 * (ζ₂))))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun K : ℕ => (K : ℝ) * Real.log 2 * ζ₂) atTop atTop :=
      (tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos one_lt_two)).atTop_mul_const hζ₂0
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul 12
  have hexp' := (tendsto_order.1 hexp).2 1 one_pos
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 (((hA.and hδK).and hexp').and (eventually_ge_atTop 2))
  refine ⟨K₀, fun K hK => ?_⟩
  obtain ⟨⟨⟨hAK, hδK'⟩, hexpK⟩, hK2⟩ := hK₀ K hK
  set δ : ℝ := (2 : ℝ)⁻¹ ^ K with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ4 : δ ≤ 1 / 4 := by
    rw [hδ]
    calc (2 : ℝ)⁻¹ ^ K ≤ (2 : ℝ)⁻¹ ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hK2
      _ = 1 / 4 := by norm_num
  have hB := H36 δ ⟨hδ0, hδK'⟩
  -- the null set where the circle-average version fails on the grid
  have hgrid : (gridPts δ).Countable :=
    (Set.countable_range fun p : ℤ × ℤ => (⟨p.1 * δ, p.2 * δ⟩ : ℂ)).mono
      fun w ⟨a, b, hw⟩ => Set.mem_range.2 ⟨(a, b), hw.symm⟩
  have hN : ∀ᵐ ω ∂P, circleAvg (h ω) 1 0 = 0 ∧
      ∀ x ∈ gridPts δ, hc δ x ω = circleAvg (h ω) δ x :=
    hh.2.and ((ae_ball_iff hgrid).2 fun x _ => hver δ hδ0 x)
  have hN0 := ae_iff.1 hN
  obtain ⟨L0, hL0⟩ := L36.exists_graphPath hδ0 hδ4
  -- inclusion of the bad event
  have hsub : {ω | (2 : ℝ) ^ (-((K : ℝ) * (1 - ξ * Q γ - ζ))) <
        lenObs ξ (phiMN W P 0 K) (rectAB 1 1) ω} ⊆
      ({ω | ¬ ∀ z ∈ (rectAB 1 1).toSet, ∀ w ∈ (rectAB 1 1).toSet, ‖z - w‖ ≤ 2 * δ →
        |hc δ z ω - phiMN W P 0 K w ω| ≤ ζ₁ * K} ∪
      {ω | ¬ graphLFPP ξ δ (fun x => circleAvg (h ω) δ x) (leftVerts δ 1) (rightVerts δ 1) (rS 1)
        ≤ δ ^ (-ξ * Q γ - ζ₂) * Real.exp (ξ * circleAvg (h ω) 1 0)}) ∪
      {ω | ¬ (circleAvg (h ω) 1 0 = 0 ∧ ∀ x ∈ gridPts δ, hc δ x ω = circleAvg (h ω) δ x)} := by
    intro ω hω
    simp only [mem_setOf_eq] at hω
    by_contra hn
    simp only [mem_union, mem_setOf_eq, not_or, not_not] at hn
    obtain ⟨⟨hA', hB'⟩, hN1, hN2⟩ := hn
    rw [hN1, mul_zero, Real.exp_zero, mul_one] at hB'
    set M := δ ^ (-ξ * Q γ - ζ₂) with hM
    have hM0 : 0 < M := Real.rpow_pos_of_pos hδ0 _
    have : Nonempty {L : List ℂ // IsGraphPath δ (rS 1) L ∧ (∃ x ∈ L.head?, x ∈ leftVerts δ 1) ∧
        ∃ y ∈ L.getLast?, y ∈ rightVerts δ 1} := ⟨⟨L0, hL0⟩⟩
    obtain ⟨⟨L, hL, hl, hr⟩, hLs⟩ := exists_lt_of_ciInf_lt (lt_of_le_of_lt hB' (by linarith :
      M < 2 * M))
    simp only at hLs
    have hsumeq : (L.map fun x => Real.exp (ξ * circleAvg (h ω) δ x)) =
        L.map fun x => Real.exp (ξ * hc δ x ω) :=
      List.map_congr_left fun x hx => by rw [hN2 x (hL.2.1 x hx).2]
    rw [hsumeq] at hLs
    have hR := rectLen_le_graph (f := fun x => phiMN W P 0 K x ω) hξ.le hδ0 (by linarith)
      (g := fun x => hc δ x ω) (c := ζ₁ * K) hA' hL hl hr
    rw [List.sum_map_mul_right] at hR
    have hS0 : 0 ≤ (L.map fun x => Real.exp (ξ * hc δ x ω)).sum :=
      List.sum_nonneg fun b hb => by obtain ⟨z, -, rfl⟩ := List.mem_map.1 hb; positivity
    have hle := ENNReal.toReal_le_of_le_ofReal (by positivity) hR
    have hlen : lenObs ξ (phiMN W P 0 K) (rectAB 1 1) ω ≤
        12 * δ * Real.exp (ξ * (ζ₁ * K)) * M := by
      refine hle.trans ?_
      have he := Real.exp_pos (ξ * (ζ₁ * K))
      have := mul_le_mul_of_nonneg_left hLs.le (by positivity : 0 ≤ 6 * δ * Real.exp (ξ * (ζ₁ * K)))
      nlinarith
    have key := up_arith (q := Q γ) (ζ := ζ) hξ K hexpK.le
    rw [← hδ, ← hζ₂, ← hζ₁, ← hM] at key
    linarith
  refine (measure_mono hsub).trans_lt ?_
  refine ((measure_union_le _ _).trans (by rw [hN0, add_zero])).trans_lt ?_
  refine (measure_union_le _ _).trans_lt ?_
  calc _ < ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) :=
        ENNReal.add_lt_add_of_lt_of_le (measure_ne_top P _) hAK hB
    _ = ENNReal.ofReal (1 / 4) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
    _ < 2⁻¹ := by
        rw [show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) by
          rw [one_div, ENNReal.ofReal_inv_of_pos two_pos]; simp]
        exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)

/-- **DDDF (5.78)** (`eq:DGupperQuantile`, l. 1276–1281) for `ξ = γ/d_γ` and every white noise,
from DG Prop 3.21 (via DFGPS Lemma 3.6) and the comparison `WPPhiCompare`. -/
theorem s6Eq5_78_of_DG (hP3 : DGProp3_21) (hcmp : WPPhiCompare) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hW : IsWhiteNoise P W) : S6Eq5_78 (xiGamma γ) (Q γ) W P := by
  obtain ⟨Ω', _, P', W', h, hc, hW', hh, -, hver, hc'⟩ := hcmp
  intro ζ hζ
  set ζ' := min ζ (1 / 2) with hζ'
  have hζ'0 : 0 < ζ' := lt_min hζ (by norm_num)
  have hζ'1 : ζ' < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨K₀, hK₀⟩ := prob_lenObs_gt_lt_half hP3 hγ hγ2 hW' hh hver (hc' 2 two_pos) hζ'0 hζ'1
  refine ⟨K₀, fun K hK => ?_⟩
  have key := lambdaN_le_of_prob_lt hW (by rw [prob_lenObs_gt_eq hW hW']; exact hK₀ K hK)
  refine key.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  have : ζ' ≤ ζ := min_le_left _ _
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  nlinarith

end S6DG
end DDDF
end LQGMetric
