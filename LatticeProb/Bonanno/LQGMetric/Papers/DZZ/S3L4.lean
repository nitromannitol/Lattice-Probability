/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L4Union

/-!
# DZZ Lemma 3.4 (`lem-neighboring-cell`) (P2-DZZ3B, WP-113)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 861–903). The event
`𝓔_{δ,α}` (eq-def-E-delta-alpha) is `eventEDeltaAlpha γ W α δ = cellSizeEvent γ W δ ∩
nbrEvent W C_mc α δ` (η-part on dyadic centres, decision D64).

* `nbrEventGen_compl_le` (S3L4Union): the union bound over `m ≤ δ^{−C_mc}`, `j ≤ (α log δ⁻¹)²` and the pairs of
  boxes (DZZ l. 893–899).
* `l34_eventually`: the elementary asymptotics in `L = log δ⁻¹` ("with high probability"):
  `8((αL)² + 1)(αL)⁴ ≤ e^L` and `8K(8609 + log (αL)²) ≤ α² (log L)²` for large `L`.
* `nbrEvent_highProb`: for every `α > 0`, `nbrEvent` holds with high probability
  (with `P(failure) ≤ δ`).
* **`dzz_lemma34`**: there is `α₀ > 0` such that `𝓔_{δ,α}` holds with high probability for all
  `α > α₀` (with Lemma 3.1, `dzz_lemma31`). On centres any `α > 0` works (`dzz_lemma34_of_pos`);
  DZZ need `α` large for the continuum maxima of their first three terms, absent here (D64).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- DZZ's event `𝓔_{δ,α}` (eq-def-E-delta-alpha, l. 861), η-part on dyadic centres (D64). -/
def eventEDeltaAlpha (γ : ℝ) (W : WNSpace → Ω → ℝ) (α δ : ℝ) : Set Ω :=
  cellSizeEvent γ W δ ∩ nbrEvent W (dzzCmc γ) α δ

/-- The elementary asymptotics in `L = log δ⁻¹`. -/
lemma l34_eventually {α K D : ℝ} (hα : 0 < α) (hK : 0 ≤ K) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ 1 ≤ (α * L) ^ 2 ∧
      8 * ((α * L) ^ 2 + 1) * ((α * L) ^ 2) ^ 2 ≤ Real.exp L ∧
      K * (D + Real.log ((α * L) ^ 2)) ≤ α ^ 2 * Real.log L ^ 2 := by
  set c : ℝ := 8 * (α ^ 2 + 1) * α ^ 4 with hc
  have hc0 : 0 < c := by positivity
  have hpoly := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 6).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / c))
  set A := 2 * K / α ^ 2
  set B := K * (D + 2 * |Real.log α|) / α ^ 2
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (A + B + 1))
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (1 / α), hpoly, hlog] with
    L hL1 hLα hLp hLl
  have hL0 : 0 < L := by linarith
  have hαL : 1 ≤ α * L := by rwa [div_le_iff₀' hα] at hLα
  refine ⟨hL1, by nlinarith, ?_, ?_⟩
  · have he := Real.exp_pos L
    have h1 : L ^ 6 < 1 / c * Real.exp L := by
      have := (mul_lt_mul_iff_of_pos_right he).2 hLp
      rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at this
    have h2 : c * L ^ 6 < Real.exp L := by
      have := (mul_lt_mul_iff_of_pos_left hc0).2 h1
      rwa [← mul_assoc, mul_one_div_cancel hc0.ne', one_mul] at this
    have hL2 : 1 ≤ L ^ 2 := by nlinarith
    have h3 : (α * L) ^ 2 + 1 ≤ (α ^ 2 + 1) * L ^ 2 := by nlinarith
    calc 8 * ((α * L) ^ 2 + 1) * ((α * L) ^ 2) ^ 2
        ≤ 8 * ((α ^ 2 + 1) * L ^ 2) * ((α * L) ^ 2) ^ 2 := by gcongr
      _ = c * L ^ 6 := by rw [hc]; ring
      _ ≤ Real.exp L := h2.le
  · set x := Real.log L
    have hx1 : 1 ≤ x := by linarith
    have hlog2 : Real.log ((α * L) ^ 2) = 2 * Real.log α + 2 * x := by
      rw [Real.log_pow, Real.log_mul hα.ne' hL0.ne']; push_cast; ring
    rw [hlog2]
    have hq : A * x + B ≤ x ^ 2 := by nlinarith
    have hα2 : 0 < α ^ 2 := by positivity
    have e1 : α ^ 2 * (A * x + B) = 2 * K * x + K * (D + 2 * |Real.log α|) := by
      simp only [A, B]; field_simp
    have hab : Real.log α ≤ |Real.log α| := le_abs_self _
    have : 2 * K * x + K * (D + 2 * |Real.log α|) ≤ α ^ 2 * x ^ 2 := by
      rw [← e1]; exact mul_le_mul_of_nonneg_left hq hα2.le
    nlinarith [mul_le_mul_of_nonneg_left hab hK]

/-- For every `α > 0` and `C_mc ≥ 0`, `nbrEvent` holds with high probability. -/
theorem nbrEvent_highProb (hW : IsWhiteNoise P W) {Cmc α : ℝ} (hCmc : 0 ≤ Cmc) (hα : 0 < α) :
    HighProb P (fun δ => nbrEvent W Cmc α δ) := by
  have := hW.isProbabilityMeasure
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 (l34_eventually (K := 8 * (5 * Cmc + 2)) (D := 1076 * 8 + 1) hα (by linarith)
    (by norm_num))
  refine ⟨1, one_pos, Real.exp (-max L₀ 1), Real.exp_pos _, fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδ1⟩ := hδ
  set L := Real.log δ⁻¹ with hLdef
  have hLgt : max L₀ 1 < L := by
    rw [hLdef, Real.log_inv, lt_neg]
    exact (Real.log_lt_iff_lt_exp hδ0).2 hδ1
  obtain ⟨hL1, hY, hpoly, hlog⟩ := hL₀ L (le_max_left _ _ |>.trans hLgt.le)
  have hδ1' : δ < 1 := hδ1.trans_le (by rw [Real.exp_le_one_iff]; linarith [le_max_right L₀ 1])
  have hδL : δ = Real.exp (-L) := by
    rw [hLdef, Real.log_inv, neg_neg, Real.exp_log hδ0]
  have hX : δ ^ (-Cmc) = Real.exp (Cmc * L) := by
    rw [Real.rpow_def_of_pos hδ0, hLdef, Real.log_inv]; ring_nf
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hT : 0 ≤ α * Real.sqrt L * Real.log L := by positivity
  have hX1 : 1 ≤ δ ^ (-Cmc) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ0 hδ1'.le (by linarith)
  have hmain := nbrEventGen_compl_le (P := P) hW (K := 8) (by norm_num) hX1 hY hT
  rw [← ofReal_measureReal (measure_ne_top _ _), Real.rpow_one]
  refine ENNReal.ofReal_le_ofReal (hmain.trans ?_)
  rw [hX]
  set Y := (α * L) ^ 2
  set V := 1076 * 8 + 1 + Real.log Y
  have hV : 0 < V := by have := Real.log_nonneg hY; simp only [V]; linarith
  set E := Real.exp (Cmc * L)
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  -- the Gaussian factor
  have hT2 : (α * Real.sqrt L * Real.log L / 2) ^ 2 = α ^ 2 * Real.log L ^ 2 * L / 4 := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by linarith)]; ring
  have hG : Real.exp (-(α * Real.sqrt L * Real.log L / 2) ^ 2 / (2 * V)) ≤
      Real.exp (-((5 * Cmc + 2) * L)) := by
    refine Real.exp_le_exp.2 ?_
    rw [hT2, neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hlog (by linarith : (0 : ℝ) ≤ L)
    nlinarith
  have hE5 : E ^ 5 * Real.exp (-((5 * Cmc + 2) * L)) = Real.exp (-(2 * L)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have hfin : Real.exp L * Real.exp (-(2 * L)) = δ := by
    rw [← Real.exp_add, hδL]; congr 1; ring
  have hY0 : 0 ≤ Y := by positivity
  calc (E + 1) * (Y + 1) * (2 * (E ^ 4 * Y ^ 2) *
        (2 * Real.exp (-(α * Real.sqrt L * Real.log L / 2) ^ 2 / (2 * V))))
      ≤ (E + E) * (Y + 1) * (2 * (E ^ 4 * Y ^ 2) * (2 * Real.exp (-((5 * Cmc + 2) * L)))) := by
        gcongr
    _ = (8 * (Y + 1) * Y ^ 2) * (E ^ 5 * Real.exp (-((5 * Cmc + 2) * L))) := by ring
    _ ≤ Real.exp L * (E ^ 5 * Real.exp (-((5 * Cmc + 2) * L))) := by
        gcongr
    _ = δ := by rw [hE5, hfin]

lemma dzzCmc_nonneg {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : 0 ≤ dzzCmc γ :=
  (dzzCMc_pos γ).le.trans (dzzCMc_le_dzzCmc hγ hγ2)

/-- **DZZ Lemma 3.4** on dyadic centres, for every `α > 0`. -/
theorem dzz_lemma34_of_pos (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {α : ℝ}
    (hα : 0 < α) : HighProb P (fun δ => eventEDeltaAlpha γ W α δ) :=
  have := hW.isProbabilityMeasure
  (dzz_lemma31 hW hγ hγ2).inter (nbrEvent_highProb hW (dzzCmc_nonneg hγ hγ2) hα)

end DZZ
end LQGMetric
