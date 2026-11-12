/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L4Tail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L6Log
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Tele

/-!
# DZZ Lemma 3.4, inputs: Gaussian tails of `η` increments (P2-DZZ3B, WP-113)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 873–903), proof of
Lemma 3.4 (`lem-neighboring-cell`): the four-term triangle inequality is bounded by
"Lemma 2.6 and a union bound" (space increments of `η_{2^{-i}}` at distance `≲ 2^{-i}`) and
"a union bound over `j` and `y ∈ 𝔠_{m+j}`" (scale increments `η_{2^{-m-j}}(y) − η_{2^{-m}}(y)`).
On dyadic centres (decision D64) only Gaussian tails of single increments are needed:

* `tail_abs_le_of_hasLaw_le`: `P(|U| ≥ y) ≤ 2 e^{−y²/(2V)}` for `U ~ N(0, v)`, `v ≤ V`
  (Chernoff, mathlib `measure_ge_le_exp_mul_mgf`).
* `tail_sqrtPi_sub`: the same for `√π W(f) − √π W(g)` with `π‖f − g‖² ≤ V`.
* `tail_etaInf_space`: `|x − y| ≤ Kε ⇒ P(|η_ε(x) − η_ε(y)| ≥ a) ≤ 2 e^{−a²/(2·1076K)}`
  (DZZ Lemma 2.5, `pi_sq_norm_etaKernelL2_sub_le`).
* `tail_etaInf_scale`: `ε' ≤ ε ⇒ P(|η_ε(y) − η_{ε'}(y)| ≥ a) ≤ 2 e^{−a²/(2(log(ε/ε') + 1))}`
  (the band `η_{ε'}^{ε}(y)` has variance `≤ log(ε/ε')`, `pi_sq_norm_etaKernelL2_Ioo_le`).
* `HighProb.inter`: intersections of high-probability events.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open WhiteNoise KilledHeat

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- Two-sided Gaussian tail with a variance upper bound:
`P(|U| ≥ y) ≤ 2 e^{−y²/(2V)}` for `U ~ N(0, v)`, `v ≤ V`, `V > 0`, `y ≥ 0`. -/
lemma tail_abs_le_of_hasLaw_le [IsProbabilityMeasure P] {U : Ω → ℝ} {v : ℝ≥0}
    (hU : HasLaw U (gaussianReal 0 v) P) {V : ℝ} (hV : 0 < V) (hvV : (v : ℝ) ≤ V) {y : ℝ}
    (hy : 0 ≤ y) :
    P.real {ω | y ≤ |U ω|} ≤ 2 * Real.exp (-y ^ 2 / (2 * V)) := by
  have hint : ∀ t, Integrable (fun ω => Real.exp (t * U ω)) P := fun t => by
    have := integrable_exp_mul_gaussianReal (μ := 0) (v := v) t
    rw [← hU.map_eq] at this
    exact (integrable_map_measure (by fun_prop) hU.aemeasurable).1 this
  have hmgf : ∀ t, mgf U P t ≤ Real.exp (V * t ^ 2 / 2) := fun t => by
    rw [mgf_gaussianReal hU]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_right hvV (sq_nonneg t)
    linarith
  have ht : 0 ≤ y / V := div_nonneg hy hV.le
  have h1 := measure_ge_le_exp_mul_mgf (μ := P) (X := U) y ht (hint _)
  have h2 := measure_le_le_exp_mul_mgf (μ := P) (X := U) (-y) (t := -(y / V))
    (by linarith) (hint _)
  have e1 : Real.exp (-(y / V) * y) * Real.exp (V * (y / V) ^ 2 / 2) =
      Real.exp (-y ^ 2 / (2 * V)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have e2 : Real.exp (-(-(y / V)) * -y) * Real.exp (V * (-(y / V)) ^ 2 / 2) =
      Real.exp (-y ^ 2 / (2 * V)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have h1' : P.real {ω | y ≤ U ω} ≤ Real.exp (-y ^ 2 / (2 * V)) := by
    rw [← e1]
    exact h1.trans (mul_le_mul_of_nonneg_left (hmgf _) (Real.exp_pos _).le)
  have h2' : P.real {ω | U ω ≤ -y} ≤ Real.exp (-y ^ 2 / (2 * V)) := by
    rw [← e2]
    exact h2.trans (mul_le_mul_of_nonneg_left (hmgf _) (Real.exp_pos _).le)
  have hsub : {ω | y ≤ |U ω|} ⊆ {ω | y ≤ U ω} ∪ {ω | U ω ≤ -y} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_union] at hω ⊢
    rcases le_abs'.1 hω with h | h
    · right; linarith
    · left; exact h
  calc P.real {ω | y ≤ |U ω|} ≤ P.real ({ω | y ≤ U ω} ∪ {ω | U ω ≤ -y}) := measureReal_mono hsub
    _ ≤ P.real {ω | y ≤ U ω} + P.real {ω | U ω ≤ -y} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-y ^ 2 / (2 * V)) := by linarith

/-- Gaussian tail of `√π W(f) − √π W(g)` when `π ‖f − g‖² ≤ V`. -/
lemma tail_sqrtPi_sub (hW : IsWhiteNoise P W) (f g : WNSpace) {V : ℝ} (hV : 0 < V)
    (hfg : Real.pi * ‖f - g‖ ^ 2 ≤ V) {y : ℝ} (hy : 0 ≤ y) :
    P.real {ω | y ≤ |Real.sqrt Real.pi * W f ω - Real.sqrt Real.pi * W g ω|} ≤
      2 * Real.exp (-y ^ 2 / (2 * V)) := by
  have := hW.isProbabilityMeasure
  have h := hW.hasLaw (ι := Fin 2) ![f, g] ![Real.sqrt Real.pi, -Real.sqrt Real.pi]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have e : (fun ω => Real.sqrt Real.pi * W f ω + -Real.sqrt Real.pi * W g ω) =
      fun ω => Real.sqrt Real.pi * W f ω - Real.sqrt Real.pi * W g ω := by
    funext ω; ring
  rw [e] at h
  refine tail_abs_le_of_hasLaw_le h hV ?_ hy
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  have e2 : Real.sqrt Real.pi • f + -Real.sqrt Real.pi • g = Real.sqrt Real.pi • (f - g) := by
    rw [smul_sub, neg_smul, sub_eq_add_neg]
  rw [e2, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt Real.pi_pos.le]
  exact hfg

/-- Space increments of `η_ε` at distance `≤ Kε` (DZZ Lemma 2.5: variance `≤ 1076 K`). -/
lemma tail_etaInf_space (hW : IsWhiteNoise P W) {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K) {x y : ℂ}
    (hxy : ‖x - y‖ ≤ K * ε) {a : ℝ} (ha : 0 ≤ a) :
    P.real {ω | a ≤ |etaInf W ε x ω - etaInf W ε y ω|} ≤
      2 * Real.exp (-a ^ 2 / (2 * (1076 * K))) := by
  refine tail_sqrtPi_sub hW _ _ (by positivity) ?_ ha
  refine (pi_sq_norm_etaKernelL2_sub_le hW hε x y).trans ?_
  rw [div_le_iff₀ hε]
  have := mul_le_mul_of_nonneg_left hxy (by norm_num : (0 : ℝ) ≤ 1076)
  linarith

/-- Scale increments `η_ε(y) − η_{ε'}(y)`, `0 < ε' ≤ ε`: the band `(ε'², ε²)` has
variance `≤ log(ε/ε')`. -/
lemma tail_etaInf_scale (hW : IsWhiteNoise P W) {ε ε' : ℝ} (hε' : 0 < ε') (hεε : ε' ≤ ε)
    (y : ℂ) {a : ℝ} (ha : 0 ≤ a) :
    P.real {ω | a ≤ |etaInf W ε y ω - etaInf W ε' y ω|} ≤
      2 * Real.exp (-a ^ 2 / (2 * (Real.log (ε / ε') + 1))) := by
  have hε : 0 < ε := hε'.trans_le hεε
  have hlog : 0 ≤ Real.log (ε / ε') := Real.log_nonneg ((one_le_div hε').2 hεε)
  refine tail_sqrtPi_sub hW _ _ (by linarith) ?_ ha
  have hsq : ε' ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ hε'.le hεε 2
  rw [etaKernelL2_split (by positivity) hsq y]
  have e : etaKernelL2 (Ioi (ε ^ 2)) y -
      (etaKernelL2 (Ioi (ε ^ 2)) y + etaKernelL2 (Ioo (ε' ^ 2) (ε ^ 2)) y) =
      -etaKernelL2 (Ioo (ε' ^ 2) (ε ^ 2)) y := by abel
  rw [e, norm_neg]
  have h := pi_sq_norm_etaKernelL2_Ioo_le (by positivity : 0 < ε' ^ 2) hsq y
  rw [← div_pow, Real.log_pow] at h
  push_cast at h
  linarith

/-- High-probability events are closed under intersections. -/
lemma HighProb.inter {E F : ℝ → Set Ω} (hE : HighProb P E) (hF : HighProb P F) :
    HighProb P (fun δ => E δ ∩ F δ) := by
  obtain ⟨c₁, hc₁, δ₁, hδ₁, h₁⟩ := hE
  obtain ⟨c₂, hc₂, δ₂, hδ₂, h₂⟩ := hF
  set c := min c₁ c₂
  have hc : 0 < c := lt_min hc₁ hc₂
  refine ⟨c / 2, by positivity, min (min δ₁ δ₂) ((1 / 2) ^ (2 / c)), by positivity,
    fun δ hδ => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδa : δ < δ₁ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδb : δ < δ₂ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδc : δ < (1 / 2) ^ (2 / c) := hδ.2.trans_le (min_le_right _ _)
  have hδ1 : δ < 1 := hδc.trans_le (Real.rpow_le_one (by norm_num) (by norm_num) (by positivity))
  rw [compl_inter]
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add (h₁ δ ⟨hδ0, hδa⟩) (h₂ δ ⟨hδ0, hδb⟩)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have m1 : δ ^ c₁ ≤ δ ^ c := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_left _ _)
  have m2 : δ ^ c₂ ≤ δ ^ c := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_right _ _)
  -- `δ^{c/2} ≤ 1/2`
  have hhalf : δ ^ (c / 2) ≤ 1 / 2 := by
    have := Real.rpow_le_rpow hδ0.le hδc.le (by positivity : 0 ≤ c / 2)
    rwa [← Real.rpow_mul (by norm_num), show 2 / c * (c / 2) = 1 by field_simp,
      Real.rpow_one] at this
  have hsplit : δ ^ c = δ ^ (c / 2) * δ ^ (c / 2) := by
    rw [← Real.rpow_add hδ0]; ring_nf
  have hpos : 0 ≤ δ ^ (c / 2) := by positivity
  nlinarith

end DZZ
end LQGMetric
