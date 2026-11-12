/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L23Var at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Variance bounds pass to pointwise limits (tool for DDDF Lemma 23)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1046–1049 (proof of `Lem:VarApriori`):
"`L^{(n)}_{1,1}(φ) = lim_k L^{(n)}_{1,1}(D_k)` almost surely. By dominated convergence
`Var log L^{(n)}_{1,1}(φ) = lim_k Var log L^{(n)}_{1,1}(D_k)`."

We only need the inequality `Var X ≤ sup_k Var X_k`, and prove it by Fatou's lemma instead of
dominated convergence, which avoids the integrable dominating function (`sup_{[0,1]²} |φ_{0,n}|`
in `L²`) that DDDF leave implicit: if `X_k → X` pointwise, `X_k ∈ L²` and `Var X_k ≤ V`, then
`X ∈ L²` and `Var X ≤ V` (`DDDF.L23.memLp_variance_le_of_tendsto`). Own elementary proof
(deviation, see the report): the means `E X_k` are bounded (Chebyshev plus
`P(sup_k |X_k| ≤ M) > 1/2`), a subsequence converges to some `a`, and Fatou gives
`E (X − a)² ≤ liminf Var X_{k_j} ≤ V`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace LQGMetric
namespace DDDF
namespace L23

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- the means of a pointwise convergent sequence with bounded variances are bounded -/
lemma exists_bound_integral {X : ℕ → Ω → ℝ} {Xl : Ω → ℝ} (hm : ∀ k, Measurable (X k))
    (hL2 : ∀ k, MemLp (X k) 2 P) {V : ℝ} (hV : ∀ k, Var[X k; P] ≤ V)
    (hconv : ∀ ω, Tendsto (fun k => X k ω) atTop (𝓝 (Xl ω))) :
    ∃ B : ℝ, ∀ k, |∫ ω, X k ω ∂P| ≤ B := by
  have hV0 : 0 ≤ V := (variance_nonneg _ _).trans (hV 0)
  set E : ℕ → Set Ω := fun M => ⋂ k, {ω | |X k ω| ≤ M} with hE
  have hEm : ∀ M, MeasurableSet (E M) := fun M =>
    MeasurableSet.iInter fun k => measurableSet_le (continuous_abs.measurable.comp (hm k)) measurable_const
  have hEmono : Monotone E := fun M M' h ω hω => by
    simp only [hE, mem_iInter, mem_setOf_eq] at hω ⊢
    exact fun k => (hω k).trans (by exact_mod_cast h)
  have hEU : (⋃ M, E M) = univ := by
    refine eq_univ_of_forall fun ω => ?_
    obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ (hconv ω)).exists_norm_le
    obtain ⟨M, hM⟩ := exists_nat_ge C
    exact mem_iUnion.2 ⟨M, mem_iInter.2 fun k =>
      (hC _ (mem_range_self k)).trans hM⟩
  have hlim := tendsto_measure_iUnion_atTop (μ := P) hEmono
  rw [hEU, measure_univ] at hlim
  have hev := (hlim.eventually (lt_mem_nhds (show (1 / 2 : ENNReal) < 1 by norm_num)))
  obtain ⟨M, hM⟩ := hev.exists
  set c := 2 * √V + 1 with hc
  have hc0 : 0 < c := by positivity
  refine ⟨M + c, fun k => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hsub : E M ⊆ {ω | c ≤ |X k ω - P[X k]|} := by
    intro ω hω
    have h1 : |X k ω| ≤ M := by simp only [hE, mem_iInter, mem_setOf_eq] at hω; exact hω k
    simp only [mem_setOf_eq]
    have := abs_sub_abs_le_abs_sub (P[X k]) (X k ω)
    rw [abs_sub_comm] at this
    linarith
  have hcheb := (measure_mono hsub).trans (meas_ge_le_variance_div_sq (hL2 k) hc0)
  have hq : Var[X k; P] / c ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have hs := Real.sq_sqrt hV0
    have : V ≤ c ^ 2 / 2 := by rw [hc]; nlinarith [Real.sqrt_nonneg V]
    linarith [hV k]
  have : (1 / 2 : ENNReal) < ENNReal.ofReal (1 / 2) := hM.trans_le
    (hcheb.trans (ENNReal.ofReal_le_ofReal hq))
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at this
  exact lt_irrefl _ this

/-- **Variance bounds pass to pointwise limits**: if `X_k → X` pointwise, each `X_k` is
measurable and in `L²`, and `Var X_k ≤ V`, then `X ∈ L²` and `Var X ≤ V`. -/
theorem memLp_variance_le_of_tendsto {X : ℕ → Ω → ℝ} {Xl : Ω → ℝ} (hm : ∀ k, Measurable (X k))
    (hL2 : ∀ k, MemLp (X k) 2 P) {V : ℝ} (hV : ∀ k, Var[X k; P] ≤ V)
    (hconv : ∀ ω, Tendsto (fun k => X k ω) atTop (𝓝 (Xl ω))) :
    MemLp Xl 2 P ∧ Var[Xl; P] ≤ V := by
  have hV0 : 0 ≤ V := (variance_nonneg _ _).trans (hV 0)
  obtain ⟨B, hB⟩ := exists_bound_integral hm hL2 hV hconv
  set m : ℕ → ℝ := fun k => ∫ ω, X k ω ∂P
  obtain ⟨a, -, φ, hφ, hma⟩ := tendsto_subseq_of_bounded (Metric.isBounded_closedBall (x := 0)
    (r := B)) (x := m) fun k => by
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]; exact hB k
  have hXlm : Measurable Xl := measurable_of_tendsto_metrizable hm (tendsto_pi_nhds.2 hconv)
  set f : ℕ → Ω → ENNReal := fun j ω => ENNReal.ofReal ((X (φ j) ω - m (φ j)) ^ 2)
  have hf : ∀ j, ∫⁻ ω, f j ω ∂P = ENNReal.ofReal (Var[X (φ j); P]) := fun j => by
    rw [(hL2 (φ j)).ofReal_variance_eq, evariance_eq_lintegral_ofReal]
  have hfl : ∀ ω, Tendsto (fun j => f j ω) atTop (𝓝 (ENNReal.ofReal ((Xl ω - a) ^ 2))) :=
    fun ω => ENNReal.tendsto_ofReal ((((hconv ω).comp hφ.tendsto_atTop).sub hma).pow 2)
  have hfat := lintegral_liminf_le' (μ := P) (u := atTop) (f := f)
    (fun j => (((hm (φ j)).sub measurable_const).pow_const 2).ennreal_ofReal.aemeasurable)
  simp_rw [fun ω => (hfl ω).liminf_eq, hf] at hfat
  have hle : ∫⁻ ω, ENNReal.ofReal ((Xl ω - a) ^ 2) ∂P ≤ ENNReal.ofReal V :=
    hfat.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun j =>
      ENNReal.ofReal_le_ofReal (hV _)))
  have hmeas : AEStronglyMeasurable (fun ω => (Xl ω - a) ^ 2) P :=
    ((hXlm.sub measurable_const).pow_const 2).aestronglyMeasurable
  have hint : Integrable (fun ω => (Xl ω - a) ^ 2) P :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas (ae_of_all _ fun ω => sq_nonneg _)).1
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)
  have hL2a : MemLp (fun ω => Xl ω - a) 2 P :=
    (memLp_two_iff_integrable_sq (hXlm.sub measurable_const).aestronglyMeasurable).2 hint
  have hL2X : MemLp Xl 2 P := by
    have := hL2a.add (memLp_const a)
    convert this using 1
    ext ω; simp
  refine ⟨hL2X, ?_⟩
  rw [← variance_sub_const hXlm.aestronglyMeasurable a]
  refine (variance_le_expectation_sq (hXlm.sub measurable_const).aestronglyMeasurable).trans ?_
  show ∫ ω, (Xl ω - a) ^ 2 ∂P ≤ V
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => sq_nonneg _) hmeas]
  exact ENNReal.toReal_le_of_le_ofReal hV0 hle

end L23
end DDDF
end LQGMetric
