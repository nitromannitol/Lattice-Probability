/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12P2D at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P2C

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.2, Step 1–2: a.s. convergence along one deterministic subsequence (P-2)

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Theorem 1.2,
T:1344–1345: "every deterministic subsequence of the `ε_n`'s has a further deterministic
subsequence `ε_{n_k}` along which `D^{ε_{n_k}}_h → D_h` a.s.", here for the countably many
truncated local metrics `truncW(𝔞⁻¹D̂^ε_h(·,·;W̄))`, `W` dyadic (Step 2, T:1368–1372).

* `exists_subseq_ae_tendsto_all` — for countably many sequences converging in measure, one
  subsequence along which all converge a.s. (Borel–Cantelli, `ae_eventually_notMem`; the
  standard argument, own packaging).
* `exists_subseq_truncW_ae` — **P-2 (truncated form)**.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.T12

open Blueprint MetricGeometry LFPP

/-- **a common a.s.-convergent subsequence** for countably many sequences converging in measure
(Borel–Cantelli) -/
theorem exists_subseq_ae_tendsto_all {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] [Countable ι] {E : ι → Type*} [∀ i, PseudoEMetricSpace (E i)]
    {f : ∀ i, ℕ → α → E i} {g : ∀ i, α → E i}
    (hfg : ∀ i, TendstoInMeasure μ (f i) atTop (g i)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, ∀ i, Tendsto (fun n => f i (ns n) x) atTop (𝓝 (g i x)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨id, strictMono_id, Eventually.of_forall fun x i => isEmptyElim i⟩
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  set r : ℝ≥0∞ := 2⁻¹ with hr
  have hr0 : ∀ n : ℕ, 0 < r ^ n := fun n => ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) n
  have hev : ∀ n : ℕ, ∀ᶠ m in atTop, ∀ k ∈ Finset.range (n + 1),
      μ {x | r ^ n ≤ edist (f (e k) m x) (g (e k) x)} < r ^ n := fun n =>
    (Finset.eventually_all _).2 fun k _ =>
      (tendsto_order.1 (hfg (e k) (r ^ n) (hr0 n))).2 _ (hr0 n)
  obtain ⟨ns, hns, hP⟩ := extraction_forall_of_eventually hev
  refine ⟨ns, hns, ?_⟩
  have hgeo : (∑' n : ℕ, r ^ n) ≠ ∞ := by
    rw [ENNReal.tsum_geometric, hr, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  have hk : ∀ k : ℕ, ∀ᵐ x ∂μ, ∀ᶠ n in atTop,
      x ∉ {x | k ≤ n ∧ r ^ n ≤ edist (f (e k) (ns n) x) (g (e k) x)} := by
    intro k
    refine ae_eventually_notMem (ne_top_of_le_ne_top hgeo (ENNReal.tsum_le_tsum fun n => ?_))
    by_cases hkn : k ≤ n
    · refine (measure_mono fun x hx => hx.2).trans (hP n k ?_).le
      exact Finset.mem_range.2 (Nat.lt_succ_of_le hkn)
    · have : {x | k ≤ n ∧ r ^ n ≤ edist (f (e k) (ns n) x) (g (e k) x)} = ∅ :=
        eq_empty_of_forall_notMem fun x hx => hkn hx.1
      rw [this, measure_empty]; exact zero_le
  have hrt : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by rw [hr]; exact ENNReal.inv_lt_one.2 (by norm_num))
  filter_upwards [ae_all_iff.2 hk] with x hx i
  obtain ⟨k, rfl⟩ := he i
  rw [tendsto_iff_edist_tendsto_0]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrt
    (Eventually.of_forall fun n => zero_le) ?_
  filter_upwards [hx k, eventually_ge_atTop k] with n hn hkn
  simp only [not_and, not_le] at hn
  exact (hn hkn).le

end LQGMetric.DFGPS.T12
