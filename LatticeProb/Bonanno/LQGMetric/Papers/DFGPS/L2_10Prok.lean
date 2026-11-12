/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_10Prok at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_10
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.10, first step: a uniform `R` from tightness (T:953–957)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:953–957: "By Lemma 2.8 applied with
`W̄ = S_1(0)`, there exists `R = R(p,C) > 1` such that `liminf_{ε→0} P[sup_{u,v∈S_{1/R}(0)}
D_h^ε(u,v) < C⁻¹ D_h^ε(S_{1/R}(0), ∂S_1(0))] ≥ p`." The paper gives no further detail. We prove
the abstract principle behind it (own argument, standard): for an increasing sequence of open
sets `G_R` in a Polish space and a tight family of laws `L_ε` all of whose subsequential limits as
`ε → 0` are carried by `⋃ G_R`, for every `p < 1` some `G_R` has `L_ε`-mass `≥ p` for all small
`ε`. Proof: otherwise pick `ε_n → 0` with `L_{ε_n}(G_n) < p`, extract a convergent subsequence
(Prokhorov, mathlib `isCompact_closure_of_isTightMeasureSet`), and apply the portmanteau theorem
(`ProbabilityMeasure.le_liminf_measure_open_of_tendsto`) to each open `G_R`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

/-- **Uniform choice of an open set of large mass** (abstract form of T:953–957). -/
theorem exists_eventually_measure_ge {E : Type*} [TopologicalSpace E] [PolishSpace E]
    [MeasurableSpace E] [BorelSpace E] (L : ℝ → Measure E)
    (hL : ∀ ε ∈ Ioo (0 : ℝ) 1, IsProbabilityMeasure (L ε))
    (hT : IsTightMeasureSet {μ | ∃ ε ∈ Ioo (0 : ℝ) 1, μ = L ε})
    {G : ℕ → Set E} (hGo : ∀ R, IsOpen (G R)) (hGm : Monotone G)
    (hlim : ∀ (εn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure E) (μ : ProbabilityMeasure E),
      (∀ n, εn n ∈ Ioo (0 : ℝ) 1 ∧ (ν n : Measure E) = L (εn n)) →
      Tendsto εn atTop (𝓝 0) → Tendsto ν atTop (𝓝 μ) → (μ : Measure E) (⋃ R, G R) = 1)
    {p : ℝ} (hp : p < 1) :
    ∃ R : ℕ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ENNReal.ofReal p ≤ L ε (G R) := by
  by_contra H
  push Not at H
  have hfreq : ∀ n : ℕ, ∃ ε, ε ∈ Ioo (0 : ℝ) (min 1 (1 / ((n : ℝ) + 1))) ∧
      L ε (G n) < ENNReal.ofReal p := by
    intro n
    have hpos : (0 : ℝ) < min 1 (1 / ((n : ℝ) + 1)) := lt_min one_pos (by positivity)
    obtain ⟨ε, h1, h2⟩ := ((H n).and_eventually (Ioo_mem_nhdsGT hpos)).exists
    exact ⟨ε, h2, h1⟩
  choose εn hεn hεL using hfreq
  have hεI : ∀ n, εn n ∈ Ioo (0 : ℝ) 1 := fun n =>
    ⟨(hεn n).1, (hεn n).2.trans_le (min_le_left _ _)⟩
  have hε0 : Tendsto εn atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (hεn n).1.le) (fun n => ?_)
    exact ((hεn n).2.trans_le (min_le_right _ _)).le
  let ν : ℕ → ProbabilityMeasure E := fun n => ⟨L (εn n), hL _ (hεI n)⟩
  have hTν : IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ range ν} := by
    refine hT.subset ?_
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨εn n, hεI n, rfl⟩
  obtain ⟨μ, -, ψ, hψ, hconv⟩ := (isCompact_closure_of_isTightMeasureSet hTν).tendsto_subseq
    (x := ν) fun n => subset_closure ⟨n, rfl⟩
  have h1 := hlim (εn ∘ ψ) (ν ∘ ψ) μ (fun n => ⟨hεI _, rfl⟩) (hε0.comp hψ.tendsto_atTop) hconv
  have hle : ∀ R, (μ : Measure E) (G R) ≤ ENNReal.ofReal p := by
    intro R
    refine (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hconv (hGo R)).trans ?_
    refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
    filter_upwards [eventually_ge_atTop R] with n hn
    exact (measure_mono (hGm (hn.trans (hψ.id_le n)))).trans (hεL (ψ n)).le
  have hU : (μ : Measure E) (⋃ R, G R) ≤ ENNReal.ofReal p := by
    rw [hGm.measure_iUnion]
    exact iSup_le hle
  rw [h1] at hU
  have : ENNReal.ofReal p < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hp
  exact absurd hU (not_le.2 this)

end LQGMetric.DFGPS
