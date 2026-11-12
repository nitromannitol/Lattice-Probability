/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_20Tight at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import LatticeProb.Bonanno.LQGMetric.Statement.Metric
import LatticeProb.Bonanno.LQGMetric.Prob.PolishContinuousMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Uniform smallness from tightness (tool for DFGPS Lemma 2.20, T:1325–1330)

DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.20: "Lemma 2.13
… implies that there exists `C > 0` … such that for each `z` and each `r > 0`,
`P[D(∂B_{r/2}(z), ∂B_r(z)) ≥ C^{-1/2} 𝔠_r e^{ξ h_r(z)}] ≥ …`" (T:1325–1327). Lemma 2.13 gives
tightness of the laws of the rescaled metrics and that every Prokhorov limit point is carried by
continuous metrics; the passage to a uniform bound is the standard compactness argument below
(Prokhorov's theorem `isCompact_closure_of_isTightMeasureSet`, metrizability of the weak topology
and the portmanteau inequality for closed sets; own elementary argument, DEVIATIONS DFB12-3):

* `L220.exists_uniform_small_of_tight` — if `S` is tight, `C_k` closed and decreasing, and every
  point of the closure of `S` gives zero mass to `⋂ C_k`, then for each `q > 0` some `C_k` has
  mass `< q` under every element of `S`.
* `L220.exists_uniform_of_lawFamily` — the same for the laws of a family of random variables.
* `L220.exists_inf_lower_of_metricFamily`, `L220.exists_sup_upper_of_metricFamily` — for a family
  of random continuous functions on `ℂ × ℂ` with tight laws whose limit points are carried by
  continuous metrics (the conclusion of Lemma 2.13), `inf_{A×B} d` is uniformly bounded below
  (`A, B` disjoint nonempty compact sets) and `sup_K d` uniformly bounded above, with probability
  `≥ 1 − q`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS.L220

variable {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]

/-- **Uniform smallness from tightness**: a tight family of laws whose Prokhorov limit points do
not charge `⋂ C_k` gives uniformly small mass to `C_k` for `k` large. -/
theorem exists_uniform_small_of_tight {S : Set (ProbabilityMeasure E)}
    (hS : IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ S})
    {Cs : ℕ → Set E} (hC : ∀ k, IsClosed (Cs k)) (hanti : Antitone Cs)
    (hnull : ∀ μ ∈ closure S, (μ : Measure E) (⋂ k, Cs k) = 0) {q : ℝ≥0∞} (hq : 0 < q) :
    ∃ k, ∀ ν ∈ S, (ν : Measure E) (Cs k) < q := by
  by_contra hne
  push Not at hne
  choose ν hνS hνq using hne
  have hcomp := isCompact_closure_of_isTightMeasureSet hS
  obtain ⟨μ, hμ, φ, hφ, hlim⟩ := hcomp.tendsto_subseq fun k => subset_closure (hνS k)
  have hge : ∀ k, q ≤ (μ : Measure E) (Cs k) := by
    intro k
    refine le_trans ?_ (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim (hC k))
    refine le_limsup_of_frequently_le (Eventually.frequently
      (eventually_atTop.2 ⟨k, fun j hj => ?_⟩)) (by isBoundedDefault)
    exact (hνq (φ j)).trans (measure_mono (hanti (hj.trans (hφ.id_le j))))
  have hlimC := tendsto_measure_iInter_atTop (μ := (μ : Measure E))
    (fun k => (hC k).measurableSet.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have : q ≤ (μ : Measure E) (⋂ k, Cs k) := ge_of_tendsto' hlimC hge
  rw [hnull μ hμ] at this
  exact absurd this (not_le.2 hq)

/-- **Uniform smallness for a family of random variables** with tight laws. -/
theorem exists_uniform_of_lawFamily {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : ι → Ω → E) (I : Set ι) (hXm : ∀ i ∈ I, AEMeasurable (X i) P)
    (htight : IsTightMeasureSet {μ | ∃ i, i ∈ I ∧ μ = P.map (X i)})
    {Cs : ℕ → Set E} (hC : ∀ k, IsClosed (Cs k)) (hanti : Antitone Cs)
    (hcl : ∀ μ : ProbabilityMeasure E,
      μ ∈ closure {ν : ProbabilityMeasure E | ∃ i, i ∈ I ∧ (ν : Measure E) = P.map (X i)} →
        (μ : Measure E) (⋂ k, Cs k) = 0) {q : ℝ≥0∞} (hq : 0 < q) :
    ∃ k, ∀ i ∈ I, P (X i ⁻¹' Cs k) < q := by
  set S := {ν : ProbabilityMeasure E | ∃ i, i ∈ I ∧ (ν : Measure E) = P.map (X i)}
  have hS : IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ S} := by
    refine htight.subset ?_
    rintro _ ⟨ν, ⟨i, hi, hν⟩, rfl⟩
    exact ⟨i, hi, hν⟩
  obtain ⟨k, hk⟩ := exists_uniform_small_of_tight hS hC hanti hcl hq
  refine ⟨k, fun i hi => ?_⟩
  have hprob : IsProbabilityMeasure (P.map (X i)) := inferInstance
  have := hk ⟨P.map (X i), hprob⟩ ⟨i, hi, rfl⟩
  rwa [ProbabilityMeasure.coe_mk, Measure.map_apply_of_aemeasurable (hXm i hi)
    (hC k).measurableSet] at this

/-- `d ↦ inf_{p ∈ K} d(p)` is continuous on `C(ℂ × ℂ, ℝ)` for compact `K` -/
lemma continuous_infOn {K : Set (ℂ × ℂ)} (hK : IsCompact K) :
    Continuous fun d : C(ℂ × ℂ, ℝ) => sInf ((fun p => d p) '' K) :=
  hK.continuous_sInf (f := fun (d : C(ℂ × ℂ, ℝ)) (p : ℂ × ℂ) => d p) continuous_eval

/-- `d ↦ sup_{p ∈ K} d(p)` is continuous on `C(ℂ × ℂ, ℝ)` for compact `K` -/
lemma continuous_supOn {K : Set (ℂ × ℂ)} (hK : IsCompact K) :
    Continuous fun d : C(ℂ × ℂ, ℝ) => sSup ((fun p => d p) '' K) :=
  hK.continuous_sSup (f := fun (d : C(ℂ × ℂ, ℝ)) (p : ℂ × ℂ) => d p) continuous_eval

/-- a continuous metric is positive on `A × B` for disjoint nonempty compact `A`, `B` -/
lemma infOn_pos {d : C(ℂ × ℂ, ℝ)} (hd : IsContinuousMetric d) {A B : Set ℂ} (hA : IsCompact A)
    (hB : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty) (hAB : Disjoint A B) :
    0 < sInf ((fun p => d p) '' (A ×ˢ B)) := by
  have hK : IsCompact (A ×ˢ B) := hA.prod hB
  obtain ⟨⟨u, v⟩, hp, hmin⟩ := hK.exists_isMinOn (hAne.prod hBne) d.continuous.continuousOn
  have hinf : sInf ((fun p => d p) '' (A ×ˢ B)) = d (u, v) := by
    refine le_antisymm (csInf_le ⟨d (u, v), ?_⟩ ⟨(u, v), hp, rfl⟩)
      (le_csInf ⟨d (u, v), (u, v), hp, rfl⟩ ?_)
    · rintro _ ⟨x, hx, rfl⟩; exact hmin hx
    · rintro _ ⟨x, hx, rfl⟩; exact hmin hx
  rw [hinf]
  have hne : u ≠ v := fun he => Set.disjoint_left.1 hAB hp.1 (he ▸ hp.2)
  have h0 : 0 ≤ d (u, v) := by
    have := hd.toIsMetricFn.triangle u v u
    rw [hd.toIsMetricFn.self_eq_zero, hd.toIsMetricFn.symm v u] at this
    linarith
  exact lt_of_le_of_ne h0 fun h => hne (hd.toIsMetricFn.eq_of_eq_zero u v h.symm)

/-- **Uniform lower bound** (first display of T:1325–1330, scale-free form): for a family of random
continuous functions with tight laws whose limit points are carried by continuous metrics, and
disjoint nonempty compact `A`, `B`, for each `q > 0` there is `a > 0` with
`P[inf_{A×B} X_i ≤ a] < q` for all `i`. -/
theorem exists_inf_lower_of_metricFamily {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : ι → Ω → C(ℂ × ℂ, ℝ)) (I : Set ι)
    (hXm : ∀ i ∈ I, AEMeasurable (X i) P)
    (htight : IsTightMeasureSet {μ | ∃ i, i ∈ I ∧ μ = P.map (X i)})
    (hcl : ∀ μ : ProbabilityMeasure C(ℂ × ℂ, ℝ),
      μ ∈ closure {ν : ProbabilityMeasure C(ℂ × ℂ, ℝ) |
        ∃ i, i ∈ I ∧ (ν : Measure C(ℂ × ℂ, ℝ)) = P.map (X i)} →
        ∀ᵐ d ∂(μ : Measure C(ℂ × ℂ, ℝ)), IsContinuousMetric d)
    {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : Disjoint A B) {q : ℝ≥0∞} (hq : 0 < q) :
    ∃ a : ℝ, 0 < a ∧ ∀ i ∈ I,
      P {ω | sInf ((fun p => X i ω p) '' (A ×ˢ B)) ≤ a} < q := by
  set m := fun d : C(ℂ × ℂ, ℝ) => sInf ((fun p => d p) '' (A ×ˢ B))
  have hm : Continuous m := continuous_infOn (hA.prod hB)
  set Cs : ℕ → Set C(ℂ × ℂ, ℝ) := fun k => {d | m d ≤ 1 / ((k : ℝ) + 1)}
  have hC : ∀ k, IsClosed (Cs k) := fun k => isClosed_le hm continuous_const
  have hanti : Antitone Cs := fun k l hkl d (hd : m d ≤ 1 / ((l : ℝ) + 1)) =>
    show m d ≤ 1 / ((k : ℝ) + 1) from hd.trans (by gcongr)
  obtain ⟨k, hk⟩ := exists_uniform_of_lawFamily X I hXm htight hC hanti (fun μ hμ => by
    refine measure_mono_null (fun d hd => ?_) (ae_iff.1 (hcl μ hμ))
    intro hdm
    have hpos := infOn_pos hdm hA hB hAne hBne hAB
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    exact absurd (mem_iInter.1 hd n) (not_le.2 hn)) hq
  exact ⟨1 / ((k : ℝ) + 1), by positivity, hk⟩

/-- **Uniform modulus near the diagonal**: in the setting of `exists_inf_lower_of_metricFamily`,
for compact `L` and `s > 0` there is `b > 0` with `P[sup_{u,v ∈ L, |u−v| ≤ b} X_i(u,v) ≥ s] < q`
for all `i`. -/
theorem exists_modulus_of_metricFamily {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : ι → Ω → C(ℂ × ℂ, ℝ)) (I : Set ι)
    (hXm : ∀ i ∈ I, AEMeasurable (X i) P)
    (htight : IsTightMeasureSet {μ | ∃ i, i ∈ I ∧ μ = P.map (X i)})
    (hcl : ∀ μ : ProbabilityMeasure C(ℂ × ℂ, ℝ),
      μ ∈ closure {ν : ProbabilityMeasure C(ℂ × ℂ, ℝ) |
        ∃ i, i ∈ I ∧ (ν : Measure C(ℂ × ℂ, ℝ)) = P.map (X i)} →
        ∀ᵐ d ∂(μ : Measure C(ℂ × ℂ, ℝ)), IsContinuousMetric d)
    {L : Set ℂ} (hL : IsCompact L) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 0 < q) :
    ∃ b : ℝ, 0 < b ∧ ∀ i ∈ I, P {ω | s ≤ sSup ((fun p => X i ω p) ''
      {p : ℂ × ℂ | p ∈ L ×ˢ L ∧ ‖p.1 - p.2‖ ≤ b})} < q := by
  set Kk : ℕ → Set (ℂ × ℂ) := fun k => {p | p ∈ L ×ˢ L ∧ ‖p.1 - p.2‖ ≤ 1 / ((k : ℝ) + 1)}
  have hK : ∀ k, IsCompact (Kk k) := fun k => (hL.prod hL).inter_right
    (isClosed_le (continuous_fst.sub continuous_snd).norm continuous_const)
  set Cs : ℕ → Set C(ℂ × ℂ, ℝ) := fun k => {d | s ≤ sSup ((fun p => d p) '' Kk k)}
  have hC : ∀ k, IsClosed (Cs k) := fun k => isClosed_le continuous_const (continuous_supOn (hK k))
  have hne : ∀ k (d : C(ℂ × ℂ, ℝ)), d ∈ Cs k → (Kk k).Nonempty := fun k d hd => by
    by_contra h0
    rw [not_nonempty_iff_eq_empty] at h0
    have hd' : s ≤ sSup ((fun p => d p) '' Kk k) := hd
    rw [h0, image_empty, Real.sSup_empty] at hd'
    linarith
  have hanti : Antitone Cs := fun k l hkl d hd => by
    have hd' : s ≤ sSup ((fun p => d p) '' Kk l) := hd
    show s ≤ sSup ((fun p => d p) '' Kk k)
    refine hd'.trans (csSup_le_csSup ((hK k).image_of_continuousOn
      d.continuous.continuousOn).bddAbove ((hne l d hd).image _) (image_mono ?_))
    rintro p ⟨hp1, hp2⟩
    refine ⟨hp1, hp2.trans ?_⟩
    gcongr
  obtain ⟨k, hk⟩ := exists_uniform_of_lawFamily X I hXm htight hC hanti (fun μ hμ => by
    refine measure_mono_null (fun d hd => ?_) (ae_iff.1 (hcl μ hμ))
    intro hdm
    obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1
      ((hL.prod hL).uniformContinuousOn_of_continuous d.continuous.continuousOn) s hs
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    have hdn : d ∈ Cs n := mem_iInter.1 hd n
    have hsup := ((hK n).image_of_continuousOn d.continuous.continuousOn).sSup_mem
      ((hne n d hdn).image _)
    obtain ⟨⟨u, v⟩, ⟨huv, hb⟩, he⟩ := hsup
    have hdn' : s ≤ sSup ((fun p => d p) '' Kk n) := hdn
    rw [← he] at hdn'
    have hdist : dist ((u, v) : ℂ × ℂ) (u, u) < δ := by
      rw [Prod.dist_eq, dist_self, dist_eq_norm]
      have hb' : ‖v - u‖ ≤ 1 / ((n : ℝ) + 1) := by rw [norm_sub_rev]; exact hb
      exact (max_le (le_of_lt (by positivity)) hb').trans_lt hn
    have := hδu (u, v) huv (u, u) ⟨huv.1, huv.1⟩ hdist
    rw [Real.dist_eq, hdm.toIsMetricFn.self_eq_zero, sub_zero] at this
    exact absurd ((abs_lt.1 this).2) (not_lt.2 hdn')) hq
  exact ⟨1 / ((k : ℝ) + 1), by positivity, hk⟩

end LQGMetric.DFGPS.L220
