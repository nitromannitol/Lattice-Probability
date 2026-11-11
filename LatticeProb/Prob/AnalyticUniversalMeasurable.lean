import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Null measurability from compact inner approximation

Let `ν` be a finite Borel measure on a Hausdorff space `X` with its Borel σ-algebra. If the outer measure
`ν A` of a set `A` is approximated from inside by compact subsets, `ν A ≤ ν K + ε` with `K ⊆ A` compact, then
`A` is `ν`-null-measurable. This is the measure-theoretic reduction used for the universal measurability of
analytic sets (Lusin; Kechris, *Classical Descriptive Set Theory*, Thm 21.10, through the capacitability of
analytic sets, Thm 30.13). The compact inner approximation is the input; no property of analytic sets is used here.

Analytic subsets of a metrizable Hausdorff space (continuous images of the Baire space `ℕ → ℕ`) are null-measurable
for every finite Borel measure (Lusin; Kechris, Thm 21.10 and Thm 30.13). The capacitability argument below is
adapted from `SubdiffusiveProcess/Paper/prop_quenched_convergence.lean` (Apache-2.0,
https://github.com/nitromannitol/subdiffusive-process).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LatticeProb

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- A set whose outer measure is approximated from inside by compact subsets is null-measurable for every
finite Borel measure: the compact subsets give a measurable inner set `K` with `ν (A \ K) = 0`. -/
theorem nullMeasurableSet_of_compact_inner (ν : Measure X) [IsFiniteMeasure ν] {A : Set X}
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set X, IsCompact K ∧ K ⊆ A ∧ ν A ≤ ν K + ε) :
    NullMeasurableSet A ν := by
  -- a measurable hull `G ⊇ A` with the same outer measure
  set G : Set X := toMeasurable ν A with hG
  have hGm : MeasurableSet G := measurableSet_toMeasurable ν A
  have hAG : A ⊆ G := subset_toMeasurable ν A
  have hνG : ν G = ν A := measure_toMeasurable A
  -- countably many compact inner approximations, one for each `(n : ℝ≥0∞)⁻¹`
  choose K hKc hKA hKν using fun n : ℕ => h (n : ℝ≥0∞)⁻¹ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n))
  set K' : Set X := ⋃ n, K n with hK'
  have hK'm : MeasurableSet K' :=
    MeasurableSet.iUnion fun n => (hKc n).isClosed.measurableSet
  have hK'A : K' ⊆ A := iUnion_subset fun n => hKA n
  have hK'G : K' ⊆ G := hK'A.trans hAG
  -- `ν A ≤ ν K'` by letting the approximation error go to zero
  have hge : ν A ≤ ν K' := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε' : (ε : ℝ≥0∞) ≠ 0 := by simpa using hε.ne'
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε'
    calc ν A ≤ ν (K n) + (n : ℝ≥0∞)⁻¹ := hKν n
      _ ≤ ν K' + ε := add_le_add (measure_mono (subset_iUnion K n)) hn.le
  -- hence the measurable set `K'` carries all of `A` up to a null set
  have hnull : ν (A \ K') = 0 := by
    have hsub : A \ K' ⊆ G \ K' := sdiff_subset_sdiff_left hAG
    have hfin : ν K' ≠ ∞ := measure_ne_top ν K'
    have hdiff : ν (G \ K') = ν G - ν K' := measure_sdiff hK'G hK'm.nullMeasurableSet hfin
    have hzero : ν (G \ K') = 0 := by
      rw [hdiff, hνG]
      exact tsub_eq_zero_of_le hge
    exact measure_mono_null hsub hzero
  -- `A = K' ∪ (A \ K')` is a union of a measurable set and a null-measurable set
  have hsplit : A = K' ∪ (A \ K') := (union_sdiff_cancel hK'A).symm
  rw [hsplit]
  exact hK'm.nullMeasurableSet.union (NullMeasurableSet.of_null hnull)

/-- One cut of the capacitability construction: restricting the `k`-th coordinate of the parameter to
`≤ b` loses at most `η` of the finite outer measure of the image, for a suitable `b`. -/
theorem analyticImage_cut_step {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : (ℕ → ℕ) → α) (S : Set (ℕ → ℕ)) (k : ℕ)
    {η : ℝ≥0∞} (hη : η ≠ 0) :
    ∃ b : ℕ, μ (f '' S) ≤ μ (f '' (S ∩ {s | s k ≤ b})) + η := by
  have hunion : f '' S = ⋃ b : ℕ, f '' (S ∩ {s | s k ≤ b}) := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact mem_iUnion.2 ⟨s k, s, ⟨hs, (le_rfl : s k ≤ s k)⟩, rfl⟩
    · intro hy
      obtain ⟨b, s, hs, rfl⟩ := mem_iUnion.1 hy
      exact ⟨s, hs.1, rfl⟩
  have hmono : Monotone (fun b : ℕ => f '' (S ∩ {s | s k ≤ b})) := by
    intro b b' hbb'
    exact image_mono (inter_subset_inter_right _ (fun s (hs : s k ≤ b) => le_trans hs hbb'))
  have hsup : μ (f '' S) = ⨆ b : ℕ, μ (f '' (S ∩ {s | s k ≤ b})) := by
    rw [hunion]
    exact hmono.measure_iUnion
  by_contra hcon
  push Not at hcon
  have hfin : μ (f '' S) ≠ ∞ := measure_ne_top μ _
  have hpos : μ (f '' S) ≠ 0 := by
    have := hcon 0
    exact (lt_of_le_of_lt zero_le this).ne'
  have hle : μ (f '' S) ≤ μ (f '' S) - η := by
    conv_lhs => rw [hsup]
    refine iSup_le fun b => ?_
    exact ENNReal.le_sub_of_add_le_right (ne_top_of_le_ne_top hfin
      (le_add_self.trans (hcon b).le)) (hcon b).le
  exact absurd hle (not_le.2 (ENNReal.sub_lt_self hfin hpos hη))

/-- The compactness step of the capacitability argument: a point in the closures of all truncated images
lies in the image of the limiting compact box. -/
theorem analyticImage_closure_box {α : Type*} [TopologicalSpace α] [T2Space α]
    [TopologicalSpace.PseudoMetrizableSpace α] (f : (ℕ → ℕ) → α) (hf : Continuous f)
    (m : ℕ → ℕ) (y : α)
    (hy : ∀ n : ℕ, y ∈ closure (f '' {s : ℕ → ℕ | ∀ i < n, s i ≤ m i})) :
    y ∈ f '' {s : ℕ → ℕ | ∀ i, s i ≤ m i} := by
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric α
  have hchoose : ∀ n : ℕ, ∃ s : ℕ → ℕ, (∀ i < n, s i ≤ m i) ∧
      dist (f s) y < 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 (hy n) _ hpos
    obtain ⟨s, hs, rfl⟩ := hb
    exact ⟨s, hs, by rwa [dist_comm]⟩
  choose s hs hsd using hchoose
  let u : ℕ → ℕ → ℕ := fun n i => min (s n i) (m i)
  have hLc : IsCompact {s : ℕ → ℕ | ∀ i, s i ≤ m i} := by
    have : {s : ℕ → ℕ | ∀ i, s i ≤ m i} = Set.pi univ (fun i => Iic (m i)) := by
      ext s; simp only [mem_ofPred_eq, Set.mem_pi, mem_univ, mem_Iic, true_implies]
    rw [this]
    exact isCompact_univ_pi fun i => (Set.finite_Iic (m i)).isCompact
  have huL : ∀ n, u n ∈ {s : ℕ → ℕ | ∀ i, s i ≤ m i} := fun n i => min_le_right _ _
  obtain ⟨a, haL, φ, hφ, hlim⟩ := hLc.tendsto_subseq huL
  have hslim : Tendsto (fun j => s (φ j)) atTop (𝓝 a) := by
    rw [tendsto_pi_nhds]
    intro i
    have hu_i : Tendsto (fun j => u (φ j) i) atTop (𝓝 (a i)) :=
      ((continuous_apply i).tendsto a).comp hlim
    refine hu_i.congr' ?_
    filter_upwards [eventually_ge_atTop (i + 1)] with j hj
    have hij : i < φ j := lt_of_lt_of_le (Nat.lt_of_succ_le hj) (hφ.id_le j)
    exact min_eq_left (hs (φ j) i hij)
  have hf1 : Tendsto (fun j => f (s (φ j))) atTop (𝓝 (f a)) :=
    (hf.tendsto a).comp hslim
  have hf2 : Tendsto (fun j => f (s (φ j))) atTop (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h0 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_) h0
    refine (hsd (φ j)).le.trans ?_
    have : (j : ℝ) ≤ φ j := by exact_mod_cast hφ.id_le j
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  exact ⟨a, haL, tendsto_nhds_unique hf1 hf2⟩

/-- Inner compact approximation of the image of a continuous map on the Baire space: for every `ε ≠ 0`
there is a compact `L ⊆ range f` with `μ (range f) ≤ μ L + ε` (Lusin; Kechris, Thm 21.10). -/
theorem analyticSet_inner_compact_approximation {α : Type*} [TopologicalSpace α]
    [T2Space α] [TopologicalSpace.PseudoMetrizableSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : (ℕ → ℕ) → α) (hf : Continuous f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ L : Set α, IsCompact L ∧ L ⊆ range f ∧ μ (range f) ≤ μ L + ε := by
  classical
  obtain ⟨ε', hε'pos, hε'sum⟩ := ENNReal.exists_pos_sum_of_countable hε ℕ
  have hstep : ∀ (S : Set (ℕ → ℕ)) (k : ℕ), ∃ b : ℕ,
      μ (f '' S) ≤ μ (f '' (S ∩ {s | s k ≤ b})) + (ε' k : ℝ≥0∞) := fun S k =>
    analyticImage_cut_step μ f S k
      (by exact_mod_cast (hε'pos k).ne')
  choose bsel hbsel using hstep
  let D : ℕ → Set (ℕ → ℕ) := fun n =>
    Nat.rec (motive := fun _ => Set (ℕ → ℕ)) univ
      (fun k Dk => Dk ∩ {s | s k ≤ bsel Dk k}) n
  have hDsucc : ∀ k, D (k + 1) = D k ∩ {s | s k ≤ bsel (D k) k} := fun k => rfl
  let m : ℕ → ℕ := fun i => bsel (D i) i
  have hDeq : ∀ n, D n = {s : ℕ → ℕ | ∀ i < n, s i ≤ m i} := by
    intro n
    induction n with
    | zero => ext s; simp [D]
    | succ k ih =>
      rw [hDsucc, ih]
      ext s
      simp only [mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact h1 i hi
        · simpa [m, ih] using h2
      · intro h
        refine ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), ?_⟩
        have := h k (Nat.lt_succ_self k)
        simpa [m, ih] using this
  have hbound : ∀ n, μ (range f) ≤ μ (f '' D n) + ∑ i ∈ Finset.range n, (ε' i : ℝ≥0∞) := by
    intro n
    induction n with
    | zero => simp [D, image_univ]
    | succ k ih =>
      rw [Finset.sum_range_succ, hDsucc]
      calc μ (range f) ≤ μ (f '' D k) + ∑ i ∈ Finset.range k, (ε' i : ℝ≥0∞) := ih
        _ ≤ (μ (f '' (D k ∩ {s | s k ≤ bsel (D k) k})) + (ε' k : ℝ≥0∞)) +
              ∑ i ∈ Finset.range k, (ε' i : ℝ≥0∞) := by gcongr; exact hbsel (D k) k
        _ = _ := by ring
  have hsum_le : ∀ n, ∑ i ∈ Finset.range n, (ε' i : ℝ≥0∞) ≤ ε := fun n =>
    (ENNReal.sum_le_tsum _).trans hε'sum.le
  let L : Set α := f '' {s : ℕ → ℕ | ∀ i, s i ≤ m i}
  have hLc : IsCompact {s : ℕ → ℕ | ∀ i, s i ≤ m i} := by
    have : {s : ℕ → ℕ | ∀ i, s i ≤ m i} = Set.pi univ (fun i => Iic (m i)) := by
      ext s; simp only [mem_ofPred_eq, Set.mem_pi, mem_univ, mem_Iic, true_implies]
    rw [this]
    exact isCompact_univ_pi fun i => (Set.finite_Iic (m i)).isCompact
  have hLcpt : IsCompact L := hLc.image hf
  refine ⟨L, hLcpt, image_subset_range _ _, ?_⟩
  -- the closures of the truncated images decrease to a subset of `L`
  let C : ℕ → Set α := fun n => closure (f '' D n)
  have hCanti : Antitone C := by
    intro n n' hnn'
    refine closure_mono (image_mono ?_)
    rw [hDeq, hDeq]
    intro s hs i hi
    exact hs i (lt_of_lt_of_le hi hnn')
  have hCsub : (⋂ n, C n) ⊆ L := by
    intro y hy
    refine analyticImage_closure_box f hf m y (fun n => ?_)
    have := mem_iInter.1 hy n
    simpa [C, hDeq n] using this
  have hmeasC : μ (⋂ n, C n) = ⨅ n, μ (C n) :=
    hCanti.measure_iInter (fun n => isClosed_closure.measurableSet.nullMeasurableSet)
      ⟨0, measure_ne_top μ _⟩
  calc μ (range f) ≤ ⨅ n, (μ (C n) + ε) := by
        refine le_iInf fun n => ?_
        calc μ (range f) ≤ μ (f '' D n) + ∑ i ∈ Finset.range n, (ε' i : ℝ≥0∞) := hbound n
          _ ≤ μ (C n) + ε := add_le_add (measure_mono subset_closure) (hsum_le n)
    _ = μ (⋂ n, C n) + ε := by rw [← ENNReal.iInf_add, hmeasC]
    _ ≤ μ L + ε := by gcongr

/-- **Analytic sets are null-measurable.** For every finite measure `μ` on a metrizable Hausdorff space with its
Borel σ-algebra, each analytic subset is `μ`-null-measurable (Lusin; Kechris, *Classical Descriptive Set Theory*,
Thm 21.10, via the capacitability of analytic sets, Thm 30.13). -/
theorem AnalyticSet.nullMeasurableSet {α : Type*} [TopologicalSpace α] [T2Space α]
    [TopologicalSpace.PseudoMetrizableSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {A : Set α} (hA : AnalyticSet A) :
    NullMeasurableSet A μ := by
  rw [AnalyticSet_def] at hA
  rcases hA with rfl | ⟨f, hf, rfl⟩
  · exact nullMeasurableSet_empty
  exact nullMeasurableSet_of_compact_inner μ fun ε hε =>
    analyticSet_inner_compact_approximation μ f hf hε.ne'

end LatticeProb
