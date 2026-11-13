/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.PathSpace at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Order.SetAccumulate
import Mathlib.Data.Set.SymmDiff
import Mathlib.Logic.Equiv.List

/-!
# The path space `L¹_loc([0,∞), S)` (Gwynne–Sung, Definition 3.9)

Let `S` be a countable set with the discrete topology.  `L¹_loc([0,∞), S)` is the metric
space of Lebesgue measurable `f : [0,∞) → S`, functions identified if they agree
Lebesgue-a.e., with

  `d(f,g) := ∫₀^∞ e^{-t} 1_{f(t) ≠ g(t)} dt`.                                    (3.30)

## Representation

`L1loc S` is `MeasureTheory.AEEqFun` (a.e.-classes of a.e.-strongly-measurable functions)
from `ℝ` to `S` with respect to the finite measure `expMeasure := e^{-t} dt` on `(0,∞)`,
where `S` carries the **discrete** topology and σ-algebra.  These are hard-coded through
the type synonym `DiscreteOf S`; the definition takes no topological or measurable
structure on `S` as input.  (For a non-discrete σ-algebra on `S` the space would not be
separable: for the trivial σ-algebra on a two-point `S` one gets uncountably many classes
pairwise at distance `1`.)

The extended distance is `edist f g = expMeasure {t | f t ≠ g t}`, i.e. the paper's
integral (3.30); see `L1loc.dist_eq` for the integral formula.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal symmDiff

universe u

namespace ReflectedWalk

/-! ### The discrete structure on `S` -/

/-- `S` with the discrete topology and the discrete σ-algebra. -/
def DiscreteOf (S : Type u) : Type u := S

namespace DiscreteOf

variable {S : Type u}

instance : TopologicalSpace (DiscreteOf S) := ⊥
instance : DiscreteTopology (DiscreteOf S) := discreteTopology_bot _
instance : MeasurableSpace (DiscreteOf S) := ⊤
instance : DiscreteMeasurableSpace (DiscreteOf S) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
instance [Countable S] : Countable (DiscreteOf S) := ‹Countable S›
instance [Nonempty S] : Nonempty (DiscreteOf S) := ‹Nonempty S›

end DiscreteOf

/-! ### The reference measure `e^{-t} dt` on `(0,∞)` -/

/-- The finite measure `e^{-t} dt` on `(0, ∞)`, as a measure on `ℝ`. -/
noncomputable def expMeasure : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity fun t => ENNReal.ofReal (Real.exp (-t))

lemma expMeasure_apply {A : Set ℝ} (hA : MeasurableSet A) :
    expMeasure A = ∫⁻ t in A ∩ Ioi 0, ENNReal.ofReal (Real.exp (-t)) := by
  rw [expMeasure, withDensity_apply _ hA, Measure.restrict_restrict hA]

lemma lintegral_ofReal_exp_neg_Ioi :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
    (ae_of_all _ fun t => (Real.exp_pos _).le), integral_exp_neg_Ioi_zero, ENNReal.ofReal_one]

instance instIsFiniteMeasureExpMeasure : IsFiniteMeasure expMeasure :=
  isFiniteMeasure_withDensity (by rw [lintegral_ofReal_exp_neg_Ioi]; exact ENNReal.one_ne_top)

lemma expMeasure_univ : expMeasure univ = 1 := by
  rw [expMeasure_apply MeasurableSet.univ, univ_inter, lintegral_ofReal_exp_neg_Ioi]

/-- `expMeasure`-a.e. is the same as Lebesgue-a.e. on `(0,∞)` (the density is positive). -/
lemma ae_expMeasure_iff {p : ℝ → Prop} :
    (∀ᵐ t ∂expMeasure, p t) ↔ ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), p t := by
  unfold expMeasure
  rw [ae_withDensity_iff (f := fun t => ENNReal.ofReal (Real.exp (-t)))
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_neg))]
  exact ⟨fun h => h.mono fun t ht => ht (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne',
    fun h => h.mono fun t ht _ => ht⟩

/-- The measure of a measurable set, in the paper's integral form. -/
lemma toReal_expMeasure_eq_integral {A : Set ℝ} (hA : MeasurableSet A) :
    (expMeasure A).toReal = ∫ t in Ioi (0 : ℝ), Real.exp (-t) * A.indicator 1 t := by
  have h1 : ∀ t, Real.exp (-t) * A.indicator 1 t = A.indicator (fun t => Real.exp (-t)) t := by
    intro t; by_cases ht : t ∈ A <;> simp [Set.indicator, ht]
  simp_rw [h1]
  rw [integral_indicator hA, Measure.restrict_restrict hA, expMeasure_apply hA,
    integral_eq_lintegral_of_nonneg_ae (f := fun t => Real.exp (-t))
      (ae_of_all _ fun t => (Real.exp_pos _).le) (by fun_prop)]

/-! ### The space -/

/-- **Definition 3.9.**  Lebesgue measurable `f : [0,∞) → S` for countable discrete `S`,
identified when they agree Lebesgue-a.e., metrized by
`d(f,g) = ∫₀^∞ e^{-t} 1_{f t ≠ g t} dt`.  Realized as a.e.-classes of strongly
measurable functions `ℝ → S` (discrete `S`) for the finite measure `expMeasure`. -/
def L1loc (S : Type u) : Type u := ℝ →ₘ[expMeasure] DiscreteOf S

namespace L1loc

variable {S : Type u}

/-- The canonical (strongly measurable) representative of a class. -/
noncomputable instance instCoeFun : CoeFun (L1loc S) fun _ => ℝ → S :=
  ⟨fun f => AEEqFun.cast (α := ℝ) (β := DiscreteOf S) (μ := expMeasure) f⟩

lemma measurable_coe (f : L1loc S) : Measurable (⇑f : ℝ → DiscreteOf S) :=
  AEEqFun.measurable (α := ℝ) (β := DiscreteOf S) (μ := expMeasure) f

lemma aestronglyMeasurable_coe (f : L1loc S) :
    AEStronglyMeasurable (⇑f : ℝ → DiscreteOf S) expMeasure :=
  AEEqFun.aestronglyMeasurable (α := ℝ) (β := DiscreteOf S) (μ := expMeasure) f

lemma measurableSet_preimage_singleton (f : L1loc S) (s : S) : MeasurableSet (⇑f ⁻¹' {s}) :=
  f.measurable_coe MeasurableSet.of_discrete

/-- Two classes are equal iff their representatives agree `expMeasure`-a.e. -/
lemma ext {f g : L1loc S} (h : ∀ᵐ t ∂expMeasure, f t = g t) : f = g :=
  AEEqFun.ext (α := ℝ) (β := DiscreteOf S) (μ := expMeasure) h

/-! #### The metric -/

noncomputable instance instEMetricSpace : EMetricSpace (L1loc S) where
  edist f g := expMeasure {t | f t ≠ g t}
  edist_self f := by simp
  edist_comm f g := by
    congr 1
    ext t
    exact ne_comm
  edist_triangle f g h := by
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro t ht
    by_contra hc
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hc
    exact ht (hc.1.trans hc.2)
  eq_of_edist_eq_zero {f g} h := ext ((ae_iff (p := fun t => f t = g t)).2 h)

lemma edist_def (f g : L1loc S) : edist f g = expMeasure {t | f t ≠ g t} := rfl

lemma edist_ne_top' (f g : L1loc S) : edist f g ≠ ∞ := measure_ne_top _ _

/-- The metric of Definition 3.9. -/
noncomputable instance instMetricSpace : MetricSpace (L1loc S) :=
  EMetricSpace.toMetricSpace edist_ne_top'

lemma dist_def (f g : L1loc S) : dist f g = (expMeasure {t | f t ≠ g t}).toReal := rfl

/-! #### Fiber-measurable functions and their classes -/

/-- `{t | f t ≠ g t}` is measurable whenever `f` and `g` have measurable fibers. -/
lemma measurableSet_ne_of_fibers [Countable S] {f g : ℝ → S}
    (hf : ∀ s, MeasurableSet (f ⁻¹' {s})) (hg : ∀ s, MeasurableSet (g ⁻¹' {s})) :
    MeasurableSet {t | f t ≠ g t} := by
  have : {t | f t ≠ g t} = (⋃ s : S, (f ⁻¹' {s}) ∩ (g ⁻¹' {s}))ᶜ := by
    ext t
    simp only [mem_ofPred_eq, mem_compl_iff, mem_iUnion, mem_inter_iff, mem_preimage,
      mem_singleton_iff, not_exists, not_and]
    exact ⟨fun h s hfs hgs => h (hfs.trans hgs.symm), fun h hfg => h (f t) rfl hfg.symm⟩
  rw [this]
  exact (MeasurableSet.iUnion fun s => (hf s).inter (hg s)).compl

lemma measurableSet_ne [Countable S] (f g : L1loc S) : MeasurableSet {t | f t ≠ g t} :=
  measurableSet_ne_of_fibers f.measurableSet_preimage_singleton g.measurableSet_preimage_singleton

lemma measurable_of_fibers [Countable S] (f : ℝ → S) (hf : ∀ s, MeasurableSet (f ⁻¹' {s})) :
    @Measurable ℝ (DiscreteOf S) _ _ f :=
  @measurable_to_countable' (DiscreteOf S) ℝ _ _ _ f hf

/-- The class of a function `f : ℝ → S` all of whose fibers are Lebesgue measurable
(for countable `S` this is exactly Lebesgue measurability of `f` into discrete `S`).
Only the values on `(0,∞)` matter. -/
noncomputable def mk [Countable S] (f : ℝ → S) (hf : ∀ s, MeasurableSet (f ⁻¹' {s})) :
    L1loc S :=
  AEEqFun.mk (α := ℝ) (β := DiscreteOf S) (μ := expMeasure) f
    (measurable_of_fibers f hf).stronglyMeasurable.aestronglyMeasurable

lemma coeFn_mk [Countable S] (f : ℝ → S) (hf : ∀ s, MeasurableSet (f ⁻¹' {s})) :
    ∀ᵐ t ∂expMeasure, (mk f hf) t = f t :=
  AEEqFun.coeFn_mk (α := ℝ) (β := DiscreteOf S) (μ := expMeasure) f _

/-- Two fiber-measurable functions have the same class iff they agree Lebesgue-a.e. on
`(0,∞)`. -/
lemma mk_eq_mk_iff [Countable S] {f g : ℝ → S} {hf : ∀ s, MeasurableSet (f ⁻¹' {s})}
    {hg : ∀ s, MeasurableSet (g ⁻¹' {s})} :
    mk f hf = mk g hg ↔ ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), f t = g t := by
  rw [← ae_expMeasure_iff]
  exact AEEqFun.mk_eq_mk (α := ℝ) (β := DiscreteOf S) (μ := expMeasure)

lemma mk_coeFn (f : L1loc S) (hf : ∀ s, MeasurableSet (⇑f ⁻¹' {s})) [Countable S] :
    mk (⇑f) hf = f :=
  AEEqFun.mk_coeFn (α := ℝ) (β := DiscreteOf S) (μ := expMeasure) f

lemma edist_mk_mk [Countable S] (f g : ℝ → S) (hf : ∀ s, MeasurableSet (f ⁻¹' {s}))
    (hg : ∀ s, MeasurableSet (g ⁻¹' {s})) :
    edist (mk f hf) (mk g hg) = expMeasure {t | f t ≠ g t} := by
  rw [edist_def]
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [coeFn_mk f hf, coeFn_mk g hg] with t h1 h2
  simp only [h1, h2]
  exact Iff.rfl

lemma edist_mk_right [Countable S] (f : L1loc S) (g : ℝ → S)
    (hg : ∀ s, MeasurableSet (g ⁻¹' {s})) :
    edist f (mk g hg) = expMeasure {t | f t ≠ g t} := by
  rw [edist_def]
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [coeFn_mk g hg] with t h
  simp only [h]

/-- **The distance formula (3.30)** for classes of fiber-measurable functions:
`dist (mk f) (mk g) = ∫₀^∞ e^{-t} 1_{f t ≠ g t} dt`. -/
theorem dist_mk_mk [Countable S] (f g : ℝ → S) (hf : ∀ s, MeasurableSet (f ⁻¹' {s}))
    (hg : ∀ s, MeasurableSet (g ⁻¹' {s})) :
    dist (mk f hf) (mk g hg) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-t) * ({t | f t ≠ g t} : Set ℝ).indicator 1 t := by
  rw [dist_edist, edist_mk_mk, toReal_expMeasure_eq_integral (measurableSet_ne_of_fibers hf hg)]

/-- **The distance formula (3.30)** on canonical representatives:
`dist f g = ∫₀^∞ e^{-t} 1_{f t ≠ g t} dt`. -/
theorem dist_eq [Countable S] (f g : L1loc S) :
    dist f g = ∫ t in Ioi (0 : ℝ), Real.exp (-t) * ({t | f t ≠ g t} : Set ℝ).indicator 1 t := by
  rw [dist_def, toReal_expMeasure_eq_integral (measurableSet_ne f g)]

/-! #### Completeness -/

section Complete

variable [Countable S]

/-- **Completeness** (Definition 3.9).  For a Cauchy sequence `u` with
`dist (u n) (u (n+1)) < 2⁻¹ ^ n`, the sets `A n = {u n ≠ u (n+1)}` have summable measure, so
by Borel–Cantelli `n ↦ u n t` is eventually constant for a.e. `t`; the a.e. limit `g` is
strongly measurable and `{u n ≠ g} ⊆ ⋃ m, A (n + m)` up to a null set, whose measure is at
most `2 · 2⁻¹ ^ n → 0`. -/
instance instCompleteSpace : CompleteSpace (L1loc S) := by
  refine Metric.complete_of_convergent_controlled_sequences (fun n => (2⁻¹ : ℝ) ^ n)
    (fun n => by positivity) fun u hu => ?_
  -- the sets where consecutive terms differ
  set A : ℕ → Set ℝ := fun n => {t | u n t ≠ u (n + 1) t} with hA
  have hA_le : ∀ n, expMeasure (A n) ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    have h : dist (u n) (u (n + 1)) < (2⁻¹ : ℝ) ^ n := hu n n (n + 1) le_rfl (Nat.le_succ n)
    rw [← edist_lt_ofReal, edist_def] at h
    refine h.le.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  have htail : ∀ n, expMeasure (⋃ m, A (n + m)) ≤ (2⁻¹ : ℝ≥0∞) ^ n * 2 := by
    intro n
    calc expMeasure (⋃ m, A (n + m)) ≤ ∑' m, expMeasure (A (n + m)) := measure_iUnion_le _
      _ ≤ ∑' m, (2⁻¹ : ℝ≥0∞) ^ (n + m) := ENNReal.tsum_le_tsum fun m => hA_le (n + m)
      _ = (2⁻¹ : ℝ≥0∞) ^ n * 2 := by
        simp_rw [pow_add]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
  have hsum : ∑' n, expMeasure (A n) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hA_le)
    rw [ENNReal.tsum_geometric_two]
    exact ENNReal.ofNat_ne_top
  -- a.e., the sequence `n ↦ u n t` is eventually constant (Borel–Cantelli)
  have hae : ∀ᵐ t ∂expMeasure, ∃ l : DiscreteOf S, Tendsto (fun n => u n t) atTop (𝓝 l) := by
    filter_upwards [ae_eventually_notMem hsum] with t ht
    obtain ⟨N, hN⟩ := eventually_atTop.1 ht
    refine ⟨u N t, ?_⟩
    rw [nhds_discrete, tendsto_pure, eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      have h := hN n hn
      simp only [hA, mem_ofPred_eq, ne_eq, not_not] at h
      exact h.symm.trans ih
  -- the a.e. limit, as a strongly measurable function
  obtain ⟨g, hg_meas, hg_lim⟩ := exists_stronglyMeasurable_limit_of_tendsto_ae (μ := expMeasure)
    (f := fun n => (⇑(u n) : ℝ → DiscreteOf S)) (fun n => (u n).aestronglyMeasurable_coe) hae
  let G : L1loc S :=
    AEEqFun.mk (α := ℝ) (β := DiscreteOf S) (μ := expMeasure) g hg_meas.aestronglyMeasurable
  have hG : ∀ᵐ t ∂expMeasure, G t = g t :=
    AEEqFun.coeFn_mk (α := ℝ) (β := DiscreteOf S) (μ := expMeasure) g _
  refine ⟨G, ?_⟩
  rw [tendsto_iff_edist_tendsto_0]
  have hlim : Tendsto (fun n : ℕ => (2⁻¹ : ℝ≥0∞) ^ n * 2) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)) (Or.inr (ENNReal.ofNat_ne_top (n := 2)))
    rwa [zero_mul] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le)
    fun n => ?_
  show edist (u n) G ≤ (2⁻¹ : ℝ≥0∞) ^ n * 2
  rw [edist_def]
  have hnull : expMeasure ({t | G t ≠ g t} ∪ {t | ¬ ∀ᶠ m in atTop, u m t = g t}) = 0 := by
    refine measure_union_null (ae_iff.1 hG) (ae_iff.1 ?_)
    filter_upwards [hg_lim] with t ht
    rw [nhds_discrete, tendsto_pure] at ht
    exact ht
  calc expMeasure {t | u n t ≠ G t}
      ≤ expMeasure (({t | G t ≠ g t} ∪ {t | ¬ ∀ᶠ m in atTop, u m t = g t}) ∪
          ⋃ m, A (n + m)) := by
        apply measure_mono
        intro t ht
        have ht' : u n t ≠ G t := ht
        by_contra hc
        simp only [mem_union, mem_iUnion, mem_ofPred_eq, ne_eq, not_or, not_exists, not_not] at hc
        obtain ⟨⟨h1, h2⟩, h3⟩ := hc
        have hconst : ∀ m, u (n + m) t = u n t := by
          intro m
          induction m with
          | zero => rfl
          | succ m ih =>
            have h := h3 m
            simp only [hA, mem_ofPred_eq, ne_eq, not_not] at h
            exact h.symm.trans ih
        obtain ⟨M, hM⟩ := eventually_atTop.1 h2
        exact ht' ((hconst M).symm.trans ((hM (n + M) (Nat.le_add_left M n)).trans h1.symm))
    _ ≤ expMeasure ({t | G t ≠ g t} ∪ {t | ¬ ∀ᶠ m in atTop, u m t = g t}) +
          expMeasure (⋃ m, A (n + m)) := measure_union_le _ _
    _ = expMeasure (⋃ m, A (n + m)) := by rw [hnull, zero_add]
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ n * 2 := htail n

end Complete

/-! #### Separability -/

section Separable

/-- A finite union of open intervals with rational endpoints. -/
abbrev ratUnion (L : List (ℚ × ℚ)) : Set ℝ := ⋃ p ∈ L, Ioo (p.1 : ℝ) p.2

lemma measurableSet_ratUnion (L : List (ℚ × ℚ)) : MeasurableSet (ratUnion L) :=
  MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => measurableSet_Ioo

open scoped Classical in
/-- The step function taking the value `e.2` on `ratUnion e.1` for the first entry `e` of the
list whose interval-union contains the point, and the value `d` elsewhere. -/
noncomputable def stepFn : List (List (ℚ × ℚ) × S) → S → ℝ → S
  | [], d, _ => d
  | e :: L, d, t => if t ∈ ratUnion e.1 then e.2 else stepFn L d t

lemma measurableSet_stepFn_preimage (L : List (List (ℚ × ℚ) × S)) (d s : S) :
    MeasurableSet (stepFn L d ⁻¹' {s}) := by
  induction L with
  | nil =>
    by_cases h : d = s
    · have : stepFn [] d ⁻¹' {s} = univ := by ext t; simp [stepFn, h]
      rw [this]; exact MeasurableSet.univ
    · have : stepFn [] d ⁻¹' {s} = ∅ := by ext t; simp [stepFn, h]
      rw [this]; exact MeasurableSet.empty
  | cons e L ih =>
    have : stepFn (e :: L) d ⁻¹' {s} =
        (ratUnion e.1 ∩ {t : ℝ | e.2 = s}) ∪ ((ratUnion e.1)ᶜ ∩ stepFn L d ⁻¹' {s}) := by
      ext t
      simp only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_ofPred_eq,
        mem_compl_iff, stepFn]
      split_ifs with ht <;> simp [ht]
    rw [this]
    have h2 : MeasurableSet {t : ℝ | e.2 = s} := by
      by_cases h : e.2 = s
      · have : {t : ℝ | e.2 = s} = univ := by ext; simp [h]
        rw [this]; exact MeasurableSet.univ
      · have : {t : ℝ | e.2 = s} = ∅ := by ext; simp [h]
        rw [this]; exact MeasurableSet.empty
    exact ((measurableSet_ratUnion _).inter h2).union ((measurableSet_ratUnion _).compl.inter ih)

/-- If every entry whose interval-union contains `t` carries the value `v`, and some entry
does contain `t`, then the step function takes the value `v` at `t`. -/
lemma stepFn_eq (L : List (List (ℚ × ℚ) × S)) (d : S) (t : ℝ) (v : S)
    (h1 : ∀ e ∈ L, t ∈ ratUnion e.1 → e.2 = v) (h2 : ∃ e ∈ L, t ∈ ratUnion e.1) :
    stepFn L d t = v := by
  induction L with
  | nil =>
    obtain ⟨e, he, -⟩ := h2
    simp at he
  | cons e L ih =>
    simp only [stepFn]
    split_ifs with ht
    · exact h1 e (List.mem_cons.2 (Or.inl rfl)) ht
    · refine ih (fun e' he' ht' => h1 e' (List.mem_cons.2 (Or.inr he')) ht') ?_
      obtain ⟨e', he', ht'⟩ := h2
      rcases List.mem_cons.1 he' with rfl | he'
      · exact absurd ht' ht
      · exact ⟨e', he', ht'⟩

/-- Every measurable set is approximated in `expMeasure` by a finite union of rational open
intervals: outer regularity of the finite measure `expMeasure` gives an open superset, which is
a countable union of rational intervals, and continuity from below truncates it. -/
lemma exists_ratUnion_approx (E : Set ℝ) (hE : MeasurableSet E) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ L : List (ℚ × ℚ), expMeasure (E ∆ ratUnion L) < δ := by
  classical
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  -- Step 1: an open `U ⊇ E` with `expMeasure (U \ E) < δ / 2`.
  obtain ⟨U, hEU, hUo, hU⟩ := Set.exists_isOpen_lt_of_lt E (expMeasure E + δ / 2)
    (ENNReal.lt_add_right (measure_ne_top _ _) hδ2.ne')
  have hUE : expMeasure (U \ E) < δ / 2 := by
    have h := measure_union_add_inter (μ := expMeasure) (U \ E) hE
    have h1 : (U \ E) ∪ E = U := by
      ext t
      constructor
      · rintro (⟨htU, -⟩ | htE)
        · exact htU
        · exact hEU htE
      · intro htU
        by_cases htE : t ∈ E
        · exact Or.inr htE
        · exact Or.inl ⟨htU, htE⟩
    have h2 : (U \ E) ∩ E = ∅ := by
      ext t
      simp only [mem_inter_iff, Set.mem_sdiff, mem_empty_iff_false, iff_false, not_and]
      exact fun h => h.2
    rw [h1, h2, measure_empty, add_zero] at h
    rw [h, add_comm (expMeasure (U \ E))] at hU
    exact (ENNReal.add_lt_add_iff_left (measure_ne_top _ _)).1 hU
  -- Step 2: `U` is a countable union of rational open intervals.
  obtain ⟨q, hq1, hq2⟩ : ∃ q : ℚ × ℚ → ℚ × ℚ, (∀ p, Ioo ((q p).1 : ℝ) (q p).2 ⊆ U) ∧
      ∀ p, Ioo (p.1 : ℝ) p.2 ⊆ U → q p = p :=
    ⟨fun p => if Ioo (p.1 : ℝ) p.2 ⊆ U then p else (p.1, p.1), fun p => by
      dsimp only
      split_ifs with h
      · exact h
      · simp, fun p hp => by simp [hp]⟩
  have hU_eq : U = ⋃ p, Ioo ((q p).1 : ℝ) (q p).2 := by
    refine Subset.antisymm (fun x hx => ?_) (iUnion_subset hq1)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUo x hx
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (sub_lt_self x hε)
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (lt_add_of_pos_right x hε)
    have hsub : Ioo (a : ℝ) b ⊆ U := fun y hy =>
      hball (by rw [Real.ball_eq_Ioo]; exact ⟨ha1.trans hy.1, hy.2.trans hb2⟩)
    refine mem_iUnion.2 ⟨(a, b), ?_⟩
    rw [hq2 (a, b) hsub]
    exact ⟨ha2, hb1⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (ℚ × ℚ)
  obtain ⟨s, hs⟩ : ∃ s : ℕ → Set ℝ, ∀ n, s n = Ioo ((q (e n)).1 : ℝ) (q (e n)).2 :=
    ⟨_, fun n => rfl⟩
  have hUs : U = ⋃ n, s n := by
    rw [hU_eq]
    ext x
    simp only [mem_iUnion, hs]
    exact ⟨fun ⟨p, hp⟩ => by obtain ⟨n, rfl⟩ := he p; exact ⟨n, hp⟩, fun ⟨n, hn⟩ => ⟨e n, hn⟩⟩
  have hs_meas : ∀ n, MeasurableSet (s n) := fun n => by rw [hs]; exact measurableSet_Ioo
  have hV_meas : ∀ n, MeasurableSet (accumulate s n) := fun n => by
    rw [accumulate_def]
    exact MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ => hs_meas m
  have hV_sub : ∀ n, accumulate s n ⊆ U := fun n =>
    (accumulate_subset_iUnion n).trans hUs.symm.subset
  -- Step 3: `expMeasure (U \ accumulate s n) → 0`, so some `n` has it `< δ / 2`.
  have hD_anti : Antitone fun n => U \ accumulate s n := fun m n hmn t ht =>
    ⟨ht.1, fun h => ht.2 (monotone_accumulate hmn h)⟩
  have hD_inter : ⋂ n, U \ accumulate s n = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun t ht => ?_
    rw [mem_iInter] at ht
    have htU : t ∈ U := (ht 0).1
    rw [hUs] at htU
    obtain ⟨m, hm⟩ := mem_iUnion.1 htU
    exact (ht m).2 (subset_accumulate hm)
  have hD_tendsto : Tendsto (fun n => expMeasure (U \ accumulate s n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := expMeasure) (s := fun n => U \ accumulate s n)
      (fun n => (hUo.measurableSet.diff (hV_meas n)).nullMeasurableSet) hD_anti
      ⟨0, measure_ne_top _ _⟩
    rw [hD_inter, measure_empty] at h
    exact h
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hD_tendsto).2 (δ / 2) hδ2).exists
  -- Step 4: the finite union `accumulate s n` is a `ratUnion`, and it approximates `E`.
  refine ⟨(List.range (n + 1)).map fun m => q (e m), ?_⟩
  have hL : ratUnion ((List.range (n + 1)).map fun m => q (e m)) = accumulate s n := by
    ext t
    constructor
    · intro ht
      obtain ⟨p, hp, htp⟩ := mem_iUnion₂.1 ht
      obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hp
      exact mem_accumulate.2 ⟨m, Nat.lt_succ_iff.1 (List.mem_range.1 hm), by rw [hs]; exact htp⟩
    · intro ht
      obtain ⟨m, hm, htm⟩ := mem_accumulate.1 ht
      refine mem_iUnion₂.2
        ⟨q (e m), List.mem_map.2 ⟨m, List.mem_range.2 (Nat.lt_succ_iff.2 hm), rfl⟩, ?_⟩
      rw [hs] at htm
      exact htm
  rw [hL]
  have hsub : E ∆ accumulate s n ⊆ (U \ E) ∪ (U \ accumulate s n) := by
    intro t ht
    rcases mem_symmDiff.1 ht with ⟨htE, htV⟩ | ⟨htV, htE⟩
    · exact Or.inr ⟨hEU htE, htV⟩
    · exact Or.inl ⟨hV_sub n htV, htE⟩
  calc expMeasure (E ∆ accumulate s n) ≤ expMeasure ((U \ E) ∪ (U \ accumulate s n)) :=
        measure_mono hsub
    _ ≤ expMeasure (U \ E) + expMeasure (U \ accumulate s n) := measure_union_le _ _
    _ < δ / 2 + δ / 2 := ENNReal.add_lt_add hUE hn
    _ = δ := ENNReal.add_halves δ

variable [Countable S]

/-- The countable family of (classes of) rational step functions. -/
noncomputable def stepClass (x : List (List (ℚ × ℚ) × S) × S) : L1loc S :=
  mk (stepFn x.1 x.2) (measurableSet_stepFn_preimage x.1 x.2)

/-- **Density of rational step functions.**  Given `f` and `ε`, first choose `n` so that the
set `C n` where `f` avoids the first `n+1` values of an enumeration of `S` has measure
`< ε/2` (continuity from above, `expMeasure` finite), then approximate each fiber
`{f = e i}`, `i ≤ n`, by a finite union of rational intervals within `ε / (2 (n+1))`. -/
theorem denseRange_stepClass : DenseRange (stepClass (S := S)) := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  suffices h : ∃ x, edist f (stepClass x) < ENNReal.ofReal ε by
    obtain ⟨x, hx⟩ := h
    exact ⟨x, edist_lt_ofReal.1 hx⟩
  have hε'pos : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  have hε'top : ENNReal.ofReal ε ≠ ∞ := ENNReal.ofReal_ne_top
  have : Nonempty S := ⟨f 0⟩
  obtain ⟨e, he⟩ := exists_surjective_nat S
  -- the fibers of `f`
  obtain ⟨E, hE_meas, hE_mem⟩ : ∃ E : ℕ → Set ℝ, (∀ i, MeasurableSet (E i)) ∧
      ∀ i t, t ∈ E i ↔ f t = e i :=
    ⟨fun i => ⇑f ⁻¹' {e i}, fun i => f.measurableSet_preimage_singleton (e i),
      fun i t => Iff.rfl⟩
  -- `C n`: the set where `f` takes none of the first `n+1` values
  obtain ⟨C, hC_meas, hC_mem⟩ : ∃ C : ℕ → Set ℝ, (∀ n, MeasurableSet (C n)) ∧
      ∀ n t, t ∈ C n ↔ ∀ i ≤ n, f t ≠ e i :=
    ⟨fun n => ⋂ i, ⋂ (_ : i ≤ n), (E i)ᶜ,
      fun n => MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => (hE_meas i).compl,
      fun n t => by simp only [mem_iInter, mem_compl_iff, hE_mem]⟩
  have hC_anti : Antitone C := fun m n hmn t ht =>
    (hC_mem m t).2 fun i hi => (hC_mem n t).1 ht i (hi.trans hmn)
  have hC_inter : ⋂ n, C n = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun t ht => ?_
    rw [mem_iInter] at ht
    obtain ⟨i, hi⟩ := he (f t)
    exact (hC_mem i t).1 (ht i) i le_rfl hi.symm
  have hC_tendsto : Tendsto (fun n => expMeasure (C n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := expMeasure) (s := C)
      (fun n => (hC_meas n).nullMeasurableSet) hC_anti ⟨0, measure_ne_top _ _⟩
    rw [hC_inter, measure_empty] at h
    exact h
  obtain ⟨n, hn⟩ :=
    ((tendsto_order.1 hC_tendsto).2 (ENNReal.ofReal ε / 2) (ENNReal.half_pos hε'pos.ne')).exists
  -- approximate the fibers `E i`, `i ≤ n`, by finite unions of rational intervals
  have hδpos : 0 < ENNReal.ofReal ε / 2 / ((n + 1 : ℕ) : ℝ≥0∞) :=
    ENNReal.div_pos_iff.2 ⟨(ENNReal.half_pos hε'pos.ne').ne', ENNReal.natCast_ne_top _⟩
  choose L hL using fun i => exists_ratUnion_approx (E i) (hE_meas i) hδpos
  refine ⟨((List.range (n + 1)).map fun i => (L i, e i), e 0), ?_⟩
  rw [stepClass, edist_mk_right]
  -- `{f ≠ step} ⊆ C n ∪ ⋃ i ≤ n, E i ∆ ratUnion (L i)`
  have hsub : {t | f t ≠ stepFn ((List.range (n + 1)).map fun i => (L i, e i)) (e 0) t} ⊆
      C n ∪ ⋃ i ∈ Finset.range (n + 1), E i ∆ ratUnion (L i) := by
    intro t ht
    have ht' : f t ≠ stepFn ((List.range (n + 1)).map fun i => (L i, e i)) (e 0) t := ht
    by_contra hc
    simp only [mem_union, mem_iUnion, Finset.mem_range, exists_prop, not_or, not_exists,
      not_and] at hc
    obtain ⟨hcC, hsym⟩ := hc
    obtain ⟨i, hi, hfi⟩ : ∃ i ≤ n, f t = e i := by
      by_contra h
      push Not at h
      exact hcC ((hC_mem n t).2 h)
    refine ht' (stepFn_eq _ _ _ (f t) ?_ ?_).symm
    · intro ent hent htent
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hent
      have h := hsym j (List.mem_range.1 hj)
      rw [mem_symmDiff] at h
      push Not at h
      exact ((hE_mem j t).1 (h.2 htent)).symm
    · refine ⟨(L i, e i), List.mem_map.2 ⟨i, List.mem_range.2 (Nat.lt_succ_of_le hi), rfl⟩, ?_⟩
      have h := hsym i (Nat.lt_succ_of_le hi)
      rw [mem_symmDiff] at h
      push Not at h
      exact h.1 ((hE_mem i t).2 hfi)
  calc expMeasure {t | f t ≠ stepFn ((List.range (n + 1)).map fun i => (L i, e i)) (e 0) t}
      ≤ expMeasure (C n ∪ ⋃ i ∈ Finset.range (n + 1), E i ∆ ratUnion (L i)) :=
        measure_mono hsub
    _ ≤ expMeasure (C n) + expMeasure (⋃ i ∈ Finset.range (n + 1), E i ∆ ratUnion (L i)) :=
        measure_union_le _ _
    _ ≤ expMeasure (C n) + ∑ i ∈ Finset.range (n + 1), expMeasure (E i ∆ ratUnion (L i)) :=
        add_le_add le_rfl (measure_biUnion_finset_le _ _)
    _ ≤ expMeasure (C n) + ∑ _i ∈ Finset.range (n + 1),
          ENNReal.ofReal ε / 2 / ((n + 1 : ℕ) : ℝ≥0∞) :=
        add_le_add le_rfl (Finset.sum_le_sum fun i _ => (hL i).le)
    _ = expMeasure (C n) + ENNReal.ofReal ε / 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.mul_div_cancel (Nat.cast_ne_zero.2 (by omega)) (ENNReal.natCast_ne_top _)]
    _ < ENNReal.ofReal ε / 2 + ENNReal.ofReal ε / 2 :=
        (ENNReal.add_lt_add_iff_right (ENNReal.div_ne_top hε'top two_ne_zero)).2 hn
    _ = ENNReal.ofReal ε := ENNReal.add_halves _

/-- **Separability** (Definition 3.9): the rational step functions form a countable dense
family. -/
instance instSeparableSpace : TopologicalSpace.SeparableSpace (L1loc S) :=
  TopologicalSpace.SeparableSpace.of_denseRange _ denseRange_stepClass

end Separable

end L1loc

end ReflectedWalk

