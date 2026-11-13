import LatticeProb.LQG.MatingOfTreesCouplingVisits

/-!
# The reparametrization part of the area clauses of a mating-of-trees coupling

The clauses `areaParam` and `areaParam₀` of a mating-of-trees coupling state, almost surely, that
the curve `η` (resp. `η₀`) is the Lebesgue-parametrized space-filling curve `η_L` run with an
increasing homeomorphism `φ` of `ℝ` fixing `0`, and that `η` is parametrized by the `γ`-LQG area.
This file shows that the first part depends only on the law of the pair of curves.

* `Continuous.strictMono_of_rat_lt`: a continuous function on `ℝ` that is strictly increasing on the
  rationals is strictly increasing.
* `ContinuousMap.reparamTriples`: the Borel set of triples `((η, L), f)` with `f` continuous, `f 0 = 0`,
  strictly increasing on the rationals, unbounded in both directions, and `η = L ∘ f` on the
  rationals. Its projection to the pair `(η, L)` is the set of pairs related by an order
  isomorphism of `ℝ` fixing `0` (`ContinuousMap.exists_orderIso_iff_mem_image_reparamTriples`), so
  that set is analytic and null-measurable for every finite Borel measure.
* `IsCouplingData.ae_exists_orderIso_η_of_map_eq` and `IsCouplingData.ae_exists_orderIso_η₀_of_map_eq`:
  the reparametrization parts of `areaParam` and `areaParam₀` hold for every measurable random element
  of the data space with the law of a coupling.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

/-- A continuous function on `ℝ` that is strictly increasing on the rationals is strictly
increasing. -/
theorem Continuous.strictMono_of_rat_lt {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ a b : ℚ, a < b → f a < f b) : StrictMono f := by
  have hle₁ : ∀ (x : ℝ) (a : ℚ), x < a → f x ≤ f a := by
    intro x a hxa
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
      ((hf.tendsto x).eventually (lt_mem_nhds hlt))
    obtain ⟨c, hxc, hca⟩ := exists_rat_btwn (lt_min hxa (lt_add_of_pos_right x hε))
    have hc1 : (c : ℝ) < a := hca.trans_le (min_le_left _ _)
    have hc2 : (c : ℝ) < x + ε := hca.trans_le (min_le_right _ _)
    have h1 : f a < f c := hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    exact lt_asymm h1 (h c a (by exact_mod_cast hc1))
  have hle₂ : ∀ (b : ℚ) (y : ℝ), (b : ℝ) < y → f b ≤ f y := by
    intro b y hby
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
      ((hf.tendsto y).eventually (gt_mem_nhds hlt))
    obtain ⟨c, hbc, hcy⟩ := exists_rat_btwn (max_lt hby (sub_lt_self y hε))
    have hc1 : (b : ℝ) < c := (le_max_left _ _).trans_lt hbc
    have hc2 : y - ε < c := (le_max_right _ _).trans_lt hbc
    have h1 : f c < f b := hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    exact lt_asymm h1 (h b c (by exact_mod_cast hc1))
  intro x y hxy
  obtain ⟨a, hxa, hay⟩ := exists_rat_btwn hxy
  obtain ⟨b, hab, hby⟩ := exists_rat_btwn hay
  exact (hle₁ x a hxa).trans_lt ((h a b (by exact_mod_cast hab)).trans_le (hle₂ b y hby))

namespace ContinuousMap

variable {E : Type*} [TopologicalSpace E]

/-- The triples `((η, L), f)` of two curves and a continuous time change `f` with `f 0 = 0`,
strictly increasing on the rationals, unbounded above and below, with `η = L ∘ f` on the
rationals. -/
def reparamTriples (E : Type*) [TopologicalSpace E] : Set ((C(ℝ, E) × C(ℝ, E)) × C(ℝ, ℝ)) :=
  {q | q.2 0 = 0} ∩ (⋂ a : ℚ, ⋂ b : ℚ, {q | (a : ℝ) < b → q.2 a < q.2 b}) ∩
    (⋂ n : ℕ, ⋃ a : ℚ, {q | (n : ℝ) < q.2 a}) ∩ (⋂ n : ℕ, ⋃ a : ℚ, {q | q.2 a < -(n : ℝ)}) ∩
    ⋂ a : ℚ, {q | q.1.1 a = q.1.2 (q.2 a)}

/-- Two curves are related by an order isomorphism of `ℝ` fixing `0` if and only if they are the
first two coordinates of a triple of `reparamTriples`. -/
theorem exists_orderIso_iff_mem_image_reparamTriples [T2Space E] (p : C(ℝ, E) × C(ℝ, E)) :
    (∃ φ : ℝ ≃o ℝ, φ 0 = 0 ∧ ∀ t, p.1 t = p.2 (φ t)) ↔ p ∈ Prod.fst '' reparamTriples E := by
  constructor
  · rintro ⟨φ, hφ0, hφ⟩
    refine ⟨(p, ⟨φ, φ.continuous⟩), ?_, rfl⟩
    simp only [reparamTriples, mem_inter_iff, mem_iInter, mem_iUnion]
    refine ⟨⟨⟨⟨hφ0, fun a b hab => φ.strictMono hab⟩, fun n => ?_⟩, fun n => ?_⟩, fun a => hφ a⟩
    · obtain ⟨a, ha⟩ := exists_rat_gt (φ.symm ((n : ℝ) + 1))
      refine ⟨a, ?_⟩
      have := φ.strictMono ha
      rw [OrderIso.apply_symm_apply] at this
      show (n : ℝ) < φ a
      linarith
    · obtain ⟨a, ha⟩ := exists_rat_lt (φ.symm (-(n : ℝ) - 1))
      refine ⟨a, ?_⟩
      have := φ.strictMono ha
      rw [OrderIso.apply_symm_apply] at this
      show φ a < -(n : ℝ)
      linarith
  · rintro ⟨⟨p', f⟩, hq, rfl⟩
    simp only [reparamTriples, mem_inter_iff, mem_iInter, mem_iUnion] at hq
    obtain ⟨⟨⟨⟨hf0, hmono⟩, htop⟩, hbot⟩, heq⟩ := hq
    have hsm : StrictMono f := f.continuous.strictMono_of_rat_lt fun a b hab => hmono a b
      (by exact_mod_cast hab)
    have hsurj : Function.Surjective f := by
      refine f.continuous.surjective (hsm.monotone.tendsto_atTop_atTop fun b => ?_)
        (hsm.monotone.tendsto_atBot_atBot fun b => ?_)
      · obtain ⟨a, ha⟩ := htop ⌈b⌉₊
        exact ⟨a, (Nat.le_ceil b).trans ha.le⟩
      · obtain ⟨a, ha⟩ := hbot ⌈-b⌉₊
        refine ⟨a, ha.le.trans ?_⟩
        linarith [Nat.le_ceil (-b)]
    refine ⟨StrictMono.orderIsoOfSurjective f hsm hsurj, hf0, fun t => ?_⟩
    have hext : (p'.1 : ℝ → E) = fun t => p'.2 (f t) :=
      Continuous.ext_on (Rat.denseRange_cast : Dense (range ((↑) : ℚ → ℝ))) p'.1.continuous
        (p'.2.continuous.comp f.continuous) (by rintro _ ⟨a, rfl⟩; exact heq a)
    exact congrFun hext t

variable [PolishSpace E]

/-- The set `reparamTriples` is Borel. -/
theorem measurableSet_reparamTriples : MeasurableSet (reparamTriples E) := by
  have : PolishSpace C(ℝ, E) := LQGMetric.polishSpace_continuousMap ℝ E
  have : PolishSpace C(ℝ, ℝ) := LQGMetric.polishSpace_continuousMap ℝ ℝ
  have hev : ∀ x : ℝ, Continuous fun q : (C(ℝ, E) × C(ℝ, E)) × C(ℝ, ℝ) => q.2 x := fun x =>
    (continuous_eval_const x).comp continuous_snd
  refine (((MeasurableSet.inter ?_ ?_).inter ?_).inter ?_).inter ?_
  · exact (isClosed_eq (hev 0) continuous_const).measurableSet
  · refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => ?_
    by_cases hab : (a : ℝ) < b
    · have hs : {q : (C(ℝ, E) × C(ℝ, E)) × C(ℝ, ℝ) | (a : ℝ) < b → q.2 a < q.2 b} =
          {q | q.2 a < q.2 b} := by
        ext q
        exact ⟨fun h => h hab, fun h _ => h⟩
      rw [hs]
      exact (isOpen_lt (hev a) (hev b)).measurableSet
    · have hs : {q : (C(ℝ, E) × C(ℝ, E)) × C(ℝ, ℝ) | (a : ℝ) < b → q.2 a < q.2 b} = univ :=
        eq_univ_of_forall fun q h => absurd h hab
      rw [hs]
      exact MeasurableSet.univ
  · exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun a =>
      (isOpen_lt continuous_const (hev a)).measurableSet
  · exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun a =>
      (isOpen_lt (hev a) continuous_const).measurableSet
  · refine MeasurableSet.iInter fun a => (isClosed_eq ?_ ?_).measurableSet
    · exact (continuous_eval_const (a : ℝ)).comp (continuous_fst.comp continuous_fst)
    · exact ContinuousEval.continuous_eval.comp
        ((continuous_snd.comp continuous_fst).prodMk (hev a))

/-- The pairs of curves related by an order isomorphism of `ℝ` fixing `0` form an analytic set. -/
theorem analyticSet_setOf_exists_orderIso :
    AnalyticSet {p : C(ℝ, E) × C(ℝ, E) | ∃ φ : ℝ ≃o ℝ, φ 0 = 0 ∧ ∀ t, p.1 t = p.2 (φ t)} := by
  have : PolishSpace C(ℝ, E) := LQGMetric.polishSpace_continuousMap ℝ E
  have : PolishSpace C(ℝ, ℝ) := LQGMetric.polishSpace_continuousMap ℝ ℝ
  have hset : {p : C(ℝ, E) × C(ℝ, E) | ∃ φ : ℝ ≃o ℝ, φ 0 = 0 ∧ ∀ t, p.1 t = p.2 (φ t)} =
      Prod.fst '' reparamTriples E := by
    ext p
    exact exists_orderIso_iff_mem_image_reparamTriples p
  rw [hset]
  exact measurableSet_reparamTriples.analyticSet.image_of_continuous continuous_fst

/-- The event that two curves are related by an order isomorphism of `ℝ` fixing `0` is
null-measurable for every finite Borel measure on pairs of curves. -/
theorem nullMeasurableSet_setOf_exists_orderIso (μ : Measure (C(ℝ, E) × C(ℝ, E)))
    [IsFiniteMeasure μ] :
    NullMeasurableSet {p : C(ℝ, E) × C(ℝ, E) | ∃ φ : ℝ ≃o ℝ, φ 0 = 0 ∧ ∀ t, p.1 t = p.2 (φ t)} μ := by
  have : PolishSpace C(ℝ, E) := LQGMetric.polishSpace_continuousMap ℝ E
  exact LatticeProb.AnalyticSet.nullMeasurableSet μ analyticSet_setOf_exists_orderIso

end ContinuousMap

namespace MatedCRTHarmonic

namespace MatedCRT

variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
  {γ : ℝ} {V : Ω → CouplingData} {V' : Ω' → CouplingData}

open CouplingData

/-- The reparametrization part of `areaParam`: for a measurable random element of the data space
with the law of a coupling, the curve `η` is almost surely `η_L` run with an order isomorphism of
`ℝ` fixing `0`. -/
theorem IsCouplingData.ae_exists_orderIso_η_of_map_eq (hC : IsCouplingData γ P V)
    (hV : Measurable V) (hV' : Measurable V') (hlaw : P'.map V' = P.map V) :
    ∀ᵐ ω ∂P', ∃ φ : ℝ ≃o ℝ, φ 0 = 0 ∧ ∀ t, (V' ω).η t = (V' ω).ηL (φ t) := by
  have hCP := (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC)
  have := hCP.isProbabilityMeasure
  have hπ : Measurable fun v : CouplingData => (v.η, v.ηL) := measurable_η.prodMk measurable_ηL
  exact ae_comp_of_map_eq_of_nullMeasurableSet (hπ.comp hV) (hπ.comp hV')
    (map_comp_of_map_eq hV hV' hlaw hπ) (ContinuousMap.nullMeasurableSet_setOf_exists_orderIso _)
    (hCP.areaParam.mono fun ω h => h.1)

/-- The reparametrization part of `areaParam₀`: for a measurable random element of the data space
with the law of a coupling, the curve `η₀` is almost surely `η_L` run with an order isomorphism of
`ℝ` fixing `0`. -/
theorem IsCouplingData.ae_exists_orderIso_η₀_of_map_eq (hC : IsCouplingData γ P V)
    (hV : Measurable V) (hV' : Measurable V') (hlaw : P'.map V' = P.map V) :
    ∀ᵐ ω ∂P', ∃ φ : ℝ ≃o ℝ, φ 0 = 0 ∧ ∀ t, (V' ω).η₀ t = (V' ω).ηL (φ t) := by
  have hCP := (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC)
  have := hCP.isProbabilityMeasure
  have hπ : Measurable fun v : CouplingData => (v.η₀, v.ηL) := measurable_η₀.prodMk measurable_ηL
  exact ae_comp_of_map_eq_of_nullMeasurableSet (hπ.comp hV) (hπ.comp hV')
    (map_comp_of_map_eq hV hV' hlaw hπ) (ContinuousMap.nullMeasurableSet_setOf_exists_orderIso _)
    (hCP.areaParam₀.mono fun ω h => h.1)

end MatedCRT

end MatedCRTHarmonic
