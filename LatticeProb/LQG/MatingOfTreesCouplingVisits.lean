import LatticeProb.LQG.MatingOfTreesCouplingLaw
import LatticeProb.Prob.AnalyticUniversalMeasurable

/-!
# Multiple points of a continuous curve

For a continuous curve `f : ℝ → E` into a Polish space, the curves having a point with more than
`k` preimages form an analytic subset of `C(ℝ, E)`: they are the projection of the Borel set of
pairs `(f, t)` with `t : Fin (k + 1) → ℝ` injective and `f ∘ t` constant. Analytic sets are
null-measurable for every finite Borel measure, so the event that every point is visited at most
`k` times is null-measurable for the law of the curve.

* `exists_lt_encard_preimage_iff`: a point has more than `k` preimages iff some `k + 1` distinct
  times have the same value;
* `ContinuousMap.analyticSet_setOf_lt_encard_preimage`;
* `ContinuousMap.nullMeasurableSet_setOf_encard_preimage_le`;
* `IsCouplingData.visitBound_of_map_eq`: the visit bound of the space-filling curve of a
  mating-of-trees coupling holds, with the same `k`, for every measurable random element of the
  data space with the law of a coupling.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

/-- A point has more than `k` preimages under `f : ℝ → β` iff some `k + 1` distinct times have the
same value. -/
theorem exists_lt_encard_preimage_iff {β : Type*} (f : ℝ → β) (k : ℕ) :
    (∃ z, (k : ℕ∞) < (f ⁻¹' {z}).encard) ↔
      ∃ t : Fin (k + 1) → ℝ, Function.Injective t ∧ ∀ i, f (t i) = f (t 0) := by
  constructor
  · rintro ⟨z, hz⟩
    have hk : ((k + 1 : ℕ) : ℕ∞) ≤ (f ⁻¹' {z}).encard := by
      rw [Nat.cast_add, Nat.cast_one]
      exact (ENat.add_one_le_iff (ENat.natCast_ne_top k)).2 hz
    obtain ⟨u, hu, hue⟩ := Set.exists_subset_encard_eq hk
    have hfin : u.Finite := Set.finite_of_encard_eq_coe hue
    have hcard : hfin.toFinset.card = k + 1 := by
      have h1 := hfin.encard_eq_coe_toFinset_card
      rw [hue] at h1
      exact_mod_cast h1.symm
    let e := hfin.toFinset.orderIsoOfFin hcard
    have hmem : ∀ i, f (e i : ℝ) = z := fun i => hu ((Set.Finite.mem_toFinset hfin).1 (e i).2)
    refine ⟨fun i => (e i : ℝ), Subtype.val_injective.comp e.injective, fun i => ?_⟩
    rw [hmem i, hmem 0]
  · rintro ⟨t, ht, heq⟩
    refine ⟨f (t 0), ?_⟩
    have hsub : range t ⊆ f ⁻¹' {f (t 0)} := by
      rintro _ ⟨i, rfl⟩
      exact heq i
    calc (k : ℕ∞) < k + 1 := by exact_mod_cast Nat.lt_succ_self k
      _ = (range t).encard := by rw [ht.encard_range]; simp
      _ ≤ (f ⁻¹' {f (t 0)}).encard := Set.encard_le_encard hsub

namespace ContinuousMap

variable {E : Type*} [TopologicalSpace E] [PolishSpace E]

/-- The continuous curves having a point with more than `k` preimages form an analytic set. -/
theorem analyticSet_setOf_lt_encard_preimage (k : ℕ) :
    AnalyticSet {f : C(ℝ, E) | ∃ z, (k : ℕ∞) < (f ⁻¹' {z}).encard} := by
  have : PolishSpace C(ℝ, E) := LQGMetric.polishSpace_continuousMap ℝ E
  have hinj : MeasurableSet {p : C(ℝ, E) × (Fin (k + 1) → ℝ) | Function.Injective p.2} := by
    have hset : {p : C(ℝ, E) × (Fin (k + 1) → ℝ) | Function.Injective p.2} =
        ⋂ i, ⋂ j, {p : C(ℝ, E) × (Fin (k + 1) → ℝ) | p.2 i = p.2 j → i = j} := by
      ext p
      simp only [mem_iInter, Set.mem_ofPred_eq]
      exact Iff.rfl
    rw [hset]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    by_cases hij : i = j
    · subst hij
      simp
    · have hc : {p : C(ℝ, E) × (Fin (k + 1) → ℝ) | p.2 i = p.2 j → i = j} =
          {p : C(ℝ, E) × (Fin (k + 1) → ℝ) | p.2 i = p.2 j}ᶜ := by
        ext p
        simp [hij]
      rw [hc]
      exact (isClosed_eq ((continuous_apply i).comp continuous_snd)
        ((continuous_apply j).comp continuous_snd)).measurableSet.compl
  have hev : ∀ i : Fin (k + 1), Continuous fun p : C(ℝ, E) × (Fin (k + 1) → ℝ) => p.1 (p.2 i) :=
    fun i => ContinuousEval.continuous_eval.comp
      (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))
  have hcl : IsClosed {p : C(ℝ, E) × (Fin (k + 1) → ℝ) | ∀ i, p.1 (p.2 i) = p.1 (p.2 0)} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq (hev i) (hev 0)
  have hT : AnalyticSet {p : C(ℝ, E) × (Fin (k + 1) → ℝ) |
      Function.Injective p.2 ∧ ∀ i, p.1 (p.2 i) = p.1 (p.2 0)} :=
    (hinj.inter hcl.measurableSet).analyticSet
  have hset : {f : C(ℝ, E) | ∃ z, (k : ℕ∞) < (f ⁻¹' {z}).encard} =
      Prod.fst '' {p : C(ℝ, E) × (Fin (k + 1) → ℝ) |
        Function.Injective p.2 ∧ ∀ i, p.1 (p.2 i) = p.1 (p.2 0)} := by
    ext f
    constructor
    · intro hf
      obtain ⟨t, ht, heq⟩ := (exists_lt_encard_preimage_iff f k).1 hf
      exact ⟨(f, t), ⟨ht, heq⟩, rfl⟩
    · rintro ⟨⟨g, t⟩, ⟨ht, heq⟩, rfl⟩
      exact (exists_lt_encard_preimage_iff g k).2 ⟨t, ht, heq⟩
  rw [hset]
  exact hT.image_of_continuous continuous_fst

/-- The event that every point is visited at most `k` times is null-measurable for every finite
Borel measure on `C(ℝ, E)`. -/
theorem nullMeasurableSet_setOf_encard_preimage_le (μ : Measure C(ℝ, E)) [IsFiniteMeasure μ]
    (k : ℕ) : NullMeasurableSet {f : C(ℝ, E) | ∀ z, (f ⁻¹' {z}).encard ≤ k} μ := by
  have : PolishSpace C(ℝ, E) := LQGMetric.polishSpace_continuousMap ℝ E
  have h := (LatticeProb.AnalyticSet.nullMeasurableSet μ
    (analyticSet_setOf_lt_encard_preimage (E := E) k)).compl
  convert h using 1
  ext f
  simp [not_lt]

end ContinuousMap

namespace MatedCRTHarmonic

namespace MatedCRT

variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
  {γ : ℝ} {V : Ω → CouplingData} {V' : Ω' → CouplingData}

open CouplingData

/-- The visit bound of the space-filling curve holds, with the same bound, for a measurable random
element of the data space with the law of a coupling. -/
theorem IsCouplingData.visitBound_of_map_eq (hC : IsCouplingData γ P V) (hV : Measurable V)
    (hV' : Measurable V') (hlaw : P'.map V' = P.map V) :
    ∃ k : ℕ, ∀ᵐ ω ∂P', ∀ z : ℂ, ((V' ω).ηL ⁻¹' {z}).encard ≤ k := by
  have hCP := (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC)
  have := hCP.isProbabilityMeasure
  obtain ⟨k, hk⟩ := hCP.visitBound
  refine ⟨k, ?_⟩
  have hlawL : P'.map (fun ω => (V' ω).ηL) = P.map (fun ω => (V ω).ηL) :=
    map_comp_of_map_eq hV hV' hlaw measurable_ηL
  exact ae_comp_of_map_eq_of_nullMeasurableSet (measurable_ηL.comp hV) (measurable_ηL.comp hV')
    hlawL (ContinuousMap.nullMeasurableSet_setOf_encard_preimage_le _ k) hk

end MatedCRT

end MatedCRTHarmonic

end
