import Mathlib
import LatticeProb.Prob.MixtureCoupling

/-!
# Couplings of mixtures with a common continuation

* `LatticeProb.exists_coupling_common_continuation`: let `A` and `B` be probability measures on
  `Y` and `Y'`, `Q` a probability measure on `U`, and `Φ₁ : Y × U → Ω₁`, `Φ₂ : Y' × U → Ω₂`
  measurable.  The image of `A ⊗ B ⊗ Q` under `(y, y', u) ↦ (Φ₁ (y, u), Φ₂ (y', u))` couples
  `(A ⊗ Q) ∘ Φ₁⁻¹` and `(B ⊗ Q) ∘ Φ₂⁻¹`; it is carried by every event that contains all the
  pairs `(Φ₁ (y, u), Φ₂ (y', u))`.
* `LatticeProb.exists_coupling_mixture_common_continuation`: for mixtures
  `μ = ∑ p v • ((A v ⊗ Q v) ∘ (Φ₁ v)⁻¹)` and `ν = ∑ q v • ((B v ⊗ Q v) ∘ (Φ₂ v)⁻¹)` there is a
  coupling of `μ` and `ν` that gives the complement of a measurable event `E` containing all the
  pairs `(Φ₁ v (y, u), Φ₂ v (y', u))` mass at most `1 - ∑ min (p v) (q v)`, and at most `a` if
  `∑_{v ∈ S} p v ≤ ∑_{v ∈ S} q v + a` for every `S`.

Abstractly: two Markov chains are stopped when they first reach a countable set `V` (here `p` and
`q` are the laws of the position of arrival, `A v` and `B v` the laws of the segments before the
arrival, given the position `v`, and `Q v` the common law of the continuation from `v`).
After the arrival positions are coupled maximally, the continuations from equal positions are made
identical.
-/

open MeasureTheory

open scoped ENNReal

namespace LatticeProb

variable {Y Y' U Ω₁ Ω₂ : Type*} [MeasurableSpace Y] [MeasurableSpace Y'] [MeasurableSpace U]
  [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

/-- **Coupling with a common continuation.**  The image of `A ⊗ B ⊗ Q` under
`(y, y', u) ↦ (Φ₁ (y, u), Φ₂ (y', u))` is a coupling of `(A ⊗ Q) ∘ Φ₁⁻¹` and `(B ⊗ Q) ∘ Φ₂⁻¹`;
the continuation `u` is shared. -/
theorem exists_coupling_common_continuation (A : Measure Y) (B : Measure Y') (Q : Measure U)
    [IsProbabilityMeasure A] [IsProbabilityMeasure B] [IsProbabilityMeasure Q]
    {Φ₁ : Y × U → Ω₁} {Φ₂ : Y' × U → Ω₂} (h₁ : Measurable Φ₁) (h₂ : Measurable Φ₂) :
    ∃ c : Measure (Ω₁ × Ω₂), c.map Prod.fst = (A.prod Q).map Φ₁ ∧
      c.map Prod.snd = (B.prod Q).map Φ₂ ∧
      ∀ E : Set (Ω₁ × Ω₂), MeasurableSet E → (∀ y y' u, (Φ₁ (y, u), Φ₂ (y', u)) ∈ E) →
        c Eᶜ = 0 := by
  let T : Y × (Y' × U) → Ω₁ × Ω₂ := fun t => (Φ₁ (t.1, t.2.2), Φ₂ t.2)
  have hT1 : Measurable (fun t : Y × (Y' × U) => Φ₁ (t.1, t.2.2)) :=
    h₁.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hT2 : Measurable (fun t : Y × (Y' × U) => Φ₂ t.2) := h₂.comp measurable_snd
  have hT : Measurable T := hT1.prodMk hT2
  refine ⟨(A.prod (B.prod Q)).map T, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hT]
    have hid : (A.prod (B.prod Q)).map (Prod.map id Prod.snd) = A.prod Q := by
      rw [← Measure.map_prod_map A (B.prod Q) measurable_id measurable_snd, Measure.map_id,
        Measure.map_snd_prod]
      simp
    have hfun : (Prod.fst ∘ T) = Φ₁ ∘ Prod.map id Prod.snd := by
      funext t; rfl
    rw [hfun, ← Measure.map_map h₁ (measurable_id.prodMap measurable_snd), hid]
  · rw [Measure.map_map measurable_snd hT]
    have hfun : (Prod.snd ∘ T) = Φ₂ ∘ Prod.snd := by
      funext t; rfl
    rw [hfun, ← Measure.map_map h₂ measurable_snd, Measure.map_snd_prod]
    simp
  · intro E hE hmem
    rw [Measure.map_apply hT hE.compl]
    have hempty : T ⁻¹' Eᶜ = ∅ := by
      ext t
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
        not_not]
      exact hmem t.1 t.2.1 t.2.2
    rw [hempty, measure_empty]

section Mixture

variable {V : Type*} [Countable V]

/-- **Coupling of mixtures with a common continuation.**  Let
`μ = ∑ p v • ((A v ⊗ Q v) ∘ (Φ₁ v)⁻¹)` and `ν = ∑ q v • ((B v ⊗ Q v) ∘ (Φ₂ v)⁻¹)` be mixtures
indexed by the countable set `V`, `p` and `q` probability vectors, and `E` a measurable event
containing all the pairs `(Φ₁ v (y, u), Φ₂ v (y', u))` for the `v` with `p v ≠ 0` and `q v ≠ 0`.
Then `μ` and `ν` have a coupling `ρ` with
`ρ Eᶜ ≤ 1 - ∑ min (p v) (q v)`. -/
theorem exists_coupling_mixture_common_continuation (p q : V → ℝ≥0∞) (hp : ∑' v, p v = 1)
    (hq : ∑' v, q v = 1) (A : V → Measure Y) (B : V → Measure Y') (Q : V → Measure U)
    [∀ v, IsProbabilityMeasure (A v)] [∀ v, IsProbabilityMeasure (B v)]
    [∀ v, IsProbabilityMeasure (Q v)] (Φ₁ : V → Y × U → Ω₁) (Φ₂ : V → Y' × U → Ω₂)
    (h₁ : ∀ v, Measurable (Φ₁ v)) (h₂ : ∀ v, Measurable (Φ₂ v))
    {E : Set (Ω₁ × Ω₂)} (hE : MeasurableSet E)
    (hEΦ : ∀ v, p v ≠ 0 → q v ≠ 0 → ∀ y y' u, (Φ₁ v (y, u), Φ₂ v (y', u)) ∈ E) :
    ∃ ρ : Measure (Ω₁ × Ω₂),
      ρ.map Prod.fst = Measure.sum (fun v => p v • ((A v).prod (Q v)).map (Φ₁ v)) ∧
      ρ.map Prod.snd = Measure.sum (fun v => q v • ((B v).prod (Q v)).map (Φ₂ v)) ∧
      ρ Eᶜ ≤ 1 - ∑' v, min (p v) (q v) := by
  choose c hc₁ hc₂ hcE using fun v =>
    exists_coupling_common_continuation (A v) (B v) (Q v) (h₁ v) (h₂ v)
  have : ∀ v, IsProbabilityMeasure (((A v).prod (Q v)).map (Φ₁ v)) := fun v =>
    (Measure.isProbabilityMeasure_map_iff (h₁ v).aemeasurable).2 inferInstance
  have : ∀ v, IsProbabilityMeasure (((B v).prod (Q v)).map (Φ₂ v)) := fun v =>
    (Measure.isProbabilityMeasure_map_iff (h₂ v).aemeasurable).2 inferInstance
  exact exists_coupling_mixture p q hp hq (fun v => ((A v).prod (Q v)).map (Φ₁ v))
    (fun v => ((B v).prod (Q v)).map (Φ₂ v)) c hc₁ hc₂ hE (fun v hp0 hq0 => hcE v E hE (hEΦ v hp0 hq0))

/-- Version with a total variation bound: if `∑_{v ∈ S} p v ≤ ∑_{v ∈ S} q v + a` for every
`S ⊆ V`, the coupling gives `Eᶜ` mass at most `a`. -/
theorem exists_coupling_mixture_common_continuation_of_tv (p q : V → ℝ≥0∞)
    (hp : ∑' v, p v = 1) (hq : ∑' v, q v = 1) {a : ℝ≥0∞}
    (hTV : ∀ S : Set V, ∑' v, S.indicator p v ≤ ∑' v, S.indicator q v + a)
    (A : V → Measure Y) (B : V → Measure Y') (Q : V → Measure U)
    [∀ v, IsProbabilityMeasure (A v)] [∀ v, IsProbabilityMeasure (B v)]
    [∀ v, IsProbabilityMeasure (Q v)] (Φ₁ : V → Y × U → Ω₁) (Φ₂ : V → Y' × U → Ω₂)
    (h₁ : ∀ v, Measurable (Φ₁ v)) (h₂ : ∀ v, Measurable (Φ₂ v))
    {E : Set (Ω₁ × Ω₂)} (hE : MeasurableSet E)
    (hEΦ : ∀ v, p v ≠ 0 → q v ≠ 0 → ∀ y y' u, (Φ₁ v (y, u), Φ₂ v (y', u)) ∈ E) :
    ∃ ρ : Measure (Ω₁ × Ω₂),
      ρ.map Prod.fst = Measure.sum (fun v => p v • ((A v).prod (Q v)).map (Φ₁ v)) ∧
      ρ.map Prod.snd = Measure.sum (fun v => q v • ((B v).prod (Q v)).map (Φ₂ v)) ∧
      ρ Eᶜ ≤ a := by
  obtain ⟨ρ, h1, h2, h3⟩ := exists_coupling_mixture_common_continuation p q hp hq A B Q Φ₁ Φ₂ h₁ h₂
    hE hEΦ
  exact ⟨ρ, h1, h2, h3.trans (one_sub_tsum_min_le p q hp hTV)⟩

end Mixture

end LatticeProb
