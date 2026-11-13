import Mathlib

/-!
# Mixture decomposition from a conditional product structure

`LatticeProb.exists_mixture_of_conditional_product`: let `P` be a probability measure on `Ω`,
`X : Ω → V` a measurable map to a countable set (a stopped position), and `pre : Ω → Y`,
`post : Ω → U` measurable maps (the data before and after the stopping time).  Suppose that
conditionally on `X = v` the data `pre` and `post` are independent and `post` has law `Q v`, i.e.
`P (pre ∈ B, X = v, post ∈ C) = P (pre ∈ B, X = v) * Q v C` for measurable `B`, `C`, and that
`ω = Φ v (pre ω, post ω)` for almost every `ω` with `X ω = v`, for a measurable `Φ v`.  Then
`P = ∑_v P (X = v) • ((A v ⊗ Q v) ∘ (Φ v)⁻¹)`, where `A v` is the law of `pre` given `X = v`.

This is the measure form of the strong Markov property for the decomposition of a path at a
stopping time into the stopped path and the shifted continuation.
-/

open MeasureTheory

open scoped ENNReal

namespace LatticeProb

variable {Ω Y U V : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSpace U]
  [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- **Mixture decomposition of a law given a conditional product structure.**  See the module
docstring.  The probability measure `A v` is the law of `pre` conditionally on `{X = v}` (an
arbitrary probability measure if `P {X = v} = 0`). -/
theorem exists_mixture_of_conditional_product (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → V} {pre : Ω → Y} {post : Ω → U} (hX : Measurable X) (hpre : Measurable pre)
    (hpost : Measurable post) (Q : V → Measure U) [∀ v, IsProbabilityMeasure (Q v)]
    (Φ : V → Y × U → Ω) (hΦ : ∀ v, Measurable (Φ v))
    (hrect : ∀ (v : V) (B : Set Y) (C : Set U), MeasurableSet B → MeasurableSet C →
      P (pre ⁻¹' B ∩ X ⁻¹' {v} ∩ post ⁻¹' C) = P (pre ⁻¹' B ∩ X ⁻¹' {v}) * Q v C)
    (hrec : ∀ᵐ ω ∂P, Φ (X ω) (pre ω, post ω) = ω) :
    ∃ A : V → Measure Y, (∀ v, IsProbabilityMeasure (A v)) ∧
      (∀ v, P (X ⁻¹' {v}) • A v = (P.restrict (X ⁻¹' {v})).map pre) ∧
      P = Measure.sum (fun v => P (X ⁻¹' {v}) • ((A v).prod (Q v)).map (Φ v)) := by
  classical
  have hmeasX : ∀ v, MeasurableSet (X ⁻¹' {v}) := fun v => hX (measurableSet_singleton v)
  have hprepost : Measurable (fun ω => (pre ω, post ω)) := hpre.prodMk hpost
  obtain ⟨μ, hμ⟩ : ∃ μ : V → Measure Ω, ∀ v, μ v = P.restrict (X ⁻¹' {v}) :=
    ⟨_, fun _ => rfl⟩
  have hfin : ∀ v, IsFiniteMeasure (μ v) := fun v => by rw [hμ]; infer_instance
  -- the law of `(pre, post)` restricted to `{X = v}` is a product measure
  have hprod : ∀ v, (μ v).map (fun ω => (pre ω, post ω)) = ((μ v).map pre).prod (Q v) := by
    intro v
    have := hfin v
    symm
    apply Measure.prod_eq
    intro B C hB hC
    rw [Measure.map_apply hprepost (hB.prod hC), Measure.map_apply hpre hB, hμ v]
    have hset : (fun ω => (pre ω, post ω)) ⁻¹' (B ×ˢ C) = pre ⁻¹' B ∩ post ⁻¹' C := rfl
    rw [hset, Measure.restrict_apply ((hpre hB).inter (hpost hC)),
      Measure.restrict_apply (hpre hB), ← hrect v B C hB hC]
    congr 1
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    tauto
  -- reassembling the path from `(pre, post)` on `{X = v}`
  have hmu : ∀ v, μ v = (((μ v).map pre).prod (Q v)).map (Φ v) := by
    intro v
    rw [← hprod v, Measure.map_map (hΦ v) hprepost]
    have hae : (Φ v ∘ fun ω => (pre ω, post ω)) =ᵐ[μ v] id := by
      have h1 : ∀ᵐ ω ∂(μ v), ω ∈ X ⁻¹' {v} := by
        rw [hμ v]; exact ae_restrict_mem (hmeasX v)
      have h2 : ∀ᵐ ω ∂(μ v), Φ (X ω) (pre ω, post ω) = ω := by
        rw [hμ v]; exact ae_restrict_of_ae hrec
      filter_upwards [h1, h2] with ω h1 h2
      have h1' : X ω = v := h1
      rw [h1'] at h2
      exact h2
    rw [Measure.map_congr hae, Measure.map_id]
  -- the restrictions to the fibres add up to `P`
  have hsum : P = Measure.sum μ := by
    ext S hS
    rw [Measure.sum_apply _ hS]
    simp only [hμ, Measure.restrict_apply hS]
    have hS' : S = ⋃ v, S ∩ X ⁻¹' {v} := by
      ext ω; simp
    calc P S = P (⋃ v, S ∩ X ⁻¹' {v}) := by rw [← hS']
      _ = ∑' v, P (S ∩ X ⁻¹' {v}) := by
        refine measure_iUnion (fun v w hvw => ?_) (fun v => hS.inter (hmeasX v))
        refine Set.disjoint_left.2 fun ω h1 h2 => hvw ?_
        have e1 : X ω = v := h1.2
        have e2 : X ω = w := h2.2
        rw [← e1, ← e2]
  -- the conditional laws of `pre`
  obtain ⟨ω₀, -⟩ : (Set.univ : Set Ω).Nonempty :=
    nonempty_of_measure_ne_zero (μ := P) (s := Set.univ) (by simp)
  obtain ⟨A, hAdef⟩ : ∃ A : V → Measure Y, ∀ v, A v =
      if P (X ⁻¹' {v}) = 0 then Measure.dirac (pre ω₀)
      else (P (X ⁻¹' {v}))⁻¹ • (μ v).map pre := ⟨_, fun _ => rfl⟩
  have huniv : ∀ v, ((μ v).map pre) Set.univ = P (X ⁻¹' {v}) := by
    intro v
    rw [Measure.map_apply hpre MeasurableSet.univ, Set.preimage_univ, hμ v,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have hA_prob : ∀ v, IsProbabilityMeasure (A v) := by
    intro v
    by_cases h0 : P (X ⁻¹' {v}) = 0
    · rw [hAdef v]
      simp only [h0, ↓reduceIte]
      infer_instance
    · refine ⟨?_⟩
      rw [hAdef v]
      simp only [h0, ↓reduceIte, Measure.smul_apply, huniv, smul_eq_mul]
      exact ENNReal.inv_mul_cancel h0 (measure_ne_top _ _)
  have hA : ∀ v, P (X ⁻¹' {v}) • A v = (μ v).map pre := by
    intro v
    by_cases h0 : P (X ⁻¹' {v}) = 0
    · have hz : μ v = 0 := by rw [hμ v]; exact Measure.restrict_eq_zero.2 h0
      rw [hAdef v]
      simp [h0, hz]
    · rw [hAdef v]
      simp only [h0, ↓reduceIte]
      rw [smul_smul, ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), one_smul]
  refine ⟨A, hA_prob, fun v => by rw [hA v, hμ v], hsum.trans (congrArg Measure.sum
    (funext fun v => ?_))⟩
  rw [hmu v, ← hA v, Measure.prod_smul_left, Measure.map_smul]
  exact (hΦ v).aemeasurable

end LatticeProb
