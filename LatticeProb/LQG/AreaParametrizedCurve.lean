import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Hom.Set
import Mathlib.Data.Rat.Cast.Order

/-!
# Curves parametrized by the mass of a measure

Let `L : ℝ → E` be a curve in a measurable space `E` (for instance `ℂ`) and `μ` a measure on `E`. A reparametrization `η = L ∘ v` by an increasing
homeomorphism `v : ℝ ≃o ℝ` with `v 0 = 0` is *parametrized by `μ`-mass* if `μ (η [s, t]) = t - s` for all `s ≤ t`
(for space-filling SLE parametrized by `γ`-LQG area, `μ` is the `γ`-LQG measure and `L` the curve parametrized by
Lebesgue measure). Then the inverse clock is the signed mass of the segments of `L`:
`v⁻¹ u = μ (L [0, u])` for `u ≥ 0` and `v⁻¹ u = -μ (L [u, 0])` for `u < 0`.
Hence the clock `v` and the curve `η` are uniquely determined by `μ` and `L`, and when the masses of the segments
of `L` depend measurably on a parameter, so do `v` and `η`.

## Main results

* `orderIso_symm_eq_measure_image`: the inverse clock is the signed mass of the segments of the reference curve.
* `orderIso_eq_and_eq_of_massParam`: uniqueness of the clock and of the reparametrized curve.
* `measurable_orderIso_symm_apply`: inversion of a measurable family of order isomorphisms of `ℝ` is measurable.
* `measurable_orderIso_apply_of_massParam`, `measurable_curve_apply_of_massParam`: measurability of the clock and of
  the reparametrized curve in the parameter, from measurability of the segment masses at rational endpoints.
-/

open MeasureTheory Set

namespace LatticeProb.LQG

/-- The image of an interval under a reparametrization `η = L ∘ v` by an order isomorphism. -/
theorem image_Icc_of_reparam {E : Type*} (L η : ℝ → E) (v : ℝ ≃o ℝ) (hη : ∀ t, η t = L (v t)) (a b : ℝ) :
    η '' Icc a b = L '' Icc (v a) (v b) := by
  have heq : η = L ∘ v := funext hη
  rw [heq, Set.image_comp, v.image_Icc]

/-- **The inverse clock is the signed segment mass.** If `η = L ∘ v` with `v 0 = 0` is parametrized by `μ`-mass,
then `v⁻¹ u = μ (L [0, u])` for `u ≥ 0` and `v⁻¹ u = -μ (L [u, 0])` for `u < 0`. -/
theorem orderIso_symm_eq_measure_image {E : Type*} [MeasurableSpace E] (μ : Measure E) (L η : ℝ → E) (v : ℝ ≃o ℝ)
    (hv : v 0 = 0) (hη : ∀ t, η t = L (v t))
    (harea : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s)) :
    ∀ u : ℝ, v.symm u = if 0 ≤ u then (μ (L '' Icc 0 u)).toReal
      else -(μ (L '' Icc u 0)).toReal := by
  intro u
  have hv0 : v.symm 0 = 0 := by
    apply v.injective
    simpa only [OrderIso.apply_symm_apply] using hv.symm
  by_cases hu : 0 ≤ u
  · have hs : 0 ≤ v.symm u := by
      simpa only [hv0] using v.symm.monotone hu
    have hm := harea 0 (v.symm u) hs
    rw [image_Icc_of_reparam L η v hη, hv, OrderIso.apply_symm_apply] at hm
    rw [ite_eq_left hu, hm, sub_zero, ENNReal.toReal_ofReal hs]
  · have hs : v.symm u ≤ 0 := by
      simpa only [hv0] using v.symm.monotone (le_of_not_ge hu)
    have hm := harea (v.symm u) 0 hs
    rw [image_Icc_of_reparam L η v hη, hv, OrderIso.apply_symm_apply] at hm
    rw [ite_eq_right hu, hm, ENNReal.toReal_ofReal (sub_nonneg.mpr hs)]
    ring

/-- **Uniqueness of the mass parametrization.** Two reparametrizations of the same curve `L`, rooted at `0` and both
parametrized by `μ`-mass, have the same clock and are the same curve. -/
theorem orderIso_eq_and_eq_of_massParam {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (L η₁ η₂ : ℝ → E) (v₁ v₂ : ℝ ≃o ℝ)
    (hv₁ : v₁ 0 = 0) (hv₂ : v₂ 0 = 0)
    (hη₁ : ∀ t, η₁ t = L (v₁ t)) (hη₂ : ∀ t, η₂ t = L (v₂ t))
    (harea₁ : ∀ s t : ℝ, s ≤ t → μ (η₁ '' Icc s t) = ENNReal.ofReal (t - s))
    (harea₂ : ∀ s t : ℝ, s ≤ t → μ (η₂ '' Icc s t) = ENNReal.ofReal (t - s)) :
    v₁ = v₂ ∧ η₁ = η₂ := by
  have heq : v₁.symm = v₂.symm := by
    ext u
    rw [orderIso_symm_eq_measure_image μ L η₁ v₁ hv₁ hη₁ harea₁ u,
      orderIso_symm_eq_measure_image μ L η₂ v₂ hv₂ hη₂ harea₂ u]
  have hv : v₁ = v₂ := by
    have := congrArg OrderIso.symm heq
    simpa only [OrderIso.symm_symm] using this
  refine ⟨hv, funext fun t => ?_⟩
  rw [hη₁, hη₂, hv]

/-- **Measurable inversion of order isomorphisms.** For a family `v ω` of order isomorphisms of `ℝ` which is
measurable in `ω` at every rational time, `ω ↦ (v ω)⁻¹ (t ω)` is measurable for every measurable `t`. -/
theorem measurable_orderIso_symm_apply {Ω : Type*} [MeasurableSpace Ω]
    (v : Ω → ℝ ≃o ℝ) (t : Ω → ℝ) (ht : Measurable t)
    (hv : ∀ q : ℚ, Measurable (fun ω => v ω q)) :
    Measurable (fun ω => (v ω).symm (t ω)) := by
  apply measurable_of_Iio
  intro x
  have hset : {ω | (v ω).symm (t ω) < x} =
      ⋃ q : {q : ℚ // (q : ℝ) < x}, {ω | t ω < v ω q.1} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      obtain ⟨q, hq, hqx⟩ := exists_rat_btwn h
      refine ⟨⟨q, hqx⟩, ?_⟩
      have hh := (v ω).strictMono hq
      simpa only [OrderIso.apply_symm_apply] using hh
    · rintro ⟨q, hq⟩
      have h : (v ω).symm (t ω) < (q.1 : ℝ) := by
        simpa only [OrderIso.symm_apply_apply] using (v ω).symm.strictMono hq
      exact lt_trans h q.2
  change MeasurableSet {ω | (v ω).symm (t ω) < x}
  rw [hset]
  exact MeasurableSet.iUnion fun q => measurableSet_lt ht (hv q.1)

/-- **The mass clock is measurable.** If `η ω = L ω ∘ v ω` is parametrized by `μ ω`-mass for every `ω`, and the
masses of the segments `L ω [0, q]`, `L ω [q, 0]` are measurable in `ω` for rational `q`, then `ω ↦ v ω (t ω)` is
measurable for every measurable `t`. -/
theorem measurable_orderIso_apply_of_massParam {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Ω → Measure E) (L η : Ω → ℝ → E) (v : Ω → ℝ ≃o ℝ)
    (hv0 : ∀ ω, v ω 0 = 0) (hη : ∀ ω t, η ω t = L ω (v ω t))
    (harea : ∀ ω s t, s ≤ t → μ ω (η ω '' Icc s t) = ENNReal.ofReal (t - s))
    (hpos : ∀ q : ℚ, Measurable (fun ω => (μ ω (L ω '' Icc 0 q)).toReal))
    (hneg : ∀ q : ℚ, Measurable (fun ω => (μ ω (L ω '' Icc q 0)).toReal))
    (t : Ω → ℝ) (ht : Measurable t) : Measurable (fun ω => v ω (t ω)) := by
  have hclock : ∀ q : ℚ, Measurable (fun ω => (v ω).symm q) := by
    intro q
    by_cases hq : 0 ≤ (q : ℝ)
    · have heq : (fun ω => (v ω).symm (q : ℝ)) =
          (fun ω => (μ ω (L ω '' Icc 0 q)).toReal) := by
        funext ω
        simpa only [ite_eq_left hq] using
          orderIso_symm_eq_measure_image (μ ω) (L ω) (η ω) (v ω) (hv0 ω) (hη ω) (harea ω) q
      rw [heq]
      exact hpos q
    · have heq : (fun ω => (v ω).symm (q : ℝ)) =
          (fun ω => -(μ ω (L ω '' Icc q 0)).toReal) := by
        funext ω
        simpa only [ite_eq_right hq] using
          orderIso_symm_eq_measure_image (μ ω) (L ω) (η ω) (v ω) (hv0 ω) (hη ω) (harea ω) q
      rw [heq]
      exact (hneg q).neg
  simpa only [OrderIso.symm_symm] using
    measurable_orderIso_symm_apply (fun ω => (v ω).symm) t ht hclock

/-- **The mass-parametrized curve is measurable.** Under the hypotheses of
`measurable_orderIso_apply_of_massParam`, if moreover `(ω, s) ↦ L ω s` is jointly measurable, then
`ω ↦ η ω (t ω)` is measurable for every measurable `t`. -/
theorem measurable_curve_apply_of_massParam {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Ω → Measure E) (L η : Ω → ℝ → E) (v : Ω → ℝ ≃o ℝ)
    (hv0 : ∀ ω, v ω 0 = 0) (hη : ∀ ω t, η ω t = L ω (v ω t))
    (harea : ∀ ω s t, s ≤ t → μ ω (η ω '' Icc s t) = ENNReal.ofReal (t - s))
    (hpos : ∀ q : ℚ, Measurable (fun ω => (μ ω (L ω '' Icc 0 q)).toReal))
    (hneg : ∀ q : ℚ, Measurable (fun ω => (μ ω (L ω '' Icc q 0)).toReal))
    (hL : Measurable (fun p : Ω × ℝ => L p.1 p.2))
    (t : Ω → ℝ) (ht : Measurable t) : Measurable (fun ω => η ω (t ω)) := by
  have hv := measurable_orderIso_apply_of_massParam μ L η v hv0 hη harea hpos hneg t ht
  have hfun : (fun ω => η ω (t ω)) = (fun ω => L ω (v ω (t ω))) :=
    funext fun ω => hη ω (t ω)
  rw [hfun]
  exact hL.comp (measurable_id.prodMk hv)

end LatticeProb.LQG
