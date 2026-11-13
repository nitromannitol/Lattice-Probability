import LatticeProb.LQG.MatingOfTreesCouplingLaw

/-!
# The imaginary-geometry clause of a mating-of-trees coupling: law transfer, first part

The `igMap` clause of a mating-of-trees coupling says that the space-filling curve `η_L` is a
measurable function `Φ` of the circle-average process `(ρ, w) ↦ h^IG_ρ(w) + U` of the shifted
imaginary geometry field, together with a coordinate-change rule and a locality rule. This file
proves the parts of its law transfer that do not involve hitting times of the curve.

* `CouplingData.igCircleAvg`: the circle-average process `(ρ, w) ↦ h^IG_ρ(w) + U` of the data, a
  measurable function of the data (`measurable_igCircleAvg`).
* `measurable_igPullback`, `measurable_restrictCircles`: the coordinate change of circle-average
  processes and their restriction to circles inside a set are measurable maps of processes.
* `continuous_excursionSegment`: an excursion segment of a continuous curve is continuous in time.
* `ae_ηL_eq_igCircleAvg_of_map_eq`, `IsCouplingData.ae_ηL_eq_of_map_eq`: the identity `η_L = Φ(h^IG + U)` passes, with the same
  measurable `Φ`, to every random element of the data space with the same law.
* `MeasureTheory.dyadicRegularize`: the regularization of a family of functions of time by limits
  along the dyadic approximations `⌊u 2ⁿ⌋ / 2ⁿ` from below. It is measurable when the family is
  (`measurable_dyadicRegularize`) and it agrees with every continuous function that agrees with
  the family at dyadic times (`eq_dyadicRegularize_of_eq`).
* `MeasureTheory.ae_eq_dyadicRegularize_of_map_eq`: an almost sure identity between continuous
  functions of time `S(V)` and the values `g(G(V))` of a measurable family passes to every random
  element `V'` with the law of `V`, with `g` replaced by its dyadic regularization. The identity
  of functions of time is not an event in general (the family `g` is measurable only for the
  product σ-algebra), but its restriction to dyadic times is, and continuity recovers the rest.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace MeasureTheory

/-- The dyadic approximation `⌊u 2ⁿ⌋ / 2ⁿ` of a real number `u` from below. -/
def dyadicFloor (n : ℕ) (u : ℝ) : ℝ := (⌊u * 2 ^ n⌋ : ℝ) / 2 ^ n

theorem dyadicFloor_le (n : ℕ) (u : ℝ) : dyadicFloor n u ≤ u := by
  unfold dyadicFloor
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

theorem sub_le_dyadicFloor (n : ℕ) (u : ℝ) : u - (1 / 2 : ℝ) ^ n ≤ dyadicFloor n u := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  unfold dyadicFloor
  rw [le_div_iff₀ hp]
  have h1 := Int.lt_floor_add_one (u * 2 ^ n)
  have e : (u - (1 / 2 : ℝ) ^ n) * 2 ^ n = u * 2 ^ n - 1 := by
    rw [sub_mul, one_div, inv_pow, inv_mul_cancel₀ hp.ne']
  rw [e]
  linarith

/-- The dyadic approximations `⌊u 2ⁿ⌋ / 2ⁿ` converge to `u`. -/
theorem tendsto_dyadicFloor (u : ℝ) : Tendsto (fun n => dyadicFloor n u) atTop (𝓝 u) := by
  have h1 : Tendsto (fun n : ℕ => u - (1 / 2 : ℝ) ^ n) atTop (𝓝 u) := by
    have := (tendsto_const_nhds (x := u)).sub
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    rwa [sub_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds (sub_le_dyadicFloor · u)
    (dyadicFloor_le · u)

variable {α ι E : Type*} [TopologicalSpace E] [Nonempty E]

/-- The **dyadic regularization** of a family `g` of functions of time: at time `u`, the limit of
the values of `g` at the dyadic approximations of `u` from below (a junk value when the limit does
not exist). -/
def dyadicRegularize (g : α → ι → ℝ → E) : α → ι → ℝ → E :=
  fun a i u => limUnder atTop fun n => g a i (dyadicFloor n u)

/-- A continuous function of time which agrees with a family at all dyadic times agrees with its
dyadic regularization everywhere. -/
theorem eq_dyadicRegularize_of_eq [T2Space E] {g : α → ι → ℝ → E} {f : ℝ → E} (hf : Continuous f)
    {a : α} {i : ι} (h : ∀ (n : ℕ) (k : ℤ), f (k / 2 ^ n) = g a i (k / 2 ^ n)) :
    f = dyadicRegularize g a i := by
  funext u
  have ht : Tendsto (fun n => g a i (dyadicFloor n u)) atTop (𝓝 (f u)) :=
    ((hf.tendsto u).comp (tendsto_dyadicFloor u)).congr fun n => h n ⌊u * 2 ^ n⌋
  exact ht.limUnder_eq.symm

variable [MeasurableSpace α] [MeasurableSpace E] [PolishSpace E] [BorelSpace E]

/-- The dyadic regularization of a measurable family of functions of time is measurable (for the
product σ-algebras). -/
theorem measurable_dyadicRegularize {g : α → ι → ℝ → E} (hg : Measurable g) :
    Measurable (dyadicRegularize g) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun u => ?_
  have hgi : ∀ n : ℕ, Measurable fun a => g a i (dyadicFloor n u) := fun n =>
    (measurable_pi_apply (dyadicFloor n u)).comp ((measurable_pi_apply i).comp hg)
  exact (StronglyMeasurable.limUnder fun n => (hgi n).stronglyMeasurable).measurable

variable {Ω Ω' 𝒱 : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace 𝒱]
  {P : Measure Ω} {P' : Measure Ω'} {V : Ω → 𝒱} {V' : Ω' → 𝒱}

/-- **Law transfer of an identity of continuous functions of time.** Let `S(v)` be a countable
family of continuous functions of time, measurable in `v` at every time, and let `g` be a
measurable family of functions of time evaluated at a measurable function `G(v)`. If almost
surely `S(V)ᵢ = g(G(V))ᵢ` for all indices `i` with `p i`, then the same holds for every random
element `V'` with the law of `V`, with `g` replaced by its dyadic regularization. -/
theorem ae_eq_dyadicRegularize_of_map_eq [Countable ι] (hV : Measurable V) (hV' : Measurable V')
    (hlaw : P'.map V' = P.map V) {S : 𝒱 → ι → ℝ → E} (hS : ∀ i u, Measurable fun v => S v i u)
    (hSc : ∀ v i, Continuous (S v i)) {G : 𝒱 → α} (hG : Measurable G) {g : α → ι → ℝ → E}
    (hg : Measurable g) (p : ι → Prop) (h : ∀ᵐ ω ∂P, ∀ i, p i → S (V ω) i = g (G (V ω)) i) :
    ∀ᵐ ω ∂P', ∀ i, p i → S (V' ω) i = dyadicRegularize g (G (V' ω)) i := by
  let T : Set 𝒱 := {v | ∀ i, p i → ∀ (n : ℕ) (k : ℤ),
    S v i (k / 2 ^ n) = g (G v) i (k / 2 ^ n)}
  have hT : MeasurableSet T := by
    refine measurableSet_setOfPred.2 (Measurable.forall fun i => measurable_const.imp
      (Measurable.forall fun n => Measurable.forall fun k => ?_))
    exact measurableSet_setOfPred.1 (measurableSet_eq_fun (hS i ((k : ℝ) / 2 ^ n))
      ((measurable_pi_apply ((k : ℝ) / 2 ^ n)).comp ((measurable_pi_apply i).comp (hg.comp hG))))
  have hTP : ∀ᵐ ω ∂P, V ω ∈ T := by
    filter_upwards [h] with ω hω i hi n k
    rw [hω i hi]
  filter_upwards [ae_comp_of_map_eq hV hV' hlaw hT hTP] with ω hω i hi
  have hω' : ∀ i, p i → ∀ (n : ℕ) (k : ℤ),
      S (V' ω) i (k / 2 ^ n) = g (G (V' ω)) i (k / 2 ^ n) := hω
  exact eq_dyadicRegularize_of_eq (hSc _ i) (hω' i hi)

end MeasureTheory

namespace MatedCRTHarmonic
namespace MatedCRT

/-- The coordinate change of circle-average processes is a measurable map of processes. -/
theorem measurable_igPullback (γ : ℝ) (z₀ : ℂ) (s φ : ℝ) : Measurable (igPullback γ z₀ s φ) :=
  measurable_pi_iff.mpr fun ρ => measurable_pi_iff.mpr fun w => by
    have h1 : Measurable fun H : ℝ → ℂ → ℝ =>
        H (s * ρ) (z₀ + (s : ℂ) * Complex.exp (φ * Complex.I) * w) :=
      (measurable_pi_apply _).comp (measurable_pi_apply (s * ρ))
    exact h1.sub_const _

/-- The restriction of circle-average processes to the circles inside a set is a measurable map of
processes. -/
theorem measurable_restrictCircles (W : Set ℂ) : Measurable (restrictCircles W) := by
  refine measurable_pi_iff.mpr fun ρ => measurable_pi_iff.mpr fun w => ?_
  simp only [restrictCircles]
  exact Measurable.ite (MeasurableSet.const _)
    ((measurable_pi_apply w).comp (measurable_pi_apply ρ)) measurable_const

/-- An excursion segment of a continuous curve is a continuous function of time. -/
theorem continuous_excursionSegment (c : C(ℝ, ℂ)) (W : Set ℂ) (z : ℂ) :
    Continuous (excursionSegment c W z) :=
  c.continuous.comp (continuous_const.add (continuous_const.max (continuous_id.min continuous_const)))

namespace CouplingData

/-- The circle-average process `(ρ, w) ↦ h^IG_ρ(w) + U` of the shifted imaginary geometry field of
the data. -/
def igCircleAvg (v : CouplingData) : ℝ → ℂ → ℝ := fun ρ w => LQGMetric.circleAvg v.hIG ρ w + v.U

theorem measurable_igCircleAvg : Measurable igCircleAvg :=
  measurable_pi_iff.mpr fun ρ => measurable_pi_iff.mpr fun w =>
    ((LQGMetric.measurable_circleAvg_left ρ w).comp measurable_hIG).add measurable_U

end CouplingData

open CouplingData

variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
  {V : Ω → CouplingData} {V' : Ω' → CouplingData}

/-- **The curve as a function of the imaginary geometry field passes through the law.** If almost
surely `η_L = Φ(h^IG + U)` (circle-average processes) for a measurable `Φ`, the same holds, with
the same `Φ`, for every random element of the data space with the same law. -/
theorem ae_ηL_eq_igCircleAvg_of_map_eq (hV : Measurable V) (hV' : Measurable V') (hlaw : P'.map V' = P.map V)
    {Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ)} (hΦ : Measurable Φ)
    (h : ∀ᵐ ω ∂P, (V ω).ηL = Φ (V ω).igCircleAvg) :
    ∀ᵐ ω ∂P', (V' ω).ηL = Φ (V' ω).igCircleAvg :=
  ae_comp_of_map_eq hV hV' hlaw (measurableSet_eq_fun measurable_ηL (hΦ.comp measurable_igCircleAvg))
    h

/-- The `igMap` identity of a coupling `η_L = Φ(h^IG + U)` passes to every random element of the
data space with its law, with the witness `Φ` of the coupling. -/
theorem IsCouplingData.ae_ηL_eq_of_map_eq {γ : ℝ} (hC : IsCouplingData γ P V) (hV : Measurable V)
    (hV' : Measurable V') (hlaw : P'.map V' = P.map V) :
    ∃ Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ), Measurable Φ ∧
      (∀ K K' : ℝ → ℂ → ℝ, (∀ ρ : ℝ, 0 < ρ → K ρ = K' ρ) → Φ K = Φ K') ∧
      (∀ᵐ ω ∂P, (V ω).ηL = Φ (V ω).igCircleAvg) ∧ ∀ᵐ ω ∂P', (V' ω).ηL = Φ (V' ω).igCircleAvg := by
  obtain ⟨Φ, hΦ, hpos, hae, -⟩ :=
    (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC).igMap
  exact ⟨Φ, hΦ, hpos, hae, ae_ηL_eq_igCircleAvg_of_map_eq hV hV' hlaw hΦ hae⟩

end MatedCRT
end MatedCRTHarmonic
