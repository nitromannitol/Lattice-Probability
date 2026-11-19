import LatticeProb.Prob.OccupationMeasureKernel

/-!
# Measurability of random Stieltjes measures on an arbitrary window

Let `Ω` be a measurable space and `F : Ω → StieltjesFunction ℝ` a family of Stieltjes functions with measurable
evaluations `ω ↦ F_ω(x)`. For every window `(x, y]`:

* `measurable_stieltjes_restrict_Ioc_window`: the restricted Lebesgue–Stieltjes measure `ω ↦ μ_{F_ω}|_{(x, y]}` is
  a measurable function of `ω` with values in `Measure ℝ` (a π-system argument on the intervals `Ioc l u`);
* `measurable_map_stieltjes_restrict_Ioc_window`: for a random continuous curve `γ` in a metrizable Borel space,
  the occupation measure `B ↦ ∫_{(x, y]} 1_B(γ_ω(s)) dF_ω(s)` is measurable in `ω`;
* `measurable_setLIntegral_stieltjes_Ioc_comp`: hence `ω ↦ ∫_{(x, y]} g(γ_ω(s)) dF_ω(s)` is measurable for every
  measurable `g ≥ 0`.

These extend the unit-window statements `measurable_stieltjes_restrict_Ioc` and
`measurable_map_stieltjes_restrict_Ioc`.
-/

open MeasureTheory ProbabilityTheory Set Filter Function TopologicalSpace
open scoped ENNReal Topology

namespace LatticeProb

section Window

variable {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [PseudoMetrizableSpace E] [MeasurableSpace E]
  [BorelSpace E]

/-- **The restriction of a random Stieltjes measure to a window is measurable.** For a family `F` of Stieltjes
functions with measurable evaluations and every window `(x, y]`, `ω ↦ μ_{F_ω}|_{(x, y]}` is measurable. -/
theorem measurable_stieltjes_restrict_Ioc_window (F : Ω → StieltjesFunction ℝ)
    (hF : ∀ x, Measurable fun ω => F ω x) (x y : ℝ) :
    Measurable fun ω => ((F ω).measure).restrict (Ioc x y) := by
  have hfin : ∀ ω, IsFiniteMeasure (((F ω).measure).restrict (Ioc x y)) := fun ω =>
    ⟨by rw [Measure.restrict_apply_univ, StieltjesFunction.measure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  refine Measurable.measure_of_isPiSystem (S := {S : Set ℝ | ∃ l u, l < u ∧ Ioc l u = S})
    ((BorelSpace.measurable_eq (α := ℝ)).trans (borel_eq_generateFrom_Ioc ℝ)) ?_ ?_ ?_
  · exact isPiSystem_Ioc (id : ℝ → ℝ) id
  · rintro s ⟨l, u, -, rfl⟩
    simp only [Measure.restrict_apply measurableSet_Ioc, Ioc_inter_Ioc, StieltjesFunction.measure_Ioc]
    exact ENNReal.measurable_ofReal.comp ((hF _).sub (hF _))
  · simp only [Measure.restrict_apply_univ, StieltjesFunction.measure_Ioc]
    exact ENNReal.measurable_ofReal.comp ((hF y).sub (hF x))

/-- **Measurability of occupation measures on a window.** For a measurable family `F` of Stieltjes functions, a
random continuous curve `γ` and a window `(x, y]`, the occupation measure
`B ↦ ∫_{(x, y]} 1_B(γ_ω(s)) dF_ω(s)` is a measurable function of `ω` with values in `Measure E`. -/
theorem measurable_map_stieltjes_restrict_Ioc_window (F : Ω → StieltjesFunction ℝ)
    (hF : ∀ x, Measurable fun ω => F ω x) (γ : Ω → ℝ → E) (hγc : ∀ ω, Continuous (γ ω))
    (hγm : ∀ s, Measurable fun ω => γ ω s) (x y : ℝ) :
    Measurable fun ω => (((F ω).measure).restrict (Ioc x y)).map (γ ω) := by
  have hν := measurable_stieltjes_restrict_Ioc_window F hF x y
  have hfin : ∀ ω, IsFiniteMeasure (((F ω).measure).restrict (Ioc x y)) := fun ω =>
    ⟨by rw [Measure.restrict_apply_univ, StieltjesFunction.measure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  let ν : Kernel Ω ℝ := ⟨_, hν⟩
  have hjoint : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => γ ω s) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => hγc ω) hγm
  refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
  have h := Kernel.measurable_kernel_prodMk_left_of_finite (κ := ν)
    (t := {p : Ω × ℝ | γ p.1 p.2 ∈ B}) (hjoint.comp measurable_swap hB) hfin
  have hfun : (fun ω => (((F ω).measure).restrict (Ioc x y)).map (γ ω) B) =
      fun ω => ν ω (Prod.mk ω ⁻¹' {p : Ω × ℝ | γ p.1 p.2 ∈ B}) :=
    funext fun ω => Measure.map_apply (hγc ω).measurable hB
  rw [hfun]
  exact h

/-- **The integral along a random curve against a random Stieltjes measure is measurable.** For a measurable
family `F` of Stieltjes functions, a random continuous curve `γ`, a window `(x, y]` and a measurable `g ≥ 0`,
`ω ↦ ∫_{(x, y]} g(γ_ω(s)) dF_ω(s)` is measurable. -/
theorem measurable_setLIntegral_stieltjes_Ioc_comp (F : Ω → StieltjesFunction ℝ)
    (hF : ∀ x, Measurable fun ω => F ω x) (γ : Ω → ℝ → E) (hγc : ∀ ω, Continuous (γ ω))
    (hγm : ∀ s, Measurable fun ω => γ ω s) (x y : ℝ) {g : E → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun ω => ∫⁻ s in Ioc x y, g (γ ω s) ∂(F ω).measure := by
  have hfun : (fun ω => ∫⁻ s in Ioc x y, g (γ ω s) ∂(F ω).measure) =
      fun ω => ∫⁻ e, g e ∂(((F ω).measure).restrict (Ioc x y)).map (γ ω) :=
    funext fun ω => (lintegral_map hg (hγc ω).measurable).symm
  rw [hfun]
  exact (Measure.measurable_lintegral hg).comp
    (measurable_map_stieltjes_restrict_Ioc_window F hF γ hγc hγm x y)

end Window

end LatticeProb
