import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Measurability of occupation measures against random Stieltjes measures

Let `Ω` be a measurable space, `F : Ω → StieltjesFunction ℝ` a family of Stieltjes functions with measurable
evaluations `ω ↦ F_ω(x)`, and `γ : Ω → ℝ → E` a random continuous curve (each `γ ω` continuous, each `γ · s`
measurable) in a metrizable Borel space `E`.  The occupation measure of the curve `γ ω` on `(0, 1]` against the
Lebesgue–Stieltjes measure of `F_ω`,
`B ↦ ∫_{(0, 1]} 1_B(γ_ω(s)) dF_ω(s)`,
is a measurable function of `ω` with values in `Measure E` (`measurable_map_stieltjes_restrict_Ioc`).  The proof
checks that `ω ↦ μ_{F_ω}|_{(0,1]}` is a kernel (a π-system argument on the intervals `Ioc l u`) and applies the
measurability of sections of a jointly measurable set for kernels of finite measures.

`measurable_rightLim_of_monotone`: the right limit `x ↦ rightLim (a_ω) x` of a measurable family of monotone
functions is measurable in `ω`; it computes the Stieltjes function `Monotone.stieltjesFunction` of a family.
-/

open MeasureTheory ProbabilityTheory Set Filter Function TopologicalSpace
open scoped ENNReal Topology

namespace LatticeProb

section RightLim

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The right limit at `x` of a measurable family of monotone real functions is measurable in the parameter. -/
theorem measurable_rightLim_of_monotone {a : Ω → ℝ → ℝ} (hmono : ∀ ω, Monotone (a ω))
    (hmeas : ∀ y, Measurable fun ω => a ω y) (x : ℝ) :
    Measurable fun ω => Function.rightLim (a ω) x := by
  refine measurable_of_tendsto_metrizable (f := fun n : ℕ => fun ω => a ω (x + 1 / ((n : ℝ) + 1)))
    (fun n => hmeas _) ?_
  rw [tendsto_pi_nhds]
  intro ω
  have h1 : Tendsto (a ω) (𝓝[>] x) (𝓝 (Function.rightLim (a ω) x)) := (hmono ω).tendsto_rightLim x
  refine h1.comp ?_
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
  · have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h2.const_add x
  · simp only [mem_Ioi]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

end RightLim

section Occupation

variable {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [PseudoMetrizableSpace E] [MeasurableSpace E]
  [BorelSpace E]

/-- The Lebesgue–Stieltjes measures `μ_{F_ω}` restricted to `(0, 1]` form a measurable family. -/
theorem measurable_stieltjes_restrict_Ioc (F : Ω → StieltjesFunction ℝ)
    (hF : ∀ x, Measurable fun ω => F ω x) :
    Measurable fun ω => ((F ω).measure).restrict (Ioc (0 : ℝ) 1) := by
  have hfin : ∀ ω, IsFiniteMeasure (((F ω).measure).restrict (Ioc (0 : ℝ) 1)) := fun ω =>
    ⟨by rw [Measure.restrict_apply_univ, StieltjesFunction.measure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  refine Measurable.measure_of_isPiSystem (S := {S : Set ℝ | ∃ l u, l < u ∧ Ioc l u = S})
    ((BorelSpace.measurable_eq (α := ℝ)).trans (borel_eq_generateFrom_Ioc ℝ)) ?_ ?_ ?_
  · exact isPiSystem_Ioc (id : ℝ → ℝ) id
  · rintro s ⟨l, u, -, rfl⟩
    simp only [Measure.restrict_apply measurableSet_Ioc, Ioc_inter_Ioc, StieltjesFunction.measure_Ioc]
    exact ENNReal.measurable_ofReal.comp ((hF _).sub (hF _))
  · simp only [Measure.restrict_apply_univ, StieltjesFunction.measure_Ioc]
    exact ENNReal.measurable_ofReal.comp ((hF 1).sub (hF 0))

/-- **Measurability of occupation measures.**  For a measurable family `F` of Stieltjes functions and a random
continuous curve `γ`, the occupation measure `B ↦ ∫_{(0, 1]} 1_B(γ_ω(s)) dF_ω(s)` is a measurable function of `ω`
with values in `Measure E`. -/
theorem measurable_map_stieltjes_restrict_Ioc (F : Ω → StieltjesFunction ℝ)
    (hF : ∀ x, Measurable fun ω => F ω x) (γ : Ω → ℝ → E) (hγc : ∀ ω, Continuous (γ ω))
    (hγm : ∀ s, Measurable fun ω => γ ω s) :
    Measurable fun ω => (((F ω).measure).restrict (Ioc (0 : ℝ) 1)).map (γ ω) := by
  have hν := measurable_stieltjes_restrict_Ioc F hF
  have hfin : ∀ ω, IsFiniteMeasure (((F ω).measure).restrict (Ioc (0 : ℝ) 1)) := fun ω =>
    ⟨by rw [Measure.restrict_apply_univ, StieltjesFunction.measure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  let ν : Kernel Ω ℝ := ⟨_, hν⟩
  have hjoint : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => γ ω s) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => hγc ω) hγm
  refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
  have h := Kernel.measurable_kernel_prodMk_left_of_finite (κ := ν)
    (t := {p : Ω × ℝ | γ p.1 p.2 ∈ B}) (hjoint.comp measurable_swap hB) hfin
  have hfun : (fun ω => (((F ω).measure).restrict (Ioc (0 : ℝ) 1)).map (γ ω) B) =
      fun ω => ν ω (Prod.mk ω ⁻¹' {p : Ω × ℝ | γ p.1 p.2 ∈ B}) :=
    funext fun ω => Measure.map_apply (hγc ω).measurable hB
  rw [hfun]
  exact h

end Occupation

end LatticeProb
