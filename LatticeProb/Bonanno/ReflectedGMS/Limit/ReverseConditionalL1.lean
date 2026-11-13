/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ReverseConditionalL1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.ReverseConditionalL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
Reverse (decreasing sigma-field) L¹ convergence of conditional expectations.

`ReflectedGMS.MartingaleLimit.tendsto_eLpNorm_condExp_iInf` gives the L²
convergence `E[f | m n] → E[f | ⨅ k, m k]` for square-integrable `f`. The
temporal-homogenization consumers also average observables that are only
integrable, so the same tail limit is needed in L¹.

The transfer is the standard three-epsilon argument on top of that checked L²
theorem, using only existing approximation APIs:

* `eLpNorm_one_condExp_sub_le_of_approx` splits
  `E[f|m₁] - E[f|m₂]` into `E[f - g|m₁] - E[f - g|m₂]` plus `E[g|m₁] - E[g|m₂]`
  and controls the first part by `2 ‖f - g‖₁`, using mathlib's L¹ contraction
  `MeasureTheory.eLpNorm_condExp_le_eLpNorm`.
* `tendsto_eLpNorm_one_condExp_iInf_of_memLp_two` embeds the L² conclusion into
  L¹ by `eLpNorm_le_eLpNorm_mul_rpow_measure_univ`, which is finite because the
  measure is finite.
* `MeasureTheory.MemLp.exists_simpleFunc_eLpNorm_sub_lt` supplies the L¹-dense
  approximating simple functions, which are automatically in L² for a finite
  measure (`MeasureTheory.SimpleFunc.memLp_of_isFiniteMeasure`); no new
  truncation construction is introduced.

The limit is the honest tail conditional expectation `E[f | ⨅ k, m k]`, not an
unconditional mean; nothing here proves almost-everywhere convergence or any
tail triviality.
-/
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

/-- Three-epsilon splitting bound. The difference of two conditional expectations of an
integrable `f` is controlled by twice the L¹ distance from any integrable comparison
function `g` plus the corresponding difference for `g`. The ambient sigma-algebra `m0`
is declared last among the measurable-space binders so that it is the one carried by
`μ`. -/
theorem eLpNorm_one_condExp_sub_le_of_approx {Ω : Type*}
    {m₁ m₂ m0 : MeasurableSpace Ω} {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    eLpNorm (μ[f|m₁] - μ[f|m₂]) 1 μ ≤
      2 * eLpNorm (f - g) 1 μ + eLpNorm (μ[g|m₁] - μ[g|m₂]) 1 μ := by
  have key : μ[f|m₁] - μ[f|m₂] =ᵐ[μ]
      (μ[f - g|m₁] - μ[f - g|m₂]) + (μ[g|m₁] - μ[g|m₂]) := by
    filter_upwards [condExp_sub hf hg m₁, condExp_sub hf hg m₂] with ω h1 h2
    simp only [Pi.add_apply, Pi.sub_apply] at h1 h2 ⊢
    rw [h1, h2]
    ring
  rw [eLpNorm_congr_ae key]
  refine (eLpNorm_add_le le_rfl).trans ?_
  refine add_le_add ?_ le_rfl
  refine (eLpNorm_sub_le le_rfl).trans ?_
  rw [two_mul]
  exact add_le_add (eLpNorm_condExp_le_eLpNorm (m := m₁) (f - g) le_rfl)
    (eLpNorm_condExp_le_eLpNorm (m := m₂) (f - g) le_rfl)

/-- Reverse L¹ convergence for a square-integrable observable: the checked L² statement
`tendsto_eLpNorm_condExp_iInf` embeds into L¹ because the measure is finite. -/
theorem tendsto_eLpNorm_one_condExp_iInf_of_memLp_two {Ω : Type*}
    {m : ℕ → MeasurableSpace Ω} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    (hm : ∀ n, m n ≤ m0) (hmono : Antitone m) {g : Ω → ℝ} (hg : MemLp g 2 μ) :
    Tendsto (fun n => eLpNorm (μ[g|m n] - μ[g|⨅ k, m k]) 1 μ) atTop (𝓝 0) := by
  set C : ℝ≥0∞ := μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) with hCdef
  have hCtop : C ≠ ∞ := by
    rw [hCdef]
    exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top μ Set.univ)).ne
  have hbound : ∀ n, eLpNorm (μ[g|m n] - μ[g|⨅ k, m k]) 1 μ ≤
      eLpNorm (μ[g|m n] - μ[g|⨅ k, m k]) 2 μ * C := fun _ =>
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num)
      (integrable_condExp.sub integrable_condExp).aestronglyMeasurable
  have hmul : Tendsto (fun n => eLpNorm (μ[g|m n] - μ[g|⨅ k, m k]) 2 μ * C) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const (tendsto_eLpNorm_condExp_iInf hm hmono hg)
      (Or.inr hCtop)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul
    (fun _ => zero_le) hbound

/-- **Reverse L¹ convergence of conditional expectations.** For a finite measure, an
antitone sequence of sub-sigma-algebras and an integrable real observable `f`, the
conditional expectations `E[f | m n]` converge in L¹ to the tail conditional
expectation `E[f | ⨅ k, m k]`. Square integrability of `f` is not required. -/
theorem tendsto_eLpNorm_one_condExp_iInf {Ω : Type*}
    {m : ℕ → MeasurableSpace Ω} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    (hm : ∀ n, m n ≤ m0) (hmono : Antitone m) {f : Ω → ℝ} (hf : Integrable f μ) :
    Tendsto (fun n => eLpNorm (μ[f|m n] - μ[f|⨅ k, m k]) 1 μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hhalf : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
  have hquarter : ε / 2 / 2 ≠ 0 := (ENNReal.half_pos hhalf.ne').ne'
  obtain ⟨g, hgclose, -⟩ :=
    (memLp_one_iff_integrable.2 hf).exists_simpleFunc_eLpNorm_sub_lt ENNReal.one_ne_top hquarter
  have hgint : Integrable (⇑g) μ := g.integrable_of_isFiniteMeasure
  have hg2 : MemLp (⇑g) 2 μ := g.memLp_of_isFiniteMeasure 2 μ
  filter_upwards [ENNReal.tendsto_nhds_zero.1
    (tendsto_eLpNorm_one_condExp_iInf_of_memLp_two hm hmono hg2) (ε / 2) hhalf] with n hn
  calc eLpNorm (μ[f|m n] - μ[f|⨅ k, m k]) 1 μ
      ≤ 2 * eLpNorm (f - ⇑g) 1 μ + eLpNorm (μ[⇑g|m n] - μ[⇑g|⨅ k, m k]) 1 μ :=
        eLpNorm_one_condExp_sub_le_of_approx hf hgint
    _ ≤ 2 * (ε / 2 / 2) + ε / 2 := by
        gcongr <;> first | exact hgclose.le | exact hn
    _ = ε := by rw [two_mul, ENNReal.add_halves, ENNReal.add_halves]

end ReflectedGMS.MartingaleLimit
