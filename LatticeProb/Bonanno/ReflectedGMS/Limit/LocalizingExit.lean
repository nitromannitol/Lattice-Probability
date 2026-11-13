/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.LocalizingExit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.SquareMartingaleMaximal
import LatticeProb.Bonanno.ReflectedGMS.Process.MartingaleIngredients
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
Finite-horizon exit probabilities vanish along a genuine localizing sequence.
The proof uses existing a.e. continuity of measure from above and the actual
WithTop convergence to infinity. This is for each fixed process and horizon;
no uniform estimate over a family or common compensated-product localizer is
asserted.
-/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A genuine localizing sequence eventually stays beyond each fixed finite
horizon with probability tending to one. Almost-sure monotonicity suffices. -/
theorem localizing_exit_tendsto_zero
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {τ : ℕ → Ω → WithTop ℝ≥0}
    (hτ : IsLocalizingSequence F τ P) (T : ℝ≥0) :
    Tendsto (fun n => P {ω | τ n ω ≤ T}) atTop (𝓝 0) := by
  have hmeas : ∀ n, NullMeasurableSet {ω | τ n ω ≤ T} P :=
    fun n => (F.le T _ (hτ.isStoppingTime n T)).nullMeasurableSet
  have hae : ∀ᵐ ω ∂P, Antitone (fun n => ω ∈ {ω | τ n ω ≤ T}) := by
    filter_upwards [hτ.mono] with ω hω
    intro i j hij hj
    exact (hω hij).trans hj
  have hanti : Antitone (fun n => P {ω | τ n ω ≤ T}) := by
    intro i j hij
    apply measure_mono_ae
    filter_upwards [hae] with ω hω
    exact hω hij
  have hzero : P (⋂ n : ℕ, {ω | τ n ω ≤ T}) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hτ.tendsto_top] with ω hω hmem
    have he := (WithTop.tendsto_nhds_top_iff _).mp hω T
    obtain ⟨n, hn⟩ := eventually_atTop.mp he
    exact (hn n le_rfl).not_ge (Set.mem_iInter.mp hmem n)
  have hinf : (⨅ n : ℕ, P {ω | τ n ω ≤ T}) = 0 :=
    (measure_iInter_of_ae_antitone hae hmeas ⟨0, measure_ne_top _ _⟩).symm.trans hzero
  simpa only [hinf] using tendsto_atTop_iInf hanti

end ReflectedGMS.MartingaleLimit
