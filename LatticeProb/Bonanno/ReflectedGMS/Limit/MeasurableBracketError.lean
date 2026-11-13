/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.MeasurableBracketError at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.ContinuousTimeMaximal
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# A measurable compact-time bracket error

The pointwise supremum over an uncountable time interval need not be visibly
measurable from deterministic-time measurability.  We therefore take the
supremum over one fixed countable dense set, together with the terminal time.
On continuous paths this equals the full compact-time supremum.  Encoding the
countable supremum first in `ℝ≥0∞` makes it measurable without a pointwise
boundedness premise; monotonicity and nonnegativity of an actual diagonal
bracket then show that it is finite on the almost-sure path event.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- One fixed countable dense set of nonnegative observation times. -/
noncomputable def bracketDenseTimes : Set ℝ≥0 :=
  Classical.choose (TopologicalSpace.exists_countable_dense ℝ≥0)

theorem bracketDenseTimes_countable : bracketDenseTimes.Countable :=
  (Classical.choose_spec (TopologicalSpace.exists_countable_dense ℝ≥0)).1

theorem bracketDenseTimes_dense : Dense bracketDenseTimes :=
  (Classical.choose_spec (TopologicalSpace.exists_countable_dense ℝ≥0)).2

/-- The countable observation set before `T`, with `T` included explicitly. -/
noncomputable def compactBracketTimes (T : ℝ≥0) : Set ℝ≥0 :=
  insert T (bracketDenseTimes ∩ Iic T)

theorem compactBracketTimes_countable (T : ℝ≥0) :
    (compactBracketTimes T).Countable :=
  (bracketDenseTimes_countable.mono inter_subset_left).insert T

theorem compactBracketTimes_le (T : ℝ≥0) {t : ℝ≥0}
    (ht : t ∈ compactBracketTimes T) : t ≤ T := by
  rcases ht with rfl | ht
  · exact le_rfl
  · exact ht.2

/-- Extended countable supremum of the bracket discrepancy.  This auxiliary
quantity is allowed to be infinite off the regular path event. -/
noncomputable def uniformBracketErrorENNReal
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (v : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ t : compactBracketTimes T,
    ENNReal.ofReal |B t.1 ω - v * (t.1 : ℝ)|

/-- A real-valued measurable version of the compact-time uniform bracket
error.  On an exceptional path where the extended supremum is infinite,
`ENNReal.toReal` assigns zero; all domination claims below are made on the
almost-sure continuous, monotone, nonnegative path event. -/
noncomputable def measurableUniformBracketError
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (v : ℝ) (ω : Ω) : ℝ :=
  (uniformBracketErrorENNReal B T v ω).toReal

theorem measurable_measurableUniformBracketError
    {B : ℝ≥0 → Ω → ℝ} (T : ℝ≥0) (v : ℝ)
    (hB : ∀ t, Measurable (B t)) :
    Measurable (measurableUniformBracketError B T v) := by
  letI : Countable (compactBracketTimes T) :=
    (compactBracketTimes_countable T).to_subtype
  apply ENNReal.measurable_toReal.comp
  apply Measurable.iSup
  intro t
  have hsub : Measurable (fun b => B t.1 b - v * (t.1 : ℝ)) :=
    (measurable_sub_const (v * (t.1 : ℝ))).comp (hB t.1)
  apply ENNReal.measurable_ofReal.comp
  exact continuous_abs.measurable.comp hsub

theorem measurableUniformBracketError_nonneg
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (v : ℝ) (ω : Ω) :
    0 ≤ measurableUniformBracketError B T v ω :=
  ENNReal.toReal_nonneg

/-- Monotonicity and nonnegativity of the diagonal bracket make the extended
countable supremum finite. -/
theorem uniformBracketErrorENNReal_ne_top
    {B : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {v : ℝ} {ω : Ω}
    (hm : Monotone (fun t => B t ω)) (h0 : ∀ t, 0 ≤ B t ω) :
    uniformBracketErrorENNReal B T v ω ≠ ∞ := by
  have hbound : uniformBracketErrorENNReal B T v ω ≤
      ENNReal.ofReal (B T ω + |v| * (T : ℝ)) := by
    apply iSup_le
    intro t
    apply ENNReal.ofReal_le_ofReal
    have ht : t.1 ≤ T := compactBracketTimes_le T t.2
    have htR : (t.1 : ℝ) ≤ T := by exact_mod_cast ht
    calc
      |B t.1 ω - v * (t.1 : ℝ)| ≤ |B t.1 ω| + |v * (t.1 : ℝ)| := abs_sub _ _
      _ = B t.1 ω + |v| * (t.1 : ℝ) := by
        rw [abs_of_nonneg (h0 t.1), abs_mul,
          abs_of_nonneg (show 0 ≤ (t.1 : ℝ) from t.1.2)]
      _ ≤ B T ω + |v| * (T : ℝ) :=
        add_le_add (hm ht) (mul_le_mul_of_nonneg_left htR (abs_nonneg v))
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound

/-- On a continuous, monotone, nonnegative bracket path, the measurable
countable supremum dominates the discrepancy at every time up to `T`. -/
theorem bracket_error_le_measurableUniformBracketError
    {B : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {v : ℝ} {ω : Ω}
    (hc : Continuous (fun t => B t ω))
    (hm : Monotone (fun t => B t ω)) (h0 : ∀ t, 0 ≤ B t ω)
    (t : ℝ≥0) (ht : t ≤ T) :
    |B t ω - v * (t : ℝ)| ≤ measurableUniformBracketError B T v ω := by
  let f : ℝ≥0 → ℝ := fun s => |B s ω - v * (s : ℝ)|
  have hf : Continuous f := by
    fun_prop
  have htop : uniformBracketErrorENNReal B T v ω ≠ ∞ :=
    uniformBracketErrorENNReal_ne_top hm h0
  by_contra hle
  have hlt : measurableUniformBracketError B T v ω < f t :=
    lt_of_not_ge hle
  let ε : ℝ := (measurableUniformBracketError B T v ω + f t) / 2
  have hEε : measurableUniformBracketError B T v ω < ε := by
    dsimp only [ε]
    linarith
  have hεt : ε < f t := by
    dsimp only [ε]
    linarith
  obtain ⟨s, hs, hεs⟩ :=
    (rightContinuous_exceedance_dense hf.isRightContinuous
      bracketDenseTimes_dense T ε).mp
      ⟨t, ⟨zero_le, ht⟩, hεt⟩
  have hsle : ENNReal.ofReal (f s) ≤ uniformBracketErrorENNReal B T v ω := by
    exact le_iSup (fun q : compactBracketTimes T =>
      ENNReal.ofReal |B q.1 ω - v * (q.1 : ℝ)|) ⟨s, hs⟩
  have hsE : f s ≤ measurableUniformBracketError B T v ω := by
    calc
      f s = (ENNReal.ofReal (f s)).toReal := by
        rw [ENNReal.toReal_ofReal]
        exact abs_nonneg _
      _ ≤ (uniformBracketErrorENNReal B T v ω).toReal :=
        ENNReal.toReal_mono htop hsle
      _ = measurableUniformBracketError B T v ω := rfl
  linarith

/-- A positive level reached by the countable supremum is already exceeded at
one compact-time observation.  This pointwise statement also covers irregular
paths, since an infinite extended supremum is sent to zero. -/
theorem measurableUniformBracketError_level_subset
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (v ε : ℝ) (hε : 0 < ε) :
    {ω | ε ≤ measurableUniformBracketError B T v ω} ⊆
      {ω | ∃ t ∈ Icc (0 : ℝ≥0) T,
        ε / 2 < |B t ω - v * (t : ℝ)|} := by
  intro ω hω
  change ε ≤ measurableUniformBracketError B T v ω at hω
  have hhalf : ε / 2 < measurableUniformBracketError B T v ω := by
    linarith
  have htop : uniformBracketErrorENNReal B T v ω ≠ ∞ := by
    intro h
    simp [measurableUniformBracketError, h] at hω
    exact (not_le_of_gt hε) hω
  have hsup : ENNReal.ofReal (ε / 2) < uniformBracketErrorENNReal B T v ω := by
    rw [← ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top htop,
      ENNReal.toReal_ofReal (le_of_lt (half_pos hε))]
    exact hhalf
  obtain ⟨t, ht⟩ := lt_iSup_iff.mp hsup
  refine ⟨t.1, ⟨zero_le, compactBracketTimes_le T t.2⟩, ?_⟩
  exact (ENNReal.ofReal_lt_ofReal_iff'.mp ht).1

/-- The conventional ucp event bound implies convergence in measure of the
measurable countable-supremum errors. -/
theorem measurableUniformBracketError_tendstoInMeasure
    {P : Measure Ω} {B : ℕ → ℝ≥0 → Ω → ℝ} (T : ℝ≥0) (v : ℝ)
    (hucp : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      P {ω | ∃ t ∈ Icc (0 : ℝ≥0) T,
        ε < |B n t ω - v * (t : ℝ)|}) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n => measurableUniformBracketError (B n) T v)
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hbound := hucp (ε / 2) (half_pos hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => zero_le) ?_
  intro n
  apply measure_mono
  intro ω hω
  apply measurableUniformBracketError_level_subset (B n) T v ε hε
  change ε ≤ dist (measurableUniformBracketError (B n) T v ω) 0 at hω
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (measurableUniformBracketError_nonneg (B n) T v ω)] at hω
  exact hω

/-- Measurable realization of the compact-time uniform bracket error required
by localization.  Continuity, monotonicity, and nonnegativity are only assumed
almost surely, so the exceptional-path value chosen by `toReal` is irrelevant. -/
theorem exists_measurable_uniform_bracket_error
    {P : Measure Ω} {B : ℕ → ℝ≥0 → Ω → ℝ} (T : ℝ≥0) (v : ℝ)
    (hB : ∀ n t, Measurable (B n t))
    (hc : ∀ n, ∀ᵐ ω ∂P, Continuous (fun t => B n t ω))
    (hm : ∀ n, ∀ᵐ ω ∂P, Monotone (fun t => B n t ω))
    (h0 : ∀ n, ∀ᵐ ω ∂P, ∀ t, 0 ≤ B n t ω)
    (hucp : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      P {ω | ∃ t ∈ Icc (0 : ℝ≥0) T,
        ε < |B n t ω - v * (t : ℝ)|}) atTop (𝓝 0)) :
    ∃ E : ℕ → Ω → ℝ,
      (∀ n, AEStronglyMeasurable (E n) P) ∧
      (∀ n, ∀ᵐ ω ∂P, 0 ≤ E n ω) ∧
      (∀ n, ∀ᵐ ω ∂P, ∀ t ≤ T,
        |B n t ω - v * (t : ℝ)| ≤ E n ω) ∧
      TendstoInMeasure P E atTop (fun _ => 0) := by
  refine ⟨fun n => measurableUniformBracketError (B n) T v,
    fun n => (measurable_measurableUniformBracketError T v (hB n)).aestronglyMeasurable,
    fun n => Filter.Eventually.of_forall
      (measurableUniformBracketError_nonneg (B n) T v), ?_,
    measurableUniformBracketError_tendstoInMeasure T v hucp⟩
  intro n
  filter_upwards [hc n, hm n, h0 n] with ω hωc hωm hω0
  exact fun t ht => bracket_error_le_measurableUniformBracketError
    hωc hωm hω0 t ht

end ReflectedGMS.MartingaleLimit
