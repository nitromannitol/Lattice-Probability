/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ReverseConditionalMaximal at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! Weak-type (1,1) maximal control for conditional expectations along a
*decreasing* family of sub-sigma-fields.

For a decreasing family `ms` of sub-sigma-fields of `m0` and a fixed horizon
`N`, the reindexed family `k ↦ ms (N - k)` is an ordinary filtration, so
`k ↦ P[f | ms (N - k)]` is a genuine martingale by the tower property and its
absolute value is a nonnegative submartingale.  Doob's maximal inequality on
the finite prefix, followed by continuity from below of the measure, gives a
countable-supremum bound with the usual `(∫ |f|)/a` constant.

No reverse convergence statement is assumed or proved here; this only supplies
the maximal estimate. -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace ReflectedGMS.ReverseConditional

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- Reindex a decreasing family of sub-sigma-fields into an honest filtration on
`ℕ`: at index `k` it is `ms (N - k)`, which is constant equal to `ms 0` past
`N` because `ℕ`-subtraction truncates. -/
def reversedFiltration {ms : ℕ → MeasurableSpace Ω} (hanti : Antitone ms)
    (hle : ∀ n, ms n ≤ m0) (N : ℕ) : Filtration ℕ m0 where
  seq k := ms (N - k)
  mono' i j hij := hanti (by omega : N - j ≤ N - i)
  le' k := hle (N - k)

/-- The absolute value of the conditional expectations of a fixed function along
a filtration is a nonnegative submartingale: the tower property makes them a
martingale and conditional Jensen for `|·|` gives the submartingale inequality. -/
theorem submartingale_abs_condExp {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℕ m0} (f : Ω → ℝ) :
    Submartingale (fun k ω => |P[f | F k] ω|) F P := by
  refine ⟨fun k => continuous_abs.comp_stronglyMeasurable
      (stronglyMeasurable_condExp (m := F k) (μ := P) (f := f)),
    fun i j hij => ?_,
    fun k => Integrable.abs (integrable_condExp (m := F k) (μ := P) (f := f))⟩
  have htower : P[P[f | F j] | F i] =ᵐ[P] P[f | F i] :=
    condExp_condExp_of_le (F.mono hij) (F.le j)
  have hjensen := abs_condExp_ae_le_condExp_abs (μ := P) (m := F i) (P[f | F j])
  filter_upwards [htower, hjensen] with ω hω hj
  have habs : |P[f | F i] ω| = |P[P[f | F j] | F i] ω| := by rw [hω]
  rw [habs]
  exact hj

/-- Finite-prefix reverse maximal inequality: only the sub-sigma-fields
`ms 0, …, ms N` are involved, and the bound is Doob's with terminal value
`P[f | ms 0]`, itself an `L¹`-contraction of `f`. -/
theorem ofReal_mul_measure_exists_le_lt_abs_condExp_le {P : Measure Ω}
    [IsFiniteMeasure P] {ms : ℕ → MeasurableSpace Ω} (hanti : Antitone ms)
    (hle : ∀ n, ms n ≤ m0) (f : Ω → ℝ) {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ENNReal.ofReal a * P {ω | ∃ n ≤ N, a < |P[f | ms n] ω|} ≤
      ENNReal.ofReal (∫ ω, |f ω| ∂P) := by
  set F := reversedFiltration hanti hle N with hF
  have hsub : Submartingale (fun k ω => |P[f | F k] ω|) F P :=
    submartingale_abs_condExp f
  have hmax := maximal_ineq hsub (fun _ _ => abs_nonneg _) (ε := a.toNNReal) N
  have hacoe : ((a.toNNReal : ℝ≥0) : ℝ) = a := Real.coe_toNNReal a ha.le
  have hsubset : {ω | ∃ n ≤ N, a < |P[f | ms n] ω|} ⊆
      {ω | ((a.toNNReal : ℝ≥0) : ℝ) ≤ (Finset.range (N + 1)).sup'
        Finset.nonempty_range_add_one fun k => |P[f | F k] ω|} := by
    rintro ω ⟨n, hn, hlt⟩
    have hmem : N - n ∈ Finset.range (N + 1) :=
      Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.sub_le N n))
    have hidx : F (N - n) = ms n := by
      show ms (N - (N - n)) = ms n
      rw [Nat.sub_sub_self hn]
    simp only [Set.mem_setOf_eq, hacoe]
    calc a ≤ |P[f | ms n] ω| := hlt.le
      _ = |P[f | F (N - n)] ω| := by rw [hidx]
      _ ≤ _ := Finset.le_sup' (fun k => |P[f | F k] ω|) hmem
  have hofReal : ENNReal.ofReal a = (a.toNNReal : ℝ≥0∞) := rfl
  rw [hofReal]
  calc (a.toNNReal : ℝ≥0∞) * P {ω | ∃ n ≤ N, a < |P[f | ms n] ω|}
      ≤ (a.toNNReal : ℝ≥0∞) * P {ω | ((a.toNNReal : ℝ≥0) : ℝ) ≤
        (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          fun k => |P[f | F k] ω|} :=
        mul_le_mul' le_rfl (measure_mono hsubset)
    _ ≤ ENNReal.ofReal (∫ ω in {ω | ((a.toNNReal : ℝ≥0) : ℝ) ≤
        (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          fun k => |P[f | F k] ω|}, |P[f | F N] ω| ∂P) := hmax
    _ ≤ ENNReal.ofReal (∫ ω, |P[f | F N] ω| ∂P) :=
        ENNReal.ofReal_le_ofReal (setIntegral_le_integral integrable_condExp.abs
          (Eventually.of_forall fun _ => abs_nonneg _))
    _ ≤ ENNReal.ofReal (∫ ω, |f ω| ∂P) :=
        ENNReal.ofReal_le_ofReal (integral_abs_condExp_le (m := F N) f)

/-- Reverse weak-`L¹` maximal inequality: along any decreasing family of
sub-sigma-fields, the conditional expectations of an integrable `f` exceed the
level `a > 0` in absolute value, for *some* index, with probability at most
`(∫ |f|)/a`. -/
theorem measure_exists_lt_abs_condExp_le {P : Measure Ω} [IsFiniteMeasure P]
    {ms : ℕ → MeasurableSpace Ω} (hanti : Antitone ms) (hle : ∀ n, ms n ≤ m0)
    (f : Ω → ℝ) {a : ℝ} (ha : 0 < a) :
    P {ω | ∃ n, a < |P[f | ms n] ω|} ≤ ENNReal.ofReal ((∫ ω, |f ω| ∂P) / a) := by
  have hmono : Monotone fun N => {ω | ∃ n ≤ N, a < |P[f | ms n] ω|} := by
    rintro N M hNM ω ⟨n, hn, h⟩
    exact ⟨n, hn.trans hNM, h⟩
  have hun : ⋃ N, {ω | ∃ n ≤ N, a < |P[f | ms n] ω|} =
      {ω | ∃ n, a < |P[f | ms n] ω|} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨fun ⟨_, n, _, h⟩ => ⟨n, h⟩, fun ⟨n, h⟩ => ⟨n, n, le_rfl, h⟩⟩
  rw [← hun, hmono.measure_iUnion]
  refine iSup_le fun N => ?_
  rw [ENNReal.ofReal_div_of_pos ha, ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.2 ha).ne') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact ofReal_mul_measure_exists_le_lt_abs_condExp_le hanti hle f ha N

end ReflectedGMS.ReverseConditional
