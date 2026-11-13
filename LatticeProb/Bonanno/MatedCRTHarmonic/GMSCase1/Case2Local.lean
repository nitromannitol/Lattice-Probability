/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCase1.Case2Local at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase1.Transfer

/-!
# [18] Proposition 4.10, Case 2 from Case 1

Source: [18] : "We next establish (4.40) for
`ρ ∈ (0, 1)` and `h` replaced by the field `h₂ := h₁ − γ log max(|·|, 1) = h₀ − γ log|· − z|`.
Indeed, since `γ log max(|·|, 1)` is identically equal to `0` on `𝔻`, this case is immediate from
The preceding one", using that the event `G^ε_f(h; ρ)` is a.s. determined by `h|_{B_{ρ+4ε^q}(0)}`
and the imaginary geometry field.

Here: CANON's `Canon.case2Field` and `Canon.rootedField` have the **same restriction to every open
`V ⊆ 𝔻`** (`restrictTo_case2Field_eq`), so every event of the restricted data
`(h|_V, ((hIG₀, U), ηL))` has the same probability for `h₂` as for `h₁`; Case 1's Hölder bound
and its small-root conditional version follow (`case2_local_event_le`,
`case2_smallRoot_local_event_le`). The identification of the actual `G^ε_f` event with an event
of the restricted data is the locality statement of [18] Lemma 4.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSCase1

open LQGMetric MatedCRTHarmonic.MatedCRT

/-! ## The deterministic identity -/

/-- `γ log max(|·|, 1)` restricts to zero on every open subset of the unit disk. -/
theorem restrictTo_ofFunC_logMax_eq_zero (γ : ℝ) (V : Opens ℂ)
    (hV : (V : Set ℂ) ⊆ ball (0 : ℂ) 1) :
    restrictTo V (CellScaling.ofFunC fun w => γ * Real.log (max ‖w‖ 1)) = 0 := by
  refine DFunLike.ext _ _ fun φ => ?_
  change (CellScaling.ofFunC fun w => γ * Real.log (max ‖w‖ 1))
    (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) φ) = 0
  rw [CellScaling.ofFunC, Distribution.ofFun_apply_eq_ite]
  split_ifs
  · refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
    have hval : ((TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) φ : TestC) :
        ℂ → ℝ) x = φ x := by
      rw [TestFunction.monoCLM_apply]
      simp only [le_refl, le_top, and_self, ite_true]
    simp only [Pi.zero_apply, smul_eq_mul]
    rw [hval]
    by_cases hx : x ∈ (V : Set ℂ)
    · have hx1 : ‖x‖ < 1 := by simpa using hV hx
      rw [max_eq_right hx1.le, Real.log_one, mul_zero, mul_zero]
    · have h0 : φ x = 0 :=
        image_eq_zero_of_notMem_tsupport fun hs => hx (φ.tsupport_subset hs)
      rw [h0, zero_mul]
  · rfl

/-- **Case 2 = Case 1 on the unit disk.** The Case 2 field and the Case 1 field have the same
restriction to every open `V ⊆ 𝔻`. -/
theorem restrictTo_case2Field_eq (γ : ℝ) (V : Opens ℂ) (hV : (V : Set ℂ) ⊆ ball (0 : ℂ) 1)
    (h : DistC) (z : ℂ) :
    restrictTo V (Canon.case2Field γ h z) = restrictTo V (Canon.rootedField γ h z) := by
  have hsub : ∀ a b : DistC, restrictTo V (a - b) = restrictTo V a - restrictTo V b :=
    fun a b => ContinuousLinearMap.sub_comp _ _ _
  rw [Canon.case2Field, hsub, restrictTo_ofFunC_logMax_eq_zero γ V hV, sub_zero]

/-! ## Local events of the whole-plane data -/

/-- Restriction of the field coordinate of the whole-plane data to `V`. -/
def restrictData (V : Opens ℂ) (x : WPData) : DistOn V × AuxData := (restrictTo V x.1, x.2)

theorem measurable_restrictData (V : Opens ℂ) : Measurable (restrictData V) :=
  ((measurable_restrictTo V).comp measurable_fst).prodMk measurable_snd

/-- The Case 2 data `(h₂, ((hIG₀, U), ηL))` on the marked carrier. -/
def case2WPData {Ω : Type} (γ : ℝ) (X₀ hIG₀ : Ω → MatedCRT.Field) (U : Ω → ℝ)
    (ηL : Ω → C(ℝ, ℂ)) (v : Ω × ℂ) : WPData :=
  (Canon.case2Field γ (wpField X₀ v.1) v.2, wpAux hIG₀ U ηL v.1)

theorem restrictData_case2WPData {Ω : Type} (γ : ℝ) (X₀ hIG₀ : Ω → MatedCRT.Field)
    (U : Ω → ℝ) (ηL : Ω → C(ℝ, ℂ)) (V : Opens ℂ) (hV : (V : Set ℂ) ⊆ ball (0 : ℂ) 1)
    (v : Ω × ℂ) :
    restrictData V (case2WPData γ X₀ hIG₀ U ηL v) =
      restrictData V (rootedWPData γ X₀ hIG₀ U ηL v) := by
  simp only [restrictData, case2WPData, rootedWPData, rootedWPField,
    restrictTo_case2Field_eq γ V hV]

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

omit [MeasurableSpace Ω] in
/-- Local events of `h₂` on `V ⊆ 𝔻` are the same sets of marked samples as those of `h₁`. -/
theorem case2_local_preimage_eq (V : Opens ℂ) (hV : (V : Set ℂ) ⊆ ball (0 : ℂ) 1)
    (G : Set (DistOn V × AuxData)) :
    (fun v : Ω × ℂ => restrictData V (case2WPData γ X₀ hIG₀ U ηL v)) ⁻¹' G =
      rootedWPData γ X₀ hIG₀ U ηL ⁻¹' (restrictData V ⁻¹' G) := by
  ext v
  simp only [mem_preimage, restrictData_case2WPData γ X₀ hIG₀ U ηL V hV v]

/-- Case 2 for local events under the conditional law given `{z ∈ B_r(0)}`, `0 ≤ r ≤ 1`. -/
theorem case2_smallRoot_local_event_le
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (V : Opens ℂ) (hV : (V : Set ℂ) ⊆ ball (0 : ℂ) 1)
    {G : Set (DistOn V × AuxData)} (hG : MeasurableSet G)
    {p q : ℝ} (hpq : p.HolderConjugate q) {δ : ℝ≥0∞}
    (hbad : P ((fun ω => restrictData V (wpData X₀ hIG₀ U ηL ω)) ⁻¹' G) ≤ δ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (Canon.rootedLaw P)[|smallRootEvent Ω r]
        ((fun v : Ω × ℂ => restrictData V (case2WPData γ X₀ hIG₀ U ηL v)) ⁻¹' G) ≤
      case1Moment D hγ p ^ (1 / p) * δ ^ (1 / q) / ENNReal.ofReal (r ^ 2) := by
  rw [case2_local_preimage_eq V hV G]
  exact case1_smallRoot_event_le D hγ (measurable_restrictData V hG) hpq hbad hr0 hr1

end Coupling

end MatedCRTHarmonic.GMSCase1
