/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSLemma27.Bookkeeping at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib

/-!
# Exponent bookkeeping for [18] Lemmas 2.7 and 2.8

Generic real-analysis helpers: probability bounds valid for small `δ` extend to `δ ∈ (0, 1)` after enlarging the
constant (`exists_bound_of_eventually`), outer-measure complements (`one_sub_le_measure_of_compl_le`), and the passage
from `o^∞` statements (`IsLittleO` against every power) to explicit bounds (`eventually_le_rpow_of_isLittleO`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal

namespace MatedCRTHarmonic.GMSLemma27

/-- A bound `g δ ≤ C₀ δ^e` for all small `δ > 0` extends to all `δ ∈ (0, 1)` with a larger constant, when `g ≤ 1`. -/
theorem exists_bound_of_eventually {g : ℝ → ℝ≥0∞} (hg : ∀ δ, g δ ≤ 1) {C₀ e : ℝ}
    (hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), g δ ≤ ENNReal.ofReal (C₀ * δ ^ e)) :
    ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1, g δ ≤ ENNReal.ofReal (C * δ ^ e) := by
  obtain ⟨δ₀, hδ₀, h⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hev
  set C : ℝ := max C₀ (max (δ₀ ^ (-e)) 1) with hC
  have hC1 : 1 ≤ C := le_max_of_le_right (le_max_right _ _)
  refine ⟨C, fun δ hδ => ?_⟩
  rcases lt_or_ge δ δ₀ with hlt | hge
  · refine (h ⟨hδ.1, hlt⟩).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hδ.1.le _)
  · refine (hg δ).trans ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rcases le_or_gt 0 e with he | he
    · have h1 : δ₀ ^ e ≤ δ ^ e := Real.rpow_le_rpow hδ₀.le hge he
      have h2 : δ₀ ^ (-e) * δ₀ ^ e = 1 := by
        rw [← Real.rpow_add hδ₀, neg_add_cancel, Real.rpow_zero]
      calc (1 : ℝ) = δ₀ ^ (-e) * δ₀ ^ e := h2.symm
        _ ≤ C * δ ^ e :=
          mul_le_mul (le_max_of_le_right (le_max_left _ _)) h1 (Real.rpow_nonneg hδ₀.le _)
            (zero_le_one.trans hC1)
    · have h1 : 1 ≤ δ ^ e := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ.1 hδ.2.le he.le
      calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
        _ ≤ C * δ ^ e := mul_le_mul hC1 h1 zero_le_one (zero_le_one.trans hC1)

/-- `P(s) ≥ 1 − x` whenever `P(sᶜ) ≤ x` (outer measures, no measurability needed). -/
theorem one_sub_le_measure_of_compl_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s : Set Ω} {x : ℝ≥0∞} (h : P sᶜ ≤ x) : 1 - x ≤ P s := by
  have h1 : (1 : ℝ≥0∞) ≤ P s + P sᶜ := by
    rw [← measure_univ (μ := P), ← union_compl_self s]
    exact measure_union_le _ _
  rw [tsub_le_iff_right]
  exact h1.trans (by gcongr)

/-- A real bound on `(P s).toReal` gives the `ENNReal` bound (probability measures). -/
theorem measure_le_ofReal_of_toReal_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {s : Set Ω} {x : ℝ} (h : (P s).toReal ≤ x) : P s ≤ ENNReal.ofReal x := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top P s)]
  exact ENNReal.ofReal_le_ofReal h

/-- From `f = o(ε^s)` as `ε → 0⁺`: eventually `f ε ≤ ε^s`. -/
theorem eventually_le_rpow_of_isLittleO {f : ℝ → ℝ} {s : ℝ}
    (h : f =o[𝓝[>] (0 : ℝ)] fun ε => ε ^ s) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε ≤ ε ^ s := by
  filter_upwards [h.bound one_pos, self_mem_nhdsWithin] with ε hε hpos
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hpos) _)]
    at hε
  exact (le_abs_self _).trans hε

/-- `ε ↦ ε^a` maps `𝓝[>] 0` to `𝓝[>] 0` for `a > 0`. -/
theorem tendsto_rpow_nhdsGT_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => ε ^ a) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h := (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto
    rw [Real.zero_rpow ha.ne'] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Real.rpow_pos_of_pos hε a

/-- `ε^a → 0` as `ε → 0⁺` for `a > 0`: eventually `ε^a < c` for each `c > 0`. -/
theorem eventually_rpow_lt {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ a < c :=
  (tendsto_rpow_nhdsGT_zero ha).mono_right nhdsWithin_le_nhds |>.eventually (gt_mem_nhds hc)

/-- Eventually `δ < c` as `δ → 0⁺`, for `c > 0`. -/
theorem eventually_lt_nhdsGT_zero {c : ℝ} (hc : 0 < c) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < c :=
  (show ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo 0 c from Ioo_mem_nhdsGT hc).mono fun _ h => h.2

end MatedCRTHarmonic.GMSLemma27
