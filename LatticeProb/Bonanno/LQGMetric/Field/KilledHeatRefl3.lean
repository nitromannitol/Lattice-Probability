/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatRefl3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatRefl2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Killed heat kernel, part 13: the bridge maximum in an interval (task P2-KILLED, D-KHK1)

DZZ (`LBM_LGDarXiv.tex` l. 491–499): for `0 < u ≤ v`,
`P(max_{s ≤ t} X^{(b)}_s ∈ [u, v]) = e^{−2u²/t} − e^{−2v²/t}` (`measureReal_bridge_max_mem_Icc`),
and the consequence `≤ 2(v − u)/√t` (`measureReal_bridge_max_mem_Icc_le`; DZZ's `C|u₁ − v₁|/√t`).
Derived from `measureReal_bridge_max_gt` by squeezing (`≥ a` versus `> a − ε`) and the
null-measurability of `{max > v}` (countably many rational times, continuity of the paths).
The Lipschitz bound is an own elementary estimate (`x e^{−x²} ≤ 1`, mean value theorem).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric
namespace KilledHeat

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `P(max_{s ≤ t} X^{(b)}_s ≥ a) = e^{−2a²/t}` for `a > 0`. -/
theorem measureReal_bridge_max_ge {t : ℝ≥0} (ht : t ≠ 0) {X : ℝ≥0 → Ω → ℂ} {P : Measure Ω}
    (hX : IsPlanarBridge t X P) (b : Bool) {a : ℝ} (ha : 0 < a) :
    P.real {ω | ∃ s : ℝ≥0, s ≤ t ∧ a ≤ coordProc X (b, s) ω} = Real.exp (-(2 * a ^ 2 / t)) := by
  have := hX.gauss.isProbabilityMeasure
  apply le_antisymm
  · have hup : ∀ ε ∈ Set.Ioo (0 : ℝ) a,
        P.real {ω | ∃ s : ℝ≥0, s ≤ t ∧ a ≤ coordProc X (b, s) ω} ≤
          Real.exp (-(2 * (a - ε) ^ 2 / t)) := by
      intro ε hε
      rw [← measureReal_bridge_max_gt ht hX b (by linarith [hε.2] : 0 < a - ε)]
      exact measureReal_mono fun ω ⟨s, hs, h⟩ ↦ ⟨s, hs, by linarith [hε.1]⟩
    have htend : Tendsto (fun ε : ℝ ↦ Real.exp (-(2 * (a - ε) ^ 2 / t))) (𝓝[>] 0)
        (𝓝 (Real.exp (-(2 * (a - 0) ^ 2 / t)))) :=
      ((by fun_prop : Continuous fun ε : ℝ ↦ Real.exp (-(2 * (a - ε) ^ 2 / t))).tendsto 0).mono_left
        nhdsWithin_le_nhds
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P.real {ω | ∃ s : ℝ≥0, s ≤ t ∧ a ≤ coordProc X (b, s) ω} ≤
        Real.exp (-(2 * (a - ε) ^ 2 / t)) := by
      filter_upwards [Ioo_mem_nhdsGT ha] with ε hε using hup ε hε
    have := ge_of_tendsto htend hev
    simpa using this
  · rw [← measureReal_bridge_max_gt ht hX b ha]
    exact measureReal_mono fun ω ⟨s, hs, h⟩ ↦ ⟨s, hs, h.le⟩

/-- `{max > v}` is null-measurable. -/
lemma nullMeasurableSet_bridge_max_gt {t : ℝ≥0} {X : ℝ≥0 → Ω → ℂ} {P : Measure Ω}
    (hX : IsPlanarBridge t X P) (b : Bool) (v : ℝ) :
    NullMeasurableSet {ω | ∃ s : ℝ≥0, s ≤ t ∧ v < coordProc X (b, s) ω} P := by
  have hC : NullMeasurableSet (⋃ q : ℚ, {ω | v < coordProc X (b, clampT t q) ω}) P :=
    NullMeasurableSet.iUnion fun q ↦
      nullMeasurableSet_lt aemeasurable_const (hX.gauss.aemeasurable _)
  refine hC.congr ?_
  filter_upwards [hX.cont] with ω hω
  apply propext
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨clampT t q, clampT_le t q, hq⟩
  · rintro ⟨s, hs, h⟩
    have hc : Continuous fun s : ℝ≥0 ↦ coordProc X (b, s) ω := by
      cases b
      · exact Complex.continuous_re.comp hω
      · exact Complex.continuous_im.comp hω
    let G : ℝ → ℝ := fun x ↦ coordProc X (b, min (Real.toNNReal x) t) ω
    have hG : Continuous G := hc.comp (continuous_real_toNNReal.min continuous_const)
    have hopen : IsOpen (G ⁻¹' Set.Ioi v) := isOpen_Ioi.preimage hG
    have hne : (G ⁻¹' Set.Ioi v).Nonempty := ⟨s, by simpa [G, min_eq_left hs] using h⟩
    obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open hopen hne
    exact ⟨q, hq⟩

/-- **DZZ l. 491–499**: `P(max_{s ≤ t} X^{(b)}_s ∈ [u, v]) = e^{−2u²/t} − e^{−2v²/t}`. -/
theorem measureReal_bridge_max_mem_Icc {t : ℝ≥0} (ht : t ≠ 0) {X : ℝ≥0 → Ω → ℂ}
    {P : Measure Ω} (hX : IsPlanarBridge t X P) (b : Bool) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    P.real ({ω | ∃ s : ℝ≥0, s ≤ t ∧ u ≤ coordProc X (b, s) ω} \
      {ω | ∃ s : ℝ≥0, s ≤ t ∧ v < coordProc X (b, s) ω}) =
      Real.exp (-(2 * u ^ 2 / t)) - Real.exp (-(2 * v ^ 2 / t)) := by
  have := hX.gauss.isProbabilityMeasure
  have hsub : {ω | ∃ s : ℝ≥0, s ≤ t ∧ v < coordProc X (b, s) ω} ⊆
      {ω | ∃ s : ℝ≥0, s ≤ t ∧ u ≤ coordProc X (b, s) ω} :=
    fun ω ⟨s, hs, h⟩ ↦ ⟨s, hs, by linarith⟩
  rw [measureReal_def, measure_sdiff hsub (nullMeasurableSet_bridge_max_gt hX b v)
    (measure_ne_top _ _), ENNReal.toReal_sub_of_le (measure_mono hsub) (measure_ne_top _ _),
    ← measureReal_def, ← measureReal_def, measureReal_bridge_max_ge ht hX b hu,
    measureReal_bridge_max_gt ht hX b (hu.trans_le huv)]

/-- `e^{−2u²/t} − e^{−2v²/t} ≤ 3(v − u)/√t` for `u ≤ v` (own elementary estimate). -/
lemma exp_sub_exp_le {t : ℝ} (ht : 0 < t) {u v : ℝ} (huv : u ≤ v) :
    Real.exp (-(2 * u ^ 2 / t)) - Real.exp (-(2 * v ^ 2 / t)) ≤ 3 * (v - u) / Real.sqrt t := by
  set f : ℝ → ℝ := fun x ↦ Real.exp (-(2 * x ^ 2 / t)) with hf
  have hderiv : ∀ x, HasDerivAt f (Real.exp (-(2 * x ^ 2 / t)) * (-(4 * x / t))) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ ↦ -(2 * x ^ 2 / t)) (-(4 * x / t)) x := by
      have := (((hasDerivAt_pow 2 x).const_mul 2).div_const t).neg
      exact this.congr_deriv (by norm_num; ring)
    exact h1.exp
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hbound : ∀ x, ‖Real.exp (-(2 * x ^ 2 / t)) * (-(4 * x / t))‖ ≤ 3 / Real.sqrt t := by
    intro x
    set y : ℝ := Real.sqrt 2 * |x| / Real.sqrt t with hy
    have hy0 : 0 ≤ y := by positivity
    have hy2 : y ^ 2 = 2 * x ^ 2 / t := by
      rw [hy, div_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt ht.le, sq_abs]
    have hkey : y * Real.exp (-(y ^ 2)) ≤ 1 := by
      have h := Real.add_one_le_exp (y ^ 2)
      have : y ≤ y ^ 2 + 1 := by nlinarith
      calc y * Real.exp (-(y ^ 2)) ≤ Real.exp (y ^ 2) * Real.exp (-(y ^ 2)) :=
            mul_le_mul_of_nonneg_right (this.trans h) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have h4 : |4 * x / t| = 2 * Real.sqrt 2 / Real.sqrt t * y := by
      have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      have hstt : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
      rw [hy, abs_div, abs_mul, abs_of_pos ht, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      field_simp
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt ht.le]
      ring
    have hs2le : Real.sqrt 2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_neg, ← hy2, h4]
    calc Real.exp (-(y ^ 2)) * (2 * Real.sqrt 2 / Real.sqrt t * y)
        = 2 * Real.sqrt 2 / Real.sqrt t * (y * Real.exp (-(y ^ 2))) := by ring
      _ ≤ 2 * Real.sqrt 2 / Real.sqrt t * 1 := by gcongr
      _ ≤ 2 * (3 / 2) / Real.sqrt t := by rw [mul_one]; gcongr
      _ = 3 / Real.sqrt t := by ring
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ ↦ (hderiv x).hasDerivWithinAt) (fun x _ ↦ hbound x) convex_univ
    (Set.mem_univ v) (Set.mem_univ u)
  have h2 : f u - f v ≤ 3 / Real.sqrt t * |u - v| :=
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
  rw [abs_of_nonpos (by linarith : u - v ≤ 0)] at h2
  calc Real.exp (-(2 * u ^ 2 / t)) - Real.exp (-(2 * v ^ 2 / t)) = f u - f v := rfl
    _ ≤ 3 / Real.sqrt t * -(u - v) := h2
    _ = 3 * (v - u) / Real.sqrt t := by ring

/-- DZZ's bound `P(max ∈ [u, v]) ≤ C |u − v| / √t` with `C = 3`. -/
theorem measureReal_bridge_max_mem_Icc_le {t : ℝ≥0} (ht : t ≠ 0) {X : ℝ≥0 → Ω → ℂ}
    {P : Measure Ω} (hX : IsPlanarBridge t X P) (b : Bool) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    P.real ({ω | ∃ s : ℝ≥0, s ≤ t ∧ u ≤ coordProc X (b, s) ω} \
      {ω | ∃ s : ℝ≥0, s ≤ t ∧ v < coordProc X (b, s) ω}) ≤ 3 * (v - u) / Real.sqrt t := by
  rw [measureReal_bridge_max_mem_Icc ht hX b hu huv]
  exact exp_sub_exp_le (lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm (by exact_mod_cast ht))) huv

end KilledHeat
end LQGMetric
