/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L7Indep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7Open
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatSupp
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseIndep

/-!
# DZZ Lemma 3.7: finite range of the band field (P2-DZZ3D, WP-113)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`) proof of Lemma 3.7, l. 992–999: the
events `𝓔_{B'_i, open}` are measurable w.r.t. `η^{ε²s}_{ts}(c̃)`, and "independent if
`|B'_i − B'_{i'}| ≥ κ ε s`", because (l. 999) `ε² s log(1/(ε² s)) ≤ ε s`: the band
`η^{b}_{·}(w)` only uses the white noise in `(·, b²) × B(w, r(b²))` (`r(u) = √u log u⁻¹/4 ∧ 1/10`).

* `etaRad_le_of_le`: `r(u) ≤ (√b log b⁻¹ + 2√b)/4` for `0 < u ≤ b ≤ 1` (own elementary bound,
  replacing the monotonicity of `√u log u⁻¹` on `(0, e^{-2}]`).
* `supportedIn_etaKernelL2_Ioo`: the band kernel at `w` is supported in `(a, b) × B(w, R)` when
  `r ≤ R` on `(a, b)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise KilledHeat

/-- `r(u) ≤ (√b log b⁻¹ + 2√b)/4` for `0 < u ≤ b ≤ 1`. -/
lemma etaRad_le_of_le {u b : ℝ} (hu : 0 < u) (hub : u ≤ b) (hb : b ≤ 1) :
    etaRad u ≤ (Real.sqrt b * Real.log b⁻¹ + 2 * Real.sqrt b) / 4 := by
  have hb0 : 0 < b := hu.trans_le hub
  refine (min_le_left _ _).trans ?_
  have hlogu : 0 ≤ Real.log u⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hu, hub.trans hb⟩)
  rw [abs_of_nonneg hlogu]
  refine div_le_div_of_nonneg_right ?_ (by norm_num)
  have hlogb : 0 ≤ Real.log b⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hb0, hb⟩)
  have hsplit : Real.log u⁻¹ = Real.log b⁻¹ + Real.log (b / u) := by
    rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
  have hsu : Real.sqrt u ≤ Real.sqrt b := Real.sqrt_le_sqrt hub
  -- `log(b/u) = 2 log √(b/u) ≤ 2 √(b/u)`
  have hq : 0 < Real.sqrt (b / u) := Real.sqrt_pos.2 (by positivity)
  have hlogq : Real.log (b / u) ≤ 2 * Real.sqrt (b / u) := by
    have e : Real.log (b / u) = 2 * Real.log (Real.sqrt (b / u)) := by
      rw [Real.log_sqrt (by positivity)]; ring
    rw [e]
    have := Real.log_le_sub_one_of_pos hq
    linarith
  have hmul : Real.sqrt u * Real.sqrt (b / u) = Real.sqrt b := by
    rw [← Real.sqrt_mul hu.le]; congr 1; field_simp
  rw [hsplit, mul_add]
  have h1 := mul_le_mul_of_nonneg_right hsu hlogb
  have h2 := mul_le_mul_of_nonneg_left hlogq (Real.sqrt_nonneg u)
  nlinarith

/-- The band kernel at `w` vanishes outside `(a, b) × B(w, R)` when `r ≤ R` on `(a, b)`. -/
theorem supportedIn_etaKernelL2_Ioo {a b R : ℝ} (ha : 0 < a)
    (hR : ∀ u ∈ Ioo a b, etaRad u ≤ R) (w : ℂ) :
    SupportedIn (Ioo a b ×ˢ Metric.ball w R) (etaKernelL2 (Ioo a b) w) := by
  have hm := memLp_etaKernel (I := Ioo a b) measurableSet_Ioo ha Ioo_subset_Ioi_self w
  unfold SupportedIn
  rw [etaKernelL2, dite_eq_left_of_eq_true (eq_true hm)]
  rw [ae_restrict_iff' (measurableSet_Ioo.prod Metric.isOpen_ball.measurableSet).compl]
  filter_upwards [hm.coeFn_toLp] with p hp hA
  rw [hp]
  by_cases h1 : p.1 ∈ Ioo a b
  · simp only [etaKernel, indicator_of_mem h1]
    by_cases h2 : p.2 ∈ Metric.ball w R
    · exact absurd (mk_mem_prod h1 h2) hA
    · have hp0 : (p.1 / 2).toNNReal ≠ 0 := by
        simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; linarith [h1.1]
      refine killedHeat_eq_zero_of_not_mem_right
        (LQGMetric.isOpen_openSquare.inter Metric.isOpen_ball) hp0 _ ?_
      intro hm2
      exact h2 (Metric.ball_subset_ball (hR _ h1) hm2.2)
  · simp [etaKernel, indicator_of_notMem h1]

lemma supportedIn_mono {A B : Set (ℝ × ℂ)} {f : WNSpace} (hf : SupportedIn A f) (h : A ⊆ B) :
    SupportedIn B f :=
  ae_restrict_of_ae_restrict_of_subset (compl_subset_compl.2 h) hf

/-- The space-time region used by the bands `η^{√b}_{√a}(w)`, `w ∈ S`, when `r ≤ R` on `(a, b)`. -/
def bandSupp (a b R : ℝ) (S : Finset ℂ) : Set (ℝ × ℂ) := Ioo a b ×ˢ ⋃ w ∈ S, Metric.ball w R

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

end DZZ
end LQGMetric
