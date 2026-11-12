/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P18S1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18R4
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L37V2
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF

/-!
# DG:1774–1775: P3.22 at every square by scaling (task P2-DG105s, DEC-118 P-118c step 4)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, proof of Prop 3.18
(DG:1774–1777): "by the scale and translation invariance of the law of `h` modulo additive
constant, the same holds for every square". For the square `t18Sq c r` put `R = 2r`,
`c₀ = c − r(1+i)`, `A y = R y + c₀` (`A 𝕊 = t18Sq c r`, `A 𝕊(1/2) = t18Sq c (2r)`). The field
`h' = h(A ·) − h_R(c₀)` is a normalized whole-plane GFF (`DFGPS.L36.isNormalizedWPGFF_rescale`)
and a.s. `H δ (A y) = H' (δ/R) y + H R c₀` for all `y` (`DFGPS.L36.ae_rescale_eq`), so
`D^δ_H(Az, Aw; t18Sq c (2r)) ≤ R e^{ξ H_R(c₀)} D^{δ/R}_{H'}(z, w; 𝕊(1/2))`
(`DFGPS.L36.lfppLength_affine`). The single Gaussian `H_R(c₀)` is bounded by `(ζ/4ξ) log δ⁻¹`
off an event of probability `≤ 2δ` (`s18_circleAvg_tail`, the radius-`R` form of
`L22T.circleAvg_tail`).

* **`dgProp3_18SqRef_of_unit : R18Unit → DGProp3_18SqRef`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

open Blueprint

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- the tail of `h_ρ(b)` for a normalized whole-plane GFF (radius-`ρ` form of
`L22T.circleAvg_tail`, same proof) -/
lemma s18_circleAvg_tail [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsNormalizedWPGFF h P)
    {ρ : ℝ} (hρ : 0 < ρ) (b : ℂ) :
    ∃ v : ℝ, 0 ≤ v ∧ ∀ A : ℝ, 0 ≤ A →
      P {ω | A / 2 < |circleAvg (h ω) ρ b|} ≤
        ENNReal.ofReal (2 * Real.exp (-(1 / (8 * (v + 1))) * A ^ 2)) := by
  obtain ⟨hmap, -⟩ := CircleAvg.map_cInc hh.1 hρ one_pos b 0
  set v := (CircleAvg.incCov b ρ 0 1 b ρ 0 1).toNNReal
  have hm := CircleAvg.measurable_cInc hh.1 ρ b 1 0
  have hae : (fun ω => circleAvg (h ω) ρ b) =ᵐ[P] CircleAvg.cInc h ρ b 1 0 := by
    filter_upwards [hh.2] with ω hω
    simp [CircleAvg.cInc, hω]
  refine ⟨v, v.2, fun A hA => ?_⟩
  have hS : P {ω | A / 2 < |circleAvg (h ω) ρ b|} =
      P (CircleAvg.cInc h ρ b 1 0 ⁻¹' {x | A / 2 < |x|}) := by
    refine measure_congr ?_
    filter_upwards [hae] with ω hω
    simp only [eq_iff_iff]
    show A / 2 < |circleAvg (h ω) ρ b| ↔ A / 2 < |CircleAvg.cInc h ρ b 1 0 ω|
    rw [hω]
  have hmeas : MeasurableSet {x : ℝ | A / 2 < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  rw [hS]
  rcases eq_or_lt_of_le (v.2 : (0 : ℝ) ≤ v) with hv | hv
  · have hv0 : v = 0 := NNReal.coe_injective hv.symm
    rw [← Measure.map_apply hm hmeas, hmap, hv0, gaussianReal_zero_var,
      Measure.dirac_apply' _ hmeas]
    simp only [mem_ofPred_eq, abs_zero, indicator, mem_ofPred_eq]
    split_ifs with h0
    · linarith
    · exact zero_le
  · have hL : HasLaw (CircleAvg.cInc h ρ b 1 0) (gaussianReal 0 v) P := ⟨hm.aemeasurable, hmap⟩
    have ht := DDDF.tail_abs_of_hasLaw hv hL (y := A / 2) (by positivity)
    have hle : P (CircleAvg.cInc h ρ b 1 0 ⁻¹' {x | A / 2 < |x|}) ≤
        P {ω | A / 2 ≤ |CircleAvg.cInc h ρ b 1 0 ω|} :=
      measure_mono fun ω (hω : A / 2 < |_|) => le_of_lt hω
    refine hle.trans ?_
    rw [← ofReal_measureReal (measure_ne_top P _)]
    refine ENNReal.ofReal_le_ofReal (ht.trans ?_)
    have hv' : (0 : ℝ) < v := hv
    have key : 1 / (8 * ((v : ℝ) + 1)) * A ^ 2 ≤ (A / 2) ^ 2 / (2 * v) := by
      rw [show (A / 2) ^ 2 / (2 * (v : ℝ)) = A ^ 2 / (8 * v) by field_simp; ring,
        one_div_mul_eq_div]
      exact div_le_div_of_nonneg_left (sq_nonneg A) (by positivity) (by linarith)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
    rw [neg_div, neg_mul]
    exact neg_le_neg key

/-- the base point `c₀ = c − r(1+i)` of the affine map `A y = 2r y + c₀` -/
def s18c0 (c : ℂ) (r : ℝ) : ℂ := c - (r : ℂ) * (1 + Complex.I)

lemma s18_A_re (c : ℂ) (r : ℝ) (y : ℂ) :
    (((2 * r : ℝ) : ℂ) * y + s18c0 c r - c).re = 2 * r * y.re - r := by
  simp [s18c0]; ring

lemma s18_A_im (c : ℂ) (r : ℝ) (y : ℂ) :
    (((2 * r : ℝ) : ℂ) * y + s18c0 c r - c).im = 2 * r * y.im - r := by
  simp [s18c0]; ring

/-- `A 𝕊(1/2) ⊆ t18Sq c (2r)` -/
lemma s18_A_half {c : ℂ} {r : ℝ} (hr : 0 < r) {y : ℂ} (hy : y ∈ p18Half) :
    ((2 * r : ℝ) : ℂ) * y + s18c0 c r ∈ t18Sq c (2 * r) := by
  simp only [p18Half, Complex.mem_reProdIm, mem_Icc] at hy
  refine ⟨?_, ?_⟩
  · rw [s18_A_re, abs_le]; constructor <;> nlinarith [hy.1.1, hy.1.2]
  · rw [s18_A_im, abs_le]; constructor <;> nlinarith [hy.2.1, hy.2.2]

/-- every `z ∈ t18Sq c r` is `A z'` with `z' ∈ 𝕊` -/
lemma s18_A_surj {c : ℂ} {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ t18Sq c r) :
    ∃ z' ∈ closedUnitSquare, ((2 * r : ℝ) : ℂ) * z' + s18c0 c r = z := by
  have hR : ((2 * r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * r : ℝ) ≠ 0)
  set z' := (z - s18c0 c r) / ((2 * r : ℝ) : ℂ)
  have hA : ((2 * r : ℝ) : ℂ) * z' + s18c0 c r = z := by
    simp only [z']; field_simp; ring
  refine ⟨z', ?_, hA⟩
  obtain ⟨h1, h2⟩ := hz
  rw [← hA, s18_A_re, abs_le] at h1
  rw [← hA, s18_A_im, abs_le] at h2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

lemma s18_half_convex : Convex ℝ p18Half :=
  ((convex_Icc _ _).linear_preimage Complex.reLm).inter
    ((convex_Icc _ _).linear_preimage Complex.imLm)

/-- **LFPP under `A`**: `D_Φ(Az, Aw; t18Sq c (2r)) ≤ 2r e^{ξa} D_φ(z, w; 𝕊(1/2))` when
`Φ ∘ A = φ + a` -/
lemma s18_dgLFPP_scale (ξ : ℝ) {c : ℂ} {r : ℝ} (hr : 0 < r) {Φ φ : ℂ → ℝ} {a : ℝ}
    (hφ : ∀ x, Φ (((2 * r : ℝ) : ℂ) * x + s18c0 c r) = φ x + a) {z w : ℂ}
    (hz : z ∈ closedUnitSquare) (hw : w ∈ closedUnitSquare) :
    dgLFPP ξ Φ (t18Sq c (2 * r)) (((2 * r : ℝ) : ℂ) * z + s18c0 c r)
        (((2 * r : ℝ) : ℂ) * w + s18c0 c r) ≤
      2 * r * Real.exp (ξ * a) * dgLFPP ξ φ p18Half z w := by
  have hK : 0 < 2 * r * Real.exp (ξ * a) := by positivity
  have hne : Nonempty {q : ℝ → ℂ // IsDGPath p18Half z w q} :=
    ⟨⟨_, t18_isDGPath_segment s18_half_convex (closedUnitSquare_sub_p18Half hz)
      (closedUnitSquare_sub_p18Half hw)⟩⟩
  rw [← div_le_iff₀' hK]
  refine le_ciInf fun q => ?_
  rw [div_le_iff₀' hK]
  have hp := DFGPS.L36.isDGPath_affine q.2 (2 * r) (s18c0 c r)
  have hS : (fun x => ((2 * r : ℝ) : ℂ) * x + s18c0 c r) '' p18Half ⊆ t18Sq c (2 * r) := by
    rintro _ ⟨y, hy, rfl⟩; exact s18_A_half hr hy
  have hp' : IsDGPath (t18Sq c (2 * r)) (((2 * r : ℝ) : ℂ) * z + s18c0 c r)
      (((2 * r : ℝ) : ℂ) * w + s18c0 c r) (fun t => ((2 * r : ℝ) : ℂ) * q.1 t + s18c0 c r) :=
    ⟨hp.source, hp.target, hp.mapsTo.mono_right hS, hp.continuousOn, hp.piecewise_contDiff⟩
  rw [← DFGPS.L36.lfppLength_affine (by positivity) (s18c0 c r) ξ a hφ q.1]
  exact ciInf_le (bddBelow_dg _ _ _ _ _) ⟨_, hp'⟩

end LQGMetric.DG
