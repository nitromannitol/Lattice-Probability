/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P18T2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18T1
import LatticeProb.Bonanno.LQGMetric.LFPP.Measurable
import LatticeProb.Bonanno.LQGDimension.LFPP.SegCombLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The LFPP events on squares are measurable in the rational circle averages

For the law transfer of DG:1774–1777 (`S3P18T1`) the event of `DGProp3_18Sq`,
`{max_{z,w ∈ S} D^δ(z,w; S(1/2)) ≤ t}` for `S = t18Sq c r`, has to be measurable in countably many
coordinates of the (continuous) field `φ = hc δ ·`. We use the points
`t18Pt c r q = c + r (q₁ + q₂ i)`, `q ∈ ℚ²`:

* a segment cost between two such points is the limit of Riemann sums whose sample points are
  again of this form (`t18Seg_eq`, LQGDimension's `SegLaw.tendsto_riemannSum`);
* on the convex square `S(1/2)` the LFPP distance is the infimum over polygonal chains with
  vertices in a countable dense set (`LFPP.lfppDOn_eq_iInf_chain`, the template
  `LFPP.lfppDistE_eq_chain`), here the points `t18Pt c r q` in `S(1/2)` (`t18DistR_eq`);
* the maximum over `z, w ∈ S` reduces to these points of `S` (short segments are cheap for a
  continuous field, as in `LFPP.iInf_sides_eq`) (`t18_event_iff`).

DG uses this measurability without comment. Own elementary argument (polygonal approximation).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

open LFPP

/-- the points `c + r (q₁ + q₂ i)` -/
def t18Pt (c : ℂ) (r : ℝ) (q : ℚ × ℚ) : ℂ := c + (r : ℂ) * ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)

/-- the `k/N` point of the rational segment from `u` to `v` -/
def t18qs (u v : ℚ × ℚ) (N k : ℕ) : ℚ × ℚ := u + ((k : ℚ) / N) • (v - u)

lemma t18Pt_qs (c : ℂ) (r : ℝ) (u v : ℚ × ℚ) (N k : ℕ) :
    t18Pt c r (t18qs u v N k) = segPath (t18Pt c r u) (t18Pt c r v) ((k : ℝ) / N) := by
  apply Complex.ext <;>
    simp [t18Pt, t18qs, segPath, Complex.real_smul] <;> ring

/-- Riemann sums of the segment cost in the coordinates `g` -/
def t18SegR (ξ : ℝ) (c : ℂ) (r : ℝ) (g : ℚ × ℚ → ℝ) (u v : ℚ × ℚ) (N : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ k ∈ Finset.range N,
    Real.exp (ξ * g (t18qs u v N k)) * ‖t18Pt c r v - t18Pt c r u‖)

/-- the segment cost in the coordinates `g` -/
def t18Seg (ξ : ℝ) (c : ℂ) (r : ℝ) (g : ℚ × ℚ → ℝ) (u v : ℚ × ℚ) : ℝ≥0∞ :=
  liminf (fun N => t18SegR ξ c r g u v N) atTop

lemma measurable_t18Seg (ξ : ℝ) (c : ℂ) (r : ℝ) (u v : ℚ × ℚ) :
    Measurable fun g : ℚ × ℚ → ℝ => t18Seg ξ c r g u v := by
  refine Measurable.liminf fun N => ?_
  refine Measurable.ennreal_ofReal (Measurable.const_mul ?_ _)
  exact Finset.measurable_sum _ fun k _ =>
    ((measurable_const.mul (measurable_pi_apply _)).exp).mul_const _

lemma t18_segCost_eq {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) (a b : ℂ) :
    segCost ξ φ a b =
      ENNReal.ofReal (∫ s in (0 : ℝ)..1, Real.exp (ξ * φ (segPath a b s)) * ‖b - a‖) := by
  have hseg : segPath a b = fun t : ℝ => a + (t : ℂ) * (b - a) := by
    funext t; simp [segPath, Complex.real_smul]
  have hp : IsDGPath univ a b (segPath a b) := by
    rw [hseg]; exact t18_isDGPath_segment convex_univ (mem_univ a) (mem_univ b)
  rw [segCost, ← t18_ofReal_lfppLength hφ hp]
  unfold LQGDimension.lfppLength
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [(hasDerivAt_segPath a b t).deriv]

lemma t18Seg_eq {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) (c : ℂ) (r : ℝ) (u v : ℚ × ℚ) :
    t18Seg ξ c r (fun q => φ (t18Pt c r q)) u v = segCost ξ φ (t18Pt c r u) (t18Pt c r v) := by
  set G : ℝ → ℝ := fun s => Real.exp (ξ * φ (segPath (t18Pt c r u) (t18Pt c r v) s)) *
    ‖t18Pt c r v - t18Pt c r u‖
  have hG : Continuous G := by
    have : Continuous (segPath (t18Pt c r u) (t18Pt c r v)) := by unfold segPath; fun_prop
    exact (Real.continuous_exp.comp (continuous_const.mul (hφ.comp this))).mul continuous_const
  have heq : ∀ N, t18SegR ξ c r (fun q => φ (t18Pt c r q)) u v N =
      ENNReal.ofReal (LQGDimension.SegLaw.riemannSum G N) := fun N => by
    simp only [t18SegR, LQGDimension.SegLaw.riemannSum, G, t18Pt_qs]
  have ht : Tendsto (fun N => t18SegR ξ c r (fun q => φ (t18Pt c r q)) u v N) atTop
      (𝓝 (segCost ξ φ (t18Pt c r u) (t18Pt c r v))) := by
    simp_rw [heq, t18_segCost_eq hφ]
    exact ENNReal.tendsto_ofReal (LQGDimension.SegLaw.tendsto_riemannSum hG)
  exact ht.liminf_eq

/-! ### Density of the rational points in squares -/

lemma t18_rat_near {M y ρ : ℝ} (hM : 0 < M) (hy : |y| ≤ M) (hρ : 0 < ρ) :
    ∃ q : ℚ, |(q : ℝ)| ≤ M ∧ |(q : ℝ) - y| < ρ := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max (-M) (y - ρ) < min M (y + ρ) by
    rw [abs_le] at hy
    refine max_lt (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith)))
  refine ⟨q, abs_le.2 ⟨(le_max_left _ _).trans hq1.le, hq2.le.trans (min_le_left _ _)⟩,
    abs_lt.2 ⟨by linarith [le_max_right (-M) (y - ρ)], by linarith [min_le_right M (y + ρ)]⟩⟩

lemma t18Pt_sub_re (c : ℂ) (r : ℝ) (q : ℚ × ℚ) : (t18Pt c r q - c).re = r * q.1 := by
  simp [t18Pt]

lemma t18Pt_sub_im (c : ℂ) (r : ℝ) (q : ℚ × ℚ) : (t18Pt c r q - c).im = r * q.2 := by
  simp [t18Pt]

/-- the points `t18Pt c r q` in `t18Sq c R` are dense in it -/
lemma t18Pt_dense {c : ℂ} {r R : ℝ} (hr : 0 < r) (hR : 0 < R) {x : ℂ} (hx : x ∈ t18Sq c R)
    {ρ : ℝ} (hρ : 0 < ρ) : ∃ q : ℚ × ℚ, t18Pt c r q ∈ t18Sq c R ∧ ‖t18Pt c r q - x‖ < ρ := by
  have hM : 0 < R / r := div_pos hR hr
  have h1 : |(x - c).re / r| ≤ R / r := by
    rw [abs_div, abs_of_pos hr]; exact div_le_div_of_nonneg_right hx.1 hr.le
  have h2 : |(x - c).im / r| ≤ R / r := by
    rw [abs_div, abs_of_pos hr]; exact div_le_div_of_nonneg_right hx.2 hr.le
  have hρ' : 0 < ρ / (2 * r) := by positivity
  obtain ⟨a, ha1, ha2⟩ := t18_rat_near hM h1 hρ'
  obtain ⟨b, hb1, hb2⟩ := t18_rat_near hM h2 hρ'
  have key : ∀ (q : ℚ) (y : ℝ), |(q : ℝ)| ≤ R / r → |r * q| ≤ R := fun q y hq => by
    rw [abs_mul, abs_of_pos hr]
    calc r * |(q : ℝ)| ≤ r * (R / r) := mul_le_mul_of_nonneg_left hq hr.le
      _ = R := by field_simp
  refine ⟨(a, b), ⟨?_, ?_⟩, ?_⟩
  · rw [t18Pt_sub_re]; exact key a 0 ha1
  · rw [t18Pt_sub_im]; exact key b 0 hb1
  · have e : t18Pt c r (a, b) - x = ((r * a - (x - c).re : ℝ) : ℂ) +
        ((r * b - (x - c).im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [t18Pt] <;> ring
    rw [e]
    refine (norm_add_le _ _).trans_lt ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have ea : r * a - (x - c).re = r * ((a : ℝ) - (x - c).re / r) := by field_simp
    have eb : r * b - (x - c).im = r * ((b : ℝ) - (x - c).im / r) := by field_simp
    rw [ea, eb, abs_mul, abs_mul, abs_of_pos hr]
    have : r * (ρ / (2 * r)) = ρ / 2 := by field_simp
    nlinarith

end LQGMetric.DG
