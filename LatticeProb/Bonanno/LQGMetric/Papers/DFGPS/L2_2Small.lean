/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_2Small at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_3Tail
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.RTHmpBC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.2, small radii: logarithmic growth of the circle averages

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:790–792: "Standard estimates for
the maximum of the circle average process (see, e.g., the proof of [HMP, Lemma 3.1]) show that
a.s. `sup_{z ∈ B_R(0)} sup_{r ∈ (0,1/2]} |h_r(z)| / ((2+ζ) log(1/r)) < ∞`."

We follow the HMP argument (Hu–Miller–Peres, *Thick points of the Gaussian free field*, Ann.
Probab. 38 (2010), Prop. 2.1 (modulus) and the proof of Lemma 3.1: grid + union bound +
Borel–Cantelli), which is formalized in QuantumZipper as `RTHmp.hmp_ae_eventually_le` (Gaussian
families on countable parameter sets at scales `2^{-k}`). It yields the growth `≤ a (k + 1)` on
the `k`-th dyadic radius block with an explicit but non-optimal constant `a`, i.e. the bound with
some deterministic `A` in place of `2 + ζ` (DEV-DFGPS-1). Inputs: the variances
`Var(h_r(z) − h_1(0)) ≤ 2|log r| + 4|z|` and the modulus
`Var(h_r(z) − h_s(w)) ≤ 2(|r − s| + |z − w|)/min(r, s)` (`incCov_self_le`); rational parameters
and continuity of the version `H` pass the bound to all parameters.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace LQGMetric.DFGPS

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}

/-- the centre `θ₀ + iθ₁` -/
def hmpPt (θ : Fin 3 → ℝ) : ℂ := (θ 0 : ℂ) + (θ 1 : ℂ) * Complex.I
/-- the radius `θ₂` (made positive) -/
def hmpRad (θ : Fin 3 → ℝ) : ℝ := if 0 < θ 2 then θ 2 else 1

lemma hmpRad_pos (θ : Fin 3 → ℝ) : 0 < hmpRad θ := by
  unfold hmpRad; split_ifs with h <;> [exact h; exact one_pos]

lemma continuous_hmpPt : Continuous hmpPt := by unfold hmpPt; fun_prop

lemma norm_hmpPt_sub (θ θ' : Fin 3 → ℝ) : ‖hmpPt θ - hmpPt θ'‖ ≤ 2 * ‖θ - θ'‖ := by
  have e : hmpPt θ - hmpPt θ' = hmpPt (θ - θ') := by
    simp only [hmpPt, Pi.sub_apply]; push_cast; ring
  rw [e]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have h0 := norm_le_pi_norm (θ - θ') 0
  have h1 := norm_le_pi_norm (θ - θ') 1
  simp only [hmpPt, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im] at *
  rw [Real.norm_eq_abs] at h0 h1
  simp only [mul_zero, sub_zero, mul_one, add_zero, zero_add]
  linarith

/-- the increment `h_{θ₂}(θ₀ + iθ₁) − h_1(0)` -/
def hmpIdx (θ : Fin 3 → ℝ) : CircleAvg.IncIdx :=
  ((⟨hmpRad θ, hmpRad_pos θ⟩, hmpPt θ), (⟨1, mem_Ioi.2 one_pos⟩, 0))

/-- the open parameter set at scale `k`: `|z| < R + 1`, `2^{-k-2} < r < 2 · 2^{-k}` -/
def hmpU (R : ℝ) (k : ℕ) : Set (Fin 3 → ℝ) :=
  {θ | ‖hmpPt θ‖ < R + 1 ∧ QuantumZipper.radius (k + 2) < θ 2 ∧ θ 2 < 2 * QuantumZipper.radius k}

/-- rational parameters -/
def ratPts : Set (Fin 3 → ℝ) := range fun q : Fin 3 → ℚ => fun i => (q i : ℝ)

lemma dense_ratPts : Dense ratPts := by
  have := DenseRange.piMap (fun _ : Fin 3 => Rat.denseRange_cast (𝕜 := ℝ))
  exact this

lemma isOpen_hmpU (R : ℝ) (k : ℕ) : IsOpen (hmpU R k) := by
  refine ((isOpen_lt (continuous_norm.comp continuous_hmpPt) continuous_const).inter
    ((isOpen_lt continuous_const (continuous_apply 2)).inter
      (isOpen_lt (continuous_apply 2) continuous_const)))

lemma radius_pos' (k : ℕ) : 0 < QuantumZipper.radius k := by
  unfold QuantumZipper.radius; positivity

lemma radius_add (k j : ℕ) :
    QuantumZipper.radius (k + j) = QuantumZipper.radius k / 2 ^ j := by
  unfold QuantumZipper.radius; rw [pow_add, div_eq_mul_inv, inv_pow, inv_pow]

lemma abs_log_le_of_mem {R : ℝ} {k : ℕ} {θ : Fin 3 → ℝ} (hθ : θ ∈ hmpU R k) :
    |Real.log (θ 2)| ≤ k + 2 := by
  obtain ⟨-, h1, h2⟩ := hθ
  have hr := radius_pos' (k + 2)
  have h0 : 0 < θ 2 := hr.trans h1
  have hk : QuantumZipper.radius k ≤ 1 := by
    unfold QuantumZipper.radius; exact pow_le_one₀ (by norm_num) (by norm_num)
  rcases le_or_gt 1 (θ 2) with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    have := Real.log_le_sub_one_of_pos h0
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    linarith
  · rw [abs_of_neg (Real.log_neg h0 h)]
    have e : QuantumZipper.radius (k + 2) = (2 ^ (k + 2))⁻¹ := by
      unfold QuantumZipper.radius; rw [inv_pow]
    rw [e] at h1
    have : -Real.log (θ 2) < (k + 2) * Real.log 2 := by
      have := Real.log_lt_log (by positivity) h1
      rw [Real.log_inv, Real.log_pow] at this; push_cast at this; linarith
    have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    have : (k + 2 : ℝ) * Real.log 2 ≤ (k + 2) * 1 := by gcongr; linarith
    linarith

/-- variance of `h_r(z) − h_1(0)`: `≤ 2|log r| + 4|z|` -/
lemma variance_cInc_le (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Var[CircleAvg.cInc h r z 1 0; P] ≤ 2 * |Real.log r| + 4 * ‖z‖ := by
  have := hh.gaussian.isProbabilityMeasure
  have hG := CircleAvg.isGaussianProcess_incProc hh
  set X := CircleAvg.cInc h r z 1 z
  set Y := CircleAvg.cInc h 1 z 1 0
  have hX : MemLp X 2 P :=
    (hG.hasGaussianLaw_eval ((⟨r, hr⟩, z), (⟨1, mem_Ioi.2 one_pos⟩, z))).memLp_two
  have hY : MemLp Y 2 P :=
    (hG.hasGaussianLaw_eval ((⟨1, mem_Ioi.2 one_pos⟩, z), (⟨1, mem_Ioi.2 one_pos⟩, 0))).memLp_two
  have e : CircleAvg.cInc h r z 1 0 = fun ω => X ω + Y ω := by
    funext ω; simp only [X, Y, CircleAvg.cInc]; ring
  have hX0 : ∫ ω, X ω ∂P = 0 := CircleAvg.integral_cInc hh hr one_pos z z
  have hY0 : ∫ ω, Y ω ∂P = 0 := CircleAvg.integral_cInc hh one_pos one_pos z 0
  have hS0 : ∫ ω, (X ω + Y ω) ∂P = 0 := by
    rw [integral_add (hX.integrable one_le_two) (hY.integrable one_le_two), hX0, hY0, add_zero]
  rw [e, variance_of_integral_eq_zero (X := fun ω => X ω + Y ω)
    (hX.aestronglyMeasurable.aemeasurable.add hY.aestronglyMeasurable.aemeasurable) hS0]
  have vX : Var[X; P] = |Real.log r| := CircleAvg.variance_cInc_one hh hr z
  have vY : Var[Y; P] ≤ 2 * ‖z‖ := by
    rw [(CircleAvg.map_cInc hh one_pos one_pos z 0).2]
    have := CircleAvg.incCov_self_le one_pos one_pos z 0
    simpa using this
  rw [variance_of_integral_eq_zero hX.aestronglyMeasurable.aemeasurable hX0] at vX
  rw [variance_of_integral_eq_zero hY.aestronglyMeasurable.aemeasurable hY0] at vY
  calc ∫ ω, (X ω + Y ω) ^ 2 ∂P ≤ ∫ ω, (2 * X ω ^ 2 + 2 * Y ω ^ 2) ∂P := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
          ((hX.integrable_sq.const_mul 2).add (hY.integrable_sq.const_mul 2))
          (Eventually.of_forall fun ω => ?_)
        nlinarith [sq_nonneg (X ω - Y ω)]
    _ = 2 * ∫ ω, X ω ^ 2 ∂P + 2 * ∫ ω, Y ω ^ 2 ∂P := by
        rw [integral_add (hX.integrable_sq.const_mul 2) (hY.integrable_sq.const_mul 2),
          integral_const_mul, integral_const_mul]
    _ ≤ 2 * |Real.log r| + 4 * ‖z‖ := by rw [vX]; linarith

/-- **HMP growth on rational parameters** (QZ `RTHmp.hmp_ae_eventually_le`). -/
theorem hmp_rat_ae (hh : IsWholePlaneGFF h P) {R : ℝ} (hR : 0 ≤ R) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ θ ∈ hmpU R k ∩ ratPts,
      |CircleAvg.cInc h (hmpRad θ) (hmpPt θ) 1 0 ω| ≤
        QuantumZipper.R18.RTHmp.hmpA 3 (8 + 4 * R) * (k + 1) := by
  have := hh.gaussian.isProbabilityMeasure
  have hD : ∀ k, (hmpU R k ∩ ratPts).Countable := fun k =>
    (countable_range _).mono inter_subset_right
  have hrad : ∀ {k : ℕ} {θ : Fin 3 → ℝ}, θ ∈ hmpU R k → hmpRad θ = θ 2 := fun hθ => by
    unfold hmpRad; exact ite_eq_left_iff.2 fun h => absurd ((radius_pos' _).trans hθ.2.1) h
  refine QuantumZipper.R18.RTHmp.hmp_ae_eventually_le
    (fun _ θ ω => CircleAvg.cInc h (hmpRad θ) (hmpPt θ) 1 0 ω) hD (R := R + 3)
    (by linarith) ?_ (fun _ => (CircleAvg.isGaussianProcess_incProc hh).comp_right hmpIdx)
    (fun _ θ => CircleAvg.integral_cInc hh (hmpRad_pos θ) one_pos _ _)
    (fun _ θ => CircleAvg.measurable_cInc hh _ _ _ _) (L := 5) (β := 1) one_pos le_rfl
    (by norm_num) (by linarith) ?_ ?_
  · intro k θ hθ
    obtain ⟨⟨hz, h1, h2⟩, -⟩ := hθ
    have hk : QuantumZipper.radius k ≤ 1 := by
      unfold QuantumZipper.radius; exact pow_le_one₀ (by norm_num) (by norm_num)
    refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => ?_
    have a0 : |θ 0| ≤ ‖hmpPt θ‖ := by
      have := Complex.abs_re_le_norm (hmpPt θ); simpa [hmpPt] using this
    have a1 : |θ 1| ≤ ‖hmpPt θ‖ := by
      have := Complex.abs_im_le_norm (hmpPt θ); simpa [hmpPt] using this
    have hr := radius_pos' (k + 2)
    fin_cases i <;> simp only [Real.norm_eq_abs] <;> simp
    · linarith
    · linarith
    · rw [abs_of_pos (hr.trans h1)]; linarith
  · intro k θ hθ
    rw [hrad hθ.1]
    refine (variance_cInc_le hh ((radius_pos' _).trans hθ.1.2.1) _).trans ?_
    have h1 := abs_log_le_of_mem hθ.1
    have h2 := hθ.1.1
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    nlinarith
  · intro k θ hθ θ' hθ' _
    have e : (fun ω => CircleAvg.cInc h (hmpRad θ) (hmpPt θ) 1 0 ω -
        CircleAvg.cInc h (hmpRad θ') (hmpPt θ') 1 0 ω) =
        CircleAvg.cInc h (hmpRad θ) (hmpPt θ) (hmpRad θ') (hmpPt θ') := by
      funext ω; simp only [CircleAvg.cInc]; ring
    rw [e, (CircleAvg.map_cInc hh (hmpRad_pos θ) (hmpRad_pos θ') _ _).2, Real.rpow_one]
    refine (CircleAvg.incCov_self_le (hmpRad_pos θ) (hmpRad_pos θ') _ _).trans ?_
    rw [hrad hθ.1, hrad hθ'.1]
    have hm : QuantumZipper.radius k / 4 ≤ min (θ 2) (θ' 2) := by
      have := radius_add k 2
      norm_num at this
      exact le_min (by linarith [hθ.1.2.1]) (by linarith [hθ'.1.2.1])
    have hk := radius_pos' k
    have hn := norm_nonneg (θ - θ')
    have hr : |θ 2 - θ' 2| ≤ ‖θ - θ'‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (θ - θ') 2
    have hz := norm_hmpPt_sub θ θ'
    have hm0 : 0 < QuantumZipper.radius k / 4 := by positivity
    have : (|θ 2 - θ' 2| + ‖hmpPt θ - hmpPt θ'‖) / min (θ 2) (θ' 2) ≤
        3 * ‖θ - θ'‖ / (QuantumZipper.radius k / 4) :=
      div_le_div₀ (by positivity) (by linarith) hm0 hm
    rw [div_div_eq_mul_div] at this
    have e2 : (5 : ℝ) ^ 2 * (‖θ - θ'‖ / QuantumZipper.radius k) =
        25 * ‖θ - θ'‖ / QuantumZipper.radius k := by ring
    rw [e2]
    have : 3 * ‖θ - θ'‖ * 4 / QuantumZipper.radius k ≤ 25 * ‖θ - θ'‖ / QuantumZipper.radius k / 2 := by
      rw [div_div, le_div_iff₀ (by positivity), div_mul_eq_mul_div, mul_comm (QuantumZipper.radius k) 2,
        ← mul_assoc, mul_div_assoc, div_self hk.ne']
      nlinarith
    linarith

end LQGMetric.DFGPS
