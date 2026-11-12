/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent2Circ at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent2Green
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentCirc
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqCov

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# White-noise circle kernels reproduce the circle-average covariance (task P2-GMCID2, G2)

For circles `∂B(z, r)`, `∂B(w, s)` whose closed discs lie in `𝕍` and
`K_μ = ∫ 1_{s>0} p_𝕍(s/2; y, ·) μ(dy)` (`GMCIdent.measKer openSquare (Ioi 0) μ`):

* `memLp_measKer_circle` : `K_{σ_{z,r}} ∈ L²`;
* **`pi_inner_measKerL2_circle`** : `π ⟪K_{σ_{z,r}}, K_{σ_{w,s}}⟫ = ∫∫ G_ℍ(φ x, φ y) dσ_{w,s} dσ_{z,r}`,
  which is `Cov(h_r(z), h_s(w))` for every zero-boundary GFF on `𝕍` (`circleCov_eq_kernel`):
  `cov_wn_circle_eq`.

Proof: Tonelli and the semigroup identity (`lintegral_wndKernel_mul`) give
`⟪K_μ, K_ν⟫ = ∫∫ ∫₀^∞ p_𝕍(s; y, y') ds dμ dν`, and the Green identity
`killedGreen_openSquare` (DZZ (eq:Green_fxn)) with the circle mean values of
`integral_greenH_sqM_circle`. This is DZZ's covariance computation (eq-cov-tildeh), l. 400–403,
for circle averages; own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric QuantumZipper
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace GMCIdent2

open KilledHeat WhiteNoise DZZ GMCIdent

/-- `∫ s in I, p_A(s; q.1, q.2) ds` as an extended real -/
def heatInt (A : Set ℂ) (I : Set ℝ) (q : ℂ × ℂ) : ℝ≥0∞ :=
  ∫⁻ s in I, ENNReal.ofReal (killedHeat A s.toNNReal q.1 q.2)

lemma measurable_heatInt {A : Set ℂ} (hA : IsOpen A) (I : Set ℝ) : Measurable (heatInt A I) := by
  have hf : Measurable fun r : (ℂ × ℂ) × ℝ =>
      ENNReal.ofReal (killedHeat A r.2.toNNReal r.1.1 r.1.2) :=
    ENNReal.measurable_ofReal.comp ((measurable_killedHeat hA).comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk
        ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst))))
  exact hf.lintegral_prod_right' (ν := volume.restrict I)

/-- **Tonelli + semigroup**: `∫ K_μ K_ν = ∫∫ ∫_I p_A(s; y, y') ds dμ dν` (extended reals). -/
theorem lintegral_measKer_mul {A : Set ℂ} (hA : IsOpen A) {I : Set ℝ} (hI : MeasurableSet I)
    (hI0 : I ⊆ Ioi 0) (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∫⁻ p, ENNReal.ofReal (measKer A I μ p) * ENNReal.ofReal (measKer A I ν p) =
      ∫⁻ q, heatInt A I q ∂(μ.prod ν) := by
  have hof : ∀ (κ : Measure ℂ) [IsFiniteMeasure κ] (p : ℝ × ℂ),
      ENNReal.ofReal (measKer A I κ p) = ∫⁻ y, ENNReal.ofReal (wndKernel A I y p) ∂κ :=
    fun κ _ p => ofReal_integral_eq_lintegral_ofReal (integrable_wndKernel_param hA hI0 κ p)
      (ae_of_all _ fun y => wndKernel_nonneg _ _ _ _)
  have hm : Measurable fun q : ℂ × (ℝ × ℂ) => ENNReal.ofReal (wndKernel A I q.1 q.2) :=
    ENNReal.measurable_ofReal.comp (measurable_wndKernel_uncurry hA hI)
  have hprod : ∀ p : ℝ × ℂ, (∫⁻ y, ENNReal.ofReal (wndKernel A I y p) ∂μ) *
      (∫⁻ y, ENNReal.ofReal (wndKernel A I y p) ∂ν) = ∫⁻ q, ENNReal.ofReal (wndKernel A I q.1 p) *
        ENNReal.ofReal (wndKernel A I q.2 p) ∂(μ.prod ν) := fun p =>
    (lintegral_prod_mul (hm.comp (measurable_id.prodMk measurable_const)).aemeasurable
      (hm.comp (measurable_id.prodMk measurable_const)).aemeasurable).symm
  simp_rw [hof μ, hof ν, hprod]
  have hjm : Measurable fun r : (ℝ × ℂ) × (ℂ × ℂ) => ENNReal.ofReal (wndKernel A I r.2.1 r.1) *
      ENNReal.ofReal (wndKernel A I r.2.2 r.1) := by
    have e1 : Measurable fun r : (ℝ × ℂ) × (ℂ × ℂ) => (r.2.1, r.1) := by fun_prop
    have e2 : Measurable fun r : (ℝ × ℂ) × (ℂ × ℂ) => (r.2.2, r.1) := by fun_prop
    have m1 : Measurable fun r : (ℝ × ℂ) × (ℂ × ℂ) => ENNReal.ofReal (wndKernel A I r.2.1 r.1) :=
      by have := hm.comp e1; exact this
    have m2 : Measurable fun r : (ℝ × ℂ) × (ℂ × ℂ) => ENNReal.ofReal (wndKernel A I r.2.2 r.1) :=
      by have := hm.comp e2; exact this
    exact m1.mul m2
  have hsw := lintegral_lintegral_swap (μ := (volume : Measure (ℝ × ℂ))) (ν := μ.prod ν)
    (f := fun p q => ENNReal.ofReal (wndKernel A I q.1 p) * ENNReal.ofReal (wndKernel A I q.2 p))
    (by have := hjm.aemeasurable (μ := (volume : Measure (ℝ × ℂ)).prod (μ.prod ν)); exact this)
  rw [hsw]
  exact lintegral_congr fun q => lintegral_wndKernel_mul hA hI hI0 q.1 q.2

/-- off the diagonal of `𝕍 × 𝕍`: `∫₀^∞ p_𝕍(s; x, y) ds = G_ℍ(φ x, φ y)/π` -/
lemma heatInt_eq {x y : ℂ} (hx : x ∈ openSquare) (hy : y ∈ openSquare) (hxy : x ≠ y) :
    heatInt openSquare (Ioi 0) (x, y) = ENNReal.ofReal (greenH (sqM x) (sqM y) / Real.pi) := by
  unfold heatInt
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_killedHeat isOpen_openSquare (by norm_num) openSquare_subset_ball2 hxy)
    (ae_of_all _ fun s => killedHeat_nonneg _ _ _ _)]
  congr 1
  rw [greenH_sqM hx hy hxy, ← killedGreen_openSquare hx hy hxy, killedGreen]
  field_simp

lemma greenH_sqM_nonneg {x y : ℂ} (hx : x ∈ openSquare) (hy : y ∈ openSquare) (hxy : x ≠ y) :
    0 ≤ greenH (sqM x) (sqM y) := by
  rw [greenH_sqM hx hy hxy, ← killedGreen_openSquare hx hy hxy]
  exact killedGreen_nonneg _ _ _

/-! ## Circles -/

/-- `c(x) = ∫ G_ℍ(φ x, φ y) dσ_{w,s}(y) = −log max(s, ‖w − x‖) + hS x w` -/
def circPot (w : ℂ) (s : ℝ) (x : ℂ) : ℝ := -Real.log (max s ‖w - x‖) + hS x w

lemma ae_ne_circleUnif {w : ℂ} {s : ℝ} (hs : 0 < s) (hB : closedBall w s ⊆ openSquare) (x : ℂ) :
    ∀ᵐ y ∂circleUnif w s, y ≠ x := by
  rw [ae_iff]
  have := noAtoms_of_isAdmissibleH (isAdmissibleH_circleUnif hs hB) x
  simpa using this

lemma integrable_greenH_sqM_circle {x w : ℂ} {s : ℝ} (hx : x ∈ openSquare) (hs : 0 < s)
    (hB : closedBall w s ⊆ openSquare) :
    Integrable (fun y => greenH (sqM x) (sqM y)) (circleUnif w s) := by
  refine ((CircleMV.integrable_log_norm_sub_circleUnif w x s).neg.add
    (integrable_hS_right hx hs.le hB)).congr ?_
  filter_upwards [ae_ne_circleUnif hs hB x, CoordReg.ae_mem_closedBall_circleUnif w hs.le]
    with y hyx hy
  show -Real.log ‖y - x‖ + hS x y = greenH (sqM x) (sqM y)
  rw [greenH_sqM hx (hB hy) (Ne.symm hyx), norm_sub_rev]

lemma circPot_nonneg {x w : ℂ} {s : ℝ} (hx : x ∈ openSquare) (hs : 0 < s)
    (hB : closedBall w s ⊆ openSquare) : 0 ≤ circPot w s x := by
  rw [circPot, ← integral_greenH_sqM_circle hx hs hB]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_ne_circleUnif hs hB x, CoordReg.ae_mem_closedBall_circleUnif w hs.le]
    with y hyx hy
  exact greenH_sqM_nonneg hx (hB hy) (Ne.symm hyx)

lemma lintegral_heatInt_circle {x w : ℂ} {s : ℝ} (hx : x ∈ openSquare) (hs : 0 < s)
    (hB : closedBall w s ⊆ openSquare) :
    ∫⁻ y, heatInt openSquare (Ioi 0) (x, y) ∂circleUnif w s =
      ENNReal.ofReal (circPot w s x / Real.pi) := by
  have hc : ∫⁻ y, heatInt openSquare (Ioi 0) (x, y) ∂circleUnif w s =
      ∫⁻ y, ENNReal.ofReal (greenH (sqM x) (sqM y) / Real.pi) ∂circleUnif w s := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_ne_circleUnif hs hB x, CoordReg.ae_mem_closedBall_circleUnif w hs.le]
      with y hyx hy
    exact heatInt_eq hx (hB hy) (Ne.symm hyx)
  rw [hc, ← ofReal_integral_eq_lintegral_ofReal
    ((integrable_greenH_sqM_circle hx hs hB).div_const _), integral_div,
    integral_greenH_sqM_circle hx hs hB, circPot]
  filter_upwards [ae_ne_circleUnif hs hB x, CoordReg.ae_mem_closedBall_circleUnif w hs.le]
    with y hyx hy
  exact div_nonneg (greenH_sqM_nonneg hx (hB hy) (Ne.symm hyx)) Real.pi_pos.le

lemma lintegral_heatInt_prod_circle {z w : ℂ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hB₁ : closedBall z r ⊆ openSquare) (hB₂ : closedBall w s ⊆ openSquare) :
    ∫⁻ q, heatInt openSquare (Ioi 0) q ∂((circleUnif z r).prod (circleUnif w s)) =
      ∫⁻ x, ENNReal.ofReal (circPot w s x / Real.pi) ∂circleUnif z r := by
  rw [lintegral_prod _ (measurable_heatInt isOpen_openSquare _).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [CoordReg.ae_mem_closedBall_circleUnif z hr.le] with x hx
  exact lintegral_heatInt_circle (hB₁ hx) hs hB₂

lemma lintegral_circPot_lt_top {z w : ℂ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hB₁ : closedBall z r ⊆ openSquare) (hB₂ : closedBall w s ⊆ openSquare) :
    ∫⁻ x, ENNReal.ofReal (circPot w s x / Real.pi) ∂circleUnif z r < ⊤ := by
  have hw : w ∈ openSquare := hB₂ (mem_closedBall_self hs.le)
  obtain ⟨M, hM⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn
    ((continuousOn_hS_right hw).mono hB₁)
  have hb : ∀ᵐ x ∂circleUnif z r,
      ENNReal.ofReal (circPot w s x / Real.pi) ≤ ENNReal.ofReal ((-Real.log s + M) / Real.pi) := by
    filter_upwards [CoordReg.ae_mem_closedBall_circleUnif z hr.le] with x hx
    refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ Real.pi_pos.le)
    have h1 : Real.log s ≤ Real.log (max s ‖w - x‖) := Real.log_le_log hs (le_max_left _ _)
    have h2 : hS x w ≤ M := by
      rw [hS_symm]; exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM x hx)
    unfold circPot; linarith
  refine (lintegral_mono_ae hb).trans_lt ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-- `∫ K_μ K_ν = ∫ c dμ / π` for circle measures, as extended reals -/
lemma lintegral_measKer_mul_circle {z w : ℂ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hB₁ : closedBall z r ⊆ openSquare) (hB₂ : closedBall w s ⊆ openSquare) :
    ∫⁻ p, ENNReal.ofReal (measKer openSquare (Ioi 0) (circleUnif z r) p *
        measKer openSquare (Ioi 0) (circleUnif w s) p) =
      ∫⁻ x, ENNReal.ofReal (circPot w s x / Real.pi) ∂circleUnif z r := by
  simp_rw [ENNReal.ofReal_mul (measKer_nonneg _ _ _ _)]
  rw [lintegral_measKer_mul isOpen_openSquare measurableSet_Ioi subset_rfl,
    lintegral_heatInt_prod_circle hr hs hB₁ hB₂]

/-- **the circle kernel is square integrable** -/
theorem memLp_measKer_circle {z : ℂ} {r : ℝ} (hr : 0 < r) (hB : closedBall z r ⊆ openSquare) :
    MemLp (measKer openSquare (Ioi 0) (circleUnif z r)) 2 volume := by
  have hm := measurable_measKer isOpen_openSquare (measurableSet_Ioi (a := (0 : ℝ))) (circleUnif z r)
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  refine ⟨(hm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun p => sq_nonneg _)]
  simp_rw [sq]
  rw [lintegral_measKer_mul_circle hr hr hB hB]
  exact lintegral_circPot_lt_top hr hr hB hB

/-- **G2**: `π ⟪K_{σ_{z,r}}, K_{σ_{w,s}}⟫ = ∫∫ G_𝕍 dσ_{w,s} dσ_{z,r}` -/
theorem pi_inner_measKerL2_circle {z w : ℂ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hB₁ : closedBall z r ⊆ openSquare) (hB₂ : closedBall w s ⊆ openSquare) :
    Real.pi * ⟪measKerL2 openSquare (Ioi 0) (circleUnif z r),
      measKerL2 openSquare (Ioi 0) (circleUnif w s)⟫ =
      ∫ x, ∫ y, greenH (sqM x) (sqM y) ∂circleUnif w s ∂circleUnif z r := by
  have hu := memLp_measKer_circle hr hB₁
  have hv := memLp_measKer_circle hs hB₂
  have hmu := measurable_measKer isOpen_openSquare (measurableSet_Ioi (a := (0 : ℝ))) (circleUnif z r)
  have hmv := measurable_measKer isOpen_openSquare (measurableSet_Ioi (a := (0 : ℝ))) (circleUnif w s)
  rw [measKerL2, measKerL2, dite_eq_left_of_eq_true (eq_true hu),
    dite_eq_left_of_eq_true (eq_true hv), L2.inner_def]
  have h1 : (fun p => ⟪(hu.toLp _ : ℝ × ℂ → ℝ) p, (hv.toLp _ : ℝ × ℂ → ℝ) p⟫) =ᵐ[volume]
      fun p => measKer openSquare (Ioi 0) (circleUnif z r) p *
        measKer openSquare (Ioi 0) (circleUnif w s) p := by
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with p h1 h2
    rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply]
    simp [mul_comm]
  rw [integral_congr_ae h1, integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun p => mul_nonneg (measKer_nonneg _ _ _ _) (measKer_nonneg _ _ _ _))
      (hmu.mul hmv).aestronglyMeasurable, lintegral_measKer_mul_circle hr hs hB₁ hB₂]
  have hR : ∫ x, ∫ y, greenH (sqM x) (sqM y) ∂circleUnif w s ∂circleUnif z r =
      ∫ x, circPot w s x ∂circleUnif z r := by
    refine integral_congr_ae ?_
    filter_upwards [CoordReg.ae_mem_closedBall_circleUnif z hr.le] with x hx
    exact integral_greenH_sqM_circle (hB₁ hx) hs hB₂
  have hcm : Measurable (circPot w s) := by
    have e : circPot w s = fun x => -Real.log (max s ‖w - x‖) + hS w x := by
      funext x; rw [circPot, hS_symm]
    rw [e]
    exact ((Real.measurable_log.comp (measurable_const.max
      (measurable_const.sub measurable_id).norm)).neg).add (measurable_hS_right w)
  rw [hR, ← integral_eq_lintegral_of_nonneg_ae, integral_div]
  · field_simp
  · filter_upwards [CoordReg.ae_mem_closedBall_circleUnif z hr.le] with x hx
    exact div_nonneg (circPot_nonneg (hB₁ hx) hs hB₂) Real.pi_pos.le
  · exact (hcm.div_const _).aestronglyMeasurable

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
  {X : Ω → Measure ℂ → ℝ}

end GMCIdent2
end LQGMetric
