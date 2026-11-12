/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.L3_1 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppA3SFub
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppA3Ker
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent3Law

/-!
DG (`metric-comparison-final.tex`, Lemma 3.1 `lem-gff-compare`, DG:966–974; proof DG:2243–2244
"Combine Lemmas 2.2, A.1 and A.2"). Here `U = 𝕍 = (0,1)²` and all fields are built from one white
noise `W` (DG's coupling: "`ĥ` and `ĥ^tr` are defined using the same white noise"):

* `h^U` tested against the uniform measure `σ_{z,r}` on `∂B(z,r)` is `√π W(K_{σ_{z,r}})`
  (`measKerL2 𝕍 (Ioi 0)`, DG:2146 `h^U = lim_{t→0} h^U_{t,∞}`); by `GMCIdent3.map_circVec_eq`
  this circle family has the law of the circle averages of the zero-boundary GFF on `𝕍`
  ([RV review, Lemma 5.4], cited by DG:2146; the identification of the white-noise field with the
  zero-boundary GFF, via the Green identity `GMCIdent2.killedGreen_openSquare`);
* `ĥ` tested against `σ_{z,r}` is `√π W(hatMeasKerL2 σ_{z,r})` (DG (3.1));
* **`dg_lemma31_hU_hat_circ`**: the continuous modification `Y` of `h^U − ĥ` on a box `K` with
  `B(z,1/10) ⊆ 𝕍` for `z ∈ K` (`dg_lemma31_hU_hat_wn`) satisfies (3.5), and its circle averages
  are a.s. `(h^U − ĥ)(σ_{z,r})` for every circle in `K` (stochastic Fubini `ae_integral_eq_wn` and
  the kernel identity `integral_dgUHatKernel_ae_eq`). So `Y` is a continuous modification of the
  distribution `(h^U − ĥ)|_K` in the sense of circle averages, as in DG.

For `𝕍`, DG's `K = {z : dist(z, ∂𝕍) ≥ 1/10} = [1/10, 9/10]²` is such a box.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3 SupTail QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the `L²` increments of the kernel of `h^U − ĥ` on the box (from (A.3) for A.1 and A.2) -/
lemma dgUHatKernel_holder {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) {y : ℂ}
    {b : ℝ} (hb : 0 < b) (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ U) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ ferniqueBox y b, ∀ c ∈ ferniqueBox y b,
      ‖dgUHatKernel U x - dgUHatKernel U c‖ ^ 2 ≤ L * ‖x - c‖ := by
  have hpi := Real.pi_pos
  obtain ⟨L, hL0, hL⟩ := dg_A1_var_box hU hUb hb hK
  obtain ⟨C, hC⟩ := dg_A2_var0
  refine ⟨2 * L + 2 * (max C 0 / Real.pi), by positivity, fun x hx c hc => ?_⟩
  have h1 := hL x hx c hc
  have h2 : ‖hatDiffKernel0 x - hatDiffKernel0 c‖ ^ 2 ≤ max C 0 / Real.pi * ‖x - c‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
    nlinarith [hC x c, mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg (x - c))]
  have e : dgUHatKernel U x - dgUHatKernel U c =
      (dgA1Kernel U x - dgA1Kernel U c) - (hatDiffKernel0 x - hatDiffKernel0 c) := by
    unfold dgUHatKernel; abel
  rw [e]
  have hsq : ∀ u v : WNSpace, ‖u - v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := fun u v => by
    have := norm_sub_le u v
    nlinarith [norm_nonneg (u - v), norm_nonneg u, norm_nonneg v, sq_nonneg (‖u‖ - ‖v‖)]
  refine (hsq _ _).trans ?_
  nlinarith

lemma continuousOn_of_sq_le {S : Set ℂ} {k : ℂ → WNSpace} {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ x ∈ S, ∀ c ∈ S, ‖k x - k c‖ ^ 2 ≤ L * ‖x - c‖) : ContinuousOn k S := by
  rw [Metric.continuousOn_iff]
  intro c hc ε hε
  refine ⟨ε ^ 2 / (L + 1), by positivity, fun x hx hxc => ?_⟩
  rw [dist_eq_norm] at hxc ⊢
  have h1 := h x hx c hc
  have h2 : L * ‖x - c‖ < ε ^ 2 := by
    calc L * ‖x - c‖ ≤ (L + 1) * ‖x - c‖ := by nlinarith [norm_nonneg (x - c)]
      _ < (L + 1) * (ε ^ 2 / (L + 1)) := by gcongr
      _ = ε ^ 2 := by field_simp
  exact lt_of_pow_lt_pow_left₀ 2 hε.le (h1.trans_lt h2)

lemma isBounded_openSquare : Bornology.IsBounded openSquare :=
  Metric.isBounded_ball.subset DZZ.openSquare_subset_ball

/-- **DG Lemma 3.1 for `(h^U, ĥ)`, `U = 𝕍`** (circle-average form, `K` a box). With
`h^U(σ) = √π W(K_σ)` (whose circle family has the law of the zero-boundary GFF on `𝕍`,
`map_circVec_eq`) and `ĥ(σ) = √π W(hatMeasKerL2 σ)`: there is a continuous process `Y` on `ℂ`
with the Gaussian tail (3.5) on `K` whose circle averages are a.s. `(h^U − ĥ)(σ_{z,r})` for every
circle `∂B(z,r) ⊆ K`. -/
theorem dg_lemma31_hU_hat_circ (hW : IsWhiteNoise P W) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun z => Y z ω) ∧ (∀ z, Measurable (Y z)) ∧
      (∃ c₀ c₁ : ℝ, 0 < c₁ ∧ ∀ A : ℝ, 0 ≤ A →
        P {ω | ¬ ∀ z ∈ ferniqueBox y b, |Y z ω| ≤ A} ≤
          ENNReal.ofReal (c₀ * Real.exp (-c₁ * A ^ 2))) ∧
      ∀ (z : ℂ) (r : ℝ), 0 < r → Metric.closedBall z r ⊆ ferniqueBox y b →
        (fun ω => ∫ x, Y x ω ∂(circleUnif z r)) =ᵐ[P] fun ω =>
          Real.sqrt Real.pi * W (measKerL2 openSquare (Ioi 0) (circleUnif z r)) ω -
            Real.sqrt Real.pi * W (hatMeasKerL2 (circleUnif z r)) ω := by
  have hpi := Real.pi_pos
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 hpi
  set S := ferniqueBox y b with hSdef
  have hSc : IsCompact S := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨Y, hYc, hYm, hYW, hT⟩ :=
    dg_lemma31_hU_hat_wn hW isOpen_openSquare isBounded_openSquare hb hK
  refine ⟨Y, hYc, hYm, hT, fun z r hr hB => ?_⟩
  set σ := circleUnif z r
  set k := dgUHatKernel openSquare
  have hσS : σ Sᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 hB) (circleUnif_compl_closedBall hr z)
  have hSae : ∀ᵐ x ∂σ, x ∈ S := mem_ae_iff.2 hσS
  obtain ⟨L, hL0, hL⟩ := dgUHatKernel_holder isOpen_openSquare isBounded_openSquare hb hK
  have hkc : ContinuousOn k S := continuousOn_of_sq_le hL0 hL
  obtain ⟨M, hM⟩ := hSc.exists_bound_of_continuousOn hkc
  have hSm : MeasurableSet S := hSc.isClosed.measurableSet
  have hkm : AEStronglyMeasurable k σ := by
    have := hkc.aestronglyMeasurable (μ := σ) hSm
    rwa [Measure.restrict_eq_self_of_ae_mem hSae] at this
  have hki : Integrable k σ := Integrable.of_bound hkm M (hSae.mono fun x hx => hM x hx)
  -- stochastic Fubini for `Y / √π`
  set Y' : ℂ → Ω → ℝ := fun x ω => Y x ω / Real.sqrt Real.pi
  have hYW' : ∀ x ∈ S, Y' x =ᵐ[P] W (k x) := fun x hx => by
    filter_upwards [hYW x hx] with ω h
    simp only [Y', h]; field_simp
  have hF := ae_integral_eq_wn hW hSc hσS hM (fun ω => (hYc ω).div_const _)
    (fun x => (hYm x).div_const _) hYW' hki
  -- the kernel identity
  have hBsq : Metric.closedBall z r ⊆ openSquare := fun x hx =>
    (hK x (hB hx)) (Metric.mem_ball_self (by norm_num))
  have hm1 := memLp_measKer_circle hr hBsq
  have hI := integral_dgUHatKernel_ae_eq isOpen_openSquare (le_of_lt two_pos)
    DZZ.openSquare_subset_ball σ (hSae.mono fun x hx => hK x hx) hki
  have hm2 : MemLp (hatMeasKer σ) 2 volume := by
    refine (hm1.sub (Lp.memLp (∫ x, k x ∂σ))).ae_eq ?_
    filter_upwards [hI] with p hp
    rw [Pi.sub_apply, hp]; ring
  have hkint : (∫ x, k x ∂σ) = measKerL2 openSquare (Ioi 0) σ - hatMeasKerL2 σ := by
    refine Lp.ext ?_
    have e1 : (measKerL2 openSquare (Ioi 0) σ : ℝ × ℂ → ℝ) =ᵐ[volume]
        measKer openSquare (Ioi 0) σ := by
      rw [measKerL2, dite_eq_left_of_eq_true (eq_true hm1)]; exact hm1.coeFn_toLp
    have e2 : (hatMeasKerL2 σ : ℝ × ℂ → ℝ) =ᵐ[volume] hatMeasKer σ := by
      rw [hatMeasKerL2, dite_eq_left_of_eq_true (eq_true hm2)]; exact hm2.coeFn_toLp
    filter_upwards [hI, Lp.coeFn_sub (measKerL2 openSquare (Ioi 0) σ) (hatMeasKerL2 σ), e1, e2]
      with p h1 h2 h3 h4
    rw [h1, h2, Pi.sub_apply, h3, h4]
  rw [hkint] at hF
  have hsub := hW.add_ae (measKerL2 openSquare (Ioi 0) σ) (-hatMeasKerL2 σ)
  have hneg := hW.smul_ae (-1) (hatMeasKerL2 σ)
  filter_upwards [hF, hsub, hneg] with ω h1 h2 h3
  have e : ∫ x, Y x ω ∂σ = Real.sqrt Real.pi * ∫ x, Y' x ω ∂σ := by
    rw [← integral_const_mul]; congr 1; funext x; simp only [Y']; field_simp
  rw [neg_one_smul] at h3
  rw [e, h1, sub_eq_add_neg (measKerL2 openSquare (Ioi 0) σ), h2, h3]
  ring

end DG
end LQGMetric
