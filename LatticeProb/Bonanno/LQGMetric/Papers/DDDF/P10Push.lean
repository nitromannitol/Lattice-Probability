/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P10Push at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic
import LatticeProb.Bonanno.LQGMetric.LFPP.PathPiece

/-!
# Crossing lengths under a conformal map (for DDDF Prop 10)

DF (Dubédat–Falconet, arXiv:1809.02607, proof of Prop. 4.5, `LiouvilleMetricStarScale.tex`
l. 552–566): for `F` holomorphic and a `C¹` path `π`,
`L(F ∘ π, e^{φ}) = ∫ e^{φ(F(π))} |F'(π)| |π'| ≤ ‖F'‖_K L(π, e^{φ ∘ F})`, hence
`L(F(A), F(B); F(K), e^{ξφ}) ≤ ‖F'‖_K L(A, B; K, e^{ξ φ∘F})` (`crossLenIn_image_le`).

The image of a piecewise-`C¹` path under a map holomorphic on an open set containing it is
piecewise `C¹` (`pcwC1_comp`, breakpoint form of `LFPP.PcwC1`), and off the finitely many
breakpoints the chain rule gives `(F ∘ π)' = F'(π) π'`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open LFPP

/-- a piecewise-`C¹` path is differentiable at every interior non-breakpoint -/
lemma differentiableAt_of_pcwC1 {P : ℝ → ℂ} {Fs : Finset ℝ} (hP : PcwC1 P Fs) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hsF : s ∉ Fs) : DifferentiableAt ℝ P s := by
  have hV : IsOpen (Ioo (0 : ℝ) 1 \ (Fs : Set ℝ)) := isOpen_Ioo.sdiff Fs.finite_toSet.isClosed
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV s ⟨hs, hsF⟩
  have hsub : Icc (s - ε / 2) (s + ε / 2) ⊆ Ioo (0 : ℝ) 1 \ (Fs : Set ℝ) := by
    intro u hu
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hu.1, hu.2]
  have hc := hP (s - ε / 2) (s + ε / 2) (hsub ⟨le_rfl, by linarith⟩).1.1.le (by linarith)
    (hsub ⟨by linarith, le_rfl⟩).1.2.le (fun x hx hxI => (hsub (Ioo_subset_Icc_self hxI)).2 hx)
  exact (hc.differentiableOn one_ne_zero).differentiableAt
    (Icc_mem_nhds (by linarith) (by linarith))

/-- the image of a piecewise-`C¹` path under a map `C¹` on an open set containing it -/
lemma pcwC1_comp {P : ℝ → ℂ} {Fs : Finset ℝ} (hP : PcwC1 P Fs) {F : ℂ → ℂ} {U : Set ℂ}
    (hF : ContDiffOn ℝ 1 F U) (hPU : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ U) : PcwC1 (F ∘ P) Fs :=
  fun a b ha hab hb hFs => hF.comp (hP a b ha hab hb hFs)
    fun t ht => hPU t ⟨ha.trans ht.1, ht.2.trans hb⟩

/-- the image path is admissible -/
lemma admPath_comp {K A B U : Set ℂ} {F : ℂ → ℂ} (hU : IsOpen U) (hKU : K ⊆ U)
    (hF : DifferentiableOn ℂ F U) {P : ℝ → ℂ} (hP : AdmPath K A B P) :
    AdmPath (F '' K) (F '' A) (F '' B) (F ∘ P) := by
  obtain ⟨z, hz, w, hw, hPc, hPK⟩ := hP
  obtain ⟨Fs, hFs⟩ := hPc.exists_pcwC1
  have hC : ContDiffOn ℝ 1 F U := ((hF.contDiffOn hU).restrict_scalars ℝ)
  refine ⟨F z, mem_image_of_mem F hz, F w, mem_image_of_mem F hw,
    IsPiecewiseC1Path.of_pcwC1 (by simp [hPc.source]) (by simp [hPc.target])
      (hC.continuousOn.comp hPc.continuousOn fun t ht => hKU (hPK t ht))
      (pcwC1_comp hFs hC fun t ht => hKU (hPK t ht)),
    fun t ht => mem_image_of_mem F (hPK t ht)⟩

/-- `L(F ∘ π, e^{ξ g}) ≤ S · L(π, e^{ξ g ∘ F})` if `|F'| ≤ S` along `π` -/
lemma lfppLen_comp_le {ξ : ℝ} {g : ℂ → ℝ} {K U : Set ℂ} {F : ℂ → ℂ} (hU : IsOpen U)
    (hKU : K ⊆ U) (hF : DifferentiableOn ℂ F U) {S : ℝ} (hS : ∀ x ∈ K, ‖deriv F x‖ ≤ S)
    {P : ℝ → ℂ} {Fs : Finset ℝ} (hFs : PcwC1 P Fs) (hPK : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ K) :
    lfppLen ξ g (F ∘ P) ≤ ENNReal.ofReal S * lfppLen ξ (g ∘ F) P := by
  unfold lfppLen
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hnull : (volume : Measure ℝ) ({0, 1} ∪ (Fs : Set ℝ)) = 0 :=
    ((Set.toFinite {0, 1}).union Fs.finite_toSet).measure_zero _
  refine setLIntegral_mono_ae' measurableSet_Icc ?_
  refine (measure_eq_zero_iff_ae_notMem.1 hnull).mono fun t ht htI => ?_
  have ht' : t ∈ Ioo (0 : ℝ) 1 ∧ t ∉ Fs := by
    simp only [mem_union, mem_insert_iff, mem_singleton_iff, Finset.mem_coe, not_or] at ht
    exact ⟨⟨lt_of_le_of_ne htI.1 (Ne.symm ht.1.1), lt_of_le_of_ne htI.2 ht.1.2⟩, ht.2⟩
  have hd := (differentiableAt_of_pcwC1 hFs ht'.1 ht'.2).hasDerivAt
  have hFd : HasDerivAt F (deriv F (P t)) (P t) :=
    ((hF _ (hKU (hPK t htI))).differentiableAt (hU.mem_nhds (hKU (hPK t htI)))).hasDerivAt
  rw [(hFd.comp t hd).deriv, norm_mul, ← ENNReal.ofReal_mul' (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [Function.comp_apply]
  have h1 := hS _ (hPK t htI)
  have h2 := Real.exp_pos (ξ * g (F (P t)))
  have h3 := norm_nonneg (deriv P t)
  nlinarith [mul_le_mul_of_nonneg_right h1 (mul_nonneg h2.le h3)]

/-- **DF (proof of Prop 4.5, l. 552–566)**: `L(F(A), F(B); F(K), e^{ξ g}) ≤ S L(A, B; K, e^{ξ g∘F})`
for `|F'| ≤ S` on `K`, `S > 0`. -/
theorem crossLenIn_image_le {ξ : ℝ} {g : ℂ → ℝ} {K A B U : Set ℂ} {F : ℂ → ℂ} (hU : IsOpen U)
    (hKU : K ⊆ U) (hF : DifferentiableOn ℂ F U) {S : ℝ} (hS0 : 0 < S)
    (hS : ∀ x ∈ K, ‖deriv F x‖ ≤ S) :
    crossLenIn ξ g (F '' K) (F '' A) (F '' B) ≤ ENNReal.ofReal S * crossLenIn ξ (g ∘ F) K A B := by
  have h0 : ENNReal.ofReal S ≠ 0 := (ENNReal.ofReal_pos.2 hS0).ne'
  rw [crossLenIn_eq_biInf ξ (g ∘ F), ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine le_iInf fun P => ?_
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine le_iInf fun hP => ?_
  obtain ⟨Fs, hFs⟩ := hP.choose_spec.2.choose_spec.2.1.exists_pcwC1
  exact (crossLenIn_le_lfppLen (admPath_comp hU hKU hF hP)).trans
    (lfppLen_comp_le hU hKU hF hS hFs hP.choose_spec.2.choose_spec.2.2)

end DDDF
end LQGMetric
