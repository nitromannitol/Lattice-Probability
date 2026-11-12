/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L6Final at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L6FinalTail
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L6FinalMeas
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L6Tail
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L6VarH
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L6Decomp
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenObs

/-!
# DDDF Lemma 6 (final form)

DDDF (Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `tightness.tex` l. 545–556, proof
l. 559–646), after Dubédat–Falconet (arXiv:1809.02607, Prop. 4.3 and (4.4), DF:396–524).

* `l6_tail_phiL`: `φ_L^{(δ)}` has a version continuous on `K` whose sup over `K` has Gaussian
  tails uniformly in `δ` (DDDF Step 2, l. 578–583: Kolmogorov + Fernique, from the increment
  bound `l6_inc_phiL` and the variance bound `l6_var_phiL`, both on a closed thickening of `K`
  inside `U`; `exists_version_tail`).
* `lemma6`: with the continuous versions `φ_δ = phiVer W P δ 1`,
  `φ̃_δ = phiVer W̃ P δ 1` (`W̃ = coupledNoise h W W'`, DDDF l. 541–543) and the version `Y_L` of
  `φ_L`, the field `Y_H := φ̃_δ ∘ F − φ_δ − Y_L` is continuous on `K` and is a version of `φ_H`
  (`l6_decomp_ae`), so (eq:Decompo) holds identically; `φ_H` has bounded variance
  (`l6_var_phiH`, DDDF l. 641–645) and is independent of `(φ_δ, φ_L)` (`l6_indep`).
  DDDF's "smooth" is weakened to "continuous on `K`", which is what is used (Prop 10).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real Metric
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise WNPush

variable {F : ℂ → ℂ} {U : Set ℂ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **DDDF Lemma 6, Gaussian tail of `‖φ_L‖_K`** (l. 549–551, Step 2 l. 578–583), uniformly in
`δ`, for a version continuous on `K`. -/
theorem l6_tail_phiL (h : ConfHyp F U) (hUb : Bornology.IsBounded U)
    (hF1 : ∀ y ∈ U, 1 ≤ ‖deriv F y‖) {M M₂ : ℝ} (hM : ∀ y ∈ U, ‖deriv F y‖ ≤ M)
    (hM2 : ∀ y ∈ U, ‖deriv (deriv F) y‖ ≤ M₂) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    {W W' : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P W')
    (hind : IndepFun (fun ω f => W f ω) (fun ω f => W' f ω) P) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ δ, 0 < δ → ∃ Y : ℂ → Ω → ℝ,
      (∀ x ∈ K, Y x =ᵐ[P] phiL h W W' δ x) ∧ (∀ ω, ContinuousOn (fun x => Y x ω) K) ∧
      ∀ u : ℝ, 0 ≤ u → P {ω | ENNReal.ofReal u ≤ ⨆ x ∈ K, ENNReal.ofReal |Y x ω|} ≤
        ENNReal.ofReal (C * exp (-c * u ^ 2)) := by
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open h.isOpen hKU
  have hK' : IsCompact (cthickening r K) := hK.cthickening
  obtain ⟨C₁, hC₁⟩ := l6_inc_phiL h hUb hF1 hM hM2 hK' hrU hW hW'
  obtain ⟨C₂, hC₂⟩ := l6_var_phiL h hUb hF1 hM hM2 hK' hrU hW hW'
  set A := max C₁ 1
  set σ := √(max C₂ 1)
  have hA : 0 < A := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hσ : 0 < σ := sqrt_pos.2 (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hσ2 : σ ^ 2 = max C₂ 1 := sq_sqrt (le_trans zero_le_one (le_max_right _ _))
  obtain ⟨C, c, hC, hc, hT⟩ := exists_version_tail (P := P) hK hr hA hσ
  refine ⟨C, c, hC, hc, fun δ hδ => ?_⟩
  obtain ⟨Y, h1, h2, h3⟩ := hT (fun x => phiL h W W' δ x) (isGaussianProcess_phiL h hW hW' hind δ)
    (fun v => integral_phiL h hW hW' δ v)
    (fun u hu v hv => by
      refine (hC₁ δ hδ v hv u hu).trans ?_
      rw [norm_sub_rev]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    (fun v hv => by rw [hσ2]; exact (hC₂ δ hδ v hv).trans (le_max_left _ _))
  exact ⟨Y, h1, h2, h3⟩

/-- **DDDF Lemma 6** (`tightness.tex` l. 545–556) in the form used by Proposition 10: for
`0 < δ ≤ 1`, with the continuous versions `φ_δ = phiVer W P δ 1` and
`φ̃_δ = phiVer W̃ P δ 1` of the coupled noise `W̃ = coupledNoise h W W'`,
`φ̃_δ ∘ F = φ_δ + Y_L + Y_H` identically, where `Y_L`, `Y_H` are continuous on `K` and are
versions of `φ_L^{(δ)}`, `φ_H^{(δ)}` on `K`; `sup_K |Y_L|` has Gaussian tails and `φ_H` has
bounded variance, uniformly in `δ`; `φ_H` is independent of `(φ_δ, φ_L)`. -/
theorem lemma6 (h : ConfHyp F U) (hUb : Bornology.IsBounded U)
    (hF1 : ∀ y ∈ U, 1 ≤ ‖deriv F y‖) {M M₂ : ℝ} (hM : ∀ y ∈ U, ‖deriv F y‖ ≤ M)
    (hM2 : ∀ y ∈ U, ‖deriv (deriv F) y‖ ≤ M₂) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    {W W' : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P W')
    (hind : IndepFun (fun ω f => W f ω) (fun ω f => W' f ω) P) :
    ∃ C c σH : ℝ, 0 < C ∧ 0 < c ∧ ∀ δ, 0 < δ → δ ≤ 1 → ∃ YL YH : ℂ → Ω → ℝ,
      (∀ x ω, phiVer (coupledNoise h W W') P δ 1 (F x) ω =
        phiVer W P δ 1 x ω + YL x ω + YH x ω) ∧
      (∀ ω, ContinuousOn (fun x => YL x ω) K) ∧ (∀ ω, ContinuousOn (fun x => YH x ω) K) ∧
      (∀ x, Measurable (YL x)) ∧ (∀ x, Measurable (YH x)) ∧
      (∀ x ∈ K, YL x =ᵐ[P] phiL h W W' δ x) ∧ (∀ x ∈ K, YH x =ᵐ[P] phiH F U W δ x) ∧
      (∀ u : ℝ, 0 ≤ u → P {ω | ENNReal.ofReal u ≤ ⨆ x ∈ K, ENNReal.ofReal |YL x ω|} ≤
        ENNReal.ofReal (C * exp (-c * u ^ 2))) ∧
      (∀ x, Var[phiH F U W δ x; P] ≤ σH) ∧
      IndepFun (fun ω x => phiH F U W δ x ω)
        (fun ω x => (phi W δ 1 x ω, phiL h W W' δ x ω)) P := by
  obtain ⟨C, c, hC, hc, hT⟩ := l6_tail_phiL h hUb hF1 hM hM2 hK hKU hW hW' hind
  obtain ⟨σH, hσH⟩ := l6_var_phiH h hW hF1 hM
  refine ⟨C, c, σH, hC, hc, fun δ hδ hδ1 => ?_⟩
  obtain ⟨YL0, hL1', hL2', hL3'⟩ := hT δ hδ
  obtain ⟨YL, hL2, hLm, hLae⟩ := exists_measurable_version (P := P) hL2'
    (fun x => (((hW.measurable _).add (hW'.measurable _)).const_mul _ :
      Measurable (phiL h W W' δ x))) hL1'
  have hL1 : ∀ x ∈ K, YL x =ᵐ[P] phiL h W W' δ x := fun x hx => by
    filter_upwards [hLae, hL1' x hx] with ω h1 h2
    rw [h1 x hx, h2]
  have hL3 : ∀ u : ℝ, 0 ≤ u → P {ω | ENNReal.ofReal u ≤ ⨆ x ∈ K, ENNReal.ofReal |YL x ω|} ≤
      ENNReal.ofReal (C * exp (-c * u ^ 2)) := by
    intro u hu
    refine le_trans (measure_mono_ae ?_) (hL3' u hu)
    filter_upwards [hLae] with ω hω h1
    change ENNReal.ofReal u ≤ ⨆ x ∈ K, ENNReal.ofReal |YL x ω| at h1
    change ENNReal.ofReal u ≤ ⨆ x ∈ K, ENNReal.ofReal |YL0 x ω|
    refine h1.trans (le_of_eq ?_)
    exact iSup_congr fun x => iSup_congr fun hx => by rw [hω x hx]
  have hWt := isWhiteNoise_coupledNoise h hW hW' hind
  have hv := isPhiVersion_phiVer hW hδ hδ1
  have hvt := isPhiVersion_phiVer hWt hδ hδ1
  set YH : ℂ → Ω → ℝ := fun x ω =>
    phiVer (coupledNoise h W W') P δ 1 (F x) ω - phiVer W P δ 1 x ω - YL x ω
  refine ⟨YL, YH, fun x ω => by simp only [YH]; ring, hL2, fun ω => ?_, hLm,
    fun x => ((hvt.meas (F x)).sub (hv.meas x)).sub (hLm x), hL1, fun x hx => ?_,
    hL3, fun x => hσH δ hδ x, l6_indep h hW hW' hind hδ⟩
  · refine (((hvt.cont ω).comp_continuousOn (h.diff.continuousOn.mono hKU)).sub
      (hv.cont ω).continuousOn).sub (hL2 ω)
  · filter_upwards [hvt.ae_eq (F x), hv.ae_eq x, hL1 x hx, l6_decomp_ae h hW δ x]
      with ω e1 e2 e3 e4
    simp only [YH, e1, e2, e3]
    have := e4
    linarith

end DDDF
end LQGMetric
