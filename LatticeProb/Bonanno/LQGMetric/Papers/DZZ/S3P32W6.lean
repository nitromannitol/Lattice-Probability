/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32W6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W1
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent4Fact
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent5Ind
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L10Var

/-!
# D97, packet P-1: `M^W` is the limit of DZZ's approximations (eq-def-M-eta)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` (eq-def-M-eta), l. 1209–1213):
`M_γ^{h̃}(A) = lim_n ∫_A e^{γ h̃_{2^{-n}}(z) − γ²/2 E h̃_{2^{-n}}(z)²} dz`.

* `wickMeas W γ n ω := e^{γ h̃_{2^{-n}}(z) − γ²/2 Var h̃_{2^{-n}}(z)} dz` (`wickMeas_eq`: its density is
  `CR^{−γ²/2}` times the density `wnDens` of `GMCIdent4.wnMeas`);
* **`ae_isVagueLimitOn_wickMeas`**: a.s. `wickMeas W γ n ω → M^W = wickQArea γ W ω` vaguely on `𝕍`
  (from `GMCIdent4.ae_isVagueLimitOn_wnMeas` with the test functions `f · CR^{−γ²/2}`, continuous on
  `(0,1)²`; the argument of `GMCIdent4.ae_isVagueLimitOn_bandMeas`).

Own glue (D97).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper GMCIdent GMCIdent3 GMCIdent4

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {W : WNSpace → Ω' → ℝ}

/-- `CR(z)^{−γ²/2}` as a real number -/
def wickR (γ : ℝ) (z : ℂ) : ℝ := Real.exp (-(γ ^ 2 / 2) * hS z z)

lemma wickR_pos (γ : ℝ) (z : ℂ) : 0 < wickR γ z := Real.exp_pos _

lemma measurable_wickR (γ : ℝ) : Measurable (wickR γ) :=
  Real.measurable_exp.comp (GMCIdent.measurable_hS_diag.const_mul _)

lemma continuousOn_wickR (γ : ℝ) : ContinuousOn (wickR γ) openSquare :=
  Real.continuous_exp.comp_continuousOn (continuousOn_const.mul GMCIdent4.continuousOn_hS_diag)

/-- DZZ's approximation `e^{γ h̃_{2^{-n}} − γ²/2 Var h̃_{2^{-n}}} dz` of (eq-def-M-eta) -/
def wickMeas (W : WNSpace → Ω' → ℝ) (γ : ℝ) (n : ℕ) (ω : Ω') : Measure ℂ :=
  volume.withDensity fun z => ENNReal.ofReal (wickR γ z * wnDens W γ n z ω)

omit [MeasurableSpace Ω'] in
/-- the density of `wickMeas` is DZZ's `e^{γ h̃_{2^{-n}}(z) − γ²/2 Var h̃_{2^{-n}}(z)}` -/
lemma wickR_mul_wnDens (γ : ℝ) (n : ℕ) (z : ℂ) (ω : Ω') :
    wickR γ z * wnDens W γ n z ω =
      Real.exp (γ * tildeVer W n z ω - γ ^ 2 / 2 * tildeVar ((2 : ℝ)⁻¹ ^ n) z) := by
  rw [wickR, wnDens, wnWeight, tildeVar, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 1; ring

/-- **`M^W` is DZZ's limit (eq-def-M-eta)**: a.s. `wickMeas W γ n ω → wickQArea γ W ω` vaguely
on `𝕍`. -/
theorem ae_isVagueLimitOn_wickMeas (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P', IsVagueLimitOn openSquare (fun n => wickMeas W γ n ω) (wickQArea γ W ω) := by
  obtain ⟨Ω, _, P, X, hP, hX⟩ := GMCIdent5.exists_zeroGFF_openSquare
  have := hX.gaussian.isProbabilityMeasure
  filter_upwards [ae_isVagueLimitOn_wnMeas hX hW hγ hγ2] with ω h
  set M := qAreaMeasureOn γ (GMCIdent3.wnField W ω) openSquare
  have hm := measurable_wickR γ
  have hci := continuousOn_wickR γ
  have eW : wickQArea γ W ω = M.withDensity fun z => ENNReal.ofReal (wickR γ z) := rfl
  refine ⟨?_, fun K hK hKU => ?_, fun f hf hfc hfU => ?_⟩
  · rw [eW]; exact withDensity_absolutelyContinuous _ _ h.1
  · obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hci.mono hKU)
    rw [eW, withDensity_apply _ hK.measurableSet]
    calc ∫⁻ z in K, ENNReal.ofReal (wickR γ z) ∂M
        ≤ ∫⁻ _z in K, ENNReal.ofReal C ∂M := by
          refine setLIntegral_mono measurable_const fun z hz => ENNReal.ofReal_le_ofReal ?_
          have := hC z hz
          rw [Real.norm_eq_abs] at this
          exact (le_abs_self _).trans this
      _ = ENNReal.ofReal C * M K := setLIntegral_const _ _
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (h.2.1 K hK hKU)
  · set g : ℂ → ℝ := fun z => f z * wickR γ z
    have hgU : tsupport g ⊆ openSquare := (tsupport_mul_subset_left).trans hfU
    have hgc : Continuous g :=
      (hf.continuousOn.mul hci).continuous_of_tsupport_subset isOpen_openSquare hgU
    have hg := h.2.2 g hgc hfc.mul_right hgU
    have e1 : ∀ n, ∫ z, f z ∂(wickMeas W γ n ω) = ∫ z, g z ∂(wnMeas W γ n ω) := by
      intro n
      rw [wickMeas, wnMeas, integral_withDensity_ofReal
          (d := fun z => wickR γ z * wnDens W γ n z ω) (hm.mul (measurable_wnDens hW γ n ω))
          (fun z => mul_nonneg (wickR_pos γ z).le (wnDens_nonneg γ n z ω)),
        integral_withDensity_ofReal (measurable_wnDens hW γ n ω) (fun z => wnDens_nonneg γ n z ω)]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [g]; ring
    have e2 : ∫ z, f z ∂(wickQArea γ W ω) = ∫ z, g z ∂M := by
      rw [eW, integral_withDensity_ofReal (d := wickR γ) hm (fun z => (wickR_pos γ z).le)]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [g]; ring
    simp_rw [e1, e2]
    exact hg

/-- DZZ's approximation (eq-def-M-eta) with the version `coarseVer` of `h̃_{2^{-n}}`, continuous in
`z` -/
def wickMeasC (hW : IsWhiteNoise P' W) (γ : ℝ) (n : ℕ) (ω : Ω') : Measure ℂ :=
  volume.withDensity fun z => ENNReal.ofReal
    (Real.exp (γ * coarseVer hW n z ω - γ ^ 2 / 2 * tildeVar ((2 : ℝ)⁻¹ ^ n) z))

/-- a.s. the two versions give the same approximations (Fubini) -/
theorem ae_wickMeas_eq_wickMeasC (hW : IsWhiteNoise P' W) (γ : ℝ) :
    ∀ᵐ ω ∂P', ∀ n, wickMeas W γ n ω = wickMeasC hW γ n ω := by
  have hP := hW.isProbabilityMeasure
  rw [ae_all_iff]; intro n
  have h : ∀ᵐ ω ∂P', ∀ᵐ z ∂(volume : Measure ℂ), tildeVer W n z ω = coarseVer hW n z ω := by
    refine (Measure.ae_ae_comm (μ := (volume : Measure ℂ)) (ν := P')
      (p := fun z ω => tildeVer W n z ω = coarseVer hW n z ω)
      (measurableSet_eq_fun (measurable_tildeVer' hW n) (GMCIdent5.measurable_coarseVer_uncurry hW n))).1
      (Eventually.of_forall fun z => ?_)
    filter_upwards [tildeVer_ae_eq hW n z, (coarseVer_spec hW n).2.2 z] with ω e1 e2
    rw [e1, e2]
  filter_upwards [h] with ω hω
  refine withDensity_congr_ae ?_
  filter_upwards [hω] with z hz
  rw [wickR_mul_wnDens, hz]

/-- **`M^W` is DZZ's limit (eq-def-M-eta)**, continuous version: a.s.
`e^{γ h̃_{2^{-n}} − γ²/2 Var h̃_{2^{-n}}} dz → M^W` vaguely on `𝕍`. -/
theorem ae_isVagueLimitOn_wickMeasC (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P', IsVagueLimitOn openSquare (fun n => wickMeasC hW γ n ω) (wickQArea γ W ω) := by
  filter_upwards [ae_isVagueLimitOn_wickMeas hW hγ hγ2, ae_wickMeas_eq_wickMeasC hW γ]
    with ω h he
  simp_rw [← he]
  exact h

end DZZ
end LQGMetric
