/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoisePushCoupling at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePushL2

/-!
# The conformally coupled white noise `W̃` (task P2-DDDFL6)

DDDF (arXiv:1904.08021, `tightness.tex` l. 541–543), after Dubédat–Falconet (arXiv:1809.02607,
`LiouvilleMetricStarScale.tex` l. 385–395): for `F : U → V` conformal, the white noise `W̃` is
coupled with `W` by `W̃(dF(y), d(t|F'(y)|²)) = |F'(y)|² W(dy,dt)` on `V × (0,∞)`, i.e.
`W̃(ω) = W(T ω)` for `ω` supported in `(0,∞) × V`, and "the rest of the white noises are chosen to
be independent". We realise this as

  `W̃(g) := W(T g) + W'(g 1_{((0,∞)×V)ᶜ})`

for a second white noise `W'` independent of `W` (`coupledNoise`), and prove that `W̃` is a white
noise (`isWhiteNoise_coupledNoise`): the two parts are independent centred Gaussians with
variances `‖T g‖² = ∫_{(0,∞)×V} g²` (`ConfHyp.norm_sq_pushL2`, Jacobian `|F'|⁴`) and
`∫_{((0,∞)×V)ᶜ} g²`, which add up to `‖g‖²`. The defining identity of the coupling is
`coupledNoise_ae_of_supportedIn`.

Reading (proposed DEVIATION D-DDDF-L6-1): the paper's "rest chosen independent" is formalised by
an extra white noise `W'` independent of `W` on the same probability space (any space carrying
`W` can be enlarged by a product to carry such a `W'`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace WNPush

open WhiteNoise

variable {F : ℂ → ℂ} {U : Set ℂ}

variable (F U) in
/-- The space-time image domain `(0,∞) × F(U)`. -/
def pushTarget : Set (ℝ × ℂ) := Ioi 0 ×ˢ (F '' U)

lemma ConfHyp.measurableSet_pushTarget (h : ConfHyp F U) : MeasurableSet (pushTarget F U) :=
  measurableSet_Ioi.prod (measurableSet_image h.1 h.2 h.3)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The coupled white noise** `W̃(g) = W(T g) + W'(g 1_{((0,∞)×F(U))ᶜ})` (DDDF l. 541–543). -/
def coupledNoise (h : ConfHyp F U) (W W' : WNSpace → Ω → ℝ) (g : WNSpace) (ω : Ω) : ℝ :=
  W (pushL2 F U g) ω + W' (cutL2 h.measurableSet_pushTarget.compl g) ω

/-- **`W̃` is a white noise.** -/
theorem isWhiteNoise_coupledNoise (h : ConfHyp F U) {W W' : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P W')
    (hind : IndepFun (fun ω f => W f ω) (fun ω f => W' f ω) P) :
    IsWhiteNoise P (coupledNoise h W W') := by
  refine ⟨fun f => (hW.measurable _).add (hW'.measurable _), ?_⟩
  intro ι _ f c
  set hc := h.measurableSet_pushTarget.compl
  set X : Ω → ℝ := fun ω => ∑ i, c i * W (pushL2 F U (f i)) ω
  set Y : Ω → ℝ := fun ω => ∑ i, c i * W' (cutL2 hc (f i)) ω
  have hX := hW.hasLaw (fun i => pushL2 F U (f i)) c
  have hY := hW'.hasLaw (fun i => cutL2 hc (f i)) c
  have hXY : IndepFun X Y P :=
    hind.comp (φ := fun x : WNSpace → ℝ => ∑ i, c i * x (pushL2 F U (f i)))
      (ψ := fun x : WNSpace → ℝ => ∑ i, c i * x (cutL2 hc (f i)))
      (Finset.measurable_sum _ fun i _ => (measurable_pi_apply _).const_mul _)
      (Finset.measurable_sum _ fun i _ => (measurable_pi_apply _).const_mul _)
  have e : (fun ω => ∑ i, c i * coupledNoise h W W' (f i) ω) = X + Y := by
    funext ω
    simp [X, Y, coupledNoise, mul_add, Finset.sum_add_distrib]
  have e1 : ∑ i, c i • pushL2 F U (f i) = pushL2 F U (∑ i, c i • f i) := by
    rw [← h.pushLM_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => (h.pushL2_smul _ _).symm
  have e2 : ∑ i, c i • cutL2 hc (f i) = cutL2 hc (∑ i, c i • f i) := by
    rw [← cutLM_apply, map_sum]
    simp only [map_smul, cutLM_apply]
  have hnorm : ‖∑ i, c i • pushL2 F U (f i)‖ ^ 2 + ‖∑ i, c i • cutL2 hc (f i)‖ ^ 2 =
      ‖∑ i, c i • f i‖ ^ 2 := by
    rw [e1, e2, h.norm_sq_pushL2, norm_sq_cutL2, norm_sq_split h.measurableSet_pushTarget]
    rfl
  rw [e]
  refine ⟨hX.aemeasurable.add hY.aemeasurable, ?_⟩
  rw [gaussianReal_add_gaussianReal_of_indepFun hXY hX hY, add_zero,
    ← Real.toNNReal_add (sq_nonneg _) (sq_nonneg _), hnorm]

/-- **The defining identity of the coupling** (DDDF l. 541–543): for `g` supported in
`(0,∞) × F(U)`, `W̃(g) = W(T g)` almost surely. -/
theorem coupledNoise_ae_of_supportedIn (h : ConfHyp F U) {W W' : WNSpace → Ω → ℝ}
    (hW' : IsWhiteNoise P W') {g : WNSpace} (hg : SupportedIn (pushTarget F U) g) :
    coupledNoise h W W' g =ᵐ[P] W (pushL2 F U g) := by
  have h0 : cutL2 h.measurableSet_pushTarget.compl g = 0 := by
    apply Lp.ext
    filter_upwards [coeFn_cutL2 h.measurableSet_pushTarget.compl g, Lp.coeFn_zero ℝ 2 volume,
      (ae_restrict_iff' h.measurableSet_pushTarget.compl).1 hg] with p h1 h2 h3
    rw [h1, h2]
    by_cases hp : p ∈ (pushTarget F U)ᶜ
    · simp [hp, h3 hp]
    · simp [hp]
  have hz : W' 0 =ᵐ[P] 0 := by
    filter_upwards [hW'.smul_ae 0 0] with ω hω
    simpa using hω
  filter_upwards [hz] with ω hω
  simp [coupledNoise, h0, hω]

end WNPush
end LQGMetric
