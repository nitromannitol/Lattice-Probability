/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4O.Prop48OSecondMomentTriple at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OSecondMoment
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OTripleMean

/-!
# The (4.30)–(4.38) second moment with the triple conditional mean

The assembly of `GMS4O/Prop48OSecondMoment.lean` carried over to the triple-centred fluctuation
`p48oPrimedFluctuationTriple` : near pairs from Lemma 4.9 (`near_pair`) and the a.s.
bound `m³ ≤ A`, far pairs from the named far-pair covariance bound in the triple form (proved as
`p48o_canonical_far_pair`), and joint integrability of the pair kernel. The result is the
unconditional bound `E[(∫_D f (X' − m³))²] ≤ C ε^{min(2q−10ζ, ζ)} ‖f‖²_∞`
(`p48o_secondMoment_triple_of_farPair`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4O

open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4.Canonical

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-! ### Auxiliary facts -/

/-- The jointly measurable centred integrand `f(z) (X̃(ω, z) − m(ω, z))`, with the test extended by
zero off `B_ρ(0)`. -/
def p48oCentredTriple
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ ρ : ℝ) (f : ℂ → ℝ) (ω : Ω) (z : ℂ) : ℝ :=
  p48oTestExt ρ f z * (p48oMaskedVersion D hγ ε q ζ ω z - p48oCondMeanTriple D hγ ε q ζ ω z)

lemma measurable_p48oCentredTriple
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) (q ζ ρ : ℝ) {f : ℂ → ℝ}
    (hfm : P48OTestMeasurable ρ f) :
    Measurable fun p : Ω × ℂ => p48oCentredTriple D hγ ε q ζ ρ f p.1 p.2 :=
  ((measurable_p48oTestExt hfm).comp measurable_snd).mul
    ((measurable_p48oMaskedVersion D hγ hε q ζ).sub (measurable_p48oCondMeanTriple D hγ ε q ζ))

/-- A.s., the centred all-visit integral is the integral of the jointly measurable integrand. -/
lemma p48o_ae_primedFluctuationTriple_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) {ρ : ℝ} {domain : Set ℂ} {f : ℂ → ℝ}
    (hadm : GMS4.Prop48TestPairAdmissible ρ domain f) :
    ∀ᵐ ω ∂P, p48oPrimedFluctuationTriple D hγ ε q ζ domain f ω =
      ∫ z, p48oCentredTriple D hγ ε q ζ ρ f ω z ∂(volume.restrict domain) := by
  filter_upwards [p48o_ae_maskedVersion_eq D hγ ε q ζ,
    p48o_ae_ae_maskedPrime_eq_masked D hγ ε q ζ] with ω h1 h2
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae h2, ae_restrict_mem hadm.domain_borel] with z hz hzD
  simp only [p48oCentredTriple]
  rw [p48oTestExt_eq_of_mem (hadm.domain_subset_ball hzD), h1 z, hz]

/-! ### The uncentred pair moments -/

section Pair

variable (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
  (hγ : γ ∈ Ioo (0 : ℝ) 2)

/-- The a.s. bound `0 ≤ m ≤ A` gives `E[m_z m_w] ≤ A²` at centres of `B_ρ(0)`. -/
lemma p48o_lintegral_condMeanTriple_mul_le {ε q ζ ρ A : ℝ} (hε : 0 ≤ ε) (hA : 0 ≤ A)
    (hmean : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧ ∀ᵐ ω ∂P, p48oCondMeanTriple D hγ ε q ζ ω z ≤ A)
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) ρ) (hw : w ∈ ball (0 : ℂ) ρ) :
    ∫⁻ ω, ENNReal.ofReal (p48oCondMeanTriple D hγ ε q ζ ω z * p48oCondMeanTriple D hγ ε q ζ ω w) ∂P
      ≤ ENNReal.ofReal (A ^ 2) := by
  let _ := D.isProbabilityMeasure
  have hle : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ᵐ ω ∂P, p48oCondMeanTriple D hγ ε q ζ ω z ≤ A :=
    fun z hz => (hmean z hz).2
  calc ∫⁻ ω, ENNReal.ofReal (p48oCondMeanTriple D hγ ε q ζ ω z *
        p48oCondMeanTriple D hγ ε q ζ ω w) ∂P ≤ ∫⁻ _ω, ENNReal.ofReal (A ^ 2) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hle z hz, hle w hw] with ω h1 h2
        refine ENNReal.ofReal_le_ofReal ?_
        rw [sq]
        exact mul_le_mul h1 h2 (p48oCondMeanTriple_nonneg D hγ ε q ζ ω w) hA
    _ = ENNReal.ofReal (A ^ 2) := by rw [lintegral_const, measure_univ, mul_one]

end Pair

/-! ### Near and far pointwise bounds -/

section Bounds

variable (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
  (hγ : γ ∈ Ioo (0 : ℝ) 2)

/-- **Near pairs** (4.32)–(4.33): the centred pair moment is at most `N² (ε^{-2ζ} K + A²)`. -/
lemma p48o_ofReal_integral_centredT_near_le {q ζ ρ : ℝ} (H : Lemma49ConditionalMoments D hγ q ζ ρ)
    {K : ℝ} (hK : 0 ≤ K)
    (hpair : ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) H.epsilonStar →
      ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ w ∈ Metric.ball (0 : ℂ) ρ,
        (∫⁻ ω, ENNReal.ofReal (maskedUStar D hγ ε q ζ z ω) *
          ENNReal.ofReal (maskedUStar D hγ ε q ζ w ω) ∂P) ≤
            ENNReal.ofReal (ε ^ (-ζ)) ^ 2 *
              (ENNReal.ofReal K ^ (1 / (2 : ℝ)) * ENNReal.ofReal K ^ (1 / (2 : ℝ))))
    {A : ℝ} (hA : 0 ≤ A) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) H.epsilonStar)
    (hmean : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧ ∀ᵐ ω ∂P, p48oCondMeanTriple D hγ ε q ζ ω z ≤ A)
    {domain : Set ℂ} {f : ℂ → ℝ} (hadm : GMS4.Prop48TestPairAdmissible ρ domain f)
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) ρ) (hw : w ∈ ball (0 : ℂ) ρ) :
    ENNReal.ofReal (∫ ω, p48oCentredTriple D hγ ε q ζ ρ f ω z *
        p48oCentredTriple D hγ ε q ζ ρ f ω w ∂P) ≤
      ENNReal.ofReal (GMS4.prop48TestSupNorm ρ f ^ 2 * (ε ^ (-(2 * ζ)) * K + A ^ 2)) := by
  set N := GMS4.prop48TestSupNorm ρ f with hN
  obtain ⟨hfz0, hfzN⟩ := p48o_testExt_bounds hadm hz
  obtain ⟨hfw0, hfwN⟩ := p48o_testExt_bounds hadm hw
  have hXm := measurable_p48oMaskedVersion D hγ hε.1.le q ζ
  have hmm := measurable_p48oCondMeanTriple D hγ ε q ζ
  have hXz : Measurable fun ω => p48oMaskedVersion D hγ ε q ζ ω z := by
    have h := hXm.comp (measurable_id.prodMk (measurable_const (a := z)) :
      Measurable fun ω : Ω => (ω, z))
    exact h
  have hXw : Measurable fun ω => p48oMaskedVersion D hγ ε q ζ ω w := by
    have h := hXm.comp (measurable_id.prodMk (measurable_const (a := w)) :
      Measurable fun ω : Ω => (ω, w))
    exact h
  have hpt : ∀ ω, p48oCentredTriple D hγ ε q ζ ρ f ω z * p48oCentredTriple D hγ ε q ζ ρ f ω w ≤
      N ^ 2 * (p48oMaskedVersion D hγ ε q ζ ω z * p48oMaskedVersion D hγ ε q ζ ω w +
        p48oCondMeanTriple D hγ ε q ζ ω z * p48oCondMeanTriple D hγ ε q ζ ω w) := by
    intro ω
    have hx := p48oMaskedVersion_nonneg D hγ ε q ζ ω z
    have hy := p48oMaskedVersion_nonneg D hγ ε q ζ ω w
    have hmx := p48oCondMeanTriple_nonneg D hγ ε q ζ ω z
    have hmy := p48oCondMeanTriple_nonneg D hγ ε q ζ ω w
    have hc := prop48_centered_near_pair_le _ _ _ _ hx hy hmx hmy
    have hbr : 0 ≤ p48oMaskedVersion D hγ ε q ζ ω z * p48oMaskedVersion D hγ ε q ζ ω w +
        p48oCondMeanTriple D hγ ε q ζ ω z * p48oCondMeanTriple D hγ ε q ζ ω w := by positivity
    have hff : p48oTestExt ρ f z * p48oTestExt ρ f w ≤ N ^ 2 := by
      rw [sq]; exact mul_le_mul hfzN hfwN hfw0 ((hfz0).trans hfzN)
    calc p48oCentredTriple D hγ ε q ζ ρ f ω z * p48oCentredTriple D hγ ε q ζ ρ f ω w
        = (p48oTestExt ρ f z * p48oTestExt ρ f w) *
            ((p48oMaskedVersion D hγ ε q ζ ω z - p48oCondMeanTriple D hγ ε q ζ ω z) *
              (p48oMaskedVersion D hγ ε q ζ ω w - p48oCondMeanTriple D hγ ε q ζ ω w)) := by
          simp only [p48oCentredTriple]; ring
      _ ≤ (p48oTestExt ρ f z * p48oTestExt ρ f w) *
            (p48oMaskedVersion D hγ ε q ζ ω z * p48oMaskedVersion D hγ ε q ζ ω w +
              p48oCondMeanTriple D hγ ε q ζ ω z * p48oCondMeanTriple D hγ ε q ζ ω w) :=
          mul_le_mul_of_nonneg_left hc (mul_nonneg hfz0 hfw0)
      _ ≤ N ^ 2 * (p48oMaskedVersion D hγ ε q ζ ω z * p48oMaskedVersion D hγ ε q ζ ω w +
              p48oCondMeanTriple D hγ ε q ζ ω z * p48oCondMeanTriple D hγ ε q ζ ω w) :=
          mul_le_mul_of_nonneg_right hff hbr
  have hmz : Measurable fun ω => p48oCondMeanTriple D hγ ε q ζ ω z := by
    have h := hmm.comp (measurable_id.prodMk (measurable_const (a := z)) :
      Measurable fun ω : Ω => (ω, z))
    exact h
  have hmw : Measurable fun ω => p48oCondMeanTriple D hγ ε q ζ ω w := by
    have h := hmm.comp (measurable_id.prodMk (measurable_const (a := w)) :
      Measurable fun ω : Ω => (ω, w))
    exact h
  calc ENNReal.ofReal (∫ ω, p48oCentredTriple D hγ ε q ζ ρ f ω z *
        p48oCentredTriple D hγ ε q ζ ρ f ω w ∂P)
      ≤ ∫⁻ ω, ENNReal.ofReal (p48oCentredTriple D hγ ε q ζ ρ f ω z *
          p48oCentredTriple D hγ ε q ζ ρ f ω w) ∂P := p48o_ofReal_integral_le_lintegral _
    _ ≤ ∫⁻ ω, ENNReal.ofReal (N ^ 2) *
          (ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) *
              ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) +
            ENNReal.ofReal (p48oCondMeanTriple D hγ ε q ζ ω z *
              p48oCondMeanTriple D hγ ε q ζ ω w)) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_mul (p48oMaskedVersion_nonneg D hγ ε q ζ ω z),
          ← ENNReal.ofReal_add
            (mul_nonneg (p48oMaskedVersion_nonneg D hγ ε q ζ ω z)
              (p48oMaskedVersion_nonneg D hγ ε q ζ ω w))
            (mul_nonneg (p48oCondMeanTriple_nonneg D hγ ε q ζ ω z)
              (p48oCondMeanTriple_nonneg D hγ ε q ζ ω w)),
          ← ENNReal.ofReal_mul (sq_nonneg N)]
        exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (N ^ 2) *
          ((∫⁻ ω, ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) *
              ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) ∂P) +
            ∫⁻ ω, ENNReal.ofReal (p48oCondMeanTriple D hγ ε q ζ ω z *
              p48oCondMeanTriple D hγ ε q ζ ω w) ∂P) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left]
        exact (ENNReal.measurable_ofReal.comp hXz).mul (ENNReal.measurable_ofReal.comp hXw)
    _ ≤ ENNReal.ofReal (N ^ 2) * (ENNReal.ofReal (ε ^ (-(2 * ζ)) * K) + ENNReal.ofReal (A ^ 2)) := by
        gcongr
        · exact p48o_lintegral_maskedVersion_mul_le D hγ H hK hpair hε hz hw
        · exact p48o_lintegral_condMeanTriple_mul_le D hγ hε.1.le hA hmean hz hw
    _ = ENNReal.ofReal (N ^ 2 * (ε ^ (-(2 * ζ)) * K + A ^ 2)) := by
        rw [← ENNReal.ofReal_add (mul_nonneg (Real.rpow_nonneg hε.1.le _) hK) (sq_nonneg A),
          ← ENNReal.ofReal_mul (sq_nonneg N)]

/-- **Far pairs**: the named covariance input, weighted by the test. -/
lemma p48o_ofReal_integral_centredT_far_le {q ζ ρ ε Cf : ℝ} (hCf : 0 ≤ Cf) (hε : 0 ≤ ε)
    (hfar : ∀ z ∈ ball (0 : ℂ) ρ, ∀ w ∈ ball (0 : ℂ) ρ, 2 * ε ^ (q - 4 * ζ) < dist z w →
      ∫ ω, (maskedUStarPrime D hγ ε q ζ z ω - p48oCondMeanTriple D hγ ε q ζ ω z) *
        (maskedUStarPrime D hγ ε q ζ w ω - p48oCondMeanTriple D hγ ε q ζ ω w) ∂P ≤ Cf * ε ^ ζ)
    {domain : Set ℂ} {f : ℂ → ℝ} (hadm : GMS4.Prop48TestPairAdmissible ρ domain f)
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) ρ) (hw : w ∈ ball (0 : ℂ) ρ)
    (hzw : 2 * ε ^ (q - 4 * ζ) < dist z w) :
    ENNReal.ofReal (∫ ω, p48oCentredTriple D hγ ε q ζ ρ f ω z *
        p48oCentredTriple D hγ ε q ζ ρ f ω w ∂P) ≤
      ENNReal.ofReal (GMS4.prop48TestSupNorm ρ f ^ 2 * (Cf * ε ^ ζ)) := by
  obtain ⟨hfz0, hfzN⟩ := p48o_testExt_bounds hadm hz
  obtain ⟨hfw0, hfwN⟩ := p48o_testExt_bounds hadm hw
  have e : (∫ ω, p48oCentredTriple D hγ ε q ζ ρ f ω z * p48oCentredTriple D hγ ε q ζ ρ f ω w ∂P) =
      (p48oTestExt ρ f z * p48oTestExt ρ f w) *
        ∫ ω, (maskedUStarPrime D hγ ε q ζ z ω - p48oCondMeanTriple D hγ ε q ζ ω z) *
          (maskedUStarPrime D hγ ε q ζ w ω - p48oCondMeanTriple D hγ ε q ζ ω w) ∂P := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [p48o_ae_maskedVersion_eq D hγ ε q ζ,
      ae_maskedUStarPrime_eq_masked_fixed D hγ ε q ζ z,
      ae_maskedUStarPrime_eq_masked_fixed D hγ ε q ζ w] with ω h1 h2 h3
    simp only [p48oCentredTriple]
    rw [h1 z, h1 w, h2, h3]
    ring
  rw [e]
  refine ENNReal.ofReal_le_ofReal ?_
  have hff : p48oTestExt ρ f z * p48oTestExt ρ f w ≤ GMS4.prop48TestSupNorm ρ f ^ 2 := by
    rw [sq]; exact mul_le_mul hfzN hfwN hfw0 (hfz0.trans hfzN)
  calc (p48oTestExt ρ f z * p48oTestExt ρ f w) *
        ∫ ω, (maskedUStarPrime D hγ ε q ζ z ω - p48oCondMeanTriple D hγ ε q ζ ω z) *
          (maskedUStarPrime D hγ ε q ζ w ω - p48oCondMeanTriple D hγ ε q ζ ω w) ∂P
      ≤ (p48oTestExt ρ f z * p48oTestExt ρ f w) * (Cf * ε ^ ζ) :=
        mul_le_mul_of_nonneg_left (hfar z hz w hw hzw) (mul_nonneg hfz0 hfw0)
    _ ≤ GMS4.prop48TestSupNorm ρ f ^ 2 * (Cf * ε ^ ζ) :=
        mul_le_mul_of_nonneg_right hff (mul_nonneg hCf (Real.rpow_nonneg hε _))

/-- **Joint integrability of the pair kernel** (the Fubini premise of (4.30)), from Lemma 4.9's
moments and the mean bound. -/
lemma p48o_integrable_pairKernelT {q ζ ρ : ℝ} (H : Lemma49ConditionalMoments D hγ q ζ ρ)
    {K : ℝ} (hK : 0 ≤ K)
    (hpair : ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) H.epsilonStar →
      ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ w ∈ Metric.ball (0 : ℂ) ρ,
        (∫⁻ ω, ENNReal.ofReal (maskedUStar D hγ ε q ζ z ω) *
          ENNReal.ofReal (maskedUStar D hγ ε q ζ w ω) ∂P) ≤
            ENNReal.ofReal (ε ^ (-ζ)) ^ 2 *
              (ENNReal.ofReal K ^ (1 / (2 : ℝ)) * ENNReal.ofReal K ^ (1 / (2 : ℝ))))
    {A : ℝ} (hA : 0 ≤ A) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) H.epsilonStar)
    (hmean : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧ ∀ᵐ ω ∂P, p48oCondMeanTriple D hγ ε q ζ ω z ≤ A)
    {domain : Set ℂ} {f : ℂ → ℝ} (hadm : GMS4.Prop48TestPairAdmissible ρ domain f) :
    Integrable (fun t : Ω × (ℂ × ℂ) => p48oCentredTriple D hγ ε q ζ ρ f t.1 t.2.1 *
        p48oCentredTriple D hγ ε q ζ ρ f t.1 t.2.2)
      (P.prod ((volume.restrict domain).prod (volume.restrict domain))) := by
  let _ := D.isProbabilityMeasure
  set N := GMS4.prop48TestSupNorm ρ f with hN
  have hCm := measurable_p48oCentredTriple D hγ hε.1.le q ζ ρ hadm.test_measurable
  have hp1 : Measurable fun t : Ω × (ℂ × ℂ) => (t.1, t.2.1) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hp2 : Measurable fun t : Ω × (ℂ × ℂ) => (t.1, t.2.2) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have hF : Measurable fun t : Ω × (ℂ × ℂ) => p48oCentredTriple D hγ ε q ζ ρ f t.1 t.2.1 *
      p48oCentredTriple D hγ ε q ζ ρ f t.1 t.2.2 := by
    have h := (hCm.comp hp1).mul (hCm.comp hp2)
    exact h
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  -- one pair
  set Bd : ℝ≥0∞ := ENNReal.ofReal (N ^ 2) *
    (ENNReal.ofReal (ε ^ (-(2 * ζ)) * K) + ENNReal.ofReal (A ^ 2) +
      (ENNReal.ofReal (ε ^ (-(2 * ζ)) * K) + ENNReal.ofReal (A ^ 2))) with hBd
  have hXm := measurable_p48oMaskedVersion D hγ hε.1.le q ζ
  have hmm := measurable_p48oCondMeanTriple D hγ ε q ζ
  have hpairBd : ∀ z ∈ domain, ∀ w ∈ domain,
      ∫⁻ ω, ‖p48oCentredTriple D hγ ε q ζ ρ f ω z * p48oCentredTriple D hγ ε q ζ ρ f ω w‖ₑ ∂P
        ≤ Bd := by
    intro z hzD w hwD
    have hz := hadm.domain_subset_ball hzD
    have hw := hadm.domain_subset_ball hwD
    obtain ⟨hfz0, hfzN⟩ := p48o_testExt_bounds hadm hz
    obtain ⟨hfw0, hfwN⟩ := p48o_testExt_bounds hadm hw
    have hXz : Measurable fun ω => p48oMaskedVersion D hγ ε q ζ ω z := by
      have h := hXm.comp (measurable_id.prodMk (measurable_const (a := z)) :
        Measurable fun ω : Ω => (ω, z))
      exact h
    have hXw : Measurable fun ω => p48oMaskedVersion D hγ ε q ζ ω w := by
      have h := hXm.comp (measurable_id.prodMk (measurable_const (a := w)) :
        Measurable fun ω : Ω => (ω, w))
      exact h
    have hmz : Measurable fun ω => p48oCondMeanTriple D hγ ε q ζ ω z := by
      have h := hmm.comp (measurable_id.prodMk (measurable_const (a := z)) :
        Measurable fun ω : Ω => (ω, z))
      exact h
    have hpt : ∀ ω, ‖p48oCentredTriple D hγ ε q ζ ρ f ω z *
        p48oCentredTriple D hγ ε q ζ ρ f ω w‖ₑ ≤
        ENNReal.ofReal (N ^ 2) *
          (ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) *
              ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) +
            ENNReal.ofReal (p48oCondMeanTriple D hγ ε q ζ ω z *
              p48oCondMeanTriple D hγ ε q ζ ω z) +
          (ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) *
              ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) +
            ENNReal.ofReal (p48oCondMeanTriple D hγ ε q ζ ω w *
              p48oCondMeanTriple D hγ ε q ζ ω w))) := by
      intro ω
      have hx := p48oMaskedVersion_nonneg D hγ ε q ζ ω z
      have hy := p48oMaskedVersion_nonneg D hγ ε q ζ ω w
      have hmx := p48oCondMeanTriple_nonneg D hγ ε q ζ ω z
      have hmy := p48oCondMeanTriple_nonneg D hγ ε q ζ ω w
      set x := p48oMaskedVersion D hγ ε q ζ ω z
      set y := p48oMaskedVersion D hγ ε q ζ ω w
      set mx := p48oCondMeanTriple D hγ ε q ζ ω z
      set my := p48oCondMeanTriple D hγ ε q ζ ω w
      set fz := p48oTestExt ρ f z
      set fw := p48oTestExt ρ f w
      rw [← ENNReal.ofReal_mul hx, ← ENNReal.ofReal_mul hy,
        ← ENNReal.ofReal_add (mul_nonneg hx hx) (mul_nonneg hmx hmx),
        ← ENNReal.ofReal_add (mul_nonneg hy hy) (mul_nonneg hmy hmy),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (sq_nonneg N), Real.enorm_eq_ofReal_abs]
      refine ENNReal.ofReal_le_ofReal ?_
      have habs1 : |x - mx| ≤ x + mx := abs_sub_le_of_nonneg_of_le hx (by linarith) hmx
        (by linarith)
      have habs2 : |y - my| ≤ y + my := abs_sub_le_of_nonneg_of_le hy (by linarith) hmy
        (by linarith)
      have hC : |fz * (x - mx) * (fw * (y - my))| ≤ N ^ 2 * ((x + mx) * (y + my)) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hfz0, abs_of_nonneg hfw0]
        have h1 : fz * |x - mx| ≤ N * (x + mx) :=
          mul_le_mul hfzN habs1 (abs_nonneg _) ((hfz0).trans hfzN)
        have h2 : fw * |y - my| ≤ N * (y + my) :=
          mul_le_mul hfwN habs2 (abs_nonneg _) ((hfw0).trans hfwN)
        calc fz * |x - mx| * (fw * |y - my|) ≤ (N * (x + mx)) * (N * (y + my)) :=
              mul_le_mul h1 h2 (mul_nonneg hfw0 (abs_nonneg _))
                (mul_nonneg ((hfz0).trans hfzN) (by linarith))
          _ = N ^ 2 * ((x + mx) * (y + my)) := by ring
      have hamgm : (x + mx) * (y + my) ≤ x * x + mx * mx + (y * y + my * my) := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (mx - my), sq_nonneg (x - my), sq_nonneg (mx - y)]
      calc |p48oCentredTriple D hγ ε q ζ ρ f ω z * p48oCentredTriple D hγ ε q ζ ρ f ω w|
          = |fz * (x - mx) * (fw * (y - my))| := rfl
        _ ≤ N ^ 2 * ((x + mx) * (y + my)) := hC
        _ ≤ N ^ 2 * (x * x + mx * mx + (y * y + my * my)) :=
          mul_le_mul_of_nonneg_left hamgm (sq_nonneg N)
    have hmw : Measurable fun ω => p48oCondMeanTriple D hγ ε q ζ ω w := by
      have h := hmm.comp (measurable_id.prodMk (measurable_const (a := w)) :
        Measurable fun ω : Ω => (ω, w))
      exact h
    have hmeasz : Measurable fun ω => ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) *
        ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) :=
      (ENNReal.measurable_ofReal.comp hXz).mul (ENNReal.measurable_ofReal.comp hXz)
    have hmeasw : Measurable fun ω => ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) *
        ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) :=
      (ENNReal.measurable_ofReal.comp hXw).mul (ENNReal.measurable_ofReal.comp hXw)
    have hmeasmz : Measurable fun ω => ENNReal.ofReal (p48oCondMeanTriple D hγ ε q ζ ω z *
        p48oCondMeanTriple D hγ ε q ζ ω z) := ENNReal.measurable_ofReal.comp (hmz.mul hmz)
    calc ∫⁻ ω, ‖p48oCentredTriple D hγ ε q ζ ρ f ω z *
          p48oCentredTriple D hγ ε q ζ ρ f ω w‖ₑ ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (N ^ 2) *
          (ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) *
              ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) +
            ENNReal.ofReal (p48oCondMeanTriple D hγ ε q ζ ω z *
              p48oCondMeanTriple D hγ ε q ζ ω z) +
          (ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) *
              ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) +
            ENNReal.ofReal (p48oCondMeanTriple D hγ ε q ζ ω w *
              p48oCondMeanTriple D hγ ε q ζ ω w))) ∂P := lintegral_mono hpt
      _ = ENNReal.ofReal (N ^ 2) *
          ((∫⁻ ω, ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) *
              ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) ∂P) +
            (∫⁻ ω, ENNReal.ofReal (p48oCondMeanTriple D hγ ε q ζ ω z *
              p48oCondMeanTriple D hγ ε q ζ ω z) ∂P) +
          ((∫⁻ ω, ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) *
              ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) ∂P) +
            ∫⁻ ω, ENNReal.ofReal (p48oCondMeanTriple D hγ ε q ζ ω w *
              p48oCondMeanTriple D hγ ε q ζ ω w) ∂P)) := by
          have hzsum : Measurable fun ω =>
              ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) *
                ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) +
              ENNReal.ofReal (p48oCondMeanTriple D hγ ε q ζ ω z *
                p48oCondMeanTriple D hγ ε q ζ ω z) := hmeasz.add hmeasmz
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_left hzsum, lintegral_add_left hmeasz,
            lintegral_add_left hmeasw]
      _ ≤ Bd := by
          rw [hBd]
          gcongr
          · exact p48o_lintegral_maskedVersion_mul_le D hγ H hK hpair hε hz hz
          · exact p48o_lintegral_condMeanTriple_mul_le D hγ hε.1.le hA hmean hz hz
          · exact p48o_lintegral_maskedVersion_mul_le D hγ H hK hpair hε hw hw
          · exact p48o_lintegral_condMeanTriple_mul_le D hγ hε.1.le hA hmean hw hw
  have hmem : ∀ᵐ p ∂((volume.restrict domain).prod (volume.restrict domain)),
      p ∈ domain ×ˢ domain := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (hadm.domain_borel.prod hadm.domain_borel)
  rw [HasFiniteIntegral, lintegral_prod_symm' _ hF.enorm]
  calc ∫⁻ p, ∫⁻ ω, ‖p48oCentredTriple D hγ ε q ζ ρ f ω p.1 *
        p48oCentredTriple D hγ ε q ζ ρ f ω p.2‖ₑ ∂P
          ∂((volume.restrict domain).prod (volume.restrict domain))
      ≤ ∫⁻ _p, Bd ∂((volume.restrict domain).prod (volume.restrict domain)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hmem] with p hp
        exact hpairBd p.1 hp.1 p.2 hp.2
    _ = Bd * (volume domain * volume domain) := by
        rw [lintegral_const, Measure.prod_restrict, Measure.restrict_apply_univ,
          Measure.prod_prod]
    _ < ⊤ := by
        have hD : volume domain < ⊤ := p48o_volume_lt_top_of_admissible hadm
        exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (by simp only [ENNReal.add_lt_top, ENNReal.ofReal_lt_top, and_self]))
          (ENNReal.mul_lt_top hD hD)

end Bounds

/-! ### Assembly of (4.30)–(4.38) -/

/-- **[18] (4.30)–(4.38), unconditional form, with the jointly measurable conditional mean.** For a
radius `ρ`, Lemma 4.9's moments (`H`), the mean bound `A` and the far-pair covariance bound give
`E[(∫_D f (X' − m))²] ≤ C ε^{min(2q−10ζ, ζ)} ‖f‖²_∞` for all small `ε` and all admissible tests. -/
theorem p48o_secondMoment_triple_of_farPair
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {q ζ ρ : ℝ} (hζ : 0 ≤ ζ) (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (H : Lemma49ConditionalMoments D hγ q ζ ρ) {A : ℝ} (hA : 0 ≤ A)
    (hmeanA : ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) H.epsilonStar → ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧ ∀ᵐ ω ∂P, p48oCondMeanTriple D hγ ε q ζ ω z ≤ A)
    {Cf ε₀ : ℝ} (hCf : 0 ≤ Cf)
    (hfar : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ z ∈ ball (0 : ℂ) ρ, ∀ w ∈ ball (0 : ℂ) ρ,
      2 * ε ^ (q - 4 * ζ) < dist z w →
        ∫ ω, (maskedUStarPrime D hγ ε q ζ z ω - p48oCondMeanTriple D hγ ε q ζ ω z) *
          (maskedUStarPrime D hγ ε q ζ w ω - p48oCondMeanTriple D hγ ε q ζ ω w) ∂P ≤
            Cf * ε ^ ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioc (0 : ℝ) (min H.epsilonStar ε₀),
      ∀ (domain : Set ℂ) (f : ℂ → ℝ), GMS4.Prop48TestPairAdmissible ρ domain f →
        ∫⁻ ω, ENNReal.ofReal (p48oPrimedFluctuationTriple D hγ ε q ζ domain f ω ^ 2) ∂P ≤
          ENNReal.ofReal (C * ε ^ GMS4.prop48RateAlpha q ζ * GMS4.prop48TestSupNorm ρ f ^ 2) := by
  let _ := D.isProbabilityMeasure
  obtain ⟨K, hK, hpair⟩ := H.near_pair
  refine ⟨Real.pi ^ 2 * (4 * (K + A ^ 2) + Cf), by positivity, ?_⟩
  intro ε hε domain f hadm
  have hε1 : ε ∈ Ioc (0 : ℝ) H.epsilonStar := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hε2 : ε ∈ Ioc (0 : ℝ) ε₀ := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  have hεle1 : ε ≤ 1 := hε1.2.trans H.epsilonStar_le_one
  have hmean := hmeanA ε hε1
  set N := GMS4.prop48TestSupNorm ρ f with hN
  set r : ℝ := 2 * ε ^ (q - 4 * ζ) with hr
  set a : Ω → ℂ → ℝ := p48oCentredTriple D hγ ε q ζ ρ f with ha
  have htriple := p48o_integrable_pairKernelT D hγ H hK hpair hA hε1 hmean hadm
  have hsquare := GMS4.prop48_square_integrable_of_triple (μ := volume.restrict domain) a htriple
  have hS : MeasurableSet {p : ℂ × ℂ | dist p.1 p.2 ≤ r} :=
    measurableSet_le (measurable_fst.dist measurable_snd) measurable_const
  have hsplit := GMS4.prop48_secondMoment_near_far_positive_split
    (μ := volume.restrict domain) a _ hS htriple hsquare
  have hlhs : ∫⁻ ω, ENNReal.ofReal (p48oPrimedFluctuationTriple D hγ ε q ζ domain f ω ^ 2) ∂P =
      ∫⁻ ω, ENNReal.ofReal ((∫ z, a ω z ∂(volume.restrict domain)) ^ (2 : ℕ)) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [p48o_ae_primedFluctuationTriple_eq D hγ ε q ζ hadm] with ω h
    rw [h]
  -- near pairs
  have hnear : ∫⁻ p in {p : ℂ × ℂ | dist p.1 p.2 ≤ r},
      ENNReal.ofReal (∫ ω, a ω p.1 * a ω p.2 ∂P)
        ∂((volume.restrict domain).prod (volume.restrict domain)) ≤
      ENNReal.ofReal (N ^ 2 * (ε ^ (-(2 * ζ)) * K + A ^ 2)) *
        (volume domain * (ENNReal.ofReal r ^ 2 * (NNReal.pi : ℝ≥0∞))) := by
    refine (p48o_setLIntegral_prod_restrict_le hadm.domain_borel hS
      (fun p _ h1 h2 => p48o_ofReal_integral_centredT_near_le D hγ H hK hpair hA hε1 hmean hadm
        (hadm.domain_subset_ball h1) (hadm.domain_subset_ball h2))).trans ?_
    gcongr
    have hset : {p : ℂ × ℂ | dist p.1 p.2 ≤ r} ∩ domain ×ˢ domain =
        {p : ℂ × ℂ | p.1 ∈ domain ∧ p.2 ∈ domain ∧ dist p.1 p.2 ≤ r} := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_prod]
      tauto
    rw [hset]
    exact GMS4.prop48_nearPair_volume_le domain hadm.domain_borel r
  -- far pairs
  have hfarI : ∫⁻ p in {p : ℂ × ℂ | dist p.1 p.2 ≤ r}ᶜ,
      ENNReal.ofReal (∫ ω, a ω p.1 * a ω p.2 ∂P)
        ∂((volume.restrict domain).prod (volume.restrict domain)) ≤
      ENNReal.ofReal (N ^ 2 * (Cf * ε ^ ζ)) * (volume domain * volume domain) := by
    refine (p48o_setLIntegral_prod_restrict_le hadm.domain_borel hS.compl
      (fun p hp h1 h2 => p48o_ofReal_integral_centredT_far_le D hγ hCf hε.1.le
        (hfar ε hε2) hadm (hadm.domain_subset_ball h1) (hadm.domain_subset_ball h2)
        (lt_of_not_ge hp))).trans ?_
    gcongr
    calc (volume.prod volume) ({p : ℂ × ℂ | dist p.1 p.2 ≤ r}ᶜ ∩ domain ×ˢ domain)
        ≤ (volume.prod volume) (domain ×ˢ domain) := measure_mono Set.inter_subset_right
      _ = volume domain * volume domain := Measure.prod_prod _ _
  have hvol : volume domain ≤ ENNReal.ofReal Real.pi := p48o_volume_le_pi hadm hρ.2.le
  have hpi : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  have hr0 : 0 ≤ r := mul_nonneg (by norm_num) (Real.rpow_nonneg hε.1.le _)
  rw [hlhs]
  calc ∫⁻ ω, ENNReal.ofReal ((∫ z, a ω z ∂(volume.restrict domain)) ^ (2 : ℕ)) ∂P
      ≤ _ := hsplit
    _ ≤ ENNReal.ofReal (N ^ 2 * (ε ^ (-(2 * ζ)) * K + A ^ 2)) *
          (volume domain * (ENNReal.ofReal r ^ 2 * (NNReal.pi : ℝ≥0∞))) +
        ENNReal.ofReal (N ^ 2 * (Cf * ε ^ ζ)) * (volume domain * volume domain) :=
        add_le_add hnear hfarI
    _ ≤ ENNReal.ofReal (N ^ 2 * (ε ^ (-(2 * ζ)) * K + A ^ 2)) *
          (ENNReal.ofReal Real.pi * (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi)) +
        ENNReal.ofReal (N ^ 2 * (Cf * ε ^ ζ)) *
          (ENNReal.ofReal Real.pi * ENNReal.ofReal Real.pi) := by
        rw [hpi]
        gcongr
    _ = ENNReal.ofReal (N ^ 2 * (ε ^ (-(2 * ζ)) * K + A ^ 2) *
          (Real.pi * (r ^ 2 * Real.pi)) + N ^ 2 * (Cf * ε ^ ζ) * (Real.pi * Real.pi)) := by
        have h1 : 0 ≤ N ^ 2 * (ε ^ (-(2 * ζ)) * K + A ^ 2) :=
          mul_nonneg (sq_nonneg _) (add_nonneg (mul_nonneg (Real.rpow_nonneg hε.1.le _) hK)
            (sq_nonneg _))
        have h2 : 0 ≤ N ^ 2 * (Cf * ε ^ ζ) :=
          mul_nonneg (sq_nonneg _) (mul_nonneg hCf (Real.rpow_nonneg hε.1.le _))
        rw [← ENNReal.ofReal_pow hr0, ← ENNReal.ofReal_mul (sq_nonneg r),
          ← ENNReal.ofReal_mul Real.pi_pos.le, ← ENNReal.ofReal_mul h1,
          ← ENNReal.ofReal_mul Real.pi_pos.le, ← ENNReal.ofReal_mul h2,
          ← ENNReal.ofReal_add (mul_nonneg h1 (by positivity)) (mul_nonneg h2 (by positivity))]
    _ ≤ ENNReal.ofReal (Real.pi ^ 2 * (4 * (K + A ^ 2) + Cf) * ε ^ GMS4.prop48RateAlpha q ζ *
          N ^ 2) :=
        ENNReal.ofReal_le_ofReal (p48o_secondMoment_arith hε.1 hεle1 hζ hK hCf)

end MatedCRTHarmonic.GMS4O
