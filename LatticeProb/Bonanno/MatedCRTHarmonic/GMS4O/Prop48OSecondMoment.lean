/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4O.Prop48OSecondMoment at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CanonicalNear
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48SecondMoment
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48Rate
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OCondMean

/-!
# The (4.30)–(4.38) second moment with the jointly measurable conditional mean

[18] bounds the second moment of the centred
spatial integral `∫_D f (1_F u_* − m)` by splitting the pair integral into near pairs
`|z − w| ≤ 2 ε^{q−4ζ}` and far pairs. This file assembles that bound for the canonical zero-cone
coupling with `m = p48oCondMeanJoint` (`GMS4O/Prop48OCondMean.lean`):

* near pairs (4.32)–(4.34): the `Lemma49ConditionalMoments.near_pair` (the masked density is at
  most `ε^{-ζ}` times the masked area ratio, plus Lemma 4.9's area moments), and the a.s. bound
  `m ≤ A`, give the centred covariance bound `ε^{-2ζ} K + A²` on a pair set of measure
  `≲ ε^{2q−8ζ}`;
* far pairs (4.35)–(4.37): the pointwise covariance bound `≤ C ε^ζ` is the single named input
  `P48OFarPairCovarianceBound` (the corrected, unconditional form of (4.36));
* joint integrability of the pair kernel (needed by Fubini) is proved here from the same moments.

The result is the **unconditional** bound `E[(∫_D f (X' − m))²] ≤ C ε^{min(2q−10ζ, ζ)} ‖f‖²_∞`
(`p48o_secondMoment_of_farPair`), which implies the source's (4.38) on the good event.
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

lemma p48o_ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : α → ℝ) : ENNReal.ofReal (∫ a, g a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (g a) ∂μ := by
  by_cases hg : Integrable g μ
  · rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg]
    calc ENNReal.ofReal ((∫⁻ a, ENNReal.ofReal (g a) ∂μ).toReal -
          (∫⁻ a, ENNReal.ofReal (-g a) ∂μ).toReal)
        ≤ ENNReal.ofReal (∫⁻ a, ENNReal.ofReal (g a) ∂μ).toReal :=
          ENNReal.ofReal_le_ofReal (sub_le_self _ ENNReal.toReal_nonneg)
      _ ≤ ∫⁻ a, ENNReal.ofReal (g a) ∂μ := ENNReal.ofReal_toReal_le
  · rw [integral_undef hg, ENNReal.ofReal_zero]
    exact zero_le

lemma p48o_ofReal_rpow_half_mul_self {K : ℝ} (hK : 0 ≤ K) :
    ENNReal.ofReal K ^ (1 / (2 : ℝ)) * ENNReal.ofReal K ^ (1 / (2 : ℝ)) = ENNReal.ofReal K := by
  rw [ENNReal.ofReal_rpow_of_nonneg hK (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ← Real.rpow_add' hK (by norm_num)]
  norm_num

lemma p48o_ofReal_rpow_neg_sq {ε ζ : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal (ε ^ (-ζ)) ^ 2 = ENNReal.ofReal (ε ^ (-(2 * ζ))) := by
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hε.le _), ← Real.rpow_natCast,
    ← Real.rpow_mul hε.le]
  norm_num
  ring_nf

/-! ### The uncentred pair moments -/

section Pair

variable (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
  (hγ : γ ∈ Ioo (0 : ℝ) 2)

/-- The uncentred product moment of the masked versions (from the `near_pair`). -/
lemma p48o_lintegral_maskedVersion_mul_le {q ζ ρ : ℝ} (H : Lemma49ConditionalMoments D hγ q ζ ρ)
    {K : ℝ} (hK : 0 ≤ K)
    (hpair : ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) H.epsilonStar →
      ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ w ∈ Metric.ball (0 : ℂ) ρ,
        (∫⁻ ω, ENNReal.ofReal (maskedUStar D hγ ε q ζ z ω) *
          ENNReal.ofReal (maskedUStar D hγ ε q ζ w ω) ∂P) ≤
            ENNReal.ofReal (ε ^ (-ζ)) ^ 2 *
              (ENNReal.ofReal K ^ (1 / (2 : ℝ)) * ENNReal.ofReal K ^ (1 / (2 : ℝ))))
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) H.epsilonStar) {z w : ℂ} (hz : z ∈ ball (0 : ℂ) ρ)
    (hw : w ∈ ball (0 : ℂ) ρ) :
    ∫⁻ ω, ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) *
      ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) ∂P ≤
        ENNReal.ofReal (ε ^ (-(2 * ζ)) * K) := by
  have heq : (fun ω => ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) *
      ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w)) =ᵐ[P]
      fun ω => ENNReal.ofReal (maskedUStar D hγ ε q ζ z ω) *
        ENNReal.ofReal (maskedUStar D hγ ε q ζ w ω) := by
    filter_upwards [p48o_ae_maskedVersion_eq D hγ ε q ζ] with ω h
    rw [h z, h w]
  rw [lintegral_congr_ae heq]
  refine (hpair ε hε z hz w hw).trans (le_of_eq ?_)
  rw [p48o_ofReal_rpow_half_mul_self hK, p48o_ofReal_rpow_neg_sq hε.1,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hε.1.le _)]

end Pair

/-! ### Near and far pointwise bounds -/

section Bounds

variable (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
  (hγ : γ ∈ Ioo (0 : ℝ) 2)

lemma p48o_testExt_bounds {ρ : ℝ} {domain : Set ℂ} {f : ℂ → ℝ}
    (hadm : GMS4.Prop48TestPairAdmissible ρ domain f) {z : ℂ} (hz : z ∈ ball (0 : ℂ) ρ) :
    0 ≤ p48oTestExt ρ f z ∧ p48oTestExt ρ f z ≤ GMS4.prop48TestSupNorm ρ f := by
  rw [p48oTestExt_eq_of_mem hz]
  exact ⟨hadm.test_nonnegative z hz, (le_abs_self _).trans (p48o_abs_test_le hadm hz)⟩

end Bounds

/-! ### Assembly of (4.30)–(4.38) -/

lemma p48o_setLIntegral_prod_restrict_le {domain : Set ℂ} (hD : MeasurableSet domain)
    {S : Set (ℂ × ℂ)} (hS : MeasurableSet S) {F : ℂ × ℂ → ℝ≥0∞} {Bd : ℝ≥0∞}
    (hF : ∀ p ∈ S, p.1 ∈ domain → p.2 ∈ domain → F p ≤ Bd) :
    ∫⁻ p in S, F p ∂((volume.restrict domain).prod (volume.restrict domain)) ≤
      Bd * (volume.prod volume) (S ∩ domain ×ˢ domain) := by
  rw [Measure.prod_restrict, Measure.restrict_restrict hS]
  calc ∫⁻ p in S ∩ domain ×ˢ domain, F p ∂(volume.prod volume)
      ≤ ∫⁻ _p in S ∩ domain ×ˢ domain, Bd ∂(volume.prod volume) :=
        setLIntegral_mono' (hS.inter (hD.prod hD)) fun p hp => hF p hp.1 hp.2.1 hp.2.2
    _ = Bd * (volume.prod volume) (S ∩ domain ×ˢ domain) := setLIntegral_const _ _

/-- The real arithmetic of (4.34), (4.37) and (4.38). -/
lemma p48o_secondMoment_arith {ε q ζ K A Cf N : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hζ : 0 ≤ ζ)
    (hK : 0 ≤ K) (hCf : 0 ≤ Cf) :
    N ^ 2 * (ε ^ (-(2 * ζ)) * K + A ^ 2) * (Real.pi * ((2 * ε ^ (q - 4 * ζ)) ^ 2 * Real.pi)) +
        N ^ 2 * (Cf * ε ^ ζ) * (Real.pi * Real.pi) ≤
      Real.pi ^ 2 * (4 * (K + A ^ 2) + Cf) * ε ^ GMS4.prop48RateAlpha q ζ * N ^ 2 := by
  have hsq : (2 * ε ^ (q - 4 * ζ)) ^ 2 = 4 * ε ^ (2 * q - 8 * ζ) := by
    rw [mul_pow, ← Real.rpow_natCast (ε ^ (q - 4 * ζ)), ← Real.rpow_mul hε.le]
    congr 1
    · norm_num
    · congr 1
      push_cast
      ring
  have hprod : ε ^ (-(2 * ζ)) * ε ^ (2 * q - 8 * ζ) = ε ^ (2 * q - 10 * ζ) := by
    rw [← Real.rpow_add hε]
    congr 1
    ring
  have h21 : ε ^ (2 * q - 8 * ζ) ≤ ε ^ (2 * q - 10 * ζ) :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  have h1a : ε ^ (2 * q - 10 * ζ) ≤ ε ^ GMS4.prop48RateAlpha q ζ :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (min_le_left _ _)
  have hza : ε ^ ζ ≤ ε ^ GMS4.prop48RateAlpha q ζ :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (min_le_right _ _)
  have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
  have hnear : (ε ^ (-(2 * ζ)) * K + A ^ 2) * (4 * ε ^ (2 * q - 8 * ζ)) ≤
      4 * (K + A ^ 2) * ε ^ GMS4.prop48RateAlpha q ζ := by
    have e : (ε ^ (-(2 * ζ)) * K + A ^ 2) * (4 * ε ^ (2 * q - 8 * ζ)) =
        4 * (K * ε ^ (2 * q - 10 * ζ) + A ^ 2 * ε ^ (2 * q - 8 * ζ)) := by
      rw [← hprod]; ring
    rw [e]
    have h1 : K * ε ^ (2 * q - 10 * ζ) ≤ K * ε ^ GMS4.prop48RateAlpha q ζ :=
      mul_le_mul_of_nonneg_left h1a hK
    have h2 : A ^ 2 * ε ^ (2 * q - 8 * ζ) ≤ A ^ 2 * ε ^ GMS4.prop48RateAlpha q ζ :=
      mul_le_mul_of_nonneg_left (h21.trans h1a) hA2
    nlinarith
  have hfar : Cf * ε ^ ζ ≤ Cf * ε ^ GMS4.prop48RateAlpha q ζ := mul_le_mul_of_nonneg_left hza hCf
  rw [hsq]
  have e : N ^ 2 * (ε ^ (-(2 * ζ)) * K + A ^ 2) * (Real.pi * (4 * ε ^ (2 * q - 8 * ζ) * Real.pi)) +
      N ^ 2 * (Cf * ε ^ ζ) * (Real.pi * Real.pi) =
      Real.pi ^ 2 * N ^ 2 * ((ε ^ (-(2 * ζ)) * K + A ^ 2) * (4 * ε ^ (2 * q - 8 * ζ)) +
        Cf * ε ^ ζ) := by ring
  rw [e]
  have e' : Real.pi ^ 2 * (4 * (K + A ^ 2) + Cf) * ε ^ GMS4.prop48RateAlpha q ζ * N ^ 2 =
      Real.pi ^ 2 * N ^ 2 * (4 * (K + A ^ 2) * ε ^ GMS4.prop48RateAlpha q ζ +
        Cf * ε ^ GMS4.prop48RateAlpha q ζ) := by ring
  rw [e']
  exact mul_le_mul_of_nonneg_left (add_le_add hnear hfar) (by positivity)

end MatedCRTHarmonic.GMS4O
