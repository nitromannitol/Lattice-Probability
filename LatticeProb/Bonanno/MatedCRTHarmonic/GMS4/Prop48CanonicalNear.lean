/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48CanonicalNear at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CanonicalMoments
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48PrimedIntegral
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OCondMean
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48NearMeasure

/-!
# Near pairs for the canonical Proposition 4.8 observable

The local event includes the actual IG phase. Its degree cap and the
authorized Lemma 4.9 area moment give the near-pair estimate (4.32)--(4.34).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4.Canonical

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The pointwise algebra in [18] (4.32): the two mixed terms in the
centered product are nonpositive for nonnegative variables. -/
theorem prop48_centered_near_pair_le (x y mx my : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hmx : 0 ≤ mx) (hmy : 0 ≤ my) :
    (x - mx) * (y - my) ≤ x * y + mx * my := by
  nlinarith [mul_nonneg hx hmy, mul_nonneg hmx hy]

/-- Pointwise near-pair control with the literal phase-aware event. -/
theorem Lemma49ConditionalMoments.near_pair
    {D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm}
    {hγ : γ ∈ Ioo (0 : ℝ) 2} {q ζ ρ : ℝ}
    (H : Lemma49ConditionalMoments D hγ q ζ ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) H.epsilonStar →
      ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ w ∈ Metric.ball (0 : ℂ) ρ,
        (∫⁻ ω, ENNReal.ofReal (maskedUStar D hγ ε q ζ z ω) *
          ENNReal.ofReal (maskedUStar D hγ ε q ζ w ω) ∂P) ≤
            ENNReal.ofReal (ε ^ (-ζ)) ^ 2 *
              (ENNReal.ofReal K ^ (1 / (2 : ℝ)) *
                ENNReal.ofReal K ^ (1 / (2 : ℝ))) := by
  obtain ⟨K, hK, hbound⟩ := H.area_lintegral_le 2 (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro ε hε z hz w hw
  let c : ℝ≥0∞ := ENNReal.ofReal (ε ^ (-ζ))
  let A : ℂ → Ω → ℝ≥0∞ :=
    fun x ω => ENNReal.ofReal (maskedAreaRatio D hγ ε q ζ x ω)
  let V : ℂ → Ω → ℝ≥0∞ :=
    fun x ω => ENNReal.ofReal (maskedUStar D hγ ε q ζ x ω)
  have hAz : AEMeasurable (A z) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (aemeasurable_maskedAreaRatio D hγ hε.1.le q ζ z)
  have hAw : AEMeasurable (A w) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (aemeasurable_maskedAreaRatio D hγ hε.1.le q ζ w)
  have hle : ∀ x ω, V x ω ≤ c * A x ω := by
    intro x ω
    change ENNReal.ofReal (maskedUStar D hγ ε q ζ x ω) ≤
      ENNReal.ofReal (ε ^ (-ζ)) *
        ENNReal.ofReal (maskedAreaRatio D hγ ε q ζ x ω)
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hε.1.le _)]
    exact ENNReal.ofReal_le_ofReal (maskedUStar_le_areaRatio D hγ ε q ζ hε.1.le x ω)
  have hpoint : ∀ ω, V z ω * V w ω ≤ c ^ 2 * (A z ω * A w ω) := by
    intro ω
    calc
      V z ω * V w ω ≤ (c * A z ω) * (c * A w ω) :=
        mul_le_mul' (hle z ω) (hle w ω)
      _ = c ^ 2 * (A z ω * A w ω) := by ring
  have hholder : (∫⁻ ω, A z ω * A w ω ∂P) ≤
      (∫⁻ ω, A z ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) *
        (∫⁻ ω, A w ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq P
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) hAz hAw
  have hboundz : (∫⁻ ω, A z ω ^ (2 : ℝ) ∂P) ≤ ENNReal.ofReal K :=
    calc
      _ = ∫⁻ ω, ENNReal.ofReal |maskedAreaRatio D hγ ε q ζ z ω| ^ (2 : ℝ) ∂P := by
        congr 1
        funext ω
        rw [abs_of_nonneg (maskedAreaRatio_nonneg D hγ ε q ζ z ω)]
      _ ≤ _ := hbound ε hε z hz
  have hboundw : (∫⁻ ω, A w ω ^ (2 : ℝ) ∂P) ≤ ENNReal.ofReal K :=
    calc
      _ = ∫⁻ ω, ENNReal.ofReal |maskedAreaRatio D hγ ε q ζ w ω| ^ (2 : ℝ) ∂P := by
        congr 1
        funext ω
        rw [abs_of_nonneg (maskedAreaRatio_nonneg D hγ ε q ζ w ω)]
      _ ≤ _ := hbound ε hε w hw
  calc
    (∫⁻ ω, V z ω * V w ω ∂P) ≤
        ∫⁻ ω, c ^ 2 * (A z ω * A w ω) ∂P := lintegral_mono hpoint
    _ = c ^ 2 * ∫⁻ ω, A z ω * A w ω ∂P := by
      exact lintegral_const_mul'' (c ^ 2) (hAz.mul hAw)
    _ ≤ c ^ 2 *
        ((∫⁻ ω, A z ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) *
          (∫⁻ ω, A w ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))) :=
      mul_le_mul' le_rfl hholder
    _ ≤ c ^ 2 * (ENNReal.ofReal K ^ (1 / (2 : ℝ)) *
          ENNReal.ofReal K ^ (1 / (2 : ℝ))) := by
      gcongr

end MatedCRTHarmonic.GMS4.Canonical

