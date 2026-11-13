/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4O.Prop48OTripleH4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OCondMean
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OKernelGeneric
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48Rate

/-!
# The -corrected good-event second-moment input

(2): in the far-pair estimate of [18] Proposition 4.8 the conditional mean conditions on the
triple `((h₀_r(z), hIG₀_r(z)), U)` (field average, normalized IG average, phase), not on the pair
`(h₀_r(z), hIG₀_r(z) + U)`. This file fixes the exact objects:

* `p48oTripleObsVersion`: the jointly measurable triple, built from measurable versions of the
  zero-cone **field** and of the phase (so it is the literal triple for all centres at once, a.s.);
* `p48oCondMeanTriple`: the jointly measurable conditional mean `m³(ω, z)`, the kernel version of
  `E[maskedUStar z | triple z]` (`GMS4O/Prop48OKernelGeneric.lean`);
* `p48oPrimedFluctuationTriple`: the centred all-visit spatial integral `∫_D f (X' − m³)`;
* `Prop48GoodEventSecondMomentInputTriple`: the source's (4.38) on a measurable spatial good event,
  in the shape of the `GMS4.Canonical.Prop48GoodEventSecondMomentInput` with `m³` in place of the
  pair mean, and with the mean premise stated for `m³`.
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

/-- The jointly measurable conditioning triple `((h₀_r(z), hIG₀_r(z)), U)` of, at the
conditioning radius `r = ε^(q−4ζ)` of [18] (4.22). -/
def p48oTripleObsVersion
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (ω : Ω) (z : ℂ) : (ℝ × ℝ) × ℝ :=
  ((LQGMetric.circleAvg (p48oZeroConeFieldVersion D hγ ω)
      (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z,
    LQGMetric.circleAvg (hIG₀ ω) (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z),
    phaseVersion D hγ ω)

/-- **The conditional mean** `m³(ω, z)`: the jointly measurable kernel version of
`E[maskedUStar z | ((h₀_r(z), hIG₀_r(z)), U)]`. -/
def p48oCondMeanTriple
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (ω : Ω) (z : ℂ) : ℝ :=
  letI := D.isProbabilityMeasure
  p48oCondValueG P (p48oTripleObsVersion D hγ ε q ζ) (p48oMaskedVersion D hγ ε q ζ)
    (z, p48oTripleObsVersion D hγ ε q ζ ω z)

/-- The centred all-visit integral `∫_D f (X' − m³)` of [18] (4.28)–(4.29), with the mean. -/
def p48oPrimedFluctuationTriple
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (domain : Set ℂ) (f : ℂ → ℝ) (ω : Ω) : ℝ :=
  ∫ z in domain, f z * (maskedUStarPrime D hγ ε q ζ z ω - p48oCondMeanTriple D hγ ε q ζ ω z)

/-- **The corrected H4**: [18] (4.38) for the triple-centred fluctuation on a measurable
spatial good event. Same quantifier shape as the `Prop48GoodEventSecondMomentInput`; the mean
premise is the a.s. bound `m³ ≤ A` used by the (4.29) comparison. -/
def Prop48GoodEventSecondMomentInputTriple
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (q ζ : ℝ)
    (H1 : ∀ ρ : ℝ, ρ ∈ Ioo (0 : ℝ) 1 → Lemma49ConditionalMoments D hγ q ζ ρ) : Prop :=
  ∀ ρ : ℝ, (hρ : ρ ∈ Ioo (0 : ℝ) 1) →
    ∀ A : ℝ, 0 < A →
      (∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) (H1 ρ hρ).epsilonStar →
        ∀ z ∈ Metric.ball (0 : ℂ) ρ,
          Integrable (maskedUStar D hγ ε q ζ z) P ∧
          ∀ᵐ ω ∂P, p48oCondMeanTriple D hγ ε q ζ ω z ≤ A) →
      ∃ Cvar : ℝ, 0 ≤ Cvar ∧ ∃ εvar : ℝ, 0 < εvar ∧
        ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) (min (H1 ρ hρ).epsilonStar εvar) →
          ∀ E : Set Ω, MeasurableSet E →
            (∀ᵐ ω ∂P, ω ∈ E →
              ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : ℂ) ρ)),
                ω ∈ localEvent D hγ ε q ζ z) →
            ∀ domain : Set ℂ, ∀ f : ℂ → ℝ,
              GMS4.Prop48TestPairAdmissible ρ domain f →
              (∫⁻ ω in E, ENNReal.ofReal
                (p48oPrimedFluctuationTriple D hγ ε q ζ domain f ω ^ 2) ∂P) ≤
              ENNReal.ofReal (Cvar * ε ^ (GMS4.prop48RateAlpha q ζ) *
                (GMS4.prop48TestSupNorm ρ f) ^ 2)

end MatedCRTHarmonic.GMS4O
