/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48CanonicalMoments at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CanonicalStatement

/-!
# Exact canonical conditional-moment input for [18] Lemma 4.9

This is the one authorized pending Lemma 4.9 hypothesis for Proposition 4.8.
It states only (4.24)--(4.25), for the literal 0-cone localized point
observables and the physical two-field conditioning pair. Integrability is
included because mathlib's conditional expectation otherwise has a zero
fallback on a nonintegrable function.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4.Canonical

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The literal real masked `DA^ε(z)` on the reference 0-cone curve. -/
def maskedAreaRatio
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) (ω : Ω) : ℝ :=
  (localEvent D hγ ε q ζ z).indicator
    (fun ω' => (MatedCRTHarmonic.Canon.realLocalPoint ε (η₀ ω') z).areaRatio) ω

theorem maskedAreaRatio_nonneg
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) (ω : Ω) :
    0 ≤ maskedAreaRatio D hγ ε q ζ z ω := by
  by_cases hω : ω ∈ localEvent D hγ ε q ζ z
  · simp only [maskedAreaRatio, Set.indicator_of_mem hω,
      MatedCRTHarmonic.Canon.realLocalPoint,
      MatedCRTHarmonic.GMS4F.realAreaRatio]
    exact ENNReal.toReal_nonneg
  · simp [maskedAreaRatio, Set.indicator_of_notMem hω]

/-- The canonical masked area ratio is measurable modulo null sets at each
fixed centre; the phase-bearing event is read from the frozen coupling. -/
theorem aemeasurable_maskedAreaRatio
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {ε : ℝ} (hε : 0 ≤ ε) (q ζ : ℝ) (z : ℂ) :
    AEMeasurable (maskedAreaRatio D hγ ε q ζ z) P := by
  have hp : Measurable (fun ω : Ω => (η₀ ω, z)) :=
    D.measurable_curves.2.2.1.prodMk measurable_const
  have hc : Measurable (fun ω =>
      (MatedCRTHarmonic.Canon.realLocalPoint ε (η₀ ω) z).areaRatio) := by
    simpa only [MatedCRTHarmonic.Canon.realLocalPoint,
      MatedCRTHarmonic.GMS4F.realAreaRatio, Function.comp_def] using
      (ENNReal.measurable_toReal.comp (GMS4b.measurable_areaRatio ε)).comp hp
  have hE : NullMeasurableSet (localEvent D hγ ε q ζ z) P :=
    MatedCRTHarmonic.Canon.nullMeasurableSet_referenceLocalEvent D hγ hε z
  exact hc.aemeasurable.indicator₀ hE

/-- The degree cap in the literal local event bounds the real density by
The masked area ratio, including the infinite geometric area case. -/
theorem maskedUStar_le_areaRatio
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (hε : 0 ≤ ε) (z : ℂ) (ω : Ω) :
    maskedUStar D hγ ε q ζ z ω ≤
      ε ^ (-ζ) * maskedAreaRatio D hγ ε q ζ z ω := by
  by_cases hω : ω ∈ localEvent D hγ ε q ζ z
  · let n : ℕ∞ := GMS4b.degreeIn ε (η₀ ω) z + GMS4b.degreeOut ε (η₀ ω) z
    have hdeg : (n : ℝ≥0∞) ≤ ENNReal.ofReal (ε ^ (-ζ)) := by
      exact (show ω ∈ MatedCRTHarmonic.Canon.referenceLocalEvent D hγ ε q ζ z
        from hω).2.1
    have hnat : ENNReal.ofReal
        ((((MatedCRTHarmonic.Canon.realLocalPoint ε (η₀ ω) z).degreeIn +
          (MatedCRTHarmonic.Canon.realLocalPoint ε (η₀ ω) z).degreeOut : ℕ) : ℝ)) ≤
          ENNReal.ofReal (ε ^ (-ζ)) := by
      rw [ENNReal.ofReal_natCast, Nat.cast_add]
      have h1 : ((MatedCRTHarmonic.GMS4F.natDegreeIn ε (η₀ ω) z : ℕ) : ℝ≥0∞) ≤
          ((GMS4b.degreeIn ε (η₀ ω) z : ℕ∞) : ℝ≥0∞) :=
        ENat.toENNReal_mono (ENat.natCast_toNat_le_self _)
      have h2 : ((MatedCRTHarmonic.GMS4F.natDegreeOut ε (η₀ ω) z : ℕ) : ℝ≥0∞) ≤
          ((GMS4b.degreeOut ε (η₀ ω) z : ℕ∞) : ℝ≥0∞) :=
        ENat.toENNReal_mono (ENat.natCast_toNat_le_self _)
      have hdeg' :
          ((GMS4b.degreeIn ε (η₀ ω) z : ℕ∞) : ℝ≥0∞) +
            ((GMS4b.degreeOut ε (η₀ ω) z : ℕ∞) : ℝ≥0∞) ≤
              ENNReal.ofReal (ε ^ (-ζ)) := by
        simpa only [n, ENat.toENNReal_add] using hdeg
      simpa only [MatedCRTHarmonic.Canon.realLocalPoint] using
        (add_le_add h1 h2).trans hdeg'
    have hreal :
        ((((MatedCRTHarmonic.Canon.realLocalPoint ε (η₀ ω) z).degreeIn +
          (MatedCRTHarmonic.Canon.realLocalPoint ε (η₀ ω) z).degreeOut : ℕ) : ℝ)) ≤
          ε ^ (-ζ) :=
      (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hε _)).1 hnat
    simp only [maskedUStar, maskedAreaRatio, Set.indicator_of_mem hω,
      uStar, MatedCRTHarmonic.Canon.realLocalPoint_formula]
    have harea : 0 ≤ (MatedCRTHarmonic.Canon.realLocalPoint ε (η₀ ω) z).areaRatio :=
      ENNReal.toReal_nonneg
    calc
      _ ≤ (MatedCRTHarmonic.Canon.realLocalPoint ε (η₀ ω) z).areaRatio * ε ^ (-ζ) :=
        mul_le_mul_of_nonneg_left hreal harea
      _ = _ := mul_comm _ _
  · simp [maskedUStar, maskedAreaRatio, Set.indicator_of_notMem hω]

/-- `p`th power of the nonnegative masked area ratio. -/
def areaMomentVariable
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ p : ℝ) (z : ℂ) (ω : Ω) : ℝ :=
  (max 0 (maskedAreaRatio D hγ ε q ζ z ω)) ^ p

/-- `p`th power of the nonnegative masked `u_*^ε(z)`. -/
def densityMomentVariable
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ p : ℝ) (z : ℂ) (ω : Ω) : ℝ :=
  (max 0 (maskedUStar D hγ ε q ζ z ω)) ^ p

/-- The exact two uniform conditional-moment conclusions of [18] Lemma 4.9,
with the measurable version of the physical IG-phase observation. Constants
may depend on `ρ`, `q`, `ζ`, and `p`, but are uniform in the centre and mesh.
This record has no regularity-event or Proposition 4.8 probability conclusion. -/
structure Lemma49ConditionalMoments
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (q ζ ρ : ℝ) where
  epsilonStar : ℝ
  epsilonStar_pos : 0 < epsilonStar
  epsilonStar_le_one : epsilonStar ≤ 1
  area : ∀ p : ℝ, 1 ≤ p → ∃ K : ℝ, 0 ≤ K ∧
    ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) epsilonStar →
      ∀ z ∈ Metric.ball (0 : ℂ) ρ,
        Integrable (areaMomentVariable D hγ ε q ζ p z) P ∧
        ∀ᵐ ω ∂P,
          P[areaMomentVariable D hγ ε q ζ p z |
            MeasurableSpace.comap (circleObservation D hγ ε q ζ z)
              inferInstance] ω ≤ K
  density : ∀ p : ℝ, 1 < p → p < 4 / γ ^ 2 → ∃ K : ℝ, 0 ≤ K ∧
    ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) epsilonStar →
      ∀ z ∈ Metric.ball (0 : ℂ) ρ,
        Integrable (densityMomentVariable D hγ ε q ζ p z) P ∧
        ∀ᵐ ω ∂P,
          P[densityMomentVariable D hγ ε q ζ p z |
            MeasurableSpace.comap (circleObservation D hγ ε q ζ z)
              inferInstance] ω ≤ K

/-- The conditional area-moment estimate gives the unconditional bound used
for near pairs, uniformly in centre and small mesh. -/
theorem Lemma49ConditionalMoments.area_integral_le
    {D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm}
    {hγ : γ ∈ Ioo (0 : ℝ) 2} {q ζ ρ : ℝ}
    (H : Lemma49ConditionalMoments D hγ q ζ ρ)
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) H.epsilonStar →
      ∀ z ∈ Metric.ball (0 : ℂ) ρ,
        ∫ ω, areaMomentVariable D hγ ε q ζ p z ω ∂P ≤ K := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨K, hK, hbound⟩ := H.area p hp
  refine ⟨K, hK, ?_⟩
  intro ε hε z hz
  obtain ⟨hi, hb⟩ := hbound ε hε z hz
  have hm : MeasurableSpace.comap (circleObservation D hγ ε q ζ z)
      inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    (measurable_circleObservation D hγ ε q ζ z).comap_le
  have hce : (∫ ω, P[areaMomentVariable D hγ ε q ζ p z |
      MeasurableSpace.comap (circleObservation D hγ ε q ζ z) inferInstance] ω ∂P) =
      ∫ ω, areaMomentVariable D hγ ε q ζ p z ω ∂P :=
    integral_condExp hm
  rw [← hce]
  calc
    (∫ ω, P[areaMomentVariable D hγ ε q ζ p z |
        MeasurableSpace.comap (circleObservation D hγ ε q ζ z) inferInstance] ω ∂P) ≤
        ∫ _ω : Ω, K ∂P :=
      integral_mono_ae integrable_condExp (integrable_const K) hb
    _ = K := by simp

/-- The near-pair Cauchy--Schwarz bound consumes the second `ENNReal`
moment of the literal masked area ratio. -/
theorem Lemma49ConditionalMoments.area_lintegral_le
    {D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm}
    {hγ : γ ∈ Ioo (0 : ℝ) 2} {q ζ ρ : ℝ}
    (H : Lemma49ConditionalMoments D hγ q ζ ρ)
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) H.epsilonStar →
      ∀ z ∈ Metric.ball (0 : ℂ) ρ,
        (∫⁻ ω, ENNReal.ofReal |maskedAreaRatio D hγ ε q ζ z ω| ^ p ∂P) ≤
          ENNReal.ofReal K := by
  obtain ⟨K, hK, hbound⟩ := H.area_integral_le p hp
  refine ⟨K, hK, ?_⟩
  intro ε hε z hz
  obtain ⟨hi, -⟩ := (H.area p hp).choose_spec.2 ε hε z hz
  have hnonneg : 0 ≤ᵐ[P] areaMomentVariable D hγ ε q ζ p z :=
    Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (le_max_left 0 _) p
  have hfun : (fun ω => ENNReal.ofReal |maskedAreaRatio D hγ ε q ζ z ω| ^ p) =
      fun ω => ENNReal.ofReal (areaMomentVariable D hγ ε q ζ p z ω) := by
    funext ω
    have hY := maskedAreaRatio_nonneg D hγ ε q ζ z ω
    simp only [areaMomentVariable, abs_of_nonneg hY, max_eq_right hY]
    exact ENNReal.ofReal_rpow_of_nonneg hY (by linarith : 0 ≤ p)
  rw [hfun]
  calc
    (∫⁻ ω, ENNReal.ofReal (areaMomentVariable D hγ ε q ζ p z ω) ∂P) =
        ENNReal.ofReal (∫ ω, areaMomentVariable D hγ ε q ζ p z ω ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hi hnonneg).symm
    _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal (hbound ε hε z hz)

/-- The same tower step gives the unconditional masked-density moment used
in the translated A.3 and far-pair estimates. -/
theorem Lemma49ConditionalMoments.density_integral_le
    {D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm}
    {hγ : γ ∈ Ioo (0 : ℝ) 2} {q ζ ρ : ℝ}
    (H : Lemma49ConditionalMoments D hγ q ζ ρ)
    (p : ℝ) (hp : 1 < p) (hpγ : p < 4 / γ ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) H.epsilonStar →
      ∀ z ∈ Metric.ball (0 : ℂ) ρ,
        ∫ ω, densityMomentVariable D hγ ε q ζ p z ω ∂P ≤ K := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨K, hK, hbound⟩ := H.density p hp hpγ
  refine ⟨K, hK, ?_⟩
  intro ε hε z hz
  obtain ⟨hi, hb⟩ := hbound ε hε z hz
  have hm : MeasurableSpace.comap (circleObservation D hγ ε q ζ z)
      inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    (measurable_circleObservation D hγ ε q ζ z).comap_le
  have hce : (∫ ω, P[densityMomentVariable D hγ ε q ζ p z |
      MeasurableSpace.comap (circleObservation D hγ ε q ζ z) inferInstance] ω ∂P) =
      ∫ ω, densityMomentVariable D hγ ε q ζ p z ω ∂P :=
    integral_condExp hm
  rw [← hce]
  calc
    (∫ ω, P[densityMomentVariable D hγ ε q ζ p z |
        MeasurableSpace.comap (circleObservation D hγ ε q ζ z) inferInstance] ω ∂P) ≤
        ∫ _ω : Ω, K ∂P :=
      integral_mono_ae integrable_condExp (integrable_const K) hb
    _ = K := by simp

/-- The far-pair A.3 lemma consumes an `ENNReal` `L^p` moment. The authorized
Lemma 4.9 bound supplies it, without using conditional expectation's fallback. -/
theorem Lemma49ConditionalMoments.density_lintegral_le
    {D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm}
    {hγ : γ ∈ Ioo (0 : ℝ) 2} {q ζ ρ : ℝ}
    (H : Lemma49ConditionalMoments D hγ q ζ ρ)
    (p : ℝ) (hp : 1 < p) (hpγ : p < 4 / γ ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) H.epsilonStar →
      ∀ z ∈ Metric.ball (0 : ℂ) ρ,
        (∫⁻ ω, ENNReal.ofReal |maskedUStar D hγ ε q ζ z ω| ^ p ∂P) ≤
          ENNReal.ofReal K := by
  obtain ⟨K, hK, hbound⟩ := H.density_integral_le p hp hpγ
  refine ⟨K, hK, ?_⟩
  intro ε hε z hz
  obtain ⟨hi, -⟩ := (H.density p hp hpγ).choose_spec.2 ε hε z hz
  have hnonneg : 0 ≤ᵐ[P] densityMomentVariable D hγ ε q ζ p z :=
    Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (le_max_left 0 _) p
  have hfun : (fun ω => ENNReal.ofReal |maskedUStar D hγ ε q ζ z ω| ^ p) =
      fun ω => ENNReal.ofReal (densityMomentVariable D hγ ε q ζ p z ω) := by
    funext ω
    have hY := maskedUStar_nonneg D hγ ε q ζ z ω
    simp only [densityMomentVariable, abs_of_nonneg hY, max_eq_right hY]
    exact ENNReal.ofReal_rpow_of_nonneg hY (by linarith : 0 ≤ p)
  rw [hfun]
  calc
    (∫⁻ ω, ENNReal.ofReal (densityMomentVariable D hγ ε q ζ p z ω) ∂P) =
        ENNReal.ofReal (∫ ω, densityMomentVariable D hγ ε q ζ p z ω ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hi hnonneg).symm
    _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal (hbound ε hε z hz)

/-- Equation (4.27), with one deterministic bound for all small scales and
centres. The conclusion is almost sure, as in the source. -/
theorem Lemma49ConditionalMoments.conditionalMean_le
    {D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm}
    {hγ : γ ∈ Ioo (0 : ℝ) 2} {q ζ ρ : ℝ}
    (H : Lemma49ConditionalMoments D hγ q ζ ρ)
    (p : ℝ) (hp : 1 < p) (hpγ : p < 4 / γ ^ 2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) H.epsilonStar →
      ∀ z ∈ Metric.ball (0 : ℂ) ρ,
        Integrable (maskedUStar D hγ ε q ζ z) P ∧
        ∀ᵐ ω ∂P, conditionalMean D hγ ε q ζ ω z ≤ A := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨K, hK, hbound⟩ := H.density p hp hpγ
  refine ⟨max 1 K, by positivity, ?_⟩
  intro ε hε z hz
  obtain ⟨hpow, hb⟩ := hbound ε hε z hz
  let Y : Ω → ℝ := maskedUStar D hγ ε q ζ z
  have hYmeas : AEStronglyMeasurable Y P :=
    (aemeasurable_maskedUStar D hγ hε.1.le q ζ z).aestronglyMeasurable
  have hYpow : Integrable (fun ω => ‖Y ω‖ ^ p) P := by
    have heq : (fun ω => ‖Y ω‖ ^ p) =
        densityMomentVariable D hγ ε q ζ p z := by
      funext ω
      simp only [Y, densityMomentVariable, Real.norm_eq_abs,
        abs_of_nonneg (maskedUStar_nonneg D hγ ε q ζ z ω),
        max_eq_right (maskedUStar_nonneg D hγ ε q ζ z ω)]
    rw [heq]
    exact hpow
  have hYint : Integrable Y P := by
    have hnorm := integrable_norm_rpow_of_le hYmeas
      (show (0 : ℝ) ≤ 1 by norm_num) (by linarith : 0 ≤ p) hp.le hYpow
    have hnorm1 : Integrable (fun ω => ‖Y ω‖) P := by
      simpa only [Real.rpow_one] using hnorm
    exact (integrable_norm_iff hYmeas).1 hnorm1
  refine ⟨hYint, ?_⟩
  have hJ : (fun ω => ‖P[Y | MeasurableSpace.comap
        (circleObservation D hγ ε q ζ z) inferInstance] ω‖ ^ p) ≤ᵐ[P]
      P[(fun ω => ‖Y ω‖ ^ p) | MeasurableSpace.comap
        (circleObservation D hγ ε q ζ z) inferInstance] :=
    Integrable.norm_condExp_rpow_le hp.le hYpow
  have hpowEq : (fun ω => ‖Y ω‖ ^ p) = densityMomentVariable D hγ ε q ζ p z := by
    funext ω
    simp only [Y, densityMomentVariable, Real.norm_eq_abs,
      abs_of_nonneg (maskedUStar_nonneg D hγ ε q ζ z ω),
      max_eq_right (maskedUStar_nonneg D hγ ε q ζ z ω)]
  filter_upwards [hJ, hb] with ω hJω hbω
  have hboundpow : ‖P[Y | MeasurableSpace.comap
      (circleObservation D hγ ε q ζ z) inferInstance] ω‖ ^ p ≤ K := by
    rw [hpowEq] at hJω
    exact hJω.trans hbω
  by_cases hlarge : 1 ≤ ‖P[Y | MeasurableSpace.comap
      (circleObservation D hγ ε q ζ z) inferInstance] ω‖
  · have hraw : P[Y | MeasurableSpace.comap
        (circleObservation D hγ ε q ζ z) inferInstance] ω ≤ K :=
      (le_abs_self _).trans ((Real.self_le_rpow_of_one_le hlarge hp.le).trans hboundpow)
    exact hraw.trans (le_max_right _ _)
  · exact (le_abs_self _).trans ((le_of_not_ge hlarge).trans (le_max_left _ _))

end MatedCRTHarmonic.GMS4.Canonical

