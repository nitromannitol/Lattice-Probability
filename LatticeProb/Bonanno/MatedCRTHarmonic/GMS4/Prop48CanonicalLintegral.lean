/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48CanonicalLintegral at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CanonicalH3
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.Case0
import LatticeProb.Bonanno.MatedCRTHarmonic.Canon.Finiteness

/-!
# Lower-integral carrier for canonical Proposition 4.8

The real and extended densities agree on a full-measure coupling event at
every spatial root. On the measurable spatial regularity event, the test
times the real density is integrable, by the masked first moment and the
all-visit/first-hit spatial identity. Source: [18].
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4.Canonical

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The exceptional identification part has probability zero, simultaneously
at every centre, for each positive mesh. -/
theorem ae_ofReal_uStar_eq_geometric_all_roots
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ z : ℂ,
      ENNReal.ofReal (uStar ε η₀ ω z) = GMS4b.uStar ε (η₀ ω) z := by
  filter_upwards [MatedCRTHarmonic.Canon.ae_referenceRealLocalPoint_eq_geometric_all_roots
    D hγ hε] with ω hω z
  simpa only [uStar, MatedCRTHarmonic.Canon.referenceLocalPoint,
    MatedCRTHarmonic.Canon.localPoint,
    MatedCRTHarmonic.Canon.referenceSample] using (hω z).2.2.2

/-- On a spatial regularity event, H1's first moment makes `f u_*`
integrable on the test domain. -/
theorem ae_integrable_test_uStar_of_goodSpatial
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε)
    {q ζ ρ A : ℝ}
    (hmean : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧
        ∀ᵐ ω ∂P, conditionalMean D hγ ε q ζ ω z ≤ A)
    (E : Set Ω)
    (hElocal : ∀ᵐ ω ∂P, ω ∈ E →
      ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : ℂ) ρ)),
        ω ∈ localEvent D hγ ε q ζ z)
    {domain : Set ℂ} {f : ℂ → ℝ}
    (hadm : GMS4.Prop48TestPairAdmissible ρ domain f) :
    ∀ᵐ ω ∂P, ω ∈ E →
      IntegrableOn (fun z => f z * uStar ε η₀ ω z) domain := by
  filter_upwards [GMS4O.p48o_ae_integrable_test_mul_maskedPrime
    D hγ hε hmean hadm,
    GMS4O.p48o_ae_ae_maskedPrime_eq_masked D hγ ε q ζ,
    hElocal] with ω hint heq hlocal hωE
  refine hint.congr ?_
  have hlocalD := ae_restrict_of_ae_restrict_of_subset
    hadm.domain_subset_ball (hlocal hωE)
  filter_upwards [ae_restrict_of_ae heq, hlocalD] with z hz hmem
  rw [hz]
  simp only [maskedUStar, Set.indicator_of_mem hmem]

/-- The exceptional set in the Bochner-to-lower-integral adapter is
contained modulo null sets in the failure of the spatial regularity event. -/
theorem exceptional_probability_le_of_goodSpatial
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε)
    {q ζ ρ A α Creg : ℝ}
    (hmean : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧
        ∀ᵐ ω ∂P, conditionalMean D hγ ε q ζ ω z ≤ A)
    {E : Set Ω} (hEfail : P Eᶜ ≤ ENNReal.ofReal (Creg * ε ^ α))
    (hElocal : ∀ᵐ ω ∂P, ω ∈ E →
      ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : ℂ) ρ)),
        ω ∈ localEvent D hγ ε q ζ z)
    {domain : Set ℂ} {f : ℂ → ℝ}
    (hadm : GMS4.Prop48TestPairAdmissible ρ domain f) :
    P {ω | ¬ (IntegrableOn (fun z => f z * uStar ε η₀ ω z) domain ∧
      ∀ᵐ z ∂volume.restrict domain,
        ENNReal.ofReal (uStar ε η₀ ω z) = GMS4b.uStar ε (η₀ ω) z)} ≤
      ENNReal.ofReal (Creg * ε ^ α) := by
  have hInt := ae_integrable_test_uStar_of_goodSpatial D hγ hε.le
    hmean E hElocal hadm
  have hEq := ae_ofReal_uStar_eq_geometric_all_roots D hγ hε
  have hsub : {ω | ¬ (IntegrableOn (fun z => f z * uStar ε η₀ ω z) domain ∧
      ∀ᵐ z ∂volume.restrict domain,
        ENNReal.ofReal (uStar ε η₀ ω z) = GMS4b.uStar ε (η₀ ω) z)} ≤ᵐ[P]
      Eᶜ := by
    filter_upwards [hInt, hEq] with ω hωInt hωEq hbad
    by_contra hωEc
    have hωE : ω ∈ E := of_not_not hωEc
    exact hbad ⟨hωInt hωE, (ae_restrict_iff' hadm.domain_borel).2
      (Filter.Eventually.of_forall fun z _ => hωEq z)⟩
  exact (measure_mono_ae hsub).trans hEfail

/-- the exceptional-set estimate with its exponent selected before the
radius. For large meshes the probability-one bound absorbs the geometric
guard and H1's small-mesh range. -/
theorem exceptional_probability_holds
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (q ζ : ℝ) (hq : q ∈ Ioo (0 : ℝ) (min (2 / (2 + γ) ^ 2) γ))
    (hζ : ζ ∈ Ioo (0 : ℝ) (q / 100))
    (H1 : ∀ ρ : ℝ, ρ ∈ Ioo (0 : ℝ) 1 →
      Lemma49ConditionalMoments D hγ q ζ ρ)
    (H2 : ThickGMCReaders D)
    (H3 : Prop48PrimedBorelLocalFactorInput D hγ q ζ H2) :
    ∃ α' : ℝ, 0 < α' ∧ ∀ ρ : ℝ, ρ ∈ Ioo (0 : ℝ) 1 →
      ∃ C' : ℝ, 0 ≤ C' ∧
        ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 →
          ∀ domain : Set ℂ, ∀ f : ℂ → ℝ,
            GMS4.Prop48TestPairAdmissible ρ domain f →
            P {ω | ¬ (IntegrableOn (fun z => f z * uStar ε η₀ ω z) domain ∧
              ∀ᵐ z ∂volume.restrict domain,
                ENNReal.ofReal (uStar ε η₀ ω z) = GMS4b.uStar ε (η₀ ω) z)} ≤
              ENNReal.ofReal (C' * ε ^ α') := by
  obtain ⟨αreg, hαreg, hregular⟩ := H3.exists_uniform_good_spatial hq hζ
  refine ⟨αreg, hαreg, ?_⟩
  intro ρ hρ
  let Hρ := H1 ρ hρ
  have hγsq : 0 < γ ^ 2 := sq_pos_of_pos hγ.1
  have hγsq4 : γ ^ 2 < 4 := by
    have hleft : 0 < 2 - γ := by linarith [hγ.2]
    have hright : 0 < 2 + γ := by linarith [hγ.1]
    nlinarith [mul_pos hleft hright]
  have hratio : 1 < 4 / γ ^ 2 :=
    (lt_div_iff₀ hγsq).2 (by simpa using hγsq4)
  let p : ℝ := (1 + 4 / γ ^ 2) / 2
  have hp1 : 1 < p := by dsimp [p]; linarith
  have hpγ : p < 4 / γ ^ 2 := by dsimp [p]; linarith
  obtain ⟨K, hK, hmean⟩ := Hρ.conditionalMean_le p hp1 hpγ
  let A : ℝ := K + 1
  have hmeanA : ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) Hρ.epsilonStar →
      ∀ z ∈ Metric.ball (0 : ℂ) ρ,
        Integrable (maskedUStar D hγ ε q ζ z) P ∧
        ∀ᵐ ω ∂P, conditionalMean D hγ ε q ζ ω z ≤ A := by
    intro ε hε z hz
    obtain ⟨hi, hb⟩ := hmean ε hε z hz
    refine ⟨hi, ?_⟩
    filter_upwards [hb] with ω hω
    dsimp [A]
    linarith
  obtain ⟨Creg, hreg⟩ := hregular ρ hρ
  let β : ℝ := q - 4 * ζ
  have hβ : 0 < β := by dsimp [β]; linarith [hζ.2, hq.1]
  let d : ℝ := (1 - ρ) / 2
  have hd : 0 < d := by dsimp [d]; linarith [hρ.2]
  let εgeom : ℝ := d ^ (1 / β)
  have hεgeom : 0 < εgeom := Real.rpow_pos_of_pos hd _
  have hεgeom_pow : εgeom ^ β = d := by
    dsimp [εgeom]
    rw [← Real.rpow_mul hd.le]
    have hmul : (1 / β) * β = 1 := by field_simp
    rw [hmul, Real.rpow_one]
  let εsmall : ℝ := min Hρ.epsilonStar εgeom
  have hεsmall : 0 < εsmall := lt_min Hρ.epsilonStar_pos hεgeom
  let Creg' := max 0 Creg
  have hCreg' : 0 ≤ Creg' := le_max_left _ _
  let C' : ℝ := Creg' + 1 / εsmall ^ αreg
  have hinv : 0 ≤ 1 / εsmall ^ αreg :=
    one_div_nonneg.mpr (Real.rpow_pos_of_pos hεsmall _).le
  have hC' : 0 ≤ C' := by
    dsimp [C']
    positivity
  refine ⟨C', hC', ?_⟩
  intro ε hε domain f hadm
  have hεpow : 0 ≤ ε ^ αreg := (Real.rpow_pos_of_pos hε.1 _).le
  by_cases hsmall : ε ≤ εsmall
  · have hεstar : ε ∈ Ioc (0 : ℝ) Hρ.epsilonStar :=
      ⟨hε.1, hsmall.trans (min_le_left _ _)⟩
    have hgeomε : ε ≤ εgeom := hsmall.trans (min_le_right _ _)
    have hgeom : ε ^ (q - 4 * ζ) + ρ < 1 := by
      have hpow : ε ^ β ≤ εgeom ^ β :=
        Real.rpow_le_rpow hε.1.le hgeomε hβ.le
      rw [hεgeom_pow] at hpow
      dsimp [β, d] at hpow
      linarith [hρ.2]
    obtain ⟨E, -, hEfail, hElocal⟩ := hreg ε hε hgeom
    have hbound := exceptional_probability_le_of_goodSpatial
      D hγ hε.1 (hmeanA ε hεstar) hEfail hElocal hadm
    exact hbound.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (by dsimp [C']; linarith [le_max_right (0 : ℝ) Creg, hinv]) hεpow))
  · have hsε : εsmall ≤ ε := (lt_of_not_ge hsmall).le
    have hspow : 0 < εsmall ^ αreg := Real.rpow_pos_of_pos hεsmall _
    have hpow_le : εsmall ^ αreg ≤ ε ^ αreg :=
      Real.rpow_le_rpow hεsmall.le hsε hαreg.le
    have hlarge : 1 ≤ C' * ε ^ αreg := by
      calc
        1 = (1 / εsmall ^ αreg) * εsmall ^ αreg := by field_simp
        _ ≤ (1 / εsmall ^ αreg) * ε ^ αreg :=
          mul_le_mul_of_nonneg_left hpow_le (by positivity)
        _ ≤ C' * ε ^ αreg :=
          mul_le_mul_of_nonneg_right (by dsimp [C']; linarith [hCreg']) hεpow
    letI : IsProbabilityMeasure P := D.isProbabilityMeasure
    have hprob : P {ω | ¬ (IntegrableOn (fun z => f z * uStar ε η₀ ω z) domain ∧
        ∀ᵐ z ∂volume.restrict domain,
          ENNReal.ofReal (uStar ε η₀ ω z) = GMS4b.uStar ε (η₀ ω) z)} ≤ 1 := prob_le_one
    exact hprob.trans (by
      rw [show (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) by norm_num]
      exact ENNReal.ofReal_le_ofReal hlarge)

end MatedCRTHarmonic.GMS4.Canonical

