/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48CanonicalTripleConclusion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CanonicalTripleTail
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CanonicalLintegral
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cQ.ThickReaders
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cS.Lemma49Complete

/-!
# -corrected canonical Proposition 4.8

The far-pair fluctuation is centred by the jointly measurable conditional
mean given the separate two circle averages and the IG phase.
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

/-- Assembly of canonical Proposition 4.8 with the triple-centred H4.
The auxiliary H1 cutoff equality is supplied by the canonical producer in
`prop48_canonical_of_tripleH4` below. -/
theorem prop48_canonical_of_tripleH4_aux
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (q ζ : ℝ) (hq : q ∈ Ioo (0 : ℝ) (min (2 / (2 + γ) ^ 2) γ))
    (hζ : ζ ∈ Ioo (0 : ℝ) (q / 100))
    (H1 : ∀ ρ : ℝ, ρ ∈ Ioo (0 : ℝ) 1 →
      Lemma49ConditionalMoments D hγ q ζ ρ)
    (hH1eps : ∀ ρ : ℝ, ∀ hρ : ρ ∈ Ioo (0 : ℝ) 1,
      (H1 ρ hρ).epsilonStar = L43O.epsStar ρ q ζ)
    (H2 : ThickGMCReaders D)
    (H3 : Prop48PrimedBorelLocalFactorInput D hγ q ζ H2)
    (H4 : GMS4O.Prop48GoodEventSecondMomentInputTriple D hγ q ζ H1) :
    ∃ α : ℝ, 0 < α ∧
      ∀ ρ : ℝ, ρ ∈ Ioo (0 : ℝ) 1 →
        ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, 0 ≤ C ∧
          ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 →
            ∀ domain : Set ℂ, ∀ f : ℂ → ℝ,
              GMS4.Prop48TestPairAdmissible ρ domain f →
              P {ω | A * (∫ z in domain, f z) +
                  ε ^ α * GMS4.prop48TestSupNorm ρ f <
                    ∫ z in domain, f z * uStar ε η₀ ω z} ≤
                ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨αreg, hαreg, hregular⟩ := H3.exists_uniform_good_spatial hq hζ
  let α₀ := GMS4.prop48RateAlpha q ζ
  have hα₀ : 0 < α₀ := GMS4.prop48RateAlpha_pos hq.1 hζ.1 hζ.2
  let α : ℝ := min (αreg / 2) (α₀ / 4)
  have hα : 0 < α := lt_min (by positivity) (by positivity)
  have hαreg_le : α ≤ αreg := by dsimp [α]; linarith [min_le_left (αreg / 2) (α₀ / 4)]
  have hαrate : 4 * α ≤ α₀ := by
    dsimp [α]
    linarith [min_le_right (αreg / 2) (α₀ / 4)]
  refine ⟨α, hα, ?_⟩
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
  obtain ⟨K, -, hmean⟩ := Hρ.conditionalMean_le p hp1 hpγ
  obtain ⟨K3, hK3, hmean3⟩ := GMS4O.p48o_condMeanTriple_le D hγ
    (q := q) (ζ := ζ) hρ hζ.1
    (by linarith [hζ.1, hζ.2, hq.1])
  let A : ℝ := K3 + 1
  have hA : 0 < A := by dsimp [A]; linarith
  have hmeanA3 : ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) Hρ.epsilonStar →
      ∀ z ∈ Metric.ball (0 : ℂ) ρ,
        Integrable (maskedUStar D hγ ε q ζ z) P ∧
        ∀ᵐ ω ∂P, GMS4O.p48oCondMeanTriple D hγ ε q ζ ω z ≤ A := by
    intro ε hε z hz
    have hε3 : ε ∈ Ioc (0 : ℝ) (L43O.epsStar ρ q ζ) := by
      rwa [← hH1eps ρ hρ]
    obtain ⟨hi, hb⟩ := hmean3 ε hε3 z hz
    refine ⟨hi, ?_⟩
    filter_upwards [hb] with ω hω
    dsimp [A]
    linarith
  obtain ⟨Cvar, hCvar, εvar, hεvar, hvar⟩ := H4 ρ hρ A hA hmeanA3
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
  let εsmall : ℝ := min Hρ.epsilonStar (min εvar εgeom)
  have hεsmall : 0 < εsmall :=
    lt_min Hρ.epsilonStar_pos (lt_min hεvar hεgeom)
  let Creg' := max 0 Creg
  have hCreg' : 0 ≤ Creg' := le_max_left _ _
  let C : ℝ := Creg' + Cvar + 1 / εsmall ^ α
  have hinv : 0 ≤ 1 / εsmall ^ α :=
    one_div_nonneg.mpr (Real.rpow_pos_of_pos hεsmall α).le
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith
  refine ⟨A, hA, C, hC, ?_⟩
  intro ε hε domain f hadm
  have hεpow : 0 ≤ ε ^ α := (Real.rpow_pos_of_pos hε.1 α).le
  by_cases hsmall : ε ≤ εsmall
  · have hεstar : ε ∈ Ioc (0 : ℝ) Hρ.epsilonStar :=
      ⟨hε.1, hsmall.trans (min_le_left _ _)⟩
    have hεvar' : ε ∈ Ioc (0 : ℝ) (min Hρ.epsilonStar εvar) := by
      refine ⟨hε.1, ?_⟩
      exact le_min (hsmall.trans (min_le_left _ _))
        (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hεgeom' : ε ≤ εgeom :=
      hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hgeom : ε ^ (q - 4 * ζ) + ρ < 1 := by
      have hpow : ε ^ β ≤ εgeom ^ β :=
        Real.rpow_le_rpow hε.1.le hεgeom' hβ.le
      rw [hεgeom_pow] at hpow
      dsimp [β, d] at hpow
      linarith [hρ.2]
    obtain ⟨E, hEm, hEfail, hElocal⟩ := hreg ε hε hgeom
    have hEfail' : P Eᶜ ≤ ENNReal.ofReal (Creg' * ε ^ α) := by
      have hpreg : ε ^ αreg ≤ ε ^ α :=
        Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2.le hαreg_le
      calc
        P Eᶜ ≤ ENNReal.ofReal (Creg * ε ^ αreg) := hEfail
        _ ≤ ENNReal.ofReal (Creg' * ε ^ αreg) :=
          ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hε.1.le _))
        _ ≤ ENNReal.ofReal (Creg' * ε ^ α) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpreg hCreg')
    have hmeanε := hmean ε hεstar
    have hmeanε3 := hmeanA3 ε hεstar
    have hvarE := hvar ε hεvar' E hEm hElocal domain f hadm
    have hvarTail : (∫⁻ ω in E, ENNReal.ofReal
        (GMS4O.p48oPrimedFluctuationTriple D hγ ε q ζ domain f ω ^ 2) ∂P) ≤
        ENNReal.ofReal (((ε ^ α * GMS4.prop48TestSupNorm ρ f) ^ 2) *
          (Cvar * ε ^ α)) := by
      exact hvarE.trans (ENNReal.ofReal_le_ofReal
        (prop48_variance_rate_le_tail hε hα.le hαrate hCvar))
    have hbound := prop48_bad_probability_le_of_spatial_variance_triple
      D hγ hε.1 hCreg' hCvar hmeanε (fun z hz => (hmeanε3 z hz).2)
        hEm hEfail' hElocal hadm hvarTail
    exact hbound.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith [hinv]) hεpow))
  · have hsε : εsmall ≤ ε := (lt_of_not_ge hsmall).le
    have hspow : 0 < εsmall ^ α := Real.rpow_pos_of_pos hεsmall α
    have hpow_le : εsmall ^ α ≤ ε ^ α :=
      Real.rpow_le_rpow hεsmall.le hsε hα.le
    have hlarge : 1 ≤ C * ε ^ α := by
      calc
        1 = (1 / εsmall ^ α) * εsmall ^ α := by field_simp
        _ ≤ (1 / εsmall ^ α) * ε ^ α :=
          mul_le_mul_of_nonneg_left hpow_le (by positivity)
        _ ≤ C * ε ^ α :=
          mul_le_mul_of_nonneg_right (by dsimp [C]; linarith [hCreg', hCvar]) hεpow
    letI : IsProbabilityMeasure P := D.isProbabilityMeasure
    calc
      P {ω | A * (∫ z in domain, f z) +
          ε ^ α * GMS4.prop48TestSupNorm ρ f <
            ∫ z in domain, f z * uStar ε η₀ ω z} ≤ 1 := prob_le_one
      _ = ENNReal.ofReal (1 : ℝ) := by norm_num
      _ ≤ ENNReal.ofReal (C * ε ^ α) := ENNReal.ofReal_le_ofReal hlarge

/-- The canonical 0-cone Proposition 4.8 with the triple-centred good-event
second moment as its sole outstanding source estimate. -/
theorem prop48_canonical_of_tripleH4
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (q ζ : ℝ) (hq : q ∈ Ioo (0 : ℝ) (min (2 / (2 + γ) ^ 2) γ))
    (hζ : ζ ∈ Ioo (0 : ℝ) (q / 100))
    (H4 : GMS4O.Prop48GoodEventSecondMomentInputTriple D hγ q ζ
      (fun ρ hρ => GMS4cS.lemma49ConditionalMoments D hγ hρ hζ.1
        (by linarith [hζ.1, hζ.2]))) :
    ∃ α : ℝ, 0 < α ∧
      ∀ ρ : ℝ, ρ ∈ Ioo (0 : ℝ) 1 →
        ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, 0 ≤ C ∧
          ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 →
            ∀ domain : Set ℂ, ∀ f : ℂ → ℝ,
              GMS4.Prop48TestPairAdmissible ρ domain f →
              P {ω | A * (∫ z in domain, f z) +
                  ε ^ α * GMS4.prop48TestSupNorm ρ f <
                    ∫ z in domain, f z * uStar ε η₀ ω z} ≤
                ENNReal.ofReal (C * ε ^ α) := by
  let H1 : ∀ ρ : ℝ, ρ ∈ Ioo (0 : ℝ) 1 →
      Lemma49ConditionalMoments D hγ q ζ ρ :=
    fun ρ hρ => GMS4cS.lemma49ConditionalMoments D hγ hρ hζ.1
      (by linarith [hζ.1, hζ.2])
  let H2 : ThickGMCReaders D := GMS4cQ.thickGMCReaders D hγ
  let H3 : Prop48PrimedBorelLocalFactorInput D hγ q ζ H2 :=
    prop48_primedBorelLocalFactor_holds D hγ q ζ H2
  have hH1eps : ∀ ρ : ℝ, ∀ hρ : ρ ∈ Ioo (0 : ℝ) 1,
      (H1 ρ hρ).epsilonStar = L43O.epsStar ρ q ζ := by
    intro ρ hρ
    rfl
  exact prop48_canonical_of_tripleH4_aux D hγ q ζ hq hζ H1 hH1eps H2 H3 H4

/-- Proposition 4.8 in the lower-integral carrier, with the
triple-centred good-event second moment as its only hypothesis. -/
theorem prop48ZeroConeLintegral_of_tripleH4
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (q ζ : ℝ) (hq : q ∈ Ioo (0 : ℝ) (min (2 / (2 + γ) ^ 2) γ))
    (hζ : ζ ∈ Ioo (0 : ℝ) (q / 100))
    (H4 : GMS4O.Prop48GoodEventSecondMomentInputTriple D hγ q ζ
      (fun ρ hρ => GMS4cS.lemma49ConditionalMoments D hγ hρ hζ.1
        (by linarith [hζ.1, hζ.2]))) :
    BundleSec4.Prop48ZeroConeLintegral P η₀ := by
  apply BundleSec4.prop48ZeroConeLintegral_of_bochner (uStar (η₀ := η₀))
  · intro ε ω z
    change 0 ≤ MatedCRTHarmonic.GMS4F.realUStar ε (η₀ ω) z
    exact MatedCRTHarmonic.GMS4F.realUStar_nonneg ε (η₀ ω) z
  · exact prop48_canonical_of_tripleH4 D hγ q ζ hq hζ H4
  · let H1 : ∀ ρ : ℝ, ρ ∈ Ioo (0 : ℝ) 1 →
        Lemma49ConditionalMoments D hγ q ζ ρ :=
      fun ρ hρ => GMS4cS.lemma49ConditionalMoments D hγ hρ hζ.1
        (by linarith [hζ.1, hζ.2])
    let H2 : ThickGMCReaders D := GMS4cQ.thickGMCReaders D hγ
    exact exceptional_probability_holds D hγ q ζ hq hζ H1 H2
      (prop48_primedBorelLocalFactor_holds D hγ q ζ H2)

end MatedCRTHarmonic.GMS4.Canonical

