/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4O.Prop48OTripleMean at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OTripleH4
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.Lemma49Canonical
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cS.Lemma49Complete

/-!
# Properties of the conditional mean `m³`

* `measurable_p48oTripleObsVersion`, `measurable_p48oCondMeanTriple`, `p48oCondMeanTriple_nonneg`;
* `p48o_ae_tripleObsVersion_eq`: the triple version is the literal triple a.s. at every centre;
* `p48o_condMeanTriple_ae_eq_condExp`: at every centre with integrable masked density, `m³(·, z)` is a
  version of `E[maskedUStar z | triple z]`;
* **`p48o_condMeanTriple_le`**: the (4.27) bound `m³ ≤ A` a.s., uniformly in `ε ≤ ε_*` and
  `z ∈ B_ρ(0)`, from the locality argument's phase-aware `lemma49_zeroCone_uStar_phase` at `p = 1` (its Lemma 4.3
  locality input is the proved `lemma49_zeroConeRescaledLocality_pair`).
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

lemma measurable_p48oTripleObsVersion
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) :
    Measurable fun p : Ω × ℂ => p48oTripleObsVersion D hγ ε q ζ p.1 p.2 := by
  set r : ℝ := MatedCRTHarmonic.Canon.conditioningRadius ε q ζ
  have hp1 : Measurable fun p : Ω × ℂ =>
      ((p48oZeroConeFieldVersion D hγ p.1, (r, p.2)) : LQGMetric.DistC × ℝ × ℂ) :=
    ((measurable_p48oZeroConeFieldVersion D hγ).comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd)
  have hp2 : Measurable fun p : Ω × ℂ => ((hIG₀ p.1, (r, p.2)) : LQGMetric.DistC × ℝ × ℂ) :=
    (D.igField.1.1.measurable.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd)
  have h1 : Measurable fun p : Ω × ℂ =>
      LQGMetric.circleAvg (p48oZeroConeFieldVersion D hγ p.1) r p.2 := by
    have h := LQGMetric.measurable_circleAvg.comp hp1
    exact h
  have h2 : Measurable fun p : Ω × ℂ => LQGMetric.circleAvg (hIG₀ p.1) r p.2 := by
    have h := LQGMetric.measurable_circleAvg.comp hp2
    exact h
  have h3 : Measurable fun p : Ω × ℂ => phaseVersion D hγ p.1 :=
    (measurable_phaseVersion D hγ).comp measurable_fst
  have h := (h1.prodMk h2).prodMk h3
  exact h

theorem measurable_p48oCondMeanTriple
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) :
    Measurable fun p : Ω × ℂ => p48oCondMeanTriple D hγ ε q ζ p.1 p.2 := by
  let _ := D.isProbabilityMeasure
  exact (measurable_p48oCondValueG P _ _).comp
    (measurable_snd.prodMk (measurable_p48oTripleObsVersion D hγ ε q ζ))

theorem p48oCondMeanTriple_nonneg
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (ω : Ω) (z : ℂ) :
    0 ≤ p48oCondMeanTriple D hγ ε q ζ ω z := by
  let _ := D.isProbabilityMeasure
  exact p48oCondValueG_nonneg P _ _ _

/-- The triple version is the literal triple, simultaneously at every centre, a.s. -/
theorem p48o_ae_tripleObsVersion_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) :
    ∀ᵐ ω ∂P, ∀ z : ℂ, p48oTripleObsVersion D hγ ε q ζ ω z =
      ((LQGMetric.circleAvg (L43O.zeroConeField γ X₀ B₀ B₀' ω)
          (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z,
        LQGMetric.circleAvg (hIG₀ ω) (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z),
        U ω) := by
  filter_upwards [p48o_ae_versions_eq D hγ] with ω hω z
  simp only [p48oTripleObsVersion, hω.1, hω.2]
  rfl

/-- **`m³` is the triple conditional expectation at every centre.** -/
theorem p48o_condMeanTriple_ae_eq_condExp
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) (q ζ : ℝ) (z : ℂ)
    (hint : Integrable (maskedUStar D hγ ε q ζ z) P) :
    (fun ω => p48oCondMeanTriple D hγ ε q ζ ω z) =ᵐ[P]
      P[maskedUStar D hγ ε q ζ z |
        MeasurableSpace.comap (fun ω => p48oTripleObsVersion D hγ ε q ζ ω z) inferInstance] := by
  let _ := D.isProbabilityMeasure
  have hTj := measurable_p48oTripleObsVersion D hγ ε q ζ
  have hXj := measurable_p48oMaskedVersion D hγ hε q ζ
  have hT : Measurable fun ω => p48oTripleObsVersion D hγ ε q ζ ω z := by
    have h := hTj.comp (measurable_id.prodMk (measurable_const (a := z)) :
      Measurable fun ω : Ω => (ω, z))
    exact h
  have hX : Measurable fun ω => p48oMaskedVersion D hγ ε q ζ ω z := by
    have h := hXj.comp (measurable_id.prodMk (measurable_const (a := z)) :
      Measurable fun ω : Ω => (ω, z))
    exact h
  have hXX : (fun ω => p48oMaskedVersion D hγ ε q ζ ω z) =ᵐ[P] maskedUStar D hγ ε q ζ z := by
    filter_upwards [p48o_ae_maskedVersion_eq D hγ ε q ζ] with ω hω
    exact hω z
  exact p48o_condValueG_ae_eq_condExp_of_law P hT hX z
    (p48oPairKernelG_apply P hTj hXj z).symm
    (fun ω => p48oMaskedVersion_nonneg D hγ ε q ζ ω z) hT (ae_eq_refl _) hint hXX

/-- **[18] (4.27) for the mean**: `m³ ≤ A` a.s. at every centre of `B_ρ(0)` and every
`ε ∈ (0, ε_*]`, with the masked density integrable there. -/
theorem p48o_condMeanTriple_le
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ρ q ζ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hζ : 0 < ζ)
    (hζq : 4 * ζ < q) :
    ∃ A : ℝ, 0 < A ∧ ∀ ε ∈ Ioc (0 : ℝ) (L43O.epsStar ρ q ζ), ∀ z ∈ ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧
        ∀ᵐ ω ∂P, p48oCondMeanTriple D hγ ε q ζ ω z ≤ A := by
  let _ := D.isProbabilityMeasure
  have hloc := (GMS4cS.lemma49_zeroConeRescaledLocality_pair D hγ).2
  obtain ⟨-, hbd⟩ := L43O.lemma49_zeroCone_uStar_phase D hγ hloc hρ hζ hζq
  have hγ4 : (1 : ℝ) < 4 / γ ^ 2 := by
    have hγsq : 0 < γ ^ 2 := by have := hγ.1; positivity
    rw [lt_div_iff₀ hγsq]
    nlinarith [hγ.1, hγ.2]
  obtain ⟨C, hC, hCb⟩ := hbd 1 le_rfl hγ4
  refine ⟨C.toReal + 1, by positivity, fun ε hε z hz => ?_⟩
  set r : ℝ := L43O.averageRadius q ζ ε with hr
  set Tl : Ω → ℝ × (ℝ × ℝ) := L43O.circleTriple γ X₀ hIG₀ B₀ B₀' U r z with hTl
  have hset : ∀ A : Set (ℝ × (ℝ × ℝ)), MeasurableSet A →
      ∫⁻ ω in Tl ⁻¹' A, ENNReal.ofReal (maskedUStar D hγ ε q ζ z ω) ∂P ≤ C * P (Tl ⁻¹' A) := by
    intro A hA
    refine (lintegral_mono fun ω => ?_).trans (hCb z hz ε hε A hA)
    have h := L43O.ofReal_densityMomentVariable_le D hγ (ε := ε) (q := q) (ζ := ζ) one_pos z ω
    simp only [densityMomentVariable, Real.rpow_one, ENNReal.rpow_one,
      max_eq_right (maskedUStar_nonneg D hγ ε q ζ z ω)] at h
    rw [ENNReal.rpow_one]
    exact h
  -- integrability of the masked density
  have hmeas : AEMeasurable (maskedUStar D hγ ε q ζ z) P :=
    aemeasurable_maskedUStar D hγ hε.1.le q ζ z
  have hint : Integrable (maskedUStar D hγ ε q ζ z) P := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have h1 := hset univ MeasurableSet.univ
    rw [preimage_univ, Measure.restrict_univ, measure_univ, mul_one] at h1
    refine lt_of_le_of_lt (le_of_eq ?_) (h1.trans_lt hC)
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal (maskedUStar_nonneg D hγ ε q ζ z ω)]
  refine ⟨hint, ?_⟩
  -- the bound for the conditional expectation given the triple version
  set Tv : Ω → (ℝ × ℝ) × ℝ := fun ω => p48oTripleObsVersion D hγ ε q ζ ω z with hTv
  have hTvm : Measurable Tv := by
    have h := (measurable_p48oTripleObsVersion D hγ ε q ζ).comp
      (measurable_id.prodMk (measurable_const (a := z)) : Measurable fun ω : Ω => (ω, z))
    exact h
  have hpre : ∀ B : Set ((ℝ × ℝ) × ℝ), (Tv ⁻¹' B : Set Ω) =ᵐ[P]
      (Tl ⁻¹' {x : ℝ × (ℝ × ℝ) | ((x.1, x.2.1), x.2.2) ∈ B} : Set Ω) := by
    intro B
    filter_upwards [p48o_ae_tripleObsVersion_eq D hγ ε q ζ] with ω hω
    show (ω ∈ Tv ⁻¹' B) = (ω ∈ Tl ⁻¹' {x : ℝ × (ℝ × ℝ) | ((x.1, x.2.1), x.2.2) ∈ B})
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hTv, hω z, hTl]
    rfl
  have hbound : ∀ B : Set ((ℝ × ℝ) × ℝ), MeasurableSet B →
      ∫ ω in Tv ⁻¹' B, maskedUStar D hγ ε q ζ z ω ∂P ≤ C.toReal * (P (Tv ⁻¹' B)).toReal := by
    intro B hB
    set A : Set (ℝ × (ℝ × ℝ)) := {x | ((x.1, x.2.1), x.2.2) ∈ B} with hAdef
    have hAm : MeasurableSet A :=
      ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)) hB
    rw [setIntegral_congr_set (hpre B), measure_congr (hpre B)]
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun ω => maskedUStar_nonneg D hγ ε q ζ z ω) hmeas.aestronglyMeasurable.restrict]
    have hfin : C * P (Tl ⁻¹' A) ≠ ⊤ := ENNReal.mul_ne_top hC.ne (measure_ne_top _ _)
    calc (∫⁻ ω in Tl ⁻¹' A, ENNReal.ofReal (maskedUStar D hγ ε q ζ z ω) ∂P).toReal
        ≤ (C * P (Tl ⁻¹' A)).toReal := ENNReal.toReal_mono hfin (hset A hAm)
      _ = C.toReal * (P (Tl ⁻¹' A)).toReal := ENNReal.toReal_mul
  have hce := L43O.condExp_le_of_setIntegral_le hTvm hint hbound
  filter_upwards [hce, p48o_condMeanTriple_ae_eq_condExp D hγ hε.1.le q ζ z hint] with ω h1 h2
  rw [h2]
  linarith

end MatedCRTHarmonic.GMS4O
