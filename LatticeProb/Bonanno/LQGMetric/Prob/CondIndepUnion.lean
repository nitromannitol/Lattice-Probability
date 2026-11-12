/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Prob.CondIndepUnion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Prob.CondIndepEv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Independence of a σ-algebra from a join (SS13 Lemma 3.5 and its conditional form)

* `LQGMetric.indep_sup_of_condIndepEv` (**SS.L3.5**): if `𝒜 ⟂ ℬ`, `𝒜 ⟂ 𝒞` and `ℬ ⟂ 𝒞 | 𝒜`,
  then `𝒜 ⟂ ℬ ∨ 𝒞`. Source: Schramm–Sheffield, *A contour line of the continuum Gaussian free
  field*, arXiv:1008.2447 (PTRF 157, 2013), Lemma 3.5 (`l.independentpair`,
  `GFFcontours.tex` lines 1885–1910). Used by Gwynne–Miller, *Local metrics of the Gaussian free
  field*, arXiv:1905.00379, `local-metrics-final.tex` line 259 (proof of Lemma 1.4).
* `LQGMetric.condIndepEv_sup_of_condIndepEv` (**LM.S1.4a**): the same under conditioning on `𝒢`:
  `𝒜 ⟂ ℬ | 𝒢`, `𝒜 ⟂ 𝒞 | 𝒢`, `ℬ ⟂ 𝒞 | 𝒜 ∨ 𝒢` give `𝒜 ⟂ ℬ ∨ 𝒞 | 𝒢`
  (LM tex lines 268–273: "applied under the conditional law given h|_V").
* mathlib-`CondIndep` forms `LQGMetric.indep_sup_of_condIndep`,
  `LQGMetric.condIndep_sup_of_condIndep` (standard Borel sample space).

Proof: SS's computation `P[A ∩ B ∩ C] = E[P[B | 𝒜] P[C | 𝒜] 1_A] = P[A] P[B] P[C]`, done with
`E[· | 𝒢]` in place of `E` (as LM indicates), and extended from the π-system
`{b ∩ c ∩ g}` to `ℬ ∨ 𝒞 ∨ 𝒢` (SS leave this π–λ step implicit). We prove the Markov form
`P[a | ℬ ∨ 𝒞 ∨ 𝒢] = P[a | 𝒢]` and conclude with `LQGMetric.condIndepEv_of_condExp_sup_eq`.
-/

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter

namespace LQGMetric

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The π-system `{b ∩ c ∩ g}` generating `ℬ ∨ 𝒞 ∨ 𝒢`. -/
def triInterPi (B C G : MeasurableSpace Ω) : Set (Set Ω) :=
  {s | ∃ b c g, MeasurableSet[B] b ∧ MeasurableSet[C] c ∧ MeasurableSet[G] g ∧ s = b ∩ c ∩ g}

lemma isPiSystem_triInterPi (B C G : MeasurableSpace Ω) : IsPiSystem (triInterPi B C G) := by
  rintro _ ⟨b, c, g, hb, hc, hg, rfl⟩ _ ⟨b', c', g', hb', hc', hg', rfl⟩ -
  exact ⟨b ∩ b', c ∩ c', g ∩ g', hb.inter hb', hc.inter hc', hg.inter hg', by ext; simp; tauto⟩

lemma sup_sup_eq_generateFrom_triInterPi (B C G : MeasurableSpace Ω) :
    B ⊔ C ⊔ G = generateFrom (triInterPi B C G) := by
  apply le_antisymm
  · refine sup_le (sup_le (fun b hb => ?_) (fun c hc => ?_)) (fun g hg => ?_)
    · exact measurableSet_generateFrom ⟨b, univ, univ, hb, .univ, .univ, by simp⟩
    · exact measurableSet_generateFrom ⟨univ, c, univ, .univ, hc, .univ, by simp⟩
    · exact measurableSet_generateFrom ⟨univ, univ, g, .univ, .univ, hg, by simp⟩
  · refine generateFrom_le ?_
    rintro _ ⟨b, c, g, hb, hc, hg, rfl⟩
    have hb' : MeasurableSet[B ⊔ C ⊔ G] b := (le_sup_left.trans le_sup_left : B ≤ B ⊔ C ⊔ G) b hb
    have hc' : MeasurableSet[B ⊔ C ⊔ G] c := (le_sup_right.trans le_sup_left : C ≤ B ⊔ C ⊔ G) c hc
    have hg' : MeasurableSet[B ⊔ C ⊔ G] g := (le_sup_right : G ≤ B ⊔ C ⊔ G) g hg
    exact (hb'.inter hc').inter hg'

/-- **LM.S1.4a** (conditional form of SS13 Lemma 3.5). If `𝒜 ⟂ ℬ | 𝒢`, `𝒜 ⟂ 𝒞 | 𝒢` and
`ℬ ⟂ 𝒞 | 𝒜 ∨ 𝒢`, then `𝒜 ⟂ ℬ ∨ 𝒞 | 𝒢`. -/
theorem condIndepEv_sup_of_condIndepEv [IsProbabilityMeasure μ]
    {G A B C : MeasurableSpace Ω} (hG : G ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ) (hC : C ≤ mΩ)
    (hAB : CondIndepEv G A B μ) (hAC : CondIndepEv G A C μ) (hBC : CondIndepEv (A ⊔ G) B C μ) :
    CondIndepEv G A (B ⊔ C) μ := by
  have hK : A ⊔ G ≤ mΩ := sup_le hA hG
  have hsup : B ⊔ C ⊔ G ≤ mΩ := sup_le (sup_le hB hC) hG
  refine condIndepEv_of_condExp_sup_eq hG hA (sup_le hB hC) fun a ha => ?_
  have ha0 := hA a ha
  refine (ae_eq_condExp_of_isPiSystem hsup (sup_sup_eq_generateFrom_triInterPi B C G)
    (isPiSystem_triInterPi B C G) (integrable_indOne ha0) integrable_condExp
    (stronglyMeasurable_condExp.mono le_sup_right) (integral_condExp hG) ?_).symm
  rintro _ ⟨b, c, g, hb, hc, hg, rfl⟩
  have hb0 := hB b hb
  have hc0 := hC c hc
  have hg0 := hG g hg
  have hb' := condExp_sup_eq_of_condIndepEv hG hA hB hAB hb
  have hc' := condExp_sup_eq_of_condIndepEv hG hA hC hAC hc
  set Z : Ω → ℝ := μ⟦b | G⟧ * μ⟦c | G⟧ with hZ
  have hZm : StronglyMeasurable[G] Z := stronglyMeasurable_condExp.mul stronglyMeasurable_condExp
  have hZi : Integrable Z μ :=
    (integrable_condExp (m := G) (μ := μ) (f := c.indicator fun _ => (1 : ℝ))).bdd_mul
      (c := 1) integrable_condExp.1 (norm_condExp_indOne_le hG hb0)
  have hbc : μ⟦b ∩ c | A ⊔ G⟧ =ᵐ[μ] Z := (hBC b c hb hc).trans (hb'.mul hc')
  have hbcG : μ⟦b ∩ c | G⟧ =ᵐ[μ] Z := by
    have h1 := (condExp_condExp_of_le (f := (b ∩ c).indicator fun _ => (1 : ℝ)) (μ := μ)
      (le_sup_right : G ≤ A ⊔ G) hK).symm.trans (condExp_congr_ae hbc)
    rwa [condExp_of_stronglyMeasurable hG hZm hZi] at h1
  have hga : MeasurableSet[A ⊔ G] (g ∩ a) :=
    ((le_sup_right : G ≤ A ⊔ G) g hg).inter ((le_sup_left : A ≤ A ⊔ G) a ha)
  have hset : b ∩ c ∩ g ∩ a = g ∩ a ∩ (b ∩ c) := by ext; simp; tauto
  calc ∫ x in b ∩ c ∩ g, (μ⟦a | G⟧) x ∂μ
      = ∫ x in g ∩ (b ∩ c), (μ⟦a | G⟧) x ∂μ := by rw [inter_comm (b ∩ c) g]
    _ = ∫ x in g, (μ⟦b ∩ c | G⟧) x * (μ⟦a | G⟧) x ∂μ :=
        setIntegral_inter_eq_condExp_mul hG (hb0.inter hc0) hg stronglyMeasurable_condExp
          integrable_condExp
    _ = ∫ x in g, (μ⟦a | G⟧) x * Z x ∂μ :=
        setIntegral_congr_ae hg0 (hbcG.mono fun x hx _ => by rw [hx, mul_comm])
    _ = ∫ x in g ∩ a, Z x ∂μ := (setIntegral_inter_eq_condExp_mul hG ha0 hg hZm hZi).symm
    _ = ∫ x in g ∩ a, (μ⟦b ∩ c | A ⊔ G⟧) x * (fun _ => (1 : ℝ)) x ∂μ :=
        setIntegral_congr_ae (hK _ hga) (hbc.mono fun x hx _ => by simp [hx])
    _ = ∫ x in g ∩ a ∩ (b ∩ c), (fun _ => (1 : ℝ)) x ∂μ :=
        (setIntegral_inter_eq_condExp_mul hK (hb0.inter hc0) hga stronglyMeasurable_const
          (integrable_const 1)).symm
    _ = ∫ x in b ∩ c ∩ g, a.indicator (fun _ => (1 : ℝ)) x ∂μ := by
        rw [setIntegral_indicator ha0, hset]

end LQGMetric
