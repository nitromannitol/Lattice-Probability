/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.G3SchemeCI at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.G3Core
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# G3 scheme: conditional independence from a Markov decomposition

The step "the conditional laws of the restrictions of `h` to the two halves are independent by the
standard GFF Markov property" (Sheffield, arXiv:1012.4797, proof of Theorem 1.8, §5.4, p. 71) in
abstract form. The GFF domain Markov property (Sheffield, *Gaussian free fields for
mathematicians*, §2.6; project: `K3.freeGFF_halfDisc_markov`) produces σ-algebras `𝒜` (the
local field in the first region), `ℬ` (the local field in the second region) and `𝒪` (the field
outside both regions) with `𝒜` independent of `ℬ ⊔ 𝒪`. Then anything built from the first region
and the outside is conditionally independent, given `𝒪`, of anything built from the second region
and the outside (`condIndepCE_of_indep_sup`).

This is the standard fact that independence of `𝒜` from `ℬ ⊔ 𝒪` gives
`P[F | 𝒜 ⊔ 𝒪] = P[F | 𝒪]` for `F ∈ ℬ ⊔ 𝒪` (Kallenberg, *Foundations of Modern Probability*,
2nd ed., Proposition 6.6 and Corollary 6.7), followed by the tower and pull-out properties. The
Lean proof is an own elementary proof along these lines (π-λ on `{a ∩ o}`), stated in the event
form `CondIndepCE` of `G3Core.lean`, since mathlib's `CondIndep` needs standard Borel spaces.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set MeasurableSpace
open scoped ENNReal

namespace QuantumZipper
namespace Thm18Asm

variable {Ω α β : Type*} {m₀ : MeasurableSpace Ω} [MeasurableSpace α] [MeasurableSpace β]
  {𝒜 ℬ 𝒪 : MeasurableSpace Ω} {P : Measure[m₀] Ω}

/-- The π-system `{a ∩ o : a ∈ 𝒜, o ∈ 𝒪}` generating `𝒜 ⊔ 𝒪`. -/
def interPi (𝒜 𝒪 : MeasurableSpace Ω) : Set (Set Ω) :=
  {s | ∃ a o, MeasurableSet[𝒜] a ∧ MeasurableSet[𝒪] o ∧ s = a ∩ o}

theorem isPiSystem_interPi : IsPiSystem (interPi 𝒜 𝒪) := by
  rintro _ ⟨a, o, ha, ho, rfl⟩ _ ⟨a', o', ha', ho', rfl⟩ -
  exact ⟨a ∩ a', o ∩ o', ha.inter ha', ho.inter ho', by ext; simp; tauto⟩

theorem sup_eq_generateFrom_interPi : 𝒜 ⊔ 𝒪 = generateFrom (interPi 𝒜 𝒪) := by
  apply le_antisymm
  · refine sup_le (fun a ha => ?_) (fun o ho => ?_)
    · exact measurableSet_generateFrom ⟨a, univ, ha, MeasurableSet.univ, (inter_univ a).symm⟩
    · exact measurableSet_generateFrom ⟨univ, o, MeasurableSet.univ, ho, (univ_inter o).symm⟩
  · refine generateFrom_le ?_
    rintro _ ⟨a, o, ha, ho, rfl⟩
    exact (le_sup_left (a := 𝒜) (b := 𝒪) a ha).inter (le_sup_right (a := 𝒜) (b := 𝒪) o ho)

/-- **Markov identity.** If `𝒜` is independent of `ℬ ⊔ 𝒪`, then for `F ∈ ℬ ⊔ 𝒪`,
`P[1_F | 𝒜 ⊔ 𝒪] = P[1_F | 𝒪]` a.e. -/
theorem condExp_indicator_sup_eq [IsProbabilityMeasure P] (h𝒜 : 𝒜 ≤ m₀) (hℬ : ℬ ≤ m₀)
    (h𝒪 : 𝒪 ≤ m₀) (hind : Indep 𝒜 (ℬ ⊔ 𝒪) P) {F : Set Ω} (hF : MeasurableSet[ℬ ⊔ 𝒪] F) :
    P[F.indicator (fun _ => (1 : ℝ)) | 𝒜 ⊔ 𝒪] =ᵐ[P] P[F.indicator (fun _ => (1 : ℝ)) | 𝒪] := by
  have hsup : 𝒜 ⊔ 𝒪 ≤ m₀ := sup_le h𝒜 h𝒪
  have hF0 : MeasurableSet[m₀] F := sup_le hℬ h𝒪 F hF
  set f : Ω → ℝ := F.indicator (fun _ => (1 : ℝ)) with hf
  have hfi : Integrable f P := (integrable_const (1 : ℝ)).indicator hF0
  set g : Ω → ℝ := P[f | 𝒪] with hg
  have hgi : Integrable g P := integrable_condExp
  refine (ae_eq_condExp_of_forall_setIntegral_eq hsup hfi (fun s _ _ => hgi.integrableOn)
    ?_ (((stronglyMeasurable_condExp (m := 𝒪) (f := f) (μ := P)).mono
      (le_sup_right : 𝒪 ≤ 𝒜 ⊔ 𝒪)).aestronglyMeasurable)).symm
  intro S hS _
  -- π-λ induction on `S ∈ 𝒜 ⊔ 𝒪`
  refine induction_on_inter (C := fun S _ => ∫ x in S, g x ∂P = ∫ x in S, f x ∂P)
    sup_eq_generateFrom_interPi isPiSystem_interPi (by simp) ?_ ?_ ?_ S hS
  · rintro _ ⟨a, o, ha, ho, rfl⟩
    have ha0 : MeasurableSet[m₀] a := h𝒜 a ha
    have ho0 : MeasurableSet[m₀] o := h𝒪 o ho
    -- left side: `∫_{a ∩ o} g = P(a) ∫_o g`
    have hL : ∫ x in a ∩ o, g x ∂P = P.real a * ∫ x in o, g x ∂P := by
      have hI : IndepFun (a.indicator (fun _ => (1 : ℝ))) (o.indicator g) P := by
        rw [IndepFun_iff_Indep]
        refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hind ?_) ?_
        · exact measurable_iff_comap_le.1
            ((measurable_const.indicator ha))
        · refine measurable_iff_comap_le.1 ?_
          exact ((stronglyMeasurable_condExp.measurable).indicator ho).mono le_sup_right le_rfl
      have hmul := hI.integral_mul_eq_mul_integral
        ((measurable_const.indicator ha0).aestronglyMeasurable)
        ((hgi.indicator ho0).aestronglyMeasurable)
      have e1 : (fun x => a.indicator (fun _ => (1 : ℝ)) x * o.indicator g x) =
          (a ∩ o).indicator g := by
        funext x; by_cases hxa : x ∈ a <;> by_cases hxo : x ∈ o <;> simp [hxa, hxo]
      rw [← integral_indicator (ha0.inter ho0), ← e1, ← Pi.mul_def, hmul,
        integral_indicator ha0, integral_indicator ho0, setIntegral_const, smul_eq_mul, mul_one]
    -- right side: `∫_{a ∩ o} f = P(a ∩ (o ∩ F)) = P(a) P(o ∩ F)`
    have hR : ∫ x in a ∩ o, f x ∂P = P.real a * P.real (o ∩ F) := by
      rw [hf, integral_indicator hF0, Measure.restrict_restrict hF0, setIntegral_const,
        smul_eq_mul, mul_one]
      have hoF : MeasurableSet[ℬ ⊔ 𝒪] (o ∩ F) := (le_sup_right (a := ℬ) (b := 𝒪) o ho).inter hF
      have := (Indep_iff _ _ _).1 hind a (o ∩ F) ha hoF
      rw [show F ∩ (a ∩ o) = a ∩ (o ∩ F) by ext; simp; tauto]
      simp only [Measure.real, this, ENNReal.toReal_mul]
    have hO : ∫ x in o, g x ∂P = P.real (o ∩ F) := by
      rw [hg, setIntegral_condExp h𝒪 hfi ho, hf, integral_indicator hF0,
        Measure.restrict_restrict hF0, setIntegral_const, smul_eq_mul, mul_one, inter_comm]
    rw [hL, hR, hO]
  · intro t htm ht
    have ht0 : MeasurableSet[m₀] t := hsup t htm
    have e1 := integral_add_compl ht0 hgi
    have e2 := integral_add_compl ht0 hfi
    have e3 : ∫ x, g x ∂P = ∫ x, f x ∂P := integral_condExp h𝒪
    linarith
  · intro s hd hsm hs
    have hs0 : ∀ i, MeasurableSet[m₀] (s i) := fun i => hsup _ (hsm i)
    rw [integral_iUnion hs0 hd hgi.integrableOn, integral_iUnion hs0 hd hfi.integrableOn]
    exact tsum_congr hs

/-- **Conditional independence from the Markov identity.** If `P[1_F | 𝒜 ⊔ 𝒪] = P[1_F | 𝒪]`
for every `F ∈ ℬ ⊔ 𝒪`, then an `𝒜 ⊔ 𝒪`-measurable `U` and a `ℬ ⊔ 𝒪`-measurable `V` are
conditionally independent given `𝒪` (event form). This form survives reweighting `P` by an
`𝒜 ⊔ 𝒪`-measurable density (Palm weighting), unlike plain independence. -/
theorem condIndepCE_of_condExp_sup_eq [IsProbabilityMeasure P] (h𝒜 : 𝒜 ≤ m₀) (hℬ : ℬ ≤ m₀)
    (h𝒪 : 𝒪 ≤ m₀)
    (hmk : ∀ F, MeasurableSet[ℬ ⊔ 𝒪] F →
      P[F.indicator (fun _ => (1 : ℝ)) | 𝒜 ⊔ 𝒪] =ᵐ[P] P[F.indicator (fun _ => (1 : ℝ)) | 𝒪])
    {U : Ω → α} {V : Ω → β}
    (hU : Measurable[𝒜 ⊔ 𝒪] U) (hV : Measurable[ℬ ⊔ 𝒪] V) : CondIndepCE 𝒪 U V P := by
  intro s t hs ht
  have hsup : 𝒜 ⊔ 𝒪 ≤ m₀ := sup_le h𝒜 h𝒪
  have hE : MeasurableSet[𝒜 ⊔ 𝒪] (U ⁻¹' s) := hU hs
  have hF : MeasurableSet[ℬ ⊔ 𝒪] (V ⁻¹' t) := hV ht
  have hE0 : MeasurableSet[m₀] (U ⁻¹' s) := hsup _ hE
  have hF0 : MeasurableSet[m₀] (V ⁻¹' t) := sup_le hℬ h𝒪 _ hF
  set e : Ω → ℝ := (U ⁻¹' s).indicator (fun _ => (1 : ℝ)) with he
  set f : Ω → ℝ := (V ⁻¹' t).indicator (fun _ => (1 : ℝ)) with hf
  have hei : Integrable e P := (integrable_const (1 : ℝ)).indicator hE0
  have hfi : Integrable f P := (integrable_const (1 : ℝ)).indicator hF0
  have hef : (U ⁻¹' s ∩ V ⁻¹' t).indicator (fun _ => (1 : ℝ)) = e * f := by
    funext x; by_cases h1 : x ∈ U ⁻¹' s <;> by_cases h2 : x ∈ V ⁻¹' t <;> simp [he, hf, h1, h2]
  have hefi : Integrable (e * f) P := by
    rw [← hef]; exact (integrable_const _).indicator (hE0.inter hF0)
  have hem : StronglyMeasurable[𝒜 ⊔ 𝒪] e :=
    (measurable_const.indicator hE).stronglyMeasurable
  -- `P[e f | 𝒜 ⊔ 𝒪] = e P[f | 𝒜 ⊔ 𝒪] = e P[f | 𝒪]`
  have h1 : P[e * f | 𝒜 ⊔ 𝒪] =ᵐ[P] e * P[f | 𝒪] := by
    filter_upwards [condExp_mul_of_stronglyMeasurable_left hem hefi hfi,
      hmk _ hF] with x hx hx'
    rw [hx, Pi.mul_apply, Pi.mul_apply, hx']
  have hgi : Integrable (P[f | 𝒪] * e) P := by
    have : P[f | 𝒪] * e = (U ⁻¹' s).indicator (P[f | 𝒪]) := by
      funext x; by_cases h1 : x ∈ U ⁻¹' s <;> simp [he, h1]
    rw [this]; exact integrable_condExp.indicator hE0
  have h2 : P[P[f | 𝒪] * e | 𝒪] =ᵐ[P] P[f | 𝒪] * P[e | 𝒪] :=
    condExp_mul_of_stronglyMeasurable_left stronglyMeasurable_condExp hgi hei
  have h3 : P[P[e * f | 𝒜 ⊔ 𝒪] | 𝒪] =ᵐ[P] P[e * f | 𝒪] :=
    condExp_condExp_of_le le_sup_right hsup
  have h4 : P[P[e * f | 𝒜 ⊔ 𝒪] | 𝒪] =ᵐ[P] P[P[f | 𝒪] * e | 𝒪] := by
    refine condExp_congr_ae ?_
    filter_upwards [h1] with x hx
    rw [hx, Pi.mul_apply, Pi.mul_apply, mul_comm]
  rw [hef]
  filter_upwards [h2, h3, h4] with x hx2 hx3 hx4
  rw [← hx3, hx4, hx2, Pi.mul_apply, Pi.mul_apply, mul_comm]

/-! ## Stability under Palm reweighting -/

/-- **The Markov identity survives reweighting by a density measurable w.r.t. `𝒜 ⊔ 𝒪`.** If
`P[1_F | 𝒜 ⊔ 𝒪] = P[1_F | 𝒪]` for all `F ∈ ℬ ⊔ 𝒪`, and `P̃ = w · P` is a probability measure with
`w` measurable w.r.t. `𝒜 ⊔ 𝒪` (in G3: the Palm weight `ν_h[−δ, 0]` is a function of the field
near `[−δ, 0]`), then the same identity holds under `P̃` (both sides equal `P[1_F | 𝒪]`).
Own elementary proof (Bayes formula for conditional expectations). -/
theorem condExp_sup_eq_withDensity [IsProbabilityMeasure P] (h𝒜 : 𝒜 ≤ m₀) (hℬ : ℬ ≤ m₀)
    (h𝒪 : 𝒪 ≤ m₀)
    (hmk : ∀ F, MeasurableSet[ℬ ⊔ 𝒪] F →
      P[F.indicator (fun _ => (1 : ℝ)) | 𝒜 ⊔ 𝒪] =ᵐ[P] P[F.indicator (fun _ => (1 : ℝ)) | 𝒪])
    {w : Ω → NNReal} (hw : Measurable[𝒜 ⊔ 𝒪] w) (hwi : Integrable (fun x => (w x : ℝ)) P)
    [IsProbabilityMeasure (P.withDensity fun x => (w x : ℝ≥0∞))]
    {F : Set Ω} (hF : MeasurableSet[ℬ ⊔ 𝒪] F) :
    (P.withDensity fun x => (w x : ℝ≥0∞))[F.indicator (fun _ => (1 : ℝ)) | 𝒜 ⊔ 𝒪] =ᵐ[P.withDensity
      fun x => (w x : ℝ≥0∞)]
      (P.withDensity fun x => (w x : ℝ≥0∞))[F.indicator (fun _ => (1 : ℝ)) | 𝒪] := by
  set Q := P.withDensity fun x => (w x : ℝ≥0∞) with hQ
  have hsup : 𝒜 ⊔ 𝒪 ≤ m₀ := sup_le h𝒜 h𝒪
  have hw0 : Measurable[m₀] w := hw.mono hsup le_rfl
  have hF0 : MeasurableSet[m₀] F := sup_le hℬ h𝒪 F hF
  set f : Ω → ℝ := F.indicator (fun _ => (1 : ℝ)) with hf
  have hfi : Integrable f P := (integrable_const (1 : ℝ)).indicator hF0
  have hfiQ : Integrable f Q := (integrable_const (1 : ℝ)).indicator hF0
  set g : Ω → ℝ := P[f | 𝒪] with hg
  have hQP : Q ≪ P := withDensity_absolutelyContinuous _ _
  have hg01 := condExp_indicator_one_mem_Icc (P := P) h𝒪 hF0
  have hgsm : StronglyMeasurable[𝒪] g := stronglyMeasurable_condExp
  have hgQ : Integrable g Q := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (hgsm.mono h𝒪).aestronglyMeasurable ?_
    filter_upwards [hQP.ae_le hg01] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]; exact hx.2
  have hwf : Integrable (fun x => (w x : ℝ) * f x) P := by
    refine Integrable.mono' hwi (hwi.aestronglyMeasurable.mul hfi.aestronglyMeasurable) ?_
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ F <;> simp [hf, hx]
  have hwg : Integrable (fun x => (w x : ℝ) * g x) P := by
    refine Integrable.mono' hwi (hwi.aestronglyMeasurable.mul
      (hgsm.mono h𝒪).aestronglyMeasurable) ?_
    filter_upwards [hg01] with x hx
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx.1, abs_of_nonneg
      (NNReal.coe_nonneg _)]
    exact mul_le_of_le_one_right (NNReal.coe_nonneg _) hx.2
  have hwsm : StronglyMeasurable[𝒜 ⊔ 𝒪] (fun x => (w x : ℝ)) :=
    (measurable_coe_nnreal_real.comp hw).stronglyMeasurable
  -- the key computation, for `S ∈ 𝒜 ⊔ 𝒪`
  have key : ∀ S, MeasurableSet[𝒜 ⊔ 𝒪] S → ∫ x in S, g x ∂Q = ∫ x in S, f x ∂Q := by
    intro S hS
    have hS0 : MeasurableSet[m₀] S := hsup S hS
    letI : MeasurableSpace Ω := m₀
    rw [hQ, setIntegral_withDensity_eq_setIntegral_smul hw0 _ hS0,
      setIntegral_withDensity_eq_setIntegral_smul hw0 _ hS0]
    simp only [NNReal.smul_def, smul_eq_mul]
    rw [← setIntegral_condExp hsup hwf hS]
    refine setIntegral_congr_ae hS0 ?_
    filter_upwards [condExp_mul_of_stronglyMeasurable_left hwsm hwf hfi, hmk F hF] with x hx hx' _
    rw [show (fun x => (w x : ℝ) * f x) = (fun x => (w x : ℝ)) * f from rfl, hx, Pi.mul_apply,
      hx']
  have e1 : g =ᵐ[Q] Q[f | 𝒜 ⊔ 𝒪] :=
    ae_eq_condExp_of_forall_setIntegral_eq hsup hfiQ (fun _ _ _ => hgQ.integrableOn)
      (fun S hS _ => key S hS) ((hgsm.mono (le_sup_right : 𝒪 ≤ 𝒜 ⊔ 𝒪)).aestronglyMeasurable)
  have e2 : g =ᵐ[Q] Q[f | 𝒪] :=
    ae_eq_condExp_of_forall_setIntegral_eq h𝒪 hfiQ (fun _ _ _ => hgQ.integrableOn)
      (fun S hS _ => key S (le_sup_right (a := 𝒜) (b := 𝒪) S hS)) hgsm.aestronglyMeasurable
  filter_upwards [e1, e2] with x h1 h2
  rw [← h1, ← h2]

/-! ## Adjoining an independent coordinate to the conditioning -/

/-- **Adjoining an independent coordinate.** If `𝒜 ⊥ 𝒞` under `P₀`, then on `Ω₀ × E` with the
product law `P₀ ⊗ λ`, the pull-back of `𝒜` is independent of the pull-back of `𝒞` together with
the second coordinate. (In G3 the second coordinate is the Palm length `ℓ = ν_h[x, 0]`, which is
put into the conditioning σ-algebra.) Own elementary proof (π-systems). -/
theorem indep_comap_fst_sup_snd {Ω₀ E : Type*} {𝒜 𝒞 : MeasurableSpace Ω₀}
    {m : MeasurableSpace Ω₀} [mE : MeasurableSpace E] (h𝒜 : 𝒜 ≤ m) (h𝒞 : 𝒞 ≤ m) {P₀ : Measure[m] Ω₀}
    [IsProbabilityMeasure P₀] {L₀ : Measure E} [IsProbabilityMeasure L₀]
    (hind : Indep 𝒜 𝒞 P₀) :
    Indep (𝒜.comap Prod.fst) (𝒞.comap Prod.fst ⊔ mE.comap Prod.snd) (P₀.prod L₀) := by
  refine IndepSets.indep (p1 := {s | MeasurableSet[𝒜.comap Prod.fst] s})
    (p2 := interPi (𝒞.comap Prod.fst) (mE.comap Prod.snd)) ?_ ?_
    (@isPiSystem_measurableSet _ (𝒜.comap Prod.fst)) isPiSystem_interPi
    (@generateFrom_measurableSet _ (𝒜.comap Prod.fst)).symm sup_eq_generateFrom_interPi ?_
  · exact (comap_mono h𝒜).trans le_sup_left
  · exact sup_le ((comap_mono h𝒞).trans le_sup_left) le_sup_right
  rw [IndepSets_iff]
  rintro _ _ ⟨a, ha, rfl⟩ ⟨_, _, ⟨c, hc, rfl⟩, ⟨e, he, rfl⟩, rfl⟩
  have e1 : Prod.fst ⁻¹' a = a ×ˢ (univ : Set E) := by ext; simp
  have e2 : Prod.fst ⁻¹' c ∩ Prod.snd ⁻¹' e = c ×ˢ e := by ext; simp
  have e3 : a ×ˢ (univ : Set E) ∩ c ×ˢ e = (a ∩ c) ×ˢ e := by ext; simp; tauto
  rw [e1, e2, e3, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
    (Indep_iff _ _ _).1 hind a c ha hc, measure_univ, mul_one]
  ring

end Thm18Asm
end QuantumZipper
