/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108Q3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108Q2
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108L1
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatLaw
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# CONF Lemma 2.10: transfer of the coarse/fine splitting to an arbitrary realisation

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF), proof of Lemma 2.10
(C:719–742). CONF builds the splitting `h = h_{0,t} + h_{t,∞}` on the white-noise space
(C:722–731), i.e. for one particular realisation of the zero-boundary GFF. `CONFLem2_10` is
stated for every realisation `X` on every `Ω`, and its hypotheses (`IsFKGFunZB`) are sample-level
a.s. statements that do not pass to the law of `X`. We therefore couple: on `Ω × Ω₀` with the
measure `P ⊗ κ(X ·)`, `κ` the conditional law of the model sample `ω₀` given `X₀ ω₀`
(mathlib's `Measure.condKernel`, `Ω₀` standard Borel), the pair `(X ∘ fst, snd)` has the law of
`(X₀, id)`; so `X ∘ fst = X₀ ∘ snd` a.s., the model splitting pulls back along `snd`, and the
`IsFKGFunZB` hypotheses pull back along `fst`. Own measure-theoretic argument (a standard
coupling), needed only because of the realisation-free form of `CONFLem2_10`.

* `law_eq_of_isZBExtField`: `IsZBExtField U` pins the law of `X` on `𝒟'(ℂ)` (the argument of
  `KilledHeat.map_eq_of_gaussian`, without countability of the index: `X` is measurable);
* **`cov_nonneg_of_model`**: the transfer;
* `CONFZBCoarseModel U`: a standard Borel model of `IsZBExtField U` with the splitting along a
  filtration (CONF C:722–738); **`confLem2_10_of_model`**: `CONFLem2_10` from it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace LQGMetric.CONF

/-- the law of a field with `IsZBExtField U` is determined -/
theorem law_eq_of_isZBExtField {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {U : TopologicalSpace.Opens ℂ} {X : Ω → DistC} {Y : Ω' → DistC}
    (hX : IsZBExtField U X P) (hY : IsZBExtField U Y P') : P.map X = P'.map Y := by
  apply measure_distC_ext
  have hev : Measurable fun (g : DistC) (j : TestC) => g j := fun _ hs => ⟨_, hs, rfl⟩
  rw [Measure.map_map hev hX.measurable, Measure.map_map hev hY.measurable]
  have h1 := isProjectiveLimit_map (X := fun (j : TestC) ω => X ω j) (P := P)
    (hev.comp hX.measurable).aemeasurable
  have h2 := isProjectiveLimit_map (X := fun (j : TestC) ω => Y ω j) (P := P')
    (hev.comp hY.measurable).aemeasurable
  simp_rw [KilledHeat.map_restrict_eq_of_gaussian hX.gaussian hY.gaussian
    (fun t => by rw [hX.centered, hY.centered])
    (fun s t => by rw [hX.covariance_eq, hY.covariance_eq])] at h1
  exact h1.unique h2

section Transfer

variable {Ω₀ : Type} [m₀ : MeasurableSpace Ω₀] [StandardBorelSpace Ω₀] {P₀ : Measure Ω₀}
  [IsProbabilityMeasure P₀]

/-- **Transfer of the splitting** (coupling through the conditional law of the model). -/
theorem cov_nonneg_of_model (ℱ : Filtration ℕ m₀) {X₀ X₀' : Ω₀ → DistC} (hX₀ : Measurable X₀)
    (hX₀' : Measurable[⨆ n, ℱ n] X₀') (hXX₀ : X₀ =ᵐ[P₀] X₀')
    (hsplit : ∀ n, ∃ S : Ω₀ → C(ℂ, ℝ), ∃ R : Ω₀ → DistC, IsCoarseSplit P₀ (ℱ n) X₀ S R)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → DistC}
    (hXm : Measurable X) (hlaw : P.map X = P₀.map X₀) {Φ Ψ : DistC → ℝ}
    (hΦ : IsFKGFunZB P X Φ) (hΨ : IsFKGFunZB P X Ψ) :
    0 ≤ cov[fun ω => Φ (X ω), fun ω => Ψ (X ω); P] := by
  haveI : Nonempty Ω₀ := by
    rcases isEmpty_or_nonempty Ω₀ with h | h
    · exact absurd (Measure.eq_zero_of_isEmpty P₀) (IsProbabilityMeasure.ne_zero P₀)
    · exact h
  have hpair : Measurable fun ω₀ : Ω₀ => (X₀ ω₀, ω₀) := hX₀.prodMk measurable_id
  set ρ : Measure (DistC × Ω₀) := P₀.map fun ω₀ => (X₀ ω₀, ω₀) with hρ
  haveI : IsProbabilityMeasure ρ := (Measure.isProbabilityMeasure_map_iff hpair.aemeasurable).2 ‹_›
  set κ := ρ.condKernel
  have hfst : ρ.fst = P.map X := by
    rw [hlaw, Measure.fst, hρ, Measure.map_map measurable_fst hpair]; rfl
  set P' : Measure (Ω × Ω₀) := P ⊗ₘ (κ.comap X hXm) with hP'
  have hq : Measurable fun p : Ω × Ω₀ => (X p.1, p.2) := (hXm.comp measurable_fst).prodMk
    measurable_snd
  -- the joint law of `(X ∘ fst, snd)` is that of `(X₀, id)`
  have hjoint : P'.map (fun p : Ω × Ω₀ => (X p.1, p.2)) = ρ := by
    have e : P'.map (fun p : Ω × Ω₀ => (X p.1, p.2)) = (P.map X) ⊗ₘ κ := by
      ext s hs
      rw [Measure.map_apply hq hs, hP', Measure.compProd_apply (hq hs),
        Measure.compProd_apply hs, lintegral_map (κ.measurable_kernel_prodMk_left hs) hXm]
      rfl
    rw [e, ← hfst]
    exact ρ.disintegrate κ
  have hP1 : P'.map Prod.fst = P := by rw [hP']; exact Measure.fst_compProd P _
  have hP2 : P'.map Prod.snd = P₀ := by
    have : P'.map Prod.snd = (P'.map fun p : Ω × Ω₀ => (X p.1, p.2)).map Prod.snd := by
      rw [Measure.map_map measurable_snd hq]; rfl
    rw [this, hjoint, hρ, Measure.map_map measurable_snd hpair]
    exact Measure.map_id
  haveI : IsProbabilityMeasure P' := by rw [hP']; infer_instance
  have pull1 : ∀ {p : Ω → Prop}, (∀ᵐ ω ∂P, p ω) → ∀ᵐ q ∂P', p q.1 := fun h =>
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hP1]; exact h)
  have pull2 : ∀ {p : Ω₀ → Prop}, (∀ᵐ ω ∂P₀, p ω) → ∀ᵐ q ∂P', p q.2 := fun h =>
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hP2]; exact h)
  have hP2s : ∀ c, MeasurableSet c → P' (Prod.snd ⁻¹' c) = P₀ c := fun c hc => by
    rw [← Measure.map_apply measurable_snd hc, hP2]
  -- `X ∘ fst = X₀ ∘ snd` a.s.
  have hdiag : ∀ᵐ q ∂P', X q.1 = X₀ q.2 := by
    have hD : MeasurableSet {y : DistC × Ω₀ | y.1 = X₀ y.2} :=
      measurableSet_eq_fun measurable_fst (hX₀.comp measurable_snd)
    have h0 : ρ {y : DistC × Ω₀ | y.1 = X₀ y.2}ᶜ = 0 := by
      rw [hρ, Measure.map_apply hpair hD.compl]
      simp
    rw [← hjoint, Measure.map_apply hq hD.compl] at h0
    exact ae_iff.2 h0
  -- the pulled-back filtration
  let ℱ' : Filtration ℕ (inferInstance : MeasurableSpace (Ω × Ω₀)) :=
    ⟨fun n => (ℱ n).comap Prod.snd, fun i j hij => MeasurableSpace.comap_mono (ℱ.mono hij),
      fun n => (MeasurableSpace.comap_mono (ℱ.le n)).trans measurable_snd.comap_le⟩
  have hsup : (⨆ n, ℱ' n) = (⨆ n, ℱ n).comap Prod.snd := MeasurableSpace.comap_iSup.symm
  have hX' : Measurable[⨆ n, ℱ' n] fun q : Ω × Ω₀ => X₀' q.2 := by
    rw [hsup]; exact fun s hs => ⟨_, hX₀' hs, rfl⟩
  have hXX' : (fun q : Ω × Ω₀ => X q.1) =ᵐ[P'] fun q => X₀' q.2 := by
    filter_upwards [hdiag, pull2 hXX₀] with q h1 h2
    rw [h1, h2]
  have hsplit' : ∀ n, ∃ S : Ω × Ω₀ → C(ℂ, ℝ), ∃ R : Ω × Ω₀ → DistC,
      IsCoarseSplit P' (ℱ' n) (fun q => X q.1) S R := by
    intro n
    obtain ⟨S, R, hs⟩ := hsplit n
    have hSm : Measurable S := hs.measS.mono (ℱ.le n) le_rfl
    refine ⟨fun q => S q.2, fun q => R q.2, ⟨fun t ht => ⟨_, hs.measS ht, rfl⟩,
      hs.measR.comp measurable_snd, ?_, ?_, fun x y => ?_, ?_⟩⟩
    · rw [Indep_iff]
      rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      have ha' : MeasurableSet a := ℱ.le n a ha
      have hb' : MeasurableSet (R ⁻¹' b) := hs.measR hb
      have e : Prod.snd ⁻¹' a ∩ (fun q : Ω × Ω₀ => R q.2) ⁻¹' b =
          Prod.snd ⁻¹' (a ∩ R ⁻¹' b) := rfl
      rw [e, hP2s _ (ha'.inter hb'), hP2s _ ha', show (fun q : Ω × Ω₀ => R q.2) ⁻¹' b =
        Prod.snd ⁻¹' (R ⁻¹' b) from rfl, hP2s _ hb']
      exact (Indep_iff _ _ _).1 hs.indep a _ ha ⟨b, hb, rfl⟩
    · refine ⟨fun I => ?_⟩
      have hI := hs.gauss.hasGaussianLaw I
      have hmI : AEMeasurable (fun ω => I.restrict fun x => S ω x) P₀ := hI.aemeasurable
      refine ⟨?_, ?_⟩
      · exact (show AEMeasurable _ (P'.map Prod.snd) by rw [hP2]; exact hmI).comp_aemeasurable
          measurable_snd.aemeasurable
      · have e : P'.map (fun q : Ω × Ω₀ => I.restrict fun x => S q.2 x) =
            P₀.map (fun ω => I.restrict fun x => S ω x) := by
          rw [← hP2, AEMeasurable.map_map_of_aemeasurable (by rw [hP2]; exact hmI)
            measurable_snd.aemeasurable]
          rfl
        rw [e]; exact hI.isGaussian_map
    · have hc := hs.cov_nonneg x y
      have hx : Measurable fun ω => S ω x := (continuous_eval_const x).measurable.comp hSm
      have hy : Measurable fun ω => S ω y := (continuous_eval_const y).measurable.comp hSm
      rw [← hP2, covariance_map_fun hx.aestronglyMeasurable hy.aestronglyMeasurable
        measurable_snd.aemeasurable] at hc
      exact hc
    · filter_upwards [hdiag, pull2 hs.eq] with q h1 h2
      rw [h1, h2]
  have hFK : ∀ {Θ : DistC → ℝ}, IsFKGFunZB P X Θ → IsFKGFunZB P' (fun q => X q.1) Θ :=
    fun hΘ => ⟨hΘ.meas, hΘ.bdd, pull1 hΘ.mono, pull1 hΘ.cont⟩
  have key := cov_nonneg_of_coarseSplit ℱ' (hXm.comp measurable_fst) hX' hXX' hsplit'
    (hFK hΦ) (hFK hΨ)
  rw [← hP1, covariance_map_fun (X := fun ω => Φ (X ω)) (Y := fun ω => Ψ (X ω)) (hΦ.meas.comp hXm).aestronglyMeasurable
    (hΨ.meas.comp hXm).aestronglyMeasurable measurable_fst.aemeasurable]
  exact key

end Transfer

/-- **A standard Borel model of the zero-boundary GFF on `U` with the splitting of CONF
C:722–738** (white-noise decomposition `h = h_{0,t} + h_{t,∞}`, Rhodes–Vargas Lemma 5.4):
a field `X₀` with `IsZBExtField U`, a filtration `ℱ` whose limit carries `X₀` (a.e.), and at
every level a coarse continuous positively correlated Gaussian part plus an independent fine
part. Open input (the white-noise construction). -/
def CONFZBCoarseModel (U : TopologicalSpace.Opens ℂ) : Prop :=
  ∃ (Ω₀ : Type) (m₀ : MeasurableSpace Ω₀) (_ : StandardBorelSpace Ω₀) (P₀ : Measure Ω₀)
    (_ : IsProbabilityMeasure P₀) (X₀ X₀' : Ω₀ → DistC) (ℱ : Filtration ℕ m₀),
    IsZBExtField U X₀ P₀ ∧ Measurable[⨆ n, ℱ n] X₀' ∧ X₀ =ᵐ[P₀] X₀' ∧
      ∀ n, ∃ S : Ω₀ → C(ℂ, ℝ), ∃ R : Ω₀ → DistC, IsCoarseSplit P₀ (ℱ n) X₀ S R

/-- **CONF Lemma 2.10 on `U`** from a model of the splitting on `U` -/
theorem confLem2_10_at_of_model {U : TopologicalSpace.Opens ℂ} (H : CONFZBCoarseModel U)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → DistC)
    (hX : IsZBExtField U X P) (Φ Ψ : DistC → ℝ) (hΦ : IsFKGFunZB P X Φ)
    (hΨ : IsFKGFunZB P X Ψ) : 0 ≤ cov[fun ω => Φ (X ω), fun ω => Ψ (X ω); P] := by
  obtain ⟨Ω₀, m₀, hsb, P₀, hP₀, X₀, X₀', ℱ, hX₀, hX₀', hXX₀, hsplit⟩ := H
  exact cov_nonneg_of_model ℱ hX₀.measurable hX₀' hXX₀ hsplit hX.measurable
    (law_eq_of_isZBExtField hX hX₀) hΦ hΨ

end LQGMetric.CONF
