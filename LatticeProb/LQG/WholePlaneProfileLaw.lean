import LatticeProb.LQG.LQGMeasureDerived
import LatticeProb.LQG.LQGNegLognormal

/-!
# The law of the LQG measure of a whole-plane Gaussian free field is the same in every model

The circle-average process `(r, z) ↦ h_r(z)` of a whole-plane GFF is almost surely continuous on
`(0, ∞) × ℂ`, so it has a modification `F` with values in the Polish space `C((0, ∞) × ℂ, ℝ)` of
continuous circle-average profiles. Evaluation at a dense sequence of circle parameters is a continuous
injection of this Polish space into `ℕ → ℝ`, hence a measurable embedding (Lusin-Souslin), and the
image law is the law of countably many circle averages, which is the same centred Gaussian law in every
model. So the law of the profile does not depend on the model, and since the γ-LQG measure is almost
surely a measurable function of the profile (Duplantier-Sheffield 2011, Proposition 1.1, in the decoder
form of `LatticeProb.LQG.ProfileDerived.lqgMeasureOfProfileMeasurable_lp`), every measurable event of
the LQG measure has the same probability in every model.

* `LatticeProb.LQG.measurableEmbedding_profileEval`: evaluation at a dense sequence is a measurable
  embedding of the space of continuous profiles.
* `LatticeProb.LQG.exists_measurable_profile`: a measurable continuous modification of the circle-average
  process of a whole-plane GFF.
* `LatticeProb.LQG.map_profile_eq_of_isWholePlaneGFF`: the law of the profile is the same for any two
  whole-plane GFFs.
* `LatticeProb.LQG.ae_mem_iff_of_isWholePlaneGFF`: for a measurable set `E` of measures,
  `μ ∈ E` almost surely in one model iff `μ' ∈ E` almost surely in another.
-/

open MeasureTheory Filter Topology Set

namespace LatticeProb.LQG

open LatticeProb.Gauss ProfileDerived

/-- A dense sequence of circle parameters `(r, z) ∈ (0, ∞) × ℂ`. -/
noncomputable def circleParamSeq : ℕ → CircleParameter :=
  @TopologicalSpace.denseSeq CircleParameter _ _ ⟨⟨⟨1, by norm_num⟩, 0⟩⟩

theorem denseRange_circleParamSeq : DenseRange circleParamSeq :=
  @TopologicalSpace.denseRange_denseSeq CircleParameter _ _ ⟨⟨⟨1, by norm_num⟩, 0⟩⟩

/-- The values of a continuous circle-average profile along the dense sequence `circleParamSeq`. -/
noncomputable def profileEval (y : C(CircleParameter, ℝ)) (n : ℕ) : ℝ := y (circleParamSeq n)

theorem continuous_profileEval : Continuous profileEval :=
  continuous_pi fun n => continuous_eval_const (circleParamSeq n)

theorem injective_profileEval : Function.Injective profileEval := fun y y' h =>
  ContinuousMap.coe_injective <| Continuous.ext_on denseRange_circleParamSeq y.continuous
    y'.continuous (by rintro _ ⟨n, rfl⟩; exact congrFun h n)

/-- **Evaluation along a dense sequence is a measurable embedding** of the Polish space of continuous
circle-average profiles into `ℕ → ℝ` (Lusin-Souslin). -/
theorem measurableEmbedding_profileEval : MeasurableEmbedding profileEval :=
  continuous_profileEval.measurableEmbedding injective_profileEval

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
  {hcirc' : Ω' → ℝ → ℂ → ℝ}

open Classical in
/-- **A measurable continuous modification of the circle-average process.** Every whole-plane GFF has a
measurable `F : Ω → C((0, ∞) × ℂ, ℝ)` with `F ω (r, z) = h_r(z)` for all `(r, z)`, almost surely. -/
theorem exists_measurable_profile (hh : IsWholePlaneGFF P hC hcirc) :
    ∃ F : Ω → C(CircleParameter, ℝ), Measurable F ∧
      ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω p.1 p.2 := by
  set Gc : Set Ω := {ω | ¬ ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)}
  set N := toMeasurable P Gc
  have hN : P N = 0 := by rw [measure_toMeasurable]; exact ae_iff.1 hh.ae_continuousOn_circle
  have hcont : ∀ ω ∈ Nᶜ, Continuous fun p : CircleParameter => hcirc ω p.1.1 p.2 := fun ω hω => by
    have h : ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) := by
      by_contra hc; exact hω (subset_toMeasurable P Gc hc)
    exact h.comp_continuous (continuous_subtype_val.prodMap continuous_id)
      fun p => ⟨p.1.2, mem_univ _⟩
  let F : Ω → C(CircleParameter, ℝ) := fun ω =>
    if hω : ω ∈ Nᶜ then ⟨fun p => hcirc ω p.1.1 p.2, hcont ω hω⟩ else 0
  have hval : ∀ ω p, F ω p = if ω ∈ Nᶜ then hcirc ω p.1.1 p.2 else 0 := by
    intro ω p
    by_cases h : ω ∈ Nᶜ
    · simp only [F, h, ↓reduceDIte, ↓reduceIte, ContinuousMap.coe_mk]
    · simp only [F, h, ↓reduceDIte, ↓reduceIte, ContinuousMap.zero_apply]
  refine ⟨F, ?_, ?_⟩
  · refine measurableEmbedding_profileEval.measurable_comp_iff.1 (Measurable.of_eval fun n => ?_)
    have : (fun ω => (profileEval ∘ F) ω n) = fun ω =>
        if ω ∈ Nᶜ then hcirc ω (circleParamSeq n).1.1 (circleParamSeq n).2 else 0 :=
      funext fun ω => hval ω _
    rw [this]
    exact Measurable.ite (measurableSet_toMeasurable P Gc).compl
      (hh.measurable_circle _ _ (circleParamSeq n).1.2) measurable_const
  · filter_upwards [compl_mem_ae_iff.2 hN] with ω hω p
    rw [hval]; simp only [hω, ↓reduceIte]

/-- **The law of the circle-average profile is the same in every model.** For two whole-plane GFFs and
measurable continuous modifications `F`, `F'` of their circle-average processes, `F` and `F'` have the
same law on `C((0, ∞) × ℂ, ℝ)`. -/
theorem map_profile_eq_of_isWholePlaneGFF (hh : IsWholePlaneGFF P hC hcirc)
    (hh' : IsWholePlaneGFF P' hC' hcirc') {F : Ω → C(CircleParameter, ℝ)}
    {F' : Ω' → C(CircleParameter, ℝ)} (hF : Measurable F) (hF' : Measurable F')
    (hFc : ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2)
    (hFc' : ∀ p : CircleParameter, (fun ω => F' ω p) =ᵐ[P'] fun ω => hcirc' ω p.1 p.2) :
    P.map F = P'.map F' := by
  have he := measurableEmbedding_profileEval
  have h1 : P.map (profileEval ∘ F) =
      P.map (fun ω n => hcirc ω (circleParamSeq n).1 (circleParamSeq n).2) :=
    Measure.map_congr ((ae_all_iff.2 fun n => hFc (circleParamSeq n)).mono fun ω hω =>
      funext fun n => hω n)
  have h2 : P'.map (profileEval ∘ F') =
      P'.map (fun ω n => hcirc' ω (circleParamSeq n).1 (circleParamSeq n).2) :=
    Measure.map_congr ((ae_all_iff.2 fun n => hFc' (circleParamSeq n)).mono fun ω hω =>
      funext fun n => hω n)
  have key : P.map (profileEval ∘ F) = P'.map (profileEval ∘ F') := by
    rw [h1, h2]
    exact hh.map_circleVector_eq hh' (fun n => (circleParamSeq n).1.1)
      (fun n => (circleParamSeq n).2) fun n => (circleParamSeq n).1.2
  rw [← he.comap_map (P.map F), ← he.comap_map (P'.map F'), Measure.map_map he.measurable hF,
    Measure.map_map he.measurable hF', key]

/-- **Events of the LQG measure have the same probability in every model.** Let `μ` and `μ'` be the
γ-LQG measures of the fields `h^ℂ − α log |·|` built from two whole-plane GFFs, possibly on different
probability spaces. For every measurable set `E` of measures on `ℂ`, almost surely `μ ∈ E` iff almost
surely `μ' ∈ E`. -/
theorem ae_mem_iff_of_isWholePlaneGFF (hh : IsWholePlaneGFF P hC hcirc)
    (hh' : IsWholePlaneGFF P' hC' hcirc') {γ α : ℝ} {μ : Ω → Measure ℂ} {μ' : Ω' → Measure ℂ}
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hμ' : IsLQGMeasureOfField P' γ α hcirc' μ')
    {E : Set (Measure ℂ)} (hE : MeasurableSet E) :
    (∀ᵐ ω ∂P, μ ω ∈ E) ↔ ∀ᵐ ω ∂P', μ' ω ∈ E := by
  have := hh.isProbabilityMeasure
  have := hh'.isProbabilityMeasure
  obtain ⟨F, hF, hFc⟩ := exists_measurable_profile hh
  obtain ⟨F', hF', hFc'⟩ := exists_measurable_profile hh'
  have hFp : ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2 :=
    fun p => hFc.mono fun ω h => h p
  have hFp' : ∀ p : CircleParameter, (fun ω => F' ω p) =ᵐ[P'] fun ω => hcirc' ω p.1 p.2 :=
    fun p => hFc'.mono fun ω h => h p
  obtain ⟨D, hD, hμD, hDlim⟩ := lqgMeasureOfProfileMeasurable_lp Ω P γ α hC hcirc μ F hh hμ hF hFp
  obtain ⟨D', hD', hμD', hDlim'⟩ :=
    lqgMeasureOfProfileMeasurable_lp Ω' P' γ α hC' hcirc' μ' F' hh' hμ' hF' hFp'
  have hlaw : P.map F = P'.map F' := map_profile_eq_of_isWholePlaneGFF hh hh' hF hF' hFp hFp'
  have e1 : (∀ᵐ ω ∂P, μ ω ∈ E) ↔ ∀ᵐ y ∂(P.map F), D y ∈ E := by
    rw [ae_map_iff (p := fun y => D y ∈ E) hF.aemeasurable (hD hE)]
    constructor
    · intro h; filter_upwards [h, hμD] with ω h1 h2; rwa [← h2]
    · intro h; filter_upwards [h, hμD] with ω h1 h2; rwa [h2]
  have e2 : (∀ᵐ ω ∂P', μ' ω ∈ E) ↔ ∀ᵐ y ∂(P'.map F'), D' y ∈ E := by
    rw [ae_map_iff (p := fun y => D' y ∈ E) hF'.aemeasurable (hD' hE)]
    constructor
    · intro h; filter_upwards [h, hμD'] with ω h1 h2; rwa [← h2]
    · intro h; filter_upwards [h, hμD'] with ω h1 h2; rwa [h2]
  rw [← hlaw] at hDlim'
  have hDD : ∀ᵐ y ∂(P.map F), D y = D' y := by
    filter_upwards [hDlim, hDlim'] with y h h' using isLQGLimit_unique h h'
  rw [e1, e2, ← hlaw]
  constructor
  · intro h; filter_upwards [h, hDD] with y h1 h2; rwa [← h2]
  · intro h; filter_upwards [h, hDD] with y h1 h2; rwa [h2]

end LatticeProb.LQG
