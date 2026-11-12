import LatticeProb.LQG.MatingOfTreesCouplingData
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core2H
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

/-!
# Law transfer for mating-of-trees couplings

Let `V` and `V'` be measurable random elements of the data space of a mating-of-trees coupling,
defined on possibly different probability spaces, with the same law. If the coordinates of `V` form a
mating-of-trees coupling, then so do the coordinates of `V'` as far as the defining properties are
properties of the law: the whole-plane GFF laws of the fields, the Brownian laws, the independence
statements, the uniform law, the measurability of the curves and the law of the boundary-length pair.

The general statements come first: for random elements `V, V'` of a measurable space with the same
law,
* `map_comp_of_map_eq`: measurable functions of `V` and `V'` have the same law;
* `ae_comp_of_map_eq_of_nullMeasurableSet`: an almost sure property of `V` given by a set that is
  null-measurable for the law of `V` is an almost sure property of `V'`;
* `measure_preimage_le_of_map_eq`: the (outer) probability that `V'` lies in such a set is at most
  that for `V`;
* `lintegral_comp_of_map_eq`: expectations of almost everywhere measurable functions agree;
* `indepFun_comp_of_map_eq`: independence of two measurable functions of `V` passes to `V'`;
* `isBrownianReal_comp_of_map_eq`: a measurable function of `V` with values in `C(ℝ≥0, ℝ)` that is
  a Brownian motion gives a Brownian motion as a function of `V'`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MeasureTheory

variable {Ω Ω' 𝒱 β β' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace 𝒱]
  [MeasurableSpace β] [MeasurableSpace β'] {P : Measure Ω} {P' : Measure Ω'} {V : Ω → 𝒱}
  {V' : Ω' → 𝒱}

/-- Measurable functions of two random elements with the same law have the same law. -/
theorem map_comp_of_map_eq (hV : Measurable V) (hV' : Measurable V') (hlaw : P'.map V' = P.map V)
    {f : 𝒱 → β} (hf : Measurable f) : P'.map (fun ω => f (V' ω)) = P.map (fun ω => f (V ω)) := by
  rw [show (fun ω => f (V' ω)) = f ∘ V' from rfl, show (fun ω => f (V ω)) = f ∘ V from rfl,
    ← Measure.map_map hf hV', ← Measure.map_map hf hV, hlaw]

/-- A random element with the law of a random element on a probability space lives on a
probability space. -/
theorem isProbabilityMeasure_of_map_eq [IsProbabilityMeasure P] (hV : Measurable V)
    (hV' : Measurable V') (hlaw : P'.map V' = P.map V) : IsProbabilityMeasure P' := by
  refine ⟨?_⟩
  have h := congrArg (fun μ : Measure 𝒱 => μ univ) hlaw
  simp only [Measure.map_apply hV' MeasurableSet.univ, Measure.map_apply hV MeasurableSet.univ,
    preimage_univ, measure_univ] at h
  exact h

/-- Almost sure properties given by measurable sets pass between random elements with the same
law. -/
theorem ae_comp_of_map_eq (hV : Measurable V) (hV' : Measurable V') (hlaw : P'.map V' = P.map V)
    {T : Set 𝒱} (hT : MeasurableSet T) (h : ∀ᵐ ω ∂P, V ω ∈ T) : ∀ᵐ ω ∂P', V' ω ∈ T := by
  have h1 : ∀ᵐ v ∂(P.map V), v ∈ T := (ae_map_iff hV.aemeasurable hT).2 h
  rw [← hlaw] at h1
  exact (ae_map_iff hV'.aemeasurable hT).1 h1

/-- A null-measurable set for the law of `V` contains a measurable set of full law-measure in it. -/
theorem exists_measurable_subset_map_diff_eq_zero {S : Set 𝒱} (hS : NullMeasurableSet S (P.map V)) :
    ∃ T ⊆ S, MeasurableSet T ∧ P.map V (S \ T) = 0 := by
  obtain ⟨T, hTS, hT, hTe⟩ := hS.exists_measurable_subset_ae_eq
  exact ⟨T, hTS, hT, (ae_eq_set.1 hTe).2⟩

/-- **Almost sure properties pass between random elements with the same law** when the property is
given by a set that is null-measurable for the law (for instance a universally measurable set). -/
theorem ae_comp_of_map_eq_of_nullMeasurableSet (hV : Measurable V) (hV' : Measurable V')
    (hlaw : P'.map V' = P.map V) {S : Set 𝒱} (hS : NullMeasurableSet S (P.map V))
    (h : ∀ᵐ ω ∂P, V ω ∈ S) : ∀ᵐ ω ∂P', V' ω ∈ S := by
  obtain ⟨T, hTS, hT, hdiff⟩ := exists_measurable_subset_map_diff_eq_zero hS
  have h0 : P (V ⁻¹' (S \ T)) = 0 :=
    nonpos_iff_eq_zero.1 ((Measure.le_map_apply hV.aemeasurable _).trans hdiff.le)
  have h0' : ∀ᵐ ω ∂P, V ω ∉ S \ T := ae_iff.2 (by simp only [not_not]; exact h0)
  have hPT : ∀ᵐ ω ∂P, V ω ∈ T := by
    filter_upwards [h, h0'] with ω h1 h2
    by_contra hT'
    exact h2 ⟨h1, hT'⟩
  filter_upwards [ae_comp_of_map_eq hV hV' hlaw hT hPT] with ω hω using hTS hω

/-- The outer probability that `V'` lies in a set that is null-measurable for the law of `V` is
at most the outer probability that `V` lies in it. -/
theorem measure_preimage_le_of_map_eq (hV : Measurable V) (hV' : Measurable V')
    (hlaw : P'.map V' = P.map V) {S : Set 𝒱} (hS : NullMeasurableSet S (P.map V)) :
    P' (V' ⁻¹' S) ≤ P (V ⁻¹' S) := by
  obtain ⟨T, hTS, hT, hdiff⟩ := exists_measurable_subset_map_diff_eq_zero hS
  have hST : P.map V S = P.map V T := by
    refine le_antisymm ?_ (measure_mono hTS)
    calc P.map V S ≤ P.map V (T ∪ S \ T) := measure_mono fun x hx => by
            by_cases hxT : x ∈ T
            · exact Or.inl hxT
            · exact Or.inr ⟨hx, hxT⟩
      _ ≤ P.map V T + P.map V (S \ T) := measure_union_le _ _
      _ = P.map V T := by rw [hdiff, add_zero]
  calc P' (V' ⁻¹' S) ≤ P'.map V' S := Measure.le_map_apply hV'.aemeasurable _
    _ = P.map V T := by rw [hlaw, hST]
    _ = P (V ⁻¹' T) := Measure.map_apply hV hT
    _ ≤ P (V ⁻¹' S) := measure_mono (preimage_mono hTS)

/-- Expectations of an almost everywhere measurable function agree for random elements with the
same law. -/
theorem lintegral_comp_of_map_eq (hV : Measurable V) (hV' : Measurable V')
    (hlaw : P'.map V' = P.map V) {F : 𝒱 → ℝ≥0∞} (hF : AEMeasurable F (P.map V)) :
    ∫⁻ ω, F (V' ω) ∂P' = ∫⁻ ω, F (V ω) ∂P := by
  rw [← lintegral_map' (hlaw ▸ hF) hV'.aemeasurable, hlaw, lintegral_map' hF hV.aemeasurable]

/-- Independence of two measurable functions of a random element depends only on its law. -/
theorem indepFun_comp_of_map_eq [IsFiniteMeasure P] [IsFiniteMeasure P'] (hV : Measurable V)
    (hV' : Measurable V') (hlaw : P'.map V' = P.map V) {f : 𝒱 → β} {g : 𝒱 → β'}
    (hf : Measurable f) (hg : Measurable g) (h : IndepFun (fun ω => f (V ω)) (fun ω => g (V ω)) P) :
    IndepFun (fun ω => f (V' ω)) (fun ω => g (V' ω)) P' := by
  have e1 := map_comp_of_map_eq hV hV' hlaw (hf.prodMk hg)
  have e2 := map_comp_of_map_eq hV hV' hlaw hf
  have e3 := map_comp_of_map_eq hV hV' hlaw hg
  have h' := (indepFun_iff_map_prod_eq_prod_map_map (hf.comp hV).aemeasurable
    (hg.comp hV).aemeasurable).1 h
  show IndepFun (f ∘ V') (g ∘ V') P'
  rw [indepFun_iff_map_prod_eq_prod_map_map (hf.comp hV').aemeasurable (hg.comp hV').aemeasurable]
  simp only [Function.comp_def] at h' ⊢
  rw [e1, e2, e3]
  exact h'

/-- The coercion of continuous paths on `[0, ∞)` to functions is measurable. -/
theorem measurable_coe_continuousMap_nnreal : Measurable fun c : C(ℝ≥0, ℝ) => (⇑c : ℝ≥0 → ℝ) :=
  measurable_pi_iff.2 fun t => ContinuousMap.measurable_eval t

/-- **The Brownian law passes between random elements with the same law.** -/
theorem isBrownianReal_comp_of_map_eq (hV : Measurable V) (hV' : Measurable V')
    (hlaw : P'.map V' = P.map V) {W : 𝒱 → C(ℝ≥0, ℝ)} (hW : Measurable W)
    (h : IsBrownianReal (fun t ω => W (V ω) t) P) : IsBrownianReal (fun t ω => W (V' ω) t) P' where
  hasLaw I := by
    have hg : Measurable fun v => I.restrict fun t => W v t :=
      measurable_pi_iff.2 fun i => (ContinuousMap.measurable_eval (i : ℝ≥0)).comp hW
    refine ⟨(hg.comp hV').aemeasurable, ?_⟩
    convert (h.hasLaw I).map_eq using 1
    exact map_comp_of_map_eq hV hV' hlaw hg
  cont := Filter.Eventually.of_forall fun ω => (W (V' ω)).continuous

end MeasureTheory

namespace MatedCRTHarmonic

namespace MatedCRT

variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
  {γ : ℝ} {V : Ω → CouplingData} {V' : Ω' → CouplingData}

open CouplingData

/-- The pair of Brownian paths of the γ-quantum cone, as functions. -/
theorem measurable_conePaths :
    Measurable fun v : CouplingData => ((⇑v.B : ℝ≥0 → ℝ), (⇑v.B' : ℝ≥0 → ℝ)) :=
  (measurable_coe_continuousMap_nnreal.comp measurable_B).prodMk
    (measurable_coe_continuousMap_nnreal.comp measurable_B')

/-- The pair of Brownian paths of the `0`-quantum cone, as functions. -/
theorem measurable_conePaths₀ :
    Measurable fun v : CouplingData => ((⇑v.B₀ : ℝ≥0 → ℝ), (⇑v.B₀' : ℝ≥0 → ℝ)) :=
  (measurable_coe_continuousMap_nnreal.comp measurable_B₀).prodMk
    (measurable_coe_continuousMap_nnreal.comp measurable_B₀')

section LawFields

variable (hC : IsCouplingData γ P V) (hV : Measurable V) (hV' : Measurable V')
  (hlaw : P'.map V' = P.map V)
include hC hV hV' hlaw

theorem IsCouplingData.isProbabilityMeasure_of_map_eq : IsProbabilityMeasure P' := by
  have := (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC).isProbabilityMeasure
  exact MeasureTheory.isProbabilityMeasure_of_map_eq hV hV' hlaw

theorem IsCouplingData.gff_of_map_eq : LQGMetric.IsWholePlaneGFF (fun ω => (V' ω).X) P' :=
  LQGMetric.DFGPS.L217.isWholePlaneGFF_of_map_eq (measurable_X.comp hV')
    (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC).gff
    (map_comp_of_map_eq hV hV' hlaw measurable_X)

theorem IsCouplingData.gff₀_of_map_eq : LQGMetric.IsWholePlaneGFF (fun ω => (V' ω).X₀) P' :=
  LQGMetric.DFGPS.L217.isWholePlaneGFF_of_map_eq (measurable_X₀.comp hV')
    (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC).gff₀
    (map_comp_of_map_eq hV hV' hlaw measurable_X₀)

theorem IsCouplingData.bm_of_map_eq :
    IsBrownianReal (fun t ω => (V' ω).B t) P' ∧ IsBrownianReal (fun t ω => (V' ω).B' t) P' ∧
      IsBrownianReal (fun t ω => (V' ω).B₀ t) P' ∧ IsBrownianReal (fun t ω => (V' ω).B₀' t) P' := by
  have hC' := (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC)
  exact ⟨isBrownianReal_comp_of_map_eq hV hV' hlaw measurable_B hC'.bm_B,
    isBrownianReal_comp_of_map_eq hV hV' hlaw measurable_B' hC'.bm_B',
    isBrownianReal_comp_of_map_eq hV hV' hlaw measurable_B₀ hC'.bm_B₀,
    isBrownianReal_comp_of_map_eq hV hV' hlaw measurable_B₀' hC'.bm_B₀'⟩

theorem IsCouplingData.indep_cone_of_map_eq :
    (IndepFun (fun ω => (V' ω).X) (fun ω => ((fun t => (V' ω).B t), (fun t => (V' ω).B' t))) P' ∧
      IndepFun (fun ω t => (V' ω).B t) (fun ω t => (V' ω).B' t) P') ∧
    (IndepFun (fun ω => (V' ω).X₀) (fun ω => ((fun t => (V' ω).B₀ t), (fun t => (V' ω).B₀' t))) P' ∧
      IndepFun (fun ω t => (V' ω).B₀ t) (fun ω t => (V' ω).B₀' t) P') := by
  have hC' := (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC)
  have := hC'.isProbabilityMeasure
  have := hC.isProbabilityMeasure_of_map_eq hV hV' hlaw
  have hc := measurable_coe_continuousMap_nnreal
  exact ⟨⟨indepFun_comp_of_map_eq hV hV' hlaw measurable_X measurable_conePaths hC'.indep_cone.1,
      indepFun_comp_of_map_eq hV hV' hlaw (hc.comp measurable_B) (hc.comp measurable_B')
        hC'.indep_cone.2⟩,
    ⟨indepFun_comp_of_map_eq hV hV' hlaw measurable_X₀ measurable_conePaths₀ hC'.indep_cone₀.1,
      indepFun_comp_of_map_eq hV hV' hlaw (hc.comp measurable_B₀) (hc.comp measurable_B₀')
        hC'.indep_cone₀.2⟩⟩

theorem IsCouplingData.igField_of_map_eq :
    LQGMetric.IsNormalizedWPGFF (fun ω => (V' ω).hIG) P' ∧
      P'.map (fun ω => (V' ω).U) = volume[|Ico (0 : ℝ) (2 * Real.pi * igChi γ)] ∧
      IndepFun (fun ω => (V' ω).hIG) (fun ω => (V' ω).U) P' := by
  have hC' := (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC)
  have := hC'.isProbabilityMeasure
  have := hC.isProbabilityMeasure_of_map_eq hV hV' hlaw
  obtain ⟨⟨hgff, hnorm⟩, hU, hind⟩ := hC'.igField
  have hTm : MeasurableSet {v : CouplingData | LQGMetric.circleAvg v.hIG 1 0 = 0} :=
    measurableSet_eq_fun ((LQGMetric.measurable_circleAvg_left 1 0).comp measurable_hIG)
      measurable_const
  refine ⟨⟨LQGMetric.DFGPS.L217.isWholePlaneGFF_of_map_eq (measurable_hIG.comp hV') hgff
      (map_comp_of_map_eq hV hV' hlaw measurable_hIG),
    ae_comp_of_map_eq hV hV' hlaw hTm hnorm⟩, ?_,
    indepFun_comp_of_map_eq hV hV' hlaw measurable_hIG measurable_U hind⟩
  rw [map_comp_of_map_eq hV hV' hlaw measurable_U]
  exact hU

theorem IsCouplingData.indep_curve_of_map_eq :
    IndepFun (fun ω => ((V' ω).hIG, (V' ω).U))
      (fun ω => ((V' ω).X, (fun t => (V' ω).B t), (fun t => (V' ω).B' t), (V' ω).X₀,
        (fun t => (V' ω).B₀ t), (fun t => (V' ω).B₀' t))) P' := by
  have hC' := (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC)
  have := hC'.isProbabilityMeasure
  have := hC.isProbabilityMeasure_of_map_eq hV hV' hlaw
  have hc := measurable_coe_continuousMap_nnreal
  exact indepFun_comp_of_map_eq hV hV' hlaw (measurable_hIG.prodMk measurable_U)
    (measurable_X.prodMk ((hc.comp measurable_B).prodMk ((hc.comp measurable_B').prodMk
      (measurable_X₀.prodMk ((hc.comp measurable_B₀).prodMk (hc.comp measurable_B₀'))))))
    hC'.indep_curve

theorem IsCouplingData.boundaryLawBM_of_map_eq :
    IsCorrelatedBM2 γ (P'.map fun ω => (V' ω).bm) := by
  rw [map_comp_of_map_eq hV hV' hlaw measurable_bm]
  exact (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC).boundaryLawBM

end LawFields

/-- The curves and the boundary-length pair of a measurable random element of the data space are
measurable. -/
theorem measurable_curves_of_measurable (hV' : Measurable V') :
    Measurable (fun ω => (V' ω).ηL) ∧ Measurable (fun ω => (V' ω).η) ∧
      Measurable (fun ω => (V' ω).η₀) ∧ Measurable (fun ω => (V' ω).bm) :=
  ⟨measurable_ηL.comp hV', measurable_η.comp hV', measurable_η₀.comp hV', measurable_bm.comp hV'⟩


end MatedCRT

end MatedCRTHarmonic

end
