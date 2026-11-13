/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.FlowCodingLocalIntegrability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.CellRootedFrameInvariance

/-!
# `hloc` is PROVED: local integrability of the line density at the bridge kernel

The frontier input `hloc` of `FlowCodingIntegrability.reflectedInvarianceConclusions_validLaw_flowKernel_loc`
(:88-90) — for each harmonic coordinate `Φ` and direction `ζ`,
`∀ᵐ ω ∂(ν ⊗ₘ κF), LocallyIntegrable (lineDensity Φ ζ ω) volume` — is discharged here from MTP,
(FE) and the harmonic coordinate (`ae_locallyIntegrable_lineDensity_flowKernel`).

Route.  At a live gate environment the fibre of `κF` is the push-forward of `P ⊗ P`
(`P` = the area walk from the origin cell) under `build`, which glues the forward half `ω.1` on
`[0, ∞)` and the left limit of the backward half `ω.2` at `-s` for `s < 0`.

* **Forward half** (`lintegral_Icc_lineDensity_build_lt_top`): on `[0, n]` the line density IS the
  directional bracket density along the area path of `ω.1`, whose entries are interval integrable
  `P`-a.s. (`CanonicalOccupationWeld.ae_intervalIntegrable_bracketDensity`, from MTP + FE + `hΦ`).
* **Backward half.**  The left limit is removed at FIXED times: at every fixed `s < 0` the walk
  `ω.2` is a.s. locally constant at `-s` (`IsReflectedWalk`, fixed-time definedness), so
  `Y_s = Y'_{-s}` a.s., where `Y' := build (swap ω)` is the configuration whose FORWARD half is
  `ω.2` (`build_label_neg_eq_swap`).  Tonelli (`Measure.ae_ae_comm`, on a jointly measurable event
  of càdlàg evaluations) turns this into: a.s., for a.e. `s < 0`, `Y_s = Y'_{-s}`
  (`ae_ae_build_neg_eq`).  The reflection `s ↦ -s` preserves Lebesgue measure, so the backward
  integral over `[-n, 0)` is the forward integral of `Y'` over `(0, n]`, finite because
  `swap` preserves `P ⊗ P` (`lintegral_Ico_lineDensity_build_lt_top`).
* **Combination** (`locallyIntegrable_lineDensity_of_halves`) through
  `CellRootedFrameInvariance.locallyIntegrable_iff_lintegral_Icc`, and the kernel level through
  the measurable local-integrability event
  (`CellRootedFrameInvariance.measurableSet_locallyIntegrable_lineDensity`) and
  `Measure.ae_compProd_of_ae_ae`.

No countability of the jump set of a càdlàg path is needed (the left limit is only evaluated at
fixed times).  Nothing here certifies the transport, `hregen`, or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.FlowCodingLocalIntegrability

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients HarmonicMainStatement
open RootDensities
open StatementIngredients AreaClocks MartingaleIngredients BracketTimeAverage
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.TrajectoryCoding ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedGMS.FlowCodingLine ReflectedGMS.FlowCodingKernel ReflectedGMS.FlowCodingDensity
open ReflectedGMS.FlowCodingFrontier ReflectedGMS.DirectionalBracketLLNWeld

/-! ### 1. One environment: the two halves of a built configuration -/

section Sample

variable {z : CellField} {e : Env} {r : Vertex e.val}

/-- Local constancy of the walk at a fixed nonnegative time makes its label path constant on a
left neighbourhood. -/
theorem labelPath_eventually_const_of_localConst {ω : (areaFamily e).Ω} {a : ℝ}
    (h : ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball a.toNNReal ε,
      (areaFamily e).X s ω = (areaFamily e).X a.toNNReal ω) :
    ∀ᶠ x in 𝓝[<] a, labelPath e ω x.toNNReal = labelPath e ω a.toNNReal := by
  obtain ⟨ε, hε, hball⟩ := h
  have hcont : ContinuousAt Real.toNNReal a := continuous_real_toNNReal.continuousAt
  have hmem : Real.toNNReal ⁻¹' Metric.ball a.toNNReal ε ∈ 𝓝 a :=
    hcont (Metric.ball_mem_nhds _ hε)
  filter_upwards [nhdsWithin_le_nhds hmem] with x hx
  have hX : (areaFamily e).X x.toNNReal ω = (areaFamily e).X a.toNNReal ω := hball _ hx
  show toENatLabel (((areaFamily e).X x.toNNReal ω).map Subtype.val) =
    toENatLabel (((areaFamily e).X a.toNNReal ω).map Subtype.val)
  rw [hX]

/-- **Forward half**: on `[0, ∞)` the line density of a built configuration is the directional
bracket density along the area path of the forward sample. -/
theorem lineDensity_build_of_nonneg (Φ : CellField) (ζ : Fin 2 → ℝ)
    {ω : (areaFamily e).Ω × (areaFamily e).Ω} (h : ω ∈ goodSet z e r) {s : ℝ} (hs : 0 ≤ s) :
    lineDensity Φ ζ (e, build z e r ω) s =
      dirForm (stateBracketDensity (decode e) (Φ.at e)
        (exponentialAreaPath (decode e) (exhaustion e) s.toNNReal ω.1)) ζ := by
  rw [lineDensity_eq_pathForwardDensity Φ e _ ζ hs, readOff_build h]
  rfl

/-- **The forward half has finite `L¹` norm on every `[0, n]`** when the bracket density along the
forward sample is interval integrable. -/
theorem lintegral_Icc_lineDensity_build_lt_top (Φ : CellField) (ζ : Fin 2 → ℝ)
    {ω : (areaFamily e).Ω × (areaFamily e).Ω} (h : ω ∈ goodSet z e r)
    (hint : ∀ (i j : Fin 2) (t : ℝ≥0), IntervalIntegrable
      (fun s : ℝ => stateBracketDensity (decode e) (Φ.at e)
        (exponentialAreaPath (decode e) (exhaustion e) (Real.toNNReal s) ω.1) i j)
      volume 0 (t : ℝ))
    (n : ℕ) :
    ∫⁻ s in Icc (0 : ℝ) n, ‖lineDensity Φ ζ (e, build z e r ω) s‖ₑ < ∞ := by
  have hent : ∀ i j : Fin 2, IntegrableOn (fun s : ℝ => stateBracketDensity (decode e) (Φ.at e)
      (exponentialAreaPath (decode e) (exhaustion e) (Real.toNNReal s) ω.1) i j)
      (Icc (0 : ℝ) n) volume := by
    intro i j
    have h1 := hint i j (n : ℝ≥0)
    rw [NNReal.coe_natCast, intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)]
      at h1
    exact (integrableOn_Icc_iff_integrableOn_Ioc (by finiteness)).2 h1
  have hg : IntegrableOn (fun s : ℝ => ∑ i : Fin 2, ∑ j : Fin 2, ζ i *
      stateBracketDensity (decode e) (Φ.at e)
        (exponentialAreaPath (decode e) (exhaustion e) (Real.toNNReal s) ω.1) i j * ζ j)
      (Icc (0 : ℝ) n) volume :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      ((hent i j).const_mul (ζ i)).mul_const (ζ j)
  rw [setLIntegral_congr_fun measurableSet_Icc (fun s hs => by
    rw [lineDensity_build_of_nonneg Φ ζ h hs.1])]
  exact hasFiniteIntegral_iff_enorm.1 hg.2

/-- **Fixed-time identification of the backward half**: if the backward sample is locally constant
at `-s` (`s < 0`), the built configuration at `s` reads the FORWARD half of the swapped pair at
`-s`. -/
theorem build_label_neg_eq_swap {ω : (areaFamily e).Ω × (areaFamily e).Ω}
    (h : ω ∈ goodSet z e r) (h' : ω.swap ∈ goodSet z e r) {s : ℝ} (hs : s < 0)
    (hloc : ∃ ε : ℝ, 0 < ε ∧ ∀ u ∈ Metric.ball (-s).toNNReal ε,
      (areaFamily e).X u ω.2 = (areaFamily e).X (-s).toNNReal ω.2) :
    (build z e r ω).1.toFun s = (build z e r ω.swap).1.toFun (-s) := by
  rw [build_label_of_nonneg h' (neg_nonneg.2 hs.le), build_of_mem z e r h]
  show glue (fun s : ℝ => labelPath e ω.1 s.toNNReal) (fun s : ℝ => labelPath e ω.2 s.toNNReal)
    s = _
  rw [glue_of_neg _ _ hs,
    leftLim_eq_of_eventuallyEq_const (labelPath_eventually_const_of_localConst (a := -s) hloc)]
  rfl

/-- The event "the backward half at `s < 0` reads the swapped forward half at `-s`" is jointly
measurable in the sample pair and the time. -/
theorem measurableSet_build_neg_eq :
    MeasurableSet {x : ((areaFamily e).Ω × (areaFamily e).Ω) × ℝ |
      x.2 < 0 → (build z e r x.1).1.toFun x.2 = (build z e r x.1.swap).1.toFun (-x.2)} := by
  have hb : Measurable (build z e r) := measurable_build z e r
  have hY : Measurable fun x : ((areaFamily e).Ω × (areaFamily e).Ω) × ℝ =>
      ((build z e r x.1).1, x.2) :=
    (measurable_fst.comp (hb.comp measurable_fst)).prodMk measurable_snd
  have hY' : Measurable fun x : ((areaFamily e).Ω × (areaFamily e).Ω) × ℝ =>
      ((build z e r x.1.swap).1, -x.2) :=
    (measurable_fst.comp (hb.comp (measurable_swap.comp measurable_fst))).prodMk
      measurable_snd.neg
  have hev : Measurable fun p : CadlagPath ℕ∞ × ℝ => p.1.toFun p.2 :=
    CadlagPath.measurable_eval_uncurry
  have hf1c := hev.comp hY
  have hf2c := hev.comp hY'
  have hf1 : Measurable fun x : ((areaFamily e).Ω × (areaFamily e).Ω) × ℝ =>
      (build z e r x.1).1.toFun x.2 := by
    simpa only [Function.comp_def] using hf1c
  have hf2 : Measurable fun x : ((areaFamily e).Ω × (areaFamily e).Ω) × ℝ =>
      (build z e r x.1.swap).1.toFun (-x.2) := by
    simpa only [Function.comp_def] using hf2c
  have hset : {x : ((areaFamily e).Ω × (areaFamily e).Ω) × ℝ |
      x.2 < 0 → (build z e r x.1).1.toFun x.2 = (build z e r x.1.swap).1.toFun (-x.2)} =
      {x : ((areaFamily e).Ω × (areaFamily e).Ω) × ℝ | x.2 < 0}ᶜ ∪
        {x | (build z e r x.1).1.toFun x.2 = (build z e r x.1.swap).1.toFun (-x.2)} := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff]
    exact imp_iff_not_or
  rw [hset]
  exact (measurableSet_lt measurable_snd measurable_const).compl.union
    (measurableSet_eq_fun hf1 hf2)

/-- **Tonelli**: almost surely, for a.e. `s < 0`, the backward half at `s` reads the swapped
forward half at `-s`. -/
theorem ae_ae_build_neg_eq (hadm : EnvironmentAreaClockAdmissible e)
    (hgood : ∀ᵐ ω ∂(((areaFamily e).P r).prod ((areaFamily e).P r)), ω ∈ goodSet z e r) :
    ∀ᵐ ω ∂(((areaFamily e).P r).prod ((areaFamily e).P r)), ∀ᵐ s ∂(volume : Measure ℝ),
      s < 0 → (build z e r ω).1.toFun s = (build z e r ω.swap).1.toFun (-s) := by
  have hw := isReflectedWalk_areaFamily e hadm
  have hgood' : ∀ᵐ ω ∂(((areaFamily e).P r).prod ((areaFamily e).P r)),
      ω.swap ∈ goodSet z e r :=
    (Measure.measurePreserving_swap (μ := (areaFamily e).P r)
      (ν := (areaFamily e).P r)).quasiMeasurePreserving.ae hgood
  have h : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ ω ∂(((areaFamily e).P r).prod ((areaFamily e).P r)),
      s < 0 → (build z e r ω).1.toFun s = (build z e r ω.swap).1.toFun (-s) := by
    refine Eventually.of_forall fun s => ?_
    by_cases hs : s < 0
    · filter_upwards [hgood, hgood',
        Measure.quasiMeasurePreserving_snd.ae ((hw r).2.1 (-s).toNNReal)] with ω h1 h2 h3 _
      exact build_label_neg_eq_swap h1 h2 hs h3.2
    · exact Eventually.of_forall fun _ h => absurd h hs
  exact (Measure.ae_ae_comm (p := fun (ω : (areaFamily e).Ω × (areaFamily e).Ω) (s : ℝ) =>
    s < 0 → (build z e r ω).1.toFun s = (build z e r ω.swap).1.toFun (-s))
    measurableSet_build_neg_eq).2 h

/-- **The backward half has finite `L¹` norm on every `[-n, 0)`**, from the a.e. identification
with the swapped forward half and the reflection invariance of Lebesgue measure. -/
theorem lintegral_Ico_lineDensity_build_lt_top (Φ : CellField) (ζ : Fin 2 → ℝ)
    {ω : (areaFamily e).Ω × (areaFamily e).Ω}
    (hae : ∀ᵐ s ∂(volume : Measure ℝ),
      s < 0 → (build z e r ω).1.toFun s = (build z e r ω.swap).1.toFun (-s))
    (hfwd : ∀ n : ℕ, ∫⁻ u in Icc (0 : ℝ) n, ‖lineDensity Φ ζ (e, build z e r ω.swap) u‖ₑ < ∞)
    (n : ℕ) :
    ∫⁻ s in Ico (-(n : ℝ)) 0, ‖lineDensity Φ ζ (e, build z e r ω) s‖ₑ < ∞ := by
  set f : ℝ → ℝ≥0∞ := fun u => ‖lineDensity Φ ζ (e, build z e r ω.swap) u‖ₑ with hf
  have h1 : ∫⁻ s in Ico (-(n : ℝ)) 0, ‖lineDensity Φ ζ (e, build z e r ω) s‖ₑ =
      ∫⁻ s in Ico (-(n : ℝ)) 0, f (-s) := by
    refine setLIntegral_congr_fun_ae measurableSet_Ico ?_
    filter_upwards [hae] with s hs hmem
    show ‖labelBracket Φ ζ e ((build z e r ω).1.toFun s)‖ₑ =
      ‖labelBracket Φ ζ e ((build z e r ω.swap).1.toFun (-s))‖ₑ
    rw [hs hmem.2]
  have h2 : ∫⁻ s in Ico (-(n : ℝ)) 0, f (-s) = ∫⁻ u in Ioc (0 : ℝ) n, f u := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
      (Homeomorph.neg ℝ).measurableEmbedding f (Ioc (0 : ℝ) n)
    have hpre : (Neg.neg ⁻¹' Ioc (0 : ℝ) n) = Ico (-(n : ℝ)) 0 := by
      ext s
      simp only [mem_preimage, mem_Ioc, mem_Ico]
      constructor
      · rintro ⟨ha, hb⟩
        exact ⟨by linarith, by linarith⟩
      · rintro ⟨ha, hb⟩
        exact ⟨by linarith, by linarith⟩
    rw [hpre] at h
    exact h
  rw [h1, h2]
  exact lt_of_le_of_lt (lintegral_mono_set Ioc_subset_Icc_self) (hfwd n)

end Sample

/-- **Local integrability from the two halves.** -/
theorem locallyIntegrable_lineDensity_of_halves (Φ : CellField) (ζ : Fin 2 → ℝ) (ω : FlowSpace)
    (hpos : ∀ n : ℕ, ∫⁻ s in Icc (0 : ℝ) n, ‖lineDensity Φ ζ ω s‖ₑ < ∞)
    (hneg : ∀ n : ℕ, ∫⁻ s in Ico (-(n : ℝ)) 0, ‖lineDensity Φ ζ ω s‖ₑ < ∞) :
    LocallyIntegrable (lineDensity Φ ζ ω) volume := by
  have hω : Measurable (lineDensity Φ ζ ω) := by
    have h : Measurable ((fun q : FlowSpace × ℝ => lineDensity Φ ζ q.1 q.2) ∘ Prod.mk ω) :=
      (CellRootedFrameInvariance.measurable_lineDensity_uncurry Φ ζ).comp measurable_prodMk_left
    simpa only [Function.comp_def] using h
  refine (CellRootedFrameInvariance.locallyIntegrable_iff_lintegral_Icc hω).2 fun n => ?_
  have hsub : Icc (-(n : ℝ)) n ⊆ Ico (-(n : ℝ)) 0 ∪ Icc 0 n := by
    intro s hs
    by_cases h0 : s < 0
    · exact Or.inl ⟨hs.1, h0⟩
    · exact Or.inr ⟨not_lt.1 h0, hs.2⟩
  calc ∫⁻ s in Icc (-(n : ℝ)) n, ‖lineDensity Φ ζ ω s‖ₑ
      ≤ ∫⁻ s in Ico (-(n : ℝ)) 0 ∪ Icc 0 n, ‖lineDensity Φ ζ ω s‖ₑ := lintegral_mono_set hsub
    _ ≤ (∫⁻ s in Ico (-(n : ℝ)) 0, ‖lineDensity Φ ζ ω s‖ₑ) +
          ∫⁻ s in Icc (0 : ℝ) n, ‖lineDensity Φ ζ ω s‖ₑ := lintegral_union_le _ _ _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hneg n, hpos n⟩

/-! ### 2. The kernel level -/

variable {z : CellField} {G : Set Env} {hG : MeasurableSet G}
  {hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e} {hext : ExtensionGate z G}

/-- **`hloc` at the bridge kernel, PROVED** from MTP, (FE) and the harmonic coordinate: almost
surely the line density is locally integrable on the whole time axis. -/
theorem ae_locallyIntegrable_lineDensity_flowKernel (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) (Φ : CellField)
    (hΦ : IsHarmonicCoordinate ν Φ) (ζ : Fin 2 → ℝ) (hGc : ν Gᶜ = 0) :
    ∀ᵐ ω ∂(ν ⊗ₘ flowKernel z G hG hwalk hext), LocallyIntegrable (lineDensity Φ ζ ω) volume := by
  have hS := CellRootedFrameInvariance.measurableSet_locallyIntegrable_lineDensity Φ ζ
  refine Measure.ae_compProd_of_ae_ae hS ?_
  have hGae : ∀ᵐ e ∂ν, e ∈ G := ae_iff.2 hGc
  filter_upwards [hGae, ae_exists_rootAt_eq_some ν Φ hΦ,
    CanonicalOccupationWeld.ae_intervalIntegrable_bracketDensity ν hmt hFE Φ hΦ]
    with e he hr hint
  obtain ⟨root, hroot⟩ := hr
  have hlive : Live G e := ⟨he, by rw [rootLabel_of_some hroot]; exact root.property⟩
  have hSe : MeasurableSet {y : FlowCoding | ((e, y) : FlowSpace) ∈
      {ω : FlowSpace | LocallyIntegrable (lineDensity Φ ζ ω) volume}} :=
    measurable_prodMk_left hS
  rw [flowKernel_apply, flowFibre_of_live hlive]
  refine (ae_map_iff (measurable_build z e _).aemeasurable hSe).2 ?_
  have : Nontrivial (Vertex e.val) := nontrivial_vertex e
  have hwd := environmentWalkData_of_areaClockReachesLevelZeroIndices e (exhaustion e)
    (decode_connected e) (areaClockReaches_exhaustion e (hwalk e he))
  have hint1 : ∀ᵐ ω₁ ∂(areaFamily e).P (rootVertex hlive), ∀ (i j : Fin 2) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => stateBracketDensity (decode e) (Φ.at e)
        (exponentialAreaPath (decode e) (exhaustion e) (Real.toNNReal s) ω₁) i j)
        volume 0 (t : ℝ) :=
    hint (nontrivial_vertex e) (exhaustion e) (decode_connected e) hwd (rootVertex hlive)
  have hgood := ae_mem_goodSet hwalk hext hlive
  have hgood' : ∀ᵐ ω ∂(((areaFamily e).P (rootVertex hlive)).prod
      ((areaFamily e).P (rootVertex hlive))), ω.swap ∈ goodSet z e (rootVertex hlive) :=
    (Measure.measurePreserving_swap (μ := (areaFamily e).P (rootVertex hlive))
      (ν := (areaFamily e).P (rootVertex hlive))).quasiMeasurePreserving.ae hgood
  filter_upwards [hgood, hgood', Measure.quasiMeasurePreserving_fst.ae hint1,
    Measure.quasiMeasurePreserving_snd.ae hint1, ae_ae_build_neg_eq (hwalk e he) hgood]
    with ω h1 h2 h3 h4 h5
  have hpos' : ∀ n : ℕ, ∫⁻ u in Icc (0 : ℝ) n,
      ‖lineDensity Φ ζ (e, build z e (rootVertex hlive) ω.swap) u‖ₑ < ∞ :=
    lintegral_Icc_lineDensity_build_lt_top Φ ζ h2 h4
  exact locallyIntegrable_lineDensity_of_halves Φ ζ _
    (lintegral_Icc_lineDensity_build_lt_top Φ ζ h1 h3)
    (lintegral_Ico_lineDensity_build_lt_top Φ ζ h5 hpos')

end ReflectedGMS.FlowCodingLocalIntegrability
