/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cO.Basic at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OPositiveRadii
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.BundleExcursions
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.ExcursionMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.LemmaA1A2
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112N3
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicScale

/-!
# Basic tools for the recentring step of [18] Lemma 4.9

* `L43O.resDist`: restriction of a distribution on `U₂` to an open `U₁ ⊆ U₂`, with
  `restrictTo_eq_resDist` and measurability;
* `L43O.rotateField_zero`: `rotateField 0 = id`;
* `L43O.excursionData V c`: the rational-point excursion coordinate of [18] Lemma 4.3's local data
  (`= (GMS4c.localConfiguration V μ h c).2`), its measurability and continuity in time;
* `L43O.eq_of_agreeRat`, `L43O.measurableSet_agreeRat`: families of continuous curves indexed by `ℚ × ℚ` agree
  iff they agree at rational times; the latter condition is measurable;
* `L43O.map_prod_eq_of_forall_ae_eq`: a scalar together with a circle-average process — coordinatewise almost
  sure equality of the processes gives equality of the joint laws.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT

namespace MatedCRTHarmonic.L43O

attribute [local instance] Classical.propDecidable

/-! ## Restriction between open sets -/

/-- Restriction `𝒟'(U₂) → 𝒟'(U₁)` (composition with the inclusion of test functions). -/
def resDist (U₁ U₂ : TopologicalSpace.Opens ℂ) (T : DistOn U₂) : DistOn U₁ :=
  T.comp (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U₁) (Ω₂ := U₂))

theorem measurable_resDist (U₁ U₂ : TopologicalSpace.Opens ℂ) : Measurable (resDist U₁ U₂) :=
  measurable_distOn_iff.2 fun _ => measurable_distOn_apply _

theorem restrictTo_eq_resDist {U₁ U₂ : TopologicalSpace.Opens ℂ} (h : U₁ ≤ U₂) (T : DistC) :
    restrictTo U₁ T = resDist U₁ U₂ (restrictTo U₂ T) := by
  refine DFunLike.ext _ _ fun φ => ?_
  change T (TestFunction.monoCLM ℝ φ) = T (TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ φ))
  congr 1
  ext x
  simp [TestFunction.monoCLM_apply, h]

/-! ## Rotation by angle zero -/

theorem rotateField_zero (h : DistC) : MoTPort.rotateField 0 h = h := by
  refine DFunLike.ext _ _ fun φ => ?_
  rw [MoTPort.rotateField_apply]
  congr 1
  ext x
  simp [MoTPort.FieldOps.testPullCLE_apply]
  rfl

/-! ## The excursion coordinate -/

/-- The rational-point excursion coordinate of the local data of [18] Lemma 4.3 (zero off `V`). -/
def excursionData (V : TopologicalSpace.Opens ℂ) (c : C(ℝ, ℂ)) : ℚ × ℚ → ℝ → ℂ :=
  fun q => if GMS4c.ratPt q ∈ V then excursionSegment c V (GMS4c.ratPt q) else 0

theorem continuous_excursionSegment (c : C(ℝ, ℂ)) (V : Set ℂ) (w : ℂ) :
    Continuous (excursionSegment c V w) := by
  unfold excursionSegment
  fun_prop

theorem continuous_excursionData (V : TopologicalSpace.Opens ℂ) (c : C(ℝ, ℂ)) (q : ℚ × ℚ) :
    Continuous (excursionData V c q) := by
  unfold excursionData
  split_ifs
  · exact continuous_excursionSegment c V _
  · exact continuous_const

theorem measurable_excursionData (V : TopologicalSpace.Opens ℂ)
    (hVc : ((V : Set ℂ)ᶜ).Nonempty) : Measurable (excursionData V) := by
  refine measurable_pi_iff.mpr fun q => ?_
  by_cases hq : GMS4c.ratPt q ∈ V
  · simpa only [excursionData, hq, ↓reduceIte] using
      GMS4c.measurable_excursionSegment V (GMS4c.ratPt q) hVc
  · simp only [excursionData, hq, ↓reduceIte]
    exact measurable_const

/-! ## Agreement at rational times -/

/-- Agreement of two `ℚ × ℚ`-indexed families of curves at every rational time. -/
def AgreeRat (f g : ℚ × ℚ → ℝ → ℂ) : Prop := ∀ q : ℚ × ℚ, ∀ t : ℚ, f q t = g q t

theorem eq_of_agreeRat {f g : ℚ × ℚ → ℝ → ℂ} (hf : ∀ q, Continuous (f q))
    (hg : ∀ q, Continuous (g q)) (h : AgreeRat f g) : f = g := by
  funext q
  have hd : DenseRange (fun t : ℚ => (t : ℝ)) := Rat.isDenseEmbedding_coe_real.dense
  exact hd.equalizer (hf q) (hg q) (funext fun t => h q t)

theorem measurableSet_agreeRat {α : Type*} [MeasurableSpace α] {f g : α → ℚ × ℚ → ℝ → ℂ}
    (hf : Measurable f) (hg : Measurable g) : MeasurableSet {x | AgreeRat (f x) (g x)} := by
  have : {x | AgreeRat (f x) (g x)} = ⋂ q : ℚ × ℚ, ⋂ t : ℚ, {x | f x q (t : ℝ) = g x q (t : ℝ)} := by
    ext x
    simp [AgreeRat]
  rw [this]
  refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun t => ?_
  exact measurableSet_eq_fun ((measurable_pi_apply _).comp ((measurable_pi_apply q).comp hf))
    ((measurable_pi_apply _).comp ((measurable_pi_apply q).comp hg))

/-! ## Joint laws from coordinatewise equality -/

/-- Encode a scalar and a circle-average process as one real process indexed by `Option (ℝ × ℂ)`. -/
def encProc (x : ℝ × (ℝ → ℂ → ℝ)) : Option (ℝ × ℂ) → ℝ
  | none => x.1
  | some p => x.2 p.1 p.2

/-- Decode. -/
def decProc (f : Option (ℝ × ℂ) → ℝ) : ℝ × (ℝ → ℂ → ℝ) :=
  (f none, fun ρ w => f (some (ρ, w)))

theorem measurable_encProc : Measurable encProc := by
  refine measurable_pi_iff.mpr fun o => ?_
  cases o with
  | none => exact measurable_fst
  | some p =>
    exact (measurable_pi_apply p.2).comp ((measurable_pi_apply p.1).comp measurable_snd)

theorem measurable_decProc : Measurable decProc :=
  (measurable_pi_apply none).prodMk
    (measurable_pi_iff.mpr fun _ => measurable_pi_iff.mpr fun _ => measurable_pi_apply _)

/-- If two circle-average processes agree coordinatewise almost surely, then each, paired with the same
scalar `a`, has the same joint law. -/
theorem map_prod_eq_of_forall_ae_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {a : Ω → ℝ} {K M : Ω → ℝ → ℂ → ℝ} (ha : AEMeasurable a P)
    (hK : AEMeasurable K P) (hM : AEMeasurable M P)
    (hKM : ∀ ρ w, (fun ω => K ω ρ w) =ᵐ[P] fun ω => M ω ρ w) :
    P.map (fun ω => (a ω, K ω)) = P.map (fun ω => (a ω, M ω)) := by
  have hK' : AEMeasurable (fun ω => encProc (a ω, K ω)) P :=
    measurable_encProc.comp_aemeasurable (ha.prodMk hK)
  have hM' : AEMeasurable (fun ω => encProc (a ω, M ω)) P :=
    measurable_encProc.comp_aemeasurable (ha.prodMk hM)
  have hpi : P.map (fun ω => encProc (a ω, K ω)) = P.map (fun ω => encProc (a ω, M ω)) := by
    refine IGLaw.map_eq_of_forall_ae_eq_pi hK' hM' fun o => ?_
    cases o with
    | none => exact Eventually.of_forall fun ω => rfl
    | some p => exact hKM p.1 p.2
  calc P.map (fun ω => (a ω, K ω))
      = (P.map fun ω => encProc (a ω, K ω)).map decProc := by
        rw [AEMeasurable.map_map_of_aemeasurable measurable_decProc.aemeasurable hK']
        rfl
    _ = (P.map fun ω => encProc (a ω, M ω)).map decProc := by rw [hpi]
    _ = P.map (fun ω => (a ω, M ω)) := by
        rw [AEMeasurable.map_map_of_aemeasurable measurable_decProc.aemeasurable hM']
        rfl

/-- Encode a pair of scalars and a circle-average process as one real process. -/
def encProc2 (x : (ℝ × ℝ) × (ℝ → ℂ → ℝ)) : Option (Option (ℝ × ℂ)) → ℝ
  | none => x.1.1
  | some none => x.1.2
  | some (some p) => x.2 p.1 p.2

/-- Decode. -/
def decProc2 (f : Option (Option (ℝ × ℂ)) → ℝ) : (ℝ × ℝ) × (ℝ → ℂ → ℝ) :=
  ((f none, f (some none)), fun ρ w => f (some (some (ρ, w))))

theorem measurable_encProc2 : Measurable encProc2 := by
  refine measurable_pi_iff.mpr fun o => ?_
  rcases o with _ | _ | p
  · exact measurable_fst.comp measurable_fst
  · exact measurable_snd.comp measurable_fst
  · exact (measurable_pi_apply p.2).comp ((measurable_pi_apply p.1).comp measurable_snd)

theorem measurable_decProc2 : Measurable decProc2 :=
  ((measurable_pi_apply none).prodMk (measurable_pi_apply (some none))).prodMk
    (measurable_pi_iff.mpr fun _ => measurable_pi_iff.mpr fun _ => measurable_pi_apply _)

/-- The two-scalar version of `map_prod_eq_of_forall_ae_eq`. -/
theorem map_prod2_eq_of_forall_ae_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {a : Ω → ℝ × ℝ} {K M : Ω → ℝ → ℂ → ℝ} (ha : AEMeasurable a P)
    (hK : AEMeasurable K P) (hM : AEMeasurable M P)
    (hKM : ∀ ρ w, (fun ω => K ω ρ w) =ᵐ[P] fun ω => M ω ρ w) :
    P.map (fun ω => (a ω, K ω)) = P.map (fun ω => (a ω, M ω)) := by
  have hK' : AEMeasurable (fun ω => encProc2 (a ω, K ω)) P :=
    measurable_encProc2.comp_aemeasurable (ha.prodMk hK)
  have hM' : AEMeasurable (fun ω => encProc2 (a ω, M ω)) P :=
    measurable_encProc2.comp_aemeasurable (ha.prodMk hM)
  have hpi : P.map (fun ω => encProc2 (a ω, K ω)) = P.map (fun ω => encProc2 (a ω, M ω)) := by
    refine IGLaw.map_eq_of_forall_ae_eq_pi hK' hM' fun o => ?_
    rcases o with _ | _ | p
    · exact Eventually.of_forall fun ω => rfl
    · exact Eventually.of_forall fun ω => rfl
    · exact hKM p.1 p.2
  calc P.map (fun ω => (a ω, K ω))
      = (P.map fun ω => encProc2 (a ω, K ω)).map decProc2 := by
        rw [AEMeasurable.map_map_of_aemeasurable measurable_decProc2.aemeasurable hK']
        rfl
    _ = (P.map fun ω => encProc2 (a ω, M ω)).map decProc2 := by rw [hpi]
    _ = P.map (fun ω => (a ω, M ω)) := by
        rw [AEMeasurable.map_map_of_aemeasurable measurable_decProc2.aemeasurable hM']
        rfl

/-! ## Independence bookkeeping -/

/-- If `(A, B) ⟂ C` and `A ⟂ B`, then `A ⟂ (B, C)`. -/
theorem indepFun_prod_of_indep {Ω α β δ : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace δ] {P : Measure Ω} [IsProbabilityMeasure P]
    {A : Ω → α} {B : Ω → β} {C : Ω → δ} (hA : AEMeasurable A P) (hB : AEMeasurable B P)
    (hC : AEMeasurable C P) (hABC : IndepFun (fun ω => (A ω, B ω)) C P) (hAB : IndepFun A B P) :
    IndepFun A (fun ω => (B ω, C ω)) P := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hA (hB.prodMk hC)]
  have h1 := (indepFun_iff_map_prod_eq_prod_map_map (hA.prodMk hB) hC).1 hABC
  have h2 := (indepFun_iff_map_prod_eq_prod_map_map hA hB).1 hAB
  have hBC : IndepFun B C P := hABC.comp measurable_snd measurable_id
  have h3 := (indepFun_iff_map_prod_eq_prod_map_map hB hC).1 hBC
  -- reassociate `(A, (B, C))` from `((A, B), C)`
  have he : Measurable (MeasurableEquiv.prodAssoc : (α × β) × δ ≃ᵐ α × (β × δ)) :=
    MeasurableEquiv.measurable _
  calc P.map (fun ω => (A ω, (B ω, C ω)))
      = (P.map fun ω => ((A ω, B ω), C ω)).map MeasurableEquiv.prodAssoc := by
        rw [AEMeasurable.map_map_of_aemeasurable he.aemeasurable ((hA.prodMk hB).prodMk hC)]
        rfl
    _ = (((P.map A).prod (P.map B)).prod (P.map C)).map MeasurableEquiv.prodAssoc := by
        rw [h1, h2]
    _ = (P.map A).prod ((P.map B).prod (P.map C)) := Measure.prodAssoc_prod
    _ = (P.map A).prod (P.map fun ω => (B ω, C ω)) := by rw [h3]

end MatedCRTHarmonic.L43O
