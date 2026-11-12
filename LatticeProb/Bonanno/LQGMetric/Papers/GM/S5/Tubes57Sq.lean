/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Tubes57Sq at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes57SqMain

/-!
# GM Lemma 5.7 for square tubes (task P2-M2L3, decision D66)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, Lemma 5.7
(`lem-geo-event-local`, l. 2997–3018), for the tubes GM use: `V` the interior of a finite union of
grid squares (`IsSquareTube`), `V ⊆ B_{3r}(z)`. Same proof as `gm_L5_7loc`/`gm_L5_7`
(`Tubes57Final.lean`, `Tubes57.lean`), now without any separation hypothesis (condition (2)
in its robust reading `SepNear`, D69, is measurable); `gm_L5_7` gives the general statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint LocalEvent

/-- **GM Lemma 5.7 for square tubes** (D66): `F_r(z)` is a.s. determined by
`(h − h_{4r}(z))|_{B_{3r}(z)}` when `V ⊆ B_{3r}(z)` is a square tube -/
def L5_7Sq : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ},
  PairSetting γ D D' c → RatiosAre D D' cs Cs → 0 < cs → cs ≤ Cs →
  ∀ (c₁ η b ε r : ℝ) (z : ℂ) (V : Set ℂ) (s : ℝ) (X : Set ℂ), 0 < r → IsSquareTube V s X →
  V ⊆ Metric.ball z (3 * r) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P →
    AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) (4 * r) z)) (ballO z (3 * r)))
      (h ⁻¹' tubeEvent D D' cs Cs c₁ η b ε r z V)

/-- `F_r(z) ∈ σ(h|_{B_{3r}(z)})` a.s. for square tubes (GM l. 3004) -/
def L5_7locSq : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ},
  PairSetting γ D D' c → RatiosAre D D' cs Cs → 0 < cs → cs ≤ Cs →
  ∀ (c₁ η b ε r : ℝ) (z : ℂ) (V : Set ℂ) (s : ℝ) (X : Set ℂ), 0 < r → IsSquareTube V s X →
  V ⊆ Metric.ball z (3 * r) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P →
    AEEventIn P (fieldSigma h (ballO z (3 * r))) (h ⁻¹' tubeEvent D D' cs Cs c₁ η b ε r z V)

/-- **GM Lemma 5.7, `σ(h|_{B_{3r}(z)})` part** (l. 3004–3017), for square tubes -/
theorem gm_L5_7locSq (h38 : DFGPSLem3_8) : L5_7locSq := by
  intro γ D D' c cs Cs hPS hRat hcs hCs c₁ η b ε r z V s X hr hVsq hVB Ω _ P _ h hh
  have hV : IsOpen V := isOpen_of_isSquareTube hVsq
  obtain ⟨hγ0, hγ2, hD, hD'⟩ := id hPS
  set U := ballO z (3 * r) with hUdef
  have hUo : IsOpen (U : Set ℂ) := U.isOpen
  have hgp := Tight.isGFFPlusCont_of_wp hh
  obtain ⟨Φ, hΦ, hΦae⟩ := hD.locality P h hgp U
  obtain ⟨Φ', hΦ', hΦae'⟩ := hD'.locality P h hgp U
  have hzU : z ∈ (U : Set ℂ) := mem_ball_self (by positivity)
  have : Nonempty (U : Set ℂ) := ⟨⟨_, hzU⟩⟩
  set q : ℕ → ℂ := fun n => (TopologicalSpace.denseSeq (U : Set ℂ) n : ℂ) with hq
  have hqU : ∀ n, q n ∈ (U : Set ℂ) := fun n => (TopologicalSpace.denseSeq (U : Set ℂ) n).2
  have hqd : (U : Set ℂ) ⊆ closure (range q) := by
    intro x hx
    rw [_root_.mem_closure_iff]
    intro o ho hxo
    obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq (U : Set ℂ)).exists_mem_open
      (ho.preimage continuous_subtype_val) ⟨⟨x, hx⟩, hxo⟩
    exact ⟨q n, hn, n, rfl⟩
  let R : DistC → (ℕ × ℕ → ℝ≥0∞) × (ℕ × ℕ → ℝ≥0∞) := fun g =>
    (fun p => (D g).chainInf U (q p.1) (q p.2), fun p => (D' g).chainInf U (q p.1) (q p.2))
  let G : DistOn U → (ℕ × ℕ → ℝ≥0∞) × (ℕ × ℕ → ℝ≥0∞) := fun x =>
    (fun p => Φ x (q p.1) (q p.2), fun p => Φ' x (q p.1) (q p.2))
  have hR : Measurable R := by
    refine Measurable.prodMk (measurable_pi_iff.2 fun p => ?_)
      (measurable_pi_iff.2 fun p => ?_)
    · exact measurable_chainInf_comp hD.measurable measurable_const measurable_const _
    · exact measurable_chainInf_comp hD'.measurable measurable_const measurable_const _
  have hG : Measurable G := by
    refine Measurable.prodMk (measurable_pi_iff.2 fun p => ?_)
      (measurable_pi_iff.2 fun p => ?_)
    · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hΦ)
    · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hΦ')
  have hVm : Measurable[fieldSigma h U] fun ω => G (restrictTo U (h ω)) :=
    hG.comp (Measurable.of_comap_le le_rfl)
  have hlen := hD.length P h hgp
  have hlen' := hD'.length P h hgp
  have hVR : ∀ᵐ ω ∂P, G (restrictTo U (h ω)) = R (h ω) := by
    filter_upwards [hΦae, hΦae', hlen, hlen'] with ω h1 h2 h3 h4
    refine Prod.ext (funext fun p => ?_) (funext fun p => ?_)
    · show Φ _ (q p.1) (q p.2) = (D (h ω)).chainInf U (q p.1) (q p.2)
      rw [← h1 _ (hqU _) _ (hqU _), (D (h ω)).internal_eq_chainInf h3 hUo]
    · show Φ' _ (q p.1) (q p.2) = (D' (h ω)).chainInf U (q p.1) (q p.2)
      rw [← h2 _ (hqU _) _ (hqU _), (D' (h ω)).internal_eq_chainInf h4 hUo]
  -- the Borel set carrying the law
  set Wr : Set DistC := {g | ∀ i j, cs * (D g).1 (qd i, qd j) ≤ (D' g).1 (qd i, qd j) ∧
    (D' g).1 (qd i, qd j) ≤ Cs * (D g).1 (qd i, qd j)} with hWr
  have hWrm : MeasurableSet Wr := by
    simp only [hWr, ofPred_forall, ofPred_and]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    have m1 : Measurable fun g : DistC => (D g).1 (qd i, qd j) :=
      (measurable_apply _).comp hD.measurable
    have m2 : Measurable fun g : DistC => (D' g).1 (qd i, qd j) :=
      (measurable_apply _).comp hD'.measurable
    exact (measurableSet_le (m1.const_mul _) m2).inter (measurableSet_le m2 (m1.const_mul _))
  set W : Set DistC := (D ⁻¹' lenSet ∩ D' ⁻¹' lenSet) ∩ Wr
  have hW : MeasurableSet W :=
    ((measurableSet_lenSet.preimage hD.measurable).inter
      (measurableSet_lenSet.preimage hD'.measurable)).inter hWrm
  have hYW : ∀ᵐ ω ∂P, h ω ∈ W := by
    filter_upwards [ae_mem_lenSet h38 hγ0 hγ2 hD P h hh,
      ae_mem_lenSet h38 hγ0 hγ2 hD' P h hh, hRat P h hh] with ω h1 h2 h3
    exact ⟨⟨h1, h2⟩, fun i j => ratio_of_ratios hcs hCs h3.1 h3.2 _ _⟩
  set B : Set DistC := tubeEvent D D' cs Cs c₁ η b ε r z V
  have hB : NullMeasurableSet B (P.map h) := by
    refine ((uMeasurableSet_tubeEventB_of V hD.measurable hD'.measurable cs Cs c₁ η b ε r z
      hV).nullMeasurableSet (P.map h)).congr ?_
    filter_upwards [(ae_map_iff hh.measurable.aemeasurable hW).2 hYW] with g hg
    exact propext (mem_tubeEvent_iff_B hV hg.1.2).symm
  have hsat : ∀ g₁ ∈ W, ∀ g₂ ∈ W, R g₁ = R g₂ → g₁ ∈ B → g₂ ∈ B := by
    rintro g₁ ⟨⟨h1, h1'⟩, w1⟩ g₂ ⟨⟨h2, h2'⟩, w2⟩ he hB1
    have l1 := isLength_of_mem_lenSet h1
    have l1' := isLength_of_mem_lenSet h1'
    have l2 := isLength_of_mem_lenSet h2
    have l2' := isLength_of_mem_lenSet h2'
    have e1 : (D g₁).internal U = (D g₂).internal U := by
      refine internal_eq_of_dense l1 l2 hUo hqU hqd fun i j => ?_
      rw [(D g₁).internal_eq_chainInf l1 hUo, (D g₂).internal_eq_chainInf l2 hUo]
      exact congrFun (congrArg Prod.fst he) (i, j)
    have e2 : (D' g₁).internal U = (D' g₂).internal U := by
      refine internal_eq_of_dense l1' l2' hUo hqU hqd fun i j => ?_
      rw [(D' g₁).internal_eq_chainInf l1' hUo, (D' g₂).internal_eq_chainInf l2' hUo]
      exact congrFun (congrArg Prod.snd he) (i, j)
    exact tubeEvent_saturated hr hcs hCs hVB h1 h1' h2 h2' (ratio_of_dense w1)
      (ratio_of_dense w2) e1 e2 hB1
  exact LocalEvent.aeEventIn_of_saturated hh.measurable hR hVm hVR hW hB hYW hsat

end LQGMetric.GM
