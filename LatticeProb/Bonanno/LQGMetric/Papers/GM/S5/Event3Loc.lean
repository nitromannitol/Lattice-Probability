/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Event3Loc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Event3Inv
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Event3Sat2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Event2Fin
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes57Main
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc

/-!
# GM Lemma 5.9: reduction to the measurability of `E_r` (task P2-M2M4, D83 P4b)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, Lemma 5.9
(`lem-geo-event-msrble`, l. 3293–3302).

* `gm_L5_9_of_loc`: GM l. 3297, "By Axiom III, the occurrence of `E_r` is unaffected by adding a
  real number to `h`, so we only need to show `E_r ∈ σ(h|_{𝔸_{r/4,4r}(0)})`" (`L5_9loc`, for every
  whole-plane GFF; applied to `h − h_{5r}(0)`, with `ae_eventE_addConst_iff`).
* `gm_L5_9loc_of_meas`: GM l. 3298–3301 (locality, "by inspection"): `L5_9loc` from the
  measurability statement `L5_9meas` (`E_r` is null-measurable for the law of the field), by the
  D51 route of `gm_L5_7loc` (`LocalEvent.aeEventIn_of_saturated`): the internal metrics of
  `𝔸 = 𝔸_{r/4,4r}(0)` at dense pairs (Axiom II), `𝔠_r e^{ξ h_r(0)}` (`∂B_r(0) ⊂ 𝔸`,
  `measurable_circleAvg_fieldSigma`) and `(h, φ)_∇`, `φ ∈ 𝓖_r` (supports in `𝔸_{r/4,3r}(0)`,
  `bumpFam_tsupport_m2m2`) are `σ(h|_𝔸)`-measurable and determine `E_r` on the a.s. set of fields
  with boundedly compact length metrics and `c_* D ≤ D̃ ≤ C_* D` (`eventE_saturated`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint LocalEvent

/-- `E_r ∈ σ(h|_{𝔸_{r/4,4r}(0)})` a.s., for every whole-plane GFF (GM l. 3297, "we only need to
show") -/
def L5_9loc : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ},
  PairSetting γ D D' c → RatiosAre D D' cs Cs → 0 < cs → cs ≤ Cs →
  ∀ (S : EData), S.ξ = xiGamma γ → S.c = c → S.cs = cs → S.Cs = Cs → S.Ranges →
  ∀ (r : ℝ), 0 < r → ∀ (U : ℂ → ℂ → Set ℂ) (fb gb : Set ℂ → TestC),
    IsTubeFam S U r → IsBumpChoice S U fb gb r →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P →
    AEEventIn P (fieldSigma h (annulus 0 (r / 4) (4 * r))) (h ⁻¹' eventE D D' S U fb gb r)

/-- **GM Lemma 5.9** from `L5_9loc` (GM l. 3297: Weyl scaling) -/
theorem gm_L5_9_of_loc (H : L5_9loc) : L5_9 := by
  intro γ D D' c cs Cs hPS hR hcs hCs S hξ hc hscs hsCs hS r hr U fb gb hU hB Ω _ P _ h hh
  have hm : Measurable fun ω => -circleAvg (h ω) (5 * r) 0 :=
    ((measurable_circleAvg_left (5 * r) 0).comp hh.measurable).neg
  have hX : IsWholePlaneGFF (fun ω => addConst (h ω) (-circleAvg (h ω) (5 * r) 0)) P :=
    hh.addConst hm
  obtain ⟨F, hF, hEF⟩ := H hPS hR hcs hCs S hξ hc hscs hsCs hS r hr U fb gb hU hB P _ hX
  refine ⟨F, hF, EventuallyEq.trans ?_ hEF⟩
  filter_upwards [ae_eventE_addConst_iff hPS hξ U fb gb hr P h hh] with ω hω
  exact propext (hω _).symm

/-- `E_r` is null-measurable for the law of the whole-plane GFF (GM l. 3298–3301, "by
inspection"); the remaining part of GM Lemma 5.9 -/
def L5_9meas : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ},
  PairSetting γ D D' c → RatiosAre D D' cs Cs → 0 < cs → cs ≤ Cs →
  ∀ (S : EData), S.ξ = xiGamma γ → S.c = c → S.cs = cs → S.Cs = Cs → S.Ranges →
  ∀ (r : ℝ), 0 < r → ∀ (U : ℂ → ℂ → Set ℂ) (fb gb : Set ℂ → TestC),
    IsTubeFam S U r → IsBumpChoice S U fb gb r →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → NullMeasurableSet (eventE D D' S U fb gb r) (P.map h)

/-- `tsupport (cmTest φ) ⊆ tsupport φ` -/
lemma tsupport_cmTest_subset_m2m4 (φ : TestC) :
    tsupport (cmTest φ : ℂ → ℝ) ⊆ tsupport (φ : ℂ → ℝ) :=
  closure_minimal (fun x hx => by_contra fun h' => hx (by
    rw [cmTest_apply, QuantumZipper.K3.laplacian_eq_zero_of_notMem_tsupport h', mul_zero]))
    (isClosed_tsupport _)

/-- **GM Lemma 5.9, `σ(h|_{𝔸_{r/4,4r}(0)})` part** (l. 3298–3301), from the measurability of `E_r` -/
theorem gm_L5_9loc_of_meas (h38 : DFGPSLem3_8) (hM : L5_9meas) : L5_9loc := by
  intro γ D D' c cs Cs hPS hRat hcs hCs S hξ hc hscs hsCs hS r hr U fb gb hU hBc Ω _ P _ h hh
  obtain ⟨hγ0, hγ2, hD, hD'⟩ := id hPS
  set A := annulus 0 (r / 4) (4 * r) with hAdef
  have hAo : IsOpen (A : Set ℂ) := A.isOpen
  have hgp := Tight.isGFFPlusCont_of_wp hh
  obtain ⟨Φ, hΦ, hΦae⟩ := hD.locality P h hgp A
  obtain ⟨Φ', hΦ', hΦae'⟩ := hD'.locality P h hgp A
  have hrA : ((r : ℝ) : ℂ) ∈ (A : Set ℂ) := by
    show r / 4 < ‖(r : ℂ) - 0‖ ∧ ‖(r : ℂ) - 0‖ < 4 * r
    rw [sub_zero, Complex.norm_real, Real.norm_of_nonneg hr.le]
    constructor <;> linarith
  have : Nonempty (A : Set ℂ) := ⟨⟨_, hrA⟩⟩
  set q : ℕ → ℂ := fun n => (TopologicalSpace.denseSeq (A : Set ℂ) n : ℂ) with hq
  have hqU : ∀ n, q n ∈ (A : Set ℂ) := fun n => (TopologicalSpace.denseSeq (A : Set ℂ) n).2
  have hqd : (A : Set ℂ) ⊆ closure (range q) := by
    intro x hx
    rw [_root_.mem_closure_iff]
    intro o ho hxo
    obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq (A : Set ℂ)).exists_mem_open
      (ho.preimage continuous_subtype_val) ⟨⟨x, hx⟩, hxo⟩
    exact ⟨q n, hn, n, rfl⟩
  -- an enumeration of the finite family `𝓖_r`
  obtain ⟨f, hf⟩ : ∃ f : ℕ → TestC, bumpFam S U fb gb r = range f :=
    (bumpFam_finite_m2m2 hS hr hU fb gb).countable.exists_eq_range ⟨0, Or.inr rfl⟩
  have hfA : ∀ n, tsupport (cmTest (f n) : ℂ → ℝ) ⊆ (A : Set ℂ) := fun n =>
    (tsupport_cmTest_subset_m2m4 _).trans ((bumpFam_tsupport_m2m2 hS hr hU hBc (f n)
      (hf ▸ mem_range_self n : f n ∈ bumpFam S U fb gb r)).trans fun w hw => ⟨hw.1, by linarith [hw.2]⟩)
  let R : DistC → ((ℕ × ℕ → ℝ≥0∞) × (ℕ × ℕ → ℝ≥0∞)) × (ℝ × (ℕ → ℝ)) := fun g =>
    ((fun p => (D g).chainInf A (q p.1) (q p.2), fun p => (D' g).chainInf A (q p.1) (q p.2)),
      (scaleFac S.ξ S.c g r 0, fun n => dirInner g (f n)))
  let V : Ω → ((ℕ × ℕ → ℝ≥0∞) × (ℕ × ℕ → ℝ≥0∞)) × (ℝ × (ℕ → ℝ)) := fun ω =>
    ((fun p => Φ (restrictTo A (h ω)) (q p.1) (q p.2),
      fun p => Φ' (restrictTo A (h ω)) (q p.1) (q p.2)),
      (scaleFac S.ξ S.c (h ω) r 0, fun n => dirInner (h ω) (f n)))
  have hR : Measurable R := by
    refine Measurable.prodMk (Measurable.prodMk (measurable_pi_iff.2 fun p => ?_)
      (measurable_pi_iff.2 fun p => ?_)) (Measurable.prodMk ?_ (measurable_pi_iff.2 fun n => ?_))
    · exact measurable_chainInf_comp hD.measurable measurable_const measurable_const _
    · exact measurable_chainInf_comp hD'.measurable measurable_const measurable_const _
    · exact measurable_const.mul ((measurable_circleAvg_left r 0).const_mul _).exp
    · exact measurable_evalDist _
  have hcA : Measurable[fieldSigma h A] fun ω => circleAvg (h ω) r 0 := by
    refine fun s hs => fieldSigma_mono h (V := nbhdO (r / 2) (sphere 0 |r|)) (W := A) ?_ _
      (measurable_circleAvg_fieldSigma h r 0 (by linarith : (0 : ℝ) < r / 2) hs)
    intro w hw
    obtain ⟨p, hp, hwp⟩ := mem_thickening_iff.1 hw
    rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hp
    rw [dist_eq_norm] at hwp
    have h1 := norm_sub_norm_le w p
    have h2 := norm_sub_norm_le p w
    rw [norm_sub_rev] at h2
    show r / 4 < ‖w - 0‖ ∧ ‖w - 0‖ < 4 * r
    rw [sub_zero]; constructor <;> linarith
  have hVm : Measurable[fieldSigma h A] V := by
    letI : MeasurableSpace Ω := fieldSigma h A
    have hG : Measurable fun ω => restrictTo A (h ω) := Measurable.of_comap_le le_rfl
    refine Measurable.prodMk (Measurable.prodMk (measurable_pi_iff.2 fun p => ?_)
      (measurable_pi_iff.2 fun p => ?_)) (Measurable.prodMk ?_ (measurable_pi_iff.2 fun n => ?_))
    · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp (hΦ.comp hG))
    · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp (hΦ'.comp hG))
    · exact measurable_const.mul (hcA.const_mul _).exp
    · exact measurable_pair_fieldSigma h _ (hfA n)
  have hlen := hD.length P h hgp
  have hlen' := hD'.length P h hgp
  have hVR : ∀ᵐ ω ∂P, V ω = R (h ω) := by
    filter_upwards [hΦae, hΦae', hlen, hlen'] with ω h1 h2 h3 h4
    refine Prod.ext (Prod.ext (funext fun p => ?_) (funext fun p => ?_)) rfl
    · show Φ _ (q p.1) (q p.2) = (D (h ω)).chainInf A (q p.1) (q p.2)
      rw [← h1 _ (hqU _) _ (hqU _), (D (h ω)).internal_eq_chainInf h3 hAo]
    · show Φ' _ (q p.1) (q p.2) = (D' (h ω)).chainInf A (q p.1) (q p.2)
      rw [← h2 _ (hqU _) _ (hqU _), (D' (h ω)).internal_eq_chainInf h4 hAo]
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
  have hB := hM hPS hRat hcs hCs S hξ hc hscs hsCs hS r hr U fb gb hU hBc P h hh
  have hsat : ∀ g₁ ∈ W, ∀ g₂ ∈ W, R g₁ = R g₂ →
      g₁ ∈ eventE D D' S U fb gb r → g₂ ∈ eventE D D' S U fb gb r := by
    rintro g₁ ⟨⟨h1, h1'⟩, w1⟩ g₂ ⟨⟨h2, h2'⟩, w2⟩ he hB1
    have l1 := isLength_of_mem_lenSet h1
    have l1' := isLength_of_mem_lenSet h1'
    have l2 := isLength_of_mem_lenSet h2
    have l2' := isLength_of_mem_lenSet h2'
    have e1 : (D g₁).internal A = (D g₂).internal A := by
      refine internal_eq_of_dense l1 l2 hAo hqU hqd fun i j => ?_
      rw [(D g₁).internal_eq_chainInf l1 hAo, (D g₂).internal_eq_chainInf l2 hAo]
      exact congrFun (congrArg Prod.fst (congrArg Prod.fst he)) (i, j)
    have e2 : (D' g₁).internal A = (D' g₂).internal A := by
      refine internal_eq_of_dense l1' l2' hAo hqU hqd fun i j => ?_
      rw [(D' g₁).internal_eq_chainInf l1' hAo, (D' g₂).internal_eq_chainInf l2' hAo]
      exact congrFun (congrArg Prod.snd (congrArg Prod.fst he)) (i, j)
    have e3 : scaleFac S.ξ S.c g₂ r 0 = scaleFac S.ξ S.c g₁ r 0 :=
      (congrArg Prod.fst (congrArg Prod.snd he)).symm
    have e4 : ∀ φ ∈ bumpFam S U fb gb r, dirInner g₂ φ = dirInner g₁ φ := by
      intro φ hφ
      rw [hf] at hφ
      obtain ⟨n, rfl⟩ := hφ
      exact (congrFun (congrArg Prod.snd (congrArg Prod.snd he)) n).symm
    exact eventE_saturated hr hS (hscs ▸ hcs) (hscs ▸ hsCs ▸ hCs) hU h1 h1' h2 h2'
      (hscs ▸ hsCs ▸ ratio_of_dense w1) (hscs ▸ hsCs ▸ ratio_of_dense w2) e1 e2 e3 e4 hB1
  exact LocalEvent.aeEventIn_of_saturated hh.measurable hR hVm hVR hW hB hYW hsat

/-- **GM Lemma 5.9** from the measurability of `E_r` (`L5_9meas`) and `DFGPSLem3_8` (GM.S1.1) -/
theorem gm_L5_9_of_meas (h38 : DFGPSLem3_8) (hM : L5_9meas) : L5_9 :=
  gm_L5_9_of_loc (gm_L5_9loc_of_meas h38 hM)

end LQGMetric.GM
