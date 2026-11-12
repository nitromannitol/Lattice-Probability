/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.GoodAnnulusMeas4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas4a
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEventLength

/-!
# GM Lemma 3.7: the measurability part `L3_7meas` (task P2-LOCMEAS, decision D51)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`, proof
of Lemma 3.7, l. 1345–1360: `𝖤_r(z)` is determined by the internal metrics of
`U = 𝔸_{r/2,2r}(z)` (`mem_goodAnnulus_iff_internal`), hence by `h|_U` (Axiom II).

The "hence" is `LocalEvent.aeEventIn_of_saturated` applied to
* `Y = h`, `W = {g | D_g, D̃_g ∈ lenSet}` (boundedly compact length metrics; a.s. by GM.S1.1,
  `gm_S1_1_bcpt`, which needs `DFGPSLem3_8`, D50);
* `R(g)` = the Borel versions (`chainInf`) of `D_g(·,·;U)`, `D̃_g(·,·;U)` at the pairs of a dense
  sequence of `U`, and `V = ` the same values computed from `h|_U` by Axiom II;
* `B = {g | goodAnnulusI (D_g(·,·;U)) (D̃_g(·,·;U)) …}`: on `W` it equals
  `gaCompareB ∩ gaLongB ∩ gaAround` (universally measurable, D48 and `GoodAnnulusMeas4a`), and it
  is determined by `R` on `W` because internal metrics of length metrics are continuous on `U × U`
  (LM Lemma 1.1, `ContMetric.continuousOn_internal`) and `∞` off `U`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint MetricGeometry

/-- the internal metric is `∞` from a point outside the domain -/
lemma internal_eq_top_of_notMem (d : ContMetric) {V : Set ℂ} {x : ℂ} (hx : x ∉ V) (y : ℂ) :
    d.internal V x y = ⊤ := by
  unfold ContMetric.internal internalEDist
  have : IsEmpty {γ : Path (d.pt x) (d.pt y) // ∀ t, γ t ∈ d.pt '' V} :=
    ⟨fun γ => hx (d.mem_image_pt.1 (by simpa only [Path.source] using γ.2 0))⟩
  exact iInf_of_empty _

/-- internal metrics of length metrics agreeing on the pairs of a dense sequence of `V` agree -/
lemma internal_eq_of_dense {d₁ d₂ : ContMetric} (h₁ : d₁.IsLength) (h₂ : d₂.IsLength)
    {V : Set ℂ} (hV : IsOpen V) {q : ℕ → ℂ} (hqV : ∀ n, q n ∈ V)
    (hq : V ⊆ closure (range q))
    (he : ∀ i j, d₁.internal V (q i) (q j) = d₂.internal V (q i) (q j)) :
    d₁.internal V = d₂.internal V := by
  funext x y
  by_cases hx : x ∈ V
  · by_cases hy : y ∈ V
    · have hE : EqOn (fun p : ℂ × ℂ => d₁.internal V p.1 p.2)
          (fun p : ℂ × ℂ => d₂.internal V p.1 p.2) (V ×ˢ V) := by
        refine EqOn.of_subset_closure (s := range (Prod.map q q)) ?_
          (d₁.continuousOn_internal h₁ hV) (d₂.continuousOn_internal h₂ hV) ?_ ?_
        · rintro _ ⟨⟨i, j⟩, rfl⟩; exact he i j
        · rintro _ ⟨⟨i, j⟩, rfl⟩; exact ⟨hqV i, hqV j⟩
        · rw [range_prodMap, closure_prod_eq]
          exact prod_mono hq hq
      exact hE (mk_mem_prod hx hy)
    · have c : ∀ d : ContMetric, d.internal V x y = d.internal V y x := fun d =>
        internalEDist_comm _ _ _
      rw [c d₁, c d₂, internal_eq_top_of_notMem d₁ hy, internal_eq_top_of_notMem d₂ hy]
  · rw [internal_eq_top_of_notMem d₁ hx, internal_eq_top_of_notMem d₂ hx]

/-- a.s. the metric is a boundedly compact length metric (GM.S1.1 via `DFGPSLem3_8`) -/
lemma ae_mem_lenSet (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) : ∀ᵐ ω ∂P, D (h ω) ∈ LocalEvent.lenSet := by
  filter_upwards [gm_S1_1_bcpt h38 hγ hγ2 hD P h hh,
    hD.length P h (Tight.isGFFPlusCont_of_wp hh)] with ω hb hl
  exact LocalEvent.mem_lenSet hl hb

/-- **GM Lemma 3.7, measurability part** (l. 1345–1360): `𝖤_r(z)`, written through the internal
metrics of `𝔸_{r/2,2r}(z)`, is a.s. an event of `σ(h|_{𝔸_{r/2,2r}(z)})`. -/
theorem gm_L3_7meas (h38 : DFGPSLem3_8) : L3_7meas := by
  intro γ D D' c hPS α hα hα1 A C' z r hr Ω _ P _ h hh
  obtain ⟨hγ0, hγ2, hD, hD'⟩ := id hPS
  set U := annulus z (r / 2) (2 * r) with hUdef
  have hUo : IsOpen (U : Set ℂ) := U.isOpen
  have hgp := Tight.isGFFPlusCont_of_wp hh
  obtain ⟨Φ, hΦ, hΦae⟩ := hD.locality P h hgp U
  obtain ⟨Φ', hΦ', hΦae'⟩ := hD'.locality P h hgp U
  -- a dense sequence of `U`
  have hzU : z + (r : ℂ) ∈ (U : Set ℂ) := by
    show r / 2 < ‖z + (r : ℂ) - z‖ ∧ ‖z + (r : ℂ) - z‖ < 2 * r
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hr.le]
    constructor <;> linarith
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
  -- the data
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
  have hV : Measurable[fieldSigma h U] fun ω => G (restrictTo U (h ω)) :=
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
  set W : Set DistC := D ⁻¹' LocalEvent.lenSet ∩ D' ⁻¹' LocalEvent.lenSet
  have hW : MeasurableSet W :=
    (LocalEvent.measurableSet_lenSet.preimage hD.measurable).inter
      (LocalEvent.measurableSet_lenSet.preimage hD'.measurable)
  have hYW : ∀ᵐ ω ∂P, h ω ∈ W := by
    filter_upwards [ae_mem_lenSet h38 hγ0 hγ2 hD P h hh,
      ae_mem_lenSet h38 hγ0 hγ2 hD' P h hh] with ω h1 h2
    exact ⟨h1, h2⟩
  set B : Set DistC := {g | goodAnnulusI ((D g).internal U) ((D' g).internal U) α A C' r z}
  -- on `W`, `B` is the universally measurable `gaCompareB ∩ gaLongB ∩ gaAround`
  have hBW : ∀ g ∈ W, (g ∈ B ↔ g ∈ gaCompareB D D' α C' r z ∩ gaLongB D D' α r z ∩
      gaAround D α A r z) := by
    rintro g ⟨hg, hg'⟩
    have hl := LocalEvent.isLength_of_mem_lenSet hg
    have hl' := LocalEvent.isLength_of_mem_lenSet hg'
    have hb := LocalEvent.bcpt_of_mem_lenSet hg
    have := properSpace_of_bcpt _ hb
    have := properSpace_of_bcpt _ (LocalEvent.bcpt_of_mem_lenSet hg')
    have hex : ∀ a b : ℂ, ∃ η, (D g).IsGeod01 a b η := fun a b =>
      exists_isGeod01_of_bcpt _ hl hb a b
    rw [show g ∈ B ↔ _ from (mem_goodAnnulus_iff_internal hα hα1 hr hl hl' hex).symm]
    simp only [goodAnnulus, mem_inter_iff, mem_gaCompare_iff hex, mem_gaLong_iff_gaLongB hl]
  have hB : NullMeasurableSet B (P.map h) := by
    have hS : UMeasurableSet (gaCompareB D D' α C' r z ∩ gaLongB D D' α r z ∩
        gaAround D α A r z) :=
      ((uMeasurableSet_gaCompareB hD.measurable hD'.measurable α C' r z).inter
        (uMeasurableSet_gaLongB hD.measurable hD'.measurable α r z)).inter
        (uMeasurableSet_gaAround hD.measurable α A r z)
    refine (hS.nullMeasurableSet (P.map h)).congr ?_
    filter_upwards [(ae_map_iff hh.measurable.aemeasurable hW).2 hYW] with g hg
    exact propext (hBW g hg).symm
  have hsat : ∀ g₁ ∈ W, ∀ g₂ ∈ W, R g₁ = R g₂ → g₁ ∈ B → g₂ ∈ B := by
    rintro g₁ ⟨h1, h1'⟩ g₂ ⟨h2, h2'⟩ he hB1
    have l1 := LocalEvent.isLength_of_mem_lenSet h1
    have l1' := LocalEvent.isLength_of_mem_lenSet h1'
    have l2 := LocalEvent.isLength_of_mem_lenSet h2
    have l2' := LocalEvent.isLength_of_mem_lenSet h2'
    have e1 : (D g₁).internal U = (D g₂).internal U := by
      refine internal_eq_of_dense l1 l2 hUo hqU hqd fun i j => ?_
      rw [(D g₁).internal_eq_chainInf l1 hUo, (D g₂).internal_eq_chainInf l2 hUo]
      exact congrFun (congrArg Prod.fst he) (i, j)
    have e2 : (D' g₁).internal U = (D' g₂).internal U := by
      refine internal_eq_of_dense l1' l2' hUo hqU hqd fun i j => ?_
      rw [(D' g₁).internal_eq_chainInf l1' hUo, (D' g₂).internal_eq_chainInf l2' hUo]
      exact congrFun (congrArg Prod.snd he) (i, j)
    show goodAnnulusI _ _ α A C' r z
    rw [← e1, ← e2]
    exact hB1
  exact LocalEvent.aeEventIn_of_saturated hh.measurable hR hV hVR hW hB hYW hsat

/-- **GM Lemma 3.7** (with `DFGPSLem3_8`, D50) -/
theorem gm_L3_7 (h38 : DFGPSLem3_8) : L3_7 := gm_L3_7_of_meas h38 (gm_L3_7meas h38)

end LQGMetric.GM
