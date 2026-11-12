/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D114T1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114S2
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114S3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114S4
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114S7
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L35B9
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112A
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.SetupStop
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate3E
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreSt
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import Mathlib.MeasureTheory.Function.Floor

/-!
# CONF Lemma 3.6, Step 3: measurability and locality inputs of (3.25)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Step 3 (C:1425–1447), decision D114 §4 C2;
route of `handoff/P2-CONF36N.md` §5.

* (B-T) `conf36_setSigma_T`: `{T_r(𝓑) = 𝔗'}` is a `σ(𝓑)`-event (hitting closed sets,
  `GM.gm_setSigma_hit_closed`).
* (B-C) `conf36_setSigma_conn`: the connectivity event `conf36Conn` is a `σ(𝓑)`-event.
* (B-z) `conf36_measurable_grid`: the grid centre `⌊x/m⌋m` is measurable.
* `conf36_aeEventIn_recSigma`: an a.s. event of `σ((h − h_{r'}(𝔷))|_{B_{5r'}(𝔷)})` is an a.s. event
  of `σ((h − h_𝔯(𝔷))|_{ℂ∖𝔘})` for `5r' ≤ 3𝔯` (`𝔘 ⊆ 𝔸_{3𝔯,4𝔯}(𝔷)`; change of normalization by
  `GM.gm_fieldSigma_circleAvg_le` and the a.s. identity `(h+a)_{r'} = h_{r'} + a`).
* (DL1) `conf36_confEU_ball`: `E^U_{r'}(𝔷)` (CONF C:1150–1154: determined by `h` on
  `𝔸_{2r',5r'}(𝔷)` modulo constants; the `hEU` step of `confEMeas_of`, S3EMeas).
* (DL2) `conf36_fatG_ball`: the `fatG` event at `r'` (Axiom II on each `W_C`, as `cond2_sq_norm`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

section SetMeas
variable {Ω : Type}

/-- **(B-T)** `{T_r(𝓑) = 𝔗'}` is a `σ(𝓑)`-event for a random closed set `𝓑` -/
theorem conf36_setSigma_T {Bf : Ω → Set ℂ} (hBc : ∀ ω, IsClosed (Bf ω)) (δ r : ℝ) (z : ℂ)
    (T : Finset (ℤ × ℤ)) : MeasurableSet[setSigma Bf] {ω | conf36T δ r z (Bf ω) = T} := by
  have hmem : ∀ k, MeasurableSet[setSigma Bf] {ω | k ∈ conf36T δ r z (Bf ω)} := by
    intro k
    have e : {ω | k ∈ conf36T δ r z (Bf ω)} =
        {_ω | k ∈ conf36Box δ ∧ k ∈ confSqIdx (δ * r) z (annulus z (3 * r) (4 * r))} ∩
          {ω | (Bf ω ∩ confSq (δ * r) z k).Nonempty} := by
      ext ω
      simp only [conf36T, Finset.mem_filter, mem_ofPred_eq, mem_inter_iff]
      rw [Set.inter_comm (Bf ω)]
      tauto
    rw [e]
    exact (MeasurableSet.const _).inter
      (GM.gm_setSigma_hit_closed hBc (GM.p412j_isClosed_confSq _ _ _))
  have e : {ω | conf36T δ r z (Bf ω) = T} =
      ⋂ k : ℤ × ℤ, {ω | k ∈ conf36T δ r z (Bf ω) ↔ k ∈ T} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, Finset.ext_iff]
  rw [e]
  refine MeasurableSet.iInter fun k => ?_
  by_cases hk : k ∈ T
  · have e2 : {ω | (k ∈ conf36T δ r z (Bf ω) ↔ k ∈ T)} = {ω | k ∈ conf36T δ r z (Bf ω)} := by
      ext ω; simp only [mem_ofPred_eq, hk, iff_true]
    rw [e2]; exact hmem k
  · have e2 : {ω | (k ∈ conf36T δ r z (Bf ω) ↔ k ∈ T)} = {ω | k ∈ conf36T δ r z (Bf ω)}ᶜ := by
      ext ω; simp only [mem_ofPred_eq, mem_compl_iff, hk, iff_false]
    rw [e2]; exact (hmem k).compl

/-- **(B-C)** the connectivity event is a `σ(𝓑)`-event -/
theorem conf36_setSigma_conn (Bf : Ω → Set ℂ) (r : ℝ) (z : ℂ) :
    MeasurableSet[setSigma Bf] {ω | conf36Conn (Bf ω) r z} := by
  have e : {ω | conf36Conn (Bf ω) r z} =
      {ω | (Bf ω ∩ (annulus z (3 * r) (4 * r) : Set ℂ)).Nonempty} ∪
        {ω | (Bf ω ∩ (closedBall z (3 * r))ᶜ).Nonempty}ᶜ := by
    ext ω
    simp only [conf36Conn, mem_ofPred_eq, mem_union, mem_compl_iff, not_nonempty_iff_eq_empty,
      ← sdiff_eq, sdiff_eq_empty]
  rw [e]
  exact (GM.gm_setSigma_hit_open Bf (annulus z (3 * r) (4 * r)).isOpen).union
    (GM.gm_setSigma_hit_open Bf isClosed_closedBall.isOpen_compl).compl

/-- **(B-z)** the grid centre `⌊x/m⌋ m` is measurable -/
theorem conf36_measurable_grid {M : MeasurableSpace Ω} {m : Ω → ℝ} {x : Ω → ℂ}
    (hm : Measurable[M] m) (hx : Measurable[M] x) :
    Measurable[M] (fun ω => conf36Grid (m ω) (x ω)) := by
  have hc : Measurable fun n : ℤ => (n : ℝ) := measurable_of_countable _
  have h1 : Measurable[M] fun ω => ((⌊(x ω).re / m ω⌋ : ℤ) : ℝ) * m ω :=
    (hc.comp ((Complex.measurable_re.comp hx).div hm).floor).mul hm
  have h2 : Measurable[M] fun ω => ((⌊(x ω).im / m ω⌋ : ℤ) : ℝ) * m ω :=
    (hc.comp ((Complex.measurable_im.comp hx).div hm).floor).mul hm
  exact Complex.measurableEquivRealProd.symm.measurable.comp (h1.prodMk h2)

end SetMeas

section Loc
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- **change of normalization**: an a.s. event of `σ((h − h_{r'}(𝔷))|_{B_{5r'}(𝔷)})` is an a.s.
event of `σ((h − h_𝔯(𝔷))|_{ℂ∖𝔘})`, `𝔘 = confU 𝔯 δ 𝔷 𝔗`, when `5r' ≤ 3𝔯` -/
theorem conf36_aeEventIn_recSigma (hh : IsWholePlaneGFF h P) {𝔯 δ r' : ℝ} {𝔷 : ℂ}
    {𝔗 : Finset (ℤ × ℤ)} (hr' : 0 < r') (h5 : 5 * r' ≤ 3 * 𝔯) {E : Set Ω}
    (hE : AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) r' 𝔷))
      ⟨ball 𝔷 (5 * r'), isOpen_ball⟩) E) :
    AEEventIn P (recSigma h 𝔯 𝔷 (confU 𝔯 δ 𝔷 𝔗)ᶜ) E := by
  set g : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) 𝔯 𝔷) with hg
  set W : Opens ℂ := ⟨ball 𝔷 (5 * r'), isOpen_ball⟩ with hW
  have hae : ∀ᵐ ω ∂P, addConst (g ω) (-circleAvg (g ω) r' 𝔷) =
      addConst (h ω) (-circleAvg (h ω) r' 𝔷) := by
    filter_upwards [CircleAvg.ae_circleAvg_addConst hh 𝔷 hr'] with ω hω
    simp only [hg, hω, GFFLaw.addConst_addConst]
    congr 1
    ring
  obtain ⟨F, hF, hEF⟩ := hE
  obtain ⟨S, hS, hSF⟩ := hF
  refine ⟨(fun ω => restrictTo W (addConst (g ω) (-circleAvg (g ω) r' 𝔷))) ⁻¹' S, ?_, ?_⟩
  · have h1 : MeasurableSet[fieldSigma (fun ω => addConst (g ω) (-circleAvg (g ω) r' 𝔷)) W]
        ((fun ω => restrictTo W (addConst (g ω) (-circleAvg (g ω) r' 𝔷))) ⁻¹' S) :=
      ⟨S, hS, rfl⟩
    have h2 := GM.gm_fieldSigma_circleAvg_le g (A := W) (W := W) (ρ := r') (z := 𝔷) le_rfl
      (by rw [abs_of_pos hr']; exact sphere_subset_ball (by linarith))
    have hsub : (W : Set ℂ) ⊆ (confU 𝔯 δ 𝔷 𝔗)ᶜ := by
      intro w hw hwU
      have h3 : 3 * 𝔯 < ‖w - 𝔷‖ := hwU.1.1
      have h4 : dist w 𝔷 < 5 * r' := hw
      rw [dist_eq_norm] at h4
      linarith
    exact DFGPS.L217.fieldSigma_le_fieldSigmaClosed_of_subset g hsub _ (h2 _ h1)
  · refine hEF.trans ?_
    rw [← hSF]
    filter_upwards [hae] with ω hω
    change (restrictTo W (addConst (h ω) (-circleAvg (h ω) r' 𝔷)) ∈ S) =
      (restrictTo W (addConst (g ω) (-circleAvg (g ω) r' 𝔷)) ∈ S)
    rw [hω]

variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}

/-- **(DL1)** `E^U_r(z)` is a.s. an event of `σ((h − h_r(z))|_{B_{5r}(z)})` (CONF C:1150–1154;
the `hEU` step of `confEMeas_of`) -/
theorem conf36_confEU_ball (hD : IsWeakLQGMetric γ D c) (hh : IsWholePlaneGFF h P)
    (p : CONFParams) {r : ℝ} (hr : 0 < r) (z : ℂ) (T : Finset (ℤ × ℤ)) :
    AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) r z))
      ⟨ball z (5 * r), isOpen_ball⟩) (confEU (xiGamma γ) c D P h p r z T) := by
  set W := annulus z (3 / 2 * r) (5 * r)
  have hUW : closure (confU r p.δ z T) ⊆ (W : Set ℂ) := by
    have hcl : IsClosed {w : ℂ | 3 * r ≤ ‖w - z‖ ∧ ‖w - z‖ ≤ 4 * r} :=
      (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
        (isClosed_le (continuous_id.sub continuous_const).norm continuous_const)
    refine (closure_minimal (fun w hw => ?_) hcl).trans (fun w hw => ?_)
    · have := hw.1; exact ⟨this.1.le, this.2.le⟩
    · show 3 / 2 * r < ‖w - z‖ ∧ ‖w - z‖ < 5 * r
      exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hWB : W ≤ ⟨ball z (5 * r), isOpen_ball⟩ := fun w hw => by
    show dist w z < 5 * r
    rw [dist_eq_norm]; exact hw.2
  have e : confEU (xiGamma γ) c D P h p r z T =
      {ω | ENNReal.ofReal (p.c * scaleFac (xiGamma γ) c (h ω) r z) ≤
        setDist (D (h ω)) (sphere z (2 * r)) (sphere z (3 * r))} ∩
      ((⋂ k : confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r)), {ω |
        internalDiam (D (h ω)) (confSq (p.δ * r) z k) (annulus z (2 * r) (5 * r)) ≤
          ENNReal.ofReal (p.c / 100 * scaleFac (xiGamma γ) c (h ω) r z)}) ∩
      {ω | ∀ u ∈ innerPart (confU r p.δ z T) (p.δ * r / 4),
        |harmPart P h (confU r p.δ z T) ω u - circleAvg (h ω) r z| ≤ p.A}) := by
    ext ω
    simp only [confEU, mem_ofPred_eq, mem_inter_iff, mem_iInter, Subtype.forall]
  have H : AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) r z)) W)
      (confEU (xiGamma γ) c D P h p r z T) := by
    rw [e]
    exact GM.p412j_aeEventIn_inter (cond1_norm hD P h hh c hr z p.c)
      (GM.p412j_aeEventIn_inter (GM.gm_aeEventIn_iInter fun k =>
        cond2_sq_norm hD P h hh c hr z (p.c / 100) p.δ k)
      (cond3_norm confHarmLocN P h hh W (GM.p412j_isOpen_confU r p.δ z T)
        (isBounded_closedBall.subset (GM.p412j_confU_subset r p.δ z T)) hUW hr _ _))
  obtain ⟨F, hF, hEF⟩ := H
  exact ⟨F, GM.fieldSigma_mono _ hWB _ hF, hEF⟩

/-- the internal-diameter event of a set `Q` in an open set `A ≤ W` is a.s. an event of
`σ((h − h_r(z))|_W)` (as `cond2_sq_norm`, S3EMeas, for a general `Q` and `A`) -/
theorem conf36_internalDiam_aeEventIn (hD : IsWeakLQGMetric γ D c) (hh : IsWholePlaneGFF h P)
    (cc : ℝ → ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) (c' : ℝ) (Q : Set ℂ) (A W : Opens ℂ)
    (hAW : Q.Nonempty → Q ⊆ (A : Set ℂ) → A ≤ W) :
    AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) r z)) W) {ω |
      internalDiam (D (h ω)) Q A ≤ ENNReal.ofReal (c' * scaleFac (xiGamma γ) cc (h ω) r z)} := by
  set g : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) r z) with hg_def
  by_cases hQ : Q.Nonempty ∧ Q ⊆ (A : Set ℂ)
  · have hm : Measurable fun ω => -circleAvg (h ω) r z :=
      ((measurable_circleAvg_left r z).comp hh.measurable).neg
    have hgp := GM.Tight.isGFFPlusCont_of_wp (hh.addConst hm)
    have hAW' := hAW hQ.1 hQ.2
    obtain ⟨Φ, hΦ, hΦae⟩ := hD.locality P g hgp A
    obtain ⟨a, haS, haD⟩ := DFGPS.L32M.exists_denseSeq hQ.1
    set V : Ω → (ℕ × ℕ → ℝ≥0∞) := fun ω q => Φ (restrictTo A (g ω)) (a q.1) (a q.2)
    have hV : Measurable[fieldSigma g W] V := by
      have hG : Measurable fun x : DistOn A => fun q : ℕ × ℕ => Φ x (a q.1) (a q.2) :=
        measurable_pi_iff.2 fun q =>
          (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hΦ)
      exact (hG.comp (Measurable.of_comap_le le_rfl)).mono (GM.fieldSigma_mono g hAW') le_rfl
    set S : Set (ℕ × ℕ → ℝ≥0∞) := {x | ⨆ q, x q ≤ ENNReal.ofReal (c' * cc r)}
    have hSm : MeasurableSet S :=
      measurableSet_le (Measurable.iSup fun q => measurable_pi_apply q) measurable_const
    refine ⟨V ⁻¹' S, hV hSm, ?_⟩
    filter_upwards [hΦae, hD.length P g hgp, ae_dist_norm hD P h hh hr z] with ω h1 hl hsc
    have he := Real.exp_pos (xiGamma γ * circleAvg (h ω) r z)
    have e : internalDiam (D (h ω)) Q A =
        ENNReal.ofReal (Real.exp (xiGamma γ * circleAvg (h ω) r z)) *
          ⨆ q : ℕ × ℕ, Φ (restrictTo A (g ω)) (a q.1) (a q.2) := by
      rw [DFGPS.L32M.internalDiam_of_scale he hsc,
        DFGPS.L32M.internalDiam_eq_iSup (D (g ω)) hl A.isOpen hQ.2 haS haD]
      congr 1
      exact iSup_congr fun q => h1 _ (hQ.2 (haS _)) _ (hQ.2 (haS _))
    have hl' : ENNReal.ofReal (c' * scaleFac (xiGamma γ) cc (h ω) r z) =
        ENNReal.ofReal (Real.exp (xiGamma γ * circleAvg (h ω) r z)) *
          ENNReal.ofReal (c' * cc r) := by
      rw [← ENNReal.ofReal_mul he.le, scaleFac]; congr 1; ring
    change (internalDiam (D (h ω)) Q A ≤
      ENNReal.ofReal (c' * scaleFac (xiGamma γ) cc (h ω) r z)) = (V ω ∈ S)
    rw [e, hl', ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 he).ne' ENNReal.ofReal_ne_top]
    rfl
  · rcases not_and_or.1 hQ with hQ | hQ
    · have : ∀ ω, internalDiam (D (h ω)) Q A = 0 := fun ω => by
        rw [not_nonempty_iff_eq_empty.1 hQ]; simp [internalDiam]
      simp only [this, zero_le]
      exact GM.p412j_aeEventIn_const True
    · obtain ⟨u, huQ, huA⟩ := not_subset.1 hQ
      have htop : ∀ ω, internalDiam (D (h ω)) Q A = ⊤ := fun ω => by
        refine top_le_iff.1 (le_trans ?_ (le_iSup₂_of_le u huQ (le_iSup₂ (f := fun v _ =>
          (D (h ω)).internal A u v) u huQ)))
        unfold ContMetric.internal MetricGeometry.internalEDist
        have : IsEmpty {γ' : Path ((D (h ω)).pt u) ((D (h ω)).pt u) //
            ∀ t, γ' t ∈ (D (h ω)).pt '' (A : Set ℂ)} := ⟨fun γ' => huA (by
          obtain ⟨w, hw, hwu⟩ := γ'.2 0
          rw [Path.source] at hwu
          exact (show w = u from hwu) ▸ hw)⟩
        rw [iInf_of_empty]
      simp only [htop, top_le_iff, ENNReal.ofReal_ne_top]
      exact GM.p412j_aeEventIn_const False

/-- **(DL2)** the `fatG` event at radius `r` is a.s. an event of `σ((h − h_r(z))|_{B_{5r}(z)})`
(`δ < 1/8`; Axiom II on each `W_C ⊆ 𝔸_{2r,5r}(z)`, `confFatW_subset_annulus`) -/
theorem conf36_fatG_ball (hD : IsWeakLQGMetric γ D c) (hh : IsWholePlaneGFF h P)
    (p : CONFParams) (hδ : 0 < p.δ) (hδ8 : p.δ < 1 / 8) (cc : ℝ → ℝ) {r : ℝ} (hr : 0 < r)
    (z : ℂ) (T : Finset (ℤ × ℤ)) :
    AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) r z))
      ⟨ball z (5 * r), isOpen_ball⟩)
      {ω | fatG p (D (h ω)) (scaleFac (xiGamma γ) cc (h ω) r z) r z T} := by
  have hε : 0 < p.δ * r := mul_pos hδ hr
  have hεr : 8 * (p.δ * r) ≤ r := by nlinarith
  have e : {ω | fatG p (D (h ω)) (scaleFac (xiGamma γ) cc (h ω) r z) r z T} =
      ⋂ k : confFree (p.δ * r) z r T, {ω |
        internalDiam (D (h ω)) (confCtrs (p.δ * r) z (confComp (confFree (p.δ * r) z r T) k))
          (⟨confFatW (p.δ * r) z (confComp (confFree (p.δ * r) z r T) k), isOpen_thickening⟩ :
            Opens ℂ) ≤ ENNReal.ofReal (p.c / 100 * scaleFac (xiGamma γ) cc (h ω) r z)} := by
    ext ω
    simp only [fatG, mem_ofPred_eq, mem_iInter, Subtype.forall]
    rfl
  rw [e]
  refine GM.gm_aeEventIn_iInter fun k => conf36_internalDiam_aeEventIn hD hh cc hr z _ _ _ _ ?_
  intro _ _ w hw
  have hC : confComp (confFree (p.δ * r) z r T) k ⊆ confFull (p.δ * r) z r :=
    (confComp_subset k.2).trans diff_subset
  have hw' := confFatW_subset_annulus hε hεr z hC hw
  show dist w z < 5 * r
  rw [dist_eq_norm]; exact hw'.2

end Loc

end LQGMetric.CONF
