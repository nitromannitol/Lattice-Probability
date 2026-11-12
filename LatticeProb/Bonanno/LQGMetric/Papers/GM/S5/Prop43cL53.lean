/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43cL53 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43bL53b
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEvent
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.HalfDiscTV

/-!
# GM Lemma 5.3: `𝔈_r^{𝕫,𝕨}(z)` is a.s. determined by `h|_{B_{4r}(z)}` and the stopped geodesic
(task P2-M2N3)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
Lemma 5.3 and its proof, l. 2775–2789: "(5.5) is determined by `h|_{B_{4r}(z)}` … on `𝔈`,
`D_h(P(s),P(t)) = D_h(P(s),P(t); B_{4r}(z))` … By Axiom II (locality) the event is determined by
`h|_{B_{4r}(z)}` and the stopped path."

The reduction to the internal form (5.4) for the stopped path is P2-M2N2's
`ae_mem_constCore_frkE_iff_stop`. Here:
* `measurable_dirInner_fieldSigma`: `(h, φ)_∇` with `supp φ ⊂ U` is `σ(h|_U)`-measurable ((5.5));
* `measurable_lastExitTime`, `measurable_stopLastExit_apply`, `continuous_stopLastExit`: the
  stopped path is a Borel function of the path, continuous in time;
* `frkDistIn_congr`: (5.4) in internal form only sees the internal metrics on `B_{4r}(z)`;
* `gm_L5_3_meas`: the internal-form event is a.s. in `σ(h|_{B_{4r}}) ∨ σ(stopped path)`
  (Axiom II for `D`, `D̃`, read on a countable dense set of pairs (LM Lemma 1.1, continuity), and
  Lusin separation `LocalEvent.aeEventIn_of_saturated`, as P2-E3a's `gm_aeEventIn_of_local`);
* `gm_L5_3`: GM Lemma 5.3 for the constant-invariant core of `𝔈` (condition (2) of
  `GeoIterateHyp` for `𝔈`, `λ₃ = 4`).
GM do not discuss measurability; the countable-dense-set reduction and Lusin separation are the
project convention (D30, D51).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter TopologicalSpace Laplacian
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-! ## (5.5) is local -/

/-- `tsupport (cmTest φ) ⊆ tsupport φ` -/
lemma tsupport_cmTest_subset_c53 (φ : TestC) :
    tsupport (cmTest φ : ℂ → ℝ) ⊆ tsupport (φ : ℂ → ℝ) :=
  closure_minimal (fun x hx => by_contra fun h' => hx (by
    rw [cmTest_apply, QuantumZipper.K3.laplacian_eq_zero_of_notMem_tsupport h', mul_zero]))
    (isClosed_tsupport _)

/-- a test function on `ℂ` supported in `U`, as an element of `𝓓(U)` -/
def testOnC53 (U : Opens ℂ) (φ : TestC) (hφ : tsupport (φ : ℂ → ℝ) ⊆ U) : TestOn U :=
  ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩

lemma restrictTo_testOnC53 (U : Opens ℂ) (g : DistC) (φ : TestC)
    (hφ : tsupport (φ : ℂ → ℝ) ⊆ U) : restrictTo U g (testOnC53 U φ hφ) = g φ := by
  change g (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤) _) = g φ
  congr 1
  ext x
  simp [TestFunction.monoCLM_apply, testOnC53]

/-- `(h, φ)_∇` is `σ(h|_U)`-measurable when `supp φ ⊂ U` (GM l. 2777) -/
lemma measurable_dirInner_fieldSigma {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC)
    (U : Opens ℂ) (φ : TestC) (hφ : tsupport (φ : ℂ → ℝ) ⊆ U) :
    Measurable[fieldSigma h U] fun ω => dirInner (h ω) φ := by
  have hφ' : tsupport (cmTest φ : ℂ → ℝ) ⊆ U := (tsupport_cmTest_subset_c53 φ).trans hφ
  have e : (fun ω => dirInner (h ω) φ) =
      (fun g : DistOn U => g (testOnC53 U (cmTest φ) hφ')) ∘ fun ω => restrictTo U (h ω) := by
    funext ω
    simp only [Function.comp, restrictTo_testOnC53, dirInner]
  rw [e]
  exact (measurable_distOn_apply _).comp (comap_measurable _)

/-- the (5.5) event is in `σ(h|_U)` -/
lemma measurableSet_dirBound_fieldSigma {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC)
    (U : Opens ℂ) (G : Finset TestC) (hG : ∀ φ ∈ G, tsupport (φ : ℂ → ℝ) ⊆ U) (Λ : ℝ) :
    MeasurableSet[fieldSigma h U]
      {ω | ∀ φ ∈ (G : Set TestC), Real.exp (-dirInner (h ω) φ + gradEnergy φ / 2) ≤ Λ} := by
  have e : {ω | ∀ φ ∈ (G : Set TestC), Real.exp (-dirInner (h ω) φ + gradEnergy φ / 2) ≤ Λ} =
      ⋂ φ ∈ G, {ω | Real.exp (-dirInner (h ω) φ + gradEnergy φ / 2) ≤ Λ} := by
    ext ω; simp
  rw [e]
  refine Finset.measurableSet_biInter _ fun φ hφ => ?_
  exact measurableSet_le
    (Real.measurable_exp.comp (((measurable_dirInner_fieldSigma h U φ (hG φ hφ)).neg).add_const _))
    measurable_const

/-! ## The stopped path -/

lemma stopLastExit_eq_lastExitTime (η : C(unitInterval, ℂ)) (K : Set ℂ) (t : unitInterval) :
    stopLastExit η K t = η (projIcc 0 1 zero_le_one ((t : ℝ) * lastExitTime η K)) := rfl

lemma continuous_stopLastExit (η : C(unitInterval, ℂ)) (K : Set ℂ) :
    Continuous (stopLastExit η K) :=
  η.continuous.comp (continuous_projIcc.comp (continuous_subtype_val.mul continuous_const))

open Classical in
/-- for `K` open, the last time in `K` is the supremum over a dense sequence of times -/
lemma lastExitTime_eq_iSup (η : C(unitInterval, ℂ)) {K : Set ℂ} (hK : IsOpen K) :
    lastExitTime η K = ⨆ k : ℕ, (if η (denseSeq unitInterval k) ∈ K then
      ((denseSeq unitInterval k : unitInterval) : ℝ) else 0) := by
  classical
  set A := {s : ℝ | ∃ u : unitInterval, (u : ℝ) = s ∧ η u ∈ K} with hA
  set f : ℕ → ℝ := fun k => if η (denseSeq unitInterval k) ∈ K then
    ((denseSeq unitInterval k : unitInterval) : ℝ) else 0 with hf
  have hf1 : ∀ k, f k ≤ 1 := fun k => by
    simp only [hf]; split_ifs
    · exact (denseSeq unitInterval k).2.2
    · exact zero_le_one
  have hbdd : BddAbove (range f) := ⟨1, by rintro _ ⟨k, rfl⟩; exact hf1 k⟩
  have hAbdd : BddAbove A := ⟨1, by rintro _ ⟨u, rfl, -⟩; exact u.2.2⟩
  show sSup A = iSup f
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · have hf0 : ∀ k, f k = 0 := fun k => by
      simp only [hf]; split_ifs with hk
      · exact absurd (show ((denseSeq unitInterval k : unitInterval) : ℝ) ∈ A from ⟨_, rfl, hk⟩)
          (hAe ▸ notMem_empty _)
      · rfl
    have hf0' : f = fun _ => 0 := funext hf0
    rw [hAe, Real.sSup_empty, hf0', ciSup_const]
  refine le_antisymm ?_ ?_
  · refine le_of_forall_lt fun c hc => ?_
    obtain ⟨s, ⟨u, rfl, hu⟩, hcs⟩ := exists_lt_of_lt_csSup hAne hc
    have hO : IsOpen {v : unitInterval | η v ∈ K ∧ c < (v : ℝ)} :=
      (hK.preimage η.continuous).inter (isOpen_lt continuous_const continuous_subtype_val)
    obtain ⟨k, hk1, hk2⟩ :=
      (denseRange_denseSeq unitInterval).exists_mem_open hO ⟨u, hu, hcs⟩
    refine lt_of_lt_of_le ?_ (le_ciSup hbdd k)
    simp only [hf, if_pos hk1]; exact hk2
  · refine ciSup_le fun k => ?_
    simp only [hf]; split_ifs with hk
    · exact le_csSup hAbdd ⟨_, rfl, hk⟩
    · obtain ⟨_, u, rfl, hu⟩ := hAne
      exact (u.2.1).trans (le_csSup hAbdd ⟨u, rfl, hu⟩)

open Classical in
lemma measurable_lastExitTime {K : Set ℂ} (hK : IsOpen K) :
    Measurable fun η : C(unitInterval, ℂ) => lastExitTime η K := by
  classical
  simp_rw [lastExitTime_eq_iSup _ hK]
  refine Measurable.iSup fun k => Measurable.ite ?_ measurable_const measurable_const
  exact (continuous_eval_const _).measurable hK.measurableSet

lemma measurable_stopLastExit_apply {K : Set ℂ} (hK : IsOpen K) (t : unitInterval) :
    Measurable fun η : C(unitInterval, ℂ) => stopLastExit η K t := by
  simp_rw [stopLastExit_eq_lastExitTime]
  have hev : Measurable fun p : C(unitInterval, ℂ) × unitInterval => p.1 p.2 :=
    continuous_eval.measurable
  exact hev.comp (measurable_id.prodMk ((continuous_projIcc (a := (0 : ℝ)) (b := 1)
    (h := zero_le_one)).measurable.comp
    (measurable_const.mul (measurable_lastExitTime hK))))

/-! ## (5.4) in internal form only sees the internal metrics on `B_{4r}(z)` -/

lemma frkDistIn_congr {d₁ d₁' d₂ d₂' : ContMetric} {cs Cs c₂ b₀ r : ℝ} (hr : 0 < r) {z : ℂ}
    {Q : unitInterval → ℂ}
    (h1 : ∀ x ∈ ball z (4 * r), ∀ y ∈ ball z (4 * r),
      d₁.internal (ball z (4 * r)) x y = d₂.internal (ball z (4 * r)) x y)
    (h2 : ∀ x ∈ ball z (4 * r), ∀ y ∈ ball z (4 * r),
      d₁'.internal (ball z (4 * r)) x y = d₂'.internal (ball z (4 * r)) x y)
    (H : frkDistIn d₁ d₁' cs Cs c₂ b₀ r z Q) : frkDistIn d₂ d₂' cs Cs c₂ b₀ r z Q := by
  obtain ⟨s, t, h0, hst, ht1, hs, ht, hb, hA, hB⟩ := H
  have hs4 : Q s ∈ ball z (4 * r) := ball_subset_ball (by linarith) hs
  have ht4 : Q t ∈ ball z (4 * r) := ball_subset_ball (by linarith) ht
  have hsd : DFGPS.setDistIn d₁' {Q s} (sphere z (3 * r)) (ball z (4 * r)) =
      DFGPS.setDistIn d₂' {Q s} (sphere z (3 * r)) (ball z (4 * r)) := by
    simp only [DFGPS.setDistIn, iInf_singleton]
    exact iInf_congr fun v => iInf_congr fun hv => h2 _ hs4 _ (sphere_subset_ball (by linarith) hv)
  refine ⟨s, t, h0, hst, ht1, hs, ht, hb, ?_, ?_⟩
  · rw [← h1 _ hs4 _ ht4, ← h2 _ hs4 _ ht4]; exact hA
  · rw [← h2 _ hs4 _ ht4, ← hsd]; exact hB

/-! ## GM Lemma 5.3 -/

/-- **GM Lemma 5.3, measurability half** (l. 2775–2789): the internal form of (5.4) for the
geodesic stopped at its last exit from `B_{4r}(z)` is a.s. an event of
`σ(h|_{B_{4r}(z)}) ∨ σ(stopped path)`. Axiom II for `D` and `D̃` on `B_{4r}(z)`, read on a
countable dense set of pairs (LM Lemma 1.1), the stopped path read at a dense set of times, and
Lusin separation (`LocalEvent.aeEventIn_of_saturated`). -/
theorem gm_L5_3_meas {γ : ℝ} {D D' : DistC → ContMetric} {c₀ c₀' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c₀) (hD' : IsWeakLQGMetric γ D' c₀')
    {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)}
    (hsel : ∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g)
    (hselm : ∀ a b : ℂ, Measurable (sel a b))
    {cs Cs c₂ b₀ r : ℝ} (hcs : 0 < cs) (hcC : cs ≤ Cs) (hc₂ : 0 ≤ c₂) (hr : 0 < r)
    (hRat : RatiosAre D D' cs Cs) (z a b : ℂ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) :
    AEEventIn P (fieldSigma h (ballO z (4 * r)) ⊔ MeasurableSpace.comap (fun ω =>
        stopLastExit (sel a b (h ω)) (ball z (4 * r))) inferInstance)
      {ω | frkDistIn (D (h ω)) (D' (h ω)) cs Cs c₂ b₀ r z
        (stopLastExit (sel a b (h ω)) (ball z (4 * r)))} := by
  classical
  set U : Opens ℂ := ballO z (4 * r) with hUdef
  have hUK : (U : Set ℂ) = ball z (4 * r) := rfl
  set B : Set DistC := {g | frkDistIn (D g) (D' g) cs Cs c₂ b₀ r z
    (stopLastExit (sel a b g) (ball z (4 * r)))} with hBdef
  show AEEventIn P _ (h ⁻¹' B)
  -- the law of `h`
  set μ := P.map h with hμ
  have : IsProbabilityMeasure μ := inferInstance
  have hid : IsWholePlaneGFF id μ := isWholePlaneGFF_id_map hh
  -- null-measurability: `B` is a.s. the Borel set `𝔈` (with no bump functions)
  have hB : NullMeasurableSet B μ := by
    have hFm := measurableSet_frkE hD.measurable hD'.measurable (hselm a b) cs Cs c₂ b₀ 1 r
      (∅ : Finset TestC) z
    refine hFm.nullMeasurableSet.congr ?_
    filter_upwards [ae_mem_constCore_frkE_iff_stop hD hD' hsel hcs hcC hc₂ hr hRat (Λ := 1)
      ((∅ : Finset TestC) : Set TestC) z a b hid,
      ae_mem_constCore_frkE_iff hD hD' hsel cs Cs c₂ b₀ 1 r ((∅ : Finset TestC) : Set TestC)
        z a b hid] with g hg1 hg2
    refine propext ⟨fun hF => (hg1.1 (hg2.2 hF)).1, fun hBg => hg2.1 (hg1.2 ⟨hBg, ?_⟩)⟩
    simp
  -- Axiom II on `U = B_{4r}(z)`
  have hgp := Tight.isGFFPlusCont_of_wp hh
  obtain ⟨Φ, hΦ, hΦae⟩ := hD.locality P h hgp U
  obtain ⟨Φ', hΦ', hΦ'ae⟩ := hD'.locality P h hgp U
  have : Nonempty U := ⟨⟨z, mem_ball_self (by positivity)⟩⟩
  let q : ℕ → ℂ := fun i => (denseSeq U i : ℂ)
  have hqU : ∀ i, q i ∈ (U : Set ℂ) := fun i => (denseSeq U i).2
  let tq : ℕ → unitInterval := denseSeq unitInterval
  let A₀ : (DistOn U → ℂ → ℂ → ℝ≥0∞) → DistOn U → (ℕ × ℕ → ℝ≥0∞) :=
    fun F x p => F x (q p.1) (q p.2)
  have hA₀ : ∀ F : DistOn U → ℂ → ℂ → ℝ≥0∞, Measurable F → Measurable (A₀ F) := fun F hF =>
    measurable_pi_iff.2 fun p => (measurable_pi_apply (q p.2)).comp
      ((measurable_pi_apply (q p.1)).comp hF)
  let pth : (unitInterval → ℂ) → (ℕ → ℂ) := fun Q k => Q (tq k)
  have hpth : Measurable pth := measurable_pi_iff.2 fun k => measurable_pi_apply (tq k)
  let R : DistC → ((ℕ × ℕ → ℝ≥0∞) × (ℕ × ℕ → ℝ≥0∞)) × (ℕ → ℂ) := fun g =>
    ((A₀ Φ (restrictTo U g), A₀ Φ' (restrictTo U g)),
      fun k => stopLastExit (sel a b g) (ball z (4 * r)) (tq k))
  have hR : Measurable R :=
    (((hA₀ Φ hΦ).comp (measurable_restrictTo U)).prodMk
      ((hA₀ Φ' hΦ').comp (measurable_restrictTo U))).prodMk
      (measurable_pi_iff.2 fun k =>
        (measurable_stopLastExit_apply isOpen_ball (tq k)).comp (hselm a b))
  have hV1 : Measurable[fieldSigma h U] fun ω => restrictTo U (h ω) := comap_measurable _
  have hV2 : Measurable[MeasurableSpace.comap (fun ω =>
      stopLastExit (sel a b (h ω)) (ball z (4 * r))) inferInstance]
      fun ω => stopLastExit (sel a b (h ω)) (ball z (4 * r)) := comap_measurable _
  have hV : Measurable[fieldSigma h U ⊔ MeasurableSpace.comap (fun ω =>
      stopLastExit (sel a b (h ω)) (ball z (4 * r))) inferInstance] fun ω => R (h ω) := by
    refine Measurable.prodMk (Measurable.prodMk ?_ ?_) ?_
    · exact (hA₀ Φ hΦ).comp (hV1.mono le_sup_left le_rfl)
    · exact (hA₀ Φ' hΦ').comp (hV1.mono le_sup_left le_rfl)
    · exact hpth.comp (hV2.mono (le_sup_right (a := fieldSigma h U)) le_rfl)
  -- the Borel set `W` carrying the law
  set Lbad : Set DistC := {g | ¬((D g).IsLength ∧ (D' g).IsLength)} with hLbad
  set N := toMeasurable μ Lbad with hN
  have hμN : μ N = 0 := by
    rw [hN, measure_toMeasurable]
    have h1 := hD.length μ id (Tight.isGFFPlusCont_of_wp hid)
    have h2 := hD'.length μ id (Tight.isGFFPlusCont_of_wp hid)
    exact ae_iff.1 (h1.and h2)
  set W₀ : Set DistC := (⋂ i, ⋂ j, {g : DistC | (D g).chainInf (U : Set ℂ) (q i) (q j) =
      Φ (restrictTo U g) (q i) (q j)}) ∩
    ⋂ i, ⋂ j, {g : DistC | (D' g).chainInf (U : Set ℂ) (q i) (q j) =
      Φ' (restrictTo U g) (q i) (q j)} with hW₀
  have hW₀m : MeasurableSet W₀ := by
    refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_eq_fun ?_ ?_) (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_eq_fun ?_ ?_)
    · exact (ContMetric.measurable_chainInf (U : Set ℂ)).comp
        (hD.measurable.prodMk (measurable_const (a := (q i, q j))))
    · exact (measurable_pi_apply (q j)).comp ((measurable_pi_apply (q i)).comp
        (hΦ.comp (measurable_restrictTo U)))
    · exact (ContMetric.measurable_chainInf (U : Set ℂ)).comp
        (hD'.measurable.prodMk (measurable_const (a := (q i, q j))))
    · exact (measurable_pi_apply (q j)).comp ((measurable_pi_apply (q i)).comp
        (hΦ'.comp (measurable_restrictTo U)))
  set W := W₀ ∩ Nᶜ with hW
  have hWm : MeasurableSet W := hW₀m.inter (measurableSet_toMeasurable _ _).compl
  have hlenW : ∀ g ∈ W, (D g).IsLength ∧ (D' g).IsLength := fun g hg => by
    by_contra hc; exact hg.2 (subset_toMeasurable _ _ hc)
  have hYW : ∀ᵐ ω ∂P, h ω ∈ W := by
    have hNae : ∀ᵐ g ∂μ, g ∉ N := measure_eq_zero_iff_ae_notMem.1 hμN
    filter_upwards [hΦae, hΦ'ae, ae_of_ae_map hh.measurable.aemeasurable hNae] with ω h1 h2 h3
    have hl : (D (h ω)).IsLength ∧ (D' (h ω)).IsLength := by
      by_contra hc; exact h3 (subset_toMeasurable _ _ hc)
    refine ⟨⟨mem_iInter.2 fun i => mem_iInter.2 fun j => ?_,
      mem_iInter.2 fun i => mem_iInter.2 fun j => ?_⟩, h3⟩
    · show (D (h ω)).chainInf U (q i) (q j) = Φ (restrictTo U (h ω)) (q i) (q j)
      rw [← ContMetric.internal_eq_chainInf _ hl.1 U.isOpen]
      exact h1 _ (hqU i) _ (hqU j)
    · show (D' (h ω)).chainInf U (q i) (q j) = Φ' (restrictTo U (h ω)) (q i) (q j)
      rw [← ContMetric.internal_eq_chainInf _ hl.2 U.isOpen]
      exact h2 _ (hqU i) _ (hqU j)
  have hclos : ∀ x ∈ (U : Set ℂ), x ∈ closure (range q) := by
    intro x hx
    have hd : (⟨x, hx⟩ : U) ∈ closure (range (denseSeq U)) := by
      rw [(denseRange_denseSeq U).closure_eq]; exact mem_univ _
    exact map_mem_closure continuous_subtype_val hd (by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩)
  -- internal metrics agreeing on the dense pairs agree on `U × U` (LM Lemma 1.1)
  have hext : ∀ d₁ d₂ : ContMetric, d₁.IsLength → d₂.IsLength →
      (∀ i j, d₁.internal U (q i) (q j) = d₂.internal U (q i) (q j)) →
      ∀ x ∈ ball z (4 * r), ∀ y ∈ ball z (4 * r),
        d₁.internal (ball z (4 * r)) x y = d₂.internal (ball z (4 * r)) x y := by
    intro d₁ d₂ hl₁ hl₂ hq x hx y hy
    have hEq : EqOn (fun p : ℂ × ℂ => d₁.internal U p.1 p.2)
        (fun p : ℂ × ℂ => d₂.internal U p.1 p.2) ((U : Set ℂ) ×ˢ (U : Set ℂ)) := by
      refine EqOn.of_subset_closure (s := range q ×ˢ range q) ?_
        (d₁.continuousOn_internal hl₁ U.isOpen) (d₂.continuousOn_internal hl₂ U.isOpen) ?_ ?_
      · rintro ⟨_, _⟩ ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
        exact hq i j
      · rintro ⟨_, _⟩ ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
        exact ⟨hqU i, hqU j⟩
      · rw [closure_prod_eq]
        exact prod_mono (fun x hx => hclos x hx) (fun x hx => hclos x hx)
    exact hEq (mk_mem_prod hx hy)
  have hsat : ∀ g₁ ∈ W, ∀ g₂ ∈ W, R g₁ = R g₂ → g₁ ∈ B → g₂ ∈ B := by
    intro g₁ hg₁ g₂ hg₂ hRe hB₁
    have hl₁ := hlenW g₁ hg₁
    have hl₂ := hlenW g₂ hg₂
    have hv : ∀ g ∈ W, ∀ i j, (D g).internal U (q i) (q j) = Φ (restrictTo U g) (q i) (q j) ∧
        (D' g).internal U (q i) (q j) = Φ' (restrictTo U g) (q i) (q j) := by
      intro g hg i j
      rw [ContMetric.internal_eq_chainInf _ (hlenW g hg).1 U.isOpen,
        ContMetric.internal_eq_chainInf _ (hlenW g hg).2 U.isOpen]
      exact ⟨mem_iInter.1 (mem_iInter.1 hg.1.1 i) j, mem_iInter.1 (mem_iInter.1 hg.1.2 i) j⟩
    have hR1 : A₀ Φ (restrictTo U g₁) = A₀ Φ (restrictTo U g₂) := congrArg (fun x => x.1.1) hRe
    have hR2 : A₀ Φ' (restrictTo U g₁) = A₀ Φ' (restrictTo U g₂) :=
      congrArg (fun x => x.1.2) hRe
    have hR3 : (fun k => stopLastExit (sel a b g₁) (ball z (4 * r)) (tq k)) =
        (fun k => stopLastExit (sel a b g₂) (ball z (4 * r)) (tq k)) := congrArg (fun x => x.2) hRe
    have e1 := hext (D g₁) (D g₂) hl₁.1 hl₂.1 fun i j => by
      rw [(hv g₁ hg₁ i j).1, (hv g₂ hg₂ i j).1]; exact congrFun hR1 (i, j)
    have e2 := hext (D' g₁) (D' g₂) hl₁.2 hl₂.2 fun i j => by
      rw [(hv g₁ hg₁ i j).2, (hv g₂ hg₂ i j).2]; exact congrFun hR2 (i, j)
    have hpath : stopLastExit (sel a b g₁) (ball z (4 * r)) =
        stopLastExit (sel a b g₂) (ball z (4 * r)) :=
      Continuous.ext_on (denseRange_denseSeq unitInterval) (continuous_stopLastExit _ _)
        (continuous_stopLastExit _ _) (by rintro _ ⟨k, rfl⟩; exact congrFun hR3 k)
    show frkDistIn (D g₂) (D' g₂) cs Cs c₂ b₀ r z (stopLastExit (sel a b g₂) (ball z (4 * r)))
    rw [← hpath]
    exact frkDistIn_congr hr e1 e2 hB₁
  exact LocalEvent.aeEventIn_of_saturated hh.measurable hR hV (ae_of_all _ fun _ => rfl) hWm hB
    hYW hsat

/-- **GM Lemma 5.3** (l. 2775–2789), condition (2) of `GeoIterateHyp` for `𝔈` (`λ₄ = 4`): the
constant-invariant core of `𝔈_r^{𝕫,𝕨}(z)` is a.s. an event of
`σ(h|_{B_{4r}(z)}) ∨ σ(stopped geodesic)`, for bump functions supported in `B_{4r}(z)`. -/
theorem gm_L5_3 {γ : ℝ} {D D' : DistC → ContMetric} {c₀ c₀' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c₀) (hD' : IsWeakLQGMetric γ D' c₀')
    {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)}
    (hsel : ∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g)
    (hselm : ∀ a b : ℂ, Measurable (sel a b))
    {cs Cs c₂ b₀ Λ r : ℝ} (hcs : 0 < cs) (hcC : cs ≤ Cs) (hc₂ : 0 ≤ c₂) (hr : 0 < r)
    (hRat : RatiosAre D D' cs Cs) (G : Finset TestC)
    (z : ℂ) (hG : ∀ φ ∈ G, tsupport (φ : ℂ → ℝ) ⊆ ball z (4 * r)) (a b : ℂ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) :
    AEEventIn P (fieldSigma h (ballO z (4 * r)) ⊔ MeasurableSpace.comap (fun ω =>
        stopLastExit (sel a b (h ω)) (ball z (4 * r))) inferInstance)
      (h ⁻¹' constCore (frkE D D' sel cs Cs c₂ b₀ Λ r (G : Set TestC) z a b)) := by
  obtain ⟨F₁, hF₁, he₁⟩ :=
    gm_L5_3_meas hD hD' hsel hselm (b₀ := b₀) hcs hcC hc₂ hr hRat z a b hh
  have hF₂ := measurableSet_dirBound_fieldSigma h (ballO z (4 * r)) G hG Λ
  refine ⟨F₁ ∩ _, hF₁.inter (le_sup_left (a := fieldSigma h (ballO z (4 * r))) _ hF₂), ?_⟩
  filter_upwards [ae_mem_constCore_frkE_iff_stop hD hD' hsel hcs hcC hc₂ hr hRat (Λ := Λ)
    (G : Set TestC) z a b hh, he₁] with ω hω h1
  have h1' : _ ↔ ω ∈ F₁ := Iff.of_eq h1
  exact propext (by
    rw [mem_preimage, hω, mem_inter_iff, ← h1']
    rfl)

end LQGMetric.GM
