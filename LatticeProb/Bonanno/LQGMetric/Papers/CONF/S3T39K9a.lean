/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K9a at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K5g
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE5
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasD6

/-!
# CONF Theorem 3.9, packet J6d / D132 P-132A (N1): the analytic saturated set `t39k9Ban`

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1559–1561 ("`𝓘_k` is determined by `(𝓑^•_{s_k}, h|_{𝓑^•_{s_k}})`"); GM = arXiv:1905.00383,
(4.7) (`arcOf`) and l. 1705–1708 (the analytic-set argument for "determined by", formalized as
`GM.gm_arcRelAn`, `GM.gm_uMeas_of_an`). Decision DEC-132 §2 N1, §4.

* `t39k9PatFB`, `t39k9_patFB_eq`, `t39k9_patFB_meas`: the hit pattern of `𝓑^•_σ(z₀; d)` is a
  Borel function of `(d, σ)` (dense sequence, `GM.gm_filledBall_inter_open_iff`);
* `t39k9PatFr`, `t39k9_patFr_eq`, `t39k9_patFr_meas`: the same for `∂𝓑^•_σ` on `lenSet`
  (`GM.gmE_ball_inter_frontier_iff`);
* `t39k9_hit_meas`: `{(d, σ) | 𝓑^•_σ(d) ∩ V ≠ ∅}` is Borel for open `V`;
* `t39k9_effros_prod_borel_eq`: `effrosSigma ⊗ Borel = comap (Pat × id)`;
* `t39k9Ban` (the analytic form of `t39k5B`) and **`t39k9_Ban_umeas`**: on `lenSet` it is the
  projection of a Borel set, hence universally measurable (`UMeasurableSet.setOf_exists`, as in
  `GM.gm_uMeas_of_an`).
The proofs of the four measurability steps follow the verified probe of DEC-132 §7.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter TopologicalSpace

namespace LQGMetric.CONF

open Blueprint LocalEvent GM

open Classical in
/-- Borel hit pattern of `𝓑^•_σ(z₀; d)`; `= t39k5Pat (filledBall d z₀ σ)` (`t39k9_patFB_eq`) -/
def t39k9PatFB (z₀ : ℂ) (q : ContMetric × ℝ) : ℕ → Bool := fun j =>
  decide (∃ i, denseSeq ℂ i ∈ ball (t39jBc j) (2 * t39jBr j) ∧
    denseSeq ℂ i ∈ filledBall q.1 z₀ q.2)

theorem t39k9_patFB_eq (z₀ : ℂ) (d : ContMetric) (σ : ℝ) :
    t39k9PatFB z₀ (d, σ) = t39k5Pat (filledBall d z₀ σ) := by
  funext j
  simp only [t39k9PatFB, t39k5Pat]
  rw [gm_filledBall_inter_open_iff d z₀ σ isOpen_ball]

theorem t39k9_patFB_meas (z₀ : ℂ) : Measurable (t39k9PatFB z₀) := by
  classical
  refine measurable_pi_iff.2 fun j => measurable_to_bool ?_
  have : (fun q : ContMetric × ℝ => t39k9PatFB z₀ q j) ⁻¹' {true} =
      ⋃ i : ℕ, {q : ContMetric × ℝ | denseSeq ℂ i ∈ ball (t39jBc j) (2 * t39jBr j) ∧
        (q.1, q.2, denseSeq ℂ i) ∈ {p : ContMetric × ℝ × ℂ | p.2.2 ∈ filledBall p.1 z₀ p.2.1}} := by
    ext q; simp [t39k9PatFB]
  rw [this]
  refine MeasurableSet.iUnion fun i => ?_
  by_cases hi : denseSeq ℂ i ∈ ball (t39jBc j) (2 * t39jBr j)
  · simp only [hi, true_and]
    exact (gmE_measurableSet_filledBall z₀).preimage
      (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  · simp only [hi, false_and, Set.ofPred_false]; exact MeasurableSet.empty

open Classical in
/-- Borel hit pattern of `∂𝓑^•_σ(z₀; d)`; `= t39k5Pat (frontier (filledBall d z₀ σ))` on
`lenSet` (`t39k9_patFr_eq`) -/
def t39k9PatFr (z₀ : ℂ) (q : ContMetric × ℝ) : ℕ → Bool := fun j =>
  decide (¬ gmBallOffF q.1 z₀ q.2 (t39jBc j) (2 * t39jBr j))

theorem t39k9_patFr_eq {d : ContMetric} (hd : d ∈ lenSet) (z₀ : ℂ) (σ : ℝ) :
    t39k9PatFr z₀ (d, σ) = t39k5Pat (frontier (filledBall d z₀ σ)) := by
  classical
  funext j
  simp only [t39k9PatFr, t39k5Pat]
  rw [← gmE_ball_inter_frontier_iff hd z₀ σ (t39jBc j) (by have := t39jBr_pos j; positivity)]
  exact Bool.decide_congr (by rw [inter_comm, nonempty_iff_ne_empty])

theorem t39k9_patFr_meas (z₀ : ℂ) : Measurable (t39k9PatFr z₀) := by
  classical
  refine measurable_pi_iff.2 fun j => measurable_to_bool ?_
  have : (fun q : ContMetric × ℝ => t39k9PatFr z₀ q j) ⁻¹' {true} =
      {q : ContMetric × ℝ | gmBallOffF q.1 z₀ q.2 (t39jBc j) (2 * t39jBr j)}ᶜ := by
    ext q; simp [t39k9PatFr]
  rw [this]
  exact (measurableSet_setOfPred.2
    (gmE_measurable_ballOffF_comp measurable_fst measurable_snd z₀ _ _)).compl

/-- **hit events of the filled ball are Borel in `(d, σ)`** -/
theorem t39k9_hit_meas (z₀ : ℂ) {V : Set ℂ} (hV : IsOpen V) :
    MeasurableSet {q : ContMetric × ℝ | (filledBall q.1 z₀ q.2 ∩ V).Nonempty} := by
  have e : {q : ContMetric × ℝ | (filledBall q.1 z₀ q.2 ∩ V).Nonempty} =
      ⋃ i : ℕ, {q : ContMetric × ℝ | denseSeq ℂ i ∈ V ∧
        (q.1, q.2, denseSeq ℂ i) ∈ {p : ContMetric × ℝ × ℂ | p.2.2 ∈ filledBall p.1 z₀ p.2.1}} := by
    ext q
    simp only [mem_ofPred_eq, mem_iUnion]
    exact gm_filledBall_inter_open_iff q.1 z₀ q.2 hV
  rw [e]
  refine MeasurableSet.iUnion fun i => ?_
  by_cases hi : denseSeq ℂ i ∈ V
  · simp only [hi, true_and]
    exact (gmE_measurableSet_filledBall z₀).preimage
      (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  · simp only [hi, false_and, Set.ofPred_false]; exact MeasurableSet.empty

/-- `effrosSigma ⊗ Borel` is the pull-back of `Pat × id` -/
theorem t39k9_effros_prod_borel_eq :
    (@Prod.instMeasurableSpace (Set ℂ) ℂ effrosSigma inferInstance) =
      MeasurableSpace.comap (Prod.map t39k5Pat id) inferInstance := by
  rw [t39k5_effros_eq_comap]
  show (MeasurableSpace.comap t39k5Pat _).comap Prod.fst ⊔
      (inferInstance : MeasurableSpace ℂ).comap Prod.snd = _
  rw [MeasurableSpace.comap_comp]
  show _ = MeasurableSpace.comap (Prod.map t39k5Pat id)
    ((MeasurableSpace.comap Prod.fst _) ⊔ (MeasurableSpace.comap Prod.snd _))
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
  rfl

/-- the analytic form of `t39k5B` (GM (4.7), GM l. 1705–1708) -/
def t39k9Ban (D : DistC → ContMetric) (z₀ : ℂ) (A : Set ℂ) (arcs : Set ℂ → Set ℂ) (U : Set ℂ) :
    Set (DistC × ((ℕ → Bool) × (ℕ → Bool))) :=
  {y | ∃ σ σ' : ℝ, 0 < σ' ∧ σ' ≤ σ ∧ t39k5Pat (filledBall (D y.1) z₀ σ) = y.2.1 ∧
    t39k5Pat (filledBall (D y.1) z₀ σ') = y.2.2 ∧
    (∃ n : ℕ, filledBall (D y.1) z₀ σ ∩ Metric.thickening ((n : ℝ) + 1)⁻¹ Aᶜ = ∅) ∧
    ∃ x ∈ arcs (frontier (filledBall (D y.1) z₀ σ')), ∃ y' ∈ U,
      x ∈ GM.confPts (D y.1) z₀ σ' σ ∧ y' ∈ GM.arcOf (D y.1) z₀ σ x}

/-- `𝓑^•_σ(d) ∩ thickening Aᶜ = ∅` is Borel in `(d, σ)` -/
theorem t39k9_thick_meas (z₀ : ℂ) (A : Set ℂ) (n : ℕ) :
    MeasurableSet {q : ContMetric × ℝ |
      filledBall q.1 z₀ q.2 ∩ Metric.thickening ((n : ℝ) + 1)⁻¹ Aᶜ = ∅} := by
  have e : {q : ContMetric × ℝ |
      filledBall q.1 z₀ q.2 ∩ Metric.thickening ((n : ℝ) + 1)⁻¹ Aᶜ = ∅} =
      {q : ContMetric × ℝ |
        (filledBall q.1 z₀ q.2 ∩ Metric.thickening ((n : ℝ) + 1)⁻¹ Aᶜ).Nonempty}ᶜ := by
    ext q
    simp only [mem_ofPred_eq, mem_compl_iff, not_nonempty_iff_eq_empty]
  rw [e]
  exact (t39k9_hit_meas z₀ isOpen_thickening).compl

/-- **N1: `t39k9Ban` is universally measurable on `lenSet`** (GM l. 1705–1708) -/
theorem t39k9_Ban_umeas {D : DistC → ContMetric} (hDm : Measurable D) (z₀ : ℂ) (A : Set ℂ)
    {arcs : Set ℂ → Set ℂ}
    (harcsM : MeasurableSet[@Prod.instMeasurableSpace (Set ℂ) ℂ effrosSigma inferInstance]
      {p : Set ℂ × ℂ | p.2 ∈ arcs p.1})
    {U : Set ℂ} (hU : MeasurableSet U) :
    UMeasurableSet ((D ⁻¹' lenSet) ×ˢ (univ : Set ((ℕ → Bool) × (ℕ → Bool))) ∩
      t39k9Ban D z₀ A arcs U) := by
  obtain ⟨β, mβ, sbβ, S, hS, hSeq⟩ := gm_arcRelAn z₀
  have hM := harcsM
  rw [t39k9_effros_prod_borel_eq] at hM
  obtain ⟨M', hM', hpre⟩ := hM
  have hmem : ∀ (Γ : Set ℂ) (x : ℂ), x ∈ arcs Γ ↔ (t39k5Pat Γ, x) ∈ M' := fun Γ x => by
    have : (Γ, x) ∈ Prod.map t39k5Pat id ⁻¹' M' ↔ (Γ, x) ∈ {p : Set ℂ × ℂ | p.2 ∈ arcs p.1} := by
      rw [hpre]
    exact this.symm
  -- coordinates of `(y, ((σ, σ'), (x, w), b))`
  have fD : Measurable fun q : (DistC × ((ℕ → Bool) × (ℕ → Bool))) × ((ℝ × ℝ) × (ℂ × ℂ) × β) =>
      D q.1.1 := hDm.comp (measurable_fst.comp measurable_fst)
  have fσ : Measurable fun q : (DistC × ((ℕ → Bool) × (ℕ → Bool))) × ((ℝ × ℝ) × (ℂ × ℂ) × β) =>
      q.2.1.1 := measurable_fst.comp (measurable_fst.comp measurable_snd)
  have fσ' : Measurable fun q : (DistC × ((ℕ → Bool) × (ℕ → Bool))) × ((ℝ × ℝ) × (ℂ × ℂ) × β) =>
      q.2.1.2 := measurable_snd.comp (measurable_fst.comp measurable_snd)
  have fζ1 : Measurable fun q : (DistC × ((ℕ → Bool) × (ℕ → Bool))) × ((ℝ × ℝ) × (ℂ × ℂ) × β) =>
      q.1.2.1 := measurable_fst.comp (measurable_snd.comp measurable_fst)
  have fζ2 : Measurable fun q : (DistC × ((ℕ → Bool) × (ℕ → Bool))) × ((ℝ × ℝ) × (ℂ × ℂ) × β) =>
      q.1.2.2 := measurable_snd.comp (measurable_snd.comp measurable_fst)
  have fx : Measurable fun q : (DistC × ((ℕ → Bool) × (ℕ → Bool))) × ((ℝ × ℝ) × (ℂ × ℂ) × β) =>
      q.2.2.1.1 := measurable_fst.comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have fw : Measurable fun q : (DistC × ((ℕ → Bool) × (ℕ → Bool))) × ((ℝ × ℝ) × (ℂ × ℂ) × β) =>
      q.2.2.1.2 := measurable_snd.comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have fb : Measurable fun q : (DistC × ((ℕ → Bool) × (ℕ → Bool))) × ((ℝ × ℝ) × (ℂ × ℂ) × β) =>
      q.2.2.2 := measurable_snd.comp (measurable_snd.comp measurable_snd)
  have m1 := measurableSet_setOfPred.1 (measurableSet_lenSet.preimage fD)
  have m2 := measurableSet_setOfPred.1 (measurableSet_lt (measurable_const (a := (0 : ℝ))) fσ')
  have m3 := measurableSet_setOfPred.1 (measurableSet_le fσ' fσ)
  have m4 := measurableSet_setOfPred.1
    (measurableSet_eq_fun ((t39k9_patFB_meas z₀).comp (fD.prodMk fσ)) fζ1)
  have m5 := measurableSet_setOfPred.1
    (measurableSet_eq_fun ((t39k9_patFB_meas z₀).comp (fD.prodMk fσ')) fζ2)
  have m6s : MeasurableSet {q : (DistC × ((ℕ → Bool) × (ℕ → Bool))) × ((ℝ × ℝ) × (ℂ × ℂ) × β) |
      ∃ n : ℕ, filledBall (D q.1.1) z₀ q.2.1.1 ∩ Metric.thickening ((n : ℝ) + 1)⁻¹ Aᶜ = ∅} := by
    rw [ofPred_exists]
    refine MeasurableSet.iUnion fun n => ?_
    have := (t39k9_thick_meas z₀ A n).preimage (fD.prodMk fσ)
    simpa only [preimage_ofPred_eq] using this
  have m6 := measurableSet_setOfPred.1 m6s
  have m7 := measurableSet_setOfPred.1
    (hM'.preimage (((t39k9_patFr_meas z₀).comp (fD.prodMk fσ')).prodMk fx))
  have m8 := measurableSet_setOfPred.1 (hU.preimage fw)
  have m9 := measurableSet_setOfPred.1
    (hS.preimage (((fD.prodMk (fσ'.prodMk fσ)).prodMk (fx.prodMk fw)).prodMk fb))
  have hS' := measurableSet_setOfPred.2
    (m1.and (m2.and (m3.and (m4.and (m5.and (m6.and (m7.and (m8.and m9))))))))
  refine (congrArg UMeasurableSet ?_).mp (UMeasurableSet.setOf_exists hS')
  ext y
  simp only [mem_ofPred_eq, mem_inter_iff, mem_prod, mem_preimage, mem_univ, and_true,
    Function.comp_apply, t39k9Ban]
  constructor
  · rintro ⟨⟨⟨σ, σ'⟩, ⟨x, w⟩, b⟩, hy, h0, hle, hP1, hP2, hth, hx, hw, hb⟩
    refine ⟨hy, σ, σ', h0, hle, by rw [← t39k9_patFB_eq]; exact hP1,
      by rw [← t39k9_patFB_eq]; exact hP2, hth, x, ?_, w, hw,
      (hSeq ((D y.1, σ', σ), x, w) hy).2 ⟨b, hb⟩⟩
    rw [hmem, ← t39k9_patFr_eq hy]
    exact hx
  · rintro ⟨hy, σ, σ', h0, hle, hP1, hP2, hth, x, hx, w, hw, hxc⟩
    obtain ⟨b, hb⟩ := (hSeq ((D y.1, σ', σ), x, w) hy).1 hxc
    refine ⟨((σ, σ'), (x, w), b), hy, h0, hle, by rw [t39k9_patFB_eq]; exact hP1,
      by rw [t39k9_patFB_eq]; exact hP2, hth, ?_, hw, hb⟩
    rw [t39k9_patFr_eq hy, ← hmem]
    exact hx

end LQGMetric.CONF
