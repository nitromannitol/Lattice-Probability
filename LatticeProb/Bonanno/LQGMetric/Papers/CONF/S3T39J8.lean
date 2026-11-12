/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39J8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J7
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114S2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9, packet J6 (part 3): measurability of the radii `s_k` on a complete space

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
(3.13) C:1258, (3.16) C:1289, (3.17) C:1295, radii `s_k` C:1543–1556; DEC-120 §4 (S9: on a
complete space). Measurability in the ambient σ-algebra `mΩ` only (the `𝓕_k`-measurability is
`T39J6Rest`). Own routine argument (CONF does not discuss measurability):

* `t39j8_measurableSet_confE`: `E_r(z)` is measurable (null-measurable by Axiom II,
  `conf36_confEU_nullMeas`, P2-D114; complete space);
* `t39j8_measurable_confRho`: `ρ^n_r(z)` is measurable (countable infima);
* `t39j8_measurable_hit`, `t39j8_measurable_infEDist`: hit events and `dist(x, 𝓑^•_{s})` for a
  measurable radius `s` (`gm_setSigma_filledBall_le`, L47MeasF);
* `t39j8_measurable_confRK`: `R^ε_𝕣(𝓑^•_s)` (a countable supremum over the grid);
* **`t39j8_measurable_confSigma`**: `ω ↦ σ^ε_{s(ω),𝕣}(ω)` is measurable
  (`{σ < x} = ⋃_{q ∈ ℚ} {s < q, q < x, B_{R}(𝓑^•_s) ⊆ 𝓑^•_q}`, the inclusion of an open set in a
  closed one read off `denseSeq`);
* **`t39j8_measurable_succ`**: `s_k`, `n_k` measurable ⇒ `s_{k+1}` measurable.
-/

noncomputable section

open MeasureTheory Set Metric Filter TopologicalSpace
open scoped ENNReal

namespace LQGMetric
namespace CONF

open Blueprint GM

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] [P.IsComplete]
  {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {h : Ω → DistC}

theorem t39j8_measurableSet_confE (hD : IsWeakLQGMetric γ D c) (hh : IsWholePlaneGFF h P)
    (p : CONFParams) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    MeasurableSet (confE (xiGamma γ) c D P h p r z) :=
  MeasurableSet.iInter fun T => MeasurableSet.iInter fun _ =>
    (conf36_confEU_nullMeas hD hh p hr z T).measurable_of_complete

theorem t39j8_measurable_confRho (hD : IsWeakLQGMetric γ D c) (hh : IsWholePlaneGFF h P)
    (p : CONFParams) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ n, Measurable (confRho (xiGamma γ) c D P h p r z n)
  | 0 => measurable_const
  | n + 1 => by
    classical
    have ih := t39j8_measurable_confRho hD hh p hr z n
    refine Measurable.iInf fun k => ?_
    set S := {ω | 6 * confRho (xiGamma γ) c D P h p r z n ω ≤ ENNReal.ofReal ((2 : ℝ) ^ k * r)} ∩
      confE (xiGamma γ) c D P h p ((2 : ℝ) ^ k * r) z
    have hS : MeasurableSet S := (measurableSet_le (measurable_const.mul ih) measurable_const).inter
      (t39j8_measurableSet_confE hD hh p (by positivity) z)
    have e : (fun ω => ⨅ (_ : 6 * confRho (xiGamma γ) c D P h p r z n ω ≤
        ENNReal.ofReal ((2 : ℝ) ^ k * r)) (_ : ω ∈ confE (xiGamma γ) c D P h p
          ((2 : ℝ) ^ k * r) z), ENNReal.ofReal ((2 : ℝ) ^ k * r)) =
        S.piecewise (fun _ => ENNReal.ofReal ((2 : ℝ) ^ k * r)) (fun _ => ⊤) := by
      funext ω
      by_cases hω : ω ∈ S
      · rw [S.piecewise_eq_of_mem _ _ hω, iInf_pos (show 6 * confRho (xiGamma γ) c D P h p r z n ω ≤
          ENNReal.ofReal ((2 : ℝ) ^ k * r) from hω.1), iInf_pos (show ω ∈ confE (xiGamma γ) c D P h p
          ((2 : ℝ) ^ k * r) z from hω.2)]
      · rw [S.piecewise_eq_of_notMem _ _ hω]
        refine iInf_eq_top.2 fun h1 => iInf_eq_top.2 fun h2 => (hω ⟨h1, h2⟩).elim
    rw [e]
    exact Measurable.piecewise hS measurable_const measurable_const

omit [IsProbabilityMeasure P] in
theorem t39j8_measurable_hit [IsFiniteMeasure P] (hDm : Measurable fun ω => D (h ω))
    {s : Ω → ℝ} (hs : Measurable s) (z₀ : ℂ) {U : Set ℂ} (hU : IsOpen U) :
    MeasurableSet {ω | (filledBall (D (h ω)) z₀ (s ω) ∩ U).Nonempty} :=
  gm_setSigma_filledBall_le (P := P) hDm hs z₀ _
    (MeasurableSpace.measurableSet_generateFrom ⟨U, hU, rfl⟩)

omit [IsProbabilityMeasure P] in
theorem t39j8_measurable_infEDist [IsFiniteMeasure P] (hDm : Measurable fun ω => D (h ω))
    {s : Ω → ℝ} (hs : Measurable s) (z₀ x : ℂ) :
    Measurable fun ω => Metric.infEDist x (filledBall (D (h ω)) z₀ (s ω)) := by
  refine measurable_of_Iio fun t => ?_
  have e : (fun ω => Metric.infEDist x (filledBall (D (h ω)) z₀ (s ω))) ⁻¹' Iio t =
      {ω | (filledBall (D (h ω)) z₀ (s ω) ∩ Metric.eball x t).Nonempty} := by
    ext ω
    simp only [mem_preimage, mem_Iio, mem_setOf_eq, Metric.infEDist_lt_iff]
    constructor
    · rintro ⟨y, hy, hxy⟩; exact ⟨y, hy, by rwa [Metric.mem_eball, edist_comm]⟩
    · rintro ⟨y, hy, hxy⟩; exact ⟨y, hy, by rwa [Metric.mem_eball, edist_comm] at hxy⟩
  rw [e]
  exact t39j8_measurable_hit (P := P) hDm hs z₀ Metric.isOpen_eball

/-- the grid supremum as a supremum over `ℤ²` -/
theorem t39j8_iSup_grid (m ρ : ℝ) (K : Set ℂ) (f : ℂ → ℝ≥0∞) :
    (⨆ z ∈ gridPts m ∩ thickening ρ K, f z) =
      ⨆ (ab : ℤ × ℤ) (_ : (⟨ab.1 * m, ab.2 * m⟩ : ℂ) ∈ thickening ρ K),
        f ⟨ab.1 * m, ab.2 * m⟩ := by
  refine le_antisymm (iSup₂_le fun z hz => ?_) (iSup₂_le fun ab hab => ?_)
  · obtain ⟨⟨a, b, rfl⟩, hz⟩ := hz
    exact le_iSup₂_of_le (a, b) hz le_rfl
  · exact le_iSup₂_of_le (f := fun z (_ : z ∈ gridPts m ∩ thickening ρ K) => f z)
      (⟨ab.1 * m, ab.2 * m⟩ : ℂ) ⟨⟨ab.1, ab.2, rfl⟩, hab⟩ le_rfl

theorem t39j8_measurable_confRK (hD : IsWeakLQGMetric γ D c) (hh : IsWholePlaneGFF h P)
    (p : CONFParams) {R ε : ℝ} (hεR : 0 < ε * R) {s : Ω → ℝ} (hs : Measurable s) (z₀ : ℂ) :
    Measurable fun ω => confRK (xiGamma γ) c D P h p R ε (filledBall (D (h ω)) z₀ (s ω)) ω := by
  classical
  have hDm : Measurable fun ω => D (h ω) := hD.measurable.comp hh.measurable
  unfold confRK
  simp_rw [t39j8_iSup_grid]
  refine (measurable_const.mul (Measurable.iSup fun ab => ?_)).add measurable_const
  set w : ℂ := ⟨ab.1 * (ε * R / 4), ab.2 * (ε * R / 4)⟩
  set H := {ω | w ∈ thickening (ε * R) (filledBall (D (h ω)) z₀ (s ω))}
  have hH : MeasurableSet H := by
    have e : H = {ω | (filledBall (D (h ω)) z₀ (s ω) ∩ ball w (ε * R)).Nonempty} := by
      ext ω
      simp only [H, mem_setOf_eq, mem_thickening_iff]
      constructor
      · rintro ⟨y, hy, hd⟩; exact ⟨y, hy, by rwa [mem_ball, dist_comm]⟩
      · rintro ⟨y, hy, hd⟩; exact ⟨y, hy, by rwa [mem_ball, dist_comm] at hd⟩
    rw [e]; exact t39j8_measurable_hit (P := P) hDm hs z₀ isOpen_ball
  have e : (fun ω => ⨆ (_ : w ∈ thickening (ε * R) (filledBall (D (h ω)) z₀ (s ω))),
      confRho (xiGamma γ) c D P h p (ε * R) w (confN p ε) ω) =
      H.piecewise (confRho (xiGamma γ) c D P h p (ε * R) w (confN p ε)) (fun _ => 0) := by
    funext ω
    by_cases hω : ω ∈ H
    · rw [H.piecewise_eq_of_mem _ _ hω,
        iSup_pos (show w ∈ thickening (ε * R) (filledBall (D (h ω)) z₀ (s ω)) from hω)]
    · rw [H.piecewise_eq_of_notMem _ _ hω,
        iSup_neg (show w ∉ thickening (ε * R) (filledBall (D (h ω)) z₀ (s ω)) from hω)]; rfl
  rw [e]
  exact Measurable.piecewise hH (t39j8_measurable_confRho hD hh p hεR w _) measurable_const

/-- an open set lies in a closed set iff its points of `denseSeq` do -/
theorem t39j8_open_subset_closed_iff {O F : Set ℂ} (hO : IsOpen O) (hF : IsClosed F) :
    O ⊆ F ↔ ∀ i, denseSeq ℂ i ∈ O → denseSeq ℂ i ∈ F := by
  refine ⟨fun h i hi => h hi, fun h => ?_⟩
  refine ((denseRange_denseSeq ℂ).open_subset_closure_inter hO).trans ?_
  refine hF.closure_subset_iff.2 ?_
  rintro _ ⟨hx, i, rfl⟩
  exact h i hx

/-- **`ω ↦ σ^ε_{s(ω),𝕣}(ω)` is measurable** (complete space, `s` measurable) -/
theorem t39j8_measurable_confSigma (hD : IsWeakLQGMetric γ D c) (hh : IsWholePlaneGFF h P)
    (p : CONFParams) (z₀ : ℂ) {R ε : ℝ} (hεR : 0 < ε * R) {s : Ω → ℝ} (hs : Measurable s) :
    Measurable fun ω => confSigma (xiGamma γ) c D P h p z₀ R ε (s ω) ω := by
  have hDm : Measurable fun ω => D (h ω) := hD.measurable.comp hh.measurable
  set ρ := fun ω => confRK (xiGamma γ) c D P h p R ε (filledBall (D (h ω)) z₀ (s ω)) ω
  have hρ : Measurable ρ := t39j8_measurable_confRK hD hh p hεR hs z₀
  set C : ℝ → Set Ω := fun q => {ω | enbhd (ρ ω) (filledBall (D (h ω)) z₀ (s ω)) ⊆
    filledBall (D (h ω)) z₀ q}
  have hC : ∀ q, MeasurableSet (C q) := by
    intro q
    have e : C q = ⋂ i, ({ω | Metric.infEDist (denseSeq ℂ i) (filledBall (D (h ω)) z₀ (s ω)) <
        ρ ω}ᶜ ∪ {ω | denseSeq ℂ i ∈ filledBall (D (h ω)) z₀ q}) := by
      ext ω
      simp only [C, mem_setOf_eq, mem_iInter, mem_union, mem_compl_iff]
      rw [t39j8_open_subset_closed_iff (O := enbhd (ρ ω) (filledBall (D (h ω)) z₀ (s ω)))
        (isOpen_lt Metric.continuous_infEDist continuous_const) (gm_filledBall_isClosed _ _ _)]
      refine forall_congr' fun i => ?_
      simp only [enbhd, mem_setOf_eq]
      tauto
    rw [e]
    refine MeasurableSet.iInter fun i => (measurableSet_lt
      (t39j8_measurable_infEDist (P := P) hDm hs z₀ _) hρ).compl.union ?_
    have hc : MeasurableSet {ω | denseSeq ℂ i ∉ filledBall (D (h ω)) z₀ q} :=
      gm_measurableSet_of_ae_eq_um (P := P) (hDm.prodMk measurable_const)
        (gm_uMeasurableSet_notMem_filledBall z₀ (denseSeq ℂ i)) EventuallyEq.rfl
    convert hc.compl using 1
    ext ω; simp
  refine measurable_of_Iio fun x => ?_
  have e : (fun ω => confSigma (xiGamma γ) c D P h p z₀ R ε (s ω) ω) ⁻¹' Iio x =
      ⋃ q : ℚ, ({ω | s ω < q} ∩ {_ω | ENNReal.ofReal q < x} ∩ C q) := by
    ext ω
    simp only [mem_preimage, mem_Iio, mem_iUnion, mem_inter_iff, mem_setOf_eq, confSigma]
    constructor
    · intro hlt
      obtain ⟨s', hlt⟩ := iInf_lt_iff.1 hlt
      obtain ⟨hss', hlt⟩ := iInf_lt_iff.1 hlt
      obtain ⟨hsub, hlt⟩ := iInf_lt_iff.1 hlt
      -- a rational `q > s'` with `ofReal q < x`
      have hx0 : 0 < x := (zero_le).trans_lt hlt
      obtain ⟨t, hst, htx⟩ : ∃ t : ℝ, s' < t ∧ ENNReal.ofReal t < x := by
        by_cases hxt : x = ⊤
        · exact ⟨s' + 1, by linarith, hxt ▸ ENNReal.ofReal_lt_top⟩
        · have hxr : 0 < x.toReal := ENNReal.toReal_pos hx0.ne' hxt
          have hs'x : s' < x.toReal := by
            rcases le_or_gt s' 0 with h0 | h0
            · exact h0.trans_lt hxr
            · exact (ENNReal.ofReal_lt_iff_lt_toReal h0.le hxt).1 hlt
          refine ⟨(s' + x.toReal) / 2, by linarith, ?_⟩
          conv_rhs => rw [← ENNReal.ofReal_toReal hxt]
          exact (ENNReal.ofReal_lt_ofReal_iff hxr).2 (by linarith)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hst
      refine ⟨q, ⟨⟨hss'.trans hq1, ?_⟩, ?_⟩⟩
      · exact (ENNReal.ofReal_le_ofReal hq2.le).trans_lt htx
      · exact hsub.trans (gm_filledBall_mono _ _ hq1.le)
    · rintro ⟨q, ⟨hsq, hqx⟩, hCq⟩
      exact (iInf_le_of_le (q : ℝ) (iInf_le_of_le hsq (iInf_le_of_le hCq le_rfl))).trans_lt hqx
  rw [e]
  exact MeasurableSet.iUnion fun q =>
    ((measurableSet_lt hs measurable_const).inter (MeasurableSet.const _)).inter (hC q)

/-- **`s_{k+1}` is measurable** when `s_k` and `n_k` are -/
theorem t39j8_measurable_succ (hD : IsWeakLQGMetric γ D c) (hh : IsWholePlaneGFF h P)
    (p : CONFParams) (z₀ : ℂ) {R : ℝ} (hR : 0 < R) {ι : Type} [Fintype ι]
    (I₀ : ι → Ω → Set ℂ) (τ : Ω → ℝ) (k : ℕ)
    (hs : Measurable (t39j7S γ D c p P h z₀ R I₀ τ k))
    (hn : Measurable (t39j7N D h z₀ I₀ (t39j7S γ D c p P h z₀ R I₀ τ k))) :
    Measurable (t39j7S γ D c p P h z₀ R I₀ τ (k + 1)) := by
  have hF : Measurable fun q : Ω × ℕ => (confSigma (xiGamma γ) c D P h p z₀ R
      ((2 : ℝ)⁻¹ ^ q.2) (t39j7S γ D c p P h z₀ R I₀ τ k q.1) q.1).toReal :=
    measurable_from_prod_countable_left fun j => by
      have hj : 0 < (2 : ℝ)⁻¹ ^ j * R := by positivity
      have := (t39j8_measurable_confSigma (ε := (2 : ℝ)⁻¹ ^ j)
        (s := t39j7S γ D c p P h z₀ R I₀ τ k) hD hh p z₀ hj hs).ennreal_toReal
      exact this
  have hg : Measurable fun ω =>
      (ω, t39gExp (t39j7N D h z₀ I₀ (t39j7S γ D c p P h z₀ R I₀ τ k) ω)) :=
    measurable_id.prodMk ((measurable_from_nat (f := t39gExp)).comp hn)
  have key := hF.comp hg
  rw [t39j7S.eq_2]
  exact key

end CONF
end LQGMetric
