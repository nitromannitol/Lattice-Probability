/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7V12 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V11
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V6

/-!
# LM Lemma 5.3 restricted to `B_m`, jointly in the grid shift `θ`

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), Lemma 5.3 (`lem-internal-msrble`, l. 956–986), restricted as in D107
§3(i) (`decisions/DEC-107.md`): `F = D(z,w;B_m)` (chain formula `t17F`) is a.s. determined by
`θ` and the internal metrics `{D(·,·;S) : S ∈ t17Box ε R}` of the squares meeting `cl B_R ⊇ B_m`.
Per field `g` (`ν = κ_g`), with `θ ~ t17Λ` (uniform on `[0,1]²`) independent of `D ~ ν`:
`t17v_l53_joint : AEDeterminedBy (F ∘ D) (θ, Y_θ(D)) (t17Λ ⊗ ν)`.

Proof (LM l. 964–986): two conditionally independent samples `D, D'` given `(θ, Y_θ)`
(`condCopyMeasure`); a.s. both are length metrics, `D' ≤ C² D` ((5.6), `t17e_bilip_measure`), and
they have the same square metrics. For fixed `D` and a.e. `θ`, `t17v_l53_perD` (LM Lemma 5.2 for a
near-geodesic of `D`) gives `F(D') ≤ F(D)`; the exceptional set is handled by Tonelli over `θ`
with a measurable integrand (D107 §1.3). Since `F(D)` and `F(D')` have the same law, `F(D) = F(D')`
a.s. (`t17v_ae_eq_of_le_of_map_eq`, replacing "Symmetrically", l. 984), and the copy criterion
(`t17v_aeDet_comp`) concludes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric.LM

/-- the law of the grid shift `θ`: uniform on `[0,1]²` -/
def t17Λ : Measure (ℝ × ℝ) := (volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)

instance t17Λ_isProb : IsProbabilityMeasure t17Λ :=
  ⟨by rw [t17Λ, Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Icc]; simp⟩

lemma t17Λ_ae {p : ℝ × ℝ → Prop} (h : ∀ᵐ θ ∂(volume : Measure (ℝ × ℝ)), p θ) :
    ∀ᵐ θ ∂t17Λ, p θ := ae_restrict_of_ae h

lemma t17Λ_mem : ∀ᵐ θ ∂t17Λ, θ ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
  ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)

/-- a pointwise bound on the dense pairs extends to all pairs -/
lemma t17v_le_of_dense {d d' : ContMetric} {c : ℝ}
    (h : ∀ n, d'.1 (TopologicalSpace.denseSeq (ℂ × ℂ) n) ≤
      c * d.1 (TopologicalSpace.denseSeq (ℂ × ℂ) n)) :
    ∀ x y : ℂ, d'.1 (x, y) ≤ c * d.1 (x, y) := by
  have hcl : IsClosed {p : ℂ × ℂ | d'.1 p ≤ c * d.1 p} :=
    isClosed_le d'.1.continuous (continuous_const.mul d.1.continuous)
  have := closure_minimal (s := range (TopologicalSpace.denseSeq (ℂ × ℂ)))
    (by rintro _ ⟨n, rfl⟩; exact h n) hcl
  rw [(TopologicalSpace.denseRange_denseSeq (ℂ × ℂ)).closure_range] at this
  exact fun x y => this (mem_univ (x, y))

/-- **LM Lemma 5.3, restricted, jointly in `θ`** -/
theorem t17v_l53_joint (ν : Measure ContMetric) [IsProbabilityMeasure ν]
    (hL : ∀ᵐ d ∂ν, d.IsLength) {C : ℝ} (hC : 0 ≤ C)
    (hcopy : ∀ᵐ p ∂ν.prod ν, ∀ z w : ℂ, p.2.1 (z, w) ≤ C * p.1.1 (z, w))
    {m : ℕ} {R : ℝ} (hmR : (m : ℝ) ≤ R) {z w : ℂ} (hz : ‖z‖ < m) (hw : ‖w‖ < m)
    {ε : ℝ} (hε : 0 < ε) :
    AEDeterminedBy (fun p : (ℝ × ℝ) × ContMetric => (t17F m z w p.2).toReal)
      (fun p => (p.1, t17Y ε p.1 (t17Box ε R) p.2)) (t17Λ.prod ν) := by
  set s := t17Box ε R
  set μ := t17Λ.prod ν with hμ
  set X : (ℝ × ℝ) × ContMetric → (ℝ × ℝ) × (s → ℕ → ℝ≥0∞) :=
    fun p => (p.1, t17Y ε p.1 s p.2) with hXdef
  have hX : Measurable X := measurable_fst.prodMk (t17v_measurable_Y ε s)
  set F : ContMetric → ℝ := fun d => (t17F m z w d).toReal with hFdef
  have hFm : Measurable F := (measurable_t17F m z w).ennreal_toReal
  refine t17v_aeDet_comp (μ := μ) hX measurable_snd hFm ?_
  set Q := condCopyMeasure Prod.snd X μ hX with hQ
  have hμsnd : μ.map Prod.snd = ν := by
    rw [hμ, Measure.map_snd_prod, measure_univ, one_smul]
  have hQ1 : Q.map (fun q => q.1.2) = ν := by
    rw [show (fun q : ((ℝ × ℝ) × ContMetric) × ContMetric => q.1.2) = Prod.snd ∘ Prod.fst
      from rfl, ← Measure.map_map measurable_snd measurable_fst, hQ, condCopyMeasure_fst, hμsnd]
  have hQ2 : Q.map Prod.snd = ν := by
    have h2 := congrArg (fun π : Measure (((ℝ × ℝ) × (s → ℕ → ℝ≥0∞)) × ContMetric) =>
      π.map Prod.snd) (condCopyMeasure_map_snd (μ := μ) (Y := Prod.snd) hX measurable_snd)
    rw [Measure.map_map measurable_snd (show Measurable fun p : ((ℝ × ℝ) × ContMetric) × ContMetric =>
        (X p.1, p.2) from (hX.comp measurable_fst).prodMk measurable_snd),
      Measure.map_map measurable_snd (show Measurable fun ω : (ℝ × ℝ) × ContMetric =>
        (X ω, ω.2) from hX.prodMk measurable_snd)] at h2
    exact h2.trans hμsnd
  obtain ⟨M, hM, hML, hνM⟩ := t17v_measurable_length_subset ν hL
  have g1 : ∀ᵐ q ∂Q, q.1.2 ∈ M := by
    have h : ∀ᵐ y ∂(Q.map fun q => q.1.2), y ∈ M := by rw [hQ1]; exact hνM
    exact ae_of_ae_map (f := fun q : ((ℝ × ℝ) × ContMetric) × ContMetric => q.1.2)
      (measurable_snd.comp measurable_fst).aemeasurable h
  have g2 : ∀ᵐ q ∂Q, q.2 ∈ M := ae_of_ae_map measurable_snd.aemeasurable (by rw [hQ2]; exact hνM)
  have hpm : Measurable fun q : ((ℝ × ℝ) × ContMetric) × ContMetric => (q.1.2, q.2) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have g3 : ∀ᵐ q ∂Q, ∀ x y : ℂ, q.2.1 (x, y) ≤ C ^ 2 * q.1.2.1 (x, y) := by
    have h1 : (Q.map fun q => (q.1.2, q.2)).map Prod.fst = ν := by
      rw [Measure.map_map measurable_fst hpm]; exact hQ1
    have h2 : (Q.map fun q => (q.1.2, q.2)).map Prod.snd = ν := by
      rw [Measure.map_map measurable_snd hpm]; exact hQ2
    exact ae_of_ae_map hpm.aemeasurable (t17e_bilip_measure hC hcopy h1 h2)
  have g4 : ∀ᵐ q ∂Q, X (q.1.1, q.2) = X q.1 := by
    have hset : MeasurableSet {t : ((ℝ × ℝ) × (s → ℕ → ℝ≥0∞)) × ContMetric | X (t.1.1, t.2) = t.1} :=
      measurableSet_eq_fun (hX.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
        measurable_fst
    have hm2 : Measurable fun q : ((ℝ × ℝ) × ContMetric) × ContMetric => (X q.1, q.2) :=
      (hX.comp measurable_fst).prodMk measurable_snd
    have h0 : ∀ᵐ t ∂(Q.map fun q => (X q.1, q.2)), X (t.1.1, t.2) = t.1 := by
      rw [condCopyMeasure_map_snd (μ := μ) (Y := Prod.snd) hX measurable_snd]
      exact (ae_map_iff (hX.prodMk measurable_snd).aemeasurable hset).2
        (Filter.Eventually.of_forall fun ω => rfl)
    exact ae_of_ae_map hm2.aemeasurable h0
  -- the bad event
  set p := TopologicalSpace.denseSeq (ℂ × ℂ)
  set E : Set (((ℝ × ℝ) × ContMetric) × ContMetric) := {q | F q.1.2 < F q.2 ∧ q.2 ∈ M ∧
    q.1.2 ∈ M ∧ X (q.1.1, q.2) = X q.1 ∧ ∀ n, q.2.1 (p n) ≤ C ^ 2 * q.1.2.1 (p n)} with hEdef
  have hev : ∀ n, Measurable fun d : ContMetric => d.1 (p n) := fun n =>
    (continuous_eval_const _).measurable.comp measurable_subtype_coe
  have hB : MeasurableSet {q : ((ℝ × ℝ) × ContMetric) × ContMetric |
      ∀ n, q.2.1 (p n) ≤ C ^ 2 * q.1.2.1 (p n)} := by
    have : {q : ((ℝ × ℝ) × ContMetric) × ContMetric | ∀ n, q.2.1 (p n) ≤ C ^ 2 * q.1.2.1 (p n)} =
        ⋂ n, {q : ((ℝ × ℝ) × ContMetric) × ContMetric | q.2.1 (p n) ≤ C ^ 2 * q.1.2.1 (p n)} := by
      ext q; simp
    rw [this]
    exact MeasurableSet.iInter fun n => measurableSet_le ((hev n).comp measurable_snd)
      (measurable_const.mul ((hev n).comp (measurable_snd.comp measurable_fst)))
  have hE : MeasurableSet E :=
    (measurableSet_lt (hFm.comp (measurable_snd.comp measurable_fst))
      (hFm.comp measurable_snd)).inter ((measurable_snd hM).inter
      (((measurable_snd.comp measurable_fst) hM).inter ((measurableSet_eq_fun
      (hX.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      (hX.comp measurable_fst)).inter hB)))
  have hQE : Q E = 0 := by
    rw [hQ, condCopyMeasure, Measure.compProd_apply hE]
    refine (lintegral_prod_symm (μ := t17Λ) (ν := ν) _
      ((condCopyKernel Prod.snd X μ hX).measurable_kernel_prodMk_left hE).aemeasurable).trans ?_
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [hνM] with d hdM
    have hd := hML hdM
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [t17Λ_ae (t17v_l53_perD hd (c := C ^ 2) (sq_nonneg C) hmR hz hw hε),
      t17Λ_mem] with θ hθ hθm
    refine (measure_mono_null (fun d' hd' => ?_) measure_empty)
    obtain ⟨hlt, hd'M, -, hXeq, hbil⟩ := hd'
    exfalso
    have hd' := hML hd'M
    have hS : ∀ k ∈ s, ∀ u ∈ t17Square ε θ k, ∀ v ∈ t17Square ε θ k,
        d.internal (t17Square ε θ k) u v = d'.internal (t17Square ε θ k) u v := by
      intro k hk
      have h2 := congrArg Prod.snd hXeq
      have henc : t17eEnc (t17Square ε θ k) d' = t17eEnc (t17Square ε θ k) d :=
        congrFun h2 ⟨k, hk⟩
      exact t17v_internal_eq_of_enc hd hd' (t17_isOpen_square ε θ k) henc
    have hle := hθ hθm.1 hθm.2 d' (t17v_le_of_dense hbil) hS
    have hfin : t17F m z w d ≠ ⊤ := by
      rw [t17F, ← d.internal_eq_chainInf hd Metric.isOpen_ball]
      exact DFGPS.T12.internal_ne_top d hd Metric.isOpen_ball (convex_ball _ _).isPreconnected
        (mem_ball_zero_iff.2 hz) (mem_ball_zero_iff.2 hw)
    exact absurd (ENNReal.toReal_mono hfin hle) (not_le.2 hlt)
  have hle : ∀ᵐ q ∂Q, F q.2 ≤ F q.1.2 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hQE, g1, g2, g3, g4] with q hq h1 h2 h3 h4
    by_contra hc
    exact hq ⟨not_le.1 hc, h2, h1, h4, fun n => h3 _ _⟩
  have hmap : Q.map (fun q => F q.2) = Q.map (fun q => F q.1.2) := by
    rw [show (fun q : ((ℝ × ℝ) × ContMetric) × ContMetric => F q.2) = F ∘ Prod.snd from rfl,
      show (fun q : ((ℝ × ℝ) × ContMetric) × ContMetric => F q.1.2) = F ∘ fun q => q.1.2 from rfl,
      ← Measure.map_map hFm measurable_snd,
      ← Measure.map_map (g := F) (f := fun q : ((ℝ × ℝ) × ContMetric) × ContMetric => q.1.2) hFm
        (measurable_snd.comp measurable_fst), hQ1, hQ2]
  filter_upwards [t17v_ae_eq_of_le_of_map_eq (hFm.comp measurable_snd)
    (hFm.comp (measurable_snd.comp measurable_fst)) hle hmap] with q hq
  exact hq.symm

end LQGMetric.LM
