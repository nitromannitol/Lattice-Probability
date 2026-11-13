/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.PathInf at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SLUMetricAPI
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase.FellBase
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect




 




set_option autoImplicit false
noncomputable section

open Set Filter Topology
open BoundedContinuousFunction
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace Uniqueness.Toolkit.PathInfimum

theorem eq_of_euclidean_and_metric_limits (D : LSCMetric) {u : ℕ → ℂ} {w x : ℂ}
    (hw : Tendsto u atTop (nhds w))
    (hd : Tendsto (fun n => D.pt (u n)) atTop (nhds (D.pt x))) : w = x := by
  have hd0 : Tendsto (fun n => D (u n, x)) atTop (nhds 0) := by
    exact (tendsto_iff_edist_tendsto_0).mp hd
  have hpair : Tendsto (fun n => ((u n, x), D (u n, x))) atTop
      (nhds ((w, x), (0 : ENNReal))) :=
    (hw.prodMk_nhds tendsto_const_nhds).prodMk_nhds hd0
  have hle : D (w, x) ≤ 0 :=
    D.lowerSemicontinuous.isClosed_epigraph.mem_of_tendsto hpair
      (Eventually.of_forall fun n => (show D (u n, x) ≤ D (u n, x) from le_rfl))
  exact D.isExtMetric.2.1 w x (le_zero_iff.mp hle)

theorem compact_separated_pairs_pos (D : LSCMetric) {K : Set ℂ}
    (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ)
    (hne : ({p : ℂ × ℂ | p.1 ∈ K ∧ p.2 ∈ K ∧ δ ≤ dist p.1 p.2}).Nonempty) :
    ∃ c : ENNReal, 0 < c ∧ ∀ p : ℂ × ℂ,
      p.1 ∈ K → p.2 ∈ K → δ ≤ dist p.1 p.2 → c ≤ D p := by
  let S : Set (ℂ × ℂ) := {p | p.1 ∈ K ∧ p.2 ∈ K ∧ δ ≤ dist p.1 p.2}
  have hS : IsCompact S := by
    have hclosed : IsClosed {p : ℂ × ℂ | δ ≤ dist p.1 p.2} := by
      exact isClosed_le continuous_const continuous_dist
    have hSeq : S = (K ×ˢ K) ∩ {p : ℂ × ℂ | δ ≤ dist p.1 p.2} := by
      ext p
      simp only [S, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod]
      tauto
    rw [hSeq]
    exact (hK.prod hK).inter_right hclosed
  obtain ⟨p, hp, hmin⟩ :=
    (D.lowerSemicontinuous.lowerSemicontinuousOn S).exists_isMinOn hne hS
  have hpne : p.1 ≠ p.2 := by
    intro heq
    have hsep : δ ≤ dist p.1 p.2 := hp.2.2
    rw [heq, dist_self] at hsep
    linarith
  have hDp : D p ≠ 0 := by
    intro hz
    exact hpne (D.isExtMetric.2.1 p.1 p.2 hz)
  refine ⟨D p, pos_iff_ne_zero.mpr hDp, ?_⟩
  intro q hq1 hq2 hqδ
  exact hmin ⟨hq1, hq2, hqδ⟩

theorem eventually_separated_pairs_pos {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (nhds D)) {K : Set ℂ} (hK : IsCompact K)
    {δ : ℝ} (hδ : 0 < δ)
    (hne : ({p : ℂ × ℂ | p.1 ∈ K ∧ p.2 ∈ K ∧ δ ≤ dist p.1 p.2}).Nonempty) :
    ∃ c : ENNReal, 0 < c ∧ ∀ᶠ n in atTop, ∀ p : ℂ × ℂ,
      p.1 ∈ K → p.2 ∈ K → δ ≤ dist p.1 p.2 → c ≤ G n p := by
  let S : Set (ℂ × ℂ) := {p | p.1 ∈ K ∧ p.2 ∈ K ∧ δ ≤ dist p.1 p.2}
  have hS : IsCompact S := by
    have hclosed : IsClosed {p : ℂ × ℂ | δ ≤ dist p.1 p.2} :=
      isClosed_le continuous_const continuous_dist
    have hSeq : S = (K ×ˢ K) ∩ {p : ℂ × ℂ | δ ≤ dist p.1 p.2} := by
      ext p
      simp only [S, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod]
      tauto
    rw [hSeq]
    exact (hK.prod hK).inter_right hclosed
  obtain ⟨c₀, hc₀, hc₀D⟩ := compact_separated_pairs_pos D hK hδ hne
  obtain ⟨c, hc, hcc₀⟩ := exists_between hc₀
  refine ⟨c, hc, ?_⟩
  by_contra hn
  rw [not_eventually] at hn
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hn
  have hbad' : ∀ n, ∃ p : ℂ × ℂ, p ∈ S ∧ G (φ n) p < c := by
    intro n
    simp only [not_forall, not_le] at hbad
    obtain ⟨p, hpK, hpK', hpδ, hp⟩ := hbad n
    exact ⟨p, ⟨hpK, hpK', hpδ⟩, hp⟩
  choose p hpS hp using hbad'
  obtain ⟨p₀, hp₀S, ψ, hψ, hpψ⟩ := hS.tendsto_subseq hpS
  have hGsub : Tendsto (fun n => G (φ (ψ n))) atTop (nhds D) :=
    hG.comp (hφ.comp hψ).tendsto_atTop
  have hlim := (LSCMetric.tendsto_iff.mp hGsub).1 (p ∘ ψ) p₀ hpψ
  have hle : liminf (fun n => G (φ (ψ n)) (p (ψ n))) atTop ≤ c :=
    liminf_le_of_frequently_le' (Frequently.of_forall fun n => (hp (ψ n)).le)
  have hDc₀ : c₀ ≤ D p₀ := hc₀D p₀ hp₀S.1 hp₀S.2.1 hp₀S.2.2
  exact (not_le_of_gt (hcc₀.trans_le hDc₀)) (hlim.trans hle)

theorem measurable_acrossDist (A : EuclideanAnnulus) :
    Measurable fun D : LSCMetric => acrossDist D A :=
  SupercriticalLQGUniqueness.measurable_acrossDist A

theorem disconnects_implies_path_hit {K E F : Set ℂ}
    (h : Disconnects K E F) : LQGMetric.Disconnects K E F := by
  intro x y γ hx hy
  by_contra hno
  apply h
  refine ⟨Set.range γ, isPreconnected_range γ.continuous, ?_, ?_, ?_⟩
  · intro z hz hzK
    exact hno ⟨z, hz, hzK⟩
  · exact ⟨x, Path.source_mem_range γ, hx⟩
  · exact ⟨y, Path.target_mem_range γ, hy⟩

theorem path_hit_implies_disconnects_of_closed {K E F : Set ℂ}
    (hK : IsClosed K) (h : LQGMetric.Disconnects K E F) : Disconnects K E F := by
  intro hnot
  obtain ⟨S, hS, hSK, ⟨x, hxS, hxE⟩, ⟨y, hyS, hyF⟩⟩ := hnot
  have hyV : y ∈ connectedComponentIn Kᶜ x :=
    hS.subset_connectedComponentIn hxS hSK hyS
  have hxV : x ∈ connectedComponentIn Kᶜ x := by
    have hxK : x ∉ K := connectedComponentIn_nonempty_iff.mp ⟨y, hyV⟩
    exact mem_connectedComponentIn hxK
  have hVo : IsOpen (connectedComponentIn Kᶜ x) := hK.isOpen_compl.connectedComponentIn
  have hVc : IsConnected (connectedComponentIn Kᶜ x) :=
    isConnected_connectedComponentIn_iff.mpr (connectedComponentIn_subset _ _ hxV)
  have hpath := ((hVo.isConnected_iff_isPathConnected).mp hVc).joinedIn x hxV y hyV
  obtain ⟨z, hzγ, hzK⟩ := h x y hpath.somePath hxE hyF
  obtain ⟨t, rfl⟩ := hzγ
  exact (connectedComponentIn_subset _ _ (hpath.somePath_mem t)) hzK

theorem disconnects_iff_path_hit_of_closed {K E F : Set ℂ} (hK : IsClosed K) :
    Disconnects K E F ↔ LQGMetric.Disconnects K E F :=
  ⟨disconnects_implies_path_hit, path_hit_implies_disconnects_of_closed hK⟩

theorem isClosed_separator_paths (E F : Set ℂ) :
    IsClosed {P : C(unitInterval, ℂ) | Disconnects (Set.range P) E F} := by
  rw [← isOpen_compl_iff]
  refine isOpen_iff_forall_mem_open.mpr ?_
  intro P hP
  have hnot : ¬ LQGMetric.Disconnects (Set.range P) E F := by
    intro hhit
    exact hP ((disconnects_iff_path_hit_of_closed
      (isCompact_range P.continuous).isClosed).2 hhit)
  unfold LQGMetric.Disconnects at hnot
  push Not at hnot
  obtain ⟨x, y, γ, hx, hy, hmiss⟩ := hnot
  let U : Set (C(unitInterval, ℂ)) :=
    {Q | Set.range Q ⊆ (Set.range γ)ᶜ}
  have hUopen : IsOpen U :=
    ContinuousMap.isOpen_setOfPred_range_subset (isCompact_range γ.continuous).isClosed.isOpen_compl
  have hPU : P ∈ U := by
    intro z hzP hzγ
    have hz : z ∈ Set.range γ ∩ Set.range P := ⟨hzγ, hzP⟩
    rw [hmiss] at hz
    exact hz
  refine ⟨U, ?_, hUopen, hPU⟩
  intro Q hQU hQsep
  have hhit := (disconnects_iff_path_hit_of_closed
    (isCompact_range Q.continuous).isClosed).1 hQsep x y γ hx hy
  obtain ⟨z, hzγ, hzQ⟩ := hhit
  exact (hQU hzQ) hzγ

theorem separator_stable_of_uniform_limit (E F : Set ℂ)
    {P : ℕ → C(unitInterval, ℂ)} {P₀ : C(unitInterval, ℂ)}
    (hP : TendstoUniformly (fun n t => P n t) (fun t => P₀ t) atTop)
    (hsep : ∀ n, Disconnects (Set.range (P n)) E F) :
    Disconnects (Set.range P₀) E F := by
  have hlim : Tendsto P atTop (nhds P₀) :=
    ContinuousMap.tendsto_iff_tendstoUniformly.mpr hP
  exact (isClosed_separator_paths E F).mem_of_tendsto hlim
    (Eventually.of_forall hsep)

theorem lipschitz_limit_of_epi {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (nhds D)) {P : ℕ → unitInterval → ℂ}
    {P₀ : unitInterval → ℂ} (hP : TendstoUniformly P P₀ atTop)
    {M : NNReal} (hLip : ∀ n, LipschitzWith M ((G n).pt ∘ P n)) :
    LipschitzWith M (D.pt ∘ P₀) := by
  intro s t
  have hst : Tendsto (fun n => (P n s, P n t)) atTop (nhds (P₀ s, P₀ t)) :=
    (hP.tendsto_at s).prodMk_nhds (hP.tendsto_at t)
  have hlim := (LSCMetric.tendsto_iff.mp hG).1
    (fun n => (P n s, P n t)) (P₀ s, P₀ t) hst
  have hbound : liminf (fun n => G n (P n s, P n t)) atTop ≤
      (M : ENNReal) * edist s t := by
    apply liminf_le_of_frequently_le'
    exact Frequently.of_forall fun n => hLip n s t
  exact hlim.trans hbound


end Uniqueness.Toolkit.PathInfimum

namespace Uniqueness.Toolkit.CompactPathInfimum
private theorem ennreal_le_liminf_add (u v : ℕ → ENNReal) :
    liminf u atTop + liminf v atTop ≤ liminf (fun n => u n + v n) atTop := by
  have hc (w : ℕ → ENNReal) : ((liminf w atTop : ENNReal) : EReal) =
      liminf (fun n => (w n : EReal)) atTop :=
    EReal.coe_ennreal_strictMono.monotone.map_liminf_of_continuousAt w
      continuous_coe_ennreal_ereal.continuousAt
  apply EReal.coe_ennreal_le_coe_ennreal_iff.mp
  rw [EReal.coe_ennreal_add, hc u, hc v, hc (fun n => u n + v n)]
  simp only [EReal.coe_ennreal_add]
  exact EReal.le_liminf_add

private theorem finset_sum_le_liminf {ι : Type*} (s : Finset ι)
    (f : ι → ENNReal) (u : ℕ → ι → ENNReal)
    (h : ∀ i ∈ s, f i ≤ liminf (fun n => u n i) atTop) :
    (∑ i ∈ s, f i) ≤ liminf (fun n => ∑ i ∈ s, u n i) atTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hi' : f i ≤ liminf (fun n => u n i) atTop := h i (Finset.mem_insert_self _ _)
    have hs : ∀ j ∈ s, f j ≤ liminf (fun n => u n j) atTop :=
      fun j hj => h j (Finset.mem_insert_of_mem hj)
    simpa only [Finset.sum_insert hi] using
      (add_le_add hi' (ih hs)).trans (ennreal_le_liminf_add _ _ :
        liminf (fun n => u n i) atTop +
          liminf (fun n => ∑ j ∈ s, u n j) atTop ≤
            liminf (fun n => u n i + ∑ j ∈ s, u n j) atTop)

 
theorem joint_len_le_liminf {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (nhds D)) {P : ℕ → ℝ → ℂ} {P₀ : ℝ → ℂ}
    (hP : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => P n t) atTop (nhds (P₀ t))) :
    D.len P₀ 0 1 ≤ liminf (fun n => (G n).len (P n) 0 1) atTop := by
  rw [len_eq_partitionLengthSup]
  unfold LQGMetric.MetricGeometry.partitionLengthSup
  refine iSup_le fun k => iSup_le fun t => iSup_le fun ht =>
    iSup_le fun h0 => iSup_le fun hk => ?_
  have hnode (i : ℕ) (hi : i ≤ k) : t i ∈ Icc (0 : ℝ) 1 := by
    have hleft : t 0 ≤ t i :=
      ht.monotoneOn (Set.mem_Iic.2 (Nat.zero_le _)) (Set.mem_Iic.2 hi)
        (Nat.zero_le _)
    have hright : t i ≤ t k :=
      ht.monotoneOn (Set.mem_Iic.2 hi) (Set.mem_Iic.2 le_rfl) hi
    exact ⟨h0 ▸ hleft, hk ▸ hright⟩
  have hsum :
      (∑ i ∈ Finset.range k, D (P₀ (t (i + 1)), P₀ (t i))) ≤
      liminf (fun n => ∑ i ∈ Finset.range k,
        G n (P n (t (i + 1)), P n (t i))) atTop := by
    refine finset_sum_le_liminf _ _ _ ?_
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hpair : Tendsto (fun n => (P n (t (i + 1)), P n (t i))) atTop
        (nhds (P₀ (t (i + 1)), P₀ (t i))) :=
      (hP _ (hnode (i + 1) (by omega))).prodMk_nhds (hP _ (hnode i (by omega)))
    exact (LSCMetric.tendsto_iff.mp hG).1 _ _ hpair
  have hpart : ∀ n, (∑ i ∈ Finset.range k,
      G n (P n (t (i + 1)), P n (t i))) ≤ (G n).len (P n) 0 1 := by
    intro n
    rw [len_eq_partitionLengthSup]
    exact le_iSup_of_le k <| le_iSup_of_le t <| le_iSup_of_le ht <|
      le_iSup_of_le h0 <| le_iSup_of_le hk le_rfl
  exact hsum.trans (liminf_le_liminf (Eventually.of_forall hpart))

 
theorem eventual_euclidean_modulus {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (nhds D)) {K : Set ℂ} (hK : IsCompact K)
    {P : ℕ → unitInterval → ℂ} (htrace : ∀ n t, P n t ∈ K)
    {M : NNReal} (hLip : ∀ n, LipschitzWith M ((G n).pt ∘ P n))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in atTop, ∀ s t : unitInterval,
      dist s t < η → dist (P n s) (P n t) < ε := by
  let S : Set (ℂ × ℂ) :=
    {p | p.1 ∈ K ∧ p.2 ∈ K ∧ ε ≤ dist p.1 p.2}
  by_cases hne : S.Nonempty
  · obtain ⟨c, hc, hcG⟩ := Toolkit.PathInfimum.eventually_separated_pairs_pos hG hK hε hne
    let c' : ENNReal := min c 1
    have hc' : 0 < c' := lt_min hc (by norm_num)
    have hc'fin : c' ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
    have hr : 0 < c'.toReal := ENNReal.toReal_pos hc'.ne' hc'fin
    let η : ℝ := c'.toReal / ((M : ℝ) + 1)
    have hM : 0 ≤ (M : ℝ) := M.property
    have hden : 0 < (M : ℝ) + 1 := by linarith
    refine ⟨η, div_pos hr hden, ?_⟩
    filter_upwards [hcG] with n hn
    intro s t hst
    by_contra hbad
    have hsep : ε ≤ dist (P n s) (P n t) := le_of_not_gt hbad
    have hcmetric : c' ≤ G n (P n s, P n t) :=
      (min_le_left _ _).trans (hn _ (htrace n s) (htrace n t) hsep)
    have hreal : (M : ℝ) * dist s t < c'.toReal := by
      have hη : dist s t < c'.toReal / ((M : ℝ) + 1) := hst
      have := (lt_div_iff₀ hden).mp hη
      nlinarith [dist_nonneg (x := s) (y := t)]
    have hm : (M : ENNReal) * edist s t < c' := by
      rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hM]
      exact (ENNReal.ofReal_lt_iff_lt_toReal (mul_nonneg hM (dist_nonneg : 0 ≤ dist s t))
        hc'fin).mpr hreal
    exact (not_lt_of_ge hcmetric) ((hLip n s t).trans_lt hm)
  · refine ⟨1, by norm_num, Eventually.of_forall fun n s t _ => ?_⟩
    by_contra hbad
    apply hne
    exact ⟨(P n s, P n t), htrace n s, htrace n t, le_of_not_gt hbad⟩

theorem continuous_euclidean_of_metric_on_compact (D : LSCMetric) {K : Set ℂ}
    (hK : IsCompact K) {f : unitInterval → ℂ} (hfK : ∀ t, f t ∈ K)
    (hfD : Continuous (D.pt ∘ f)) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro t
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨w, hwK, φ, hφ, hw⟩ :=
    hK.tendsto_subseq (fun n => hfK (ns n))
  refine ⟨φ, ?_⟩
  have hd : Tendsto (fun n => D.pt (f (ns (φ n)))) atTop (nhds (D.pt (f t))) :=
    (hfD.tendsto t).comp (hns.comp hφ.tendsto_atTop)
  have heq : w = f t := Toolkit.PathInfimum.eq_of_euclidean_and_metric_limits D hw hd
  change Tendsto (fun n => f (ns (φ n))) atTop (nhds w) at hw
  simpa only [heq] using hw

private theorem uniformEquicontinuous_of_eventual_modulus
    {P : ℕ → unitInterval → ℂ} (hcont : ∀ n, Continuous (P n))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in atTop,
      ∀ s t : unitInterval, dist s t < η → dist (P n s) (P n t) < ε) :
    UniformEquicontinuous P := by
  rw [Metric.uniformEquicontinuous_iff]
  intro ε hε
  obtain ⟨η, hη, htail⟩ := hmod ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  have hfin : UniformEquicontinuous (fun i : Fin N => P i) :=
    uniformEquicontinuous_finite.mpr fun i =>
      CompactSpace.uniformContinuous_of_continuous (hcont i)
  obtain ⟨η₀, hη₀, hhead⟩ := Metric.uniformEquicontinuous_iff.mp hfin ε hε
  refine ⟨min η η₀, lt_min hη hη₀, ?_⟩
  intro s t hst n
  by_cases hn : n < N
  · exact hhead s t (hst.trans_le (min_le_right _ _)) ⟨n, hn⟩
  · exact hN n (Nat.le_of_not_gt hn) s t (hst.trans_le (min_le_left _ _))

 
theorem compact_trace_path_subseq {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (nhds D)) {K : Set ℂ} (hK : IsCompact K)
    {P : ℕ → unitInterval → ℂ} (htrace : ∀ n t, P n t ∈ K)
    {M : NNReal} (hLip : ∀ n, LipschitzWith M ((G n).pt ∘ P n)) :
    ∃ (φ : ℕ → ℕ) (P₀ : C(unitInterval, ℂ)), StrictMono φ ∧
      TendstoUniformly (fun n t => P (φ n) t) P₀ atTop ∧
      (∀ t, P₀ t ∈ K) := by
  have hcont : ∀ n, Continuous (P n) := fun n =>
    continuous_euclidean_of_metric_on_compact (G n) hK (htrace n) (hLip n).continuous
  have hmod : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in atTop,
      ∀ s t : unitInterval, dist s t < η → dist (P n s) (P n t) < ε :=
    fun ε hε => eventual_euclidean_modulus hG hK htrace hLip hε
  have hequi : UniformEquicontinuous P :=
    uniformEquicontinuous_of_eventual_modulus hcont hmod
  let u : ℕ → unitInterval →ᵇ ℂ := fun n =>
    BoundedContinuousFunction.mkOfCompact ⟨P n, hcont n⟩
  have hu (n : ℕ) (t : unitInterval) : u n t = P n t := rfl
  have hin : ∀ (f : unitInterval →ᵇ ℂ) (t : unitInterval),
      f ∈ Set.range u → f t ∈ K := by
    rintro f t ⟨n, rfl⟩
    exact hu n t ▸ htrace n t
  have hequi' : Equicontinuous ((↑) : Set.range u → unitInterval → ℂ) := by
    intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδP⟩ := Metric.uniformEquicontinuous_iff.mp hequi ε hε
    refine ⟨δ, hδ, fun y hy i => ?_⟩
    obtain ⟨n, hn⟩ := i.property
    rw [← hn]
    simpa only [hu] using hδP x y (by simpa only [dist_comm] using hy) n
  have hcpt := BoundedContinuousFunction.arzela_ascoli K hK (Set.range u) hin hequi'
  obtain ⟨f, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq (x := u)
    (fun n => subset_closure ⟨n, rfl⟩)
  have hlimU := (tendsto_iff_tendstoUniformly).mp hlim
  have hlimP : TendstoUniformly (fun n t => P (φ n) t) (fun t => f t) atTop := by
    change TendstoUniformly (fun n t => u (φ n) t) (fun t => f t) atTop at hlimU
    have hfun : (fun n t => u (φ n) t) = (fun n t => P (φ n) t) := by
      funext n t
      exact hu (φ n) t
    rw [hfun] at hlimU
    exact hlimU
  refine ⟨φ, f.toContinuousMap, hφ, ?_, ?_⟩
  · exact hlimP
  · intro t
    exact hK.isClosed.mem_of_tendsto (hlimP.tendsto_at t)
      (Eventually.of_forall fun n => htrace (φ n) t)

 

end Uniqueness.Toolkit.CompactPathInfimum

namespace Uniqueness.Toolkit.CountableBase

 

theorem continuous_euclidean_of_metric_on_compact
    {α : Type*} [TopologicalSpace α] [FirstCountableTopology α]
    (D : LSCMetric) {K : Set ℂ} (hK : IsCompact K)
    {f : α → ℂ} (hfK : ∀ t, f t ∈ K)
    (hfD : Continuous (D.pt ∘ f)) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro t
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨w, hwK, φ, hφ, hw⟩ := hK.tendsto_subseq (fun n => hfK (ns n))
  refine ⟨φ, ?_⟩
  have hd : Tendsto (fun n => D.pt (f (ns (φ n)))) atTop (nhds (D.pt (f t))) :=
    (hfD.tendsto t).comp (hns.comp hφ.tendsto_atTop)
  have heq : w = f t := Toolkit.PathInfimum.eq_of_euclidean_and_metric_limits D hw hd
  change Tendsto (fun n => f (ns (φ n))) atTop (nhds w) at hw
  simpa only [heq] using hw

 


theorem curve_continuousOn_euclidean_of_bounded
    (D : LSCMetric) {U : Set ℂ} (hUb : Bornology.IsBounded U)
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b)
    (htrace : ∀ t ∈ Icc a b, P t ∈ U) :
    ContinuousOn P (Icc a b) := by
  let f : Icc a b → ℂ := fun t => P t
  have hfK : ∀ t, f t ∈ closure U :=
    fun t => subset_closure (htrace t t.2)
  have hfD : Continuous (D.pt ∘ f) :=
    continuousOn_iff_continuous_domRestrict.mp hP.2
  have hf : Continuous f :=
    continuous_euclidean_of_metric_on_compact D hUb.isCompact_closure hfK hfD
  exact continuousOn_iff_continuous_domRestrict.mpr hf

 

theorem curve_trace_in_compact_exhaustion
    (D : LSCMetric) {U : Set ℂ} (hUb : Bornology.IsBounded U)
    (H : CompactExhaustion U)
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b)
    (htrace : ∀ t ∈ Icc a b, P t ∈ U) :
    ∃ n : ℕ, ∀ t ∈ Icc a b, P t ∈ (H n).image Subtype.val := by
  have hcont : ContinuousOn P (Icc a b) :=
    curve_continuousOn_euclidean_of_bounded D hUb hP htrace
  let g : Icc a b → U := fun t => ⟨P t, htrace t t.2⟩
  have hg : Continuous g := by
    exact (continuousOn_iff_continuous_domRestrict.mp hcont).subtype_mk _
  obtain ⟨n, hn⟩ :=
    H.exists_superset_of_isCompact (isCompact_univ.image hg)
  refine ⟨n, fun t ht => ?_⟩
  exact ⟨g ⟨t, ht⟩, hn (Set.mem_image_of_mem g (Set.mem_univ _)), rfl⟩

 

end Uniqueness.Toolkit.CountableBase
end SupercriticalLQGUniqueness
