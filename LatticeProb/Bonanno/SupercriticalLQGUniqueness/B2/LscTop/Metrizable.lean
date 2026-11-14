/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.LscTop.Metrizable at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase.FellBase
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements
import Mathlib.Topology.Metrizable.Urysohn

 

















set_option autoImplicit false

noncomputable section

open Set Filter Topology TopologicalSpace
open SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase

namespace SupercriticalLQGUniqueness.B2.LscTop

 

 


theorem exists_tests_eq_generateFrom :
    ∃ B S : Set (Set (ℂ × ℂ)), B.Countable ∧ S.Countable ∧ IsTopologicalBasis B ∧
      (∀ K ∈ S, IsCompact K) ∧
      (∀ q (V : Set (ℂ × ℂ)), IsOpen V → q ∈ V → ∃ K ∈ S, K ∈ 𝓝 q ∧ K ⊆ V) ∧
      LSCFun.instTopologicalSpace = generateFrom (Tests B S) := by
  obtain ⟨S, hSc, hSk, hSloc⟩ := exists_countable_compact_local_base
  let B := countableBasis (ℂ × ℂ)
  have hBc : B.Countable := countable_countableBasis _
  have hBo : ∀ O ∈ B, IsOpen O := fun O hO => isOpen_of_mem_countableBasis hO
  have hBbasis : IsTopologicalBasis B := isBasis_countableBasis _
  refine ⟨B, S, hBc, hSc, hBbasis, hSk, hSloc, ?_⟩
  let t : TopologicalSpace LSCFun := generateFrom (Tests B S)
  have hsecond : @SecondCountableTopology LSCFun t :=
    SecondCountableTopology.mk' (tests_countable hBc hSc)
  have hseq : @SequentialSpace LSCFun t := by
    let _ : TopologicalSpace LSCFun := t
    have _ : SecondCountableTopology LSCFun := hsecond
    infer_instance
  refine (LSCFun.eq_of_sequentialSpace t hseq fun F f =>
    ⟨fun h => lscTendsto_of_tests hBbasis hSloc h, fun h => ?_⟩).symm
  exact (LSCFun.tendsto_of_lscTendsto h).mono_right
    (nhds_mono (le_generateFrom (tests_open hBo hSk)))

 

 

theorem exists_open_separating {f g : LSCFun} {q : ℂ × ℂ} (h : f.1 q < g.1 q) :
    ∃ u v : Set LSCFun, IsOpen u ∧ IsOpen v ∧ f ∈ u ∧ g ∈ v ∧ Disjoint u v := by
  obtain ⟨s, hfs, hsg⟩ := exists_between h
  obtain ⟨K, hK, hqK, hKV⟩ :=
    exists_compact_subset (g.2.isOpen_preimage s) (show q ∈ g.1 ⁻¹' Ioi s from hsg)
  refine ⟨{k : LSCFun | ∃ x ∈ interior K, k.1 x < s}, {k : LSCFun | ∀ x ∈ K, s < k.1 x},
    LSCFun.isOpen_setOf_exists_lt isOpen_interior s, LSCFun.isOpen_setOf_forall_lt hK s,
    ⟨q, hqK, hfs⟩, fun x hx => hKV hx, ?_⟩
  rw [Set.disjoint_left]
  rintro k ⟨x, hx, hkx⟩ hk
  exact lt_asymm hkx (hk x (interior_subset hx))

 
instance instT2Space : T2Space LSCFun := by
  refine ⟨fun f g hfg => ?_⟩
  have hne : ∃ q, f.1 q ≠ g.1 q := by
    by_contra hc
    push Not at hc
    exact hfg (Subtype.ext (funext hc))
  obtain ⟨q, hq⟩ := hne
  rcases hq.lt_or_gt with h | h
  · exact exists_open_separating h
  · obtain ⟨u, v, hu, hv, hgu, hfv, huv⟩ := exists_open_separating h
    exact ⟨v, u, hv, hu, hfv, hgu, huv.symm⟩

 

 

theorem disjoint_nhdsSet_compl_hit {O : Set (ℂ × ℂ)} (hO : IsOpen O) {s : EReal} {f : LSCFun}
    (hf : ∃ q ∈ O, f.1 q < s) :
    Disjoint (𝓝ˢ {g : LSCFun | ∃ q ∈ O, g.1 q < s}ᶜ) (𝓝 f) := by
  obtain ⟨q, hqO, hfq⟩ := hf
  obtain ⟨s', hfs', hs's⟩ := exists_between hfq
  obtain ⟨K, hK, hqK, hKO⟩ := exists_compact_subset hO hqO
  refine Filter.disjoint_of_disjoint_of_mem (s := {g : LSCFun | ∀ x ∈ K, s' < g.1 x})
    (t := {g : LSCFun | ∃ x ∈ interior K, g.1 x < s'}) ?_ ?_ ?_
  · rw [Set.disjoint_left]
    rintro g hg ⟨x, hx, hgx⟩
    exact lt_asymm hgx (hg x (interior_subset hx))
  · refine (LSCFun.isOpen_setOf_forall_lt hK s').mem_nhdsSet.2 fun g hg x hx => ?_
    simp only [mem_compl_iff, mem_ofPred_eq, not_exists, not_and, not_lt] at hg
    exact hs's.trans_le (hg x (hKO hx))
  · exact (LSCFun.isOpen_setOf_exists_lt isOpen_interior s').mem_nhds ⟨q, hqK, hfs'⟩

 


theorem disjoint_nhdsSet_compl_miss {K : Set (ℂ × ℂ)} (hK : IsCompact K) {s : EReal}
    {f : LSCFun} (hf : ∀ q ∈ K, s < f.1 q) :
    Disjoint (𝓝ˢ {g : LSCFun | ∀ q ∈ K, s < g.1 q}ᶜ) (𝓝 f) := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp
  obtain ⟨x₀, hx₀K, hmin⟩ :=
    (f.2.lowerSemicontinuousOn K).exists_isMinOn hKne hK
  obtain ⟨s', hss', hs'f⟩ := exists_between (hf x₀ hx₀K)
  obtain ⟨L, hL, hKL, hLV⟩ := exists_compact_between hK (f.2.isOpen_preimage s')
    (fun x hx => hs'f.trans_le (hmin hx))
  refine Filter.disjoint_of_disjoint_of_mem (s := {g : LSCFun | ∃ x ∈ interior L, g.1 x < s'})
    (t := {g : LSCFun | ∀ x ∈ L, s' < g.1 x}) ?_ ?_ ?_
  · rw [Set.disjoint_left]
    rintro g ⟨x, hx, hgx⟩ hg
    exact lt_asymm hgx (hg x (interior_subset hx))
  · refine (LSCFun.isOpen_setOf_exists_lt isOpen_interior s').mem_nhdsSet.2 fun g hg => ?_
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall, not_lt, exists_prop] at hg
    obtain ⟨x, hxK, hgx⟩ := hg
    exact ⟨x, hKL hxK, hgx.trans_lt hss'⟩
  · exact (LSCFun.isOpen_setOf_forall_lt hL s').mem_nhds fun x hx => hLV hx

 

instance instRegularSpace : RegularSpace LSCFun := by
  obtain ⟨B, S, -, -, hB, hSk, -, heq⟩ := exists_tests_eq_generateFrom
  refine (regularSpace_generateFrom heq).2 ?_
  rintro t (⟨⟨⟨O, hO⟩, r⟩, rfl⟩ | ⟨⟨⟨K, hK⟩, r⟩, rfl⟩) f hf
  · exact disjoint_nhdsSet_compl_hit (hB.isOpen hO) hf
  · exact disjoint_nhdsSet_compl_miss (hSk K hK) hf

instance instT3Space : T3Space LSCFun := inferInstance

 

instance instMetrizableSpace : MetrizableSpace LSCFun :=
  metrizableSpace_of_t3_secondCountable LSCFun

 

theorem toLSCFun_injective : Function.Injective LSCMetric.toLSCFun := fun _ _ h =>
  LSCMetric.ext fun p => EReal.coe_ennreal_injective (congrFun (congrArg Subtype.val h) p)

theorem isEmbedding_toLSCFun : IsEmbedding LSCMetric.toLSCFun :=
  ⟨LSCMetric.isInducing_toLSCFun, toLSCFun_injective⟩

instance instSecondCountableLSCMetric : SecondCountableTopology LSCMetric :=
  LSCMetric.isInducing_toLSCFun.secondCountableTopology

instance instT2SpaceLSCMetric : T2Space LSCMetric := isEmbedding_toLSCFun.t2Space

instance instRegularSpaceLSCMetric : RegularSpace LSCMetric :=
  LSCMetric.isInducing_toLSCFun.regularSpace

 

instance instMetrizableSpaceLSCMetric : MetrizableSpace LSCMetric :=
  isEmbedding_toLSCFun.metrizableSpace

 
end SupercriticalLQGUniqueness.B2.LscTop
