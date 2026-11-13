/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase.FellBase at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SLUMetricAPI
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.SecondCountableSpace




 




set_option autoImplicit false
noncomputable section

open Set Filter Topology

namespace SupercriticalLQGUniqueness
namespace Uniqueness.Toolkit.CountableBase

def Hit (O : Set (ℂ × ℂ)) (r : ℚ) : Set LSCFun :=
  {f | ∃ q ∈ O, f.1 q < (((r : ℝ) : EReal))}

def Miss (K : Set (ℂ × ℂ)) (r : ℚ) : Set LSCFun :=
  {f | ∀ q ∈ K, (((r : ℝ) : EReal)) < f.1 q}

def Tests (B S : Set (Set (ℂ × ℂ))) : Set (Set LSCFun) :=
  Set.range (fun z : B × ℚ => Hit z.1.1 z.2) ∪
    Set.range (fun z : S × ℚ => Miss z.1.1 z.2)

theorem tests_countable {B S : Set (Set (ℂ × ℂ))}
    (hB : B.Countable) (hS : S.Countable) : (Tests B S).Countable := by
  letI : Countable B := hB.to_subtype
  letI : Countable S := hS.to_subtype
  exact (Set.countable_range (fun z : B × ℚ => Hit z.1.1 z.2)).union
    (Set.countable_range (fun z : S × ℚ => Miss z.1.1 z.2))

theorem tests_open {B S : Set (Set (ℂ × ℂ))}
    (hB : ∀ O ∈ B, IsOpen O) (hS : ∀ K ∈ S, IsCompact K) :
    ∀ U ∈ Tests B S, IsOpen U := by
  intro U hU
  rcases hU with ⟨⟨⟨O, hO⟩, r⟩, rfl⟩ | ⟨⟨⟨K, hK⟩, r⟩, rfl⟩
  · exact LSCFun.isOpen_setOf_exists_lt (hB O hO) _
  · exact LSCFun.isOpen_setOf_forall_lt (hS K hK) _


 

theorem condition_i_of_miss_tests {B S : Set (Set (ℂ × ℂ))}
    (hS : ∀ q (V : Set (ℂ × ℂ)), IsOpen V → q ∈ V →
      ∃ K ∈ S, K ∈ 𝓝 q ∧ K ⊆ V)
    {F : ℕ → LSCFun} {f : LSCFun}
    (hF : Tendsto F atTop
      (@nhds LSCFun (TopologicalSpace.generateFrom (Tests B S)) f)) :
    ∀ (p : ℕ → ℂ × ℂ) (q : ℂ × ℂ), Tendsto p atTop (𝓝 q) →
      f.1 q ≤ liminf (fun n => (F n).1 (p n)) atTop := by
  intro p q hp
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨r, hrlo, hrhi⟩ := EReal.exists_rat_btwn_of_lt hlt
  let V : Set (ℂ × ℂ) := {x | (((r : ℝ) : EReal)) < f.1 x}
  have hVo : IsOpen V := f.2.isOpen_preimage _
  obtain ⟨K, hKS, hKq, hKV⟩ := hS q V hVo hrhi
  have hfK : f ∈ Miss K r := fun x hx => hKV hx
  have htest : Miss K r ∈ Tests B S :=
    Or.inr ⟨((⟨K, hKS⟩ : S), r), rfl⟩
  have hopen : @IsOpen LSCFun (TopologicalSpace.generateFrom (Tests B S))
      (Miss K r) := TopologicalSpace.isOpen_generateFrom_of_mem htest
  have hnhds : Miss K r ∈
      @nhds LSCFun (TopologicalSpace.generateFrom (Tests B S)) f :=
    @IsOpen.mem_nhds LSCFun (TopologicalSpace.generateFrom (Tests B S))
      f (Miss K r) hopen hfK
  have hev : ∀ᶠ n in atTop, (((r : ℝ) : EReal)) ≤ (F n).1 (p n) := by
    filter_upwards [hF hnhds, hp hKq] with n hn1 hn2
    exact (hn1 (p n) hn2).le
  exact absurd (le_liminf_of_le (by isBoundedDefault) hev) (not_le.2 hrlo)


 

theorem lscTendsto_of_tests {B S : Set (Set (ℂ × ℂ))}
    (hB : TopologicalSpace.IsTopologicalBasis B)
    (hS : ∀ q (V : Set (ℂ × ℂ)), IsOpen V → q ∈ V →
      ∃ K ∈ S, K ∈ 𝓝 q ∧ K ⊆ V)
    {F : ℕ → LSCFun} {f : LSCFun}
    (hF : Tendsto F atTop
      (@nhds LSCFun (TopologicalSpace.generateFrom (Tests B S)) f)) :
    LSCTendsto (fun n => (F n).1) f.1 := by
  classical
  have hi := condition_i_of_miss_tests hS hF
  refine ⟨hi, fun q => ?_⟩
  by_cases htop : f.1 q = ⊤
  · refine ⟨fun _ => q, tendsto_const_nhds, ?_⟩
    have h1 := hi (fun _ => q) q tendsto_const_nhds
    rw [htop] at h1 ⊢
    exact tendsto_of_le_liminf_of_limsup_le h1 le_top
  obtain ⟨s, -, hs_mem, hs_lim⟩ :=
    exists_seq_strictAnti_tendsto' (lt_top_iff_ne_top.2 htop)
  obtain ⟨O, hO⟩ := (𝓝 q).exists_antitone_basis
  let P : ℕ → ℕ → Prop := fun n k => ∃ x ∈ O k, (F n).1 x < s k
  have hPev : ∀ k, ∀ᶠ n in atTop, P n k := by
    intro k
    obtain ⟨U, hUB, hqU, hUO⟩ := hB.mem_nhds_iff.1 (hO.mem k)
    obtain ⟨r, hfr, hrs⟩ := EReal.exists_rat_btwn_of_lt (hs_mem k).1
    have hfU : f ∈ Hit U r := ⟨q, hqU, hfr⟩
    have htest : Hit U r ∈ Tests B S :=
      Or.inl ⟨((⟨U, hUB⟩ : B), r), rfl⟩
    have hopen : @IsOpen LSCFun (TopologicalSpace.generateFrom (Tests B S))
        (Hit U r) := TopologicalSpace.isOpen_generateFrom_of_mem htest
    have hnhds : Hit U r ∈
        @nhds LSCFun (TopologicalSpace.generateFrom (Tests B S)) f :=
      @IsOpen.mem_nhds LSCFun (TopologicalSpace.generateFrom (Tests B S))
        f (Hit U r) hopen hfU
    filter_upwards [hF hnhds] with n ⟨x, hxU, hxr⟩
    exact ⟨x, hUO hxU, hxr.trans hrs⟩
  let ρ : ℕ → ℕ := fun n => Nat.findGreatest (P n) n
  have hρ : Tendsto ρ atTop atTop := by
    refine tendsto_atTop.2 fun K => ?_
    filter_upwards [hPev K, eventually_ge_atTop K] with n hn hKn
    exact Nat.le_findGreatest hKn hn
  have hPρ : ∀ᶠ n in atTop, P n (ρ n) := by
    filter_upwards [hPev 0] with n hn
    exact Nat.findGreatest_spec (Nat.zero_le n) hn
  let x : ℕ → ℂ × ℂ := fun n => if h : P n (ρ n) then h.choose else q
  have hxP : ∀ᶠ n in atTop, x n ∈ O (ρ n) ∧ (F n).1 (x n) < s (ρ n) := by
    filter_upwards [hPρ] with n hn
    simp only [x, dite_eq_left hn]
    exact hn.choose_spec
  have hx : Tendsto x atTop (𝓝 q) := by
    refine hO.1.tendsto_right_iff.2 fun K _ => ?_
    filter_upwards [hxP, hρ.eventually_ge_atTop K] with n hn hKn
    exact hO.2 hKn hn.1
  refine ⟨x, hx, tendsto_of_le_liminf_of_limsup_le (hi x q hx) ?_⟩
  calc limsup (fun n => (F n).1 (x n)) atTop ≤ limsup (fun n => s (ρ n)) atTop :=
        limsup_le_limsup (hxP.mono fun n hn => hn.2.le)
    _ = f.1 q := (hs_lim.comp hρ).limsup_eq


 

theorem exists_countable_compact_local_base :
    ∃ S : Set (Set (ℂ × ℂ)), S.Countable ∧
      (∀ K ∈ S, IsCompact K) ∧
      ∀ q (V : Set (ℂ × ℂ)), IsOpen V → q ∈ V →
        ∃ K ∈ S, K ∈ 𝓝 q ∧ K ⊆ V := by
  have (U : TopologicalSpace.countableBasis (ℂ × ℂ)) :
      LocallyCompactSpace U.1 :=
    (TopologicalSpace.isOpen_of_mem_countableBasis U.2).locallyCompactSpace
  let K := fun U : TopologicalSpace.countableBasis (ℂ × ℂ) =>
    CompactExhaustion.choice U.1
  use ⋃ U : TopologicalSpace.countableBasis (ℂ × ℂ),
    Set.range fun n => K U n
  refine ⟨Set.countable_iUnion fun _ => Set.countable_range _, ?_, ?_⟩
  · simp only [Set.mem_iUnion, Set.mem_range]
    rintro L ⟨U, n, rfl⟩
    exact ((K U).isCompact n).image continuous_subtype_val
  · intro q V hVo hqV
    obtain ⟨U, hU, hqU, hUV⟩ :=
      (TopologicalSpace.isBasis_countableBasis _).isOpen_iff.mp hVo q hqV
    lift q to U using hqU
    lift U to TopologicalSpace.countableBasis (ℂ × ℂ) using hU
    obtain ⟨n, hn⟩ := (K U).exists_mem_nhds q
    refine ⟨K U n, Set.mem_iUnion.2 ⟨U, Set.mem_range_self _⟩, ?_, ?_⟩
    · rw [← map_nhds_subtype_coe_eq_nhds q.2]
      exacts [image_mem_map hn, (TopologicalSpace.isOpen_of_mem_countableBasis U.2).mem_nhds q.2]
    · rw [Set.image_subset_iff]
      exact fun y hy => hUV y.2


 

theorem secondCountable_of_countable_open_tests
    (B : Set (Set LSCFun)) (hcount : B.Countable)
    (hopen : ∀ U ∈ B, IsOpen U)
    (hconv : ∀ (F : ℕ → LSCFun) (f : LSCFun),
      Tendsto F atTop (@nhds LSCFun (TopologicalSpace.generateFrom B) f) →
      LSCTendsto (fun n => (F n).1) f.1) :
    SecondCountableTopology LSCFun := by
  let t : TopologicalSpace LSCFun := TopologicalSpace.generateFrom B
  have hsecond : @SecondCountableTopology LSCFun t :=
    TopologicalSpace.SecondCountableTopology.mk' hcount
  have hseq : @SequentialSpace LSCFun t := by
    letI : TopologicalSpace LSCFun := t
    letI : SecondCountableTopology LSCFun := hsecond
    infer_instance
  have ht : ∀ (F : ℕ → LSCFun) (f : LSCFun),
      Tendsto F atTop (@nhds LSCFun t f) ↔
        LSCTendsto (fun n => (F n).1) f.1 := by
    intro F f
    constructor
    · exact hconv F f
    · intro h
      have h₁ := LSCFun.tendsto_of_lscTendsto h
      have hle : LSCFun.instTopologicalSpace ≤ t :=
        le_generateFrom hopen
      exact h₁.mono_right (nhds_mono hle)
  have heq : t = LSCFun.instTopologicalSpace :=
    LSCFun.eq_of_sequentialSpace t hseq ht
  rw [← heq]
  exact hsecond

 


instance instSecondCountableLSCFun : SecondCountableTopology LSCFun := by
  obtain ⟨S, hSc, hSk, hSloc⟩ := exists_countable_compact_local_base
  let B := TopologicalSpace.countableBasis (ℂ × ℂ)
  have hBc : B.Countable := TopologicalSpace.countable_countableBasis _
  have hBo : ∀ O ∈ B, IsOpen O :=
    fun O hO => TopologicalSpace.isOpen_of_mem_countableBasis hO
  have hBbasis : TopologicalSpace.IsTopologicalBasis B :=
    TopologicalSpace.isBasis_countableBasis _
  exact secondCountable_of_countable_open_tests
    (Tests B S) (tests_countable hBc hSc) (tests_open hBo hSk)
    (fun F f hF => lscTendsto_of_tests hBbasis hSloc hF)

 

instance instFirstCountableLSCMetric : FirstCountableTopology LSCMetric := by
  exact LSCMetric.isInducing_toLSCFun.firstCountableTopology

instance instSequentialLSCMetric : SequentialSpace LSCMetric := by
  infer_instance



end Uniqueness.Toolkit.CountableBase
end SupercriticalLQGUniqueness
