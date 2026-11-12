/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L45Pos2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Pos1
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Sel2

/-!
# GM Lemma 4.5 with no null-measurability hypotheses (task P2-E2T)

GM = Gwynne–Miller, arXiv:1905.00383v3, Lemma 4.5 (`lem-geo-sigma-algebra`, l. 1655–1688).
The last measurability input `hnullGC` of `gm_L4_5_of_null'` (the decoding events `gmGeodCEv`,
whose negative clause "`arcOf x` misses `V n`" sits under `∃ x`) is proved by
**inclusion–exclusion over the a.s. finite set `Conf(s,t)`** (GM.S4.1): writing
`N_G(F) = #{x ∈ Conf : arcOf x hits V n (n ∈ F), misses V n (n ∈ G), Φ x}`,

  `N_G(F) = N_{G ∪ {n}}(F) + N_G(F ∪ {n})`,

so on `{Conf finite}` each `{m ≤ N_G(F)}` is a countable Boolean combination of the positive
counting events `{m' ≤ N_∅(F')}`, which are analytic (`gmP_leEncardAn`, `L45Pos1`), hence
null-measurable. `gmGeodCEv = {1 ≤ N_G(F)}`. Own descriptive-set-theory argument (D65); GM do
not discuss measurability.

`gm_L4_5_final`: GM Lemma 4.5 (both directions) at `s_k`, `t_k`, from `DFGPSLem3_8` and the
CONF Blueprint propositions only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

section Split
variable (V : ℕ → Set ℂ) (Φ : ContMetric → ℂ → Prop) (d : ContMetric) (𝕫 : ℂ) (s t : ℝ)

lemma gmP_split (F G : Finset ℕ) (n : ℕ) :
    gmPosS V Φ d 𝕫 s t F G =
      gmPosS V Φ d 𝕫 s t F (insert n G) ∪ gmPosS V Φ d 𝕫 s t (insert n F) G := by
  ext x
  simp only [gmPosS, mem_ofPred_eq, mem_union, Finset.forall_mem_insert]
  by_cases hp : gmPat V d 𝕫 t x n <;> tauto

lemma gmP_disjoint (F G : Finset ℕ) (n : ℕ) :
    Disjoint (gmPosS V Φ d 𝕫 s t F (insert n G)) (gmPosS V Φ d 𝕫 s t (insert n F) G) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, -, hG, -⟩ ⟨-, hF, -, -⟩
  exact (hG n (Finset.mem_insert_self n G)) (hF n (Finset.mem_insert_self n F))

lemma gmP_subset (F G : Finset ℕ) : gmPosS V Φ d 𝕫 s t F G ⊆ gmPosS V Φ d 𝕫 s t ∅ ∅ := by
  rintro x ⟨hx, -, -, hΦ⟩
  exact ⟨hx, by simp, by simp, hΦ⟩

lemma gmP_encard_split (F G : Finset ℕ) (n : ℕ) :
    (gmPosS V Φ d 𝕫 s t F G).encard =
      (gmPosS V Φ d 𝕫 s t F (insert n G)).encard + (gmPosS V Φ d 𝕫 s t (insert n F) G).encard := by
  rw [← encard_union_eq (gmP_disjoint V Φ d 𝕫 s t F G n), ← gmP_split]

end Split

/-- **inclusion–exclusion for null-measurability**: if `N F G = N F (G ∪ {n}) + N (F ∪ {n}) G`,
all `N F G ≤ N ∅ ∅ < ⊤` a.e., and the positive events `{m ≤ N F ∅}` are null-measurable, then so
are all `{m ≤ N F G}` -/
theorem gmP_nullMeas_count {α : Type} [MeasurableSpace α] {μ : Measure α}
    (N : Finset ℕ → Finset ℕ → α → ℕ∞)
    (hsplit : ∀ F G n a, N F G a = N F (insert n G) a + N (insert n F) G a)
    (hle : ∀ F G a, N F G a ≤ N ∅ ∅ a) (hfin : ∀ᵐ a ∂μ, N ∅ ∅ a ≠ ⊤)
    (hbase : ∀ F (m : ℕ), NullMeasurableSet {a | (m : ℕ∞) ≤ N F ∅ a} μ) :
    ∀ G F (m : ℕ), NullMeasurableSet {a | (m : ℕ∞) ≤ N F G a} μ := by
  classical
  intro G
  induction G using Finset.induction_on with
  | empty => exact hbase
  | insert n G _ ih =>
    intro F m
    have hY : NullMeasurableSet (⋃ b : ℕ, ({a | (b : ℕ∞) ≤ N (insert n F) G a} \
        {a | ((b + 1 : ℕ) : ℕ∞) ≤ N (insert n F) G a}) ∩
        {a | ((m + b : ℕ) : ℕ∞) ≤ N F G a}) μ :=
      NullMeasurableSet.iUnion fun b => ((ih _ b).diff (ih _ (b + 1))).inter (ih F (m + b))
    refine hY.congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hfin] with a ha
    have h1 : N F (insert n G) a ≠ ⊤ := ne_top_of_le_ne_top ha (hle _ _ a)
    have h2 : N (insert n F) G a ≠ ⊤ := ne_top_of_le_ne_top ha (hle _ _ a)
    obtain ⟨x, hx⟩ := ENat.ne_top_iff_exists.1 h1
    obtain ⟨y, hy⟩ := ENat.ne_top_iff_exists.1 h2
    have hs := hsplit F G n a
    rw [← hx, ← hy] at hs
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
    rw [hs, ← hx, ← hy]
    norm_cast
    constructor
    · rintro ⟨b, ⟨hb1, hb2⟩, hb3⟩
      omega
    · intro hm
      exact ⟨y, ⟨le_rfl, by omega⟩, by omega⟩

/-- **`hnullGC`** (the last input of `gm_L4_5_of_null'`): the decoding events `gmGeodCEv` are
null-measurable for the law of the field -/
theorem gm_hnullGC (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4) (hC27 : CONFLem2_7)
    (hC14 : CONFThm1_4) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    {c' : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c') {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) {R c₀ c : ℝ}
    (hR : 0 < R) (hc₀ : 0 < c₀) (hc : c₀ < c) {V : ℕ → Set ℂ} (hVo : ∀ n, IsOpen (V n))
    (u : unitInterval) (i : (Bool × ℚ) × Finset ℕ × Finset ℕ) (n : ℕ) (s : Finset (ℤ × ℤ)) :
    NullMeasurableSet ({g | gmGeodCEv V (D g) 𝕫 (tauD (D g) 𝕫 R * c₀) (tauD (D g) 𝕫 R * c) u i} ∩
      {g | dyadicHull n (gmKt D 𝕫 R c g) = LocalEvent.hullFin n s}) (P.map h) := by
  set Φ : ContMetric → ℂ → Prop := fun d x =>
    ∃ Q : C(unitInterval, ℂ), IsGeod01 d 𝕫 x Q ∧ Q u ∈ gmHalf i.1 with hΦdef
  set N : Finset ℕ → Finset ℕ → DistC → ℕ∞ := fun F G g =>
    (gmPosS V Φ (D g) 𝕫 (tauD (D g) 𝕫 R * c₀) (tauD (D g) 𝕫 R * c) F G).encard with hNdef
  have hlen := ae_mem_lenSet h38 hγ hγ2 hD P h hh
  have hbase : ∀ F (m : ℕ), NullMeasurableSet {g | (m : ℕ∞) ≤ N F ∅ g} (P.map h) :=
    fun F m => gmE_nullMeas_of_an hD.measurable hh.measurable.aemeasurable hlen
      (gmP_leEncardAn hVo (gmP_geodHalfAn 𝕫 u i.1) 𝕫 R c₀ c F m)
  have hfin : ∀ᵐ g ∂(P.map h), N ∅ ∅ g ≠ ⊤ := by
    have hB : NullMeasurableSet {g | N ∅ ∅ g = ⊤} (P.map h) := by
      have e : {g | N ∅ ∅ g = ⊤} = ⋂ m : ℕ, {g | (m : ℕ∞) ≤ N ∅ ∅ g} := by
        ext g
        simp only [mem_ofPred_eq, mem_iInter]
        exact ⟨fun h m => h ▸ le_top, fun h => ENat.eq_top_iff_forall_ge.2 h⟩
      rw [e]
      exact NullMeasurableSet.iInter fun m => hbase ∅ m
    have hP : ∀ᵐ ω ∂P, N ∅ ∅ (h ω) ≠ ⊤ := by
      filter_upwards [gm_S4_1 hC24 hC27 hC14 hγ hγ2 hD P h hh 𝕫] with ω hS
      have hτ := gm_tauD_pos (D (h ω)) 𝕫 hR
      obtain ⟨hf, -⟩ := hS _ _ (mul_pos hτ hc₀) (mul_lt_mul_of_pos_left hc hτ)
      exact encard_ne_top_iff.2 (hf.subset fun x hx => hx.1)
    have hP0 := ae_iff.1 hP
    simp only [ne_eq, not_not] at hP0
    rw [ae_iff]
    simp only [ne_eq, not_not]
    rw [Measure.map_apply₀ hh.measurable.aemeasurable hB]
    exact hP0
  have hcnt := gmP_nullMeas_count (μ := P.map h) N
    (fun F G n g => gmP_encard_split V Φ (D g) 𝕫 _ _ F G n)
    (fun F G g => encard_le_encard (gmP_subset V Φ (D g) 𝕫 _ _ F G)) hfin hbase i.2.2 i.2.1 1
  have e : {g | gmGeodCEv V (D g) 𝕫 (tauD (D g) 𝕫 R * c₀) (tauD (D g) 𝕫 R * c) u i} =
      {g | ((1 : ℕ) : ℕ∞) ≤ N i.2.1 i.2.2 g} := by
    ext g
    simp only [mem_ofPred_eq, Nat.cast_one, hNdef, one_le_encard_iff_nonempty]
    rfl
  rw [e]
  exact hcnt.inter (gmE_nullMeas_of_an hD.measurable hh.measurable.aemeasurable hlen
    (gmE_hullAn 𝕫 R c n _))

end LQGMetric.GM
