/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L45Det6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Det5

/-!
# GM Lemma 4.5: decoding the point of `Conf_k` from its arc (task P2-E2R)

GM, arXiv:1905.00383, `uniqueness-final.tex` l. 1674–1675 ("this point is determined by which arc
of `𝓘_k` contains `P(t_k)`"), deterministic part of `GMConfPtSel`: with `Conf` finite and the hit
pattern `pat x = (n ↦ arcOf x ∩ V n ≠ ∅)` injective on `Conf` (`gm_conf_hitPattern_injOn`), a
point `x ∈ Conf` lies in a half-plane `H` iff for all long prefixes of `pat x` some point of
`Conf ∩ H` has an arc with that prefix (`gm_conf_decode`); `x` is then the supremum of the
rational half-planes it lies in (`gm_ereal_iSup_rat`). The prefix events `gmConfEv` are field
events of the type handled by `gm_aeEventIn_Kt`. Own elementary arguments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- test half-planes `{re > a}` (`true`) and `{im > a}` (`false`) -/
def gmHalf (j : Bool × ℚ) : Set ℂ :=
  if j.1 then {w | ((j.2 : ℝ)) < w.re} else {w | ((j.2 : ℝ)) < w.im}

open Classical in
/-- the indices `n < L` with `σ n` -/
def gmPreF (σ : ℕ → Prop) (L : ℕ) : Finset ℕ := (Finset.range L).filter fun n => σ n

open Classical in
/-- the indices `n < L` with `¬ σ n` -/
def gmPreG (σ : ℕ → Prop) (L : ℕ) : Finset ℕ := (Finset.range L).filter fun n => ¬ σ n

/-- the hit pattern of `arcOf x` on `V` -/
def gmPat (V : ℕ → Set ℂ) (d : ContMetric) (𝕫 : ℂ) (t : ℝ) (x : ℂ) : ℕ → Prop :=
  fun n => (arcOf d 𝕫 t x ∩ V n).Nonempty

/-- a finite set on which the patterns are injective is separated by a finite prefix -/
lemma gm_exists_prefix {C : Set ℂ} (hfin : C.Finite) {p : ℂ → ℕ → Prop} (hinj : InjOn p C)
    {x : ℂ} (hx : x ∈ C) :
    ∃ L₀, ∀ x' ∈ C, (∀ n < L₀, (p x' n ↔ p x n)) → x' = x := by
  classical
  have hsep : ∀ x' ∈ C, x' ≠ x → ∃ n, ¬ (p x' n ↔ p x n) := by
    intro x' hx' hne
    by_contra hall
    push_neg at hall
    exact hne (hinj hx' hx (funext fun n => propext (hall n)))
  choose! N hN using hsep
  refine ⟨hfin.toFinset.sup (fun x' => N x' + 1), fun x' hx' hpre => ?_⟩
  by_contra hne
  apply hN x' hx' hne
  apply hpre
  have := Finset.le_sup (f := fun x' => N x' + 1) (hfin.mem_toFinset.2 hx')
  omega

open Classical in
/-- a real number is the supremum of the rationals below it, in `EReal` -/
lemma gm_ereal_iSup_rat (r : ℝ) :
    (⨆ a : ℚ, if ((a : ℝ)) < r then (((a : ℝ)) : EReal) else ⊥) = (r : EReal) := by
  apply le_antisymm
  · refine iSup_le fun a => ?_
    split_ifs with h
    · exact EReal.coe_le_coe_iff.2 h.le
    · exact bot_le
  · refine le_of_forall_lt fun c hc => ?_
    obtain ⟨a, hca, har⟩ := EReal.exists_rat_btwn_of_lt hc
    refine lt_of_lt_of_le hca (le_iSup_of_le a ?_)
    rw [ite_cond_eq_true _ _ (eq_true (EReal.coe_lt_coe_iff.1 har))]

open Classical in
/-- the prefix predicate read off a code `Z` -/
def gmPre {Ω : Type} (Z : Ω → (Bool × ℚ) × Finset ℕ × Finset ℕ → Bool) (ω : Ω) (σ : ℕ → Prop)
    (j : Bool × ℚ) : Prop :=
  ∃ L, ∀ L' ≥ L, Z ω (j, gmPreF σ L', gmPreG σ L') = true

open Classical in
/-- the decoder `Ξ`: the supremum of the rational half-planes certified by the code -/
def gmXi {Ω : Type} (Z : Ω → (Bool × ℚ) × Finset ℕ × Finset ℕ → Bool) (p : Ω × (ℕ → Prop)) : ℂ :=
  ((⨆ a : ℚ, if gmPre Z p.1 p.2 (true, a) then (((a : ℝ)) : EReal) else ⊥).toReal : ℂ) +
    ((⨆ a : ℚ, if gmPre Z p.1 p.2 (false, a) then (((a : ℝ)) : EReal) else ⊥).toReal : ℂ) *
      Complex.I

lemma gm_measurableSet_pre_eq (L : ℕ) (F : Finset ℕ) :
    MeasurableSet {σ : ℕ → Prop | gmPreF σ L = F} ∧ MeasurableSet {σ : ℕ → Prop | gmPreG σ L = F} := by
  classical
  have h0 : ∀ n, MeasurableSet {σ : ℕ → Prop | σ n} := fun n =>
    measurableSet_setOfPred.2 (measurable_pi_apply n)
  have hcoord : ∀ n (q : Prop), MeasurableSet {σ : ℕ → Prop | σ n ↔ q} := fun n q => by
    by_cases hq : q
    · convert h0 n using 1; ext σ; simp [hq]
    · convert (h0 n).compl using 1; ext σ; simp [hq]
  have hcoord' : ∀ n (q : Prop), MeasurableSet {σ : ℕ → Prop | ¬ σ n ↔ q} := fun n q => by
    by_cases hq : q
    · convert (h0 n).compl using 1; ext σ; simp [hq]
    · convert h0 n using 1; ext σ; simp [hq]
  have e1 : {σ : ℕ → Prop | gmPreF σ L = F} =
      if F ⊆ Finset.range L then ⋂ n ∈ Finset.range L, {σ : ℕ → Prop | σ n ↔ n ∈ F} else ∅ := by
    ext σ
    split_ifs with hF
    · simp only [mem_ofPred_eq, mem_iInter, Finset.ext_iff, gmPreF, Finset.mem_filter,
        Finset.mem_range]
      constructor
      · intro h n hn
        exact ⟨fun hs => (h n).1 ⟨hn, hs⟩, fun hm => ((h n).2 hm).2⟩
      · intro h n
        exact ⟨fun hn => (h n hn.1).1 hn.2, fun hm =>
          ⟨Finset.mem_range.1 (hF hm), (h n (Finset.mem_range.1 (hF hm))).2 hm⟩⟩
    · simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro rfl
      exact hF (Finset.filter_subset _ _)
  have e2 : {σ : ℕ → Prop | gmPreG σ L = F} =
      if F ⊆ Finset.range L then ⋂ n ∈ Finset.range L, {σ : ℕ → Prop | ¬ σ n ↔ n ∈ F} else ∅ := by
    ext σ
    split_ifs with hF
    · simp only [mem_ofPred_eq, mem_iInter, Finset.ext_iff, gmPreG, Finset.mem_filter,
        Finset.mem_range]
      constructor
      · intro h n hn
        exact ⟨fun hs => (h n).1 ⟨hn, hs⟩, fun hm => ((h n).2 hm).2⟩
      · intro h n
        exact ⟨fun hn => (h n hn.1).1 hn.2, fun hm =>
          ⟨Finset.mem_range.1 (hF hm), (h n (Finset.mem_range.1 (hF hm))).2 hm⟩⟩
    · simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro rfl
      exact hF (Finset.filter_subset _ _)
  constructor
  · rw [e1]
    split_ifs
    · exact MeasurableSet.biInter (Finset.range L).countable_toSet fun n _ => hcoord n _
    · exact MeasurableSet.empty
  · rw [e2]
    split_ifs
    · exact MeasurableSet.biInter (Finset.range L).countable_toSet fun n _ => hcoord' n _
    · exact MeasurableSet.empty

/-- the decoder is measurable for `m ⊗ σ(patterns)` when the code is `m`-measurable -/
theorem gm_measurable_gmXi {Ω : Type} (m : MeasurableSpace Ω)
    {Z : Ω → (Bool × ℚ) × Finset ℕ × Finset ℕ → Bool} (hZ : Measurable[m] Z) :
    @Measurable _ _ (m.prod inferInstance) _ (gmXi Z) := by
  classical
  let _ := m
  have hpre : ∀ j, MeasurableSet {p : Ω × (ℕ → Prop) | gmPre Z p.1 p.2 j} := by
    intro j
    have hL : ∀ L', MeasurableSet {p : Ω × (ℕ → Prop) |
        Z p.1 (j, gmPreF p.2 L', gmPreG p.2 L') = true} := by
      intro L'
      have e : {p : Ω × (ℕ → Prop) | Z p.1 (j, gmPreF p.2 L', gmPreG p.2 L') = true} =
          ⋃ FG : Finset ℕ × Finset ℕ, {ω | Z ω (j, FG.1, FG.2) = true} ×ˢ
            ({σ | gmPreF σ L' = FG.1} ∩ {σ | gmPreG σ L' = FG.2}) := by
        ext p
        simp only [mem_ofPred_eq, mem_iUnion, mem_prod, mem_inter_iff]
        exact ⟨fun h => ⟨(gmPreF p.2 L', gmPreG p.2 L'), h, rfl, rfl⟩,
          fun ⟨FG, h, h1, h2⟩ => by rw [h1, h2]; exact h⟩
      rw [e]
      refine MeasurableSet.iUnion fun FG => MeasurableSet.prod ?_
        ((gm_measurableSet_pre_eq L' FG.1).1.inter (gm_measurableSet_pre_eq L' FG.2).2)
      exact (measurable_pi_apply _).comp hZ (measurableSet_singleton true)
    have e : {p : Ω × (ℕ → Prop) | gmPre Z p.1 p.2 j} =
        ⋃ L, ⋂ L', ⋂ (_ : L' ≥ L), {p : Ω × (ℕ → Prop) |
          Z p.1 (j, gmPreF p.2 L', gmPreG p.2 L') = true} := by
      ext p
      simp only [gmPre, mem_ofPred_eq, mem_iUnion, mem_iInter]
    rw [e]
    exact MeasurableSet.iUnion fun L => MeasurableSet.iInter fun L' =>
      MeasurableSet.iInter fun _ => hL L'
  have hsup : ∀ b : Bool, Measurable fun p : Ω × (ℕ → Prop) =>
      (⨆ a : ℚ, if gmPre Z p.1 p.2 (b, a) then (((a : ℝ)) : EReal) else ⊥).toReal :=
    fun b => (Measurable.iSup fun a => Measurable.ite (hpre (b, a)) measurable_const
      measurable_const).ereal_toReal
  exact (Complex.measurable_ofReal.comp (hsup true)).add
    ((Complex.measurable_ofReal.comp (hsup false)).mul_const _)

end LQGMetric.GM
