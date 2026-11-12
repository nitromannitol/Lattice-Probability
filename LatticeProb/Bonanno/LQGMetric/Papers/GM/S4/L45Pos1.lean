/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L45Pos1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE10

/-!
# GM Lemma 4.5, decoding events with positive hit clauses: analyticity (task P2-E2T)

GM = Gwynne–Miller, arXiv:1905.00383v3, Lemma 4.5 (l. 1655–1688). The decoding event
`gmGeodCEv` of `gm_L4_5_E2b_of_null` contains the negative clause "`arcOf x` misses `V n`"
under `∃ x`, so it is not visibly analytic (handoff/P2-E3d.md). Here we prove that the
POSITIVE counting events

  `m ≤ #{x ∈ Conf(s,t) : arcOf x hits V n for n ∈ F, and Φ(x)}`

are analytic on `lenSet` (`gmP_leEncardAn`): they are projections of Borel sets (an injective
`m`-tuple of witnesses, and for each witness and each `n ∈ F` a point of `arcOf x ∩ V n`).
In `L45Pos2` the event with negative clauses is recovered from these by inclusion–exclusion,
since `Conf(s,t)` is a.s. finite (GM.S4.1). Own descriptive-set-theory argument (D65); GM do
not discuss measurability.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

/-- the points of `Conf(s,t)` whose arcs hit `V n` (`n ∈ F`), miss `V n` (`n ∈ G`), with `Φ` -/
def gmPosS (V : ℕ → Set ℂ) (Φ : ContMetric → ℂ → Prop) (d : ContMetric) (𝕫 : ℂ) (s t : ℝ)
    (F G : Finset ℕ) : Set ℂ :=
  {x | x ∈ confPts d 𝕫 s t ∧ (∀ n ∈ F, gmPat V d 𝕫 t x n) ∧
    (∀ n ∈ G, ¬ gmPat V d 𝕫 t x n) ∧ Φ d x}

theorem gmAn_biInter {α ι : Type} [MeasurableSpace α] {L : Set α} {A : ι → Set α}
    (s : Finset ι) (h : ∀ i ∈ s, GMAnalyticOn L (A i)) : GMAnalyticOn L (⋂ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using gmAn_of_measurableSet (L := L) MeasurableSet.univ
  | insert a s ha ih =>
    rw [Finset.set_biInter_insert]
    exact gmAn_inter (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- `x ∈ Conf(τ c₀, τ c)` and `arcOf x` meets `U` (Borel), analytic in `(d, x)` on `lenSet` -/
theorem gmP_hitAn (𝕫 : ℂ) (R c₀ c : ℝ) {U : Set ℂ} (hU : MeasurableSet U) :
    GMAnalyticOn {p : ContMetric × ℂ | p.1 ∈ lenSet}
      {p | p.2 ∈ confPts p.1 𝕫 (tauD p.1 𝕫 R * c₀) (tauD p.1 𝕫 R * c) ∧
        (arcOf p.1 𝕫 (tauD p.1 𝕫 R * c) p.2 ∩ U).Nonempty} := by
  have hτ := gm_measurable_tauB 𝕫 R
  have hf : Measurable fun q : (ContMetric × ℂ) × ℂ =>
      ((q.1.1, gmTauB 𝕫 R q.1.1 * c₀, gmTauB 𝕫 R q.1.1 * c), q.1.2, q.2) :=
    ((measurable_fst.comp measurable_fst).prodMk
      (((hτ.comp (measurable_fst.comp measurable_fst)).mul_const c₀).prodMk
        ((hτ.comp (measurable_fst.comp measurable_fst)).mul_const c))).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have A1 := gmAn_preimage hf (gm_arcRelAn 𝕫)
  have A1' : GMAnalyticOn {q : (ContMetric × ℂ) × ℂ | q.1 ∈ {p : ContMetric × ℂ | p.1 ∈ lenSet}}
      _ := gmAn_mono A1 fun q hq => hq
  have A2 := gmAn_inter A1' (gmAn_of_measurableSet
    (A := {q : (ContMetric × ℂ) × ℂ | q.2 ∈ U}) (measurable_snd hU))
  refine gmAn_congr (gmAn_exists A2) fun p hp => ?_
  have hd : p.1 ∈ lenSet := hp
  simp only [mem_ofPred_eq, mem_preimage, mem_inter_iff, gm_tauD_eq_tauB hd]
  constructor
  · rintro ⟨y, ⟨hx, hy⟩, hyU⟩; exact ⟨hx, y, hy, hyU⟩
  · rintro ⟨hx, y, hy, hyU⟩; exact ⟨y, ⟨hx, hy⟩, hyU⟩

/-- a point of `Conf(s,t)` lies on a leftmost geodesic to a point of its own arc -/
lemma gmP_arcOf_nonempty {d : ContMetric} {𝕫 : ℂ} {s t : ℝ} {x : ℂ}
    (hx : x ∈ confPts d 𝕫 s t) : (arcOf d 𝕫 t x ∩ univ).Nonempty := by
  obtain ⟨-, y, P, hP, u, hu, hPu⟩ := hx
  exact ⟨y, ⟨hP.1, P, hP, u, hu, hPu⟩, mem_univ _⟩

/-- `∃` geodesic `Q` from `𝕫` to `x` with `Q u ∈ gmHalf j`, analytic in `(d, x)` -/
theorem gmP_geodHalfAn (𝕫 : ℂ) (u : unitInterval) (j : Bool × ℚ) :
    GMAnalyticOn {p : ContMetric × ℂ | p.1 ∈ lenSet}
      {p | ∃ Q : C(unitInterval, ℂ), IsGeod01 p.1 𝕫 p.2 Q ∧ Q u ∈ gmHalf j} := by
  have hcl : IsClosed {q : (ContMetric × ℂ) × C(unitInterval, ℂ) | IsGeod01 q.1.1 𝕫 q.1.2 q.2} := by
    have e : {q : (ContMetric × ℂ) × C(unitInterval, ℂ) | IsGeod01 q.1.1 𝕫 q.1.2 q.2} =
        {q | q.2 0 = 𝕫} ∩ ({q | q.2 1 = q.1.2} ∩ ⋂ s : unitInterval, ⋂ t : unitInterval,
          {q | q.1.1.1 (q.2 s, q.2 t) = |(t : ℝ) - s| * q.1.1.1 (𝕫, q.1.2)}) := by
      ext q; simp only [IsGeod01, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    rw [e]
    refine (isClosed_eq ((continuous_eval_const 0).comp continuous_snd) continuous_const).inter
      ((isClosed_eq ((continuous_eval_const 1).comp continuous_snd)
        (continuous_snd.comp continuous_fst)).inter
        (isClosed_iInter fun s => isClosed_iInter fun t => isClosed_eq ?_ ?_))
    · exact continuous_contMetric_apply.comp ((continuous_fst.comp continuous_fst).prodMk
        (((continuous_eval_const s).comp continuous_snd).prodMk
          ((continuous_eval_const t).comp continuous_snd)))
    · exact continuous_const.mul (continuous_contMetric_apply.comp
        ((continuous_fst.comp continuous_fst).prodMk
          (continuous_const.prodMk (continuous_snd.comp continuous_fst))))
  have hg : Measurable fun q : (ContMetric × ℂ) × C(unitInterval, ℂ) => q.2 u :=
    (continuous_eval_const u).measurable.comp measurable_snd
  refine gmAn_congr (gmAn_exists (gmAn_of_measurableSet
    (L := {q : (ContMetric × ℂ) × C(unitInterval, ℂ) | q.1 ∈ {p : ContMetric × ℂ | p.1 ∈ lenSet}})
    (A := {q : (ContMetric × ℂ) × C(unitInterval, ℂ) | IsGeod01 q.1.1 𝕫 q.1.2 q.2 ∧
      q.2 u ∈ gmHalf j}) (hcl.measurableSet.inter (hg (gmE_measurableSet_half j)))))
    fun p _ => Iff.rfl

/-- the defining property of `gmPosS … F ∅` is analytic in `(d, x)` -/
theorem gmP_ptAn {V : ℕ → Set ℂ} (hVo : ∀ n, IsOpen (V n)) {Φ : ContMetric → ℂ → Prop}
    (hΦ : GMAnalyticOn {p : ContMetric × ℂ | p.1 ∈ lenSet} {p | Φ p.1 p.2}) (𝕫 : ℂ)
    (R c₀ c : ℝ) (F : Finset ℕ) :
    GMAnalyticOn {p : ContMetric × ℂ | p.1 ∈ lenSet}
      {p | p.2 ∈ gmPosS V Φ p.1 𝕫 (tauD p.1 𝕫 R * c₀) (tauD p.1 𝕫 R * c) F ∅} := by
  have A := gmAn_inter (gmAn_inter (gmP_hitAn 𝕫 R c₀ c MeasurableSet.univ)
    (gmAn_biInter F fun n _ => gmP_hitAn 𝕫 R c₀ c (hVo n).measurableSet)) hΦ
  refine gmAn_congr A fun p _ => ?_
  simp only [gmPosS, gmPat, mem_ofPred_eq, mem_inter_iff, mem_iInter, Finset.notMem_empty,
    IsEmpty.forall_iff, implies_true, true_and]
  constructor
  · rintro ⟨⟨⟨hx, -⟩, hF⟩, hΦp⟩
    exact ⟨hx, fun n hn => (hF n hn).2, hΦp⟩
  · rintro ⟨hx, hF, hΦp⟩
    exact ⟨⟨⟨hx, gmP_arcOf_nonempty hx⟩, fun n hn => ⟨hx, hF n hn⟩⟩, hΦp⟩

/-- `m ≤ #S` iff `S` contains an injective `m`-tuple -/
lemma gmP_le_encard_iff (S : Set ℂ) (m : ℕ) :
    (m : ℕ∞) ≤ S.encard ↔ ∃ f : Fin m → ℂ, Function.Injective f ∧ ∀ i, f i ∈ S := by
  classical
  constructor
  · intro hm
    obtain ⟨t, hts, htm⟩ := exists_subset_encard_eq hm
    have ht : t.Finite := finite_of_encard_eq_coe htm
    have hcard : ht.toFinset.card = m := by
      have := htm
      rw [← ht.coe_toFinset, encard_coe_eq_coe_finsetCard] at this
      exact_mod_cast this
    let e := ht.toFinset.equivFinOfCardEq hcard
    refine ⟨fun i => (e.symm i : ℂ), Subtype.val_injective.comp e.symm.injective, fun i => ?_⟩
    exact hts ((ht.mem_toFinset).1 (e.symm i).2)
  · rintro ⟨f, hf, hfS⟩
    have := encard_le_encard_of_injOn (s := (univ : Set (Fin m))) (t := S) (f := f)
      (fun i _ => hfS i) hf.injOn
    simpa [encard_univ] using this

lemma gmP_measurableSet_inj (m : ℕ) :
    MeasurableSet {f : Fin m → ℂ | Function.Injective f} := by
  have e : {f : Fin m → ℂ | Function.Injective f} =
      ⋂ i, ⋂ j, ({f : Fin m → ℂ | f i = f j}ᶜ ∪ {_f | i = j}) := by
    ext f
    simp only [Function.Injective, mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff]
    exact forall_congr' fun i => forall_congr' fun j => imp_iff_not_or
  rw [e]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    (measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)).compl.union
      (MeasurableSet.const _)

/-- **positive counting events are analytic on `lenSet`** -/
theorem gmP_leEncardAn {V : ℕ → Set ℂ} (hVo : ∀ n, IsOpen (V n)) {Φ : ContMetric → ℂ → Prop}
    (hΦ : GMAnalyticOn {p : ContMetric × ℂ | p.1 ∈ lenSet} {p | Φ p.1 p.2}) (𝕫 : ℂ)
    (R c₀ c : ℝ) (F : Finset ℕ) (m : ℕ) :
    GMAnalyticOn lenSet {d | (m : ℕ∞) ≤
      (gmPosS V Φ d 𝕫 (tauD d 𝕫 R * c₀) (tauD d 𝕫 R * c) F ∅).encard} := by
  have hP := gmP_ptAn hVo hΦ 𝕫 R c₀ c F
  have Ai : ∀ i : Fin m, GMAnalyticOn {q : ContMetric × (Fin m → ℂ) | q.1 ∈ lenSet}
      {q | q.2 i ∈ gmPosS V Φ q.1 𝕫 (tauD q.1 𝕫 R * c₀) (tauD q.1 𝕫 R * c) F ∅} := fun i =>
    gmAn_preimage (f := fun q : ContMetric × (Fin m → ℂ) => (q.1, q.2 i))
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)) hP
  have A := gmAn_inter (gmAn_of_measurableSet
    (L := {q : ContMetric × (Fin m → ℂ) | q.1 ∈ lenSet})
    (A := {q : ContMetric × (Fin m → ℂ) | Function.Injective q.2})
    (measurable_snd (gmP_measurableSet_inj m))) (gmAn_biInter Finset.univ fun i _ => Ai i)
  refine gmAn_congr (gmAn_exists A) fun d _ => ?_
  simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, Finset.mem_univ, true_implies]
  rw [gmP_le_encard_iff]

end LQGMetric.GM
