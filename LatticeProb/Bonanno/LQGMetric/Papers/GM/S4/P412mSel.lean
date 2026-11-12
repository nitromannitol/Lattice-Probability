/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412mSel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412gCentre

/-!
# Guard centres without sure boundedness (decision D106, part 1)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
L4.15 Step 3, l. 2159–2183 (the points `z_y ∈ ∂𝓑^•_{t_k}` chosen depending only on
`(𝓑^•_{t_k}, h|)`); decision D106.

`p412f_frontier_select_near` and `p412g_grid_centres` need `K ω` bounded with `∂K ω ≠ ∅` for
*every* `ω`. For a weak LQG metric this holds only a.s. (the metric may be changed on a GFF-null
set of fields, DEC-106). Here the random set is replaced by `K' ω = K ω` if `K ω` is bounded and
`{z₀}` otherwise; `{K ω bounded}` is a `σ(K)`-event, so `σ(K') ≤ σ(K)`.

* `p412m_bdd_meas`: `{ω | K ω bounded}` is `setSigma K`-measurable;
* `p412m_select_near`: as `p412f_frontier_select_near`, the frontier properties at bounded `ω`;
* `p412m_grid_centres`: as `p412g_grid_centres` (same proof), frontier properties at bounded `ω`.
Own routine arguments (GM silent on measurability).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory MeasurableSpace Set Filter Metric
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

/-- boundedness of a random set is an event of `σ(K)` -/
theorem p412m_bdd_meas {Ω : Type} (K : Ω → Set ℂ) :
    MeasurableSet[setSigma K] {ω | Bornology.IsBounded (K ω)} := by
  have e : {ω | Bornology.IsBounded (K ω)} =
      ⋃ n : ℕ, {ω | (K ω ∩ (closedBall (0 : ℂ) n)ᶜ).Nonempty}ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_compl_iff]
    constructor
    · intro hb
      obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).1 hb
      refine ⟨⌈r⌉₊, fun ⟨w, hw, hw'⟩ => hw' ?_⟩
      exact closedBall_subset_closedBall (Nat.le_ceil r) (hr hw)
    · rintro ⟨n, hn⟩
      refine (isBounded_closedBall (x := (0 : ℂ)) (r := (n : ℝ))).subset fun w hw => ?_
      by_contra h'
      exact hn ⟨w, hw, h'⟩
  rw [e]
  refine MeasurableSet.iUnion fun n => MeasurableSet.compl ?_
  exact measurableSet_generateFrom ⟨(closedBall (0 : ℂ) n)ᶜ, isClosed_closedBall.isOpen_compl, rfl⟩

/-- **frontier selection near `q`** at the bounded `ω` (D106) -/
theorem p412m_select_near {Ω : Type} (K : Ω → Set ℂ) (hKc : ∀ ω, IsClosed (K ω)) (z₀ : ℂ)
    (hz : ∀ ω, z₀ ∈ K ω) (q : ℂ) (ρ : ℝ) :
    ∃ x : Ω → ℂ, Measurable[setSigma K] x ∧ ∀ ω, Bornology.IsBounded (K ω) →
      x ω ∈ frontier (K ω) ∧
      ((frontier (K ω) ∩ closedBall q ρ).Nonempty → x ω ∈ closedBall q ρ) := by
  classical
  set K' : Ω → Set ℂ := fun ω => if Bornology.IsBounded (K ω) then K ω else {z₀} with hK'
  have hK'c : ∀ ω, IsClosed (K' ω) := fun ω => by
    simp only [hK']; split_ifs
    · exact hKc ω
    · exact isClosed_singleton
  have hK'b : ∀ ω, Bornology.IsBounded (K' ω) ∧ z₀ ∈ K' ω := fun ω => by
    simp only [hK']; split_ifs with hb
    · exact ⟨hb, hz ω⟩
    · exact ⟨Bornology.isBounded_singleton, rfl⟩
  have hK'ne : ∀ ω, (frontier (K' ω)).Nonempty := fun ω =>
    nonempty_frontier_iff.2 ⟨⟨z₀, (hK'b ω).2⟩, fun hU => by
      have := (hK'b ω).1
      rw [hU] at this
      exact NormedSpace.unbounded_univ ℝ ℂ this⟩
  obtain ⟨x, hxm, hx⟩ := p412f_frontier_select_near K' hK'c (fun ω => (hK'b ω).1) hK'ne q ρ
  have hle : setSigma K' ≤ setSigma K := by
    refine generateFrom_le ?_
    rintro _ ⟨U, hU, rfl⟩
    have e : {ω | (K' ω ∩ U).Nonempty} =
        ({ω | Bornology.IsBounded (K ω)} ∩ {ω | (K ω ∩ U).Nonempty}) ∪
          ({ω | Bornology.IsBounded (K ω)}ᶜ ∩ {_ω | z₀ ∈ U}) := by
      ext ω
      by_cases hb : Bornology.IsBounded (K ω)
      · simp [hK', hb]
      · simp [hK', hb]
    rw [e]
    exact ((p412m_bdd_meas K).inter (measurableSet_generateFrom ⟨U, hU, rfl⟩)).union
      ((p412m_bdd_meas K).compl.inter (MeasurableSet.const _))
  refine ⟨x, hxm.mono hle le_rfl, fun ω hb => ?_⟩
  have := hx ω
  simp only [hK', if_pos hb] at this
  exact this

/-- **centres from a random grid set** at the bounded `ω` (D106; the proof of
`p412g_grid_centres` with the selections of `p412m_select_near`) -/
theorem p412m_grid_centres {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (h : Ω → DistC)
    (K : Ω → Set ℂ) (hKc : ∀ ω, IsClosed (K ω)) (z₀ : ℂ) (hz : ∀ ω, z₀ ∈ K ω) (g : ℕ → ℂ)
    (ρ : ℝ) (Q : Ω → Set ℕ) (hQ : ∀ i, AEEventIn P (localSigma h K) {ω | i ∈ Q ω}) (N : ℕ)
    (hN : ∀ᵐ ω ∂P, (Q ω).encard ≤ N) :
    ∃ x : ℕ → Ω → ℂ, (∀ j, Measurable[localSigma h K] (x j)) ∧
      (∀ j ω, Bornology.IsBounded (K ω) → x j ω ∈ frontier (K ω)) ∧
      ∀ᵐ ω ∂P, ∀ i ∈ Q ω, ∃ j < N, (Bornology.IsBounded (K ω) →
        (frontier (K ω) ∩ closedBall (g i) ρ).Nonempty → x j ω ∈ closedBall (g i) ρ) := by
  classical
  have hsel := fun i => p412m_select_near K hKc z₀ hz (g i) ρ
  choose sel hselm hsel using hsel
  have hselm' : ∀ i, Measurable[localSigma h K] (sel i) := fun i =>
    (hselm i).mono (p412f_setSigma_le_localSigma h K) le_rfl
  obtain ⟨Z, hZm, hZ⟩ := exists_measurable_code (m := localSigma h K) hQ
  set cnt : Ω → ℕ → ℕ := fun ω i => Nat.count (fun k => Z ω k = true) i with hcnt
  let x : ℕ → Ω → ℂ := fun j ω =>
    if hx : ∃ i, Z ω i = true ∧ cnt ω i = j then sel (Nat.find hx) ω else sel 0 ω
  have hev : ∀ i j, MeasurableSet[localSigma h K] {ω | Z ω i = true ∧ cnt ω i = j} := by
    intro i j
    refine MeasurableSet.inter ?_ ?_
    · exact (measurable_pi_apply i).comp hZm (measurableSet_singleton true)
    · exact ((p412g_measurable_count i).comp hZm) (measurableSet_singleton j)
  refine ⟨x, fun j => ?_, fun j ω hb => ?_, ?_⟩
  · intro B hB
    have e : x j ⁻¹' B = (⋃ i, {ω | Z ω i = true ∧ cnt ω i = j} ∩ sel i ⁻¹' B) ∪
        ({ω | ¬ ∃ i, Z ω i = true ∧ cnt ω i = j} ∩ sel 0 ⁻¹' B) := by
      ext ω
      simp only [mem_preimage, mem_union, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      by_cases hx : ∃ i, Z ω i = true ∧ cnt ω i = j
      · simp only [x, dif_pos hx, hx, not_true_eq_false, false_and, or_false]
        constructor
        · intro hB'
          exact ⟨Nat.find hx, Nat.find_spec hx, hB'⟩
        · rintro ⟨i, hi, hB'⟩
          rwa [p412g_find_eq hi.1 hi.2 hx]
      · simp only [x, dif_neg hx, hx, not_false_eq_true, true_and]
        constructor
        · exact Or.inr
        · rintro (⟨i, hi, -⟩ | hB')
          · exact absurd ⟨i, hi⟩ hx
          · exact hB'
    rw [e]
    refine MeasurableSet.union (MeasurableSet.iUnion fun i => (hev i j).inter (hselm' i hB)) ?_
    have hne' : MeasurableSet[localSigma h K] {ω | ∃ i, Z ω i = true ∧ cnt ω i = j} := by
      have : {ω | ∃ i, Z ω i = true ∧ cnt ω i = j} = ⋃ i, {ω | Z ω i = true ∧ cnt ω i = j} := by
        ext ω; simp only [mem_ofPred_eq, mem_iUnion]
      rw [this]; exact MeasurableSet.iUnion fun i => hev i j
    exact hne'.compl.inter (hselm' 0 hB)
  · simp only [x]
    split_ifs
    · exact (hsel _ ω hb).1
    · exact (hsel 0 ω hb).1
  · filter_upwards [hZ, hN] with ω hZω hNω
    intro i hi
    have hZi : Z ω i = true := (hZω i).2 hi
    refine ⟨cnt ω i, ?_, fun hb hmeet => ?_⟩
    · set T : Finset ℕ := (Finset.range i).filter fun k => Z ω k = true
      have hcT : cnt ω i = T.card := Nat.count_eq_card_filter_range _ i
      have hsub : ((insert i T : Finset ℕ) : Set ℕ) ⊆ Q ω := by
        intro k hk
        rcases Finset.mem_insert.1 hk with rfl | hk
        · exact hi
        · exact (hZω k).1 (Finset.mem_filter.1 hk).2
      have hiT : i ∉ T := fun h => by simp [T] at h
      have hcard := (Set.encard_le_encard hsub).trans hNω
      rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_insert_of_notMem hiT] at hcard
      have : T.card + 1 ≤ N := by exact_mod_cast hcard
      omega
    · have hx : ∃ i', Z ω i' = true ∧ cnt ω i' = cnt ω i := ⟨i, hZi, rfl⟩
      have : x (cnt ω i) ω = sel i ω := by
        simp only [x, dif_pos hx, p412g_find_eq hZi rfl hx]
      rw [this]
      exact (hsel i ω hb).2 hmeet

end LQGMetric.GM
