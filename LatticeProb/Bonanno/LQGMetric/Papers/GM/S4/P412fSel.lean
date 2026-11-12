/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412fSel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412fHit
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# A measurable point of `∂𝓑^•_t` (toward D94)

GM L4.15 Step 3 (l. 2161) chooses the centres `z_y ∈ ∂𝓑^•_{t_k}` "in a manner depending only
on `(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})`", and CONF Lemma 3.6 (`CONFLem3_6At`) takes a point
`x ω ∈ ∂𝓑^•_τ` measurable w.r.t. `localSigma h 𝓑^•_τ`.

* `p412f_meas_select`: a random nonempty compact set `F` with measurable hit events
  `{F ∩ U ≠ ∅}` (`U` open) has a measurable selection, the lexicographic minimum
  (`Re` first, then `Im`) — own elementary proof (the standard Kuratowski–Ryll-Nardzewski
  theorem is not in mathlib; for compact values the lexicographic minimum suffices).
* `p412f_frontier_select`: for a random closed bounded set `K` with `∂K ≠ ∅` there is a
  `σ(K)`-measurable (hence `localSigma h K`-measurable) `x` with `x ω ∈ ∂K(ω)` for all `ω`
  (via `p412f_frontier_hit_meas`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- **measurable selection of a random compact set** (lexicographic minimum) -/
theorem p412f_meas_select {Ω : Type} [MeasurableSpace Ω] (F : Ω → Set ℂ)
    (hFc : ∀ ω, IsCompact (F ω)) (hFne : ∀ ω, (F ω).Nonempty)
    (hhit : ∀ U : Set ℂ, IsOpen U → MeasurableSet {ω | (F ω ∩ U).Nonempty}) :
    ∃ x : Ω → ℂ, Measurable x ∧ ∀ ω, x ω ∈ F ω := by
  -- the minimal real part
  set m₁ : Ω → ℝ := fun ω => sInf (Complex.re '' F ω) with hm₁
  have hc1 : ∀ ω, IsCompact (Complex.re '' F ω) := fun ω =>
    (hFc ω).image Complex.continuous_re
  have hm₁mem : ∀ ω, m₁ ω ∈ Complex.re '' F ω := fun ω =>
    (hc1 ω).sInf_mem ((hFne ω).image _)
  have hm₁le : ∀ ω, ∀ z ∈ F ω, m₁ ω ≤ z.re := fun ω z hz =>
    csInf_le (hc1 ω).bddBelow ⟨z, hz, rfl⟩
  have hm₁m : Measurable m₁ := measurable_of_Iio fun c => by
    have : m₁ ⁻¹' Iio c = {ω | (F ω ∩ {z : ℂ | z.re < c}).Nonempty} := by
      ext ω
      simp only [mem_preimage, mem_Iio, mem_setOf_eq]
      constructor
      · intro h
        obtain ⟨z, hz, hzr⟩ := hm₁mem ω
        exact ⟨z, hz, by simp only [mem_setOf_eq]; rw [hzr]; exact h⟩
      · rintro ⟨z, hz, hzc⟩
        exact lt_of_le_of_lt (hm₁le ω z hz) hzc
    rw [this]; exact hhit _ (isOpen_lt Complex.continuous_re continuous_const)
  -- the minimal imaginary part on `{Re = m₁}`
  set F₁ : Ω → Set ℂ := fun ω => F ω ∩ {z | z.re = m₁ ω} with hF₁
  have hF₁c : ∀ ω, IsCompact (F₁ ω) := fun ω =>
    (hFc ω).inter_right (isClosed_eq Complex.continuous_re continuous_const)
  have hF₁ne : ∀ ω, (F₁ ω).Nonempty := fun ω => by
    obtain ⟨z, hz, hzr⟩ := hm₁mem ω; exact ⟨z, hz, hzr⟩
  set m₂ : Ω → ℝ := fun ω => sInf (Complex.im '' F₁ ω) with hm₂
  have hc2 : ∀ ω, IsCompact (Complex.im '' F₁ ω) := fun ω =>
    (hF₁c ω).image Complex.continuous_im
  have hm₂mem : ∀ ω, m₂ ω ∈ Complex.im '' F₁ ω := fun ω =>
    (hc2 ω).sInf_mem ((hF₁ne ω).image _)
  have hm₂le : ∀ ω, ∀ z ∈ F₁ ω, m₂ ω ≤ z.im := fun ω z hz =>
    csInf_le (hc2 ω).bddBelow ⟨z, hz, rfl⟩
  have hm₂lt : ∀ ω d, m₂ ω < d ↔ ∃ d' : ℚ, (d' : ℝ) < d ∧ ∀ n : ℕ, ∃ q : ℚ,
      (q : ℝ) < m₁ ω + 1 / (n + 1) ∧ (F ω ∩ {z : ℂ | z.re < q ∧ z.im < d'}).Nonempty := by
    intro ω d
    constructor
    · intro h
      obtain ⟨z, hz, hzi⟩ := hm₂mem ω
      obtain ⟨d', h1, h2⟩ := exists_rat_btwn (show z.im < d by rw [hzi]; exact h)
      refine ⟨d', h2, fun n => ?_⟩
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show m₁ ω < m₁ ω + 1 / (n + 1) by
        have : (0 : ℝ) < 1 / (n + 1) := by positivity
        linarith)
      exact ⟨q, hq2, z, hz.1, by rw [hz.2]; exact hq1, h1⟩
    · rintro ⟨d', hd', H⟩
      choose q hq z hz using H
      obtain ⟨a, haF, φ, hφ, hlim⟩ := (hFc ω).tendsto_subseq (fun n => (hz n).1)
      have hre := (Complex.continuous_re.tendsto a).comp hlim
      have him := (Complex.continuous_im.tendsto a).comp hlim
      have hare : a.re ≤ m₁ ω := by
        refine le_of_forall_pos_le_add fun δ hδ => ?_
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
        refine le_of_tendsto hre (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
        have h1 : ((z ∘ φ) n).re < m₁ ω + 1 / ((φ n : ℝ) + 1) :=
          ((hz (φ n)).2.1).trans (hq (φ n))
        have h2 : (1 : ℝ) / ((φ n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
          have : (N : ℝ) ≤ φ n := by exact_mod_cast hn.trans (hφ.id_le n)
          exact one_div_le_one_div_of_le (by positivity) (by linarith)
        simp only [Function.comp_apply] at h1 ⊢
        linarith
      have haim : a.im ≤ d' :=
        le_of_tendsto him (Eventually.of_forall fun n => ((hz (φ n)).2.2).le)
      have haF₁ : a ∈ F₁ ω := ⟨haF, le_antisymm hare (hm₁le ω a haF)⟩
      exact lt_of_le_of_lt ((hm₂le ω a haF₁).trans haim) hd'
  have hm₂m : Measurable m₂ := measurable_of_Iio fun d => by
    have : m₂ ⁻¹' Iio d = ⋃ (d' : ℚ) (_ : (d' : ℝ) < d), ⋂ n : ℕ, ⋃ q : ℚ,
        ({ω | (q : ℝ) < m₁ ω + 1 / (n + 1)} ∩
          {ω | (F ω ∩ {z : ℂ | z.re < q ∧ z.im < d'}).Nonempty}) := by
      ext ω
      simp only [mem_preimage, mem_Iio, mem_iUnion, mem_iInter, mem_inter_iff, mem_setOf_eq,
        exists_prop]
      exact hm₂lt ω d
    rw [this]
    refine MeasurableSet.iUnion fun d' => MeasurableSet.iUnion fun _ =>
      MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q => ?_
    refine (measurableSet_lt measurable_const (hm₁m.add measurable_const)).inter
      (hhit _ ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt Complex.continuous_im continuous_const)))
  refine ⟨fun ω => Complex.measurableEquivRealProd.symm (m₁ ω, m₂ ω),
    Complex.measurableEquivRealProd.symm.measurable.comp (hm₁m.prodMk hm₂m), fun ω => ?_⟩
  obtain ⟨z, hz, hzi⟩ := hm₂mem ω
  have : z = Complex.measurableEquivRealProd.symm (m₁ ω, m₂ ω) := Complex.ext hz.2 hzi
  show Complex.measurableEquivRealProd.symm (m₁ ω, m₂ ω) ∈ F ω
  rw [← this]; exact hz.1

/-- hit events of `F ∩ closedBall q ρ` from those of a random compact `F` -/
theorem p412f_hit_inter_closedBall {Ω : Type} [MeasurableSpace Ω] (F : Ω → Set ℂ)
    (hFc : ∀ ω, IsCompact (F ω))
    (hhit : ∀ U : Set ℂ, IsOpen U → MeasurableSet {ω | (F ω ∩ U).Nonempty}) (q : ℂ) (ρ : ℝ)
    {U : Set ℂ} (hU : IsOpen U) :
    MeasurableSet {ω | (F ω ∩ closedBall q ρ ∩ U).Nonempty} := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have heq : {ω | (F ω ∩ closedBall q ρ ∩ U).Nonempty} =
      ⋃ p ∈ S, ⋃ r : ℚ, ⋃ (_ : 0 < (r : ℝ) ∧ closedBall p r ⊆ U), ⋂ n : ℕ,
        {ω | (F ω ∩ (ball p (r + 1 / (n + 1)) ∩ ball q (ρ + 1 / (n + 1)))).Nonempty} := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, mem_iInter, exists_prop]
    constructor
    · rintro ⟨x, ⟨hxF, hxq⟩, hxU⟩
      obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU x hxU
      obtain ⟨r, hr0, hrδ⟩ := exists_rat_btwn (show (0 : ℝ) < δ / 3 by positivity)
      have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
      obtain ⟨p, hpS, hpx⟩ := hSd.exists_mem_open isOpen_ball ⟨x, mem_ball_self hr0'⟩
      have hxp : dist x p < r := by rw [dist_comm]; exact hpx
      refine ⟨p, hpS, r, ⟨hr0', fun y hy => hδU ?_⟩, fun n => ⟨x, hxF, ?_, ?_⟩⟩
      · rw [mem_closedBall] at hy; rw [mem_ball]; linarith [dist_triangle y p x, dist_comm p x]
      · rw [mem_ball]; have : (0 : ℝ) < 1 / (n + 1) := by positivity
        linarith
      · rw [mem_ball]; have : (0 : ℝ) < 1 / (n + 1) := by positivity
        rw [mem_closedBall] at hxq; linarith
    · rintro ⟨p, -, r, ⟨hr0, hsub⟩, H⟩
      choose z hz using H
      obtain ⟨a, haF, φ, hφ, hlim⟩ := (hFc ω).tendsto_subseq (fun n => (hz n).1)
      have hd : ∀ (c : ℂ) (R : ℝ), (∀ n, dist (z n) c < R + 1 / (n + 1)) → dist a c ≤ R := by
        intro c R hc
        refine le_of_forall_pos_le_add fun δ hδ => ?_
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
        refine le_of_tendsto ((continuous_id.dist continuous_const).tendsto a |>.comp hlim)
          (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
        have h1 := hc (φ n)
        have h2 : (1 : ℝ) / ((φ n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
          have : (N : ℝ) ≤ φ n := by exact_mod_cast hn.trans (hφ.id_le n)
          exact one_div_le_one_div_of_le (by positivity) (by linarith)
        simp only [Function.comp_apply, id]
        linarith
      have hap := hd p r fun n => mem_ball.1 (hz n).2.1
      have haq := hd q ρ fun n => mem_ball.1 (hz n).2.2
      exact ⟨a, ⟨haF, mem_closedBall.2 haq⟩, hsub (mem_closedBall.2 hap)⟩
  rw [heq]
  exact MeasurableSet.biUnion hSc fun p _ => MeasurableSet.iUnion fun r =>
    MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun n =>
      hhit _ (isOpen_ball.inter isOpen_ball)

/-- **a measurable point of `∂K` near `q`**: for a random closed bounded `K` with `∂K ≠ ∅`, a
point `q` and `ρ`, there is a `σ(K)`-measurable `x` with `x ω ∈ ∂K(ω)` for all `ω`, and
`x ω ∈ closedBall q ρ` whenever `∂K(ω)` meets `closedBall q ρ` -/
theorem p412f_frontier_select_near {Ω : Type} (K : Ω → Set ℂ) (hKc : ∀ ω, IsClosed (K ω))
    (hKb : ∀ ω, Bornology.IsBounded (K ω)) (hne : ∀ ω, (frontier (K ω)).Nonempty)
    (q : ℂ) (ρ : ℝ) :
    ∃ x : Ω → ℂ, Measurable[setSigma K] x ∧ ∀ ω, x ω ∈ frontier (K ω) ∧
      ((frontier (K ω) ∩ closedBall q ρ).Nonempty → x ω ∈ closedBall q ρ) := by
  letI : MeasurableSpace Ω := setSigma K
  have hFc : ∀ ω, IsCompact (frontier (K ω)) := fun ω =>
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier
      ((hKb ω).subset ((hKc ω).frontier_subset))
  have hhit : ∀ U : Set ℂ, IsOpen U → MeasurableSet {ω | (frontier (K ω) ∩ U).Nonempty} :=
    fun U hU => p412f_frontier_hit_meas K hKc hU
  obtain ⟨x₀, hx₀m, hx₀⟩ := p412f_meas_select (fun ω => frontier (K ω)) hFc hne hhit
  set A : Set Ω := {ω | (frontier (K ω) ∩ closedBall q ρ).Nonempty} with hA
  have hAm : MeasurableSet A := by
    have := p412f_hit_inter_closedBall (fun ω => frontier (K ω)) hFc hhit q ρ isOpen_univ
    simpa [hA] using this
  -- the selection inside `∂K ∩ closedBall q ρ` on `A`
  classical
  set F' : Ω → Set ℂ := fun ω => if ω ∈ A then frontier (K ω) ∩ closedBall q ρ
    else frontier (K ω) with hF'
  have hF'c : ∀ ω, IsCompact (F' ω) := fun ω => by
    simp only [hF']; split_ifs
    · exact (hFc ω).inter_right isClosed_closedBall
    · exact hFc ω
  have hF'ne : ∀ ω, (F' ω).Nonempty := fun ω => by
    simp only [hF']; split_ifs with h
    · exact h
    · exact hne ω
  have hF'hit : ∀ U : Set ℂ, IsOpen U → MeasurableSet {ω | (F' ω ∩ U).Nonempty} := by
    intro U hU
    have : {ω | (F' ω ∩ U).Nonempty} =
        (A ∩ {ω | (frontier (K ω) ∩ closedBall q ρ ∩ U).Nonempty}) ∪
          (Aᶜ ∩ {ω | (frontier (K ω) ∩ U).Nonempty}) := by
      ext ω
      by_cases h : ω ∈ A <;> simp [hF', h]
    rw [this]
    exact (hAm.inter (p412f_hit_inter_closedBall _ hFc hhit q ρ hU)).union
      (hAm.compl.inter (hhit U hU))
  obtain ⟨x, hxm, hx⟩ := p412f_meas_select F' hF'c hF'ne hF'hit
  refine ⟨x, hxm, fun ω => ?_⟩
  have := hx ω
  by_cases h : ω ∈ A
  · simp only [hF', if_pos h] at this
    exact ⟨this.1, fun _ => this.2⟩
  · simp only [hF', if_neg h] at this
    exact ⟨this, fun h' => absurd h' h⟩

end LQGMetric.GM
