/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K5d at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J3d

/-!
# CONF Theorem 3.9, packet J6d: membership in the canonical arcs is jointly measurable

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1514, 1740–1744 (arcs of `∂𝓑^•_τ` "chosen in a manner depending only on `𝓑^•_τ`"); DV-D120-1.

The arcs `I^{(s)} = t39gArc … s I` (C:1543) depend on the arcs `I = t39jArcs m i Γ` of
`Γ = ∂𝓑^•_τ` through the membership `P(τ) ∈ I` of points of geodesics, which is not determined by
the hit events of `I` (`T39JArcChoice.meas`) when `I` is not closed. **`t39k5_arcs_mem_meas`**:
`{(Γ, y) | y ∈ t39jArcs m i Γ}` is measurable for `effrosSigma ⊗ Borel` (same countable
descriptions as `t39j_rc_meas`, `t39j_arcs_meas` of S3T39J2b–J3c, with the point `y` as a second
coordinate). Own elementary argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace LQGMetric.CONF

attribute [local instance 2000] effrosSigma

theorem t39k5_fst_meas {A : Set (Set ℂ)} (hA : MeasurableSet A) :
    MeasurableSet {p : Set ℂ × ℂ | p.1 ∈ A} := measurable_fst hA

/-- the rational chain relation `RC(x Γ, y)` is jointly measurable -/
theorem t39k5_rc_mem_meas (L : ℕ) {x : Set ℂ → ℂ} (hx : Measurable x) :
    MeasurableSet {p : Set ℂ × ℂ | t39jRC L p.1 (x p.1) p.2} := by
  have heq : {p : Set ℂ × ℂ | t39jRC L p.1 (x p.1) p.2} = ⋃ η : ℚ, ⋃ (_ : 0 < η),
      ⋂ ε : ℚ, ⋂ (_ : 0 < ε), ⋃ δ : ℚ, ⋃ (_ : 0 < δ), ⋃ v : ℚ × ℚ, ⋃ v' : ℚ × ℚ, ⋃ n : ℕ,
        ({p : Set ℂ × ℂ | t39jGood L η δ p.1 (t39jRq v) ∧ t39jGood L η δ p.1 (t39jRq v') ∧
          dist (x p.1) (t39jRq v) + δ < ε ∧ t39jReach L η ε δ p.1 n (t39jRq v) (t39jRq v')} ∩
          {p | dist (t39jRq v') p.2 + δ < ε}) := by
    ext p
    simp only [t39jRC, mem_ofPred_eq, mem_iUnion, mem_iInter, mem_inter_iff, exists_prop]
    refine exists_congr fun η => and_congr_right fun _ => forall₂_congr fun ε _ =>
      exists_congr fun δ => and_congr_right fun _ => ?_
    constructor
    · rintro ⟨w, w', n, hg, hg', h1, h2, hr⟩
      obtain ⟨v, rfl⟩ := hg.1
      obtain ⟨v', rfl⟩ := hg'.1
      exact ⟨v, v', n, ⟨hg, hg', h1, hr⟩, h2⟩
    · rintro ⟨v, v', n, ⟨hg, hg', h1, hr⟩, h2⟩
      exact ⟨_, _, n, hg, hg', h1, h2, hr⟩
  rw [heq]
  refine MeasurableSet.iUnion fun η => MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun ε =>
    MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun δ => MeasurableSet.iUnion fun _ =>
      MeasurableSet.iUnion fun v => MeasurableSet.iUnion fun v' => MeasurableSet.iUnion fun n =>
        MeasurableSet.inter ?_ ?_
  · refine t39k5_fst_meas (A := {Γ | t39jGood L η δ Γ (t39jRq v) ∧ t39jGood L η δ Γ (t39jRq v') ∧
      dist (x Γ) (t39jRq v) + δ < ε ∧ t39jReach L η ε δ Γ n (t39jRq v) (t39jRq v')}) ?_
    exact (t39j_good_meas L η δ v).inter ((t39j_good_meas L η δ v').inter
      ((measurableSet_lt ((hx.dist measurable_const).add_const _) measurable_const).inter
        (t39j_reach_meas L η ε δ n v v')))
  · exact measurableSet_lt ((measurable_const.dist measurable_snd).add_const _) measurable_const

/-- `y ∈ closure Γ` is jointly measurable -/
theorem t39k5_closure_mem_meas : MeasurableSet {p : Set ℂ × ℂ | p.2 ∈ closure p.1} := by
  have heq : {p : Set ℂ × ℂ | p.2 ∈ closure p.1} = ⋂ n : ℕ, ⋃ v : ℚ × ℚ,
      ({p : Set ℂ × ℂ | (p.1 ∩ ball (t39jRq v) (1 / ((n : ℝ) + 1))).Nonempty} ∩
        {p | dist p.2 (t39jRq v) < 1 / ((n : ℝ) + 1)}) := by
    ext ⟨Γ, y⟩
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_inter_iff]
    constructor
    · intro hy n
      have hr : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨z, hzΓ, hz⟩ := Metric.mem_closure_iff.1 hy _ (half_pos hr)
      obtain ⟨_, ⟨v, rfl⟩, hv⟩ := t39j_rq_near z (half_pos hr)
      refine ⟨v, ⟨z, hzΓ, ?_⟩, ?_⟩
      · rw [mem_ball]; linarith
      · linarith [dist_triangle y z (t39jRq v)]
    · intro H
      refine Metric.mem_closure_iff.2 fun ε hε => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
      obtain ⟨v, ⟨z, hzΓ, hz⟩, hyv⟩ := H n
      rw [mem_ball] at hz
      exact ⟨z, hzΓ, by linarith [dist_triangle y (t39jRq v) z, dist_comm z (t39jRq v)]⟩
  rw [heq]
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun v => MeasurableSet.inter ?_ ?_
  · exact t39k5_fst_meas (A := {Γ | (Γ ∩ ball (t39jRq v) (1 / ((n : ℝ) + 1))).Nonempty})
      (t39j_hit_open isOpen_ball)
  · exact measurableSet_lt (measurable_snd.dist measurable_const) measurable_const

/-- `y ∉ P_L(Γ)` (the cut points) is jointly measurable -/
theorem t39k5_notCut_meas (L : ℕ) : MeasurableSet {p : Set ℂ × ℂ | p.2 ∉ t39jCut L p.1} := by
  have heq : {p : Set ℂ × ℂ | p.2 ∉ t39jCut L p.1} = ⋂ j ∈ Finset.range L,
      ({p : Set ℂ × ℂ | t39jValid j p.1}ᶜ ∪ {p | p.2 ≠ t39jPt j p.1}) := by
    ext p
    simp only [t39jCut, mem_ofPred_eq, mem_iInter, Finset.mem_range, mem_union, mem_compl_iff]
    constructor
    · intro h j hj
      by_cases hv : t39jValid j p.1
      · exact Or.inr fun he => h ⟨j, hj, hv, he⟩
      · exact Or.inl hv
    · rintro h ⟨j, hj, hv, he⟩
      exact ((h j hj).resolve_left (not_not.2 hv)) he
  rw [heq]
  refine Finset.measurableSet_biInter _ fun j _ =>
    (t39k5_fst_meas (t39jValid_meas j)).compl.union ?_
  exact (measurableSet_eq_fun measurable_snd ((t39jPt_meas j).comp measurable_fst)).compl

/-- membership in a chain class is jointly measurable -/
theorem t39k5_class_mem_meas (L i : ℕ) :
    MeasurableSet {p : Set ℂ × ℂ | p.2 ∈ t39jClass L p.1 (t39jPt i p.1)} :=
  t39k5_closure_mem_meas.inter ((t39k5_notCut_meas L).inter (t39k5_rc_mem_meas L (t39jPt_meas i)))

theorem t39k5_arcL_mem_meas (L i : ℕ) :
    MeasurableSet {p : Set ℂ × ℂ | p.2 ∈ t39jArcL L i p.1} := by
  classical
  set S1 := {Γ : Set ℂ | i < L ∧ t39jValid i Γ ∧ t39jFirst i Γ}
  have hS1 : MeasurableSet S1 :=
    (MeasurableSet.const (i < L)).inter ((t39jValid_meas i).inter (t39j_first_meas i))
  have heq : {p : Set ℂ × ℂ | p.2 ∈ t39jArcL L i p.1} =
      ({p : Set ℂ × ℂ | p.1 ∈ S1} ∩ {p | p.2 = t39jPt i p.1}) ∪
      ({p : Set ℂ × ℂ | p.1 ∈ S1ᶜ ∩ {Γ | t39jNew L i Γ}} ∩
        {p | p.2 ∈ t39jClass L p.1 (t39jPt i p.1)}) := by
    ext ⟨Γ, y⟩
    by_cases h1 : Γ ∈ S1
    · have h1' : i < L ∧ t39jValid i Γ ∧ t39jFirst i Γ := h1
      simp [t39jArcL, h1', h1]
    · have h1' : ¬ (i < L ∧ t39jValid i Γ ∧ t39jFirst i Γ) := h1
      by_cases h2 : t39jNew L i Γ
      · simp [t39jArcL, h1', h1, h2]
      · simp [t39jArcL, h1', h1, h2]
  rw [heq]
  exact ((t39k5_fst_meas hS1).inter (measurableSet_eq_fun measurable_snd
    ((t39jPt_meas i).comp measurable_fst))).union
    ((t39k5_fst_meas (hS1.compl.inter (t39j_new_meas L i))).inter (t39k5_class_mem_meas L i))

/-- **membership in the canonical arcs `t39jArcs m i Γ` is `effrosSigma ⊗ Borel`-measurable** -/
theorem t39k5_arcs_mem_meas (m : ℕ) (i : Fin m) :
    MeasurableSet {p : Set ℂ × ℂ | p.2 ∈ t39jArcs m i p.1} := by
  have heq : {p : Set ℂ × ℂ | p.2 ∈ t39jArcs m i p.1} = ⋃ L ∈ Finset.range (m + 1),
      ({p : Set ℂ × ℂ | p.1 ∈ t39jLev m ⁻¹' {L}} ∩ {p | p.2 ∈ t39jArcL L i p.1}) := by
    ext ⟨Γ, y⟩
    simp only [t39jArcs, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage,
      mem_singleton_iff, Finset.mem_range, exists_prop]
    constructor
    · intro h; exact ⟨_, Nat.lt_succ_of_le (t39j_lev_le m Γ), rfl, h⟩
    · rintro ⟨L, -, hL, h⟩; rw [hL]; exact h
  rw [heq]
  exact Finset.measurableSet_biUnion _ fun L _ =>
    (t39k5_fst_meas ((t39j_lev_meas m) (measurableSet_singleton L))).inter (t39k5_arcL_mem_meas L i)

end LQGMetric.CONF
