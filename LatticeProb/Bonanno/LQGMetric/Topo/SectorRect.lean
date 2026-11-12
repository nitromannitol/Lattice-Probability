/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Topo.SectorRect at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Topo.RectMeet
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Complex.ReImTopology

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Sector lemma, rectangle part: three disjoint left–right crossing continua are linearly ordered

Node GMSector (handoff P2-J1B / P2-GMSEC). In a closed rectangle `R = [x₀, x₁] × [y₀, y₁]`:

* `lr_tb_meet`: a continuum meeting the left and right sides meets every continuum meeting the
  top and bottom sides. From the path version `RectMeet.rect_crossings_meet` (Maehara's lemma /
  2-d Poincaré–Miranda) by approximating each continuum by a path in its `δ`-thickening (open
  connected sets of `ℂ` are path-connected) and clamping the path back into `R`.
* the sides `cc (R \ L) τ`, `cc (R \ L) β` (components of the top-left and bottom-left corners)
  of a crossing continuum `L` avoiding the top and bottom sides are distinct
  (`top_not_mem_cc_bot`), every crossing continuum disjoint from `L` lies in one of them
  (`crosser_dichotomy`), and two disjoint crossers cannot lie on the same side of each other
  (`not_both_side`).
* `three_crossers_rect`: hence of three pairwise disjoint crossers one separates the other two in
  `R`: there are no connected sets `Nᵢ ⊆ R \ Lᵢ` containing the other two crossers.

This is the classical separation/ordering of crossing continua (Newman, *Elements of the topology
of plane sets of points*, Ch. V; not available here). Own write-up from the rectangle crossing
lemma, recorded in `DEVIATIONS.md` (proposed).
-/

namespace LQGMetric

namespace Sector

open Set Metric RectCross

variable {x₀ x₁ y₀ y₁ : ℝ}

theorem convex_rect : Convex ℝ (rect x₀ x₁ y₀ y₁) :=
  ((convex_Icc x₀ x₁).linear_preimage Complex.reLm).inter
    ((convex_Icc y₀ y₁).linear_preimage Complex.imLm)

theorem rect_eq : rect x₀ x₁ y₀ y₁ = Icc x₀ x₁ ×ℂ Icc y₀ y₁ := by
  ext z; simp [rect, Complex.mem_reProdIm]

theorem isCompact_rect : IsCompact (rect x₀ x₁ y₀ y₁) := by
  rw [rect_eq]; exact isCompact_Icc.reProdIm isCompact_Icc

theorem isClosed_rect : IsClosed (rect x₀ x₁ y₀ y₁) := isCompact_rect.isClosed

/-- Coordinatewise projection onto the rectangle. -/
noncomputable def clampR (x₀ x₁ y₀ y₁ : ℝ) (z : ℂ) : ℂ :=
  ⟨max x₀ (min x₁ z.re), max y₀ (min y₁ z.im)⟩

theorem continuous_clampR : Continuous (clampR x₀ x₁ y₀ y₁) := by
  have h1 : Continuous fun z : ℂ => max x₀ (min x₁ z.re) := by fun_prop
  have h2 : Continuous fun z : ℂ => max y₀ (min y₁ z.im) := by fun_prop
  have : clampR x₀ x₁ y₀ y₁ = fun z => Complex.equivRealProdCLM.symm
      (max x₀ (min x₁ z.re), max y₀ (min y₁ z.im)) := by
    funext z; rfl
  rw [this]; fun_prop

theorem clampR_mem (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) (z : ℂ) :
    clampR x₀ x₁ y₀ y₁ z ∈ rect x₀ x₁ y₀ y₁ :=
  ⟨⟨le_max_left _ _, max_le hx (min_le_left _ _)⟩, ⟨le_max_left _ _, max_le hy (min_le_left _ _)⟩⟩

theorem clampR_of_mem {z : ℂ} (hz : z ∈ rect x₀ x₁ y₀ y₁) : clampR x₀ x₁ y₀ y₁ z = z := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
  apply Complex.ext
  · show max x₀ (min x₁ z.re) = z.re
    rw [min_eq_right h2, max_eq_right h1]
  · show max y₀ (min y₁ z.im) = z.im
    rw [min_eq_right h4, max_eq_right h3]

theorem clamp1_sq {a b c d : ℝ} (hab : a ≤ b) (hc0 : a ≤ c) (hc1 : c ≤ b) :
    (max a (min b d) - c) ^ 2 ≤ (d - c) ^ 2 := by
  rcases le_total d a with h | h
  · rw [min_eq_right (h.trans hab), max_eq_left h]; nlinarith
  · rcases le_total d b with h' | h'
    · rw [min_eq_right h', max_eq_right h]
    · rw [min_eq_left h', max_eq_right hab]; nlinarith

theorem dist_clampR_le (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) (z : ℂ) {l : ℂ}
    (hl : l ∈ rect x₀ x₁ y₀ y₁) : dist (clampR x₀ x₁ y₀ y₁ z) l ≤ dist z l := by
  rw [dist_eq_norm, dist_eq_norm]
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  have e1 := clamp1_sq (d := z.re) hx hl.1.1 hl.1.2
  have e2 := clamp1_sq (d := z.im) hy hl.2.1 hl.2.2
  simp only [Complex.sub_re, Complex.sub_im]
  change (max x₀ (min x₁ z.re) - l.re) * (max x₀ (min x₁ z.re) - l.re) +
      (max y₀ (min y₁ z.im) - l.im) * (max y₀ (min y₁ z.im) - l.im) ≤ _
  nlinarith

/-- A union of balls centred on a preconnected set is preconnected. -/
theorem isPreconnected_biUnion_ball {C : Set ℂ} (hC : IsPreconnected C) (ε : ℂ → ℝ)
    (hε : ∀ q ∈ C, 0 < ε q) : IsPreconnected (⋃ q ∈ C, ball q (ε q)) := by
  rcases C.eq_empty_or_nonempty with h | ⟨c, hc⟩
  · subst h; simpa using isPreconnected_empty
  refine isPreconnected_of_forall c fun y hy => ?_
  obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.1 hy
  refine ⟨C ∪ ball q (ε q), union_subset (fun z hz => mem_iUnion₂.2 ⟨z, hz, mem_ball_self (hε z hz)⟩)
    (subset_iUnion₂ (s := fun q _ => ball q (ε q)) q hq), Or.inl hc, Or.inr hyq, ?_⟩
  exact IsPreconnected.union q hq (mem_ball_self (hε q hq)) hC (convex_ball q (ε q)).isPreconnected

/-- A path inside an open connected set of `ℂ` between two points of the rectangle, clamped into
the rectangle. -/
theorem exists_clamp_path {O : Set ℂ} (hO : IsOpen O)
    (hc : IsPreconnected O) {a b : ℂ} (ha : a ∈ O) (hb : b ∈ O) (haR : a ∈ rect x₀ x₁ y₀ y₁)
    (hbR : b ∈ rect x₀ x₁ y₀ y₁) :
    ∃ γ : ℝ → ℂ, Continuous γ ∧ γ 0 = a ∧ γ 1 = b ∧
      ∀ t, ∃ z ∈ O, γ t = clampR x₀ x₁ y₀ y₁ z := by
  have hpc : IsPathConnected O := hO.isConnected_iff_isPathConnected.1 ⟨⟨a, ha⟩, hc⟩
  have hj := hpc.joinedIn a ha b hb
  set p := hj.somePath
  refine ⟨fun t => clampR x₀ x₁ y₀ y₁ (p.extend t),
    continuous_clampR.comp p.continuous_extend, ?_, ?_, fun t => ⟨p.extend t, ?_, rfl⟩⟩
  · simp only [Path.extend_zero]; exact clampR_of_mem haR
  · simp only [Path.extend_one]; exact clampR_of_mem hbR
  · exact hj.somePath_mem _

/-- **Continuum crossing lemma.** A continuum in the rectangle meeting its left and right sides
meets every continuum in the rectangle meeting its top and bottom sides. -/
theorem lr_tb_meet (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) {L M : Set ℂ} (hL : IsCompact L)
    (hLc : IsPreconnected L) (hLR : L ⊆ rect x₀ x₁ y₀ y₁) (hL0 : ∃ p ∈ L, p.re = x₀)
    (hL1 : ∃ p ∈ L, p.re = x₁) (hM : IsCompact M) (hMc : IsPreconnected M)
    (hMR : M ⊆ rect x₀ x₁ y₀ y₁) (hM1 : ∃ p ∈ M, p.im = y₁) (hM0 : ∃ p ∈ M, p.im = y₀) :
    (L ∩ M).Nonempty := by
  by_contra hne
  have hdis : Disjoint L M := disjoint_iff_inter_eq_empty.2 (not_nonempty_iff_eq_empty.1 hne)
  obtain ⟨δ, hδ, hdδ⟩ := hdis.exists_thickenings hL hM.isClosed
  have hconn : ∀ {E : Set ℂ}, IsPreconnected E → IsPreconnected (thickening δ E) := fun hE => by
    rw [thickening_eq_biUnion_ball]; exact isPreconnected_biUnion_ball hE _ fun _ _ => hδ
  have hcl : ∀ {E : Set ℂ}, E ⊆ rect x₀ x₁ y₀ y₁ → ∀ z ∈ thickening δ E,
      clampR x₀ x₁ y₀ y₁ z ∈ thickening δ E := fun hE z hz => by
    obtain ⟨l, hl, hzl⟩ := mem_thickening_iff.1 hz
    exact mem_thickening_iff.2 ⟨l, hl, (dist_clampR_le hx hy z (hE hl)).trans_lt hzl⟩
  obtain ⟨a, haL, ha⟩ := hL0
  obtain ⟨b, hbL, hb⟩ := hL1
  obtain ⟨c, hcM, hc⟩ := hM1
  obtain ⟨d, hdM, hd⟩ := hM0
  obtain ⟨γ, hγc, hγ0, hγ1, hγ⟩ := exists_clamp_path isOpen_thickening (hconn hLc)
    (self_subset_thickening hδ L haL) (self_subset_thickening hδ L hbL) (hLR haL) (hLR hbL)
  obtain ⟨η, hηc, hη0, hη1, hη⟩ := exists_clamp_path isOpen_thickening (hconn hMc)
    (self_subset_thickening hδ M hcM) (self_subset_thickening hδ M hdM) (hMR hcM) (hMR hdM)
  obtain ⟨s, -, t, -, hst⟩ := RectMeet.rect_crossings_meet x₀ x₁ y₀ y₁ γ η hγc.continuousOn
    hηc.continuousOn
    (fun t _ => by obtain ⟨z, -, hz⟩ := hγ t; rw [hz]; exact clampR_mem hx hy z)
    (fun t _ => by obtain ⟨z, -, hz⟩ := hη t; rw [hz]; exact clampR_mem hx hy z)
    (by rw [hγ0, ha]) (by rw [hγ1, hb]) (by rw [hη0, hc]) (by rw [hη1, hd])
  obtain ⟨z, hz, hz'⟩ := hγ s
  obtain ⟨w, hw, hw'⟩ := hη t
  have h1 : γ s ∈ thickening δ L := hz' ▸ hcl hLR z hz
  have h2 : γ s ∈ thickening δ M := hst ▸ hw' ▸ hcl hMR w hw
  exact hdδ.le_bot ⟨h1, h2⟩

end Sector

end LQGMetric
