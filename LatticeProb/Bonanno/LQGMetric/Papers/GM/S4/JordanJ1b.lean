/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.JordanJ1b at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanLC

/-!
# Node J1b (local connectivity of `Γ = ∂𝓑^•_s`): the metric half of MS's argument

Miller–Sheffield arXiv:1506.03806, proof of Prop 2.1 (`mapmaking_final.tex` l. 570–601), with
Euclidean annuli in place of metric-ball annuli (decision D17, `decisions/DEC-B.md` (b), J1b).

MS argue by contradiction: if `Γ` is not locally connected at `x`, then (l. 582) "both `A ∩ U`
and `A ∩ Ũ` contain infinitely many distinct components crossing `A`" for an annulus `A`
centred at `x`; then (l. 585–601) a geodesic from a point `w` of the inner part of such a
component towards the centre `z` of the ball has to leave the component through a place which
is `D`-close to `Γ`, while it has already travelled a definite `D`-distance from `w`; since all
of `Γ` is at `D`-distance `s` from `z` (and the geodesic is in `𝓑_s`) this is impossible.

This file formalizes the metric half (l. 585–601) in the following robust form.

* `j1b_exit_path`: a near-geodesic path from `z` to a point `w` of an open annulus
  `{a < |y − x| < b}` not containing `z` has a last exit point `v` with `|v − x| ∈ {a, b}`;
  the final piece of the path joins `v` to `w` inside the closed annulus, and
  `D(z, v) + D(v, w) ≤ D(z, w) + η` (MS l. 597: "`d(x, w) = d(x, v) + d(v, w)`").
* `gm_j1b_finite` (MS l. 585–601): for `r₁ < ρ₁ ≤ ρ₂ < r₂` with `z ∉ A := {r₁ < |y − x| < r₂}`,
  only **finitely many** components of `A ∖ Γ` contain points `w ∈ 𝓑_s` with
  `ρ₁ ≤ |w − x| ≤ ρ₂`. Proof: the exit point `v` of a near-geodesic from `z` to `w` through the
  circles `|y − x| ∈ {a, b}` (`a ∈ (r₁, ρ₁)`, `b ∈ (ρ₂, r₂)`) lies in the component of `w` and
  has `D(z, v) ≤ s − δ`, `δ` = the `D`-distance between the middle and the two circles; the
  compact set `E` of such points of the circles misses `Γ`, so it is covered by finitely many
  (open) components of `A ∖ Γ`. (MS use short arcs of a middle loop `A_M` and the crossing
  point of two geodesics; we use the exit point directly, which avoids MS's unproved claim that
  the geodesic must cross a given short geodesic `η` — an own variant of l. 585–601.)
* `GMJ1bTop`: the purely topological claim of MS l. 582 (no metric), in the form used here.
* `gm_filledBallBdyLC_of_top`: `GMJ1bTop` implies J1b (`FilledBallBdyLC`) for every continuous
  length metric with bounded balls.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- The open Euclidean annulus `{r₁ < |y − x| < r₂}`. -/
def j1bAnn (x : ℂ) (r₁ r₂ : ℝ) : Set ℂ := {y | r₁ < ‖y - x‖ ∧ ‖y - x‖ < r₂}

theorem j1b_isOpen_ann (x : ℂ) (r₁ r₂ : ℝ) : IsOpen (j1bAnn x r₁ r₂) :=
  (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)

variable {D : ContMetric} {z : ℂ} {s : ℝ}

theorem j1b_edist_eq (D : ContMetric) (p q : D.Space) :
    edist p q = ENNReal.ofReal (D.1 (D.unpt p, D.unpt q)) := edist_dist p q

theorem j1b_nonneg (D : ContMetric) (p q : ℂ) : 0 ≤ D.1 (p, q) :=
  dist_nonneg (x := D.pt p) (y := D.pt q)

/-- **Exit point of a near-geodesic** (MS l. 597). -/
theorem j1b_exit_path (hL : D.IsLength) {x w : ℂ} {a b η : ℝ}
    (hw : a < ‖w - x‖ ∧ ‖w - x‖ < b) (hz : ¬ (a < ‖z - x‖ ∧ ‖z - x‖ < b)) (hη : 0 < η) :
    ∃ v : ℂ, ∃ P : Set ℂ, (‖v - x‖ = a ∨ ‖v - x‖ = b) ∧ IsPreconnected P ∧ v ∈ P ∧ w ∈ P ∧
      (∀ y ∈ P, a ≤ ‖y - x‖ ∧ ‖y - x‖ ≤ b) ∧ (∀ y ∈ P, D.1 (z, y) ≤ D.1 (z, w) + η) ∧
      D.1 (z, v) + D.1 (v, w) ≤ D.1 (z, w) + η := by
  obtain ⟨γ, hγ⟩ := hL (D.pt z) (D.pt w) η hη
  set g : ℝ → ℂ := fun t => D.unpt (γ.extend t) with hg
  have hgc : Continuous g := D.continuous_unpt.comp γ.continuous_extend
  have hg0 : g 0 = z := by simp only [hg, Path.extend_zero]; rfl
  have hg1 : g 1 = w := by simp only [hg, Path.extend_one]; rfl
  set f : ℝ → ℝ := fun t => ‖g t - x‖ with hf
  have hfc : Continuous f := (hgc.sub continuous_const).norm
  set T : Set ℝ := Icc 0 1 ∩ {t | a < f t ∧ f t < b}ᶜ with hT
  have hTc : IsClosed T := isClosed_Icc.inter
    ((isOpen_lt continuous_const hfc).inter (isOpen_lt hfc continuous_const)).isClosed_compl
  have h0T : (0 : ℝ) ∈ T := ⟨⟨le_rfl, zero_le_one⟩, by
    show ¬ (a < f 0 ∧ f 0 < b)
    simpa only [hf, hg0] using hz⟩
  have hTb : BddAbove T := ⟨1, fun t ht => ht.1.2⟩
  set t₀ := sSup T with ht₀
  have ht₀T : t₀ ∈ T := hTc.csSup_mem ⟨0, h0T⟩ hTb
  have ht₀1 : t₀ < 1 := lt_of_le_of_ne ht₀T.1.2 fun h => ht₀T.2 (by
    show a < f t₀ ∧ f t₀ < b
    rw [h]
    simpa only [hf, hg1] using hw)
  have hafter : ∀ t ∈ Ioc t₀ 1, a < f t ∧ f t < b := fun t ht => by
    by_contra h
    exact (not_le.2 ht.1) (le_csSup hTb ⟨⟨ht₀T.1.1.trans ht.1.le, ht.2⟩, h⟩)
  have hft₀ : a ≤ f t₀ ∧ f t₀ ≤ b := by
    have hcl : t₀ ∈ closure (Ioc t₀ 1) := by
      rw [closure_Ioc ht₀1.ne]
      exact ⟨le_rfl, ht₀1.le⟩
    have h1 := mem_closure_image hfc.continuousAt hcl
    have h2 : closure (f '' Ioc t₀ 1) ⊆ Icc a b :=
      closure_minimal (image_subset_iff.2 fun t ht => Ioo_subset_Icc_self (hafter t ht))
        isClosed_Icc
    exact h2 h1
  have hv : f t₀ = a ∨ f t₀ = b := by
    by_contra h
    push Not at h
    exact ht₀T.2 ⟨lt_of_le_of_ne hft₀.1 h.1.symm, lt_of_le_of_ne hft₀.2 h.2⟩
  -- distances along the path
  have hlen : MetricGeometry.curveLength γ.extend 0 1 ≤
      ENNReal.ofReal (D.1 (z, w)) + ENNReal.ofReal η := by
    rw [j1b_edist_eq] at hγ; exact hγ
  have hDt : ∀ t ∈ Icc (0 : ℝ) 1, D.1 (z, g t) ≤ D.1 (z, w) + η := fun t ht => by
    have h1 : edist (γ.extend 0) (γ.extend t) ≤ MetricGeometry.curveLength γ.extend 0 1 :=
      (MetricGeometry.edist_le_curveLength γ.extend ht.1).trans
        (MetricGeometry.curveLength_mono _ le_rfl ht.2)
    have h2 := h1.trans hlen
    rw [j1b_edist_eq, ← ENNReal.ofReal_add (j1b_nonneg D z w) hη.le,
      ENNReal.ofReal_le_ofReal_iff (add_nonneg (j1b_nonneg D z w) hη.le)] at h2
    rw [Path.extend_zero] at h2; exact h2
  refine ⟨g t₀, g '' Icc t₀ 1, hv, isPreconnected_Icc.image g hgc.continuousOn,
    mem_image_of_mem g ⟨le_rfl, ht₀1.le⟩, hg1 ▸ mem_image_of_mem g ⟨ht₀1.le, le_rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    rcases ht.1.lt_or_eq with h | h
    · exact ⟨(hafter t ⟨h, ht.2⟩).1.le, (hafter t ⟨h, ht.2⟩).2.le⟩
    · rw [← h]; exact hft₀
  · rintro _ ⟨t, ht, rfl⟩
    exact hDt t ⟨ht₀T.1.1.trans ht.1, ht.2⟩
  · have h1 : edist (γ.extend 0) (γ.extend t₀) + edist (γ.extend t₀) (γ.extend 1) ≤
        MetricGeometry.curveLength γ.extend 0 1 := by
      rw [← MetricGeometry.curveLength_add γ.extend ht₀T.1.1 ht₀1.le]
      exact add_le_add (MetricGeometry.edist_le_curveLength γ.extend ht₀T.1.1)
        (MetricGeometry.edist_le_curveLength γ.extend ht₀1.le)
    have h2 := h1.trans hlen
    rw [j1b_edist_eq, j1b_edist_eq, ← ENNReal.ofReal_add (j1b_nonneg D _ _) (j1b_nonneg D _ _),
      ← ENNReal.ofReal_add (j1b_nonneg D z w) hη.le,
      ENNReal.ofReal_le_ofReal_iff (add_nonneg (j1b_nonneg D z w) hη.le)] at h2
    rw [Path.extend_zero, Path.extend_one] at h2; exact h2

/-- **MS l. 585–601 (metric half of J1b).** For `r₁ < ρ₁ ≤ ρ₂ < r₂` and `z` outside the annulus
`A = {r₁ < |y − x| < r₂}`, only finitely many components of `A ∖ Γ` contain a point `w ∈ 𝓑_s`
with `ρ₁ ≤ |w − x| ≤ ρ₂`. -/
theorem gm_j1b_finite (hL : D.IsLength) (hbd : Bornology.IsBounded (ballM D z s)) {x : ℂ}
    {r₁ ρ₁ ρ₂ r₂ : ℝ} (h12 : r₁ < ρ₁) (h23 : ρ₁ ≤ ρ₂) (h34 : ρ₂ < r₂)
    (hz : z ∉ j1bAnn x r₁ r₂) :
    {W | ∃ w ∈ ballM D z s, ρ₁ ≤ ‖w - x‖ ∧ ‖w - x‖ ≤ ρ₂ ∧
      W = connectedComponentIn (j1bAnn x r₁ r₂ \ frontier (filledBall D z s)) w}.Finite := by
  set Γ := frontier (filledBall D z s) with hΓ
  set O := j1bAnn x r₁ r₂ \ Γ with hO
  have hOo : IsOpen O := (j1b_isOpen_ann x r₁ r₂).sdiff isClosed_frontier
  set a := (r₁ + ρ₁) / 2 with ha
  set b := (ρ₂ + r₂) / 2 with hb
  have hn : Continuous fun y : ℂ => ‖y - x‖ := (continuous_id.sub continuous_const).norm
  set M : Set ℂ := {y | ρ₁ ≤ ‖y - x‖ ∧ ‖y - x‖ ≤ ρ₂} with hM
  set S : Set ℂ := {y | ‖y - x‖ = a ∨ ‖y - x‖ = b} with hS
  have hMc : IsCompact M := by
    refine Metric.isCompact_of_isClosed_isBounded
      ((isClosed_le continuous_const hn).inter (isClosed_le hn continuous_const))
      (isBounded_closedBall (x := x) (r := ρ₂) |>.subset fun y hy => ?_)
    rw [mem_closedBall, dist_eq_norm]; exact hy.2
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded
      ((isClosed_eq hn continuous_const).union (isClosed_eq hn continuous_const))
      (isBounded_closedBall (x := x) (r := |a| + |b|) |>.subset fun y hy => ?_)
    rw [mem_closedBall, dist_eq_norm]
    rcases hy with h | h <;> rw [h]
    · linarith [le_abs_self a, abs_nonneg b]
    · linarith [le_abs_self b, abs_nonneg a]
  -- `δ` = the `D`-distance between `M` and the two circles
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ > 0, ∀ m ∈ M, ∀ v ∈ S, δ ≤ D.1 (m, v) := by
    rcases (M ×ˢ S).eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun m hm v hv => ?_⟩
      have := he ▸ mk_mem_prod hm hv
      exact absurd this (notMem_empty _)
    obtain ⟨p, hp, hpmin⟩ := (hMc.prod hSc).exists_isMinOn hne D.1.continuous.continuousOn
    refine ⟨D.1 p, ?_, fun m hm v hv => hpmin (mk_mem_prod hm hv)⟩
    have hne' : p.1 ≠ p.2 := fun h => by
      have h1 : ρ₁ ≤ ‖p.2 - x‖ ∧ ‖p.2 - x‖ ≤ ρ₂ := h ▸ hp.1
      rcases hp.2 with h2 | h2 <;> rw [h2] at h1 <;> linarith [h1.1, h1.2]
    exact dist_pos.2 (show D.pt p.1 ≠ D.pt p.2 from hne')
  set E : Set ℂ := S ∩ {v | D.1 (z, v) ≤ s - δ / 2} with hE
  have hEc : IsCompact E := hSc.inter_right
    (isClosed_le (D.1.continuous.comp (continuous_const.prodMk continuous_id)) continuous_const)
  have hEO : E ⊆ O := fun v hv => by
    refine ⟨?_, fun hvΓ => ?_⟩
    · rcases hv.1 with h | h <;> refine ⟨?_, ?_⟩ <;> rw [h] <;> linarith
    · have h1 : D.1 (z, v) = s := jp_frontier_subset_sphere hbd hvΓ
      have h2 : D.1 (z, v) ≤ s - δ / 2 := hv.2
      linarith
  obtain ⟨t, htE, hcov⟩ := hEc.elim_nhds_subcover (fun e => connectedComponentIn O e)
    fun e he => hOo.connectedComponentIn.mem_nhds (mem_connectedComponentIn (hEO he))
  refine ((t.finite_toSet).image fun e => connectedComponentIn O e).subset ?_
  rintro W ⟨w, hwV, hw1, hw2, rfl⟩
  have hwV' : D.1 (z, w) < s := hwV
  set η := min (δ / 2) ((s - D.1 (z, w)) / 2) with hη
  have hηpos : 0 < η := lt_min (by linarith) (by linarith)
  have hwab : a < ‖w - x‖ ∧ ‖w - x‖ < b := ⟨by linarith, by linarith⟩
  have hzab : ¬ (a < ‖z - x‖ ∧ ‖z - x‖ < b) := fun h => hz ⟨by linarith [h.1], by linarith [h.2]⟩
  obtain ⟨v, P, hvS, hP, hvP, hwP, hPab, hPD, hvD⟩ := j1b_exit_path hL hwab hzab hηpos
  have hη1 : η ≤ δ / 2 := min_le_left _ _
  have hη2 : η ≤ (s - D.1 (z, w)) / 2 := min_le_right _ _
  have hPO : P ⊆ O := fun y hy => by
    refine ⟨⟨by linarith [(hPab y hy).1], by linarith [(hPab y hy).2]⟩, fun hyΓ => ?_⟩
    have hyV : y ∈ ballM D z s := show D.1 (z, y) < s by linarith [hPD y hy]
    exact disjoint_left.1 jb_disjoint_ballM_frontier hyV hyΓ
  have hPsub : P ⊆ connectedComponentIn O w := hP.subset_connectedComponentIn hwP hPO
  have hδvw : δ ≤ D.1 (v, w) := by
    rw [D.2.symm]; exact hδle w ⟨hw1, hw2⟩ v hvS
  have hvE : v ∈ E := ⟨hvS, show D.1 (z, v) ≤ s - δ / 2 by linarith⟩
  obtain ⟨e, he, hve⟩ := mem_iUnion₂.1 (hcov hvE)
  refine ⟨e, he, ?_⟩
  show connectedComponentIn O e = connectedComponentIn O w
  rw [connectedComponentIn_eq (hPsub hvP), connectedComponentIn_eq hve]

/-- **The topological half of J1b** (MS l. 572–582, "it is not hard to see that both `A ∩ U` and
`A ∩ Ũ` contain infinitely many distinct components crossing `A`"), in the form needed by
`gm_j1b_finite`: if a compact connected set `Γ ⊆ cl V` (`V` disjoint from `Γ`) is not locally
connected at `x ∈ Γ` (Newman form, as in `FilledBallBdyLC`), then inside every ball `B(x, R)`
there is an annulus `A = {r₁ < |y − x| < r₂}` such that infinitely many components of `A ∖ Γ`
contain points of `V` in the middle region `{ρ₁ ≤ |y − x| ≤ ρ₂}`. Pure plane topology: no
metric. Proved from the sector lemma in `JordanJ1bTop.lean` (`gm_j1bTop_of_sector`). -/
def GMJ1bTop : Prop :=
  ∀ (Γ V : Set ℂ) (x : ℂ) (ε R : ℝ), IsCompact Γ → IsPreconnected Γ → Disjoint V Γ →
    Γ ⊆ closure V → x ∈ Γ → 0 < ε → 0 < R →
    (∀ ρ > 0, ∃ a ∈ Γ, dist a x < ρ ∧
      ¬ ∃ β ⊆ Γ, IsPreconnected β ∧ x ∈ β ∧ a ∈ β ∧ Metric.diam β ≤ ε) →
    ∃ r₁ ρ₁ ρ₂ r₂ : ℝ, 0 < r₁ ∧ r₁ < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < r₂ ∧ r₂ ≤ R ∧
      {W | ∃ w ∈ V, ρ₁ ≤ ‖w - x‖ ∧ ‖w - x‖ ≤ ρ₂ ∧
        W = connectedComponentIn (j1bAnn x r₁ r₂ \ Γ) w}.Infinite

/-- Node J1b as a proposition (handoff/P2-M2I.md). -/
def GMJ1b : Prop :=
  ∀ (D : ContMetric) (z : ℂ) (s : ℝ), 0 < s → D.IsLength → Bornology.IsBounded (ballM D z s) →
    FilledBallBdyLC D z s

/-- **J1b from its topological half** (MS Prop 2.1 proof, l. 570–601). -/
theorem gm_filledBallBdyLC_of_top (htop : GMJ1bTop) (hs : 0 < s) (hL : D.IsLength)
    (hbd : Bornology.IsBounded (ballM D z s)) : FilledBallBdyLC D z s := by
  set Γ := frontier (filledBall D z s) with hΓ
  set V := ballM D z s with hV
  set K := filledBall D z s with hK
  have hKc : IsClosed K := jb_isClosed_filledBall hbd
  have hΓK : Γ ⊆ K := hKc.frontier_subset
  have hΓc : IsCompact Γ :=
    (jb_isCompact_filledBall hbd).of_isClosed_subset isClosed_frontier hΓK
  have hzΓ : z ∉ Γ := jo_not_mem_frontier_self hs
  have hΓp : IsPreconnected Γ := by
    have := jb_isPreconnected_frontier_diff hs hL hbd z
    rwa [sdiff_singleton_eq_self hzΓ] at this
  have hVΓ : Disjoint V Γ := jb_disjoint_ballM_frontier
  intro x hx ε hε
  by_contra hneg
  have hbad : ∀ ρ > 0, ∃ a ∈ Γ, dist a x < ρ ∧
      ¬ ∃ β ⊆ Γ, IsPreconnected β ∧ x ∈ β ∧ a ∈ β ∧ Metric.diam β ≤ ε := fun ρ hρ => by
    by_contra h'
    exact hneg ⟨ρ, hρ, fun a ha hax => by
      by_contra hb
      exact h' ⟨a, ha, hax, hb⟩⟩
  have hxz : 0 < ‖z - x‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hzΓ (h ▸ hx))
  obtain ⟨r₁, ρ₁, ρ₂, r₂, -, h12, h23, h34, h4R, hinf⟩ :=
    htop Γ V x ε ‖z - x‖ hΓc hΓp hVΓ (jb_frontier_subset_closure hbd) hx hε hxz hbad
  exact hinf (gm_j1b_finite hL hbd h12 h23 h34 fun h => (not_lt.2 h4R) h.2)

end LQGMetric.GM
