/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Topo.CrosscutMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Topo.CrosscutSep

/-!
# Crosscuts by circle arcs, part III: exactly one bounded and one unbounded component

GM (arXiv:1905.00383), proof of Lemma 4.14 (`lem-dc-set`), tex l. 2478–2479: for `B` a closed
Euclidean ball, "the set `∂B ∖ K` is a countable union of open arcs of `∂B`. Each such arc divides
`ℂ ∖ K` into a bounded connected component and an unbounded connected component."

`crosscut_circle`: `K` compact connected with `ℂ ∖ K` connected, `Y` a component of
`sphere c r ∖ K`. Then `(Y ∪ K)ᶜ` is the union of exactly two components, one bounded and one
unbounded, and `Y` lies in the closure of both.

Source: Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §2.4, Prop. 2.12 (a crosscut
of a simply connected domain splits it into exactly two domains), applied to the domain
`Ĉ ∖ K`. We do not follow Pommerenke's proof (Riemann map plus Jordan curve theorem); the route
here is own and elementary: (a) at most two components, since every component of `(Y ∪ K)ᶜ`
touches `Y` (`ℂ ∖ K` connected) and near `Y` there are only the inner and the outer radial collar
(`CrosscutRadial`); (b) the two collars are separated (`CrosscutSep.cc_sep`, Eilenberg's criterion
as in Burckel Ex. 4.37). No Jordan hypothesis on `∂K` is needed. Recorded in `DEVIATIONS.md`
(proposed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter Complex Bornology

namespace LQGMetric.Topo.Crosscut

/-- Abstract finish: two components `p, q` covering `F`, the one at `p` containing an unbounded
preconnected `E ⊆ F` whose complement is bounded. -/
theorem finish_aux {F E : Set ℂ} {p q e c : ℂ} {R : ℝ} (hpq : q ∉ connectedComponentIn F p)
    (hE : IsPreconnected E) (hEF : E ⊆ F) (he : e ∈ E) (hep : e ∈ connectedComponentIn F p)
    (hEc : ∀ z, z ∉ E → ‖z - c‖ ≤ R) (hEu : ¬ IsBounded E) :
    IsBounded (connectedComponentIn F q) ∧ ¬ IsBounded (connectedComponentIn F p) := by
  have hEp : E ⊆ connectedComponentIn F p := by
    rw [connectedComponentIn_eq hep]; exact hE.subset_connectedComponentIn he hEF
  refine ⟨(isBounded_closedBall (x := c) (r := R)).subset fun z hz => ?_,
    fun h => hEu (h.subset hEp)⟩
  rw [mem_closedBall, dist_eq_norm]
  refine hEc z fun hzE => hpq ?_
  have hq : q ∈ F := connectedComponentIn_nonempty_iff.1 ⟨z, hz⟩
  rw [connectedComponentIn_eq (hEp hzE), ← connectedComponentIn_eq hz]
  exact mem_connectedComponentIn hq

/-- **Crosscut by a circle arc** (GM tex l. 2478–2479; Pommerenke Prop. 2.12 for `Ĉ ∖ K`). -/
theorem crosscut_circle {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hKo : IsPreconnected Kᶜ) {c y₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hy₀ : y₀ ∈ sphere c r) (hy₀K : y₀ ∉ K) {Y : Set ℂ}
    (hY : Y = connectedComponentIn (sphere c r \ K) y₀) :
    ∃ u w : ℂ, u ∉ Y ∪ K ∧ w ∉ Y ∪ K ∧
      IsBounded (connectedComponentIn (Y ∪ K)ᶜ u) ∧
      ¬ IsBounded (connectedComponentIn (Y ∪ K)ᶜ w) ∧
      (∀ x ∉ Y ∪ K, x ∈ connectedComponentIn (Y ∪ K)ᶜ u ∨
        x ∈ connectedComponentIn (Y ∪ K)ᶜ w) ∧
      Y ⊆ closure (connectedComponentIn (Y ∪ K)ᶜ u) ∧
      Y ⊆ closure (connectedComponentIn (Y ∪ K)ᶜ w) := by
  have hKcl := hK.isClosed
  have hKne := hKc.nonempty
  have hYS : Y ⊆ sphere c r \ K := hY ▸ connectedComponentIn_subset _ _
  have hy₀Y : y₀ ∈ Y := hY ▸ mem_connectedComponentIn ⟨hy₀, hy₀K⟩
  have hYc : IsPreconnected Y := hY ▸ isPreconnected_connectedComponentIn
  have hYKcl : IsClosed (Y ∪ K) := hY ▸ isClosed_cc_union K hKcl c y₀ r
  set F := (Y ∪ K)ᶜ with hFdef
  have hFo : IsOpen F := hYKcl.isOpen_compl
  -- the two collars lie in `F`
  have hcolF : ∀ σ : ℝ, |σ| = 1 → col K c r Y σ ⊆ F := by
    intro σ hσ z hz
    obtain ⟨hzK, s, hs0, -, hs⟩ := col_prop hKcl hKne hr hσ hYS hz
    rintro (hzY | hzK')
    · have h1 : ‖z - c‖ = r := by
        have := (hYS hzY).1; rwa [mem_sphere, dist_eq_norm] at this
      have h2 : σ * s * r = 0 := by linarith
      rcases mul_eq_zero.1 h2 with h3 | h3
      · rcases mul_eq_zero.1 h3 with h4 | h4
        · rw [h4, abs_zero] at hσ; norm_num at hσ
        · linarith
      · linarith
    · exact hzK hzK'
  have hσm : |(-1 : ℝ)| = 1 := by norm_num
  have hσp : |(1 : ℝ)| = 1 := by norm_num
  -- the inner and the outer point near `y₀`
  obtain ⟨ρo, hρo, hballo⟩ := cc_sphere_open hKcl hKne hr hy₀ hy₀K
  rw [← hY] at hballo
  have hd := (hKcl.notMem_iff_infDist_pos hKne).1 hy₀K
  set ρ := min ρo (infDist y₀ K)
  have hρ : 0 < ρ := lt_min hρo hd
  obtain ⟨a, haC, hay⟩ := Metric.mem_closure_iff.1
    (subset_closure_col (K := K) (c := c) (r := r) (σ := -1) hy₀Y) ρ hρ
  obtain ⟨b, hbC, hby⟩ := Metric.mem_closure_iff.1
    (subset_closure_col (K := K) (c := c) (r := r) (σ := 1) hy₀Y) ρ hρ
  have hballsub : ball y₀ ρ ⊆ (K ∪ (sphere c r \ Y))ᶜ := by
    intro w hw
    rw [mem_ball, dist_comm] at hw
    rintro (hwK | ⟨hwS, hwY⟩)
    · have := infDist_le_dist_of_mem (x := y₀) hwK
      linarith [min_le_right ρo (infDist y₀ K)]
    · exact hwY (hballo ⟨by rw [mem_ball, dist_comm]; linarith [min_le_left ρo (infDist y₀ K)],
        hwS⟩)
  have hab : b ∈ connectedComponentIn (K ∪ (sphere c r \ Y))ᶜ a :=
    (convex_ball y₀ ρ).isPreconnected.subset_connectedComponentIn
      (by rw [mem_ball, dist_comm]; exact hay) hballsub (by rw [mem_ball, dist_comm]; exact hby)
  have ha : ‖a - c‖ < r := by
    obtain ⟨-, s, hs0, -, hs⟩ := col_prop hKcl hKne hr hσm hYS haC
    rw [hs]; nlinarith
  have hb : r < ‖b - c‖ := by
    obtain ⟨-, s, hs0, -, hs⟩ := col_prop hKcl hKne hr hσp hYS hbC
    rw [hs]; nlinarith
  have hsep : b ∉ connectedComponentIn F a := by
    have h := cc_sep hK hKc y₀ hr ha hb (by rw [hY] at hab; exact hab)
    rwa [← hY] at h
  have hca : col K c r Y (-1) ⊆ connectedComponentIn F a :=
    (col_isPreconnected hYc).subset_connectedComponentIn haC (hcolF _ hσm)
  have hcb : col K c r Y 1 ⊆ connectedComponentIn F b :=
    (col_isPreconnected hYc).subset_connectedComponentIn hbC (hcolF _ hσp)
  -- every component touches `Y`, hence meets a collar
  have hdich : ∀ x ∈ F, x ∈ connectedComponentIn F a ∨ x ∈ connectedComponentIn F b := by
    intro x hx
    set W := connectedComponentIn F x
    have hWo : IsOpen W := hFo.connectedComponentIn
    have htouch : (closure W ∩ Y).Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      have hsub : Kᶜ ⊆ W := hKo.subset_of_closure_inter_subset hWo
        ⟨x, fun hxK => hx (Or.inr hxK), mem_connectedComponentIn hx⟩ (fun z ⟨hzc, hzK⟩ => by
          by_contra hzW
          have hfr : z ∈ frontier W := ⟨hzc, by rwa [hWo.interior_eq]⟩
          rcases QuantumZipper.CA.Topo.frontier_connectedComponentIn_compl_subset hYKcl x hfr
            with hzY | hzK'
          · exact (eq_empty_iff_forall_notMem.1 hne) z ⟨hzc, hzY⟩
          · exact hzK hzK')
      exact (connectedComponentIn_subset _ _ (hsub hy₀K)) (Or.inl hy₀Y)
    obtain ⟨y, hyW, hyY⟩ := htouch
    have hyS := (hYS hyY).1
    obtain ⟨ρ1, hρ1, hball1⟩ := cc_sphere_open hKcl hKne hr hyS (hYS hyY).2
    have hcc : connectedComponentIn (sphere c r \ K) y = Y := by
      rw [hY]; exact (connectedComponentIn_eq (hY ▸ hyY)).symm
    rw [hcc] at hball1
    obtain ⟨ρ2, hρ2, hnear⟩ := mem_col_of_near hKcl hKne hr hYS hyY hρ1 hball1
    obtain ⟨z, hzW, hzy⟩ := Metric.mem_closure_iff.1 hyW (min ρ1 ρ2) (lt_min hρ1 hρ2)
    have hzF : z ∈ F := connectedComponentIn_subset _ _ hzW
    have hzS : z ∉ sphere c r := fun hzS => hzF (Or.inl (hball1
      ⟨by rw [mem_ball, dist_comm]; linarith [min_le_left ρ1 ρ2], hzS⟩))
    have hxz : connectedComponentIn F x = connectedComponentIn F z := connectedComponentIn_eq hzW
    rcases hnear z (by rw [mem_ball, dist_comm]; linarith [min_le_right ρ1 ρ2]) hzS with h | h
    · left; rw [connectedComponentIn_eq (hca h), ← hxz]; exact mem_connectedComponentIn hx
    · right; rw [connectedComponentIn_eq (hcb h), ← hxz]; exact mem_connectedComponentIn hx
  -- the far exterior
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall c
  set R' := max R r + 1
  set E := {z : ℂ | R' < ‖z - c‖}
  have hEpre : IsPreconnected E := by
    have h := (QuantumZipper.CA.Topo.isPreconnected_setOf_lt_norm R').image (fun z => z + c)
      (by fun_prop)
    convert h using 1
    ext w; constructor
    · intro hw; exact ⟨w - c, hw, by ring⟩
    · rintro ⟨z, hz, rfl⟩; show R' < ‖z + c - c‖; simpa using hz
  have hEF : E ⊆ F := by
    intro z hz
    have hz' : R' < ‖z - c‖ := hz
    rintro (hzY | hzK)
    · have := (hYS hzY).1; rw [mem_sphere, dist_eq_norm] at this
      linarith [le_max_right R r]
    · have := hR hzK; rw [mem_closedBall, dist_eq_norm] at this
      linarith [le_max_left R r]
  have hEc : ∀ z, z ∉ E → ‖z - c‖ ≤ R' := fun z hz => not_lt.1 hz
  have hEu : ¬ IsBounded E := by
    intro h
    obtain ⟨M, hM⟩ := h.subset_closedBall c
    set m := max M R' + 1
    have hm : ‖(c + (m : ℂ)) - c‖ = m := by
      rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
    have hmE : c + (m : ℂ) ∈ E := by
      show R' < ‖(c + (m : ℂ)) - c‖; rw [hm]; linarith [le_max_right M R']
    have := hM hmE; rw [mem_closedBall, dist_eq_norm, hm] at this
    linarith [le_max_left M R']
  set e := c + ((R' + 1 : ℝ) : ℂ)
  have heE : e ∈ E := by
    show R' < ‖e - c‖
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hYa : Y ⊆ closure (connectedComponentIn F a) := fun y hy =>
    closure_mono hca (subset_closure_col hy)
  have hYb : Y ⊆ closure (connectedComponentIn F b) := fun y hy =>
    closure_mono hcb (subset_closure_col hy)
  have haF : a ∈ F := hcolF _ hσm haC
  have hbF : b ∈ F := hcolF _ hσp hbC
  have hba : a ∉ connectedComponentIn F b := fun h => hsep (by
    rw [← connectedComponentIn_eq h]; exact mem_connectedComponentIn hbF)
  rcases hdich e (hEF heE) with he | he
  · obtain ⟨h1, h2⟩ := finish_aux hsep hEpre hEF heE he hEc hEu
    exact ⟨b, a, hbF, haF, h1, h2, fun x hx => (hdich x hx).symm, hYb, hYa⟩
  · obtain ⟨h1, h2⟩ := finish_aux hba hEpre hEF heE he hEc hEu
    exact ⟨a, b, haF, hbF, h1, h2, hdich, hYa, hYb⟩

end LQGMetric.Topo.Crosscut
