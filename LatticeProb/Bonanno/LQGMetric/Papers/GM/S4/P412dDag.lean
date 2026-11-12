/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412dDag at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412dArc

/-!
# GM L4.14′, repaired proof (DEC-86 (1)): (†)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.14
(`lem-dc-set`, l. 2485, 2490–2501), as repaired in DEC-86 (decisions/DEC-86.md, item (1), (†)).

* `p412d_dagger` — (†): for `X ⊆ int B` and a bounded component `V` of `ℂ ∖ (X ∪ K)` there is an
  arc `α ⊆ cl N(B)` of `∂B ∖ K` with `V ⊆ U(α)`; the inner collar of `α` lies in `U(α)`.
  Proof as in DEC-86: `V ∩ cl N(B) = ∅`; a point `p` of `∂M ∩ (ℂ∖K)`, `M` the component of
  `(ℂ∖K) ∖ cl N(B)` of `V`, lies on `∂B ∖ K`; near `p` the outer collar of `α ∋ p` lies in
  `N(B) ⊆ W(α)` and the inner one in `U(α)`, and `M` meets the inner collar.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Bornology
open LQGMetric.Topo.Crosscut

namespace LQGMetric.GM

/-- **(†)** (DEC-86 (1)). -/
theorem p412d_dagger {K X : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hKo : IsPreconnected Kᶜ) (hXK : X ⊆ Kᶜ) {c v : ℂ} {r : ℝ} (hr : 0 < r)
    (hXB : X ⊆ ball c r) (hv : v ∉ X ∪ K)
    (hb : IsBounded (connectedComponentIn (X ∪ K)ᶜ v)) :
    ∃ y₀ ∈ sphere c r, y₀ ∉ K ∧
      connectedComponentIn (sphere c r \ K) y₀ ⊆ closure (dgW (closedBall c r ∪ K)) ∧
      connectedComponentIn (X ∪ K)ᶜ v ⊆
        dgB (connectedComponentIn (sphere c r \ K) y₀ ∪ K) ∧
      col K c r (connectedComponentIn (sphere c r \ K) y₀) (-1) ⊆
        dgB (connectedComponentIn (sphere c r \ K) y₀ ∪ K) := by
  set V := connectedComponentIn (X ∪ K)ᶜ v
  set Fb := closedBall c r ∪ K
  have hKne := hKc.nonempty
  have hKcl := hK.isClosed
  have hFbb : IsBounded Fb := isBounded_closedBall.union hK.isBounded
  have hFbcl : IsClosed Fb := isClosed_closedBall.union hKcl
  obtain ⟨hNpre, hNu⟩ := p412d_dgW_props hFbb
  set N := dgW Fb
  have hNFb : N ⊆ Fbᶜ := p412d_dgW_compl Fb
  have hNo : IsOpen N := p412d_isOpen_dgW hFbcl
  have hNout : ∀ z ∈ N, r < dist z c ∧ z ∉ K := fun z hz =>
    ⟨not_le.1 fun h => hNFb hz (Or.inl h), fun h => hNFb hz (Or.inr h)⟩
  have hvV : v ∈ V := mem_connectedComponentIn hv
  -- `V ∩ cl N = ∅`
  have hVN : ∀ z ∈ V, z ∉ closure N := by
    intro z hzV hzN
    have hzF : z ∈ (X ∪ K)ᶜ := connectedComponentIn_subset _ _ hzV
    have hpre : IsPreconnected (insert z N) :=
      hNpre.subset_closure (subset_insert _ _) (insert_subset hzN subset_closure)
    have hsub : insert z N ⊆ (X ∪ K)ᶜ := by
      refine insert_subset hzF fun q hq hqXK => ?_
      rcases hqXK with hqX | hqK
      · have := mem_ball.1 (hXB hqX); linarith [(hNout q hq).1]
      · exact (hNout q hq).2 hqK
    have := hpre.subset_connectedComponentIn (mem_insert _ _) hsub
    rw [← connectedComponentIn_eq hzV] at this
    exact hNu (hb.subset ((subset_insert _ _).trans this))
  -- the component `M` of `(ℂ ∖ K) ∖ cl N` containing `v`
  set O := Kᶜ \ closure N
  have hOo : IsOpen O := hKcl.isOpen_compl.sdiff isClosed_closure
  have hvO : v ∈ O := ⟨fun h => hv (Or.inr h), hVN v hvV⟩
  set M := connectedComponentIn O v
  have hMo : IsOpen M := hOo.connectedComponentIn
  have hMO : M ⊆ O := connectedComponentIn_subset _ _
  have hMcl : ∀ p ∈ closure M, p ∈ O → p ∈ M := by
    intro p hpM hpO
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hpM _ hOo.connectedComponentIn
      (mem_connectedComponentIn hpO)
    have h1 : M = connectedComponentIn O z := connectedComponentIn_eq hz2
    rw [h1, ← connectedComponentIn_eq hz1]
    exact mem_connectedComponentIn hpO
  -- a point of `∂M` off `K`
  obtain ⟨p, hpM, hpK, hpnM⟩ : ∃ p ∈ closure M, p ∉ K ∧ p ∉ M := by
    by_contra hcon
    push Not at hcon
    have hsub : Kᶜ ⊆ M := hKo.subset_of_closure_inter_subset hMo
      ⟨v, hvO.1, mem_connectedComponentIn hvO⟩ (fun z ⟨hz1, hz2⟩ => hcon z hz1 hz2)
    obtain ⟨n, hn⟩ : N.Nonempty := by
      by_contra h
      exact hNu (by rw [not_nonempty_iff_eq_empty.1 h]; exact isBounded_empty)
    exact (hMO (hsub (hNout n hn).2)).2 (subset_closure hn)
  have hpN : p ∈ closure N := by
    by_contra h
    exact hpnM (hMcl p hpM ⟨hpK, h⟩)
  have hpnN : p ∉ N := fun h => by
    obtain ⟨z, hzN, hzM⟩ := mem_closure_iff.1 hpM N hNo h
    exact (hMO hzM).2 (subset_closure hzN)
  have hpFb : p ∈ Fb := by
    by_contra hpF
    rcases p412d_mem_dgB_or Fb hpF with h | h
    · obtain ⟨z, hzB, hzN⟩ := mem_closure_iff.1 hpN _ (p412d_isOpen_dgB hFbcl) h
      exact disjoint_left.1 (p412d_dgB_dgW_disj Fb) hzB hzN
    · exact hpnN h
  have hpS : p ∈ sphere c r := by
    have hpB : p ∈ closedBall c r := hpFb.resolve_right hpK
    refine mem_sphere.2 (le_antisymm (mem_closedBall.1 hpB) (not_lt.1 fun hlt => ?_))
    obtain ⟨z, hzb, hzN⟩ := mem_closure_iff.1 hpN _ isOpen_ball (mem_ball.2 hlt)
    linarith [(hNout z hzN).1, mem_ball.1 hzb]
  -- the arc `α ∋ p` and its collars
  obtain ⟨ρo, hρo, hballo⟩ := cc_sphere_open hKcl hKne hr hpS hpK
  set α := connectedComponentIn (sphere c r \ K) p
  have hαS : α ⊆ sphere c r \ K := connectedComponentIn_subset _ _
  have hpα : p ∈ α := mem_connectedComponentIn ⟨hpS, hpK⟩
  have hαc : IsPreconnected α := isPreconnected_connectedComponentIn
  obtain ⟨ρ1, hρ1, hnear⟩ := mem_col_of_near hKcl hKne hr hαS hpα hρo hballo
  set δ := min ρo ρ1
  have hδ : 0 < δ := lt_min hρo hρ1
  have hσm : |(-1 : ℝ)| = 1 := by norm_num
  have hσp : |(1 : ℝ)| = 1 := by norm_num
  have hcolm : ∀ z ∈ col K c r α (-1), z ∉ K ∧ dist z c < r := fun z hz => by
    obtain ⟨hzK, s, hs0, -, hs⟩ := col_prop hKcl hKne hr hσm hαS hz
    exact ⟨hzK, by rw [dist_eq_norm, hs]; nlinarith⟩
  have hcolp : ∀ z ∈ col K c r α 1, z ∉ K ∧ r < dist z c := fun z hz => by
    obtain ⟨hzK, s, hs0, -, hs⟩ := col_prop hKcl hKne hr hσp hαS hz
    exact ⟨hzK, by rw [dist_eq_norm, hs]; nlinarith⟩
  have hnear' : ∀ z, dist p z < δ → z ∉ α → z ∈ col K c r α (-1) ∪ col K c r α 1 := by
    intro z hz hzα
    refine hnear z (by rw [mem_ball, dist_comm]; exact lt_of_lt_of_le hz (min_le_right _ _))
      fun hzS => hzα (hballo ⟨?_, hzS⟩)
    rw [mem_ball, dist_comm]; exact lt_of_lt_of_le hz (min_le_left _ _)
  have hαr : ∀ z ∈ α, dist z c = r := fun z hz => mem_sphere.1 (hαS hz).1
  -- the outer collar lies in `N`
  have hcolpN : col K c r α 1 ⊆ N := by
    obtain ⟨z, hzN, hz⟩ := Metric.mem_closure_iff.1 hpN δ hδ
    have hzα : z ∉ α := fun h => by linarith [hαr z h, (hNout z hzN).1]
    have hz1 : z ∈ col K c r α 1 := (hnear' z hz hzα).resolve_left fun h => by
      linarith [(hcolm z h).2, (hNout z hzN).1]
    refine p412d_sub_dgW (col_isPreconnected hαc) (fun q hq hqF => ?_) hz1 hzN
    rcases hqF with h | h
    · linarith [mem_closedBall.1 h, (hcolp q hq).2]
    · exact (hcolp q hq).1 h
  have hαN : α ⊆ closure N := fun q hq => closure_mono hcolpN (subset_closure_col hq)
  have hNαK : N ⊆ (α ∪ K)ᶜ := by
    rintro z hzN (h | h)
    · linarith [hαr z h, (hNout z hzN).1]
    · exact (hNout z hzN).2 h
  have hNW : N ⊆ dgW (α ∪ K) := p412d_sub_dgW_of_unbdd hNpre hNαK hNu
  obtain ⟨u, w, -, -, hαB, -⟩ := p412d_arc hK hKc hKo hr hpS hpK
  -- the inner collar lies in `U(α)`
  have hcolmF : col K c r α (-1) ⊆ (α ∪ K)ᶜ := by
    rintro z hz (h | h)
    · linarith [hαr z h, (hcolm z hz).2]
    · exact (hcolm z hz).1 h
  have hcolmB : col K c r α (-1) ⊆ dgB (α ∪ K) := by
    have hBo : IsOpen (dgB (α ∪ K)) :=
      p412d_isOpen_dgB (isClosed_cc_union K hKcl c p r)
    obtain ⟨z, hzB, hz⟩ := Metric.mem_closure_iff.1 (hαB hpα) δ hδ
    have hzα : z ∉ α := fun h => hzB.1 (Or.inl h)
    have hzm : z ∈ col K c r α (-1) := (hnear' z hz hzα).resolve_right fun h =>
      disjoint_left.1 (p412d_dgB_dgW_disj _) hzB (hNW (hcolpN h))
    exact p412d_sub_dgB (col_isPreconnected hαc) hcolmF hzm hzB
  -- `M` meets the inner collar
  have hMαK : M ⊆ (α ∪ K)ᶜ := by
    rintro z hzM (h | h)
    · exact (hMO hzM).2 (hαN h)
    · exact (hMO hzM).1 h
  obtain ⟨z, hzM, hz⟩ := Metric.mem_closure_iff.1 hpM δ hδ
  have hzα : z ∉ α := fun h => hMαK hzM (Or.inl h)
  have hzm : z ∈ col K c r α (-1) := (hnear' z hz hzα).resolve_right fun h =>
    (hMO hzM).2 (subset_closure (hcolpN h))
  have hMB : M ⊆ dgB (α ∪ K) :=
    p412d_sub_dgB isPreconnected_connectedComponentIn hMαK hzM (hcolmB hzm)
  have hVαK : V ⊆ (α ∪ K)ᶜ := by
    rintro z hzV (h | h)
    · exact hVN z hzV (hαN h)
    · exact (connectedComponentIn_subset _ _ hzV) (Or.inr h)
  exact ⟨p, hpS, hpK, hαN, p412d_sub_dgB isPreconnected_connectedComponentIn hVαK hvV
    (hMB (mem_connectedComponentIn hvO)), hcolmB⟩

end LQGMetric.GM
