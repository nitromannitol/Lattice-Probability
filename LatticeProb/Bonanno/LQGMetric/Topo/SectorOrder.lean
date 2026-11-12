/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Topo.SectorOrder at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Topo.SectorRect

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Sector lemma, rectangle part II: sides of a crossing continuum and the order of three crossers

See `LQGMetric.Topo.SectorRect` for the overview. With `R = [x₀, x₁] × [y₀, y₁]`, a *crosser*
`L` (`IsCrosser`) is a continuum in `R` meeting the left and right sides and avoiding the top and
bottom sides. Its two sides are the components of `R \ L` containing the corners
`β = (x₀, y₀)` and `τ = (x₀, y₁)`. Components of `R \ L` are relatively open in `R` (`cc_nhds`),
their closures meet `L` (`closure_cc_meets`), and two points of one component are joined by a
continuum (a clamped path) inside it (`exists_continuum_in_cc`). With the continuum crossing
lemma `lr_tb_meet` this gives: `β` and `τ` lie in different components; a crosser disjoint from
`L` lies on one side of `L` (`crosser_dichotomy`); two disjoint crossers do not lie on the same
side of each other (`not_both_side`). Hence `three_crossers_rect`. Own write-up (DEVIATIONS,
proposed), classical content of Newman, *Elements of the topology of plane sets of points*, Ch. V.
-/

namespace LQGMetric

namespace Sector

open Set Metric RectCross

variable {x₀ x₁ y₀ y₁ : ℝ}

local notation "𝐑" => rect x₀ x₁ y₀ y₁

/-- A crossing continuum of the rectangle avoiding its top and bottom sides. -/
def IsCrosser (x₀ x₁ y₀ y₁ : ℝ) (L : Set ℂ) : Prop :=
  IsCompact L ∧ IsPreconnected L ∧ L ⊆ rect x₀ x₁ y₀ y₁ ∧ (∃ p ∈ L, p.re = x₀) ∧
    (∃ p ∈ L, p.re = x₁) ∧ ∀ p ∈ L, y₀ < p.im ∧ p.im < y₁

theorem cc_nhds {L : Set ℂ} (hL : IsClosed L) {p q : ℂ}
    (hq : q ∈ connectedComponentIn (𝐑 \ L) p) :
    ∃ ε > 0, ball q ε ∩ 𝐑 ⊆ connectedComponentIn (𝐑 \ L) p := by
  have hq' := connectedComponentIn_subset _ _ hq
  obtain ⟨ε, hε, hεL⟩ := Metric.isOpen_iff.1 hL.isOpen_compl q hq'.2
  refine ⟨ε, hε, ?_⟩
  rw [connectedComponentIn_eq hq]
  exact ((convex_ball q ε).inter convex_rect).isPreconnected.subset_connectedComponentIn
    ⟨mem_ball_self hε, hq'.1⟩ fun z hz => ⟨hz.2, hεL hz.1⟩

theorem cc_eq_of_mem_closure {L : Set ℂ} (hL : IsClosed L) {p q a : ℂ}
    (hq : q ∈ connectedComponentIn (𝐑 \ L) p)
    (hqa : q ∈ closure (connectedComponentIn (𝐑 \ L) a)) :
    connectedComponentIn (𝐑 \ L) p = connectedComponentIn (𝐑 \ L) a := by
  obtain ⟨ε, hε, hsub⟩ := cc_nhds hL hq
  obtain ⟨w, hw, hqw⟩ := Metric.mem_closure_iff.1 hqa ε hε
  have hwR : w ∈ 𝐑 := (connectedComponentIn_subset _ _ hw).1
  have hw' : w ∈ connectedComponentIn (𝐑 \ L) p :=
    hsub ⟨by rw [mem_ball, dist_comm]; exact hqw, hwR⟩
  rw [connectedComponentIn_eq hw', connectedComponentIn_eq hw]

theorem closure_cc_meets {L : Set ℂ} (hL : IsClosed L) (hLne : L.Nonempty)
    (hLR : L ⊆ 𝐑) {b : ℂ} (hb : b ∈ 𝐑) (hbL : b ∉ L) :
    (closure (connectedComponentIn (𝐑 \ L) b) ∩ L).Nonempty := by
  by_contra hne
  set C := connectedComponentIn (𝐑 \ L) b with hC
  choose! ε hεpos hεsub using fun q (hq : q ∈ C) => cc_nhds hL hq
  have hR : IsPreconnected 𝐑 := convex_rect.isPreconnected
  obtain ⟨l, hl⟩ := hLne
  have hbC : b ∈ C := mem_connectedComponentIn ⟨hb, hbL⟩
  obtain ⟨z, hzR, hzu, hzv⟩ := hR (⋃ q ∈ C, ball q (ε q)) (closure C)ᶜ
    (isOpen_biUnion fun q _ => isOpen_ball) isClosed_closure.isOpen_compl
    (fun z hzR => by
      by_cases hz : z ∈ closure C
      · left
        have hzL : z ∉ L := fun h => hne ⟨z, hz, h⟩
        have hzC : z ∈ C := by
          have := cc_eq_of_mem_closure hL
            (mem_connectedComponentIn (⟨hzR, hzL⟩ : z ∈ 𝐑 \ L)) hz
          rw [hC, ← this]; exact mem_connectedComponentIn ⟨hzR, hzL⟩
        exact mem_iUnion₂.2 ⟨z, hzC, mem_ball_self (hεpos z hzC)⟩
      · exact Or.inr hz)
    ⟨b, hb, mem_iUnion₂.2 ⟨b, hbC, mem_ball_self (hεpos b hbC)⟩⟩
    ⟨l, hLR hl, fun h => hne ⟨l, h, hl⟩⟩
  obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.1 hzu
  exact hzv (subset_closure (hεsub q hq ⟨hzq, hzR⟩))

/-- Two points of a component of `R \ L` are joined by a continuum inside the component. -/
theorem exists_continuum_in_cc (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) {L : Set ℂ} (hL : IsClosed L)
    {a b : ℂ} (ha : a ∈ 𝐑 \ L) (hb : b ∈ connectedComponentIn (𝐑 \ L) a) :
    ∃ M : Set ℂ, IsCompact M ∧ IsPreconnected M ∧ M ⊆ connectedComponentIn (𝐑 \ L) a ∧
      a ∈ M ∧ b ∈ M := by
  set C := connectedComponentIn (𝐑 \ L) a with hC
  choose! ε hεpos hεsub using fun q (hq : q ∈ C) => cc_nhds hL hq
  have haC : a ∈ C := mem_connectedComponentIn ha
  obtain ⟨γ, hγc, hγ0, hγ1, hγ⟩ := exists_clamp_path (x₀ := x₀) (x₁ := x₁) (y₀ := y₀)
    (y₁ := y₁) (isOpen_biUnion fun q _ => isOpen_ball)
    (isPreconnected_biUnion_ball isPreconnected_connectedComponentIn ε hεpos)
    (mem_iUnion₂.2 ⟨a, haC, mem_ball_self (hεpos a haC)⟩)
    (mem_iUnion₂.2 ⟨b, hb, mem_ball_self (hεpos b hb)⟩) ha.1
    (connectedComponentIn_subset _ _ hb).1
  refine ⟨γ '' Icc 0 1, isCompact_Icc.image hγc, isPreconnected_Icc.image _ hγc.continuousOn,
    ?_, ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩, ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1⟩⟩
  rintro _ ⟨t, -, rfl⟩
  obtain ⟨z, hz, hzt⟩ := hγ t
  obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.1 hz
  rw [hzt]
  exact hεsub q hq ⟨(dist_clampR_le hx hy z (connectedComponentIn_subset _ _ hq).1).trans_lt hzq,
    clampR_mem hx hy z⟩

/-- A top point is not in the component of a bottom point of `R \ L` for a crosser `L`. -/
theorem not_mem_cc_of_crosser (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) {L : Set ℂ}
    (hL : IsCrosser x₀ x₁ y₀ y₁ L) {a c : ℂ} (ha : a ∈ 𝐑 \ L) (ha0 : a.im = y₀)
    (hc1 : c.im = y₁) : c ∉ connectedComponentIn (𝐑 \ L) a := by
  intro hcC
  obtain ⟨M, hMc, hMp, hMsub, haM, hcM⟩ := exists_continuum_in_cc hx hy hL.1.isClosed ha hcC
  obtain ⟨z, hzL, hzM⟩ := lr_tb_meet hx hy hL.1 hL.2.1 hL.2.2.1 hL.2.2.2.1 hL.2.2.2.2.1 hMc hMp
    (fun z hz => (connectedComponentIn_subset _ _ (hMsub hz)).1) ⟨c, hcM, hc1⟩ ⟨a, haM, ha0⟩
  exact (connectedComponentIn_subset _ _ (hMsub hzM)).2 hzL

theorem not_mem_cc_of_crosser' (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) {L : Set ℂ}
    (hL : IsCrosser x₀ x₁ y₀ y₁ L) {a c : ℂ} (hc : c ∈ 𝐑 \ L) (ha1 : a.im = y₁)
    (hc0 : c.im = y₀) : c ∉ connectedComponentIn (𝐑 \ L) a := by
  intro hcC
  have hcC' := mem_connectedComponentIn hc
  rw [← connectedComponentIn_eq hcC] at hcC'
  have haC : a ∈ connectedComponentIn (𝐑 \ L) a :=
    mem_connectedComponentIn (connectedComponentIn_nonempty_iff.1 ⟨c, hcC⟩)
  rw [connectedComponentIn_eq hcC] at haC
  exact not_mem_cc_of_crosser hx hy hL hc hc0 ha1 haC

theorem crosser_dichotomy (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) {L L' : Set ℂ}
    (hL : IsCrosser x₀ x₁ y₀ y₁ L) (hL' : IsCrosser x₀ x₁ y₀ y₁ L') (hd : Disjoint L L')
    {β τ : ℂ} (hβ : β ∈ 𝐑) (hτ : τ ∈ 𝐑) (hβ0 : β.im = y₀) (hτ1 : τ.im = y₁) :
    L' ⊆ connectedComponentIn (𝐑 \ L) τ ∨ L' ⊆ connectedComponentIn (𝐑 \ L) β := by
  have hβL : β ∉ L := fun h => by have := (hL.2.2.2.2.2 β h).1; linarith
  have hτL : τ ∉ L := fun h => by have := (hL.2.2.2.2.2 τ h).2; linarith
  have hcl := hL.1.isClosed
  obtain ⟨p, hp, -⟩ := hL'.2.2.2.1
  obtain ⟨l, hl, -⟩ := hL.2.2.2.1
  have hL'R : L' ⊆ 𝐑 \ L := fun z hz => ⟨hL'.2.2.1 hz, fun h => hd.le_bot ⟨h, hz⟩⟩
  have hsub := hL'.2.1.subset_connectedComponentIn hp hL'R
  by_contra hno
  rw [not_or] at hno
  obtain ⟨hnU, hnD⟩ := hno
  set U := connectedComponentIn (𝐑 \ L) τ with hU
  set D := connectedComponentIn (𝐑 \ L) β with hD
  have hUL := closure_cc_meets hcl ⟨l, hl⟩ hL.2.2.1 hτ hτL
  have hDL := closure_cc_meets hcl ⟨l, hl⟩ hL.2.2.1 hβ hβL
  have hUR : closure U ⊆ 𝐑 :=
    closure_minimal (fun z hz => (connectedComponentIn_subset _ _ hz).1) isClosed_rect
  have hDR : closure D ⊆ 𝐑 :=
    closure_minimal (fun z hz => (connectedComponentIn_subset _ _ hz).1) isClosed_rect
  have hMR : closure U ∪ L ∪ closure D ⊆ 𝐑 := union_subset (union_subset hUR hL.2.2.1) hDR
  have hMc : IsCompact (closure U ∪ L ∪ closure D) := isCompact_rect.of_isClosed_subset
    ((isClosed_closure.union hcl).union isClosed_closure) hMR
  have hMp : IsPreconnected (closure U ∪ L ∪ closure D) := by
    refine (isPreconnected_connectedComponentIn.closure.union' hUL hL.2.1).union' ?_
      isPreconnected_connectedComponentIn.closure
    obtain ⟨z, hz1, hz2⟩ := hDL
    exact ⟨z, Or.inr hz2, hz1⟩
  obtain ⟨z, hzL', hzM⟩ := lr_tb_meet hx hy hL'.1 hL'.2.1 hL'.2.2.1 hL'.2.2.2.1
    hL'.2.2.2.2.1 hMc hMp hMR
    ⟨τ, Or.inl (Or.inl (subset_closure (mem_connectedComponentIn ⟨hτ, hτL⟩))), hτ1⟩
    ⟨β, Or.inr (subset_closure (mem_connectedComponentIn ⟨hβ, hβL⟩)), hβ0⟩
  rcases hzM with (hzU | hzL) | hzD
  · have e := cc_eq_of_mem_closure hcl (hsub hzL') hzU
    exact hnU (by rw [hU, ← e]; exact hsub)
  · exact hd.le_bot ⟨hzL, hzL'⟩
  · have e := cc_eq_of_mem_closure hcl (hsub hzL') hzD
    exact hnD (by rw [hD, ← e]; exact hsub)

theorem cc_subset_cc_of_side {L L' : Set ℂ} {a c : ℂ} (ha : a ∈ 𝐑 \ L) (haL' : a ∉ L')
    (hc : c ∈ 𝐑 \ L) (hca : c ∉ connectedComponentIn (𝐑 \ L) a)
    (hL' : L' ⊆ connectedComponentIn (𝐑 \ L) c) :
    connectedComponentIn (𝐑 \ L) a ⊆ connectedComponentIn (𝐑 \ L') a := by
  refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn ha) fun z hz =>
      ⟨(connectedComponentIn_subset _ _ hz).1, fun hzL' => hca ?_⟩
  rw [connectedComponentIn_eq hz, ← connectedComponentIn_eq (hL' hzL')]
  exact mem_connectedComponentIn hc

theorem not_both_side {L L' : Set ℂ} (hL : IsClosed L) (hL' : IsClosed L')
    (hL'ne : L'.Nonempty) (hL'R : L' ⊆ 𝐑) {a c : ℂ} (ha : a ∈ 𝐑 \ L) (haL' : a ∉ L')
    (hc : c ∈ 𝐑 \ L) (hcL' : c ∉ L') (hca : c ∉ connectedComponentIn (𝐑 \ L) a)
    (hca' : c ∉ connectedComponentIn (𝐑 \ L') a) (h1 : L' ⊆ connectedComponentIn (𝐑 \ L) c)
    (h2 : L ⊆ connectedComponentIn (𝐑 \ L') c) : False := by
  have e1 := cc_subset_cc_of_side ha haL' hc hca h1
  have e2 := cc_subset_cc_of_side ⟨ha.1, haL'⟩ ha.2 ⟨hc.1, hcL'⟩ hca' h2
  have heq := e1.antisymm e2
  obtain ⟨q, hq, hqL'⟩ := closure_cc_meets hL' hL'ne hL'R ha.1 haL'
  rw [← heq] at hq
  have := cc_eq_of_mem_closure hL (h1 hqL') hq
  exact hca (this ▸ mem_connectedComponentIn hc)

theorem same_side {F X Y N : Set ℂ} {t : ℂ} (hN : IsPreconnected N) (hNF : N ⊆ F)
    (hX : X ⊆ N) (hY : Y ⊆ N) (hXne : X.Nonempty) (hXt : X ⊆ connectedComponentIn F t) :
    Y ⊆ connectedComponentIn F t := by
  obtain ⟨p, hp⟩ := hXne
  have hNp := hN.subset_connectedComponentIn (hX hp) hNF
  rw [connectedComponentIn_eq (hXt hp)]
  exact hY.trans hNp

theorem pair_facts (hx : x₀ ≤ x₁) (hy : y₀ < y₁) {L L' : Set ℂ}
    (hL : IsCrosser x₀ x₁ y₀ y₁ L) (hL' : IsCrosser x₀ x₁ y₀ y₁ L') (hd : Disjoint L L') :
    (L' ⊆ connectedComponentIn (𝐑 \ L) ⟨x₀, y₁⟩ ∨ L' ⊆ connectedComponentIn (𝐑 \ L) ⟨x₀, y₀⟩) ∧
    ¬(L' ⊆ connectedComponentIn (𝐑 \ L) ⟨x₀, y₁⟩ ∧
      L ⊆ connectedComponentIn (𝐑 \ L') ⟨x₀, y₁⟩) ∧
    ¬(L' ⊆ connectedComponentIn (𝐑 \ L) ⟨x₀, y₀⟩ ∧
      L ⊆ connectedComponentIn (𝐑 \ L') ⟨x₀, y₀⟩) := by
  have hβ : (⟨x₀, y₀⟩ : ℂ) ∈ 𝐑 := ⟨⟨le_rfl, hx⟩, ⟨le_rfl, hy.le⟩⟩
  have hτ : (⟨x₀, y₁⟩ : ℂ) ∈ 𝐑 := ⟨⟨le_rfl, hx⟩, ⟨hy.le, le_rfl⟩⟩
  have nβ : ∀ {K}, IsCrosser x₀ x₁ y₀ y₁ K → (⟨x₀, y₀⟩ : ℂ) ∉ K := fun hK h =>
    lt_irrefl y₀ (hK.2.2.2.2.2 _ h).1
  have nτ : ∀ {K}, IsCrosser x₀ x₁ y₀ y₁ K → (⟨x₀, y₁⟩ : ℂ) ∉ K := fun hK h =>
    lt_irrefl y₁ (hK.2.2.2.2.2 _ h).2
  obtain ⟨l', hl', -⟩ := hL'.2.2.2.1
  refine ⟨crosser_dichotomy hx hy.le hL hL' hd hβ hτ rfl rfl, fun ⟨h1, h2⟩ => ?_,
    fun ⟨h1, h2⟩ => ?_⟩
  · exact not_both_side hL.1.isClosed hL'.1.isClosed ⟨l', hl'⟩ hL'.2.2.1 ⟨hβ, nβ hL⟩ (nβ hL')
      ⟨hτ, nτ hL⟩ (nτ hL') (not_mem_cc_of_crosser hx hy.le hL ⟨hβ, nβ hL⟩ rfl rfl)
      (not_mem_cc_of_crosser hx hy.le hL' ⟨hβ, nβ hL'⟩ rfl rfl) h1 h2
  · exact not_both_side hL.1.isClosed hL'.1.isClosed ⟨l', hl'⟩ hL'.2.2.1 ⟨hτ, nτ hL⟩ (nτ hL')
      ⟨hβ, nβ hL⟩ (nβ hL') (not_mem_cc_of_crosser' hx hy.le hL ⟨hβ, nβ hL⟩ rfl rfl)
      (not_mem_cc_of_crosser' hx hy.le hL' ⟨hβ, nβ hL'⟩ rfl rfl) h1 h2

/-- **Three crossers.** Of three pairwise disjoint crossers of a rectangle, one separates the
other two: there are no connected `Nᵢ ⊆ R \ Lᵢ` containing the other two crossers. -/
theorem three_crossers_rect (hx : x₀ ≤ x₁) (hy : y₀ < y₁) {L₁ L₂ L₃ N₁ N₂ N₃ : Set ℂ}
    (h₁ : IsCrosser x₀ x₁ y₀ y₁ L₁) (h₂ : IsCrosser x₀ x₁ y₀ y₁ L₂)
    (h₃ : IsCrosser x₀ x₁ y₀ y₁ L₃)
    (d₁₂ : Disjoint L₁ L₂) (d₁₃ : Disjoint L₁ L₃) (d₂₃ : Disjoint L₂ L₃)
    (hN₁ : IsPreconnected N₁) (hN₁R : N₁ ⊆ 𝐑 \ L₁) (hN₁s : L₂ ∪ L₃ ⊆ N₁)
    (hN₂ : IsPreconnected N₂) (hN₂R : N₂ ⊆ 𝐑 \ L₂) (hN₂s : L₁ ∪ L₃ ⊆ N₂)
    (hN₃ : IsPreconnected N₃) (hN₃R : N₃ ⊆ 𝐑 \ L₃) (hN₃s : L₁ ∪ L₂ ⊆ N₃) : False := by
  have ne : ∀ {K}, IsCrosser x₀ x₁ y₀ y₁ K → K.Nonempty := fun hK =>
    let ⟨p, hp, _⟩ := hK.2.2.2.1; ⟨p, hp⟩
  have ss : ∀ {Li Lj Lk Ni : Set ℂ} {t : ℂ}, IsCrosser x₀ x₁ y₀ y₁ Lj → IsPreconnected Ni →
      Ni ⊆ 𝐑 \ Li → Lj ∪ Lk ⊆ Ni → Lj ⊆ connectedComponentIn (𝐑 \ Li) t →
      Lk ⊆ connectedComponentIn (𝐑 \ Li) t := fun hj hN hNR hs h =>
    same_side hN hNR (subset_union_left.trans hs) (subset_union_right.trans hs) (ne hj) h
  obtain ⟨D12, U12, B12⟩ := pair_facts hx hy h₁ h₂ d₁₂
  obtain ⟨-, U13, B13⟩ := pair_facts hx hy h₁ h₃ d₁₃
  obtain ⟨D21, -, -⟩ := pair_facts hx hy h₂ h₁ d₁₂.symm
  obtain ⟨-, U23, B23⟩ := pair_facts hx hy h₂ h₃ d₂₃
  obtain ⟨D31, -, -⟩ := pair_facts hx hy h₃ h₁ d₁₃.symm
  rcases D12 with u12 | n12
  · have u13 := ss h₂ hN₁ hN₁R hN₁s u12
    rcases D21 with u21 | n21
    · exact U12 ⟨u12, u21⟩
    have n23 := ss h₁ hN₂ hN₂R hN₂s n21
    rcases D31 with u31 | n31
    · exact U13 ⟨u13, u31⟩
    exact B23 ⟨n23, ss h₁ hN₃ hN₃R hN₃s n31⟩
  · have n13 := ss h₂ hN₁ hN₁R hN₁s n12
    rcases D21 with u21 | n21
    · have u23 := ss h₁ hN₂ hN₂R hN₂s u21
      rcases D31 with u31 | n31
      · exact U23 ⟨u23, ss h₁ hN₃ hN₃R hN₃s u31⟩
      · exact B13 ⟨n13, n31⟩
    · exact B12 ⟨n12, n21⟩

end Sector

end LQGMetric
