/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412eSep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eCollar
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eArcs
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412cInt
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanPunct
import LatticeProb.Bonanno.LQGMetric.Topo.CrosscutTheta

/-!
# GM L4.13′, separation step (l. 2081–2082) for filled metric balls

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.13, l. 2081–2082:
"Hence one of the connected components `V` of `ℂ ∖ (𝓑^•_s ∪ X)` is bounded and contains an
endpoint of `I`. Since `Cl'(X)` intersects `I` only at `P(s)`, … also `P(s) ∈ ∂V`."

* `p412e_sep`: `K = 𝓑^•_t`, `X ⊆ ℂ ∖ K` connected and bounded with `cl X ∩ K ⊆ {p, q}`,
  `p ≠ q ∈ ∂K ∩ cl X`: there is a bounded component `V` of `ℂ ∖ (cl X ∪ K)` and a preconnected
  `S ⊆ ∂K` (one of the two arcs of `∂K` between `p` and `q`) with `p, q ∈ S ⊆ cl V`. Proof:
  `p412e_split` (arcs `A, B` via the exterior map `Ψ`), `theta_bounded` (Topo.Crosscut, with
  `hint := p412c_filledBall_interior_isPreconnected`), `p412e_collar` with (LC)
  (`p412c_filledBall_locConnAt`).
* `p412e_endpoint`: a preconnected `S ⊆ ∂K` from `p ∈ I` to `q ∉ I` contains an "endpoint" of
  `I`, i.e. a point of `cl I ∩ cl(∂K ∖ I)` (reading of "endpoint of `I`", proposed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- the endpoint of `I` on a connected piece `S` of `∂K` joining `p ∈ I` to `q ∉ I` -/
theorem p412e_endpoint {F I S : Set ℂ} (hSF : S ⊆ F) (hS : IsPreconnected S)
    {p q : ℂ} (hpS : p ∈ S) (hqS : q ∈ S) (hpI : p ∈ I) (hqI : q ∉ I) :
    ∃ e ∈ S, e ∈ closure I ∧ e ∈ closure (F \ I) := by
  obtain ⟨e, heS, he1, he2⟩ := isPreconnected_closed_iff.1 hS (closure I) (closure (F \ I))
    isClosed_closure isClosed_closure
    (fun x hx => by
      by_cases hxI : x ∈ I
      · exact Or.inl (subset_closure hxI)
      · exact Or.inr (subset_closure ⟨hSF hx, hxI⟩))
    ⟨p, hpS, subset_closure hpI⟩ ⟨q, hqS, subset_closure ⟨hSF hqS, hqI⟩⟩
  exact ⟨e, heS, he1, he2⟩

/-- the point `α ∈ ∂K` off a closed set `Z` has nearby points `a ∉ K`, `a' ∈ int K` with the
segment `[a, a']` off `Z`, and all points of `ℂ ∖ K` near `α` lie in the component of `a` of
`ℂ ∖ (K ∪ X')` (`X' ⊆ Z`) -/
theorem p412e_side {D : ContMetric} {𝕫 : ℂ} {t : ℝ} (ht : 0 < t) (hL : D.IsLength)
    (hbd : Bornology.IsBounded (ballM D 𝕫 t)) {Z X' : Set ℂ} (hZ : IsClosed Z) (hX'Z : X' ⊆ Z)
    {α : ℂ} (hα : α ∈ frontier (filledBall D 𝕫 t)) (hαZ : α ∉ Z) :
    ∃ a a' : ℂ, a ∉ filledBall D 𝕫 t ∧ a' ∈ interior (filledBall D 𝕫 t) ∧
      segment ℝ a a' ⊆ Zᶜ ∧ ∃ ρ > 0, ball α ρ \ filledBall D 𝕫 t ⊆
        connectedComponentIn (filledBall D 𝕫 t ∪ X')ᶜ a := by
  set K := filledBall D 𝕫 t
  obtain ⟨r₁, hr₁, hr₁Z⟩ := Metric.isOpen_iff.1 hZ.isOpen_compl α hαZ
  obtain ⟨δ', hδ', H⟩ := p412c_filledBall_locConnAt ht hL hbd hα r₁ hr₁
  set m := min δ' r₁
  have hm : 0 < m := lt_min hδ' hr₁
  have hαc : α ∈ closure Kᶜ := by
    have := frontier_subset_closure (s := Kᶜ) (by rwa [frontier_compl])
    exact this
  obtain ⟨a, ha, haK⟩ := mem_closure_iff.1 hαc _ isOpen_ball (mem_ball_self hm)
  obtain ⟨a', ha', ha'B⟩ := mem_closure_iff.1 (jb_frontier_subset_closure hbd hα) _ isOpen_ball
    (mem_ball_self hm)
  refine ⟨a, a', haK, jb_ballM_subset_interior ha'B, fun x hx => hr₁Z (ball_subset_ball
    (min_le_right _ _) ((convex_ball α m).segment_subset ha ha' hx)), δ', hδ', fun z hz => ?_⟩
  obtain ⟨C, hCs, hC, haC, hzC⟩ := H a ⟨ball_subset_ball (min_le_left _ _) ha, haK⟩ z hz
  refine hC.subset_connectedComponentIn haC (fun c hc => ?_) hzC
  rintro (h | h)
  · exact (hCs hc).2 h
  · exact hr₁Z (hCs hc).1 (hX'Z h)

/-- **GM L4.13′, separation step** (l. 2081–2082) for `K = 𝓑^•_t` -/
theorem p412e_sep {D : ContMetric} {𝕫 : ℂ} {t : ℝ} (ht : 0 < t) (hL : D.IsLength)
    (hbd : Bornology.IsBounded (ballM D 𝕫 t)) {X : Set ℂ}
    (hXc : IsConnected X) (hXb : Bornology.IsBounded X) {p q : ℂ}
    (hp : p ∈ frontier (filledBall D 𝕫 t)) (hq : q ∈ frontier (filledBall D 𝕫 t)) (hpq : p ≠ q)
    (hpX : p ∈ closure X) (hqX : q ∈ closure X)
    (hclX : closure X ∩ filledBall D 𝕫 t ⊆ {p, q}) :
    ∃ S ⊆ frontier (filledBall D 𝕫 t), IsPreconnected S ∧ p ∈ S ∧ q ∈ S ∧ ∃ v₀,
      v₀ ∉ closure X ∪ filledBall D 𝕫 t ∧
      Bornology.IsBounded (connectedComponentIn (closure X ∪ filledBall D 𝕫 t)ᶜ v₀) ∧
      S ⊆ closure (connectedComponentIn (closure X ∪ filledBall D 𝕫 t)ᶜ v₀) := by
  set K := filledBall D 𝕫 t with hKdef
  have hKcpt : IsCompact K := jb_isCompact_filledBall hbd
  have hKcl : IsClosed K := hKcpt.isClosed
  have hKc : IsConnected K := ⟨⟨𝕫, jo_mem_filledBall_self ht⟩, jp_isPreconnected_filledBall ht hL⟩
  have hKo : IsPreconnected Kᶜ := jb_isPreconnected_compl hbd
  have hint := p412c_filledBall_interior_isPreconnected ht hL hbd
  obtain ⟨Ψ, hΨc, hΨi, -, -, hΨS, -⟩ := gm_filledBall_conformal' ht hL hbd
  have hsub : sphere (0 : ℂ) 1 ⊆ closedBall 0 1 \ {0} := fun w hw =>
    ⟨sphere_subset_closedBall hw, fun h => by
      rw [mem_singleton_iff] at h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hw
      exact zero_ne_one hw⟩
  rw [← hΨS] at hp hq
  obtain ⟨A, B, A₀, B₀, hAc, hBc, hAB, hAiB, hA₀A, hB₀B, hAeq, hBeq, hpA₀, hqA₀, hpB₀, hqB₀,
    hA₀c, hB₀c, hpA, hqA, hpB, hqB⟩ := p412e_split (hΨc.mono hsub) (hΨi.mono hsub) hp hq hpq
  rw [hΨS] at hAB hp hq
  have hAK : A ⊆ frontier K := fun x hx => hAB ▸ Or.inl hx
  have hBK : B ⊆ frontier K := fun x hx => hAB ▸ Or.inr hx
  set X' := closure X
  have hX'cl : IsClosed X' := isClosed_closure
  have hX'c : IsCompact X' := Metric.isCompact_of_isClosed_isBounded hX'cl hXb.closure
  have hX'K : X' ∩ K ⊆ A ∩ B := hAiB.symm ▸ hclX
  have hABX : A ∩ B ⊆ X' := by
    rw [hAiB]; rintro x (rfl | rfl)
    · exact hpX
    · exact hqX
  -- interior points of the arcs avoid `cl X` and the other arc
  have hoff : ∀ {C C₀ E : Set ℂ}, C₀ ⊆ C → p ∉ C₀ → q ∉ C₀ → C ∩ E ⊆ {p, q} →
      ∀ α ∈ C₀, α ∈ frontier K → α ∉ X' ∪ E := by
    intro C C₀ E hC₀ hp₀ hq₀ hCE α hα hαK hαXE
    have hpq' : α ∈ ({p, q} : Set ℂ) := by
      rcases hαXE with h | h
      · exact hclX ⟨h, hKcl.frontier_subset hαK⟩
      · exact hCE ⟨hC₀ hα, h⟩
    rcases hpq' with rfl | rfl
    · exact hp₀ hα
    · exact hq₀ hα
  obtain ⟨α, hα⟩ : A₀.Nonempty := by
    by_contra h; rw [not_nonempty_iff_eq_empty] at h; rw [h, closure_empty] at hpA; exact hpA
  obtain ⟨β, hβ⟩ : B₀.Nonempty := by
    by_contra h; rw [not_nonempty_iff_eq_empty] at h; rw [h, closure_empty] at hpB; exact hpB
  have hαK : α ∈ frontier K := hAK (hA₀A hα)
  have hβK : β ∈ frontier K := hBK (hB₀B hβ)
  obtain ⟨a, a', haK, ha', haa', ρa, hρa, hVa⟩ := p412e_side ht hL hbd (hX'cl.union hBc.isClosed)
    subset_union_left hαK (hoff hA₀A hpA₀ hqA₀ hAiB.subset α hα hαK)
  obtain ⟨b, b', hbK, hb', hbb', ρb, hρb, hVb⟩ := p412e_side ht hL hbd (hX'cl.union hAc.isClosed)
    subset_union_left hβK (hoff hB₀B hpB₀ hqB₀ (by rw [inter_comm, hAiB]) β hβ hβK)
  obtain ⟨-, hbdd⟩ := Topo.Crosscut.theta_bounded hKcpt hKc hKo hint hX'c hXc.closure hAc hBc hAK
    hBK hAB.symm.subset hX'K hABX haK hbK ha' hb' haa' hbb'
  have hfrK : frontier K ⊆ closure Kᶜ := fun x hx => by
    have := frontier_subset_closure (s := Kᶜ) (by rwa [frontier_compl]); exact this
  have hLC : ∀ x ∈ frontier K, LocConnAt K x := fun x hx => p412c_filledBall_locConnAt ht hL hbd hx
  have hdisj : ∀ {C₀ C E : Set ℂ}, C₀ ⊆ C → p ∉ C₀ → q ∉ C₀ → C ∩ E ⊆ {p, q} → C ⊆ frontier K →
      Disjoint C₀ X' := fun hC₀ hp₀ hq₀ hCE hCK => disjoint_left.2 fun x hx hxX =>
    hoff hC₀ hp₀ hq₀ hCE x hx (hCK (hC₀ hx)) (Or.inl hxX)
  have hcomm : (closure X ∪ K)ᶜ = (K ∪ X')ᶜ := by rw [union_comm]
  rcases hbdd with hba | hbb
  · have hcol := p412e_collar hX'cl (fun x hx => hfrK (hAK (hA₀A hx)))
      (fun x hx => hLC x (hAK (hA₀A hx))) (hdisj hA₀A hpA₀ hqA₀ hAiB.subset hAK) hA₀c
      hα hρa hVa
    refine ⟨closure A₀, (closure_minimal (fun x hx => hAK (hA₀A hx)) isClosed_frontier),
      hA₀c.closure, hpA, hqA, a, ?_, by rwa [hcomm], by
        rw [hcomm]; exact closure_minimal hcol isClosed_closure⟩
    rintro (h | h)
    · exact (haa' (left_mem_segment ℝ a a')) (Or.inl h)
    · exact haK h
  · have hcol := p412e_collar hX'cl (fun x hx => hfrK (hBK (hB₀B hx)))
      (fun x hx => hLC x (hBK (hB₀B hx)))
      (hdisj hB₀B hpB₀ hqB₀ (by rw [inter_comm, hAiB]) hBK) hB₀c hβ hρb hVb
    refine ⟨closure B₀, (closure_minimal (fun x hx => hBK (hB₀B hx)) isClosed_frontier),
      hB₀c.closure, hpB, hqB, b, ?_, by rwa [hcomm], by
        rw [hcomm]; exact closure_minimal hcol isClosed_closure⟩
    rintro (h | h)
    · exact (hbb' (left_mem_segment ℝ b b')) (Or.inl h)
    · exact hbK h

end LQGMetric.GM
