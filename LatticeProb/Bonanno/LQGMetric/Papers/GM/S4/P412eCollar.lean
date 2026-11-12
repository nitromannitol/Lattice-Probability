/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412eCollar at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412cLC

/-!
# The outer collar of an arc of `∂K` lies in one component (for GM L4.13′, l. 2081–2082)

GM L4.13 (l. 2081–2082): "one of the connected components `V` of `ℂ ∖ (𝓑 ∪ X)` is bounded and
contains an endpoint of `I` … also `P(s) ∈ ∂V`". The formal route: `theta_bounded` gives a
bounded component `V` containing a point `a` just outside an arc `A₀ ⊆ ∂K` that avoids `cl X`;
`p412e_collar` shows that then every point of `A₀` is in `cl V` (the points of `ℂ ∖ K` near
`A₀` all lie in `V`), using (LC) along `A₀` and the connectedness of `A₀`. Own elementary
argument (DV-L413-sep proposed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric

namespace LQGMetric.GM

/-- **Collar lemma**: if `ℂ ∖ K` is locally connected along a preconnected `A₀ ⊆ cl(ℂ ∖ K)`
disjoint from the closed set `X'`, and the points of `ℂ ∖ K` near one `α₀ ∈ A₀` lie in the
component `V` of `ℂ ∖ (K ∪ X')` of `a`, then `A₀ ⊆ cl V` -/
theorem p412e_collar {K X' A₀ : Set ℂ} (hX' : IsClosed X') (hA₀K : A₀ ⊆ closure Kᶜ)
    (hLC : ∀ α ∈ A₀, LocConnAt K α) (hA₀X : Disjoint A₀ X') (hA₀c : IsPreconnected A₀)
    {a α₀ : ℂ} (hα₀ : α₀ ∈ A₀) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (h₀ : ball α₀ ρ₀ \ K ⊆ connectedComponentIn (K ∪ X')ᶜ a) :
    A₀ ⊆ closure (connectedComponentIn (K ∪ X')ᶜ a) := by
  set V := connectedComponentIn (K ∪ X')ᶜ a with hVdef
  -- points of `ℂ ∖ K` near `β ∈ cl(ℂ∖K)`
  have hnear : ∀ β ∈ closure Kᶜ, ∀ r > 0, ∃ z, z ∈ ball β r \ K := fun β hβ r hr => by
    obtain ⟨z, hz, hzK⟩ := mem_closure_iff.1 hβ _ isOpen_ball (mem_ball_self hr)
    exact ⟨z, hz, hzK⟩
  -- local structure at `α ∈ A₀`
  have hloc : ∀ α ∈ A₀, ∃ δ > 0, ∀ z ∈ ball α δ \ K, ∀ w ∈ ball α δ \ K,
      w ∈ connectedComponentIn (K ∪ X')ᶜ z := by
    intro α hα
    have hαX : α ∈ X'ᶜ := fun h => disjoint_left.1 hA₀X hα h
    obtain ⟨δ₁, hδ₁, hδ₁X⟩ := Metric.isOpen_iff.1 hX'.isOpen_compl α hαX
    obtain ⟨δ', hδ', H⟩ := hLC α hα δ₁ hδ₁
    refine ⟨δ', hδ', fun z hz w hw => ?_⟩
    obtain ⟨C, hCs, hC, hzC, hwC⟩ := H z hz w hw
    refine hC.subset_connectedComponentIn hzC (fun c hc => ?_) hwC
    have hc' := hCs hc
    rintro (h | h)
    · exact hc'.2 h
    · exact hδ₁X hc'.1 h
  -- the key equivalence
  have hiff : ∀ α ∈ A₀, ∀ δ > 0, (∀ z ∈ ball α δ \ K, ∀ w ∈ ball α δ \ K,
      w ∈ connectedComponentIn (K ∪ X')ᶜ z) → ∀ z₀ ∈ ball α δ \ K, ∀ β ∈ closure Kᶜ, ∀ r > 0,
      ball β r ⊆ ball α δ → ((∃ ρ > 0, ball β ρ \ K ⊆ V) ↔ z₀ ∈ V) := by
    intro α _ δ _ Hδ z₀ hz₀ β hβ r hr hsub
    constructor
    · rintro ⟨ρ, hρ, hV⟩
      obtain ⟨z₁, hz₁⟩ := hnear β hβ (min ρ r) (lt_min hρ hr)
      have hz₁V : z₁ ∈ V := hV ⟨ball_subset_ball (min_le_left _ _) hz₁.1, hz₁.2⟩
      have hz₁' : z₁ ∈ ball α δ \ K := ⟨hsub (ball_subset_ball (min_le_right _ _) hz₁.1), hz₁.2⟩
      have := Hδ z₁ hz₁' z₀ hz₀
      rw [hVdef, connectedComponentIn_eq hz₁V]; exact this
    · intro hz₀V
      refine ⟨r, hr, fun z hz => ?_⟩
      have := Hδ z₀ hz₀ z ⟨hsub hz.1, hz.2⟩
      rw [hVdef, connectedComponentIn_eq hz₀V]; exact this
  classical
  let f : ℂ → Bool := fun α => decide (∃ ρ > 0, ball α ρ \ K ⊆ V)
  have hf : ContinuousOn f A₀ := by
    intro α hα
    obtain ⟨δ, hδ, Hδ⟩ := hloc α hα
    refine (continuousWithinAt_const (b := f α)).congr_of_eventuallyEq ?_ rfl
    filter_upwards [inter_mem_nhdsWithin A₀ (ball_mem_nhds α (half_pos hδ)), self_mem_nhdsWithin]
      with β hβ hβA
    obtain ⟨z₀, hz₀⟩ := hnear β (hA₀K hβA) (δ / 2) (half_pos hδ)
    have hz₀' : z₀ ∈ ball α δ \ K := ⟨by
      have h1 := mem_ball.1 hz₀.1; have h2 := mem_ball.1 hβ.2
      rw [mem_ball]; linarith [dist_triangle z₀ β α], hz₀.2⟩
    have hsubβ : ball β (δ / 2) ⊆ ball α δ := by
      intro w hw
      have h1 := mem_ball.1 hw; have h2 := mem_ball.1 hβ.2
      rw [mem_ball]; linarith [dist_triangle w β α]
    have e1 := hiff α hα δ hδ Hδ z₀ hz₀' β (hA₀K hβA) (δ / 2) (half_pos hδ) hsubβ
    have e2 := hiff α hα δ hδ Hδ z₀ hz₀' α (hA₀K hα) δ hδ subset_rfl
    simp only [f, decide_eq_decide]
    exact e1.trans e2.symm
  have hconst : ∀ α ∈ A₀, f α = f α₀ := fun α hα => hA₀c.constant hf hα hα₀
  have hf₀ : f α₀ = true := by simp only [f, decide_eq_true_eq]; exact ⟨ρ₀, hρ₀, h₀⟩
  intro α hα
  have hfa : f α = true := (hconst α hα).trans hf₀
  simp only [f, decide_eq_true_eq] at hfa
  obtain ⟨ρ, hρ, hV⟩ := hfa
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨z, hz⟩ := hnear α (hA₀K hα) (min ε ρ) (lt_min hε hρ)
  refine ⟨z, hV ⟨ball_subset_ball (min_le_right _ _) hz.1, hz.2⟩, ?_⟩
  rw [dist_comm]
  exact (mem_ball.1 hz.1).trans_le (min_le_left _ _)

end LQGMetric.GM
