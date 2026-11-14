/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RAllArc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RQuadrant
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRefXCost

 










set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Complex Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF

 


def LaneC1RDetour (D : ContMetric) (ρ : ℝ → ℂ) (a b : ℝ) (c : ℂ) (r : ℝ)
    (γ : ℝ → ℂ) : Prop :=
  ∃ (α : ℝ → ℂ) (t₀ t₁ : ℝ), ContinuousOn α (Icc (0 : ℝ) 1) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, r < dist (α t) c ∧ dist (α t) c < 2 * r) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, α t ∈ (rectAB 1 1).toSet) ∧
    D.len α 0 1 ≤ D.len ρ a b ∧
    t₀ ∈ Icc (0 : ℝ) 1 ∧ t₁ ∈ Icc (0 : ℝ) 1 ∧ t₀ ≤ t₁ ∧
    ((γ t₀ = α 0 ∧ ∀ t ∈ Icc (0 : ℝ) t₀, r ≤ dist (γ t) c) ∨
      (t₀ = 0 ∧ α 0 ∈ (rectAB 1 1).side₁)) ∧
    ((γ t₁ = α 1 ∧ ∀ t ∈ Icc t₁ (1 : ℝ), r ≤ dist (γ t) c) ∨
      (t₁ = 1 ∧ α 1 ∈ (rectAB 1 1).side₂))

 
def LaneC1RDetourHyp (D : ContMetric) (ρ : ℝ → ℂ) (a b : ℝ) (c : ℂ) (r : ℝ)
    (γ : ℝ → ℂ) : Prop :=
  a ≤ b ∧ ContinuousOn ρ (Icc a b) ∧ 0 < r ∧
    (∀ x ∈ Icc a b, r < dist (ρ x) c ∧ dist (ρ x) c < 2 * r) ∧
    LQGMetric.Disconnects (ρ '' Icc a b) (sphere c r) (sphere c (2 * r)) ∧
    ContinuousOn γ (Icc (0 : ℝ) 1) ∧ (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (rectAB 1 1).toSet) ∧
    γ 0 ∈ (rectAB 1 1).side₁ ∧ γ 1 ∈ (rectAB 1 1).side₂ ∧
    ∃ m ∈ Icc (0 : ℝ) 1, dist (γ m) c < r

theorem laneC1R_detour_of_quadrant {D : ContMetric} {ρ γ : ℝ → ℂ} {a b : ℝ} {c : ℂ} {r : ℝ}
    (h : LaneC1RDetourHyp D ρ a b c r γ) (hcR : c.re + 2 * r ≤ 1) (hcB : 2 * r ≤ c.im) :
    LaneC1RDetour D ρ a b c r γ := by
  obtain ⟨hab, hρ, hr, hρann, hsep, hγ, hγS, hγ0, hγ1, m, hm, hvisit⟩ := h
  exact laneC1R_quadrant_detour D hab hρ hr hρann hsep hcR hcB hγ hγS hγ0 hγ1 hm hvisit

 
theorem laneC1R_detour_refX {D : ContMetric} {ρ γ : ℝ → ℂ} {a b : ℝ} {c : ℂ} {r : ℝ}
    (hrefl : LaneC1RDetourHyp (laneCRefXMetric D) (fun t => laneCRefX (ρ t)) a b
        (laneCRefX c) r (fun t => laneCRefX (γ (1 - t))) →
      LaneC1RDetour (laneCRefXMetric D) (fun t => laneCRefX (ρ t)) a b
        (laneCRefX c) r (fun t => laneCRefX (γ (1 - t))))
    (h : LaneC1RDetourHyp D ρ a b c r γ) : LaneC1RDetour D ρ a b c r γ := by
  let φ := laneCRefX
  obtain ⟨hab, hρ, hr, hρann, hsep, hγ, hγS, hγ0, hγ1, m, hm, hvisit⟩ := h
  have hrev (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 1 - t ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hdφ : ∀ z : ℂ, dist (φ z) (φ c) = dist z c := fun z => laneC_refX_dist z c
  have hH : LaneC1RDetourHyp (laneCRefXMetric D) (fun t => φ (ρ t)) a b (φ c) r
      (fun t => φ (γ (1 - t))) := by
    refine ⟨hab, laneC_refX_continuous.comp_continuousOn hρ, hr, ?_, ?_,
      laneC_refX_continuous.comp_continuousOn (hγ.comp (by fun_prop) hrev),
      fun t ht => laneC_refX_square (hγS _ (hrev t ht)), ?_, ?_, 1 - m, hrev m hm, ?_⟩
    · intro x hx
      rw [hdφ]
      exact hρann x hx
    · have hh := laneC_disconnects_image_of_involution
        laneC_refX_continuous laneC_refX_involutive hsep
      rw [laneC_refX_sphere, laneC_refX_sphere] at hh
      simpa only [φ, image_image] using hh
    · simpa using laneC_refX_right_to_left hγ1
    · simpa using laneC_refX_left_to_right hγ0
    · simpa [hdφ] using hvisit
  obtain ⟨α', t₀', t₁', hα', hαann', hαS', hcost', ht₀', ht₁', hle', hstart', hend'⟩ :=
    hrefl hH
  let α : ℝ → ℂ := fun t => φ (α' (1 - t))
  have hdα : ∀ t, dist (α t) c = dist (α' (1 - t)) (φ c) := by
    intro t
    simpa only [α, φ, laneC_refX_involutive] using laneC_refX_dist (α' (1 - t)) (φ c)
  refine ⟨α, 1 - t₁', 1 - t₀', laneC_refX_continuous.comp_continuousOn
      (hα'.comp (by fun_prop) hrev), ?_, ?_, ?_, hrev _ ht₁', hrev _ ht₀', by linarith, ?_, ?_⟩
  · intro t ht
    rw [hdα]
    exact hαann' _ (hrev t ht)
  · intro t ht
    exact laneC_refX_square (hαS' _ (hrev t ht))
  · have h1 : (laneCRefXMetric D).len (fun t => α' (1 - t)) 0 1 = D.len α 0 1 := by
      simpa [α, φ] using laneC_refXMetric_len D (fun t => α' (1 - t)) 0 1
    have h2 : (laneCRefXMetric D).len (fun t => α' (1 - t)) 0 1 =
        (laneCRefXMetric D).len α' 0 1 := by
      unfold ContMetric.len
      simpa [Function.comp_def] using
        MetricGeometry.curveLength_reverse ((laneCRefXMetric D).pt ∘ α') (zero_le_one' ℝ)
    rw [← h1, h2]
    exact hcost'.trans (le_of_eq (laneC_refXMetric_len_reflected D ρ a b))
  · rcases hend' with ⟨hhit, hsafe⟩ | ⟨h1, hside⟩
    · left
      refine ⟨?_, fun t ht => ?_⟩
      · have := congrArg φ hhit
        simpa [α, φ, laneC_refX_involutive] using this
      · have hs : 1 - t ∈ Icc t₁' (1 : ℝ) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
        have := hsafe (1 - t) hs
        simpa [laneC_refX_dist] using this
    · right
      refine ⟨by rw [h1]; ring, ?_⟩
      simpa [α] using laneC_refX_right_to_left hside
  · rcases hstart' with ⟨hhit, hsafe⟩ | ⟨h0, hside⟩
    · left
      refine ⟨?_, fun t ht => ?_⟩
      · have := congrArg φ hhit
        simpa [α, φ, laneC_refX_involutive] using this
      · have hs : 1 - t ∈ Icc (0 : ℝ) t₀' := ⟨by linarith [ht.2], by linarith [ht.1]⟩
        have := hsafe (1 - t) hs
        simpa [laneC_refX_dist] using this
    · right
      refine ⟨by rw [h0]; ring, ?_⟩
      simpa [α] using laneC_refX_left_to_right hside

 
theorem laneC1R_detour_refY {D : ContMetric} {ρ γ : ℝ → ℂ} {a b : ℝ} {c : ℂ} {r : ℝ}
    (hrefl : LaneC1RDetourHyp (laneCRefYMetric D) (fun t => laneCRefY (ρ t)) a b
        (laneCRefY c) r (fun t => laneCRefY (γ t)) →
      LaneC1RDetour (laneCRefYMetric D) (fun t => laneCRefY (ρ t)) a b
        (laneCRefY c) r (fun t => laneCRefY (γ t)))
    (h : LaneC1RDetourHyp D ρ a b c r γ) : LaneC1RDetour D ρ a b c r γ := by
  let φ := laneCRefY
  obtain ⟨hab, hρ, hr, hρann, hsep, hγ, hγS, hγ0, hγ1, m, hm, hvisit⟩ := h
  have hdφ : ∀ z : ℂ, dist (φ z) (φ c) = dist z c := fun z => laneC_refY_dist z c
  have hH : LaneC1RDetourHyp (laneCRefYMetric D) (fun t => φ (ρ t)) a b (φ c) r
      (fun t => φ (γ t)) := by
    refine ⟨hab, laneC_refY_continuous.comp_continuousOn hρ, hr, ?_, ?_,
      laneC_refY_continuous.comp_continuousOn hγ,
      fun t ht => laneC_refY_square (hγS t ht), laneC_refY_left hγ0, laneC_refY_right hγ1,
      m, hm, by simpa [hdφ] using hvisit⟩
    · intro x hx
      rw [hdφ]
      exact hρann x hx
    · have hh := laneC_disconnects_image_of_involution
        laneC_refY_continuous laneC_refY_involutive hsep
      rw [laneC_refY_sphere, laneC_refY_sphere] at hh
      simpa only [φ, image_image] using hh
  obtain ⟨α', t₀, t₁, hα', hαann', hαS', hcost', ht₀, ht₁, hle, hstart', hend'⟩ := hrefl hH
  let α : ℝ → ℂ := fun t => φ (α' t)
  have hdα : ∀ t, dist (α t) c = dist (α' t) (φ c) := by
    intro t
    simpa only [α, φ, laneC_refY_involutive] using laneC_refY_dist (α' t) (φ c)
  refine ⟨α, t₀, t₁, laneC_refY_continuous.comp_continuousOn hα', ?_, ?_, ?_, ht₀, ht₁, hle,
    ?_, ?_⟩
  · intro t ht
    rw [hdα]
    exact hαann' t ht
  · intro t ht
    exact laneC_refY_square (hαS' t ht)
  · have h1 : (laneCRefYMetric D).len α' 0 1 = D.len α 0 1 := by
      simpa [α, φ] using laneC_refYMetric_len D α' 0 1
    rw [← h1]
    exact hcost'.trans (le_of_eq (laneC_refYMetric_len_reflected D ρ a b))
  · rcases hstart' with ⟨hhit, hsafe⟩ | ⟨h0, hside⟩
    · left
      refine ⟨?_, fun t ht => ?_⟩
      · have := congrArg φ hhit
        simpa [α, φ, laneC_refY_involutive] using this
      · simpa [laneC_refY_dist] using hsafe t ht
    · exact Or.inr ⟨h0, laneC_refY_left hside⟩
  · rcases hend' with ⟨hhit, hsafe⟩ | ⟨h1, hside⟩
    · left
      refine ⟨?_, fun t ht => ?_⟩
      · have := congrArg φ hhit
        simpa [α, φ, laneC_refY_involutive] using this
      · simpa [laneC_refY_dist] using hsafe t ht
    · exact Or.inr ⟨h1, laneC_refY_right hside⟩

 
theorem laneC1R_detour_of_bottom_free {D : ContMetric} {ρ γ : ℝ → ℂ} {a b : ℝ} {c : ℂ}
    {r : ℝ} (hsmall : 4 * r ≤ 1) (hcB : 2 * r ≤ c.im) (h : LaneC1RDetourHyp D ρ a b c r γ) :
    LaneC1RDetour D ρ a b c r γ := by
  by_cases hcR : c.re + 2 * r ≤ 1
  · exact laneC1R_detour_of_quadrant h hcR hcB
  · apply laneC1R_detour_refX _ h
    intro hH
    apply laneC1R_detour_of_quadrant hH
    · rw [laneC_refX_re]; linarith
    · rw [laneC_refX_im]; exact hcB

 
theorem laneC1R_detour_all {D : ContMetric} {ρ γ : ℝ → ℂ} {a b : ℝ} {c : ℂ} {r : ℝ}
    (hsmall : 4 * r ≤ 1) (h : LaneC1RDetourHyp D ρ a b c r γ) :
    LaneC1RDetour D ρ a b c r γ := by
  by_cases hcB : 2 * r ≤ c.im
  · exact laneC1R_detour_of_bottom_free hsmall hcB h
  · apply laneC1R_detour_refY _ h
    intro hH
    apply laneC1R_detour_of_bottom_free hsmall _ hH
    rw [laneC_refY_im]
    linarith

end SupercriticalLQGUniqueness.B2.DG20Conc
