/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L214Beurling at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWBeurlingMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 2.14, node R3: the Beurling step

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), proof of Lemma 2.14,
confluence-final.tex 864–867: a Brownian motion from `φ(w_I)` exits `φ(H_I)` in `φ(J_I⁻)` with
probability `≥ a`, while by the Beurling estimate it leaves `B_{R d}(φ(w_I))`, `d = dist(φ(w_I), ∂U)`,
before hitting `∂U` with probability `≲ R^{-1/2}`; hence (for `R` large) the component of
`φ(H_I) ∩ B_{Rd}(φ(w_I))` containing `φ(w_I)` reaches `φ(J_I⁻)`.

Analytic form (`l214_beurling_reach`): let `G` be open, `x ∈ G`, `h` harmonic on `G` with values
in `[0,1]`, tending to `0` at every frontier point of `G` in `B_ρ(x)` outside a target set `T`.
If a connected `K` disjoint from `G` meets `B̄_d(x)` and leaves `B_ρ(x)`, and
`h(x) > C (d/ρ)^{1/2}` (`C` the Beurling constant), then the closure of the component `V` of
`G ∩ B_ρ(x)` containing `x` meets `T ∩ B_ρ(x)`.

Source: the Beurling estimate is QuantumZipper's `beurlingHarmStmt_holds` (analytic form,
harmonic-measure version of Beurling's projection theorem; Garnett–Marshall, *Harmonic Measure*,
Ch. III §9). The contrapositive packaging is an own elementary step.
-/

namespace LQGMetric
namespace CONF

open Set Metric Filter
open scoped Topology

/-- **CONF Lemma 2.14, R3** (C:864–867): the Beurling step in analytic form. -/
theorem l214_beurling_reach : ∃ C : ℝ, 0 ≤ C ∧ ∀ (G K T : Set ℂ) (x : ℂ) (d ρ : ℝ) (h : ℂ → ℝ),
    IsOpen G → x ∈ G → 0 < d → d ≤ ρ → IsConnected K → Disjoint K G →
    (K ∩ closedBall x d).Nonempty → (K \ ball x ρ).Nonempty →
    InnerProductSpace.HarmonicOnNhd h G → (∀ y ∈ G, 0 ≤ h y ∧ h y ≤ 1) →
    (∀ x₀ ∈ frontier G ∩ ball x ρ, x₀ ∉ T → Tendsto h (𝓝[G] x₀) (𝓝 0)) →
    C * (d / ρ) ^ (1 / 2 : ℝ) < h x →
    (closure (connectedComponentIn (G ∩ ball x ρ) x) ∩ T ∩ ball x ρ).Nonempty := by
  obtain ⟨C, hC0, hC⟩ := QuantumZipper.Thm18Asm.LWFar.beurlingHarmStmt_holds
  refine ⟨C, hC0, ?_⟩
  intro G K T x d ρ h hG hx hd hdρ hK hKG hKd hKρ hharm hbnd hdecay hlt
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  set D := G ∩ ball x ρ with hD
  have hρ : 0 < ρ := hd.trans_le hdρ
  have hDD : D ∩ ball x ρ = D := by rw [hD, inter_assoc, inter_self]
  set V := connectedComponentIn D x with hV
  have hVG : V ⊆ G := (connectedComponentIn_subset _ _).trans inter_subset_left
  have hle := hC D K x d ρ h (hG.inter isOpen_ball) ⟨hx, mem_ball_self hρ⟩ hd hdρ hK
    (hKG.mono_right inter_subset_left) hKd hKρ
    (by rw [hDD]; exact fun y hy => hharm y (hVG hy))
    (by rw [hDD]; exact fun y hy => hbnd y (hVG hy))
    (by
      rw [hDD]
      intro x₀ hx₀ ε hε
      have hx₀G : x₀ ∈ frontier G := by
        have h1 := frontier_inter_subset G (ball x ρ) hx₀.1
        rcases h1 with h1 | h1
        · exact h1.1
        · exact absurd hx₀.2 (by
            have := h1.2; rw [isOpen_ball.frontier_eq] at this; exact this.2)
      by_cases hT : x₀ ∈ T
      · -- `x₀ ∉ closure V`, so a small ball around `x₀` misses `V`
        have hx₀V : x₀ ∉ closure V := by
          intro hcl
          have : x₀ ∈ closure V ∩ T ∩ ball x ρ := ⟨⟨hcl, hT⟩, hx₀.2⟩
          rw [hne] at this; exact this
        obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.1
          ((isClosed_closure.isOpen_compl).mem_nhds hx₀V)
        refine ⟨δ, hδ, fun y hy hyd => ?_⟩
        exact absurd (subset_closure hy) (hδV (mem_ball.2 hyd))
      · have ht := hdecay x₀ ⟨hx₀G, hx₀.2⟩ hT
        obtain ⟨δ, hδ, hδh⟩ := Metric.tendsto_nhdsWithin_nhds.1 ht ε hε
        refine ⟨δ, hδ, fun y hy hyd => ?_⟩
        have := hδh (hVG hy) hyd
        rw [Real.dist_eq, sub_zero] at this
        exact (le_abs_self _).trans this.le)
  linarith

end CONF
end LQGMetric
