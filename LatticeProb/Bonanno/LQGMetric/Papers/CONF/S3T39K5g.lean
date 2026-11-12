/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K5g at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K5b
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K5f

/-!
# CONF Theorem 3.9, packet J6d: the saturated set of the arc hit events

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1559–1561. The hit event `{I^{(s)} ∩ U ≠ ∅}` of an arc `I^{(s)} = t39gArc D_h z₀ s (arcs ∂𝓑^•_τ)`
is written, on a hull piece with `𝓑^•_s ⊆ A`, as `{(h − h_r(z), Z) ∈ B}` with `Z` the pair of hit
patterns of `𝓑^•_s`, `𝓑^•_τ` (S3T39K5) and `B = t39k5B …` (the radii are existentially
quantified, so they need not be recovered measurably). `B` is saturated for the internal metric
on `A` (`t39k5_B_sat`, the `hsat` input of `t39k5_piece_sat`).

* `t39k5Kset`, `t39k5_Kset_pat`: a closed set is recovered from its hit pattern;
* `t39k5B`, **`t39k5_B_sat`**;
* `t39k5_radius_eq` (a bounded filled ball of positive radius determines the radius: its frontier
  lies on the sphere, `jp_frontier_subset_sphere`), **`t39k5_mem_B_iff`**: for `D_g = C·D_h` and
  `𝓑^•_s ⊆ A`, `(g, Z) ∈ B` iff `I^{(s)}` meets `U` (scale invariance `t39k5_gArc_smul`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter TopologicalSpace

namespace LQGMetric.CONF

open Blueprint LocalEvent GM

/-- the closed set with hit pattern `p` -/
def t39k5Kset (p : ℕ → Bool) : Set ℂ :=
  {x | ∀ j, x ∈ ball (t39jBc j) (2 * t39jBr j) → p j = true}

/-- a closed set is recovered from its hit pattern -/
theorem t39k5_Kset_pat {K : Set ℂ} (hK : IsClosed K) : t39k5Kset (t39k5Pat K) = K := by
  ext x
  constructor
  · intro hx
    by_contra hxK
    obtain ⟨j, hxj, hjU⟩ := t39k5_ball_basis hK.isOpen_compl hxK
    have := hx j hxj
    simp only [t39k5Pat, decide_eq_true_eq] at this
    obtain ⟨y, hyK, hyj⟩ := this
    exact hjU hyj hyK
  · intro hx j hxj
    simp only [t39k5Pat, decide_eq_true_eq]
    exact ⟨x, hx, hxj⟩

/-- a bounded filled ball of positive radius has nonempty frontier -/
theorem t39k5_frontier_nonempty {d : ContMetric} {z₀ : ℂ} {σ : ℝ} (hσ : 0 < σ)
    (hKb : Bornology.IsBounded (filledBall d z₀ σ)) : (frontier (filledBall d z₀ σ)).Nonempty := by
  rw [nonempty_frontier_iff]
  refine ⟨⟨z₀, jo_mem_filledBall_self hσ⟩, fun he => ?_⟩
  rw [he] at hKb
  exact NormedSpace.unbounded_univ ℝ ℂ hKb

theorem t39k5_ballM_subset_filledBall (d : ContMetric) (z₀ : ℂ) (σ : ℝ) :
    ballM d z₀ σ ⊆ filledBall d z₀ σ := fun _ hx => Or.inl (subset_closure hx)

/-- a bounded filled ball of positive radius determines the radius -/
theorem t39k5_radius_eq {d : ContMetric} {z₀ : ℂ} {σ₁ σ₂ : ℝ} (h1 : 0 < σ₁)
    (hKb : Bornology.IsBounded (filledBall d z₀ σ₁))
    (he : filledBall d z₀ σ₁ = filledBall d z₀ σ₂) : σ₁ = σ₂ := by
  obtain ⟨x, hx⟩ := t39k5_frontier_nonempty h1 hKb
  have hx2 : x ∈ frontier (filledBall d z₀ σ₂) := he ▸ hx
  have hKb2 : Bornology.IsBounded (filledBall d z₀ σ₂) := he ▸ hKb
  have e1 : d.1 (z₀, x) = σ₁ :=
    jp_frontier_subset_sphere (hKb.subset (t39k5_ballM_subset_filledBall d z₀ σ₁)) hx
  have e2 : d.1 (z₀, x) = σ₂ :=
    jp_frontier_subset_sphere (hKb2.subset (t39k5_ballM_subset_filledBall d z₀ σ₂)) hx2
  linarith

end LQGMetric.CONF
