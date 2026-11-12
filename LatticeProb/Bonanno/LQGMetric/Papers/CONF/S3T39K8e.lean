/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K8e at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K8d

/-!
# CONF Theorem 3.9, packet J6d, node O2: hit events of the frontier and of the centre set

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1586. For `K` closed (bounded, Jordan frontier, `J ⊆ ∂K`):

* `k8BallSub_iff`, **`k8FrHit_iff`**: the hit events of `∂K` through hit events of `K`;
* `k8W_uniform`: chains to `{‖·‖ > N}` extend to `{‖·‖ > n}` once `K ∪ B̄_a(c) ⊆ B̄_{N-1}(0)`;
* `k8DiscR_limit`: disconnection with a fixed radius passes to limits of the balls;
* **`k8CtrHit_iff`**: the hit events of the centre set `t39jCtrSet K J r` (S3T39J1) through the
  countable condition `k8CtrHit` (rational approximations of the centre, `k8Disc`).

Own elementary arguments (CONF gives none).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology

namespace LQGMetric.CONF

/-- `ball p ρ ⊆ K`, through hit events (for closed `K`) -/
def k8BallSub (K : Set ℂ) (p : ℂ) (ρ : ℝ) : Prop :=
  ∀ q : ℚ × ℚ, k8Q q ∈ ball p ρ → ∀ i : ℕ, (K ∩ ball (k8Q q) (1 / ((i : ℝ) + 1))).Nonempty

theorem k8BallSub_iff {K : Set ℂ} (hK : IsClosed K) (p : ℂ) (ρ : ℝ) :
    k8BallSub K p ρ ↔ ball p ρ ⊆ K := by
  constructor
  · intro h w hw
    rw [← hK.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδb⟩ := Metric.isOpen_iff.1 isOpen_ball w hw
    obtain ⟨q, hq⟩ := k8_exists_rat w (lt_min hδ (half_pos hε))
    have hq' : dist (k8Q q) w < min δ (ε / 2) := hq
    obtain ⟨i, hi⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨z, hzK, hz⟩ := h q (hδb (by rw [mem_ball]; exact hq'.trans_le (min_le_left _ _))) i
    refine ⟨z, hzK, ?_⟩
    rw [mem_ball] at hz
    have := hq'.trans_le (min_le_right _ _)
    linarith [dist_triangle w (k8Q q) z, dist_comm (k8Q q) w, dist_comm z (k8Q q)]
  · intro h q hq i
    exact ⟨k8Q q, h hq, mem_ball_self (by positivity)⟩

/-- `∂K` meets `U`, through hit events of `K` -/
def k8FrHit (K U : Set ℂ) : Prop :=
  ∃ p : ℚ × ℚ, ∃ ρ : ℚ, (0 : ℝ) < ρ ∧ ball (k8Q p) ρ ⊆ U ∧ (K ∩ ball (k8Q p) ρ).Nonempty ∧
    ¬ k8BallSub K (k8Q p) ρ

theorem k8FrHit_iff {K : Set ℂ} (hK : IsClosed K) {U : Set ℂ} (hU : IsOpen U) :
    k8FrHit K U ↔ (frontier K ∩ U).Nonempty := by
  constructor
  · rintro ⟨p, ρ, -, hpU, hKp, hsub⟩
    rw [k8BallSub_iff hK] at hsub
    obtain ⟨v, hvb, hvK⟩ := not_subset.1 hsub
    by_contra hfr
    have hdisj : ball (k8Q p) ρ ⊆ interior K ∪ (closure K)ᶜ := by
      intro w hw
      by_cases hwK : w ∈ closure K
      · left
        by_contra hwi
        exact hfr ⟨w, ⟨hwK, hwi⟩, hpU hw⟩
      · exact Or.inr hwK
    rcases (convex_ball (k8Q p) (ρ : ℝ)).isPreconnected.subset_or_subset isOpen_interior
      isClosed_closure.isOpen_compl
      ((disjoint_compl_right (a := closure K)).mono_left interior_subset_closure) hdisj with h | h
    · exact hvK (interior_subset (h hvb))
    · obtain ⟨w, hwK, hwb⟩ := hKp
      exact h hwb (subset_closure hwK)
  · rintro ⟨x, hxf, hxU⟩
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hxU
    obtain ⟨q, hq⟩ := k8_exists_rat x (show 0 < ε / 4 by linarith)
    obtain ⟨ρ, hρ₁, hρ₂⟩ := exists_rat_btwn (show ε / 4 < ε / 2 by linarith)
    have hq' : dist (k8Q q) x < ε / 4 := hq
    have hxb : x ∈ ball (k8Q q) ρ := by rw [mem_ball, dist_comm]; linarith
    refine ⟨q, ρ, by linarith, fun w hw => hεU ?_, ⟨x, hK.frontier_subset hxf, hxb⟩, ?_⟩
    · rw [mem_ball] at hw ⊢; linarith [dist_triangle w (k8Q q) x]
    · rw [k8BallSub_iff hK]
      intro hsub
      exact hxf.2 (interior_maximal hsub isOpen_ball hxb)

/-- **chains to `{‖·‖ > N}` extend to `{‖·‖ > n}`** -/
theorem k8W_uniform {K : Set ℂ} (hK : IsClosed K) {c : ℂ} {a : ℝ} {N : ℕ} (hN : (1 : ℝ) ≤ N)
    (hKN : ∀ z ∈ K, ‖z‖ ≤ (N : ℝ) - 1) (hcN : ‖c‖ + a ≤ (N : ℝ) - 1) {q : ℂ}
    (h : k8W K c a N q) (n : ℕ) : k8W K c a n q := by
  obtain ⟨l, hl, y, hy, hG⟩ := h
  set f : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) with hfdef
  have hf : Continuous f := by fun_prop
  set T := f '' (Ioi ((N : ℝ) - 1) ×ˢ univ)
  have hT : IsPreconnected T :=
    (isPreconnected_Ioi.prod isPreconnected_univ).image _ hf.continuousOn
  have hnorm : ∀ p : ℝ × ℝ, 0 ≤ p.1 → ‖f p‖ = p.1 := by
    intro p hp
    rw [hfdef]
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hp]
  have hyT : y ∈ T :=
    ⟨(‖y‖, Complex.arg y), ⟨show (N : ℝ) - 1 < ‖y‖ by linarith, trivial⟩,
      Complex.norm_mul_exp_arg_mul_I y⟩
  set y₂ : ℂ := (((n : ℝ) + N + 1 : ℝ) : ℂ)
  have hy₂T : y₂ ∈ T := ⟨((n : ℝ) + N + 1, 0),
    ⟨show (N : ℝ) - 1 < (n : ℝ) + N + 1 by have := n.cast_nonneg (α := ℝ); linarith, trivial⟩, by simp [hfdef, y₂]⟩
  have hcov : ∀ z ∈ T, ∃ b, k8Good K c a b ∧ z ∈ k8Ball b := by
    rintro z ⟨p, ⟨hp1, -⟩, rfl⟩
    have hp1' : (N : ℝ) - 1 < p.1 := hp1
    have hz := hnorm p (by linarith)
    have hzK : f p ∉ K := fun h' => by have := hKN _ h'; linarith
    have hzc : a < dist (f p) c := by
      rw [dist_eq_norm]; linarith [norm_sub_norm_le (f p) c]
    obtain ⟨b, hb, hzb, -⟩ := k8_exists_good hK hzK hzc one_pos
    exact ⟨b, hb, hzb⟩
  obtain ⟨l₂, hl₂, hG₂⟩ := k8_preconn hT (k8Good K c a) hcov hyT hy₂T
  obtain ⟨l'', hl'', hG''⟩ := k8G_trans hG hG₂
  refine ⟨l'', fun b hb => (hl'' b hb).elim (hl b) (hl₂ b), y₂, ?_, hG''⟩
  have : ‖y₂‖ = (n : ℝ) + N + 1 := by
    simp only [y₂, Complex.norm_real, Real.norm_eq_abs]; rw [abs_of_nonneg (by positivity)]
  rw [this]; linarith

/-- **disconnection with a fixed radius passes to limits of the balls** -/
theorem k8DiscR_limit {K J : Set ℂ} {R : ℝ} {c : ℕ → ℂ} {a : ℕ → ℝ} {c₀ : ℂ} {a₀ : ℝ}
    (hc : Tendsto c atTop (𝓝 c₀)) (ha : Tendsto a atTop (𝓝 a₀))
    (h : ∀ j, k8DiscR K (closedBall (c j) (a j)) J R) : k8DiscR K (closedBall c₀ a₀) J R := by
  intro y x γ hy hx hγK
  by_contra hne
  have hcpt : IsCompact (range γ) := isCompact_range γ.continuous
  obtain ⟨p₀, hp₀, hmin⟩ := hcpt.exists_isMinOn (range_nonempty γ)
    (continuous_id.dist continuous_const).continuousOn
  have hp₀c : a₀ < dist p₀ c₀ := by
    by_contra hle
    exact hne ⟨p₀, hp₀, by rw [mem_closedBall]; exact not_lt.1 hle⟩
  set η := dist p₀ c₀ - a₀
  have hη : 0 < η := by linarith
  obtain ⟨j₁, hj₁⟩ := (Metric.tendsto_atTop.1 hc) (η / 2) (by linarith)
  obtain ⟨j₂, hj₂⟩ := (Metric.tendsto_atTop.1 ha) (η / 2) (by linarith)
  obtain ⟨p, hp, hpc⟩ := h (max j₁ j₂) y x γ hy hx hγK
  have h1 := hj₁ (max j₁ j₂) (le_max_left _ _)
  have h2 := hj₂ (max j₁ j₂) (le_max_right _ _)
  rw [Real.dist_eq, abs_lt] at h2
  have h3 : dist p₀ c₀ ≤ dist p c₀ := hmin hp
  rw [mem_closedBall] at hpc
  linarith [dist_triangle p (c (max j₁ j₂)) c₀]

end LQGMetric.CONF
