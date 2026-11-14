/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistOneArmPaths at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistSiteFamily
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistChainOffset
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistSitePathInU

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem exists_pt_dist_one_arm_paths {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ξ : Ioi (0 : ℝ)) (Q ζ C : ℝ) (n k₀ : ℕ) (hk₀ : k₀ ≤ n)
    (F : ℕ → Finset ℂ) (V U : Set ℂ) (R T : ℝ) (t : ℕ → ℝ)
    (hR : 1 / 4 ≤ R) (hT : 0 < T) (ω : Ω)
    (hgood : ω ∈ ptDistAllScalesGood P W ξ Q ζ C n F V R T t)
    (hinside : ∀ k ≤ n, ∀ x ∈ F k, x ∈ V)
    (hcover : ∀ k ≤ n, ∀ z ∈ V, ∃ x ∈ F k,
      dist z x < ((2 : ℝ)⁻¹) ^ (k + 2))
    (z : ℂ) (hz : z ∈ V)
    (hcollar : ∀ k, k₀ ≤ k → ∀ x : ℂ,
      dist z x < ((2 : ℝ)⁻¹) ^ k / 4 →
      ball x (17 * ((2 : ℝ)⁻¹ ^ k)) ⊆ U) :
    ∃ (x : ℕ → ℂ) (p : ℕ → ℝ → ℂ),
      (∀ k ≤ n,
        dist z (x k) < ((2 : ℝ)⁻¹) ^ k / 4 ∧
        ω ∈ ptDistSiteGood P W ξ Q ζ C n k (x k) T ∧
        |phiMN W P 0 k (x k) ω - phiMN W P 0 k z ω| ≤ R * t k) ∧
      (∀ j ≤ n - k₀,
        AdmPath U (sphere (x (k₀ + j)) (((2 : ℝ)⁻¹ ^ (k₀ + j)) / 4))
          (sphere (x (k₀ + j)) (16 * ((2 : ℝ)⁻¹ ^ (k₀ + j))))
          (p (k₀ + j)) ∧
        lfppLen (ξ : ℝ) (fun y => phiMN W P 0 n y ω) (p (k₀ + j)) <
          ENNReal.ofReal (2 *
            (Real.exp ((ξ : ℝ) * phiMN W P 0 (k₀ + j) (x (k₀ + j)) ω) *
              (T * ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) *
                ((k₀ + j : ℕ) : ℝ)) * lambdaN ξ W P n))))) ∧
      lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω) U
        (p k₀ 0) (p n 0) ≤
        ∑ j ∈ Finset.range (n - k₀),
          (lfppLen (ξ : ℝ) (fun y => phiMN W P 0 n y ω) (p (k₀ + (j + 1))) +
            ENNReal.ofReal (T * (C *
              (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) *
                ((k₀ + (j + 1) : ℕ) : ℝ)) * lambdaN ξ W P n) *
              Real.exp ((ξ : ℝ) * phiMN W P 0 (k₀ + (j + 1))
                (x (k₀ + (j + 1))) ω)) +
            lfppLen (ξ : ℝ) (fun y => phiMN W P 0 n y ω) (p (k₀ + j))) := by
  obtain ⟨x, hx, hnear⟩ := exists_pt_dist_good_site_family P W ξ Q ζ C n F V R T t
    hR ω hgood hinside hcover z hz
  let f : ℂ → ℝ := fun y => phiMN W P 0 n y ω
  let L (k : ℕ) : ℝ := T * (C *
      (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n) *
      Real.exp ((ξ : ℝ) * phiMN W P 0 k (x k) ω)
  let N : ℕ := n - k₀
  have hsum : k₀ + N = n := by dsimp [N]; omega
  have hpaths (j : ℕ) : ∃ q : ℝ → ℂ, j ≤ N →
      AdmPath U (sphere (x (k₀ + j)) (((2 : ℝ)⁻¹ ^ (k₀ + j)) / 4))
        (sphere (x (k₀ + j)) (16 * ((2 : ℝ)⁻¹ ^ (k₀ + j)))) q ∧
      lfppLen (ξ : ℝ) f q < ENNReal.ofReal (2 *
        (Real.exp ((ξ : ℝ) * phiMN W P 0 (k₀ + j) (x (k₀ + j)) ω) *
          (T * ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) *
            ((k₀ + j : ℕ) : ℝ)) * lambdaN ξ W P n)))) := by
    by_cases hj : j ≤ N
    · have hk : k₀ + j ≤ n := by omega
      obtain ⟨q, hq, hlen⟩ :=
        pt_dist_site_crossing_path_in_U P W hW ξ Q ζ C n (k₀ + j)
          (x (k₀ + j)) U T hT ω (hx (k₀ + j) hk).2.1
          (hcollar (k₀ + j) (by omega) (x (k₀ + j)) (hx (k₀ + j) hk).1)
      exact ⟨q, fun _ => ⟨hq, hlen⟩⟩
    · exact ⟨fun _ => 0, fun h => False.elim (hj h)⟩
  let q (j : ℕ) : ℝ → ℂ := Classical.choose (hpaths j)
  let p (k : ℕ) : ℝ → ℂ := q (k - k₀)
  have hp (j : ℕ) (hj : j ≤ N) :
      AdmPath U (sphere (x (k₀ + j)) (((2 : ℝ)⁻¹ ^ (k₀ + j)) / 4))
        (sphere (x (k₀ + j)) (16 * ((2 : ℝ)⁻¹ ^ (k₀ + j))))
        (p (k₀ + j)) ∧
      lfppLen (ξ : ℝ) f (p (k₀ + j)) < ENNReal.ofReal (2 *
        (Real.exp ((ξ : ℝ) * phiMN W P 0 (k₀ + j) (x (k₀ + j)) ω) *
          (T * ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) *
            ((k₀ + j : ℕ) : ℝ)) * lambdaN ξ W P n)))) := by
    simpa only [p, Nat.add_sub_cancel_left] using
      (Classical.choose_spec (hpaths j) hj)
  have hn (j : ℕ) (hj : j < N) :
      dist (x (k₀ + (j + 1))) (x (k₀ + j)) ≤
        3 * ((2 : ℝ)⁻¹ ^ (k₀ + (j + 1))) / 4 := by
    simpa only [Nat.add_assoc] using hnear (k₀ + j) (by omega)
  have hl (j : ℕ) (hj : j < N) :
      Inputs.HasAroundLoop (ξ : ℝ) f (x (k₀ + (j + 1)))
        ((2 : ℝ)⁻¹ ^ (k₀ + (j + 1))) (by positivity)
        (ENNReal.ofReal (L (k₀ + (j + 1)))) :=
    (hx (k₀ + (j + 1)) (by omega)).2.1.2
  have hb (j : ℕ) (hj : j < N) :
      ball (x (k₀ + (j + 1)))
        (8 * ((2 : ℝ)⁻¹ ^ (k₀ + (j + 1)))) ⊆ U := by
    intro y hy
    apply hcollar (k₀ + (j + 1)) (by omega) (x (k₀ + (j + 1)))
      (hx (k₀ + (j + 1)) (by omega)).1
    have hr : 0 < ((2 : ℝ)⁻¹ ^ (k₀ + (j + 1))) := by positivity
    have hd : dist y (x (k₀ + (j + 1))) <
        8 * ((2 : ℝ)⁻¹ ^ (k₀ + (j + 1))) := mem_ball.mp hy
    exact mem_ball.mpr (by linarith)
  have hchain := pt_dist_selected_crossing_chain_offset (ξ := (ξ : ℝ))
    (f := f) (U := U) k₀ N x p
    (fun j => ENNReal.ofReal (L (k₀ + (j + 1))))
    (fun j hj => (hp j hj).1) hn hl hb
  refine ⟨x, p, hx, ?_, ?_⟩
  · exact hp
  · simpa only [N, hsum, L, f] using hchain

end SupercriticalLQGUniqueness.B2.DG20Pt
