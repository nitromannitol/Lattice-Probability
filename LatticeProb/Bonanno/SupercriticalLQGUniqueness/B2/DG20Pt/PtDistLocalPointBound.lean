/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLocalPointBound at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLocalEventBound
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistPointBudget

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_local_point_field_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ξ : Ioi (0 : ℝ)) (Q ζ C Clam : ℝ) (n k₀ : ℕ) (hk₀ : k₀ ≤ n)
    (F : ℕ → Finset ℂ) (V U : Set ℂ) (R T : ℝ)
    (hR : 1 ≤ R) (hT : 3 < T) (hζ : 0 ≤ ζ) (hC : 0 ≤ C)
    (hClam : 0 < Clam)
    (hlamLower : Clam⁻¹ * (2 : ℝ) ^
      (-(1 - (ξ : ℝ) * Q + ζ) * (n : ℝ)) ≤ lambdaN ξ W P n)
    (ω : Ω)
    (hgood : ω ∈ ptDistAllScalesGood P W ξ Q ζ C n F V R T
      (fun k => (Real.log T + ζ * (k : ℝ)) / (R * (ξ : ℝ))))
    (hinside : ∀ k ≤ n, ∀ x ∈ F k, x ∈ V)
    (hcover : ∀ k ≤ n, ∀ v ∈ V, ∃ x ∈ F k,
      dist v x < ((2 : ℝ)⁻¹) ^ (k + 2))
    (z w : ℂ) (hz : z ∈ V) (hw : w ∈ V)
    (hzw : dist z w ≤ 2 * ((2 : ℝ)⁻¹ ^ k₀))
    (hcollarZ : ∀ k, k₀ ≤ k → ∀ x : ℂ,
      dist z x < ((2 : ℝ)⁻¹) ^ k / 4 →
      ball x (17 * ((2 : ℝ)⁻¹ ^ k)) ⊆ U)
    (hcollarW : ∀ k, k₀ ≤ k → ∀ x : ℂ,
      dist w x < ((2 : ℝ)⁻¹) ^ k / 4 →
      ball x (17 * ((2 : ℝ)⁻¹ ^ k)) ⊆ U)
    (hVballZ : closedBall z ((2 : ℝ)⁻¹ ^ n) ⊆ V)
    (hVballW : closedBall w ((2 : ℝ)⁻¹ ^ n) ⊆ V)
    (hUballZ : closedBall z ((2 : ℝ)⁻¹ ^ n) ⊆ U)
    (hUballW : closedBall w ((2 : ℝ)⁻¹ ^ n) ⊆ U) :
    let b (v : ℂ) (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal
      (2 * T ^ 2 * (2 : ℝ) ^
        (-((ξ : ℝ) * Q - 3 * ζ) * (k : ℝ)) *
        Real.exp ((ξ : ℝ) * phiMN W P 0 k v ω) * lambdaN ξ W P n)
    let ell (v : ℂ) (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal
      (C * T ^ 2 * (2 : ℝ) ^
        (-((ξ : ℝ) * Q - 3 * ζ) * (k : ℝ)) *
        Real.exp ((ξ : ℝ) * phiMN W P 0 k v ω) * lambdaN ξ W P n)
    let a (v : ℂ) : ℝ≥0∞ := ∑ j ∈ Finset.range (n - k₀),
      (b v (k₀ + (j + 1)) + ell v (k₀ + (j + 1)) + b v (k₀ + j))
    let term (v : ℂ) : ℝ≥0∞ := ENNReal.ofReal
      (Clam * T * lambdaN ξ W P n * (2 : ℝ) ^
        (-((ξ : ℝ) * Q - 3 * ζ) * (n : ℝ)) *
        Real.exp ((ξ : ℝ) * phiMN W P 0 n v ω))
    lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω) U z w ≤
      term z + a z + (b z k₀ + ell z k₀ + b w k₀) + a w + term w := by
  dsimp
  have hR0 : R ≠ 0 := ne_of_gt (by linarith)
  have hξ0 : (ξ : ℝ) ≠ 0 := ne_of_gt ξ.2
  have ht (k : ℕ) :
      R * ((Real.log T + ζ * (k : ℝ)) / (R * (ξ : ℝ))) =
        (Real.log T + ζ * (k : ℝ)) / (ξ : ℝ) := by
    field_simp
  have hlam0 : 0 ≤ lambdaN ξ W P n :=
    le_trans (by positivity) hlamLower
  let bS (x : ℕ → ℂ) (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal (2 *
    (Real.exp ((ξ : ℝ) * phiMN W P 0 k (x k) ω) *
      (T * ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n))))
  let ellS (x : ℕ → ℂ) (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal (T * (C *
    (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n) *
    Real.exp ((ξ : ℝ) * phiMN W P 0 k (x k) ω))
  let aS (x : ℕ → ℂ) : ℝ≥0∞ := ∑ j ∈ Finset.range (n - k₀),
    (bS x (k₀ + (j + 1)) + ellS x (k₀ + (j + 1)) + bS x (k₀ + j))
  let termS (v : ℂ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) *
    (phiMN W P 0 n v ω + R *
      ((Real.log T + ζ * (n : ℝ)) / (R * (ξ : ℝ))))) *
      (((2 : ℝ)⁻¹ ^ n) / 2))
  obtain ⟨xz, xw, hfield, hdist⟩ :=
    pt_dist_local_selected_site_bound P W hW ξ Q ζ C n k₀ hk₀
      F V U R T (fun k => (Real.log T + ζ * (k : ℝ)) / (R * (ξ : ℝ)))
      hR (by linarith) ω hgood hinside hcover z w hz hw hzw
      hcollarZ hcollarW hVballZ hVballW hUballZ hUballW
  let b (v : ℂ) (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal
    (2 * T ^ 2 * (2 : ℝ) ^ (-((ξ : ℝ) * Q - 3 * ζ) * (k : ℝ)) *
      Real.exp ((ξ : ℝ) * phiMN W P 0 k v ω) * lambdaN ξ W P n)
  let ell (v : ℂ) (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal
    (C * T ^ 2 * (2 : ℝ) ^ (-((ξ : ℝ) * Q - 3 * ζ) * (k : ℝ)) *
      Real.exp ((ξ : ℝ) * phiMN W P 0 k v ω) * lambdaN ξ W P n)
  let a (v : ℂ) : ℝ≥0∞ := ∑ j ∈ Finset.range (n - k₀),
    (b v (k₀ + (j + 1)) + ell v (k₀ + (j + 1)) + b v (k₀ + j))
  let term (v : ℂ) : ℝ≥0∞ := ENNReal.ofReal
    (Clam * T * lambdaN ξ W P n * (2 : ℝ) ^
      (-((ξ : ℝ) * Q - 3 * ζ) * (n : ℝ)) *
      Real.exp ((ξ : ℝ) * phiMN W P 0 n v ω))
  have hsite (x : ℕ → ℂ) (v : ℂ) (k : ℕ) (hk : k ≤ n)
      (hf : |phiMN W P 0 k (x k) ω - phiMN W P 0 k v ω| ≤
        R * ((Real.log T + ζ * (k : ℝ)) / (R * (ξ : ℝ)))) :
      bS x k ≤ b v k ∧ ellS x k ≤ ell v k := by
    have hf' : |phiMN W P 0 k (x k) ω - phiMN W P 0 k v ω| ≤
        (Real.log T + ζ * (k : ℝ)) / (ξ : ℝ) := by
      rwa [ht] at hf
    exact pt_dist_selected_budgets_le_point (ξ : ℝ) Q ζ C T
      (lambdaN ξ W P n) (phiMN W P 0 k (x k) ω)
      (phiMN W P 0 k v ω) k ξ.2 (by linarith) hζ hC hlam0 hf'
  have hterm (v : ℂ) : termS v ≤ term v := by
    dsimp [termS, term]
    rw [ht]
    exact pt_dist_terminal_cost_le_point (ξ : ℝ) Q ζ Clam T
      (lambdaN ξ W P n) (phiMN W P 0 n v ω) n ξ.2 hζ hClam
      (by linarith) (by linarith) hlamLower
  have harm (x : ℕ → ℂ) (v : ℂ)
      (hf : ∀ k ≤ n, |phiMN W P 0 k (x k) ω - phiMN W P 0 k v ω| ≤
        R * ((Real.log T + ζ * (k : ℝ)) / (R * (ξ : ℝ)))) :
      aS x ≤ a v := by
    apply Finset.sum_le_sum
    intro j hj
    have hj : j < n - k₀ := Finset.mem_range.mp hj
    have hj0 : k₀ + j ≤ n := by omega
    have hj1 : k₀ + (j + 1) ≤ n := by omega
    exact add_le_add
      (add_le_add (hsite x v _ hj1 (hf _ hj1)).1
        (hsite x v _ hj1 (hf _ hj1)).2)
      (hsite x v _ hj0 (hf _ hj0)).1
  have hzsite := hsite xz z k₀ hk₀ (hfield k₀ hk₀).1
  have hwsite := hsite xw w k₀ hk₀ (hfield k₀ hk₀).2
  calc
    _ ≤ termS z + aS xz + (bS xz k₀ + ellS xz k₀ + bS xw k₀) +
        aS xw + termS w := hdist
    _ ≤ term z + a z + (b z k₀ + ell z k₀ + b w k₀) +
        a w + term w := by
      gcongr
      · exact hterm z
      · exact harm xz z (fun k hk => (hfield k hk).1)
      · exact hzsite.1
      · exact hzsite.2
      · exact hwsite.1
      · exact harm xw w (fun k hk => (hfield k hk).2)
      · exact hterm w

end SupercriticalLQGUniqueness.B2.DG20Pt
