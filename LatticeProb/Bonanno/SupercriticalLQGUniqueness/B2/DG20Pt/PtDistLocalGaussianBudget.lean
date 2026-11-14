/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLocalGaussianBudget at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistPointCostGaussian

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

def ptDistLocalGaussianBudget
    (ξ Q ζ L β T C Clam lam : ℝ) (n k₀ : ℕ) : ℝ≥0∞ :=
  let p (k : ℕ) : ℝ := (2 : ℝ) ^
    (-(ξ * Q - 3 * ζ - 2 * β) * (k : ℝ))
  let b (k : ℕ) : ℝ≥0∞ :=
    ENNReal.ofReal (2 * T ^ 2 * Real.exp L * p k * lam)
  let ell (k : ℕ) : ℝ≥0∞ :=
    ENNReal.ofReal (C * T ^ 2 * Real.exp L * p k * lam)
  let term : ℝ≥0∞ :=
    ENNReal.ofReal (Clam * T ^ 2 * lam * Real.exp L * p n)
  let arm : ℝ≥0∞ := ∑ j ∈ Finset.range (n - k₀),
    (b (k₀ + (j + 1)) + ell (k₀ + (j + 1)) + b (k₀ + j))
  term + arm + (b k₀ + ell k₀ + b k₀) + arm + term

theorem pt_dist_local_point_budget_le_gaussian_budget
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (ξ : Ioi (0 : ℝ)) (Q ζ L β T C Clam : ℝ)
    (n k₀ : ℕ) (hk₀ : 1 ≤ k₀) (hkn : k₀ ≤ n)
    (hβ : 0 ≤ β) (hT : 1 ≤ T) (hC : 0 ≤ C)
    (hClam : 0 ≤ Clam) (hlam : 0 ≤ lambdaN ξ W P n)
    (z w : ℂ) (ω : Ω)
    (hzGood : ω ∈ ptDistPointFieldGood P W (ξ : ℝ) L β n z)
    (hwGood : ω ∈ ptDistPointFieldGood P W (ξ : ℝ) L β n w) :
    ptDistLocalPointBudget P W ξ Q ζ C Clam T n k₀ z w ω ≤
      ptDistLocalGaussianBudget (ξ : ℝ) Q ζ L β T C Clam
        (lambdaN ξ W P n) n k₀ := by
  let p (k : ℕ) : ℝ := (2 : ℝ) ^
    (-((ξ : ℝ) * Q - 3 * ζ - 2 * β) * (k : ℝ))
  let b (k : ℕ) : ℝ≥0∞ :=
    ENNReal.ofReal (2 * T ^ 2 * Real.exp L * p k * lambdaN ξ W P n)
  let ell (k : ℕ) : ℝ≥0∞ :=
    ENNReal.ofReal (C * T ^ 2 * Real.exp L * p k * lambdaN ξ W P n)
  let term : ℝ≥0∞ :=
    ENNReal.ofReal (Clam * T ^ 2 * lambdaN ξ W P n * Real.exp L * p n)
  let arm : ℝ≥0∞ := ∑ j ∈ Finset.range (n - k₀),
    (b (k₀ + (j + 1)) + ell (k₀ + (j + 1)) + b (k₀ + j))
  let bP (v : ℂ) (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal
    (2 * T ^ 2 * (2 : ℝ) ^
      (-((ξ : ℝ) * Q - 3 * ζ) * (k : ℝ)) *
      Real.exp ((ξ : ℝ) * phiMN W P 0 k v ω) * lambdaN ξ W P n)
  let ellP (v : ℂ) (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal
    (C * T ^ 2 * (2 : ℝ) ^
      (-((ξ : ℝ) * Q - 3 * ζ) * (k : ℝ)) *
      Real.exp ((ξ : ℝ) * phiMN W P 0 k v ω) * lambdaN ξ W P n)
  let termP (v : ℂ) : ℝ≥0∞ := ENNReal.ofReal
    (Clam * T * lambdaN ξ W P n * (2 : ℝ) ^
      (-((ξ : ℝ) * Q - 3 * ζ) * (n : ℝ)) *
      Real.exp ((ξ : ℝ) * phiMN W P 0 n v ω))
  let armP (v : ℂ) : ℝ≥0∞ := ∑ j ∈ Finset.range (n - k₀),
    (bP v (k₀ + (j + 1)) + ellP v (k₀ + (j + 1)) + bP v (k₀ + j))
  have hfield (v : ℂ) (hv : ω ∈ ptDistPointFieldGood P W (ξ : ℝ) L β n v)
      (k : ℕ) (hk : k₀ ≤ k) (hkn' : k ≤ n) :
      |phiMN W P 0 k v ω| ≤ (L + β * (k : ℝ)) / (ξ : ℝ) := by
    exact le_of_lt (hv k (Finset.mem_Icc.mpr ⟨by omega, hkn'⟩))
  have hcost (v : ℂ) (hv : ω ∈ ptDistPointFieldGood P W (ξ : ℝ) L β n v)
      (k : ℕ) (hk : k₀ ≤ k) (hkn' : k ≤ n) :
      bP v k ≤ b k ∧ ellP v k ≤ ell k := by
    have h := pt_dist_point_costs_on_gaussian_good
      (ξ : ℝ) Q ζ L β T C Clam (lambdaN ξ W P n)
      (phiMN W P 0 k v ω) k ξ.2 hβ hT hC hClam hlam
      (hfield v hv k hk hkn')
    exact ⟨h.1, h.2.1⟩
  have hterm (v : ℂ) (hv : ω ∈ ptDistPointFieldGood P W (ξ : ℝ) L β n v) :
      termP v ≤ term := by
    exact (pt_dist_point_costs_on_gaussian_good
      (ξ : ℝ) Q ζ L β T C Clam (lambdaN ξ W P n)
      (phiMN W P 0 n v ω) n ξ.2 hβ hT hC hClam hlam
      (hfield v hv n hkn le_rfl)).2.2
  have hcostZ (k : ℕ) (hk : k₀ ≤ k) (hn : k ≤ n) :=
    hcost z hzGood k hk hn
  have hcostW (k : ℕ) (hk : k₀ ≤ k) (hn : k ≤ n) :=
    hcost w hwGood k hk hn
  have harm (v : ℂ) (hv : ω ∈ ptDistPointFieldGood P W (ξ : ℝ) L β n v) :
      armP v ≤ arm := by
    apply Finset.sum_le_sum
    intro j hj
    have hj : j < n - k₀ := Finset.mem_range.mp hj
    have hj0 : k₀ + j ≤ n := by omega
    have hj1 : k₀ + (j + 1) ≤ n := by omega
    exact add_le_add
      (add_le_add (hcost v hv _ (by omega) hj1).1
        (hcost v hv _ (by omega) hj1).2)
      (hcost v hv _ (by omega) hj0).1
  change termP z + armP z +
      (bP z k₀ + ellP z k₀ + bP w k₀) + armP w + termP w ≤
    term + arm + (b k₀ + ell k₀ + b k₀) + arm + term
  exact add_le_add
    (add_le_add
      (add_le_add
        (add_le_add (hterm z hzGood) (harm z hzGood))
        (add_le_add
          (add_le_add (hcostZ k₀ le_rfl hkn).1 (hcostZ k₀ le_rfl hkn).2)
          (hcostW k₀ le_rfl hkn).1))
      (harm w hwGood))
    (hterm w hwGood)

end SupercriticalLQGUniqueness.B2.DG20Pt
