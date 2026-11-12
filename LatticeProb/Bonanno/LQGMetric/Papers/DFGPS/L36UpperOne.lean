/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L36UpperOne at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36UpperStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The good event of the upper half of DFGPS Lemma 3.6 (D52)

Failure events of the pieces of the left–right path (`boxBad`, `momBad`, `walkBad`, `oscBad`,
`nullBad`) and the deterministic statement that off all of them the left–right graph distance
is `≤ δ^{−ξQ−ζ} e^{ξ h_1(0)}` (`graphLFPP_le_of_good`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS.L36

open Blueprint
open LQGDimension.Blueprint.Draft (osc)

variable {Ω : Type}

/-- failure of DG Prop 3.21 in the box `c + r_k B(a, 3/4)` -/
def boxBad (H : ℝ → ℂ → Ω → ℝ) (ξ lam δ : ℝ) (c a b : ℂ) (k : ℕ) : Set Ω :=
  {ω | ¬ ∃ q : ℝ → ℂ, DG.IsDGPath ((fun x => (rk k : ℂ) * x + c) '' Metric.closedBall a (3/4))
    ((rk k : ℂ) * b + c) ((rk k : ℂ) * a + c) q ∧
    LQGDimension.lfppLength ξ (fun x => H δ x ω) q ≤
      2 * rk k * Real.exp (ξ * H (rk k) c ω) * (δ / rk k) ^ lam}

/-- failure of the scale-sum bound -/
def momBad (H : ℝ → ℂ → Ω → ℝ) (ξ s ζ₁ δ : ℝ) (c : ℂ) (N : ℕ) : Set Ω :=
  {ω | δ ^ (-ζ₁) < ∑ k ∈ Finset.range (N + 1), rk k ^ s * Real.exp (ξ * H (rk k) c ω)}

/-- failure of the walk bound -/
def walkBad (H : ℝ → ℂ → Ω → ℝ) (ξ s ζ₁ δ : ℝ) (k k' : ℤ × ℤ) : Set Ω :=
  {ω | δ ^ (-s - ζ₁) < ((gridWalk δ k k').map fun x => Real.exp (ξ * H δ x ω)).sum}

/-- failure of the oscillation bound -/
def oscBad (H : ℝ → ℂ → Ω → ℝ) (κ δ : ℝ) : Set Ω :=
  {ω | κ * Real.log (1 / δ) < osc (fun z => H δ z ω) (8 * δ)}

/-- the null set where `h_1(0) ≠ 0` or the version `H` differs from `h_δ` on the grid -/
def nullBad (h : Ω → DistC) (H : ℝ → ℂ → Ω → ℝ) (δ : ℝ) : Set Ω :=
  {ω | ¬ (circleAvg (h ω) 1 0 = 0 ∧ ∀ ab : ℤ × ℤ,
    H δ ⟨ab.1 * δ, ab.2 * δ⟩ ω = circleAvg (h ω) δ ⟨ab.1 * δ, ab.2 * δ⟩)}

/-- **Off the failure events**, `D̃^δ(∂_L 𝕊, ∂_R 𝕊; 𝕊) ≤ δ^{−s−4ζ₁} e^{ξ h_1(0)}`. -/
theorem graphLFPP_le_of_good {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}
    (hHc : ∀ δ, 0 < δ → ∀ ω, Continuous fun z => H δ z ω) {ξ s ζ₁ δ : ℝ} (hδ : 0 < δ)
    (hδ64 : δ ≤ 1/64) (hξ : 0 < ξ) (hs : 0 ≤ s) (hζ₁ : 0 ≤ ζ₁) (N : ℕ)
    (hN : 64 * δ ≤ rk (N + 1)) (h18 : 18 ≤ δ ^ (-ζ₁)) (ω : Ω)
    (hO : ω ∉ oscBad H (ζ₁ / ξ) δ)
    (hL : ∀ k < N + 1, ω ∉ boxBad H ξ ((1 - s) - ζ₁) δ 0 aL bL k)
    (hR : ∀ k < N + 1, ω ∉ boxBad H ξ ((1 - s) - ζ₁) δ 1 aR bR k)
    (hmL : ω ∉ momBad H ξ s ζ₁ δ 0 N) (hmR : ω ∉ momBad H ξ s ζ₁ δ 1 N)
    (hwL : ω ∉ walkBad H ξ s ζ₁ δ (1, 1) (rnd δ (xL (N + 1))))
    (hwR : ω ∉ walkBad H ξ s ζ₁ δ (rnd δ (xR (N + 1))) (mR δ, 1))
    (hn : ω ∉ nullBad h H δ) :
    graphLFPP ξ δ (fun x => circleAvg (h ω) δ x) (leftVerts δ 1) (rightVerts δ 1) (rS 1) ≤
      δ ^ (-s - 4 * ζ₁) * Real.exp (ξ * circleAvg (h ω) 1 0) := by
  simp only [oscBad, momBad, walkBad, mem_setOf_eq, not_lt] at hO hmL hmR hwL hwR
  simp only [nullBad, mem_setOf_eq, not_not] at hn
  have hcongr : graphLFPP ξ δ (fun x => circleAvg (h ω) δ x) (leftVerts δ 1)
      (rightVerts δ 1) (rS 1) = graphLFPP ξ δ (fun x => H δ x ω) (leftVerts δ 1)
      (rightVerts δ 1) (rS 1) := by
    refine graphLFPP_congr fun x _ hx => ?_
    obtain ⟨a', b', rfl⟩ := hx
    exact (hn.2 (a', b')).symm
  rw [hcongr, hn.1, mul_zero, Real.exp_zero, mul_one]
  refine graphLFPP_le_good hδ hδ64 hξ hs hζ₁ (hHc δ hδ ω) (fun r c => H r c ω) N hN
    (fun k hk => ?_) (fun k hk => ?_) ?_ hmL hmR hwL hwR h18
  · have := hL k hk
    simp only [boxBad, mem_setOf_eq, not_not] at this
    exact this
  · have := hR k hk
    simp only [boxBad, mem_setOf_eq, not_not] at this
    exact this
  · have := mul_le_mul_of_nonneg_left hO hξ.le
    rw [← mul_assoc, mul_div_cancel₀ _ hξ.ne'] at this
    exact this

end LQGMetric.DFGPS.L36
