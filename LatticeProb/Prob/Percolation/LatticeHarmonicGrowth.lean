import LatticeProb.Prob.Percolation.LatticeClusterL2Triangle
import LatticeProb.Network.HarmonicAlgebra
import Mathlib.Topology.Algebra.Order.Field

/-!
# Harmonic functions of subpolynomial averaged L² growth

For natural k the growth condition is the actual real-radius limit of
R^(-(k+1)) times the cardinality-normalized L² on the open Euclidean ball.
The nonnegative tail characterization expresses ordinary limsup zero without
using the junk value of a real-valued limsup for an unbounded function.
-/

namespace LatticeProb.Percolation

open Filter
open scoped BigOperators

noncomputable section

variable {d : ℕ} {ω : Configuration d}

/-- The literal normalized L² growth condition at all real radii tending to infinity. -/
def componentL2Subpolynomial (C : OpenComponent ω) (k : ℕ) (u : C → ℝ) : Prop :=
  Tendsto (fun R : ℝ => (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R u) atTop (nhds 0)

/-- On nonnegative radii the scaled actual L² quantity is nonnegative. -/
theorem componentL2_scaled_nonneg (C : OpenComponent ω) (k : ℕ) (u : C → ℝ)
    {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R u :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hR _)) (componentBallL2_nonneg C 0 R u)

/-- The zero-limit condition is equivalent to the ordinary nonnegative limsup-zero tail. -/
theorem componentL2Subpolynomial_iff_tail (C : OpenComponent ω) (k : ℕ) (u : C → ℝ) :
    componentL2Subpolynomial C k u ↔
      ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 < R₀ ∧
        ∀ R : ℝ, R₀ ≤ R → (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R u < ε := by
  constructor
  · intro h ε hε
    obtain ⟨a, ha⟩ := eventually_atTop.mp ((tendsto_order.mp h).2 ε hε)
    refine ⟨max a 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro R hR
    exact ha R ((le_max_left _ _).trans hR)
  · intro h
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact eventually_atTop.mpr ⟨0, fun R hR =>
        ha.trans_le (componentL2_scaled_nonneg C k u hR)⟩
    · intro ε hε
      obtain ⟨a, _, ha⟩ := h ε hε
      exact eventually_atTop.mpr ⟨a, ha⟩

/-- Actual finite L² Minkowski makes the growth condition closed under addition. -/
theorem componentL2Subpolynomial_add (C : OpenComponent ω) (k : ℕ)
    {u v : C → ℝ} (hu : componentL2Subpolynomial C k u)
    (hv : componentL2Subpolynomial C k v) : componentL2Subpolynomial C k (u + v) := by
  apply squeeze_zero'
  · exact eventually_atTop.mpr ⟨0, fun R hR => componentL2_scaled_nonneg C k _ hR⟩
  · refine eventually_atTop.mpr ⟨0, fun R hR => ?_⟩
    calc
      (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R (u + v) ≤
          (R ^ (k + 1))⁻¹ * (componentBallL2 C 0 R u + componentBallL2 C 0 R v) :=
        mul_le_mul_of_nonneg_left (componentBallL2_add_le C 0 R u v)
          (inv_nonneg.mpr (pow_nonneg hR _))
      _ = (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R u +
          (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R v := mul_add _ _ _
  · simpa only [add_zero] using hu.add hv

/-- The normalized L² scalar identity preserves the zero growth limit. -/
theorem componentL2Subpolynomial_smul (C : OpenComponent ω) (k : ℕ)
    {u : C → ℝ} (hu : componentL2Subpolynomial C k u) (a : ℝ) :
    componentL2Subpolynomial C k (a • u) := by
  have h := hu.const_mul |a|
  simp only [mul_zero] at h
  exact h.congr (fun R => by rw [componentBallL2_smul]; ring)

/-- Every constant has subpolynomial normalized L² growth for every natural index. -/
theorem componentL2Subpolynomial_const (C : OpenComponent ω) (k : ℕ) (c : ℝ) :
    componentL2Subpolynomial C k (fun _ => c) := by
  apply squeeze_zero'
  · exact eventually_atTop.mpr ⟨0, fun R hR => componentL2_scaled_nonneg C k _ hR⟩
  · refine eventually_atTop.mpr ⟨0, fun R hR => ?_⟩
    exact mul_le_mul_of_nonneg_left (componentBallL2_const_le C 0 R c)
      (inv_nonneg.mpr (pow_nonneg hR _))
  · have h := (tendsto_pow_atTop (α := ℝ) (Nat.succ_ne_zero k)).inv_tendsto_atTop
    simpa only [Pi.inv_apply, Nat.succ_eq_add_one, zero_mul] using h.mul_const |c|

/-- Source A_k on an actual open component, with literal exponent k+1 and averaged L². -/
def harmonicGrowthSpace (C : OpenComponent ω) (k : ℕ) : Submodule ℝ (C → ℝ) where
  carrier := {u | (∀ x, componentLaplacian C u x = 0) ∧ componentL2Subpolynomial C k u}
  zero_mem' := by
    constructor
    · intro x
      rw [componentLaplacian_eq_netLaplacian]
      exact Network.netLaplacian_const _ 0 x
    · exact componentL2Subpolynomial_const C k 0
  add_mem' := by
    rintro u v ⟨hu, hgu⟩ ⟨hv, hgv⟩
    constructor
    · exact (component_harmonic_iff C _).mpr
        (Network.harmonic_add ((component_harmonic_iff C u).mp hu)
          ((component_harmonic_iff C v).mp hv))
    · exact componentL2Subpolynomial_add C k hgu hgv
  smul_mem' := by
    rintro a u ⟨hu, hgu⟩
    constructor
    · exact (component_harmonic_iff C _).mpr
        (Network.harmonic_smul ((component_harmonic_iff C u).mp hu) a)
    · exact componentL2Subpolynomial_smul C k hgu a

/-- Full membership characterization by the literal harmonic equation and real-radius limit. -/
theorem mem_harmonicGrowthSpace_iff (C : OpenComponent ω) (k : ℕ) (u : C → ℝ) :
    u ∈ harmonicGrowthSpace C k ↔ (∀ x, componentLaplacian C u x = 0) ∧
      Tendsto (fun R : ℝ => (R ^ (k + 1))⁻¹ *
        Real.sqrt ((∑ x ∈ componentEuclideanBall C 0 R, (u x) ^ 2) /
          ((componentEuclideanBall C 0 R).card : ℝ))) atTop (nhds 0) := Iff.rfl

/-- Constants are actual harmonic elements of every source growth space. -/
theorem const_mem_harmonicGrowthSpace (C : OpenComponent ω) (k : ℕ) (c : ℝ) :
    (fun _ : C => c) ∈ harmonicGrowthSpace C k := by
  refine ⟨?_, componentL2Subpolynomial_const C k c⟩
  intro x
  rw [componentLaplacian_eq_netLaplacian]
  exact Network.netLaplacian_const _ c x

/-- The actual zero function belongs to every source growth space. -/
theorem zero_mem_harmonicGrowthSpace (C : OpenComponent ω) (k : ℕ) :
    (0 : C → ℝ) ∈ harmonicGrowthSpace C k := (harmonicGrowthSpace C k).zero_mem

/-- Membership also has the full harmonic-equation and nonnegative-tail characterization. -/
theorem mem_harmonicGrowthSpace_iff_tail (C : OpenComponent ω) (k : ℕ) (u : C → ℝ) :
    u ∈ harmonicGrowthSpace C k ↔ (∀ x, componentLaplacian C u x = 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 < R₀ ∧
        ∀ R : ℝ, R₀ ≤ R → (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R u < ε := by
  change (_ ∧ componentL2Subpolynomial C k u) ↔ _
  rw [componentL2Subpolynomial_iff_tail]

/-- Global linear growth in the source ℓ¹ norm implies membership in A_1.
This assumes a bound at every component vertex, with no eventual-to-global conversion. -/
theorem mem_harmonicGrowthSpace_one_of_global_l1_bound (C : OpenComponent ω)
    (u : C → ℝ) (hu : ∀ x, componentLaplacian C u x = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x : C, |u x| ≤ M * (1 + ∑ i : Fin d, |(x.val i : ℝ)|)) :
    u ∈ harmonicGrowthSpace C 1 := by
  refine ⟨hu, ?_⟩
  apply squeeze_zero'
  · exact eventually_atTop.mpr ⟨0, fun R hR => componentL2_scaled_nonneg C 1 u hR⟩
  · refine eventually_atTop.mpr ⟨1, fun R hR => ?_⟩
    have hRp : 0 < R := zero_lt_one.trans_le hR
    have hball : componentBallL2 C 0 R u ≤ M * (1 + (d : ℝ)) * R := by
      apply componentBallL2_le_of_abs_le C 0 R u
        (mul_nonneg (mul_nonneg hM (by positivity)) hRp.le)
      intro x hx
      have hcoord (i : Fin d) : |(x.val i : ℝ)| ≤ R := by
        have hi := PiLp.norm_apply_le
          (latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding (0 : Vertex d)) i
        change |(x.val i : ℝ) - ((0 : Vertex d) i : ℝ)| ≤
          ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding (0 : Vertex d)‖ at hi
        simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at hi
        exact hi.trans (mem_componentEuclideanBall C 0 R x |>.mp hx).le
      have hsum : (∑ i : Fin d, |(x.val i : ℝ)|) ≤ (d : ℝ) * R := by
        calc
          _ ≤ ∑ _i : Fin d, R := Finset.sum_le_sum (fun i _ => hcoord i)
          _ = (d : ℝ) * R := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc
        |u x| ≤ M * (1 + ∑ i : Fin d, |(x.val i : ℝ)|) := hbound x
        _ ≤ M * (1 + (d : ℝ) * R) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) hM
        _ ≤ M * (1 + (d : ℝ)) * R := by nlinarith
    calc
      (R ^ (1 + 1))⁻¹ * componentBallL2 C 0 R u ≤
          (R ^ (1 + 1))⁻¹ * (M * (1 + (d : ℝ)) * R) :=
        mul_le_mul_of_nonneg_left hball (inv_nonneg.mpr (sq_nonneg R))
      _ = R⁻¹ * (M * (1 + (d : ℝ))) := by
        field_simp; ring
  · simpa only [zero_mul] using
      (tendsto_inv_atTop_zero (𝕜 := ℝ)).mul_const (M * (1 + (d : ℝ)))

/-- On an actual all-closed component every function belongs to every growth space. -/
theorem allClosed_mem_harmonicGrowthSpace (z : Vertex d) (k : ℕ)
    (u : (openGraph (allClosed d)).connectedComponentMk z → ℝ) :
    u ∈ harmonicGrowthSpace ((openGraph (allClosed d)).connectedComponentMk z) k := by
  have he : u = fun _ => u ⟨z, rfl⟩ := by
    funext x
    exact congrArg u (Subtype.ext (allClosed_component_vertex_eq z x))
  rw [he]
  exact const_mem_harmonicGrowthSpace _ k _

end

end LatticeProb.Percolation
