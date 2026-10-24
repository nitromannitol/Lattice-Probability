import LatticeProb.Analysis.HarmonicBridge
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Interior localization on Euclidean balls

Increasing inner balls exhaust an open ball. A twice continuously differentiable function
on the ball admits compactly supported extensions near each closed inner ball, with the
same values and Laplacian there.
-/

namespace LatticeProb

open Set Filter Metric
open scoped Topology
open Laplacian

noncomputable section

/-- Radii of an increasing exhaustion strictly inside a ball of radius `R`. -/
def innerRadius (R : ℝ) (k : ℕ) : ℝ := R * (1 - 1 / ((k : ℝ) + 2))

/-- Every inner radius is positive when the outer radius is positive. -/
theorem innerRadius_pos {R : ℝ} (hR : 0 < R) (k : ℕ) : 0 < innerRadius R k := by
  apply mul_pos hR
  have hk : (1 : ℝ) < (k : ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have := (div_lt_one (by positivity : (0 : ℝ) < (k : ℝ) + 2)).2 hk
  linarith

/-- Every inner radius is strictly less than the outer radius. -/
theorem innerRadius_lt {R : ℝ} (hR : 0 < R) (k : ℕ) : innerRadius R k < R := by
  unfold innerRadius
  have hp : 0 < 1 / ((k : ℝ) + 2) := by positivity
  nlinarith

/-- The exhaustion radii are monotone. -/
theorem innerRadius_monotone {R : ℝ} (hR : 0 < R) : Monotone (innerRadius R) := by
  intro j k hjk
  apply mul_le_mul_of_nonneg_left _ hR.le
  have hcast : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
  have hdiv : 1 / ((k : ℝ) + 2) ≤ 1 / ((j : ℝ) + 2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

/-- The inner radii tend to the outer radius. -/
theorem tendsto_innerRadius (R : ℝ) :
    Tendsto (innerRadius R) atTop (𝓝 R) := by
  have hdiv : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    change Tendsto (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) at h
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h
  change Tendsto (fun k : ℕ => R * (1 - 1 / ((k : ℝ) + 2))) atTop (𝓝 R)
  simpa only [mul_one, sub_zero] using
    (tendsto_const_nhds (x := R)).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hdiv)

variable {d : ℕ} {c : EuclideanSpace ℝ (Fin d)} {R : ℝ}

/-- A `C²` function on a ball has a compactly supported `C²` extension near each
closed inner ball. The support of the extension remains inside the outer ball. -/
theorem exists_local_extension (hR : 0 < R) {v : EuclideanSpace ℝ (Fin d) → ℝ}
    (hv : ContDiffOn ℝ 2 v (ball c R)) (k : ℕ) :
    ∃ (f : EuclideanSpace ℝ (Fin d) → ℝ) (W : Set (EuclideanSpace ℝ (Fin d))),
      IsOpen W ∧ closure (ball c (innerRadius R k)) ⊆ W ∧ W ⊆ ball c R ∧
      ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ tsupport f ⊆ ball c R ∧ EqOn f v W := by
  have hcompact : IsCompact (closure (ball c (innerRadius R k))) :=
    (isCompact_closedBall c (innerRadius R k)).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall
  exact exists_contDiff_compactSupport_eq_near_compact hcompact isOpen_ball
    (closure_ball_subset_closedBall.trans (closedBall_subset_ball (innerRadius_lt hR k))) hv

/-- Equality on an open neighborhood gives equality of values and Laplacians there. -/
theorem laplacian_eq_of_eqOn {f v : EuclideanSpace ℝ (Fin d) → ℝ}
    {W : Set (EuclideanSpace ℝ (Fin d))} (hW : IsOpen W) (heq : EqOn f v W)
    {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ W) :
    Δ f y = Δ v y ∧ f y = v y := by
  have hlocal : f =ᶠ[𝓝 y] v := by
    filter_upwards [hW.mem_nhds hy] with z hz
    exact heq hz
  exact ⟨(InnerProductSpace.laplacian_congr_nhds hlocal).eq_of_nhds, heq hy⟩

/-- Every compact subset of the outer ball fits in a single inner ball. -/
theorem IsCompact.subset_innerRadius_ball {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hR : 0 < R) (hKB : K ⊆ ball c R) :
    ∃ k : ℕ, K ⊆ ball c (innerRadius R k) := by
  apply hK.elim_directed_cover (fun k => ball c (innerRadius R k)) (fun _ => isOpen_ball)
  · intro y hy
    have hlt : dist y c < R := hKB hy
    obtain ⟨k, hk⟩ := ((tendsto_innerRadius R).eventually (lt_mem_nhds hlt)).exists
    exact mem_iUnion.mpr ⟨k, hk⟩
  · intro j k
    exact ⟨max j k, ball_subset_ball ((innerRadius_monotone hR) (le_max_left j k)),
      ball_subset_ball ((innerRadius_monotone hR) (le_max_right j k))⟩

end

end LatticeProb
