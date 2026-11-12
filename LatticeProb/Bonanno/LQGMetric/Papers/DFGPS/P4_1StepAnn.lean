/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_1StepAnn at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_1StepCross
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5CentreGeom
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_10Neg
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_1GaussMom

/-!
# DFGPS Proposition 4.1, Steps 1–2: annulus bounds on a general space; the tube condition

DFGPS (arXiv:1905.00380), proof of Proposition 4.1 (T:2459–2492).

* `ann_bound_general` — Step 1 (T:2464–2470): DFGPS Proposition 3.1 for the annulus
  `B̄_{3s/4}(z) → ∂B_{3s/2}(z)` inside `B_{2s}(z)`, at every centre `z` and scale `s`, on an
  arbitrary probability space carrying a normalized whole-plane GFF (transferred from the
  canonical space `DFGPS.prop3_1_centre_ann` through the law, `prob_le_canonical`).
* `TubeBlocks L b` — the deterministic geometric content of Step 2 and of the choice of the
  intervals `[k₁, k₂]` in Step 3 (T:2486–2490, T:2502): for each small `ε` a bounded number of
  blocks of `≍ ε⁻¹` well-separated centres near `L` such that any path in `B_{ε𝕣}(𝕣L)` between
  two points at distance `≥ b𝕣` comes within `2ε𝕣` of all the centres `𝕣 w_k` of one block.
* `tube_sum_le` — the consequence of `crossing_sum_le` used in Step 3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace LQGMetric.DFGPS.P41

open Blueprint MetricGeometry

/-- **DFGPS Prop 4.1, Step 1** (T:2464–2470), one centre: Prop 3.1 for the annulus
`B̄_{3s/4}(z) → ∂B_{3s/2}(z)` in `B_{2s}(z)`, uniformly over the probability space. -/
theorem ann_bound_general (h31 : Prop3_1) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) :
    ∀ p : ℝ, 0 < p → ∃ C A₀ : ℝ, ∀ A, A₀ < A →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWPGFF h P → ∀ s : ℝ, 0 < s → ∀ z : ℂ,
      P {ω | ENNReal.ofReal (A⁻¹ * scaleFac (xiGamma γ) c (h ω) s z) ≤
            setDistIn (D (h ω)) (closedBall z (3 / 4 * s)) (sphere z (3 / 2 * s))
              (ball z (2 * s))}ᶜ ≤
        ENNReal.ofReal (C * A ^ (-p)) := by
  obtain ⟨μ, hμP, hμ⟩ := exists_canonical_normGFF
  intro p hp
  obtain ⟨C, A₀, hC⟩ := prop3_1_centre_ann h31 hγ0 hγ2 hD hμ p hp
  refine ⟨C, A₀, fun A hA Ω _ P _ h hh s hs z => ?_⟩
  exact (prob_le_canonical hμ P h hh _).trans (hC A hA s hs z)

/-- The deterministic tube condition of DFGPS Prop 4.1, Steps 2–3 (T:2486–2490, T:2502), at
unit scale: constants `κ, K, c, R`, a number `M` of blocks and `ε₁ > 0` such that for every
`ε ∈ (0, ε₁)` there are `M` blocks of centres `w m k` (`k < n m`, `κ/ε ≤ n m ≤ K/ε`), each block
`9ε`-separated with `‖w m j − w m k‖ ≥ c ε (|j − k| + 1)`, contained in `B̄_R(0)`, and such that for
all `𝕣 > 0`, `u, v ∈ B_{ε𝕣}(𝕣L)` with `|u − v| ≥ b𝕣` and every path from `u` to `v` in
`B_{ε𝕣}(𝕣L)`, some block has all its centres `𝕣 w m k` at distance `> 4ε𝕣` from `u` and the path
comes within `2ε𝕣` of each of them. (The block may depend on the path: for a whole circle a path
may go either way around, DEV-P41-5.) -/
def TubeBlocks (L : Set ℂ) (b : ℝ) : Prop :=
  ∃ (κ K c R ε₁ : ℝ) (M : ℕ), 0 < κ ∧ 0 < c ∧ 0 ≤ R ∧ 0 < ε₁ ∧
    ∀ ε ∈ Ioo (0 : ℝ) ε₁, ∃ (n : Fin M → ℕ) (w : (m : Fin M) → Fin (n m) → ℂ),
      (∀ m, κ / ε ≤ n m ∧ (n m : ℝ) ≤ K / ε) ∧ (∀ m k, ‖w m k‖ ≤ R) ∧
      (∀ m j k, j ≠ k → 9 * ε ≤ ‖w m j - w m k‖ ∧
        c * ε * ((dN j k : ℝ) + 1) ≤ ‖w m j - w m k‖) ∧
      ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ u ∈ thickening (ε * 𝕣) (scaleSet 𝕣 0 L),
        ∀ v ∈ thickening (ε * 𝕣) (scaleSet 𝕣 0 L), b * 𝕣 ≤ ‖u - v‖ →
        ∀ γ : ℝ → ℂ, Continuous γ → γ 0 = u → γ 1 = v →
          γ '' Icc 0 1 ⊆ thickening (ε * 𝕣) (scaleSet 𝕣 0 L) →
          ∃ m : Fin M, (∀ k, 4 * (ε * 𝕣) < ‖u - 𝕣 * w m k‖) ∧
            ∀ k, ∃ t ∈ Icc (0 : ℝ) 1, ‖γ t - 𝕣 * w m k‖ ≤ 2 * (ε * 𝕣)

/-- `crossing_sum_le_path` for a `9ρ`-separated family, with the crossing distances bounded
below. -/
theorem tube_sum_le_path (Dg : ContMetric) {u v : ℂ} {n : ℕ} (z : Fin n → ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hsep : ∀ j k, j ≠ k → 9 * ρ ≤ ‖z j - z k‖)
    (hu : ∀ k, 4 * ρ < ‖u - z k‖) (γ : Path (Dg.pt u) (Dg.pt v))
    (hmeet : ∀ k, ∃ t ∈ Icc (0 : ℝ) 1, ‖Dg.unpt (γ.extend t) - z k‖ ≤ 2 * ρ)
    (a : Fin n → ℝ) (ha0 : ∀ k, 0 ≤ a k)
    (ha : ∀ k, ENNReal.ofReal (a k) ≤ setDistIn Dg (closedBall (z k) (2 * ρ))
      (sphere (z k) (4 * ρ)) (ball (z k) (16 / 3 * ρ))) :
    ENNReal.ofReal (∑ k, a k) ≤ pathLength γ := by
  have hdisj : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
      fun i => closedBall (z i) (4 * ρ) := by
    intro i _ j _ hij
    refine closedBall_disjoint_closedBall ?_
    rw [dist_eq_norm]
    linarith [hsep i j hij]
  refine le_trans ?_ (crossing_sum_le_path Dg Finset.univ z hρ hdisj (fun k _ => hu k) γ
    (fun k _ => hmeet k))
  rw [ENNReal.ofReal_sum_of_nonneg fun k _ => ha0 k]
  exact Finset.sum_le_sum fun k _ => ha k

end LQGMetric.DFGPS.P41
