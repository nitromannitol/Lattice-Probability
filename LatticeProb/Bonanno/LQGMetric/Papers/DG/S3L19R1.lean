/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L19R1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L19Det
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L20

/-!
# DG Lemma 3.19 at `μ = μ_ĥ`: deterministic steps of node 4 (P2-DG105r)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, proof of Lemma 3.19
(DG:1638–1660) and of Lemma 3.21 (DG:1699–1706). DG's event `E_S^ε` (DG:1642) has two
conditions: (1) `D^ε(S, ∂S(1/2)) ≥ ε^{−1/(d_γ+ζ)}` and (2) every disk meeting `S(1/2)` with
mass `≤ ε` lies in `S(3/4)` ("so that `E_S^ε` is determined by `ĥ^tr|_{S(3/4)}`").
This file has the deterministic steps that turn the unit-frame event into DG's condition 1 for
the grid square of `s𝒜_n + b`:

* `dgLGDSet_ge_of_map`: a path from `A` to `∂B` (`A` closed in `int B`, `B` closed) is cut at
  its first crossing of `B` (`exists_cross_subpath`, S3L20); the balls that do not meet the
  piece are replaced by one that does; the piece and its balls are carried by a map that scales
  distances by `κ`. So the unrestricted distance from `A` to `∂B` for `μ` dominates the one for
  `ν` in the image (restricted to `U'`), as soon as every ball meeting `B` of `μ`-mass `≤ ε` has
  image in `Ū'` of `ν`-mass `≤ ε'` (DG's condition 2 is what makes this hold, DG:1642–1643).
* `l319_cross_mono`: `D(A, ∂S) ≤ D(A, ∂T)` for `A ⊆ int S`, `S ⊆ T` (unrestricted). This is
  the crossing monotonicity `l312Box u (1/20) ⊆ l312Box u (1/16) = 𝕊(1/2)` for `dg_lemma320`.
* `l319_heavy`: a ball meeting `B̄(u, 1/28)` and not contained in `B̄(u, 13/280)` contains a
  grid ball `B(w, g)`, `g ≤ 3/1120`, `w ∈ gℤ²`, `|w − u| ≤ 1/28 + 3/560 + g` (the scheme of `l320_heavy`,
  S3L20, with the smaller radii needed for the locality at `PercFar 9`). Own elementary
  geometric glue.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

/-- **cut at the first crossing and map** (DG:1642–1652): the unrestricted distance from `A` to
`∂B` for `μ` dominates the one for `ν` between the images, if balls meeting `B` of small
`μ`-mass have images (under the `κ`-scaling map `f`) of small `ν`-mass -/
theorem dgLGDSet_ge_of_map {μ ν : Measure ℂ} {ε ε' κ : ℝ} (hκ : 0 < κ) {f : ℂ → ℂ}
    (hf : ∀ a b, dist (f a) (f b) = κ * dist a b) {A B A' B' U' : Set ℂ} (hA : IsClosed A)
    (hB : IsClosed B) (hAB : A ⊆ interior B) (hA' : f '' A ⊆ A') (hB' : f '' frontier B ⊆ B')
    (hball : ∀ x ρ, 0 < ρ → (∃ p ∈ ball x ρ, p ∈ B) → μ (ball x ρ) ≤ ENNReal.ofReal ε →
      ball (f x) (κ * ρ) ⊆ closure U' ∧ ν (ball (f x) (κ * ρ)) ≤ ENNReal.ofReal ε') :
    dgLGDSet ν ε' U' A' B' ≤ dgLGDSet μ ε univ A (frontier B) := by
  have hfc : Continuous f := by
    refine Metric.continuous_iff.2 fun a e he => ⟨e / κ, div_pos he hκ, fun b hb => ?_⟩
    rw [hf]
    calc κ * dist b a < κ * (e / κ) := mul_lt_mul_of_pos_left hb hκ
      _ = e := by field_simp
  refine le_iInf₂ fun z hz => le_iInf₂ fun w hw => ?_
  unfold dgLGD
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨x, ρ, P, hb, hc⟩ := hN
  have hw' : w ∉ interior B := hw.2
  obtain ⟨t₀, t₁, -, h01, -, h0, h1, hin⟩ :=
    exists_cross_subpath P hA isOpen_interior hAB hz hw'
  set Q := subPathE P t₀ t₁ with hQ
  have hQB : ∀ r : unitInterval, Q r ∈ B := by
    intro r
    have hr : t₀ + (r : ℝ) * (t₁ - t₀) ∈ Icc t₀ t₁ := by
      have := r.2.1; have := r.2.2
      constructor <;> nlinarith
    exact closure_minimal interior_subset hB (hin _ hr)
  have hQcov : ∀ r : unitInterval, ∃ i, Q r ∈ ball (x i) (ρ i) := by
    intro r
    obtain ⟨t', ht'⟩ := range_subPathE P t₀ t₁ ⟨r, rfl⟩
    obtain ⟨i, hi⟩ := hc t'
    exact ⟨i, ht' ▸ hi⟩
  obtain ⟨i₀, hi₀⟩ := hQcov 0
  classical
  set j : Fin N → Fin N := fun i => if ∃ r, Q r ∈ ball (x i) (ρ i) then i else i₀ with hj
  have hjm : ∀ i, ∃ r, Q r ∈ ball (x (j i)) (ρ (j i)) := by
    intro i
    by_cases h : ∃ r, Q r ∈ ball (x i) (ρ i)
    · simp only [hj, if_pos h]; exact h
    · simp only [hj, if_neg h]; exact ⟨0, hi₀⟩
  have hwit : LGDWit ν ε' U' (f (P.extend t₀)) (f (P.extend t₁)) N := by
    refine ⟨fun i => f (x (j i)), fun i => κ * ρ (j i), Q.map hfc, fun i => ⟨?_, ?_, ?_⟩,
      fun r => ?_⟩
    · exact mul_pos hκ (hb (j i)).1
    · obtain ⟨r, hr⟩ := hjm i
      exact (hball _ _ (hb (j i)).1 ⟨Q r, hr, hQB r⟩ (hb (j i)).2.2).1
    · obtain ⟨r, hr⟩ := hjm i
      exact (hball _ _ (hb (j i)).1 ⟨Q r, hr, hQB r⟩ (hb (j i)).2.2).2
    · obtain ⟨i, hi⟩ := hQcov r
      have hji : j i = i := by simp only [hj, if_pos (⟨r, hi⟩ : ∃ r, Q r ∈ ball (x i) (ρ i))]
      refine ⟨i, ?_⟩
      simp only [Path.map_coe, Function.comp_apply, mem_ball, hji, hf] at hi ⊢
      exact mul_lt_mul_of_pos_left hi hκ
  have hzA : f (P.extend t₀) ∈ A' := by
    refine hA' ⟨_, ?_, rfl⟩
    have := frontier_subset_closure h0
    rwa [hA.closure_eq] at this
  have hwB : f (P.extend t₁) ∈ B' := hB' ⟨_, frontier_interior_subset h1, rfl⟩
  exact (dgLGDSet_le hzA hwB).trans (dgLGD_le_of_wit hwit)

/-- **crossing monotonicity**: `D(A, ∂S) ≤ D(A, ∂T)` (unrestricted) for `A` closed in `int S`,
`S ⊆ T` -/
lemma l319_cross_mono {μ : Measure ℂ} {ε : ℝ} {A S T : Set ℂ} (hA : IsClosed A)
    (hAS : A ⊆ interior S) (hST : S ⊆ T) :
    dgLGDSet μ ε univ A (frontier S) ≤ dgLGDSet μ ε univ A (frontier T) := by
  refine le_iInf₂ fun z hz => le_iInf₂ fun w hw => ?_
  unfold dgLGD
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨x, ρ, P, hb, hc⟩ := hN
  exact dgLGDSet_half_le hA hAS P hb hc (t := 0) (by rw [Path.extend_zero]; exact hz)
    (fun h => hw.2 (interior_mono hST h))

/-- **heavy balls** (`g ≤ 3/1120`): a ball meeting `B̄(u, 1/28)` and not contained in
`B̄(u, 13/280)` contains a grid ball `B(w, g)`, `w ∈ gℤ²`, `|w − u| ≤ 1/28 + 3/560 + g`
(as `l320_heavy`) -/
lemma l319_heavy {μ : Measure ℂ} {u : ℂ} {g t : ℝ} (hg : 0 < g) (hg' : g ≤ 3 / 1120)
    (hgrid : ∀ i j : ℤ, ‖(⟨i * g, j * g⟩ : ℂ) - u‖ ≤ 1 / 28 + 3 / 560 + g →
      ENNReal.ofReal t < μ (ball ⟨i * g, j * g⟩ g))
    {x : ℂ} {ρ : ℝ} {p : ℂ} (hp : p ∈ ball x ρ) (hpu : ‖p - u‖ ≤ 1 / 28)
    (hnot : ¬ ball x ρ ⊆ closedBall u (13 / 280)) : ENNReal.ofReal t < μ (ball x ρ) := by
  obtain ⟨q, hq, hqu⟩ := not_subset.1 hnot
  rw [mem_closedBall, not_le, dist_eq_norm] at hqu
  rw [mem_ball, dist_eq_norm] at hp hq
  have hpq : 3 / 280 < ‖q - p‖ := by
    linarith [norm_sub_le (q - p) (u - p), (by abel : q - p - (u - p) = q - u),
      norm_sub_rev p u, norm_sub_le_norm_sub_add_norm_sub q p u]
  have hρ : 3 / 560 < ρ := by
    have := norm_sub_le_norm_sub_add_norm_sub q x p
    rw [norm_sub_rev x p] at this
    linarith
  obtain ⟨p', hp'1, hp'2⟩ : ∃ p' : ℂ, ball p' (3 / 560) ⊆ ball x ρ ∧ ‖p' - p‖ ≤ 3 / 560 := by
    by_cases hd : ‖x - p‖ ≤ 3 / 560
    · exact ⟨x, ball_subset_ball (by linarith), hd⟩
    · replace hd := not_le.1 hd
      have hdρ : ‖x - p‖ < ρ := by rw [norm_sub_rev]; exact hp
      set d := ‖x - p‖
      have hd0 : 0 < d := by linarith
      refine ⟨p + ((3 / 560 / d : ℝ) : ℂ) * (x - p), ball_subset_ball' ?_, ?_⟩
      · rw [dist_eq_norm]
        have e : p + ((3 / 560 / d : ℝ) : ℂ) * (x - p) - x =
            ((1 - 3 / 560 / d : ℝ) : ℂ) * (p - x) := by
          push_cast; ring
        rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev p x,
          abs_of_nonneg (by rw [sub_nonneg, div_le_one hd0]; linarith)]
        have : (1 - 3 / 560 / d) * d = d - 3 / 560 := by field_simp
        rw [this]; linarith
      · rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        rw [div_mul_cancel₀ _ hd0.ne']
  obtain ⟨i, j, hij⟩ := DZZ.exists_grid_near p' hg
  have hball : ball (⟨i * g, j * g⟩ : ℂ) g ⊆ ball x ρ := by
    refine (ball_subset_ball' ?_).trans hp'1
    rw [dist_eq_norm]; linarith
  have hwu : ‖(⟨i * g, j * g⟩ : ℂ) - u‖ ≤ 1 / 28 + 3 / 560 + g := by
    have h1 := norm_sub_le_norm_sub_add_norm_sub (⟨i * g, j * g⟩ : ℂ) p' u
    have h2 := norm_sub_le_norm_sub_add_norm_sub p' p u
    linarith
  exact (hgrid i j hwu).trans_le (measure_mono hball)

/-- the crossing box `𝕍̄_u = l312Box u (1/20)` of `dg_lemma320` lies in `B̄(u, 1/28)` -/
lemma l312Box_sub_closedBall (u : ℂ) : l312Box u (1 / 20) ⊆ closedBall u (1 / 28) := by
  intro z hz
  obtain ⟨h1, h2⟩ := hz
  rw [mem_closedBall, dist_eq_norm]
  have hre : (z - u).re ^ 2 ≤ (1 / 40) ^ 2 := by
    rw [Complex.sub_re]; exact sq_le_sq' (by linarith [abs_le.1 h1]) (by linarith [abs_le.1 h1])
  have him : (z - u).im ^ 2 ≤ (1 / 40) ^ 2 := by
    rw [Complex.sub_im]; exact sq_le_sq' (by linarith [abs_le.1 h2]) (by linarith [abs_le.1 h2])
  have hn : ‖z - u‖ ^ 2 ≤ (1 / 28) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).1 hn

end DG
end LQGMetric
