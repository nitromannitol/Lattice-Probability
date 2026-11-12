/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L12Chain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.LGDBasic
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# DZZ Lemma 2.12, lower half: the deterministic ball-chain count (task P2-DZZPRE4)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 756–758 (proof of Lemma 2.12,
`lem-obvious-bounds`): "if `M_γ(B(v, 2^{-k})) ≥ δ²` for all `v ∈ 𝔠_k` … any Euclidean ball with
LQG measure at most `δ²` has radius at most `2^{-k+2}`. This implies the claimed lower bound on
the Liouville graph distance." DZZ give no details; the two steps are:

* `lgdDZZ_ge_of_large_balls_heavy` : if every ball of radius `≥ r` meeting `B̄(u, R)`
  (`R ≤ |u − v|`) has mass `> δ²`, then `D_δ(u, v) ≥ R/(2r)` (a path from `u` to `v` crosses
  every circle `∂B(u, s)`, `s ≤ R`; each crossing point lies in a chain ball of radius `< r`,
  so `[0, R]` is covered by `N` intervals of length `2r`);
* `large_ball_heavy_of_grid` : if every grid ball `B(w, s)`, `w ∈ sℤ²`, `|w − u| ≤ R + 3s`, has
  mass `> δ²`, then every ball of radius `≥ 4s` meeting `B̄(u, R)` has mass `> δ²` (it contains
  a grid ball).

Own elementary proofs of DZZ's one-line step (recorded in DEVIATIONS.md).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- The count: a chain of `N` balls of mass `≤ δ²` covering a path from `u` to `v` has
`R ≤ 2 r N` if all balls of radius `≥ r` meeting `B̄(u, R)` are heavy. -/
theorem chain_count_le {μ : Measure ℂ} {δ r R : ℝ} {u v : ℂ} (hR : 0 ≤ R) (huv : R ≤ ‖v - u‖)
    (hmass : ∀ (c : ℂ) (ρ : ℝ), r ≤ ρ → (ball c ρ ∩ closedBall u R).Nonempty →
      ENNReal.ofReal (δ ^ 2) < μ (ball c ρ))
    {N : ℕ} (c : Fin N → ℂ) (ρ : Fin N → ℝ) (P : Path u v)
    (h1 : ∀ i, μ (ball (c i) (ρ i)) ≤ ENNReal.ofReal (δ ^ 2))
    (h2 : ∀ t, ∃ i, P t ∈ ball (c i) (ρ i)) : R ≤ 2 * r * N := by
  -- every `s ∈ [0, R]` is within `r` of some `‖c i − u‖`
  have hcov : Icc 0 R ⊆ ⋃ i : Fin N, Ioo (‖c i - u‖ - r) (‖c i - u‖ + r) := by
    intro s hs
    have hf : Continuous fun t => ‖P t - u‖ := (P.continuous.sub continuous_const).norm
    have hIVT := intermediate_value_univ (0 : unitInterval) 1 hf
    have hs' : s ∈ Icc ‖P 0 - u‖ ‖P 1 - u‖ := by
      rw [P.source, P.target, sub_self, norm_zero]
      exact ⟨hs.1, hs.2.trans huv⟩
    obtain ⟨t, ht⟩ := hIVT hs'
    obtain ⟨i, hi⟩ := h2 t
    have hρ : ρ i < r := by
      by_contra hcon
      push_neg at hcon
      have hne : (ball (c i) (ρ i) ∩ closedBall u R).Nonempty :=
        ⟨P t, hi, by rw [mem_closedBall, dist_eq_norm]; simp only at ht; rw [ht]; exact hs.2⟩
      exact absurd (h1 i) (not_le.2 (hmass _ _ hcon hne))
    rw [mem_ball, dist_eq_norm] at hi
    simp only at ht
    have hd : |‖P t - u‖ - ‖c i - u‖| ≤ ‖P t - c i‖ := by
      have := abs_norm_sub_norm_le (P t - u) (c i - u)
      simpa using this
    rw [ht] at hd
    refine mem_iUnion.2 ⟨i, ?_, ?_⟩ <;>
    · have := abs_le.1 hd; linarith [this.1, this.2]
  have hvol := (measure_mono hcov).trans (measure_iUnion_fintype_le volume _)
  simp only [Real.volume_Icc, Real.volume_Ioo, sub_zero] at hvol
  have e : ∀ i : Fin N, ‖c i - u‖ + r - (‖c i - u‖ - r) = 2 * r := fun i => by ring
  simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hvol
  by_cases hr : 0 ≤ r
  · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hvol
    linarith
  · push_neg at hr
    obtain ⟨i, hi⟩ := h2 0
    have hne : (ball (c i) (ρ i) ∩ closedBall u R).Nonempty :=
      ⟨P 0, hi, by rw [P.source]; exact mem_closedBall_self hR⟩
    have hρ0 : 0 < ρ i := pos_of_mem_ball hi
    exact absurd (h1 i) (not_le.2 (hmass _ _ (by linarith) hne))

/-- **DZZ L2.12 lower half, deterministic step**: if every ball of radius `≥ r` meeting
`B̄(u, R)` (`0 ≤ R ≤ |v − u|`) has mass `> δ²`, then `n ≤ D_δ(u, v)` for every `n ≤ R/(2r)`. -/
theorem lgdDZZ_ge_of_large_balls_heavy {μ : Measure ℂ} {δ r R : ℝ} {u v : ℂ} (hr : 0 < r)
    (hR : 0 ≤ R) (huv : R ≤ ‖v - u‖)
    (hmass : ∀ (c : ℂ) (ρ : ℝ), r ≤ ρ → (ball c ρ ∩ closedBall u R).Nonempty →
      ENNReal.ofReal (δ ^ 2) < μ (ball c ρ))
    {n : ℕ} (hn : (n : ℝ) ≤ R / (2 * r)) : (n : ℕ∞) ≤ lgdDZZ μ δ u v := by
  unfold lgdDZZ
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨c, ρ, P, h1, h2⟩ := hN
  have h := chain_count_le hR huv hmass (fun i => ratPt (c i)) ρ P (fun i => (h1 i).2) h2
  have : (n : ℝ) ≤ N := by
    refine hn.trans ?_
    rw [div_le_iff₀ (by positivity)]; linarith
  exact_mod_cast this

/-- Grid rounding: every `z` is within `s` of a point of `sℤ²`. -/
lemma exists_grid_near (z : ℂ) {s : ℝ} (hs : 0 < s) :
    ∃ i j : ℤ, ‖(⟨i * s, j * s⟩ : ℂ) - z‖ ≤ s := by
  refine ⟨round (z.re / s), round (z.im / s), ?_⟩
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have h1 : |(round (z.re / s) : ℝ) * s - z.re| ≤ s / 2 := by
    have := abs_sub_round (z.re / s)
    rw [abs_sub_comm] at this
    calc |(round (z.re / s) : ℝ) * s - z.re| = |(round (z.re / s) : ℝ) - z.re / s| * s := by
          rw [← abs_of_pos hs, ← abs_mul, abs_of_pos hs]; congr 1; field_simp
      _ ≤ 1 / 2 * s := mul_le_mul_of_nonneg_right this hs.le
      _ = s / 2 := by ring
  have h2 : |(round (z.im / s) : ℝ) * s - z.im| ≤ s / 2 := by
    have := abs_sub_round (z.im / s)
    rw [abs_sub_comm] at this
    calc |(round (z.im / s) : ℝ) * s - z.im| = |(round (z.im / s) : ℝ) - z.im / s| * s := by
          rw [← abs_of_pos hs, ← abs_mul, abs_of_pos hs]; congr 1; field_simp
      _ ≤ 1 / 2 * s := mul_le_mul_of_nonneg_right this hs.le
      _ = s / 2 := by ring
  simp only [Complex.sub_re, Complex.sub_im]
  linarith

/-- **From grid balls to all large balls** (DZZ l. 757–758): if every grid ball `B(w, s)`,
`w ∈ sℤ²`, `|w − u| ≤ R + 3s`, has mass `> δ²`, then every ball of radius `≥ 4s` meeting
`B̄(u, R)` has mass `> δ²`. -/
theorem large_ball_heavy_of_grid {μ : Measure ℂ} {δ s R : ℝ} {u : ℂ} (hs : 0 < s)
    (hgrid : ∀ i j : ℤ, ‖(⟨i * s, j * s⟩ : ℂ) - u‖ ≤ R + 3 * s →
      ENNReal.ofReal (δ ^ 2) < μ (ball ⟨i * s, j * s⟩ s))
    (c : ℂ) (ρ : ℝ) (hρ : 4 * s ≤ ρ) (hne : (ball c ρ ∩ closedBall u R).Nonempty) :
    ENNReal.ofReal (δ ^ 2) < μ (ball c ρ) := by
  obtain ⟨y, hyc, hyu⟩ := hne
  rw [mem_ball, dist_eq_norm] at hyc
  rw [mem_closedBall, dist_eq_norm] at hyu
  have hρ0 : 0 < ρ := by linarith
  set θ := 2 * s / ρ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [div_le_one hρ0]; linarith
  set c' := c + (1 - θ) • (y - c)
  have hc'c : ‖c' - c‖ ≤ ρ - 2 * s := by
    have : c' - c = (1 - θ) • (y - c) := by simp [c']
    rw [this, norm_smul, Real.norm_of_nonneg (by linarith)]
    calc (1 - θ) * ‖y - c‖ ≤ (1 - θ) * ρ := mul_le_mul_of_nonneg_left hyc.le (by linarith)
      _ = ρ - 2 * s := by simp only [θ]; field_simp
  have hc'y : ‖c' - y‖ ≤ 2 * s := by
    have : c' - y = θ • (c - y) := by
      simp only [c']; rw [smul_sub, smul_sub, sub_smul, sub_smul, one_smul, one_smul]; abel
    rw [this, norm_smul, Real.norm_of_nonneg hθ0, norm_sub_rev]
    calc θ * ‖y - c‖ ≤ θ * ρ := mul_le_mul_of_nonneg_left hyc.le hθ0
      _ = 2 * s := by simp only [θ]; field_simp
  obtain ⟨i, j, hw⟩ := exists_grid_near c' hs
  set w : ℂ := ⟨i * s, j * s⟩
  have hwu : ‖w - u‖ ≤ R + 3 * s := by
    have := norm_sub_le_norm_sub_add_norm_sub w c' u
    have := norm_sub_le_norm_sub_add_norm_sub c' y u
    linarith
  refine (hgrid i j hwu).trans_le (measure_mono fun z hz => ?_)
  rw [mem_ball, dist_eq_norm] at hz ⊢
  have := norm_sub_le_norm_sub_add_norm_sub z w c
  have := norm_sub_le_norm_sub_add_norm_sub w c' c
  linarith

end DZZ
end LQGMetric
