/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L54B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54A

/-!
# DZZ Lemma 5.4: the boundary `∂𝕍_{u,1/20}` as a union of `4n` segments (P2-DZZ54)

DZZ, arXiv:1807.00422, proof of Lemma 5.4 (l. 2571–2573): "`min_{x ∈ ∂𝕍̄_u} D̄(u,x) =
min_{L_δ} min_{x ∈ L_δ} D̄(u,x)`, where the minimization is over `4δ^{−2ι}` many disjoint segments
`L_δ` of length `δ^{2ι}`". We cut each side of `∂𝕍_{u,1/20}` into `n` closed segments of length
`h = (1/20)/n` (`l54Piece u h σ k`, side `σ < 4`, index `k < n`), and prove:
* each piece is an axis-parallel segment of length `h` contained in `∂𝕍_{u,1/20}`, connected,
  of diameter `≥ h` (so admissible in DZZ's sense once `δ^ξ ≤ h`);
* `lgdMinSet_frontier_eq_piece`: the point-to-boundary distance equals the point-to-piece distance
  of some piece.
(The pieces of one side share endpoints; DZZ's "disjoint" plays no role.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- The `k`-th segment (length `h`) of side `σ` of `∂𝕍_{u,1/20}`: bottom, left, top, right. -/
def l54Piece (u : ℂ) (h : ℝ) (σ k : ℕ) : Set ℂ :=
  match σ with
  | 0 => Icc (u.re - 1 / 20 / 2 + k * h) (u.re - 1 / 20 / 2 + k * h + h) ×ℂ {u.im - 1 / 20 / 2}
  | 1 => {u.re - 1 / 20 / 2} ×ℂ Icc (u.im - 1 / 20 / 2 + k * h) (u.im - 1 / 20 / 2 + k * h + h)
  | 2 => Icc (u.re - 1 / 20 / 2 + k * h) (u.re - 1 / 20 / 2 + k * h + h) ×ℂ {u.im + 1 / 20 / 2}
  | _ => {u.re + 1 / 20 / 2} ×ℂ Icc (u.im - 1 / 20 / 2 + k * h) (u.im - 1 / 20 / 2 + k * h + h)

lemma l54Piece_seg (u : ℂ) (h : ℝ) (σ k : ℕ) : ∃ a c : ℝ,
    l54Piece u h σ k = Icc a (a + h) ×ℂ {c} ∨ l54Piece u h σ k = {c} ×ℂ Icc a (a + h) := by
  rcases σ with _ | _ | _ | σ
  · exact ⟨_, _, Or.inl rfl⟩
  · exact ⟨_, _, Or.inr rfl⟩
  · exact ⟨_, _, Or.inl rfl⟩
  · exact ⟨_, _, Or.inr rfl⟩

lemma l54Piece_subset_frontier (u : ℂ) {h : ℝ} (hh : 0 ≤ h) (σ : ℕ) {k : ℕ}
    (hk : ((k : ℝ) + 1) * h ≤ 1 / 20) : l54Piece u h σ k ⊆ frontier (sqBox u (1 / 20)) := by
  rw [frontier_sqBox (by norm_num)]
  have hk0 : 0 ≤ (k : ℝ) * h := by positivity
  intro z hz
  rcases σ with _ | _ | _ | σ <;> simp only [l54Piece, Complex.mem_reProdIm, mem_Icc,
    mem_singleton_iff] at hz <;> simp only [mem_union, Complex.mem_reProdIm, mem_Icc,
    mem_singleton_iff]
  · exact Or.inl (Or.inl (Or.inl ⟨⟨by linarith, by linarith⟩, hz.2⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨hz.1, by linarith, by linarith⟩))
  · exact Or.inl (Or.inr ⟨⟨by linarith, by linarith⟩, hz.2⟩)
  · exact Or.inr ⟨hz.1, by linarith, by linarith⟩

/-- One-dimensional covering: `[a, a + n h]` is the union of the `[a + k h, a + k h + h]`. -/
lemma l54_exists_Icc_piece {a t h : ℝ} {n : ℕ} (hn : 1 ≤ n) (hh : 0 < h)
    (ht : t ∈ Icc a (a + n * h)) : ∃ k < n, t ∈ Icc (a + k * h) (a + k * h + h) := by
  obtain ⟨h1, h2⟩ := ht
  set m := ⌊(t - a) / h⌋₊ with hm
  have hq : 0 ≤ (t - a) / h := div_nonneg (by linarith) hh.le
  have hm1 : (m : ℝ) ≤ (t - a) / h := Nat.floor_le hq
  have hm2 : (t - a) / h < m + 1 := Nat.lt_floor_add_one _
  have hqn : (t - a) / h ≤ n := by rw [div_le_iff₀ hh]; linarith
  by_cases hmn : m < n
  · refine ⟨m, hmn, ?_, ?_⟩
    · rw [le_div_iff₀ hh] at hm1; linarith
    · rw [div_lt_iff₀ hh] at hm2; linarith
  · push_neg at hmn
    refine ⟨n - 1, by omega, ?_, ?_⟩
    · have : ((n - 1 : ℕ) : ℝ) ≤ (t - a) / h :=
        le_trans (by exact_mod_cast (show n - 1 ≤ m by omega)) hm1
      rw [le_div_iff₀ hh] at this; linarith
    · rw [Nat.cast_sub hn]; push_cast; linarith

lemma exists_l54Piece_of_mem_frontier (u : ℂ) {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : z ∈ frontier (sqBox u (1 / 20))) :
    ∃ σ < 4, ∃ k < n, z ∈ l54Piece u (1 / 20 / n) σ k := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hh : (0 : ℝ) < 1 / 20 / n := by positivity
  have hnh : (n : ℝ) * (1 / 20 / n) = 1 / 20 := by field_simp
  rw [frontier_sqBox (by norm_num)] at hz
  simp only [mem_union, Complex.mem_reProdIm, mem_singleton_iff] at hz
  have key : ∀ {c t : ℝ}, t ∈ Icc (c - 1 / 20 / 2) (c + 1 / 20 / 2) → ∃ k < n,
      t ∈ Icc (c - 1 / 20 / 2 + k * (1 / 20 / n)) (c - 1 / 20 / 2 + k * (1 / 20 / n) + 1 / 20 / n) :=
    fun {c t} ht => l54_exists_Icc_piece hn hh ⟨ht.1, by rw [hnh]; linarith [ht.2]⟩
  rcases hz with ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · obtain ⟨k, hk, hk'⟩ := key h1
    refine ⟨0, by norm_num, k, hk, ?_⟩
    simp only [l54Piece, Complex.mem_reProdIm, mem_preimage, mem_singleton_iff]
    exact ⟨hk', h2⟩
  · obtain ⟨k, hk, hk'⟩ := key h2
    refine ⟨1, by norm_num, k, hk, ?_⟩
    simp only [l54Piece, Complex.mem_reProdIm, mem_preimage, mem_singleton_iff]
    exact ⟨h1, hk'⟩
  · obtain ⟨k, hk, hk'⟩ := key h1
    refine ⟨2, by norm_num, k, hk, ?_⟩
    simp only [l54Piece, Complex.mem_reProdIm, mem_preimage, mem_singleton_iff]
    exact ⟨hk', h2⟩
  · obtain ⟨k, hk, hk'⟩ := key h2
    refine ⟨3, by norm_num, k, hk, ?_⟩
    simp only [l54Piece, Complex.mem_reProdIm, mem_preimage, mem_singleton_iff]
    exact ⟨h1, hk'⟩

lemma isConnected_l54Piece (u : ℂ) {h : ℝ} (hh : 0 ≤ h) (σ k : ℕ) :
    IsConnected (l54Piece u h σ k) := by
  obtain ⟨a, c, hac | hac⟩ := l54Piece_seg u h σ k <;> rw [hac]
  · exact isConnected_reProdIm (isConnected_Icc (by linarith)) isConnected_singleton
  · exact isConnected_reProdIm isConnected_singleton (isConnected_Icc (by linarith))

lemma le_diam_l54Piece (u : ℂ) {h : ℝ} (hh : 0 ≤ h) (σ : ℕ) {k : ℕ}
    (hk : ((k : ℝ) + 1) * h ≤ 1 / 20) : h ≤ Metric.diam (l54Piece u h σ k) := by
  have hb : Bornology.IsBounded (l54Piece u h σ k) :=
    (Metric.isBounded_closedBall.subset (sqBox_subset_closedBall u (by norm_num : (0 : ℝ) ≤ 1 / 20))).subset
      ((l54Piece_subset_frontier u hh σ hk).trans (isClosed_sqBox u _).frontier_subset)
  obtain ⟨a, c, hac | hac⟩ := l54Piece_seg u h σ k
  · have hp : (⟨a, c⟩ : ℂ) ∈ l54Piece u h σ k := by
      rw [hac]; exact ⟨⟨le_rfl, by simp only; linarith⟩, rfl⟩
    have hq : (⟨a + h, c⟩ : ℂ) ∈ l54Piece u h σ k := by
      rw [hac]; exact ⟨⟨by simp only; linarith, le_rfl⟩, rfl⟩
    refine le_trans ?_ (Metric.dist_le_diam_of_mem hb hq hp)
    have := Complex.abs_re_le_norm ((⟨a + h, c⟩ : ℂ) - ⟨a, c⟩)
    rw [dist_eq_norm]; refine le_trans (le_of_eq ?_) this
    simp [abs_of_nonneg hh]
  · have hp : (⟨c, a⟩ : ℂ) ∈ l54Piece u h σ k := by
      rw [hac]; exact ⟨rfl, ⟨le_rfl, by simp only; linarith⟩⟩
    have hq : (⟨c, a + h⟩ : ℂ) ∈ l54Piece u h σ k := by
      rw [hac]; exact ⟨rfl, ⟨by simp only; linarith, le_rfl⟩⟩
    refine le_trans ?_ (Metric.dist_le_diam_of_mem hb hq hp)
    have := Complex.abs_im_le_norm ((⟨c, a + h⟩ : ℂ) - ⟨c, a⟩)
    rw [dist_eq_norm]; refine le_trans (le_of_eq ?_) this
    simp [abs_of_nonneg hh]

end DZZ
end LQGMetric
