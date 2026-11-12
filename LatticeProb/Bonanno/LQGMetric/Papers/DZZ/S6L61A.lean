/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S6L61A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Adapt

/-!
# DZZ Lemma 6.1, lower half: boundary segments of a box (P2-DZZ61L)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 6.1 (l. 2598–2603):
"it suffices to show that for any fixed `ι > 0` and any segment `L_δ ⊆ ∂𝕍̄_{u,α}` with length in
`[δ^{2ι}/2, δ^{2ι}]` …" (and l. 2575: the minimum over `∂𝕍̄_u` is the minimum over
`O(δ^{-2ι})` disjoint segments). This file has the deterministic geometry:

* `IsBdrySeg c a ℓ L`: `L` is a segment contained in `∂𝕍_{c,a}` of length in `[ℓ/2, ℓ]`
  (a segment inside the boundary of a square of side `a` is a horizontal or vertical piece of a side,
  `Icc s t ×ℂ {y}` or `{y} ×ℂ Icc s t`);
* `bdrySeg c a n j k`: the `k`-th of the `n` equal pieces of the `j`-th side of `∂𝕍_{c,a}`;
* `frontier_sqBox_subset_iUnion_bdrySeg`: these `4n` pieces cover `∂𝕍_{c,a}`;
* `isBdrySeg_bdrySeg`, `IsBdrySeg.isConnected`, `IsBdrySeg.diam_ge`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- `L` is a segment of length in `[ℓ/2, ℓ]` contained in the boundary of the box `𝕍_{c,a}`
(DZZ l. 2601). -/
def IsBdrySeg (c : ℂ) (a ℓ : ℝ) (L : Set ℂ) : Prop :=
  L ⊆ frontier (sqBox c a) ∧ ∃ s t y : ℝ, (L = Icc s t ×ℂ {y} ∨ L = {y} ×ℂ Icc s t) ∧
    ℓ / 2 ≤ t - s ∧ t - s ≤ ℓ

/-- The `k`-th of the `n` equal pieces of the `j`-th side of `∂𝕍_{c,a}` (bottom, left, top,
right). -/
def bdrySeg (c : ℂ) (a : ℝ) (n : ℕ) (j : Fin 4) (k : ℕ) : Set ℂ :=
  ![Icc (c.re - a / 2 + k * (a / n)) (c.re - a / 2 + (k + 1) * (a / n)) ×ℂ {c.im - a / 2},
    {c.re - a / 2} ×ℂ Icc (c.im - a / 2 + k * (a / n)) (c.im - a / 2 + (k + 1) * (a / n)),
    Icc (c.re - a / 2 + k * (a / n)) (c.re - a / 2 + (k + 1) * (a / n)) ×ℂ {c.im + a / 2},
    {c.re + a / 2} ×ℂ Icc (c.im - a / 2 + k * (a / n)) (c.im - a / 2 + (k + 1) * (a / n))] j

lemma exists_Icc_piece {lo h x : ℝ} {n : ℕ} (hn : 0 < n) (hh : 0 < h)
    (hx : x ∈ Icc lo (lo + n * h)) : ∃ k < n, x ∈ Icc (lo + k * h) (lo + (k + 1) * h) := by
  obtain ⟨h1, h2⟩ := hx
  have hq : 0 ≤ (x - lo) / h := div_nonneg (by linarith) hh.le
  by_cases hk : ⌊(x - lo) / h⌋₊ < n
  · refine ⟨_, hk, ?_, ?_⟩
    · have := Nat.floor_le hq
      rw [le_div_iff₀ hh] at this; linarith
    · have := Nat.lt_floor_add_one ((x - lo) / h)
      rw [div_lt_iff₀ hh] at this; linarith
  · push_neg at hk
    have hnx : (n : ℝ) ≤ (x - lo) / h :=
      (Nat.cast_le.mpr hk).trans (Nat.floor_le hq)
    rw [le_div_iff₀ hh] at hnx
    refine ⟨n - 1, Nat.sub_lt hn one_pos, ?_, ?_⟩
    · have : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
      nlinarith
    · rw [Nat.cast_sub (by omega), Nat.cast_one, sub_add_cancel]; linarith

lemma Icc_piece_subset {lo h : ℝ} {n k : ℕ} (hk : k < n) (hh : 0 ≤ h) :
    Icc (lo + k * h) (lo + (k + 1) * h) ⊆ Icc lo (lo + n * h) := by
  have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
  exact Icc_subset_Icc (by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (by nlinarith)

lemma frontier_sqBox_subset_iUnion_bdrySeg (c : ℂ) {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) :
    frontier (sqBox c a) ⊆ ⋃ j : Fin 4, ⋃ k : Fin n, bdrySeg c a n j k := by
  have hh : 0 < a / n := div_pos ha (by exact_mod_cast hn)
  have hnh : ∀ lo : ℝ, lo + n * (a / n) = lo + a := fun lo => by
    rw [mul_div_cancel₀ _ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)]
  have hI : ∀ x lo : ℝ, x ∈ Icc lo (lo + a) →
      ∃ k : Fin n, x ∈ Icc (lo + k * (a / n)) (lo + (k + 1) * (a / n)) := fun x lo hx => by
    rw [← hnh lo] at hx
    obtain ⟨k, hk, hx⟩ := exists_Icc_piece hn hh hx
    exact ⟨⟨k, hk⟩, hx⟩
  have hre : ∀ x : ℝ, x ∈ Icc (c.re - a / 2) (c.re + a / 2) → x ∈ Icc (c.re - a / 2) (c.re - a / 2 + a) :=
    fun x hx => by rwa [show c.re - a / 2 + a = c.re + a / 2 by ring]
  have him : ∀ x : ℝ, x ∈ Icc (c.im - a / 2) (c.im + a / 2) → x ∈ Icc (c.im - a / 2) (c.im - a / 2 + a) :=
    fun x hx => by rwa [show c.im - a / 2 + a = c.im + a / 2 by ring]
  intro z hz
  rw [frontier_sqBox ha] at hz
  simp only [mem_iUnion]
  rcases hz with ((hz | hz) | hz) | hz <;> rw [Complex.mem_reProdIm] at hz
  · obtain ⟨k, hk⟩ := hI _ _ (hre _ hz.1)
    exact ⟨0, k, by simp only [bdrySeg]; exact Complex.mem_reProdIm.mpr ⟨hk, hz.2⟩⟩
  · obtain ⟨k, hk⟩ := hI _ _ (him _ hz.2)
    exact ⟨1, k, by simp only [bdrySeg]; exact Complex.mem_reProdIm.mpr ⟨hz.1, hk⟩⟩
  · obtain ⟨k, hk⟩ := hI _ _ (hre _ hz.1)
    exact ⟨2, k, by simp only [bdrySeg]; exact Complex.mem_reProdIm.mpr ⟨hk, hz.2⟩⟩
  · obtain ⟨k, hk⟩ := hI _ _ (him _ hz.2)
    exact ⟨3, k, by simp only [bdrySeg]; exact Complex.mem_reProdIm.mpr ⟨hz.1, hk⟩⟩

lemma isBdrySeg_bdrySeg (c : ℂ) {a ℓ : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n)
    (hℓ1 : ℓ / 2 ≤ a / n) (hℓ2 : a / n ≤ ℓ) (j : Fin 4) {k : ℕ} (hk : k < n) :
    IsBdrySeg c a ℓ (bdrySeg c a n j k) := by
  have hh : 0 ≤ a / n := div_nonneg ha.le (Nat.cast_nonneg n)
  have hnh : ∀ lo : ℝ, lo + n * (a / n) = lo + a := fun lo => by
    rw [mul_div_cancel₀ _ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)]
  have hsub : ∀ lo : ℝ, Icc (lo + k * (a / n)) (lo + (k + 1) * (a / n)) ⊆ Icc lo (lo + a) :=
    fun lo => by rw [← hnh lo]; exact Icc_piece_subset hk hh
  have hlen : ∀ lo : ℝ, lo + (k + 1) * (a / n) - (lo + k * (a / n)) = a / n := fun lo => by ring
  have e1 : c.re - a / 2 + a = c.re + a / 2 := by ring
  have e2 : c.im - a / 2 + a = c.im + a / 2 := by ring
  unfold IsBdrySeg
  rw [frontier_sqBox ha]
  fin_cases j <;> simp only [bdrySeg, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons]
  · refine ⟨fun z hz => Or.inl (Or.inl (Or.inl ?_)), _, _, _, Or.inl rfl, by rw [hlen]; exact hℓ1,
      by rw [hlen]; exact hℓ2⟩
    replace hz := Complex.mem_reProdIm.mp hz; rw [Complex.mem_reProdIm]
    exact ⟨by rw [← e1]; exact hsub _ hz.1, hz.2⟩
  · refine ⟨fun z hz => Or.inl (Or.inl (Or.inr ?_)), _, _, _, Or.inr rfl, by rw [hlen]; exact hℓ1,
      by rw [hlen]; exact hℓ2⟩
    replace hz := Complex.mem_reProdIm.mp hz; rw [Complex.mem_reProdIm]
    exact ⟨hz.1, by rw [← e2]; exact hsub _ hz.2⟩
  · refine ⟨fun z hz => Or.inl (Or.inr ?_), _, _, _, Or.inl rfl, by rw [hlen]; exact hℓ1,
      by rw [hlen]; exact hℓ2⟩
    replace hz := Complex.mem_reProdIm.mp hz; rw [Complex.mem_reProdIm]
    exact ⟨by rw [← e1]; exact hsub _ hz.1, hz.2⟩
  · refine ⟨fun z hz => Or.inr ?_, _, _, _, Or.inr rfl, by rw [hlen]; exact hℓ1,
      by rw [hlen]; exact hℓ2⟩
    replace hz := Complex.mem_reProdIm.mp hz; rw [Complex.mem_reProdIm]
    exact ⟨hz.1, by rw [← e2]; exact hsub _ hz.2⟩

lemma IsBdrySeg.subset_sqBox {c : ℂ} {a ℓ : ℝ} {L : Set ℂ} (h : IsBdrySeg c a ℓ L) :
    L ⊆ sqBox c a :=
  h.1.trans (isClosed_sqBox c a).frontier_subset

lemma IsBdrySeg.isConnected {c : ℂ} {a ℓ : ℝ} {L : Set ℂ} (h : IsBdrySeg c a ℓ L)
    (hℓ : 0 ≤ ℓ) : IsConnected L := by
  obtain ⟨-, s, t, y, hL, h1, -⟩ := h
  have hI : IsConnected (Icc s t) := isConnected_Icc (by linarith)
  rcases hL with rfl | rfl
  · exact isConnected_reProdIm hI isConnected_singleton
  · exact isConnected_reProdIm isConnected_singleton hI

lemma IsBdrySeg.diam_ge {c : ℂ} {a ℓ : ℝ} {L : Set ℂ} (h : IsBdrySeg c a ℓ L) (ha : 0 ≤ a)
    (hℓ : 0 ≤ ℓ) :
    ℓ / 2 ≤ Metric.diam L := by
  have hb : Bornology.IsBounded L :=
    (Metric.isBounded_closedBall.subset (sqBox_subset_closedBall c ha)).subset h.subset_sqBox
  obtain ⟨-, s, t, y, hL, h1, -⟩ := h
  have hst : s ≤ t := by linarith
  rcases hL with rfl | rfl
  · have hp : (⟨s, y⟩ : ℂ) ∈ Icc s t ×ℂ {y} :=
      Complex.mem_reProdIm.mpr ⟨⟨le_rfl, hst⟩, rfl⟩
    have hq : (⟨t, y⟩ : ℂ) ∈ Icc s t ×ℂ {y} :=
      Complex.mem_reProdIm.mpr ⟨⟨hst, le_rfl⟩, rfl⟩
    refine le_trans ?_ (Metric.dist_le_diam_of_mem hb hp hq)
    rw [Complex.dist_of_im_eq (show (⟨s, y⟩ : ℂ).im = (⟨t, y⟩ : ℂ).im from rfl), Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
    exact h1
  · have hp : (⟨y, s⟩ : ℂ) ∈ {y} ×ℂ Icc s t :=
      Complex.mem_reProdIm.mpr ⟨rfl, ⟨le_rfl, hst⟩⟩
    have hq : (⟨y, t⟩ : ℂ) ∈ {y} ×ℂ Icc s t :=
      Complex.mem_reProdIm.mpr ⟨rfl, ⟨hst, le_rfl⟩⟩
    refine le_trans ?_ (Metric.dist_le_diam_of_mem hb hp hq)
    rw [Complex.dist_of_re_eq (show (⟨y, s⟩ : ℂ).re = (⟨y, t⟩ : ℂ).re from rfl), Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
    exact h1

end DZZ
end LQGMetric
