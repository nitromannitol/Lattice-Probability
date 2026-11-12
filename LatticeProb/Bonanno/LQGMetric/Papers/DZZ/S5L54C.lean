/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L54C at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54B

/-!
# DZZ Lemma 5.4 from the point-to-segment bound (P2-DZZ54)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, Lemma 5.4
(`lem-exponent-point-to-boundary`, statement l. 2299–2304, proof l. 2530–2578).

DZZ's proof has two steps.
1. (eq-point-to-segment), l. 2545–2550: for fixed small `ι` and all small `δ`, every segment
   `L_δ ⊆ ∂𝕍̄_u` of length in `[δ^{2ι}/2, δ^{2ι}]` has
   `E log min_{x ∈ L_δ} D̄_δ(u,x) ≥ (χ − 2ι) log δ⁻¹`. The proof (l. 2551–2568) is by contradiction,
   gluing geodesics and four short RSW crossings (Fig. glue) with the scaling argument of
   (eq-z-open). Here it is the hypothesis `DZZLem54Seg` (open node).
2. l. 2570–2577: `∂𝕍̄_u` is the union of `≈ 4δ^{−2ι}` such segments; Proposition 3.17 applied to the
   pairs `(u, L_δ)` and a union bound give the lower bound. This file proves step 2
   (`dzzLem54_lower`), with Proposition 3.17 (`DZZProp317`, at the walled measure of
   `𝕍_{u,1/10}`, DZZ Remark 5.2) as hypothesis.

Two technical points of the Lean proof (the argument is DZZ's):
* Proposition 3.17 is a statement about one admissible *sequence* `(A_δ, B_δ)`, with a threshold
  `δ₀` that depends on the sequence. To get a bound that holds uniformly over the `4n(δ)` segments,
  we apply it to the sequence `B_δ =` the segment with the largest deviation probability at
  scale `δ` (`idx`), and bound the union by `4n(δ)` times that probability.
* DZZ's last step ("this implies `E log min ≥ (χ − 2ι − Cι^{1/2}) log δ⁻¹`") goes from a bound
  that holds with high probability to a bound on the mean. We do it with Proposition 3.17 for the
  pair `(u, ∂𝕍̄_u)`: an `ω` in both good events gives the mean bound. This needs no
  integrability hypothesis.
We choose the concentration level `ι' = min(ε/4, 1/2)` first and then `ι ≤ cι'²/4`. DZZ do the
reverse, with `ι' = Cι^{1/2}`; the two choices are equivalent.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

variable {Ω : Type*} [MeasurableSpace Ω]

lemma eventually_rpow_lt {p r : ℝ} (hp : 0 < p) (hr : 0 < r) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ p < r := by
  have h : Tendsto (fun δ : ℝ => δ ^ p) (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow hp.ne'] using (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto
  exact (tendsto_nhdsWithin_of_tendsto_nhds h).eventually (Iio_mem_nhds hr)

lemma succ_mul_div_le {k n : ℕ} (hk : k < n) : ((k : ℝ) + 1) * (1 / 20 / n) ≤ 1 / 20 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
  rw [show ((k : ℝ) + 1) * (1 / 20 / n) = 1 / 20 * (((k : ℝ) + 1) / n) by ring]
  exact mul_le_of_le_one_right (by norm_num) ((div_le_one hn0).mpr this)

/-- The number `n = ⌈(1/20) δ^{−2ι}⌉` of segments per side and its properties. -/
lemma l54_count {ι ξ δ : ℝ} (hδ : 0 < δ) (h1 : δ ^ (2 * ι) < 1 / 20)
    (h2 : δ ^ (ξ - 2 * ι) < 1 / 2) {n : ℕ} (hn : n = ⌈1 / 20 * (δ ^ (2 * ι))⁻¹⌉₊) :
    1 ≤ n ∧ δ ^ (2 * ι) / 2 ≤ 1 / 20 / n ∧ 1 / 20 / n ≤ δ ^ (2 * ι) ∧
      (4 * n : ℝ) ≤ (δ ^ (2 * ι))⁻¹ ∧ δ ^ ξ ≤ 1 / 20 / n := by
  set y := δ ^ (2 * ι) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hδ _
  set X := 1 / 20 * y⁻¹ with hX
  have hXy : X * y = 1 / 20 := by rw [hX]; field_simp
  have hX1 : 1 < X := by
    by_contra hc; push_neg at hc
    nlinarith
  have hnX : X ≤ n := hn ▸ Nat.le_ceil X
  have hnX' : (n : ℝ) < X + 1 := hn ▸ Nat.ceil_lt_add_one (by linarith)
  have hn0 : (0 : ℝ) < n := by linarith
  have hyinv : y⁻¹ = 20 * X := by rw [hX]; ring
  refine ⟨by exact_mod_cast (show (1 : ℝ) ≤ n by linarith), ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hn0]
    have : y / 2 * n ≤ y / 2 * (2 * X) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  · rw [div_le_iff₀ hn0]
    have : y * X ≤ y * n := mul_le_mul_of_nonneg_left hnX hy0.le
    linarith
  · rw [hyinv]; linarith
  · have hsplit : δ ^ ξ = δ ^ (ξ - 2 * ι) * y := by
      rw [hy, ← Real.rpow_add hδ]; ring_nf
    have hy2 : y / 2 ≤ 1 / 20 / n := by
      rw [le_div_iff₀ hn0]
      have : y / 2 * n ≤ y / 2 * (2 * X) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    rw [hsplit]
    nlinarith

/-- The sequences used with Proposition 3.17: `A_δ = {u}`, and `B_δ` a subset of `∂𝕍_{u,1/20}`
for `δ < δ₁`, the point `x₀ = l54Pt u` otherwise; these are `ξ`-admissible for `ξ ≤ 1/40`. -/
lemma l54_isXiAdmissible {ξ δ₁ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 40) {u : ℂ} (hu : u ∈ dzzVbar)
    (B : ℝ → Set ℂ) (hB : ∀ δ ∈ Ioo (0 : ℝ) 1, δ < δ₁ →
      B δ ⊆ frontier (sqBox u (1 / 20)) ∧ IsXiAdmissibleSet ξ δ (B δ)) :
    IsXiAdmissible ξ (fun _ => {u}) (fun δ => if δ < δ₁ then B δ else {l54Pt u}) := by
  have hF : frontier (sqBox u (1 / 20)) ⊆ dzzVXi ξ := fun z hz =>
    mem_dzzVXi_of_mem_sqBox hu ((isClosed_sqBox u _).frontier_subset hz) le_rfl hξ.le
      (by linarith)
  have hu0 : ∀ l : ℝ, 0 ≤ l → u ∈ sqBox u l := fun l hl =>
    ⟨by rw [sub_self, abs_zero]; linarith, by rw [sub_self, abs_zero]; linarith⟩
  have huF : ∀ b ∈ frontier (sqBox u (1 / 20)), ξ ≤ dist u b := by
    intro b hb
    have he := edge_of_mem_frontier_sqBox (by norm_num) hb
    norm_num at he
    have := dist_ge_of_edge (α := 0) (hu0 _ (by norm_num)) he
    norm_num at this
    linarith
  have hx0 := l54Pt_mem_frontier u
  refine ⟨fun _ _ => singleton_subset_iff.mpr
      (mem_dzzVXi_of_mem_sqBox hu (hu0 _ (by norm_num)) (le_refl (1 / 20)) hξ.le (by linarith)),
    fun δ hδ => ?_, fun _ _ => Or.inl ⟨u, rfl⟩, fun δ hδ => ?_, fun δ hδ a ha b hb => ?_⟩
  · split_ifs with h
    · exact (hB δ hδ h).1.trans hF
    · exact singleton_subset_iff.mpr (hF hx0)
  · split_ifs with h
    · exact (hB δ hδ h).2
    · exact Or.inl ⟨_, rfl⟩
  · rw [mem_singleton_iff.mp ha]
    split_ifs at hb with h
    · exact huF b ((hB δ hδ h).1 hb)
    · rw [mem_singleton_iff.mp hb]; exact huF _ hx0

end DZZ
end LQGMetric
