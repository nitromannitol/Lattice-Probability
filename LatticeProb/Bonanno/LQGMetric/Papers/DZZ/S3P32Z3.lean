/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32Z3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32Z2

/-!
# `Φ^W_{B',δ,r} ≤ λ` from the masses of DZZ's corner balls (D102 P-4bW, step (a))

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1131–1139): the `4ε/t` balls of radius `ts` at the grid
corners on `∂B'_i` cover `∂B'_i`; if each has mass `≤ δ²` then `Φ_{B'_i,δ} ≤ 4ε/t ≤ λ`. At `μIn`
(D102 §2) only the corners not on `∂𝕍` are used, and `PhiLeW` (the cover of `∂B' ∩ 𝕍_{−r}`) follows:

* `cornerIdx B' ℓ`: the indices of the level-`(n+ℓ)` grid points on `∂B'` (`≤ 4 (2^ℓ + 1)`);
* **`phiLeW_of_corner_mass`**: if every ball of radius `2^{-(n+ℓ)}` at a grid point of `B'` not on
  `∂𝕍` has `μ`-mass `≤ δ²`, then `PhiLeW μ δ r B' λ` for `λ ≥ 4 (2^ℓ + 1)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- the indices `(m₁, m₂)` of the level-`(n+ℓ)` grid points on `∂B'` -/
def cornerIdx (B' : DyBox) (ℓ : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (2 ^ ℓ + 1)).image (fun i => (B'.j * 2 ^ ℓ + i, B'.k * 2 ^ ℓ)) ∪
    (Finset.range (2 ^ ℓ + 1)).image (fun i => (B'.j * 2 ^ ℓ + i, B'.k * 2 ^ ℓ + 2 ^ ℓ)) ∪
    (Finset.range (2 ^ ℓ + 1)).image (fun i => (B'.j * 2 ^ ℓ, B'.k * 2 ^ ℓ + i)) ∪
    (Finset.range (2 ^ ℓ + 1)).image (fun i => (B'.j * 2 ^ ℓ + 2 ^ ℓ, B'.k * 2 ^ ℓ + i))

lemma card_cornerIdx_le (B' : DyBox) (ℓ : ℕ) : (cornerIdx B' ℓ).card ≤ 4 * (2 ^ ℓ + 1) := by
  unfold cornerIdx
  refine (Finset.card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right ((Finset.card_union_le _ _).trans (Nat.add_le_add_right
    (Finset.card_union_le _ _) _)) _).trans ?_
  have h := fun f : ℕ → ℕ × ℕ =>
    (Finset.card_image_le (s := Finset.range (2 ^ ℓ + 1)) (f := f)).trans_eq
      (Finset.card_range _)
  linarith [h (fun i => (B'.j * 2 ^ ℓ + i, B'.k * 2 ^ ℓ)),
    h (fun i => (B'.j * 2 ^ ℓ + i, B'.k * 2 ^ ℓ + 2 ^ ℓ)),
    h (fun i => (B'.j * 2 ^ ℓ, B'.k * 2 ^ ℓ + i)),
    h (fun i => (B'.j * 2 ^ ℓ + 2 ^ ℓ, B'.k * 2 ^ ℓ + i))]

/-- the grid point found by `exists_corner_ball` is in `cornerIdx` -/
lemma mem_cornerIdx_of (B' : DyBox) (ℓ : ℕ) {m₁ m₂ : ℕ}
    (hbox : (⟨m₁ * (2⁻¹ : ℝ) ^ (B'.n + ℓ), m₂ * (2⁻¹ : ℝ) ^ (B'.n + ℓ)⟩ : ℂ) ∈ B'.closedBox)
    (hedge : (m₁ : ℝ) * (2⁻¹ : ℝ) ^ (B'.n + ℓ) = B'.j * B'.side ∨
        (m₁ : ℝ) * (2⁻¹ : ℝ) ^ (B'.n + ℓ) = (B'.j + 1) * B'.side ∨
        (m₂ : ℝ) * (2⁻¹ : ℝ) ^ (B'.n + ℓ) = B'.k * B'.side ∨
        (m₂ : ℝ) * (2⁻¹ : ℝ) ^ (B'.n + ℓ) = (B'.k + 1) * B'.side) :
    (m₁, m₂) ∈ cornerIdx B' ℓ := by
  set h : ℝ := (2⁻¹ : ℝ) ^ (B'.n + ℓ) with hhdef
  have hh : 0 < h := by positivity
  have hside : B'.side = (2 : ℝ) ^ ℓ * h := side_eq_pow_mul_Z2 B'.n ℓ
  obtain ⟨c1, c2, c3, c4⟩ := hbox
  simp only at c1 c2 c3 c4
  -- integer forms
  have key : ∀ {a b : ℕ}, (a : ℝ) * h ≤ (b : ℝ) * h → a ≤ b := fun hab => by
    exact_mod_cast le_of_mul_le_mul_right hab hh
  have keyeq : ∀ {a b : ℕ}, (a : ℝ) * h = (b : ℝ) * h → a = b := fun hab => by
    exact_mod_cast mul_right_cancel₀ hh.ne' hab
  have ej : (B'.j : ℝ) * B'.side = ((B'.j * 2 ^ ℓ : ℕ) : ℝ) * h := by rw [hside]; push_cast; ring
  have ej1 : ((B'.j : ℝ) + 1) * B'.side = ((B'.j * 2 ^ ℓ + 2 ^ ℓ : ℕ) : ℝ) * h := by
    rw [hside]; push_cast; ring
  have ek : (B'.k : ℝ) * B'.side = ((B'.k * 2 ^ ℓ : ℕ) : ℝ) * h := by rw [hside]; push_cast; ring
  have ek1 : ((B'.k : ℝ) + 1) * B'.side = ((B'.k * 2 ^ ℓ + 2 ^ ℓ : ℕ) : ℝ) * h := by
    rw [hside]; push_cast; ring
  rw [ej] at c1; rw [ej1] at c2; rw [ek] at c3; rw [ek1] at c4
  have i1 := key c1; have i2 := key c2; have i3 := key c3; have i4 := key c4
  unfold cornerIdx
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
  rcases hedge with e | e | e | e
  · rw [ej] at e; have := keyeq e
    left; right; exact ⟨m₂ - B'.k * 2 ^ ℓ, by omega, by omega, by omega⟩
  · rw [ej1] at e; have := keyeq e
    right; exact ⟨m₂ - B'.k * 2 ^ ℓ, by omega, by omega, by omega⟩
  · rw [ek] at e; have := keyeq e
    left; left; left; exact ⟨m₁ - B'.j * 2 ^ ℓ, by omega, by omega, by omega⟩
  · rw [ek1] at e; have := keyeq e
    left; left; right; exact ⟨m₁ - B'.j * 2 ^ ℓ, by omega, by omega, by omega⟩

open Classical in
/-- **DZZ l. 1131–1139 at `μIn`** (deterministic): masses of the corner balls `≤ δ²` give
`Φ^W_{B',δ,r} ≤ λ`. -/
theorem phiLeW_of_corner_mass {μ : Measure ℂ} {δ r lam : ℝ} (B' : DyBox) (ℓ : ℕ)
    (hn : 1 ≤ B'.n + ℓ) (hr : 0 < r)
    (hmass : ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → m₁ + 1 ≤ 2 ^ (B'.n + ℓ) → 1 ≤ m₂ → m₂ + 1 ≤ 2 ^ (B'.n + ℓ) →
      (⟨m₁ * (2⁻¹ : ℝ) ^ (B'.n + ℓ), m₂ * (2⁻¹ : ℝ) ^ (B'.n + ℓ)⟩ : ℂ) ∈ B'.closedBox →
      ((m₁ : ℝ) * (2⁻¹ : ℝ) ^ (B'.n + ℓ) = B'.j * B'.side ∨
        (m₁ : ℝ) * (2⁻¹ : ℝ) ^ (B'.n + ℓ) = (B'.j + 1) * B'.side ∨
        (m₂ : ℝ) * (2⁻¹ : ℝ) ^ (B'.n + ℓ) = B'.k * B'.side ∨
        (m₂ : ℝ) * (2⁻¹ : ℝ) ^ (B'.n + ℓ) = (B'.k + 1) * B'.side) →
      μ (Metric.ball (⟨m₁ * (2⁻¹ : ℝ) ^ (B'.n + ℓ), m₂ * (2⁻¹ : ℝ) ^ (B'.n + ℓ)⟩ : ℂ)
        ((2⁻¹ : ℝ) ^ (B'.n + ℓ))) ≤ ENNReal.ofReal (δ ^ 2))
    (hlam : (4 * (2 ^ ℓ + 1) : ℝ) ≤ lam) : PhiLeW μ δ r B' lam := by
  set h : ℝ := (2⁻¹ : ℝ) ^ (B'.n + ℓ) with hhdef
  set N : ℕ := 2 ^ (B'.n + ℓ)
  set I := (cornerIdx B' ℓ).filter (fun p => 1 ≤ p.1 ∧ p.1 + 1 ≤ N ∧ 1 ≤ p.2 ∧ p.2 + 1 ≤ N ∧
    (⟨p.1 * h, p.2 * h⟩ : ℂ) ∈ B'.closedBox ∧
    ((p.1 : ℝ) * h = B'.j * B'.side ∨ (p.1 : ℝ) * h = (B'.j + 1) * B'.side ∨
      (p.2 : ℝ) * h = B'.k * B'.side ∨ (p.2 : ℝ) * h = (B'.k + 1) * B'.side))
  set S : Finset (ℂ × ℝ) := I.image fun p => ((⟨p.1 * h, p.2 * h⟩ : ℂ), h)
  have hcov : frontier B'.closedBox ∩ dzzVIn r ⊆ ⋃ p ∈ S, Metric.ball p.1 p.2 := by
    intro z hz
    obtain ⟨m₁, m₂, a1, a2, a3, a4, hbox, hedge, hball⟩ := exists_corner_ball B' ℓ hn hr hz
    have hI : (m₁, m₂) ∈ I := Finset.mem_filter.2
      ⟨mem_cornerIdx_of B' ℓ hbox hedge, a1, a2, a3, a4, hbox, hedge⟩
    simp only [mem_iUnion, exists_prop]
    exact ⟨_, Finset.mem_image_of_mem _ hI, hball⟩
  have hmS : ∀ p ∈ S, μ (Metric.ball p.1 p.2) ≤ ENNReal.ofReal (δ ^ 2) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨-, b1, b2, b3, b4, b5, b6⟩ := Finset.mem_filter.1 hq
    exact hmass q.1 q.2 b1 b2 b3 b4 b5 b6
  have hcard : S.card ≤ 4 * (2 ^ ℓ + 1) :=
    (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans (card_cornerIdx_le B' ℓ)
  have hle : cellPhiW μ δ r B' ≤ (S.card : ℕ∞) :=
    iInf_le_of_le S (iInf_le_of_le hcov (iInf_le_of_le hmS le_rfl))
  have hfin : cellPhiW μ δ r B' ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hle
  refine ⟨(cellPhiW μ δ r B').toNat, (ENat.coe_toNat hfin).symm, ?_⟩
  have h1 : (cellPhiW μ δ r B').toNat ≤ S.card := by
    have := ENat.toNat_le_toNat hle (ENat.coe_ne_top _)
    simpa using this
  have h2 : ((cellPhiW μ δ r B').toNat : ℝ) ≤ 4 * (2 ^ ℓ + 1) := by
    have : (cellPhiW μ δ r B').toNat ≤ 4 * (2 ^ ℓ + 1) := h1.trans hcard
    exact_mod_cast this
  linarith

end DZZ
end LQGMetric
