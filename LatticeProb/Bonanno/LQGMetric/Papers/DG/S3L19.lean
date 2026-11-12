/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L19 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L19Det
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11

/-!
# DG Lemma 3.19 for a truncated-type field: the Peierls step (P2-DG105g)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.19 (`lem-annulus-perc`,
DG:1614–1660), the truncated bound (eqn-annulus-perc-truncated) (DG:1633–1636), at scale `s` and
offset `b` (D105 item 1, DV-D105-3).

DG's proof: (eqn-perc-prob') each `E_S^ε` has probability `≥ 1 − p` (L3.20 + translation
invariance, DG:1643–1646); `E_S^ε` is determined by `ĥ^tr|_{S(1)}` (condition 2 of `E_S^ε`,
DG:1642–1644), so the "same percolation-type argument" as for L3.11 (DG:1656) gives a closed
path of squares disconnecting `∂_in 𝒜_n` from `∂_out 𝒜_n` on which every `E_S^ε` occurs, outside
probability `a₀ e^{−a₁ n}`; then (DG:1650–1652) `D^ε(∂_in, ∂_out) ≥ ε^{−1/(d+ζ)}`.

Here the percolation argument is `perc_annulus_peierls` (Perc/AnnulusPeierls: enclosures of the
annulus `c₀ + 2 ≤ ‖z‖_∞ ≤ n − 2 + c₀`, `c₀ = ⌊n/2⌋`, `θ = 1/32`, independence at
`ℓ^∞`-distance `> 9`, `p = 32^{−100}`), and DG:1650–1652 is `dgLGDSet_ann_ge_of_enc`
(S3L19Det). The events `E z` are arbitrary events contained in condition 1 of DG's `E_S^ε`
(`goodAnn`), so that DG's condition 2 (locality, DG:1642) can be included by the caller.
Constants: `a₀ = 768`, `a₁ = log 2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `4 (2N + 1) (1/4)^{N − n + 1} ≤ 768 · 2^{−(m+4)}` for the annulus of `n = m + 4` -/
lemma l319_num (m : ℕ) :
    4 * (((2 * (m + 2 + (m + 4) / 2) + 1 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ (m + 1)) ≤
      768 * (2 : ℝ)⁻¹ ^ (m + 4) := by
  have hc : ((2 * (m + 2 + (m + 4) / 2) + 1 : ℕ) : ℝ) ≤ 48 * 2 ^ m := by
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have h2 := Nat.lt_two_pow_self (n := m)
    have : 2 * (m + 2 + (m + 4) / 2) + 1 ≤ 48 * 2 ^ m := by omega
    exact_mod_cast this
  have e1 : (1 / 4 : ℝ) ^ (m + 1) = (1 / 4) * ((2 : ℝ)⁻¹ ^ m * (2 : ℝ)⁻¹ ^ m) := by
    rw [← mul_pow, pow_succ]; norm_num; ring
  have e2 : (2 : ℝ)⁻¹ ^ m * 2 ^ m = 1 := by rw [← mul_pow]; norm_num
  have hp : 0 ≤ (2 : ℝ)⁻¹ ^ m * (2 : ℝ)⁻¹ ^ m := by positivity
  rw [e1, pow_add]
  calc 4 * (((2 * (m + 2 + (m + 4) / 2) + 1 : ℕ) : ℝ) * (1 / 4 * ((2 : ℝ)⁻¹ ^ m * (2 : ℝ)⁻¹ ^ m)))
      ≤ 4 * ((48 * 2 ^ m) * (1 / 4 * ((2 : ℝ)⁻¹ ^ m * (2 : ℝ)⁻¹ ^ m))) := by gcongr
    _ = 48 * ((2 : ℝ)⁻¹ ^ m * 2 ^ m) * (2 : ℝ)⁻¹ ^ m := by ring
    _ = 768 * ((2 : ℝ)⁻¹ ^ m * (2 : ℝ)⁻¹ ^ 4) := by rw [e2]; norm_num; ring

lemma percEnclosure_mono {n N : ℤ} {G G' : Set (ℤ × ℤ)} (h : PercEnclosure n N G)
    (hG : G ⊆ G') : PercEnclosure n N G' := by
  obtain ⟨U, hU, h1, h2, h3⟩ := h
  exact ⟨U, fun z hz => ⟨hG (hU z hz).1, (hU z hz).2⟩, h1, h2, h3⟩

/-- the Peierls bound for good enclosures of the annulus `c₀ + 2 ≤ ‖z‖_∞ ≤ n − 2 + c₀` of
`s𝒜_n + b` (`perc_annulus_peierls`, `θ = 1/32`, `r = 9`) for arbitrary site events -/
lemma l319_bad_le (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (E : ℤ × ℤ → Set Ω)
    (hgood : ∀ z, (∃ d, z ∈ annRect ((n / 2 + 2 : ℕ) : ℤ) ((n - 2 + n / 2 : ℕ) : ℤ) d) →
      P (E z)ᶜ ≤ (32⁻¹ : ℝ≥0∞) ^ 100)
    (hind : ∀ F : Finset (ℤ × ℤ),
      (∀ z ∈ F, ∃ d, z ∈ annRect ((n / 2 + 2 : ℕ) : ℤ) ((n - 2 + n / 2 : ℕ) : ℤ) d) →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar 9 x y) →
      P (⋂ x ∈ F, (E x)ᶜ) ≤ ∏ x ∈ F, P (E x)ᶜ) :
    P {ω | ¬ PercEnclosure ((n / 2 + 2 : ℕ) : ℤ) ((n - 2 + n / 2 : ℕ) : ℤ) {z | ω ∈ E z}} ≤
      ENNReal.ofReal (768 * (2 : ℝ)⁻¹ ^ n) := by
  rcases lt_or_ge n 4 with hn | hn
  · refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have : (2 : ℝ)⁻¹ ^ 3 ≤ (2 : ℝ)⁻¹ ^ n := pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (by omega)
    norm_num at this ⊢
    linarith
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  set B : ℤ × ℤ → Set Ω := fun z => (E z)ᶜ
  have hpeier := perc_annulus_peierls P ((m + 4) / 2 + 2) (m + 4 - 2 + (m + 4) / 2)
    (by omega) (by omega) B 9 (θ := (32⁻¹ : ℝ≥0∞)) (ε := (32⁻¹ : ℝ≥0∞) ^ 100)
    (by
      have h : (8 : ℝ≥0∞) * 32⁻¹ = ENNReal.ofReal (8 * 32⁻¹) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
      have h' : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ := by
        rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
      rw [h, h']
      exact ENNReal.ofReal_le_ofReal (by norm_num))
    (le_of_eq (by norm_num)) hgood hind
  have hsub : {ω | ¬ PercEnclosure (((m + 4) / 2 + 2 : ℕ) : ℤ) ((m + 4 - 2 + (m + 4) / 2 : ℕ) : ℤ)
        {z | ω ∈ E z}} ⊆
      {ω | ¬ PercEnclosure (((m + 4) / 2 + 2 : ℕ) : ℤ) ((m + 4 - 2 + (m + 4) / 2 : ℕ) : ℤ)
        {z | ω ∉ B z}} := by
    intro ω hω henc
    exact hω (percEnclosure_mono henc fun z hz => by simpa [B] using hz)
  refine (measure_mono hsub).trans (hpeier.trans ?_)
  have h8 : (8 * 32⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 4) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat,
      one_div]
    rw [show (32 : ℝ≥0∞) = 8 * 4 by norm_num, ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
      ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
  have hex : m + 4 - 2 + (m + 4) / 2 - ((m + 4) / 2 + 2) + 1 = m + 1 := by omega
  have hN : 2 * (m + 4 - 2 + (m + 4) / 2) + 1 = 2 * (m + 2 + (m + 4) / 2) + 1 := by omega
  rw [hex, hN, h8, ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_ofNat 4,
    ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := l319_num m
  push_cast at this ⊢
  exact this

/-- the enclosure event for the sites `c₀ + 2 ≤ ‖z‖_∞ ≤ n − 2 + c₀` gives the bound of DG:1652 -/
lemma l319_le_of_enc {μ : Measure ℂ} {ε s M : ℝ} (hs : 0 < s) (b : ℂ) (n : ℕ)
    {G : Set (ℤ × ℤ)} (hG : ∀ z ∈ G, goodAnn μ ε s b (n / 2 : ℕ) M z)
    (henc : PercEnclosure ((n / 2 + 2 : ℕ) : ℤ) ((n - 2 + n / 2 : ℕ) : ℤ) G) :
    ENNReal.ofReal M ≤ (dgLGDSet μ ε univ (annIn s b n) (frontier (annOut s b n)) : ℝ≥0∞) := by
  rcases lt_or_ge n 2 with hn | hn
  · -- degenerate: the inner radius exceeds the outer one, there is no enclosure
    exfalso
    obtain ⟨U, hU, ⟨z, hz⟩, -⟩ := henc
    obtain ⟨-, d, hzd, hd⟩ := hU z hz
    obtain ⟨h1, h2, h3, h4⟩ := hzd
    interval_cases n <;> cases d <;> simp [annDir] at hd <;> omega
  refine dgLGDSet_ann_ge_of_enc hs b n hG ?_
  have e1 : ((n / 2 + 2 : ℕ) : ℤ) = ((n / 2 : ℕ) : ℤ) + 2 := by push_cast; ring
  have e2 : ((n - 2 + n / 2 : ℕ) : ℤ) = (n : ℤ) - 2 + ((n / 2 : ℕ) : ℤ) := by omega
  rwa [e1, e2] at henc

end DG
end LQGMetric
