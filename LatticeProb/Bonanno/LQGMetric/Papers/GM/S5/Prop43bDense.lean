/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43bDense at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.Defs
import Mathlib.Data.Nat.Nth

/-!
# Condition (1) of `GeoIterateHyp` from a count of good scales (task P2-M2N2)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Prop 4.3, l. 2853–2862: Prop 3.5 gives at least `μ log_8 ε⁻¹` good scales
`8^{-k} 𝕣 ∈ [ε^{1+ν}𝕣, ε𝕣]`; condition (1) of Thm 4.2 asks for radii in `ℛ ∩ [ε^{1+ν}𝕣, ε𝕣]`
with consecutive ratios `≥ λ₄/λ₁`. Taking every other good scale (DV-B3: `μ/2` in Thm 4.2) gives
`⌊(μ/2) log_8 ε⁻¹⌋` radii with ratios `≥ 8² = 64 ≥ 16 = λ₄/λ₁`.

`exists_sparse_radii` : the elementary extraction (own elementary argument, no source needed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric.GM

/-- every other element of a finite set of naturals with at least `2n` elements -/
lemma exists_every_other {Q : ℕ → Prop} (n : ℕ) (hcard : 2 * n ≤ {k | Q k}.ncard) :
    ∃ kk : ℕ → ℕ, (∀ i < n, Q (kk i)) ∧ ∀ i, i + 1 < n → kk i + 2 ≤ kk (i + 1) := by
  by_cases hfin : {k | Q k}.Finite
  · have hc : {k | Q k}.ncard = hfin.toFinset.card := ncard_eq_toFinset_card _ hfin
    refine ⟨fun i => Nat.nth Q (2 * i), fun i hi => ?_, fun i hi => ?_⟩
    · exact Nat.nth_mem_of_lt_card hfin (by omega)
    · have h1 : Nat.nth Q (2 * i) < Nat.nth Q (2 * i + 1) :=
        Nat.nth_lt_nth_of_lt_card hfin (by omega) (by omega)
      have h2 : Nat.nth Q (2 * i + 1) < Nat.nth Q (2 * (i + 1)) :=
        Nat.nth_lt_nth_of_lt_card hfin (by omega) (by omega)
      beta_reduce
      omega
  · have hinf : {k | Q k}.Infinite := hfin
    refine ⟨fun i => Nat.nth Q (2 * i), fun i _ => Nat.nth_mem_of_infinite hinf _,
      fun i _ => ?_⟩
    have h1 : Nat.nth Q (2 * i) < Nat.nth Q (2 * i + 1) := (Nat.nth_lt_nth hinf).2 (by omega)
    have h2 : Nat.nth Q (2 * i + 1) < Nat.nth Q (2 * (i + 1)) := (Nat.nth_lt_nth hinf).2 (by omega)
    beta_reduce
    omega

/-- **condition (1) from a count of good scales**: if at least `μ log_8 ε⁻¹` scales
`8^{-k} ∈ [ε^{1+ν}, ε]` satisfy `Q`, and `8^{-k}R ∈ ℛ` for those, then there are
`⌊(μ/2) log_8 ε⁻¹⌋` radii in `ℛ ∩ [ε^{1+ν}R, εR]` with consecutive ratios `≥ 64` -/
theorem exists_sparse_radii {μ ν ε R : ℝ} (hR : 0 < R) {Q : ℕ → Prop}
    (hcount : μ * Real.logb 8 ε⁻¹ ≤ scaleCount ε ν Q) (Rad : Set ℝ)
    (hRad : ∀ k, Q k → ε ^ (1 + ν) ≤ (8 : ℝ)⁻¹ ^ k → (8 : ℝ)⁻¹ ^ k ≤ ε →
      (8 : ℝ)⁻¹ ^ k * R ∈ Rad) :
    ∃ rr : ℕ → ℝ, (∀ k < ⌊μ / 2 * Real.logb 8 ε⁻¹⌋₊,
      rr k ∈ Icc (ε ^ (1 + ν) * R) (ε * R) ∧ rr k ∈ Rad) ∧
      ∀ k, k + 1 < ⌊μ / 2 * Real.logb 8 ε⁻¹⌋₊ → 64 ≤ rr k / rr (k + 1) := by
  set n := ⌊μ / 2 * Real.logb 8 ε⁻¹⌋₊
  set Q' : ℕ → Prop := fun k => ε ^ (1 + ν) ≤ (8 : ℝ)⁻¹ ^ k ∧ (8 : ℝ)⁻¹ ^ k ≤ ε ∧ Q k
  have hcard : 2 * n ≤ {k | Q' k}.ncard := by
    by_cases hn : n = 0
    · rw [hn]; exact Nat.zero_le _
    have hpos : 0 < μ / 2 * Real.logb 8 ε⁻¹ := by
      by_contra hc
      exact hn (Nat.floor_eq_zero.2 (lt_of_le_of_lt (not_lt.1 hc) one_pos))
    have h1 : (n : ℝ) ≤ μ / 2 * Real.logb 8 ε⁻¹ := Nat.floor_le hpos.le
    have h2 : ((2 * n : ℕ) : ℝ) ≤ ({k | Q' k}.ncard : ℝ) := by
      have e : ({k | Q' k}.ncard : ℝ) = (scaleCount ε ν Q : ℝ) := rfl
      push_cast
      rw [e]
      linarith
    exact_mod_cast h2
  obtain ⟨kk, hkQ, hkgap⟩ := exists_every_other n hcard
  refine ⟨fun i => (8 : ℝ)⁻¹ ^ kk i * R, fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hkQ i hi
    exact ⟨⟨mul_le_mul_of_nonneg_right h1 hR.le, mul_le_mul_of_nonneg_right h2 hR.le⟩,
      hRad _ h3 h1 h2⟩
  · have hg := hkgap i hi
    obtain ⟨d, hd⟩ : ∃ d, kk (i + 1) = kk i + 2 + d := ⟨kk (i + 1) - (kk i + 2), by omega⟩
    simp only
    rw [hd, pow_add, pow_add]
    have h8 : (0 : ℝ) < (8 : ℝ)⁻¹ ^ kk i := by positivity
    have h8d : (0 : ℝ) < (8 : ℝ)⁻¹ ^ d := by positivity
    have hd1 : (8 : ℝ)⁻¹ ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    rw [le_div_iff₀ (by positivity)]
    have : 64 * ((8 : ℝ)⁻¹ ^ kk i * (8 : ℝ)⁻¹ ^ 2 * (8 : ℝ)⁻¹ ^ d * R) =
        (8 : ℝ)⁻¹ ^ kk i * R * (8 : ℝ)⁻¹ ^ d := by ring
    rw [this]
    exact mul_le_of_le_one_right (by positivity) hd1

end LQGMetric.GM
