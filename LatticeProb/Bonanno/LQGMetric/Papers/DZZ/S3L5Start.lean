/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5Start at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinGood

/-!
# DZZ Lemma 3.5: the start and end pieces `ℂ_start`, `ℂ_end` (P2-DZZ3G)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1058–1066): for `A_δ = {u}`,
"applying (eq-B-good-Phi) of Lemma 3.7 to all dyadic boxes containing `u` with side length at
least `δ^{C_mc}` (so in total we apply (eq-B-good-Phi) `O(log δ⁻¹)` times), we see that with high
probability `D'_{γ,δ'}(u, ∂𝖢_large) ≤ δ^{-ι}(δ/δ')³` for all `𝖢 ∈ S_u`", where
`S_u = {𝖢 ∈ 𝒱_δ : u ∈ 𝖢_large}`. The boxes `B` of level `n` with `u ∈ B_large` are among the
`3 × 3` boxes around the level-`n` box of `u` (`clampBox`), so the union bound runs over
`9 ⌊C_mc log₂ δ⁻¹⌋` boxes (DZZ's "boxes containing `u`" read as "with `u ∈ B_large`", which is
what `S_u` needs).

* `startGood`: the event `∀ 𝖢 ∈ 𝒱_δ, u ∈ 𝖢_large → D'_{δ'}(u, ∂𝖢_large ∩ 𝕍) ≤ δ^{-ι}(δ/δ')³`.
* `l35_start_hp`: `P(startGood ∩ 𝓔_{δ,α})ᶜ ≤ δ^{ι/20} + P(𝓔_{δ,α}ᶜ)` for small `δ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-- The level-`n` box of column `min j (2ⁿ−1)` and row `min k (2ⁿ−1)`. -/
def clampBox (n j k : ℕ) : DyBox :=
  ⟨n, min j (2 ^ n - 1), min k (2 ^ n - 1), lt_of_le_of_lt (min_le_right _ _)
    (two_pow_sub_one_lt n), lt_of_le_of_lt (min_le_right _ _) (two_pow_sub_one_lt n)⟩

/-- A box `B` with `x ∈ B_large` has column within `1` of the column of `x`. -/
lemma idx_near_of_mem_largeBox {b : DyBox} {x : ℂ} (hx : x ∈ b.largeBox) (hxV : x ∈ dzzV) :
    idx b.n x.re ≤ b.j + 1 ∧ b.j ≤ idx b.n x.re + 1 ∧
      idx b.n x.im ≤ b.k + 1 ∧ b.k ≤ idx b.n x.im + 1 := by
  obtain ⟨hr, hi⟩ := hx
  obtain ⟨h0, h1, h2, h3⟩ := hxV
  have e : b.side * 2 ^ b.n = 1 := by unfold DyBox.side; exact pow_inv_mul_pow b.n
  obtain ⟨a1, a2⟩ := idx_bounds (n := b.n) h0 h1
  obtain ⟨c1, c2⟩ := idx_bounds (n := b.n) h2 h3
  have ar := abs_le.1 hr
  have ai := abs_le.1 hi
  have h2n : (0 : ℝ) ≤ 2 ^ b.n := by positivity
  have hre : (x.re - b.center.re) * 2 ^ b.n = x.re * 2 ^ b.n - (b.j + 1 / 2) * (b.side * 2 ^ b.n) := by
    simp only [DyBox.center]; ring
  have him : (x.im - b.center.im) * 2 ^ b.n = x.im * 2 ^ b.n - (b.k + 1 / 2) * (b.side * 2 ^ b.n) := by
    simp only [DyBox.center]; ring
  rw [e, mul_one] at hre him
  have r1 := mul_le_mul_of_nonneg_right ar.2 h2n
  have r2 := mul_le_mul_of_nonneg_right ar.1 h2n
  have i1 := mul_le_mul_of_nonneg_right ai.2 h2n
  have i2 := mul_le_mul_of_nonneg_right ai.1 h2n
  rw [e] at r1 i1
  rw [neg_mul, e] at r2 i2
  have q1 : (idx b.n x.re : ℝ) < b.j + 2 := by linarith
  have q2 : (b.j : ℝ) < idx b.n x.re + 2 := by linarith
  have q3 : (idx b.n x.im : ℝ) < b.k + 2 := by linarith
  have q4 : (b.k : ℝ) < idx b.n x.im + 2 := by linarith
  have n1 : idx b.n x.re < b.j + 2 := by exact_mod_cast q1
  have n2 : b.j < idx b.n x.re + 2 := by exact_mod_cast q2
  have n3 : idx b.n x.im < b.k + 2 := by exact_mod_cast q3
  have n4 : b.k < idx b.n x.im + 2 := by exact_mod_cast q4
  omega

lemma eq_clampBox_of_mem_largeBox {b : DyBox} {x : ℂ} (hx : x ∈ b.largeBox) (hxV : x ∈ dzzV) :
    ∃ ac : Fin 3 × Fin 3, b = clampBox b.n (idx b.n x.re - 1 + ac.1) (idx b.n x.im - 1 + ac.2) := by
  obtain ⟨n1, n2, n3, n4⟩ := idx_near_of_mem_largeBox hx hxV
  refine ⟨(⟨b.j - (idx b.n x.re - 1), by omega⟩, ⟨b.k - (idx b.n x.im - 1), by omega⟩), ?_⟩
  have hj := b.hj
  have hk := b.hk
  refine DyBox.ext rfl ?_ ?_ <;> simp only [clampBox] <;> omega

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `∀ 𝖢 ∈ 𝒱_δ` with `x ∈ 𝖢_large`: `D'_{γ,δ'}(x, ∂𝖢_large ∩ 𝕍) ≤ δ^{-ι}(δ/δ')³`. -/
def startGood (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ δ' ι : ℝ) (x : ℂ) : Set Ω :=
  {ω | ∀ b, IsCell (approxLQG γ W ω) δ b → x ∈ b.largeBox →
    ((approxLGDSet γ W δ' {x} (frontier b.largeBox ∩ dzzV) ω : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal (δ ^ (-ι) * (δ / δ') ^ 3)}

/-- **DZZ l. 1058–1066**: with high probability `D'_{δ'}(x, ∂𝖢_large ∩ 𝕍) ≤ δ^{-ι}(δ/δ')³` for
all cells `𝖢 ∈ S_x` (union bound of (eq-B-good-Phi)), uniformly in `x ∈ 𝕍`. -/
theorem l35_start_hp (hW : IsWhiteNoise P W) {γ α ι : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : 0 < α) (hι : 0 < ι) :
    ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ δ' ∈ Ioc (0 : ℝ) δ, ∀ x ∈ dzzV,
      P.real (startGood γ W δ δ' ι x ∩ eventEFine γ W α δ)ᶜ ≤
        δ ^ (ι / 20) + P.real (eventEFine γ W α δ)ᶜ := by
  classical
  have := hW.isProbabilityMeasure
  obtain ⟨δ₁, hδ₁, hgood⟩ := dzz_lemma37_good hW hγ hγ2 hα hι
  set C := dzzCmc γ with hCdef
  have hC : 0 < C := by have := l31theta_pos hγ hγ2; rw [hCdef]; unfold dzzCmc; linarith
  set M := 14400 * C / ι ^ 2 + 1 with hMdef
  refine ⟨min δ₁ (min (1 / 2) (Real.exp (-M))), by positivity, ?_⟩
  rintro δ ⟨hδ0, hδ⟩ δ' hδ' x hxV
  have hδa : δ < δ₁ := hδ.trans_le (min_le_left _ _)
  have hδ1 : δ < 1 := by linarith [hδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))]
  have hδM : δ < Real.exp (-M) := hδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  set L := Real.log δ⁻¹ with hLdef
  have hlogδ : Real.log δ = -L := by rw [hLdef, Real.log_inv, neg_neg]
  have hLM : M < L := by
    have := Real.log_lt_log hδ0 hδM
    rw [Real.log_exp] at this; linarith
  have hL0 : 0 < L := lt_of_le_of_lt (by positivity) hLM
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hKr : 0 ≤ C * Real.logb 2 δ⁻¹ := by
    rw [Real.logb, ← hLdef]; positivity
  set K := ⌊C * Real.logb 2 δ⁻¹⌋₊ with hKdef
  have hK : (K : ℝ) ≤ C * L / Real.log 2 := by
    calc (K : ℝ) ≤ C * Real.logb 2 δ⁻¹ := Nat.floor_le hKr
      _ = C * L / Real.log 2 := by rw [Real.logb, ← hLdef, mul_div_assoc]
  set Bad : DyBox → Set Ω := fun b => if x ∈ b.largeBox then
    {ω | approxLQG γ W ω b ≤ δ ^ 2} ∩ eventEFine γ W α δ ∩
      {ω | ENNReal.ofReal (δ ^ (-ι) * (δ / δ') ^ 3) <
        ((approxLGDSet γ W δ' {x} (frontier b.largeBox ∩ dzzV) ω : ℕ∞) : ℝ≥0∞)} else ∅
    with hBad
  set cb : ℕ → Fin 3 × Fin 3 → DyBox := fun n ac =>
    clampBox n (idx n x.re - 1 + ac.1) (idx n x.im - 1 + ac.2) with hcb
  have hsub : (startGood γ W δ δ' ι x ∩ eventEFine γ W α δ)ᶜ ⊆ (eventEFine γ W α δ)ᶜ ∪
      ⋃ n ∈ Finset.Icc 1 K, ⋃ ac : Fin 3 × Fin 3, Bad (cb n ac) := by
    intro ω hω
    by_cases hE : ω ∈ eventEFine γ W α δ
    · right
      have hn : ¬ ∀ b, IsCell (approxLQG γ W ω) δ b → x ∈ b.largeBox →
          ((approxLGDSet γ W δ' {x} (frontier b.largeBox ∩ dzzV) ω : ℕ∞) : ℝ≥0∞) ≤
            ENNReal.ofReal (δ ^ (-ι) * (δ / δ') ^ 3) := fun h => hω ⟨h, hE⟩
      push Not at hn
      obtain ⟨b, hb, hxb, hlt⟩ := hn
      obtain ⟨hs1, hs2⟩ := hE.1.2 b hb
      have hn1 : 1 ≤ b.n := by
        by_contra h0
        have h0' : b.n = 0 := by omega
        have : b.side = 1 := by unfold DyBox.side; rw [h0', pow_zero]
        have hlt : δ ^ dzzCMc γ < 1 := Real.rpow_lt_one hδ0.le hδ1 (dzzCMc_pos γ)
        linarith
      have hnK : b.n ≤ K := by
        rw [hKdef]; apply Nat.le_floor
        have h1 := Real.log_le_log (by positivity) hs1
        rw [Real.log_rpow hδ0, hlogδ] at h1
        have h2 : Real.log b.side = -(b.n * Real.log 2) := by
          unfold DyBox.side; rw [Real.log_pow, Real.log_inv]; ring
        rw [h2] at h1
        rw [Real.logb, ← hLdef, mul_div_assoc', le_div_iff₀ hlog2]
        linarith
      obtain ⟨ac, hac⟩ := eq_clampBox_of_mem_largeBox hxb hxV
      refine mem_iUnion₂.2 ⟨b.n, Finset.mem_Icc.2 ⟨hn1, hnK⟩, mem_iUnion.2 ⟨ac, ?_⟩⟩
      have hb' : cb b.n ac = b := hac.symm
      rw [hb']
      simp only [Bad, hxb, if_true]
      exact ⟨⟨hb.1.le, hE⟩, hlt⟩
    · left; exact hE
  have hlevel : ∀ n ∈ Finset.Icc 1 K, ∀ ac : Fin 3 × Fin 3,
      P.real (Bad (cb n ac)) ≤ δ ^ (ι / 10) := by
    intro n hn ac
    obtain ⟨hn1, hnK⟩ := Finset.mem_Icc.1 hn
    have hbn : (cb n ac).n = n := rfl
    have hbK : ((cb n ac).n : ℝ) ≤ C * Real.logb 2 δ⁻¹ := by
      rw [hbn]; exact (Nat.cast_le.2 hnK).trans (Nat.floor_le hKr)
    simp only [Bad]
    split_ifs with hxb
    · exact ENNReal.toReal_le_of_le_ofReal (by positivity)
        (hgood δ ⟨hδ0, hδa⟩ δ' hδ' (cb n ac) (hbn ▸ hn1) hbK x ⟨hxb, hxV⟩)
    · simp only [measureReal_empty]; positivity
  have hsum : ∑ n ∈ Finset.Icc 1 K, ∑ ac : Fin 3 × Fin 3, δ ^ (ι / 10) ≤ δ ^ (ι / 20) := by
    have e : ∑ n ∈ Finset.Icc 1 K, ∑ ac : Fin 3 × Fin 3, δ ^ (ι / 10) =
        (K : ℝ) * (9 * δ ^ (ι / 10)) := by
      simp [Finset.sum_const, Nat.card_Icc]
    rw [e]
    have hKL : (K : ℝ) ≤ 2 * C * L := by
      refine hK.trans ?_
      rw [div_le_iff₀ hlog2]
      have := mul_le_mul_of_nonneg_left hlog2'.le (mul_pos hC hL0).le
      linarith
    have hy : (ι * L / 20) ^ 2 / 2 ≤ Real.exp (ι * L / 20) := by
      have := Real.pow_div_factorial_le_exp (ι * L / 20) (by positivity) 2
      rwa [Nat.factorial_two, Nat.cast_ofNat] at this
    have hM' : 14400 * C ≤ ι ^ 2 * L := by
      have : 14400 * C / ι ^ 2 < L := by linarith
      rw [div_lt_iff₀ (by positivity)] at this
      linarith [mul_comm L (ι ^ 2)]
    have h18 : 18 * C * L ≤ Real.exp (ι * L / 20) := by
      refine le_trans ?_ hy
      have : 18 * C * L * 800 ≤ ι ^ 2 * L * L := by nlinarith
      nlinarith
    rw [Real.rpow_def_of_pos hδ0, Real.rpow_def_of_pos hδ0, hlogδ]
    calc (K : ℝ) * (9 * Real.exp (-L * (ι / 10))) ≤
          (18 * C * L) * Real.exp (-L * (ι / 10)) := by
          have := Real.exp_pos (-L * (ι / 10))
          nlinarith
      _ ≤ Real.exp (ι * L / 20) * Real.exp (-L * (ι / 10)) :=
          mul_le_mul_of_nonneg_right h18 (Real.exp_pos _).le
      _ = Real.exp (-L * (ι / 20)) := by rw [← Real.exp_add]; congr 1; ring
  calc P.real (startGood γ W δ δ' ι x ∩ eventEFine γ W α δ)ᶜ
      ≤ P.real ((eventEFine γ W α δ)ᶜ ∪
          ⋃ n ∈ Finset.Icc 1 K, ⋃ ac : Fin 3 × Fin 3, Bad (cb n ac)) := measureReal_mono hsub
    _ ≤ P.real (eventEFine γ W α δ)ᶜ +
          P.real (⋃ n ∈ Finset.Icc 1 K, ⋃ ac : Fin 3 × Fin 3, Bad (cb n ac)) :=
        measureReal_union_le _ _
    _ ≤ P.real (eventEFine γ W α δ)ᶜ + δ ^ (ι / 20) := by
        gcongr
        refine (measureReal_biUnion_finset_le _ _).trans ?_
        refine le_trans (Finset.sum_le_sum fun n hn =>
          (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum fun ac _ =>
            hlevel n hn ac)) hsum
    _ = δ ^ (ι / 20) + P.real (eventEFine γ W α δ)ᶜ := add_comm _ _

end DZZ
end LQGMetric
