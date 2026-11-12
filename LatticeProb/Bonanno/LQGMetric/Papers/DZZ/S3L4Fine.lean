/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L4Fine at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L4

/-!
# DZZ Lemma 3.4 at finer centres (P2-DZZ3B, WP-113)

DZZ Lemma 3.7 (l. 975–980) evaluates `η_{2^{-m-j}}` (`2^{-m-j} = ε² s`) at the centre `c_{B̃}` of a
box `B̃` of side `ts ≤ ε² s`, which is a dyadic centre of a *finer* level than `m + j`. This
file extends the η-part of `𝓔_{δ,α}` to `y = c_{B''}` for all dyadic boxes `B''` of level
`≥ m + j` (`nbrFineEvent`), following the third term of DZZ's proof of Lemma 3.4 (l. 885–891):
`|η_{2^{-n}}(c_{B'}) − η_{2^{-n}}(y)|` for `y` in the level-`n` box `B'` is bounded by
DZZ Lemma 2.6 (`dzz_lemma26_eta`, continuous version `Y_n` of `η_{2^{-n}}`, which agrees with
`η_{2^{-n}}` a.s. simultaneously at the countably many dyadic centres) and a union bound.

* `DyBox.center_mem_box01`, `DyBox.norm_sub_center_boxAt_le`: geometry of dyadic centres.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise SupTail

instance : Countable DyBox := by
  refine Function.Injective.countable (f := fun b : DyBox => (b.n, b.j, b.k)) ?_
  rintro ⟨n, j, k, _, _⟩ ⟨n', j', k', _, _⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

lemma DyBox.center_mem_box01 (b : DyBox) : b.center ∈ ferniqueBox 0 1 := by
  have hs := b.side_pos
  have hN : b.side * 2 ^ b.n = 1 := by
    rw [DyBox.side, ← mul_pow]; norm_num
  have hj : (b.j : ℝ) + 1 ≤ 2 ^ b.n := by exact_mod_cast b.hj
  have hk : (b.k : ℝ) + 1 ≤ 2 ^ b.n := by exact_mod_cast b.hk
  simp only [ferniqueBox, Complex.mem_reProdIm, DyBox.center, Complex.zero_re,
    Complex.zero_im, zero_add, mem_Icc]
  refine ⟨⟨by positivity, ?_⟩, ⟨by positivity, ?_⟩⟩ <;> nlinarith

lemma idx_bounds {n : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (DyBox.idx n x : ℝ) ≤ x * 2 ^ n ∧ x * 2 ^ n ≤ DyBox.idx n x + 1 := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hxN : 0 ≤ x * 2 ^ n := by positivity
  unfold DyBox.idx
  rcases le_total ⌊x * 2 ^ n⌋₊ (2 ^ n - 1) with h | h
  · rw [min_eq_left h]
    exact ⟨Nat.floor_le hxN, (Nat.lt_floor_add_one _).le⟩
  · rw [min_eq_right h]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have e : ((2 ^ n - 1 : ℕ) : ℝ) = 2 ^ n - 1 := by push_cast [Nat.cast_sub h1]; ring
    rw [e]
    have hle : x * 2 ^ n ≤ 2 ^ n := by nlinarith
    refine ⟨?_, by linarith⟩
    have h' : ((2 ^ n - 1 : ℕ) : ℝ) ≤ ⌊x * 2 ^ n⌋₊ := by exact_mod_cast h
    rw [e] at h'
    linarith [Nat.floor_le hxN]

lemma DyBox.norm_sub_center_boxAt_le {v : ℂ} (hv : v ∈ ferniqueBox 0 1) (n : ℕ) :
    ‖v - (DyBox.boxAt n v).center‖ ≤ (2 : ℝ)⁻¹ ^ n := by
  simp only [ferniqueBox, Complex.mem_reProdIm, Complex.zero_re, Complex.zero_im, zero_add,
    mem_Icc] at hv
  obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩⟩ := hv
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hs : (2 : ℝ)⁻¹ ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
  have hs0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  obtain ⟨r1, r2⟩ := idx_bounds (n := n) a0 a1
  obtain ⟨i1, i2⟩ := idx_bounds (n := n) b0 b1
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im, DyBox.center, DyBox.boxAt, DyBox.side]
  set s := (2 : ℝ)⁻¹ ^ n
  -- each coordinate is within `s/2`
  have key : ∀ (x : ℝ) (i : ℝ), i ≤ x * 2 ^ n → x * 2 ^ n ≤ i + 1 →
      |x - (i + 1 / 2) * s| ≤ s / 2 := by
    intro x i h1 h2
    have e : x - (i + 1 / 2) * s = (x * 2 ^ n - (i + 1 / 2)) * s := by
      rw [sub_mul, mul_assoc, mul_comm ((2 : ℝ) ^ n), hs, mul_one]
    rw [e, abs_mul, abs_of_pos hs0]
    have : |x * 2 ^ n - (i + 1 / 2)| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    calc |x * 2 ^ n - (i + 1 / 2)| * s ≤ 1 / 2 * s := mul_le_mul_of_nonneg_right this hs0.le
      _ = s / 2 := by ring
  have k1 := key v.re _ r1 r2
  have k2 := key v.im _ i1 i2
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- The η-part of `𝓔_{δ,α}` at all finer centres: for `2^m ≤ X`, `2^j ≤ Y`, `B ∈ 𝔠_m` and any
dyadic box `B''` of level `≥ m + j` with `|c_B − c_{B''}| ≤ 8 · 2^{−m}`:
`|η_{2^{-m}}(c_B) − η_{2^{-m-j}}(c_{B''})| ≤ T`. -/
def nbrFineGen (W : WNSpace → Ω → ℝ) (X Y T : ℝ) : Set Ω :=
  {ω | ∀ m j : ℕ, (2 : ℝ) ^ m ≤ X → (2 : ℝ) ^ j ≤ Y →
    ∀ b b'' : DyBox, b.n = m → m + j ≤ b''.n → ‖b.center - b''.center‖ ≤ 8 * b.side →
      |etaInf W b.side b.center ω - etaInf W ((2 : ℝ)⁻¹ ^ (m + j)) b''.center ω| ≤ T}

/-- Union bound for `nbrFineGen`: the level-`(m+j)` comparison (`nbrEventGen` with `K = 9`,
threshold `2T/3`) plus the oscillation of `η_{2^{-n}}` inside the level-`n` boxes (DZZ Lemma 2.6),
`a = T/(3 log 2)`. -/
theorem nbrFineGen_compl_le (hW : IsWhiteNoise P W) {X Y T : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hT : 0 ≤ T) (Ys : ℕ → ℂ → Ω → ℝ)
    (hYae : ∀ n x, Ys n x =ᵐ[P] etaInf W ((2 : ℝ)⁻¹ ^ n) x) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ n : ℕ, ∀ u ∈ ferniqueBox 0 1,
      P.real {ω | ∃ v ∈ ferniqueBox 0 1, ‖v - u‖ ≤ ((1 : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ n ∧
        T / (3 * Real.log 2) * Real.log (((1 : ℕ) : ℝ) + 1) ≤ |Ys n v ω - Ys n u ω|} ≤
        C * Real.exp (-(T / (3 * Real.log 2)) ^ 2 / C)) :
    P.real (nbrFineGen W X Y T)ᶜ ≤ P.real (nbrEventGen W 9 X Y (2 * T / 3))ᶜ +
      (X * Y + 1) * ((X * Y) ^ 2 * (C * Real.exp (-(T / (3 * Real.log 2)) ^ 2 / C))) := by
  have := hW.isProbabilityMeasure
  set a := T / (3 * Real.log 2) with ha
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set O : ℕ → DyBox → Set Ω := fun n b' => {ω | (2 : ℝ) ^ n ≤ X * Y ∧
    ∃ v ∈ ferniqueBox 0 1, ‖v - b'.center‖ ≤ ((1 : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ n ∧
      a * Real.log (((1 : ℕ) : ℝ) + 1) ≤ |Ys n v ω - Ys n b'.center ω|} with hO
  set N : Set Ω := ⋃ n : ℕ, ⋃ b : DyBox,
    {ω | Ys n b.center ω ≠ etaInf W ((2 : ℝ)⁻¹ ^ n) b.center ω} with hN
  have hN0 : P N = 0 := by
    refine measure_iUnion_null fun n => measure_iUnion_null fun b => ?_
    exact ae_iff.1 (hYae n b.center)
  have hsub : (nbrFineGen W X Y T)ᶜ ⊆ ((nbrEventGen W 9 X Y (2 * T / 3))ᶜ ∪
      ⋃ n ∈ Finset.range (⌊X * Y⌋₊ + 1), {ω | ∃ b' : DyBox, b'.n = n ∧ ω ∈ O n b'}) ∪ N := by
    intro ω hω
    by_cases hωN : ω ∈ N
    · exact Or.inr hωN
    left
    simp only [hN, mem_iUnion, mem_ofPred_eq, not_exists, not_not] at hωN
    simp only [nbrFineGen, mem_compl_iff, mem_ofPred_eq] at hω
    push Not at hω
    obtain ⟨m, j, hm, hj, b, b'', hb, hb'', h8, hlt⟩ := hω
    set b' := DyBox.boxAt (m + j) b''.center with hb'
    have hb'n : b'.n = m + j := rfl
    have hside : b.side = (2 : ℝ)⁻¹ ^ m := by rw [DyBox.side, hb]
    have hs'le : (2 : ℝ)⁻¹ ^ (m + j) ≤ b.side := by
      rw [hside]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hcl := DyBox.norm_sub_center_boxAt_le b''.center_mem_box01 (m + j)
    by_cases h1 : |etaInf W b.side b.center ω - etaInf W b'.side b'.center ω| ≤ 2 * T / 3
    · right
      have h2mj : (2 : ℝ) ^ (m + j) ≤ X * Y := by
        rw [pow_add]; exact mul_le_mul hm hj (by positivity) (by linarith)
      have hmj : ((m + j : ℕ) : ℝ) ≤ X * Y :=
        (by exact_mod_cast (m + j).lt_two_pow_self.le : ((m + j : ℕ) : ℝ) ≤ 2 ^ (m + j)).trans h2mj
      simp only [mem_iUnion, Finset.mem_range]
      refine ⟨m + j, Nat.lt_succ_of_le (Nat.le_floor hmj), b', hb'n, h2mj, b''.center,
        b''.center_mem_box01, by rw [Nat.cast_one, one_mul]; exact hcl, ?_⟩
      have e3 : T / (3 * Real.log 2) * Real.log 2 = T / 3 := by field_simp
      rw [hωN, hωN, Nat.cast_one, one_add_one_eq_two, ha, e3]
      have e : b'.side = (2 : ℝ)⁻¹ ^ (m + j) := rfl
      rw [e] at h1
      have tri := abs_sub_le (etaInf W b.side b.center ω)
        (etaInf W ((2 : ℝ)⁻¹ ^ (m + j)) b'.center ω)
        (etaInf W ((2 : ℝ)⁻¹ ^ (m + j)) b''.center ω)
      rw [abs_sub_comm (etaInf W ((2 : ℝ)⁻¹ ^ (m + j)) b'.center ω)] at tri
      linarith
    · left
      intro hall
      refine h1 (hall m j hm hj b b' hb hb'n ?_)
      calc ‖b.center - b'.center‖ ≤ ‖b.center - b''.center‖ + ‖b''.center - b'.center‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 8 * b.side + b.side := add_le_add h8 (hcl.trans hs'le)
        _ = 9 * b.side := by ring
  set D := C * Real.exp (-a ^ 2 / C)
  have hD0 : 0 ≤ D := by positivity
  have hO : ∀ n, P.real {ω | ∃ b' : DyBox, b'.n = n ∧ ω ∈ O n b'} ≤ (X * Y) ^ 2 * D := by
    intro n
    by_cases hn : (2 : ℝ) ^ n ≤ X * Y
    · refine (measureReal_level_le n (O n) (B := D) fun b' _ =>
        (measureReal_mono fun ω hω => hω.2).trans (hC n _ b'.center_mem_box01)).trans ?_
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hn 2) hD0
    · have e : {ω | ∃ b' : DyBox, b'.n = n ∧ ω ∈ O n b'} = ∅ := by
        ext ω; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, hO]
        rintro ⟨b', -, h, -⟩; exact hn h
      rw [e, measureReal_empty]; positivity
  have hXY : 0 ≤ X * Y := by nlinarith
  calc P.real (nbrFineGen W X Y T)ᶜ
      ≤ P.real (((nbrEventGen W 9 X Y (2 * T / 3))ᶜ ∪
          ⋃ n ∈ Finset.range (⌊X * Y⌋₊ + 1), {ω | ∃ b' : DyBox, b'.n = n ∧ ω ∈ O n b'}) ∪ N) :=
        measureReal_mono hsub
    _ ≤ P.real ((nbrEventGen W 9 X Y (2 * T / 3))ᶜ ∪
          ⋃ n ∈ Finset.range (⌊X * Y⌋₊ + 1), {ω | ∃ b' : DyBox, b'.n = n ∧ ω ∈ O n b'}) +
          P.real N := measureReal_union_le _ _
    _ = P.real ((nbrEventGen W 9 X Y (2 * T / 3))ᶜ ∪
          ⋃ n ∈ Finset.range (⌊X * Y⌋₊ + 1), {ω | ∃ b' : DyBox, b'.n = n ∧ ω ∈ O n b'}) := by
        have : P.real N = 0 := by rw [measureReal_def, hN0, ENNReal.toReal_zero]
        rw [this, add_zero]
    _ ≤ P.real (nbrEventGen W 9 X Y (2 * T / 3))ᶜ + ∑ n ∈ Finset.range (⌊X * Y⌋₊ + 1),
          P.real {ω | ∃ b' : DyBox, b'.n = n ∧ ω ∈ O n b'} :=
        (measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_biUnion_finset_le _ _))
    _ ≤ P.real (nbrEventGen W 9 X Y (2 * T / 3))ᶜ +
          ((⌊X * Y⌋₊ + 1 : ℕ) : ℝ) * ((X * Y) ^ 2 * D) := by
        refine add_le_add le_rfl ((Finset.sum_le_sum fun n _ => hO n).trans_eq ?_)
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ P.real (nbrEventGen W 9 X Y (2 * T / 3))ᶜ + (X * Y + 1) * ((X * Y) ^ 2 * D) := by
        refine add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ (by positivity))
        push_cast; linarith [Nat.floor_le hXY]

end DZZ
end LQGMetric
