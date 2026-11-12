/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L4Union at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L4Tail

/-!
# DZZ Lemma 3.4: the event `𝓔_{δ,α}` and its union bound (P2-DZZ3B, WP-113)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 861–903), (eq-def-E-delta-alpha):
`𝓔_{δ,α} = {δ^{C_mc} ≤ s_C ≤ δ^{C_Mc} ∀ cells} ∩ ⋂_{m,j,x,y} {|η_{2^{-m}}(x) − η_{2^{-m-j}}(y)|
≤ α √(log δ⁻¹) log log δ⁻¹}` over `1 ≤ 2^m ≤ δ^{−C_mc}`, `1 ≤ 2^j ≤ (α log δ⁻¹)²`, `|x − y| ≤ 2^{−m+3}`.
Decision D64: `x, y` range over dyadic box centres, `x = c_B`, `B ∈ 𝔠_m`, `y = c_{B'}`, `B' ∈ 𝔠_{m+j}`
(`nbrEvent`).

Proof (DZZ l. 876–901, restricted to centres, so `x = x̃`, `y = ỹ` and the first and third terms
of the four-term triangle inequality vanish): `|η_{2^{-m}}(x) − η_{2^{-m-j}}(y)| ≤
|η_{2^{-m}}(x) − η_{2^{-m}}(y)| + |η_{2^{-m}}(y) − η_{2^{-m-j}}(y)|`; the first has variance
`O(1)` (Lemma 2.5), the second `≤ j log 2 + 1 ≤ log (α log δ⁻¹)² + 1`; Gaussian tails and the union
bound over `m, j` and the `≤ 4^m · 4^{m+j}` pairs of boxes (`nbrEvent_compl_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- The generic neighbouring-scale event: for `2^m ≤ X`, `2^j ≤ Y`, `B ∈ 𝔠_m`, `B' ∈ 𝔠_{m+j}` with
`|c_B − c_{B'}| ≤ K 2^{−m}`: `|η_{2^{-m}}(c_B) − η_{2^{-m-j}}(c_{B'})| ≤ T`. -/
def nbrEventGen (W : WNSpace → Ω → ℝ) (K X Y T : ℝ) : Set Ω :=
  {ω | ∀ m j : ℕ, (2 : ℝ) ^ m ≤ X → (2 : ℝ) ^ j ≤ Y →
    ∀ b b' : DyBox, b.n = m → b'.n = m + j → ‖b.center - b'.center‖ ≤ K * b.side →
      |etaInf W b.side b.center ω - etaInf W b'.side b'.center ω| ≤ T}

/-- The `η`-part of DZZ's event `𝓔_{δ,α}` (eq-def-E-delta-alpha, l. 864), on dyadic centres (D64):
for `2^m ≤ δ^{−C_mc}`, `2^j ≤ (α log δ⁻¹)²`, `B ∈ 𝔠_m`, `B' ∈ 𝔠_{m+j}` with
`|c_B − c_{B'}| ≤ 2^{−m+3}`: `|η_{2^{-m}}(c_B) − η_{2^{-m-j}}(c_{B'})| ≤ α √(log δ⁻¹) log log δ⁻¹`. -/
def nbrEvent (W : WNSpace → Ω → ℝ) (Cmc α δ : ℝ) : Set Ω :=
  nbrEventGen W 8 (δ ^ (-Cmc)) ((α * Real.log δ⁻¹) ^ 2)
    (α * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹))

/-- Space-increment part of the union bound. -/
def l34S1 (W : WNSpace → Ω → ℝ) (K X Y a : ℝ) (m j : ℕ) (b b' : DyBox) : Set Ω :=
  {ω | (2 : ℝ) ^ m ≤ X ∧ (2 : ℝ) ^ j ≤ Y ∧ ‖b.center - b'.center‖ ≤ K * b.side ∧
    a ≤ |etaInf W b.side b.center ω - etaInf W b.side b'.center ω|}

/-- Scale-increment part of the union bound. -/
def l34S2 (W : WNSpace → Ω → ℝ) (X Y a : ℝ) (m j : ℕ) (b' : DyBox) : Set Ω :=
  {ω | (2 : ℝ) ^ m ≤ X ∧ (2 : ℝ) ^ j ≤ Y ∧
    a ≤ |etaInf W ((2 : ℝ)⁻¹ ^ m) b'.center ω - etaInf W b'.side b'.center ω|}

lemma two_exp_tail_mono {V' V a : ℝ} (hV' : 0 < V') (hVV : V' ≤ V) :
    2 * Real.exp (-a ^ 2 / (2 * V')) ≤ 2 * Real.exp (-a ^ 2 / (2 * V)) := by
  have hV : 0 < V := hV'.trans_le hVV
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_left (sq_nonneg a) (by positivity) (by linarith)

/-- Per-`(m, j)` bound: `P(⋃ S1 ∪ ⋃ S2) ≤ 2 X⁴ Y² · 2 e^{−a²/(2V)}`. -/
lemma l34_level_le (hW : IsWhiteNoise P W) {K X Y a : ℝ} (hK : 0 < K) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (ha : 0 ≤ a) (m j : ℕ) :
    P.real ({ω | ∃ b : DyBox, b.n = m ∧ ω ∈ {ω | ∃ b' : DyBox, b'.n = m + j ∧
        ω ∈ l34S1 W K X Y a m j b b'}} ∪ {ω | ∃ b' : DyBox, b'.n = m + j ∧ ω ∈ l34S2 W X Y a m j b'})
      ≤ 2 * (X ^ 4 * Y ^ 2) * (2 * Real.exp (-a ^ 2 / (2 * (1076 * K + 1 + Real.log Y)))) := by
  have := hW.isProbabilityMeasure
  set V := 1076 * K + 1 + Real.log Y with hVdef
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY
  set B := 2 * Real.exp (-a ^ 2 / (2 * V)) with hBdef
  have hB0 : 0 ≤ B := by positivity
  by_cases hc : (2 : ℝ) ^ m ≤ X ∧ (2 : ℝ) ^ j ≤ Y
  swap
  · have e : ({ω | ∃ b : DyBox, b.n = m ∧ ω ∈ {ω | ∃ b' : DyBox, b'.n = m + j ∧
        ω ∈ l34S1 W K X Y a m j b b'}} ∪
          {ω | ∃ b' : DyBox, b'.n = m + j ∧ ω ∈ l34S2 W X Y a m j b'}) = ∅ := by
      ext ω
      simp only [mem_union, mem_ofPred_eq, l34S1, l34S2, mem_empty_iff_false, iff_false]
      rintro (⟨b, -, b', -, h1, h2, -⟩ | ⟨b', -, h1, h2, -⟩) <;> exact hc ⟨h1, h2⟩
    rw [e, measureReal_empty]
    positivity
  obtain ⟨hmX, hjY⟩ := hc
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have h2mj : (2 : ℝ) ^ (m + j) ≤ X * Y := by
    rw [pow_add]; exact mul_le_mul hmX hjY (by positivity) (by linarith)
  -- space increments
  have hS1 : ∀ b b' : DyBox, P.real (l34S1 W K X Y a m j b b') ≤ B := by
    intro b b'
    by_cases h8 : ‖b.center - b'.center‖ ≤ K * b.side
    · refine (measureReal_mono fun ω hω => hω.2.2.2).trans ?_
      refine (tail_etaInf_space hW (DyBox.side_pos b) hK h8 ha).trans ?_
      exact two_exp_tail_mono (by positivity) (by linarith)
    · have e : l34S1 W K X Y a m j b b' = ∅ := by
        ext ω; simp only [l34S1, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => h8 h.2.2.1
      rw [e, measureReal_empty]; exact hB0
  -- scale increments
  have hS2 : ∀ b' : DyBox, b'.n = m + j → P.real (l34S2 W X Y a m j b') ≤ B := by
    intro b' hb'
    refine (measureReal_mono fun ω hω => hω.2.2).trans ?_
    have hs' : b'.side = (2 : ℝ)⁻¹ ^ m * (2 : ℝ)⁻¹ ^ j := by
      rw [DyBox.side, hb', pow_add]
    have hle : b'.side ≤ (2 : ℝ)⁻¹ ^ m := by
      rw [hs']
      exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
    refine (tail_etaInf_scale hW (DyBox.side_pos b') hle b'.center ha).trans ?_
    refine two_exp_tail_mono ?_ ?_
    · have := Real.log_nonneg ((one_le_div (DyBox.side_pos b')).2 hle); linarith
    · have hq : (2 : ℝ)⁻¹ ^ m / b'.side = 2 ^ j := by
        rw [hs', div_mul_cancel_left₀ (by positivity), inv_pow, inv_inv]
      rw [hq]
      have := Real.log_le_log (by positivity) hjY
      linarith
  have hA1 := measureReal_level_le (P := P) m
    (fun b => {ω | ∃ b' : DyBox, b'.n = m + j ∧ ω ∈ l34S1 W K X Y a m j b b'})
    (B := ((2 : ℝ) ^ (m + j)) ^ 2 * B)
    (fun b _ => measureReal_level_le (m + j) _ (fun b' _ => hS1 b b'))
  have hA2 := measureReal_level_le (P := P) (m + j) (l34S2 W X Y a m j) (B := B) hS2
  refine (measureReal_union_le _ _).trans ?_
  have e1 : ((2 : ℝ) ^ m) ^ 2 * (((2 : ℝ) ^ (m + j)) ^ 2 * B) ≤ X ^ 4 * Y ^ 2 * B := by
    have h1 : ((2 : ℝ) ^ m) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ h2m.le hmX 2
    have h2 : ((2 : ℝ) ^ (m + j)) ^ 2 ≤ (X * Y) ^ 2 := pow_le_pow_left₀ (by positivity) h2mj 2
    calc ((2 : ℝ) ^ m) ^ 2 * (((2 : ℝ) ^ (m + j)) ^ 2 * B) ≤ X ^ 2 * ((X * Y) ^ 2 * B) :=
          mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 hB0) (by positivity) (by positivity)
      _ = X ^ 4 * Y ^ 2 * B := by ring
  have e2 : ((2 : ℝ) ^ (m + j)) ^ 2 * B ≤ X ^ 4 * Y ^ 2 * B := by
    have h2 : ((2 : ℝ) ^ (m + j)) ^ 2 ≤ (X * Y) ^ 2 := pow_le_pow_left₀ (by positivity) h2mj 2
    have h3 : (X * Y) ^ 2 ≤ X ^ 4 * Y ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hX (by norm_num)) (by positivity)
    exact mul_le_mul_of_nonneg_right (h2.trans h3) hB0
  linarith

/-- The union bound of DZZ l. 893–899 on dyadic centres. -/
theorem nbrEventGen_compl_le (hW : IsWhiteNoise P W) {K X Y T : ℝ} (hK : 0 < K) (hX : 1 ≤ X)
    (hY : 1 ≤ Y) (hT : 0 ≤ T) :
    P.real (nbrEventGen W K X Y T)ᶜ ≤ (X + 1) * (Y + 1) *
      (2 * (X ^ 4 * Y ^ 2) * (2 * Real.exp (-(T / 2) ^ 2 / (2 * (1076 * K + 1 + Real.log Y))))) := by
  have := hW.isProbabilityMeasure
  set A : ℕ → ℕ → Set Ω := fun m j =>
    {ω | ∃ b : DyBox, b.n = m ∧ ω ∈ {ω | ∃ b' : DyBox, b'.n = m + j ∧
        ω ∈ l34S1 W K X Y (T / 2) m j b b'}} ∪
      {ω | ∃ b' : DyBox, b'.n = m + j ∧ ω ∈ l34S2 W X Y (T / 2) m j b'} with hA
  have hsub : (nbrEventGen W K X Y T)ᶜ ⊆
      ⋃ m ∈ Finset.range (⌊X⌋₊ + 1), ⋃ j ∈ Finset.range (⌊Y⌋₊ + 1), A m j := by
    intro ω hω
    simp only [nbrEventGen, mem_compl_iff, mem_ofPred_eq] at hω
    push Not at hω
    obtain ⟨m, j, hm, hj, b, b', hb, hb', h8, hlt⟩ := hω
    simp only [mem_iUnion, Finset.mem_range]
    have hmX : (m : ℝ) ≤ X := (by exact_mod_cast m.lt_two_pow_self.le : (m : ℝ) ≤ 2 ^ m).trans hm
    have hjY : (j : ℝ) ≤ Y := (by exact_mod_cast j.lt_two_pow_self.le : (j : ℝ) ≤ 2 ^ j).trans hj
    refine ⟨m, Nat.lt_succ_of_le (Nat.le_floor hmX), j, Nat.lt_succ_of_le (Nat.le_floor hjY), ?_⟩
    have hside : b.side = (2 : ℝ)⁻¹ ^ m := by rw [DyBox.side, hb]
    have tri := abs_sub_le (etaInf W b.side b.center ω) (etaInf W b.side b'.center ω)
      (etaInf W b'.side b'.center ω)
    by_cases h1 : T / 2 ≤ |etaInf W b.side b.center ω - etaInf W b.side b'.center ω|
    · exact Or.inl ⟨b, hb, b', hb', hm, hj, h8, h1⟩
    · refine Or.inr ⟨b', hb', hm, hj, ?_⟩
      rw [← hside]
      linarith
  have hlev := fun m j => l34_level_le (P := P) hW hK hX hY (by linarith : 0 ≤ T / 2) m j
  set C := 2 * (X ^ 4 * Y ^ 2) * (2 * Real.exp (-(T / 2) ^ 2 / (2 * (1076 * K + 1 + Real.log Y))))
  have hC0 : 0 ≤ C := by positivity
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans ?_)
  calc ∑ m ∈ Finset.range (⌊X⌋₊ + 1), P.real (⋃ j ∈ Finset.range (⌊Y⌋₊ + 1), A m j)
      ≤ ∑ _m ∈ Finset.range (⌊X⌋₊ + 1), ((⌊Y⌋₊ + 1 : ℕ) : ℝ) * C := by
        refine Finset.sum_le_sum fun m _ => (measureReal_biUnion_finset_le _ _).trans ?_
        calc ∑ j ∈ Finset.range (⌊Y⌋₊ + 1), P.real (A m j)
            ≤ ∑ _j ∈ Finset.range (⌊Y⌋₊ + 1), C := Finset.sum_le_sum fun j _ => hlev m j
          _ = ((⌊Y⌋₊ + 1 : ℕ) : ℝ) * C := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ((⌊X⌋₊ + 1 : ℕ) : ℝ) * (((⌊Y⌋₊ + 1 : ℕ) : ℝ) * C) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (X + 1) * ((Y + 1) * C) := by
        have h1 : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ X + 1 := by
          push_cast; linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ X)]
        have h2 : ((⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ Y + 1 := by
          push_cast; linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ Y)]
        exact mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 hC0) (by positivity) (by positivity)
    _ = (X + 1) * (Y + 1) * C := by ring

end DZZ
end LQGMetric
