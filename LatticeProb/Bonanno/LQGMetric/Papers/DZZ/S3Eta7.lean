/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3Eta7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3Eta6
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W15

/-!
# DZZ (Eq.LD-lowerbound-approx-LGD) for one box, from the comparison with `M̃_{γ,ε²s',η}`
(P2-DZZETA)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1192–1206). Fix a box `B` (side `s`), a square
`S = sqSB B a b ∈ 𝒮_B` (side `s' = s/1024`, lower-left corner `sqCorner B a b`) and `k ≥ 1`;
`K = 2k = 1/ε`, `h = ε s'`, `δ̂ = ε² s'`. The squares `evenSq (sqCorner B a b) h i j`
(`i, j < k`) are the `K²/4` squares `S̃_{i_j}` of DZZ l. 1197–1198.

* `L32TildeMLowerBox`: the comparison of DZZ l. 1193–1195 on an event `G`, for these squares:
  `M(S̃) ≥ c_A (δ')² s^{-2} M̃_{γ,δ̂,η}(S̃)` (`c_A = e^{-2αγ√L log L}`) when `M_{γ,s}(B) ≥ δ'²`.
* **`measure_cellCompare_le_of_lower`**: under it, and the parameter conditions
  `16·1024² δ² ≤ β² c_A δ'²` (DZZ l. 1200: `e^{2αγ√L log L}(δ/δ')² s²/(ε s')² ≤ β² K²/4`), the finite
  range condition `δ̂ (log δ̂⁻¹ + 1) < h` (DZZ l. 1197: `ε² s' log(1/(ε² s')) < ε s'`), `β ≤ 1/2`
  and `β C ≤ 1`:
  `P(G ∩ {M_{γ,s}(B) ≥ δ'², M(S) ≤ δ²}) ≤ 2^{k²} (β C)^{⌊k²/2⌋}` (`C = C_{γ,−1}`, up to the factor 4
  of our normalization by the inscribed radius `h/2`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the lower-left corner of `sqSB B a b` -/
def sqCorner (B : DyBox) (a b : ℕ) : ℂ :=
  ⟨B.center.re - 2 * B.side + a * (B.side / 1024), B.center.im - 2 * B.side + b * (B.side / 1024)⟩

/-- the comparison of DZZ l. 1193–1195 on `G`, for the squares `S̃_{i_j}` of `sqSB B a b`
(`K = 2k`, side `h = s'/(2k)`, η-chaos parameter `δ̂ = s'/(2k)²`) -/
def L32TildeMLowerBox (γ : ℝ) (W : WNSpace → Ω → ℝ) (ν : Ω → Measure ℂ) (G : Set Ω) (B : DyBox)
    (a b k : ℕ) (m₀ cA : ℝ) : Prop :=
  ∀ ω ∈ G, m₀ ≤ approxLQG γ W ω B → ∀ i j : ℕ, i < k → j < k →
    ENNReal.ofReal (cA * m₀ / B.side ^ 2) *
        etaChaos W γ (B.side / 1024 / (2 * k) ^ 2)
          (evenSq (sqCorner B a b) (B.side / 1024 / (2 * k)) i j) ω ≤
      ν ω (evenSq (sqCorner B a b) (B.side / 1024 / (2 * k)) i j)

lemma evenSq_subset_sqSB (B : DyBox) (a b : ℕ) {k : ℕ} (hk : 1 ≤ k) {i j : ℕ} (hi : i < k)
    (hj : j < k) : evenSq (sqCorner B a b) (B.side / 1024 / (2 * k)) i j ⊆ sqSB B a b := by
  have hs := DyBox.side_pos' B
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hi' : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
  have hj' : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
  have hh : (0 : ℝ) ≤ B.side / 1024 / (2 * k) := by positivity
  have hK : (2 * k : ℝ) * (B.side / 1024 / (2 * k)) = B.side / 1024 := by field_simp
  intro z hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  simp only [sqCorner] at h1 h2 h3 h4
  have e1 : (2 * (i : ℝ) + 1) * (B.side / 1024 / (2 * k)) ≤ B.side / 1024 :=
    (mul_le_mul_of_nonneg_right (by linarith) hh).trans_eq hK
  have e2 : (2 * (j : ℝ) + 1) * (B.side / 1024 / (2 * k)) ≤ B.side / 1024 :=
    (mul_le_mul_of_nonneg_right (by linarith) hh).trans_eq hK
  have e3 : 0 ≤ 2 * (i : ℝ) * (B.side / 1024 / (2 * k)) := by positivity
  have e4 : 0 ≤ 2 * (j : ℝ) * (B.side / 1024 / (2 * k)) := by positivity
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **DZZ (Eq.LD-lowerbound-approx-LGD) for one box**, from the comparison `L32TildeMLowerBox` -/
theorem measure_cellCompare_le_of_lower (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (ν : Ω → Measure ℂ) (G : Set Ω) (B : DyBox) (a b k : ℕ)
      (δ m₀ cA β : ℝ), 1 ≤ k → 0 < m₀ → 0 < cA → 0 < β → β ≤ 2⁻¹ → ENNReal.ofReal β * C ≤ 1 →
      16 * 1024 ^ 2 * δ ^ 2 ≤ β ^ 2 * cA * m₀ →
      B.side / 1024 / (2 * k) ^ 2 ≤ 1 →
      B.side / 1024 / (2 * k) ^ 2 * (Real.log (B.side / 1024 / (2 * k) ^ 2)⁻¹ + 1) <
        B.side / 1024 / (2 * k) →
      L32TildeMLowerBox γ W ν G B a b k m₀ cA →
      P (G ∩ {ω | m₀ ≤ approxLQG γ W ω B ∧ ν ω (sqSB B a b) ≤ ENNReal.ofReal (δ ^ 2)}) ≤
        2 ^ (k * k) * (ENNReal.ofReal β * C) ^ (k * k / 2) := by
  obtain ⟨C, hC, hsum⟩ := measure_sum_etaChaos_le hW hγ hγ2
  refine ⟨C, hC, fun ν G B a b k δ m₀ cA β hk hm₀ hcA hβ0 hβ hβC hratio hδ1 hrange hcomp => ?_⟩
  have hs := DyBox.side_pos' B
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set h : ℝ := B.side / 1024 / (2 * k) with hh_def
  set δh : ℝ := B.side / 1024 / (2 * k) ^ 2 with hδh_def
  have hh : 0 < h := by positivity
  have hδh : 0 < δh := by positivity
  have hδhh : δh = h / (2 * k) := by simp only [h, δh]; field_simp
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hδh2 : δh ≤ h / 2 := by
    rw [hδhh]; exact div_le_div_of_nonneg_left hh.le (by norm_num) (by linarith)
  set R : ℝ := (δh * Real.log δh⁻¹ + δh) / 2
  have hR := etaRad_le_bandHalf hδh hδ1
  have h2R : 2 * R = δh * (Real.log δh⁻¹ + 1) := by simp only [R]; ring
  set ρ : ℝ := (h - 2 * R) / 4
  have hρ : 0 < ρ := by simp only [ρ]; linarith
  have hRh : 2 * (R + ρ) ≤ h := by simp only [ρ]; linarith
  have hb := hsum δh R ρ h (sqCorner B a b) k hδh hh hδh2 hR hρ hRh (ENNReal.ofReal β)
    (ENNReal.ofReal_pos.2 hβ0).ne' (by
      calc ENNReal.ofReal β ≤ ENNReal.ofReal 2⁻¹ := ENNReal.ofReal_le_ofReal hβ
        _ = 2⁻¹ := by rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]) hβC
  refine le_trans (measure_mono fun ω hω => ?_) hb
  obtain ⟨hG, hm, hν⟩ := hω
  have hc := hcomp ω hG hm
  set c : ℝ := cA * m₀ / B.side ^ 2
  have hc0 : 0 < c := by positivity
  set F : Fin k × Fin k → Set ℂ := fun ij => evenSq (sqCorner B a b) h ij.1 ij.2
  set T : ℝ≥0∞ := ∑ ij : Fin k × Fin k, etaChaos W γ δh (F ij) ω
  have hdisj : Pairwise (Function.onFun Disjoint F) := fun ij ij' hne => by
    have := disjoint_thickening_evenSq (w := sqCorner B a b) hh (r := h / 2) (by linarith)
      (i := ij.1) (j := ij.2) (i' := ij'.1) (j' := ij'.2) (fun he => hne (by
        ext
        · exact congrArg Prod.fst he
        · exact congrArg Prod.snd he))
    exact this.mono (self_subset_thickening (by linarith) _) (self_subset_thickening (by linarith) _)
  have hcT : ENNReal.ofReal c * T ≤ ENNReal.ofReal (δ ^ 2) := by
    calc ENNReal.ofReal c * T = ∑ ij : Fin k × Fin k, ENNReal.ofReal c * etaChaos W γ δh (F ij) ω :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ ij : Fin k × Fin k, ν ω (F ij) :=
          Finset.sum_le_sum fun ij _ => hc ij.1 ij.2 ij.1.2 ij.2.2
      _ = ν ω (⋃ ij, F ij) := by
          rw [measure_iUnion hdisj fun ij => measurableSet_evenSq _ _ _ _, tsum_fintype]
      _ ≤ ν ω (sqSB B a b) := measure_mono (iUnion_subset fun ij =>
          evenSq_subset_sqSB B a b hk ij.1.2 ij.2.2)
      _ ≤ _ := hν
  have hTt : T ≠ ⊤ := by
    intro hT
    rw [hT, ENNReal.mul_top (ENNReal.ofReal_pos.2 hc0).ne'] at hcT
    exact ENNReal.ofReal_ne_top (top_le_iff.1 hcT)
  set t : ℝ := T.toReal
  have hTt' : T = ENNReal.ofReal t := (ENNReal.ofReal_toReal hTt).symm
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have hct : c * t ≤ δ ^ 2 := by
    rw [hTt', ← ENNReal.ofReal_mul hc0.le] at hcT
    exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 hcT
  show ∑ ij : Fin k × Fin k, (ENNReal.ofReal (h / 2) ^ 2)⁻¹ * etaChaos W γ δh (F ij) ω ≤ _
  rw [← Finset.mul_sum]
  change _ * T ≤ _
  rw [hTt', ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_pow hβ0.le, show ((k * k : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((k : ℝ) * k) by
      rw [← ENNReal.ofReal_natCast]; push_cast; rfl,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- `(h/2)^{-2} t ≤ (h/2)^{-2} δ²/c ≤ β² k²`
  have hh2 : ((h / 2) ^ 2)⁻¹ = 16 * 1024 ^ 2 * k ^ 2 / B.side ^ 2 := by
    simp only [h]; field_simp; ring
  rw [hh2]
  have ht : t ≤ δ ^ 2 / c := by rw [le_div_iff₀ hc0]; linarith
  calc 16 * 1024 ^ 2 * (k : ℝ) ^ 2 / B.side ^ 2 * t
      ≤ 16 * 1024 ^ 2 * (k : ℝ) ^ 2 / B.side ^ 2 * (δ ^ 2 / c) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
    _ = (16 * 1024 ^ 2 * δ ^ 2) / (cA * m₀) * k ^ 2 := by
        simp only [c]; field_simp
    _ ≤ β ^ 2 * (k * k) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (k : ℝ)]

end DZZ
end LQGMetric
