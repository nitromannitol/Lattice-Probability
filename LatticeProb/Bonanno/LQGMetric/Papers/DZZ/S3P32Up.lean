/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32Up at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32Low

/-!
# DZZ Proposition 3.2, upper bound: the final count (P2-DZZ32)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Proposition 3.2, upper bound,
l. 1088–1103. With `λ = e^{(log δ⁻¹)^{0.7}}` and `ε = 2^{-k}` as in Lemma 3.7, DZZ prove
(eq-B-percolation-Psi) and (eq-B-good-Psi) and then "complete the proof following the same
argument as in the proof of Lemma 3.5": the crossing gives (Eq.boundDprime) for `D`,
`min D_δ ≤ d λ/ε² + 2δ^{-ι}λ`, `d = min D'_δ`, and (Eq.lowerboundforDprime) `d ≥ δ^{-2ι}` finishes
(l. 1101).

* `lamP32 δ = e^{(log δ⁻¹)^{0.7}}`.
* `L32UpperCross P γ W μ ξ ξd` (open): the crossing bound (Eq.boundDprime) for `D_δ`, in the
  normalization of the proved L3.5 crossing (`L35Crossing`, S3L5Cross):
  `min D_δ ≤ min D'_δ · 4^{k+2}(λ+1) + 2δ^{-ι}λ + 8` with `ι = C_Mc/2`, with high probability,
  uniformly over pairs admissible at `δ`. DZZ obtain it from (eq-B-percolation-Psi),
  (eq-B-good-Psi) (l. 1090–1153) and the crossing argument of l. 1071–1079.
* **`dzz_prop32_upper`**: the upper half of P3.2 from `L32UpperCross`, via the lower bound
  (Eq.lowerboundforDprime) on `cellSizeEvent` (Lemma 3.1, `dzz_lemma31_bound`) and the
  arithmetic of l. 1101 (as in `dzz_lemma35U_of_crossing`, with `(δ/δ')³ = 1`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `λ = e^{(log δ⁻¹)^{0.7}}` (DZZ l. 1089). -/
def lamP32 (δ : ℝ) : ℝ := Real.exp (Real.log δ⁻¹ ^ (0.7 : ℝ))

/-- The event of (Eq.boundDprime) for `D_δ` (DZZ l. 1101, first inequality), `ι = C_Mc/2`. -/
def p32CrossEvent (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (δ : ℝ) (A B : Set ℂ) :
    Set Ω :=
  {ω | ((lgdMinSet (μ ω) δ A B : ℕ∞) : ℝ≥0∞) ≤
      ((approxLGDSet γ W δ A B ω : ℕ∞) : ℝ≥0∞) *
          ENNReal.ofReal (4 ^ (kL37 γ δ + 2) * (lamP32 δ + 1)) +
        ENNReal.ofReal (2 * (δ ^ (-(dzzCMc γ / 2)) * lamP32 δ) + 8)}

/-- **(Eq.boundDprime) for `D_δ`** (DZZ l. 1088–1103; open): with high probability, uniformly over
pairs admissible at `δ`. -/
def L32UpperCross (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ)
    (ξ ξd : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ A B : Set ℂ,
    IsXiAdmissibleAt ξ ξd δ A B → P (p32CrossEvent γ W μ δ A B)ᶜ ≤ ENNReal.ofReal (δ ^ c)

set_option maxHeartbeats 1000000 in
/-- **Upper bound of DZZ Proposition 3.2** (l. 1098–1103) from (Eq.boundDprime). -/
theorem dzz_prop32_upper {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} {ξ ξd : ℝ}
    (hX : L32UpperCross P γ W μ ξ ξd) (hξ : 0 < ξ) (hξd : ξd < dzzCMc γ) :
    ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ A B : Set ℂ,
      IsXiAdmissibleAt ξ ξd δ A B → P (prop32Upper γ W μ δ A B)ᶜ ≤ ENNReal.ofReal (δ ^ c) := by
  have := hW.isProbabilityMeasure
  set C := dzzCmc γ with hCdef
  set c := dzzCMc γ with hcdef
  have hC : 0 < C := by have := l31theta_pos hγ hγ2; rw [hCdef]; unfold dzzCmc; linarith
  have hc : 0 < c := dzzCMc_pos γ
  set ι := c / 2 with hιdef
  obtain ⟨c₁, hc₁, δ₁, hδ₁, hcr⟩ := hX
  obtain ⟨δ₃, hδ₃, hasym⟩ := l35_asym hC hc hξ hξd
  set K := l31const γ + 1 with hKdef
  have hK : 0 < K := by rw [hKdef]; unfold l31const; positivity
  set c0 := min c₁ 1 with hc0def
  have hc0 : 0 < c0 := lt_min hc₁ one_pos
  refine ⟨c0 / 2, by positivity, min (min δ₁ δ₃) (min (min (1 / 3) (Real.exp (-1)))
    ((1 / (1 + K)) ^ (2 / c0))), by positivity, fun δ hδ A B hAB => ?_⟩
  obtain ⟨hδ0, hδ⟩ := hδ
  have hδ1' : δ < δ₁ := hδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ3' : δ < δ₃ := hδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδh : δ < 1 / 3 := hδ.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hδe : δ < Real.exp (-1) := hδ.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hδK : δ < (1 / (1 + K)) ^ (2 / c0) :=
    hδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hδ1 : δ < 1 := by linarith
  obtain ⟨as1, as2, -, as4⟩ := hasym δ ⟨hδ0, hδ3'⟩
  set L := Real.log δ⁻¹ with hLdef
  have hL1 : 1 ≤ L := by
    have := Real.log_lt_log hδ0 hδe
    rw [Real.log_exp] at this
    rw [hLdef, Real.log_inv]; linarith
  have hL0 : 0 < L := by linarith
  set k := kL37 γ δ with hkdef
  set lam := lamP32 δ with hlamdef
  set Q := Real.exp (L ^ (0.8 : ℝ)) with hQdef
  have hQ1 : 1 ≤ Q := Real.one_le_exp (Real.rpow_nonneg hL0.le _)
  have hlamQ : lam ≤ Q := Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  have hlam1 : 1 ≤ lam := Real.one_le_exp (Real.rpow_nonneg hL0.le _)
  have hδι : 1 ≤ δ ^ (-ι) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ0 hδ1.le
    (by rw [hιdef]; linarith)
  have hkx : (2 : ℝ) ^ k ≤ 4 * C * L := by
    have hfl : ⌊4 * C * L⌋₊ ≠ 0 := by
      have := Nat.floor_pos.2 (show (1 : ℝ) ≤ 4 * C * L by linarith); omega
    have h1 := Nat.pow_log_le_self 2 hfl
    have h2 : ((2 ^ k : ℕ) : ℝ) ≤ (⌊4 * C * L⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h2; exact h2.trans (Nat.floor_le (by linarith))
  have ha : 4 ^ (k + 2) * (lam + 1) ≤ Q / 2 := by
    have e4 : (4 : ℝ) ^ (k + 2) = 16 * ((2 : ℝ) ^ k) ^ 2 := by
      rw [← pow_mul, pow_add, show (4 : ℝ) ^ 2 = 16 by norm_num, mul_comm,
        show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm k 2]
    have h2k : ((2 : ℝ) ^ k) ^ 2 ≤ (4 * C * L) ^ 2 := pow_le_pow_left₀ (by positivity) hkx 2
    have hl2 : lam + 1 ≤ 2 * lam := by linarith
    calc 4 ^ (k + 2) * (lam + 1) ≤ (16 * (4 * C * L) ^ 2) * (2 * lam) := by
          rw [e4]; gcongr
      _ = 1024 * C ^ 2 * L ^ 2 * Real.exp (L ^ (0.7 : ℝ)) / 2 := by
          rw [hlamdef, lamP32]; ring
      _ ≤ Q / 2 := by rw [hQdef]; linarith
  have hb : 2 * (δ ^ (-ι) * lam) + 8 ≤ 20 * δ ^ (-ι) * (Q / 2) := by
    have h1 : δ ^ (-ι) * lam ≤ δ ^ (-ι) * Q := mul_le_mul_of_nonneg_left hlamQ (by positivity)
    have h2 : 1 ≤ δ ^ (-ι) * Q := one_le_mul_of_one_le_of_one_le hδι hQ1
    nlinarith
  -- the deterministic inclusion
  have hsub : p32CrossEvent γ W μ δ A B ∩ cellSizeEvent γ W δ ⊆ prop32Upper γ W μ δ A B := by
    rintro ω ⟨hD, hcs⟩
    set m := approxLQG γ W ω with hmdef
    have hside : ∀ b, IsCell m δ b → b.side ≤ δ ^ c := fun b hb => (hcs.2 b hb).2
    set n := ⌈20 * δ ^ (-ι)⌉₊ with hndef
    have hn : (n : ℝ) ≤ 20 * δ ^ (-ι) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hlow := approxDistSet_ge_of_dist (m := m) (δ := δ) (s := δ ^ c) (n := n) hside
      (A := A) (B := B) fun x hx y hy => by
        have := hAB.dist_ge x hx y hy
        have h2 : 2 * δ ^ c * n ≤ 2 * δ ^ c * (20 * δ ^ (-ι) + 1) :=
          mul_le_mul_of_nonneg_left hn (by positivity)
        linarith
    have hN : ENNReal.ofReal (20 * δ ^ (-ι)) ≤
        ((approxDistSet m δ A B : ℕ∞) : ℝ≥0∞) := by
      refine le_trans ?_ (ENat.toENNReal_le.2 hlow)
      rw [show (n : ℕ∞) + 1 = ((n + 1 : ℕ) : ℕ∞) by push_cast; rfl, ENat.toENNReal_coe,
        ← ENNReal.ofReal_natCast]
      refine ENNReal.ofReal_le_ofReal ?_
      push_cast
      linarith [Nat.le_ceil (20 * δ ^ (-ι))]
    have hfin := ennreal_chain hD ha hb (by positivity) hN (by positivity)
    rw [prop32Upper, mem_ofPred_eq]
    refine hfin.trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
      (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))) _)
  -- the probability
  have p1 := hcr δ ⟨hδ0, hδ1'⟩ A B hAB
  have p2 := dzz_lemma31_bound hW hγ hγ2 hδ0 (show δ ≤ 1 / 2 by linarith)
  have p2' : P (cellSizeEvent γ W δ)ᶜ ≤ ENNReal.ofReal (l31const γ * δ) :=
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
      (by unfold l31const; positivity)).2 p2
  have hm1 : δ ^ c₁ ≤ δ ^ c0 := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_left _ _)
  have hm2 : δ ≤ δ ^ c0 := by
    have := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_right c₁ 1)
    rwa [Real.rpow_one] at this
  have hl31 : 0 ≤ l31const γ := by unfold l31const; positivity
  have hhalf : δ ^ (c0 / 2) ≤ 1 / (1 + K) := by
    have := Real.rpow_le_rpow hδ0.le hδK.le (by positivity : 0 ≤ c0 / 2)
    rwa [← Real.rpow_mul (by positivity), show 2 / c0 * (c0 / 2) = 1 by field_simp,
      Real.rpow_one] at this
  have hsplit : δ ^ c0 = δ ^ (c0 / 2) * δ ^ (c0 / 2) := by
    rw [← Real.rpow_add hδ0]; ring_nf
  calc P (prop32Upper γ W μ δ A B)ᶜ
      ≤ P ((p32CrossEvent γ W μ δ A B)ᶜ ∪ (cellSizeEvent γ W δ)ᶜ) := by
        refine measure_mono ?_
        rw [← compl_inter]; exact compl_subset_compl.2 hsub
    _ ≤ ENNReal.ofReal (δ ^ c₁) + ENNReal.ofReal (l31const γ * δ) :=
        (measure_union_le _ _).trans (add_le_add p1 p2')
    _ = ENNReal.ofReal (δ ^ c₁ + l31const γ * δ) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (δ ^ (c0 / 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h0 : 0 ≤ δ ^ (c0 / 2) := by positivity
        have h3 : δ ^ c₁ + l31const γ * δ ≤ (1 + K) * δ ^ c0 := by
          have : l31const γ * δ ≤ K * δ ^ c0 := by
            rw [hKdef]; nlinarith
          linarith
        have h4 : (1 + K) * δ ^ (c0 / 2) ≤ 1 := by
          rw [le_div_iff₀ (by positivity)] at hhalf; linarith
        rw [hsplit] at h3
        nlinarith

end DZZ
end LQGMetric
