/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2Sum at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Box

/-!
# DZZ §2.2: uniform Gaussian tail of a sum of scale bands (task P2-DZZPRE, WP-112)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`), proof of Lemma 2.7
(`lem-tilde-h-eta`, l. 571–594), repeated verbatim for Lemma 2.8 (`lem-hat-h-eta`, l. 616–621):
with `Δ_i` the difference of the two fields restricted to the scale band `(2^{-i}, 2^{-i+1})`,
"uniformly in `v` and `i`, `Var Δ_i(v) = O(1) e^{−Ω(i²)}` (eq-variance-truncation) …
`Var(Δ_i(v) − Δ_i(u)) ≤ O(1) min{e^{−Ω((i+1)²)}, 2^i|u − v|}` (eq-feb25). Combined with Lemmas 2.1
and 2.3, this gives (eq-boring-2) … (eq-boring-3) …", and summing over `i`,
`P(max_v Σ_i |Δ_i(v)| ≥ λ) ≤ O(1) e^{−Ω(λ²)}`.

`dzz_sum_sup_tail` is this probabilistic core, for continuous centered Gaussian fields `Δ_i` on a
box `ferniqueBox x₀ s` (`s ≤ 1`) with `Var Δ_i(v) ≤ K ρ^i` (`ρ < 1`; DZZ have the stronger
`e^{−Ω(i²)}`) and `E(Δ_i(v) − Δ_i(u))² ≤ K 2^i |u − v|`; the constant depends only on `K, ρ`.

Following DZZ, each level `i` is handled by a union bound over sub-boxes, Lemma 2.3 (Fernique) on
each sub-box and the Gaussian concentration (Lemma 2.1, Borell–TIS form) at a level `t_i` with
`Σ_i t_i ≤ λ`. Deviation (bookkeeping only): DZZ use sub-boxes of side `≍ i^{-4} 2^{-i}` around
the grid `𝔠_{i + 4 log₂ i}` and levels `λ(i+1)^{-2}`; we use sub-boxes of side `≤ (ρ/2)^i` and
geometric levels `t_i = λ(1 − θ)θ^i`, `θ = ρ^{1/4}`, which only needs `Var Δ_i ≤ K ρ^i`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace LQGMetric
namespace DZZ

open SupTail

universe u

/-- **DZZ, proof of Lemma 2.7 (l. 571–594) and Lemma 2.8 (l. 616–621)**: if continuous centered
Gaussian fields `Δ_i` on a box of side `s ≤ 1` satisfy `Var Δ_i(v) ≤ K ρ^i` and
`E(Δ_i(v) − Δ_i(u))² ≤ K 2^i |u − v|`, then
`P(∃ v ∈ box, ∃ n, λ ≤ Σ_{i<n} |Δ_i(v)|) ≤ C e^{−λ²/C}` with `C = C(K, ρ)`. -/
theorem dzz_sum_sup_tail {K ρ : ℝ} (hK : 0 < K) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (x₀ : ℂ) (s : ℝ),
      0 < s → s ≤ 1 → ∀ Δ : ℕ → ℂ → Ω → ℝ, (∀ i, IsGaussianProcess (Δ i) P) →
      (∀ i v, ∫ ω, Δ i v ω ∂P = 0) →
      (∀ i ω, ContinuousOn (fun v => Δ i v ω) (ferniqueBox x₀ s)) →
      (∀ i, ∀ v ∈ ferniqueBox x₀ s, Var[Δ i v; P] ≤ K * ρ ^ i) →
      (∀ i, ∀ u ∈ ferniqueBox x₀ s, ∀ v ∈ ferniqueBox x₀ s,
        ∫ ω, (Δ i v ω - Δ i u ω) ^ 2 ∂P ≤ K * 2 ^ i * ‖u - v‖) →
      ∀ lam : ℝ, 0 ≤ lam →
        P.real {ω | ∃ v ∈ ferniqueBox x₀ s, ∃ n : ℕ, lam ≤ ∑ i ∈ Finset.range n, |Δ i v ω|} ≤
          C * Real.exp (-lam ^ 2 / C) := by
  -- the parameters
  set r := Real.sqrt ρ with hr_def
  set θ := Real.sqrt r with hθ_def
  have hr0 : 0 < r := Real.sqrt_pos.2 hρ0
  have hθ0 : 0 < θ := Real.sqrt_pos.2 hr0
  have hθ2 : θ ^ 2 = r := Real.sq_sqrt hr0.le
  have hr2 : r ^ 2 = ρ := Real.sq_sqrt hρ0.le
  have hθ4 : θ ^ 4 = ρ := by rw [show θ ^ 4 = (θ ^ 2) ^ 2 by ring, hθ2, hr2]
  have hθ1 : θ < 1 := by
    by_contra h
    push_neg at h
    have : 1 ≤ θ ^ 4 := one_le_pow₀ h
    linarith
  have hθ21 : θ ^ 2 < 1 := by nlinarith
  set w := (1 - θ) ^ 2 / (4 * K) with hw_def
  have hw : 0 < w := by
    have : 0 < 1 - θ := by linarith
    positivity
  set q := (θ ^ 2)⁻¹ with hq_def
  have hq1 : 1 < q := (one_lt_inv₀ (by positivity)).2 hθ21
  have h8 : 1 ≤ 8 / ρ ^ 2 := by
    rw [one_le_div (by positivity)]; nlinarith
  set Λ := Real.log (8 / ρ ^ 2) / (w * (q - 1)) with hΛ_def
  have hwq : 0 < w * (q - 1) := mul_pos hw (by linarith)
  have hΛ : 0 ≤ Λ := div_nonneg (Real.log_nonneg h8) hwq.le
  set A := 2 * Real.exp (ferniqueCF ^ 2 / 2) with hA_def
  have hA : 0 < A := by positivity
  obtain ⟨C, hC_def⟩ : ∃ C : ℝ, C = 8 * A + w⁻¹ + 2 * Λ + 3 := ⟨_, rfl⟩
  have hwi : 0 < w⁻¹ := inv_pos.2 hw
  have hC0 : 0 < C := by rw [hC_def]; positivity
  have h8A : 8 * A ≤ C := by linarith only [hC_def, hwi, hΛ]
  have hwiC : w⁻¹ ≤ C := by linarith only [hC_def, hA, hΛ]
  have hΛC : 2 * Λ ≤ C := by linarith only [hC_def, hA, hwi]
  have hC3 : 3 ≤ C := by linarith only [hC_def, hA, hwi, hΛ]
  refine ⟨C, hC0, ?_⟩
  intro Ω _ P x₀ s hs hs1 Δ hΔ h0 hc hvar hinc lam hlam
  have hP : IsProbabilityMeasure P := (hΔ 0).isProbabilityMeasure
  set S := {ω | ∃ v ∈ ferniqueBox x₀ s, ∃ n : ℕ, lam ≤ ∑ i ∈ Finset.range n, |Δ i v ω|}
  by_cases hsmall : lam ^ 2 ≤ Λ
  · have h1 : P.real S ≤ 1 := measureReal_le_one
    have hx : lam ^ 2 / C ≤ 1 / 2 := by
      rw [div_le_iff₀ hC0]; linarith only [hsmall, hΛC]
    have he : 1 / 2 ≤ Real.exp (-lam ^ 2 / C) := by
      have := Real.add_one_le_exp (-lam ^ 2 / C)
      rw [neg_div] at this ⊢
      linarith only [this, hx]
    have : 1 ≤ C * Real.exp (-lam ^ 2 / C) := by
      nlinarith only [he, hC3]
    linarith only [this, h1]
  push_neg at hsmall
  -- the levels
  set b : ℕ → ℝ := fun i => (ρ / 2) ^ i with hb_def
  have hb0 : ∀ i, 0 < b i := fun i => by positivity
  set m : ℕ → ℕ := fun i => ⌈s / b i⌉₊ with hm_def
  have hm0 : ∀ i, 0 < m i := fun i => Nat.ceil_pos.2 (div_pos hs (hb0 i))
  set h : ℕ → ℝ := fun i => s / m i with hh_def
  have hh0 : ∀ i, 0 < h i := fun i => div_pos hs (Nat.cast_pos.2 (hm0 i))
  have hh_le : ∀ i, h i ≤ b i := by
    intro i
    rw [hh_def, div_le_iff₀ (Nat.cast_pos.2 (hm0 i))]
    have := Nat.le_ceil (s / b i)
    rw [div_le_iff₀ (hb0 i)] at this
    simp only [hm_def]
    linarith [mul_comm (b i) (⌈s / b i⌉₊ : ℝ)]
  set σ : ℕ → ℝ := fun i => Real.sqrt (K * ρ ^ i) with hσ_def
  have hσ2 : ∀ i, σ i ^ 2 = K * ρ ^ i := fun i => Real.sq_sqrt (by positivity)
  have hσ0 : ∀ i, 0 < σ i := fun i => Real.sqrt_pos.2 (by positivity)
  set t : ℕ → ℝ := fun i => lam * (1 - θ) * θ ^ i with ht_def
  have ht0 : ∀ i, 0 ≤ t i := fun i => by
    have : 0 ≤ 1 - θ := by linarith
    positivity
  set E : (i : ℕ) → Fin (m i) × Fin (m i) → Set Ω := fun i kl =>
    {ω | t i ≤ ⨆ v : subBox x₀ s (m i) kl.1 kl.2, |Δ i v ω|} with hE_def
  -- the event is covered by the level events
  have hsub : S ⊆ ⋃ i, ⋃ kl, E i kl := by
    rintro ω ⟨v, hv, n, hn⟩
    by_contra hne
    simp only [mem_iUnion, not_exists] at hne
    have hlt : ∀ i, |Δ i v ω| < t i := by
      intro i
      obtain ⟨k, l, hkl⟩ := exists_mem_subBox hs (hm0 i) hv
      have h1 := hne i (k, l)
      simp only [hE_def, mem_ofPred_eq, not_le] at h1
      refine lt_of_le_of_lt ?_ h1
      have : CompactSpace (subBox x₀ s (m i) k l) :=
        isCompact_iff_compactSpace.1 (isCompact_ferniqueBox _ _)
      exact le_ciSup (f := fun v' : subBox x₀ s (m i) k l => |Δ i v' ω|)
        (bddAbove_range_of_continuous (X := fun (v' : subBox x₀ s (m i) k l) ω => |Δ i v' ω|)
          (fun ω' => (continuousOn_iff_continuous_domRestrict.1
            ((hc i ω').mono (subBox_subset hs k l))).abs) ω) ⟨v, hkl⟩
    have hsum : ∑ i ∈ Finset.range n, |Δ i v ω| ≤ ∑ i ∈ Finset.range n, t i :=
      Finset.sum_le_sum fun i _ => (hlt i).le
    have hgeom : ∑ i ∈ Finset.range n, t i < lam := by
      have hlam0 : 0 < lam := by
        rcases hlam.lt_or_eq with h | h
        · exact h
        · rw [← h] at hsmall; simp at hsmall; linarith
      simp only [ht_def]
      rw [← Finset.mul_sum, geom_sum_eq hθ1.ne n]
      have hne1 : θ - 1 ≠ 0 := sub_ne_zero.2 hθ1.ne
      have e : lam * (1 - θ) * ((θ ^ n - 1) / (θ - 1)) = lam * (1 - θ ^ n) := by
        rw [mul_assoc, mul_div_assoc',
          show (1 - θ) * (θ ^ n - 1) / (θ - 1) = 1 - θ ^ n by rw [div_eq_iff hne1]; ring]
      rw [e]
      have : 0 < θ ^ n := pow_pos hθ0 n
      nlinarith
    linarith
  -- the bound at each level and sub-box
  have hE : ∀ i kl, P.real (E i kl) ≤ A * Real.exp (-lam ^ 2 * w * q ^ i) := by
    rintro i ⟨k, l⟩
    have hQ := subBox_subset (x₀ := x₀) hs k l
    have hLh : K * 2 ^ i * h i ≤ K * ρ ^ i := by
      have : (2 : ℝ) ^ i * b i = ρ ^ i := by
        simp only [hb_def]; rw [← mul_pow]; congr 1; ring
      calc K * 2 ^ i * h i ≤ K * 2 ^ i * b i :=
            mul_le_mul_of_nonneg_left (hh_le i) (by positivity)
        _ = K * ρ ^ i := by rw [mul_assoc, this]
    have hM : ferniqueCF * Real.sqrt (K * 2 ^ i * h i) ≤ ferniqueCF * σ i :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hLh) ferniqueCF_pos.le
    have key := dzz_box_sup_abs_tail (X := Δ i) (hΔ i) (h0 i) (hh0 i) (by positivity)
      (fun ω => (hc i ω).mono hQ) (fun u hu v hv => hinc i u (hQ hu) v (hQ hv))
      (fun v hv => (hvar i v (hQ hv)).trans_eq (hσ2 i).symm) hM (ht0 i)
    refine key.trans (le_of_eq ?_)
    have e1 : (ferniqueCF * σ i) ^ 2 / (2 * σ i ^ 2) = ferniqueCF ^ 2 / 2 := by
      have := (hσ0 i).ne'
      rw [mul_pow, mul_div_mul_right _ _ (pow_ne_zero 2 this)]
    have e2 : -t i ^ 2 / (2 * (2 * σ i ^ 2)) = -lam ^ 2 * w * q ^ i := by
      have hy : ρ ^ i = (θ ^ i) ^ 4 := by rw [← hθ4, ← pow_mul, ← pow_mul, mul_comm]
      have hq' : q ^ i = ((θ ^ i) ^ 2)⁻¹ := by
        rw [hq_def, inv_pow, ← pow_mul, ← pow_mul, mul_comm]
      rw [hσ2, hy, hq', ht_def, hw_def]
      have := pow_ne_zero i hθ0.ne'
      have := hK.ne'
      field_simp
      ring
    rw [e1, e2]
  -- summation over the levels
  set g : ℕ → ℝ := fun i => 4 * A * Real.exp (-lam ^ 2 * w) * (1 / 2) ^ i with hg_def
  have hg0 : ∀ i, 0 ≤ g i := fun i => by positivity
  have hterm : ∀ i, (m i : ℝ) * (m i : ℝ) * (A * Real.exp (-lam ^ 2 * w * q ^ i)) ≤ g i := by
    intro i
    have hmi : (m i : ℝ) ≤ 2 * (2 / ρ) ^ i := by
      have h1 : (m i : ℝ) < s / b i + 1 := Nat.ceil_lt_add_one (div_pos hs (hb0 i)).le
      have h2 : s / b i ≤ (2 / ρ) ^ i := by
        rw [div_le_iff₀ (hb0 i)]
        have : (2 / ρ) ^ i * b i = 1 := by
          simp only [hb_def]; rw [← mul_pow]
          have : 2 / ρ * (ρ / 2) = 1 := by field_simp
          rw [this, one_pow]
        linarith
      have h3 : 1 ≤ (2 / ρ) ^ i := one_le_pow₀ (by rw [le_div_iff₀ hρ0]; linarith)
      linarith
    have hm2 : (m i : ℝ) * (m i : ℝ) ≤ 4 * (4 / ρ ^ 2) ^ i := by
      have h0' : (0 : ℝ) ≤ m i := Nat.cast_nonneg _
      calc (m i : ℝ) * (m i : ℝ) ≤ (2 * (2 / ρ) ^ i) * (2 * (2 / ρ) ^ i) :=
            mul_le_mul hmi hmi h0' (by positivity)
        _ = 4 * (4 / ρ ^ 2) ^ i := by
            rw [show (4 : ℝ) / ρ ^ 2 = (2 / ρ) ^ 2 by ring, ← pow_mul, mul_comm 2 i, pow_mul]
            ring
    have hexp : Real.exp (-lam ^ 2 * w * q ^ i) ≤ Real.exp (-lam ^ 2 * w) * (ρ ^ 2 / 8) ^ i := by
      have hbern : 1 + (i : ℝ) * (q - 1) ≤ q ^ i := by
        have := one_add_mul_le_pow (a := q - 1) (by linarith) i
        simpa using this
      have hlog : Real.log (8 / ρ ^ 2) ≤ lam ^ 2 * w * (q - 1) := by
        have := hsmall
        rw [hΛ_def, div_lt_iff₀ hwq] at this
        nlinarith
      have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
      have hlw : 0 ≤ lam ^ 2 * w := by positivity
      have hexp' : -lam ^ 2 * w * q ^ i ≤ -lam ^ 2 * w + i * (-Real.log (8 / ρ ^ 2)) := by
        nlinarith [mul_le_mul_of_nonneg_left hbern hlw, mul_le_mul_of_nonneg_left hlog hi]
      refine (Real.exp_le_exp.2 hexp').trans (le_of_eq ?_)
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by positivity), inv_div]
    calc (m i : ℝ) * (m i : ℝ) * (A * Real.exp (-lam ^ 2 * w * q ^ i))
        ≤ 4 * (4 / ρ ^ 2) ^ i * (A * (Real.exp (-lam ^ 2 * w) * (ρ ^ 2 / 8) ^ i)) := by
          gcongr
      _ = g i := by
          simp only [hg_def]
          have : (4 / ρ ^ 2) ^ i * (ρ ^ 2 / 8) ^ i = (1 / 2) ^ i := by
            rw [← mul_pow]; congr 1; field_simp; norm_num
          rw [show 4 * (4 / ρ ^ 2) ^ i * (A * (Real.exp (-lam ^ 2 * w) * (ρ ^ 2 / 8) ^ i)) =
            4 * A * Real.exp (-lam ^ 2 * w) * ((4 / ρ ^ 2) ^ i * (ρ ^ 2 / 8) ^ i) by ring, this]
  have hgs : Summable g := (summable_geometric_two.mul_left _)
  have hgsum : ∑' i, g i = 8 * A * Real.exp (-lam ^ 2 * w) := by
    simp only [hg_def]; rw [tsum_mul_left, tsum_geometric_two]; ring
  have hPS : P S ≤ ENNReal.ofReal (8 * A * Real.exp (-lam ^ 2 * w)) := by
    calc P S ≤ P (⋃ i, ⋃ kl, E i kl) := measure_mono hsub
      _ ≤ ∑' i, P (⋃ kl, E i kl) := measure_iUnion_le _
      _ ≤ ∑' i, ENNReal.ofReal (g i) := by
          refine ENNReal.tsum_le_tsum fun i => (measure_iUnion_fintype_le _ _).trans ?_
          calc ∑ kl, P (E i kl) ≤ ∑ _kl : Fin (m i) × Fin (m i),
                ENNReal.ofReal (A * Real.exp (-lam ^ 2 * w * q ^ i)) :=
                Finset.sum_le_sum fun kl _ => by
                  rw [← ofReal_measureReal]; exact ENNReal.ofReal_le_ofReal (hE i kl)
            _ = ENNReal.ofReal ((m i : ℝ) * (m i : ℝ) * (A * Real.exp (-lam ^ 2 * w * q ^ i))) := by
                rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), Finset.sum_const,
                  Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul,
                  Nat.cast_mul, mul_assoc]
            _ ≤ ENNReal.ofReal (g i) := ENNReal.ofReal_le_ofReal (hterm i)
      _ = ENNReal.ofReal (∑' i, g i) := (ENNReal.ofReal_tsum_of_nonneg hg0 hgs).symm
      _ = ENNReal.ofReal (8 * A * Real.exp (-lam ^ 2 * w)) := by rw [hgsum]
  have hfin : P.real S ≤ 8 * A * Real.exp (-lam ^ 2 * w) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hPS
  refine hfin.trans ?_
  have hwC : 1 ≤ w * C := by
    have : w⁻¹ ≤ C := hwiC
    calc (1 : ℝ) = w * w⁻¹ := (mul_inv_cancel₀ hw.ne').symm
      _ ≤ w * C := mul_le_mul_of_nonneg_left this hw.le
  have hex : Real.exp (-lam ^ 2 * w) ≤ Real.exp (-lam ^ 2 / C) := by
    refine Real.exp_le_exp.2 ?_
    rw [neg_div, neg_mul, neg_le_neg_iff, div_le_iff₀ hC0]
    have := mul_le_mul_of_nonneg_left hwC (sq_nonneg lam)
    linarith only [this]
  exact mul_le_mul h8A hex (Real.exp_pos _).le hC0.le

end DZZ
end LQGMetric
