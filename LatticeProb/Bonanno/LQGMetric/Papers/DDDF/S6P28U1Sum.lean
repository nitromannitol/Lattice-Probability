/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P28U1Sum at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28U1Lvl

/-!
# DDDF Prop 28 Part 1 Step 1 for the family: the chaining sum at scale `K` (task P2-DDDF28U)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1414–1418: for `φ_δ` (`δ ≤ 2^{-N}`), a.s., for all
`1 ≤ K < N` and all `x, y ∈ [0,1]²` whose coordinates differ by less than `2^{-K}`,
`d(x, y) ≤ 2E + R_K` (`ae_chain`), where `E` bounds the distances `≤ 4·2^{-N}` and
`R_K = 8 e^{ξ max|φ_{0,K}|} Z^S_K + 24 Σ_{K ≤ k < N} e^{ξ max|φ_{0,k+1}|} Z_{k}` is the sum of
the decoupled `ℓ^q` norms of the crossings of levels `≥ K` (`RK`): `chain_restr` +
`ae_len21_le` (`eq:Decouplage`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6P28U

open LFPP T20E Blueprint WhiteNoise S6D SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- the index set of the shifted squares of scale `K` -/
def idxS (K : ℕ) : Finset ((ℕ × ℕ) × Fin 4) :=
  (Finset.range (2 ^ K - 1) ×ˢ Finset.range (2 ^ K - 1)) ×ˢ Finset.univ

lemma card_idxS_le (K : ℕ) : ((idxS K).card : ℝ) ≤ 4 ^ (K + 1) := by
  simp only [idxS, Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_fin]
  have h : (2 ^ K - 1) * (2 ^ K - 1) * 4 ≤ 4 ^ (K + 1) := by
    have : 2 ^ K - 1 ≤ 2 ^ K := Nat.sub_le _ _
    calc (2 ^ K - 1) * (2 ^ K - 1) * 4 ≤ 2 ^ K * 2 ^ K * 4 := by gcongr
      _ = 4 ^ (K + 1) := by rw [← mul_pow, pow_succ]; norm_num
  exact_mod_cast h

lemma card_idxSet_le (k : ℕ) : ((idxSet k).card : ℝ) ≤ 4 ^ (k + 1 + 1) := by
  have h : (idxSet k).card = 4 ^ (k + 1) := by
    simp only [idxSet, Finset.card_product, Finset.card_range, Finset.card_univ,
      Fintype.card_fin]
    rw [← mul_pow, pow_succ]; norm_num
  rw [h]; push_cast
  exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)

/-- the decoupled bound of the halves of level `k` (scale `k + 1`) -/
def XH (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (δ : ℝ) (q k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (ξ * supAbs (fun z => phiMN W P 0 (k + 1) z ω))) *
    ZqG ξ (fun x => phiVer W P δ ((2 : ℝ)⁻¹ ^ (k + 1)) x ω) (k + 1) q (idxSet k)
      (fun r => hm k r.1.1 r.1.2 r.2)

/-- the decoupled bound of the shifted squares of scale `K` -/
def XS (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (δ : ℝ) (q K : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (ξ * supAbs (fun z => phiMN W P 0 K z ω))) *
    ZqG ξ (fun x => phiVer W P δ ((2 : ℝ)⁻¹ ^ K) x ω) K q (idxS K)
      (fun r => hmS K r.1.1 r.1.2 r.2)

/-- the chaining sum at scale `K` down to level `m` -/
def RK (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (δ : ℝ) (q K m : ℕ) (ω : Ω) : ℝ≥0∞ :=
  8 * XS ξ W P δ q K ω + 24 * ∑ t ∈ Finset.range (m - K + 1), XH ξ W P δ q (K + t) ω

lemma measurable_XH (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) (q k : ℕ)
    (hδk : δ ≤ (2 : ℝ)⁻¹ ^ (k + 1)) : Measurable (XH ξ W P δ q k) := by
  have hφF := isPhiVersion_phiMN (P := P) hW (Nat.zero_le (k + 1))
  have hφG := isPhiVersion_phiVer hW hδ hδk
  have hFm : Measurable (fun ω x => phiMN W P 0 (k + 1) x ω) :=
    measurable_pi_iff.2 fun x => hφF.meas x
  have hGm : Measurable (fun ω x => phiVer W P δ ((2 : ℝ)⁻¹ ^ (k + 1)) x ω) :=
    measurable_pi_iff.2 fun x => hφG.meas x
  exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (((measurable_comap_supAbs _ hφF.cont).mono hFm.comap_le le_rfl).const_mul ξ))).mul
    ((measurable_comap_ZqG _ hφG.cont _ q _ _).mono hGm.comap_le le_rfl)

lemma measurable_XS (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) (q K : ℕ)
    (hδK : δ ≤ (2 : ℝ)⁻¹ ^ K) : Measurable (XS ξ W P δ q K) := by
  have hφF := isPhiVersion_phiMN (P := P) hW (Nat.zero_le K)
  have hφG := isPhiVersion_phiVer hW hδ hδK
  have hFm : Measurable (fun ω x => phiMN W P 0 K x ω) :=
    measurable_pi_iff.2 fun x => hφF.meas x
  have hGm : Measurable (fun ω x => phiVer W P δ ((2 : ℝ)⁻¹ ^ K) x ω) :=
    measurable_pi_iff.2 fun x => hφG.meas x
  exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (((measurable_comap_supAbs _ hφF.cont).mono hFm.comap_le le_rfl).const_mul ξ))).mul
    ((measurable_comap_ZqG _ hφG.cont _ q _ _).mono hGm.comap_le le_rfl)

lemma inv_two_pow_anti {a b : ℕ} (h : a ≤ b) : (2 : ℝ)⁻¹ ^ b ≤ (2 : ℝ)⁻¹ ^ a :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

lemma measurable_RK (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) {N : ℕ}
    (hδN : δ ≤ (2 : ℝ)⁻¹ ^ N) (q : ℕ) {K : ℕ} (hKN : K + 1 ≤ N) :
    Measurable (RK ξ W P δ q K (N - 1)) := by
  refine ((measurable_XS hW hδ q K (hδN.trans (inv_two_pow_anti (by omega)))).const_mul _).add
    ((Finset.measurable_sum _ fun t ht => ?_).const_mul _)
  have : t ≤ N - 1 - K := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
  exact measurable_XH hW hδ q (K + t) (hδN.trans (inv_two_pow_anti (by omega)))

/-- **the chaining at scale `K` for `φ_δ`** (DDDF l. 1414–1418), pathwise a.s. -/
theorem ae_chain (hW : IsWhiteNoise P W) (hξ : 0 ≤ ξ) {δ : ℝ} {N : ℕ} (hδ : 0 < δ)
    (hδN : δ ≤ (2 : ℝ)⁻¹ ^ N) {q : ℕ} (hq : q ≠ 0) :
    ∀ᵐ ω ∂P, ∀ K : ℕ, 1 ≤ K → K + 1 ≤ N → ∀ E : ℝ≥0∞,
      (∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare, ‖w - z‖ ≤ 2 * (2 : ℝ)⁻¹ ^ (N - 1) →
        lfppDOn ξ (fun x => phiVer W P δ 1 x ω) closedUnitSquare z w ≤ E) →
      ∀ x ∈ closedUnitSquare, ∀ y ∈ closedUnitSquare,
        |x.re - y.re| < (2 : ℝ)⁻¹ ^ K → |x.im - y.im| < (2 : ℝ)⁻¹ ^ K →
        lfppDOn ξ (fun x => phiVer W P δ 1 x ω) closedUnitSquare x y ≤
          2 * E + RK ξ W P δ q K (N - 1) ω := by
  -- halves of all levels `k` with `k + 1 ≤ N`
  have hH : ∀ᵐ ω ∂P, ∀ k : ℕ, k + 1 ≤ N → ∀ r ∈ idxSet k,
      len21 ξ (fun x => phiVer W P δ 1 x ω) (k + 1) (hm k r.1.1 r.1.2 r.2) ≤ XH ξ W P δ q k ω := by
    refine ae_all_iff.2 fun k => ?_
    by_cases hk : k + 1 ≤ N
    · filter_upwards [ae_len21_le hW hξ hδ (hδN.trans (inv_two_pow_anti hk)) hq (idxSet k)
        (fun r => hm k r.1.1 r.1.2 r.2) (fun r hr => by
          simp only [idxSet, Finset.mem_product, Finset.mem_range, Finset.mem_univ,
            and_true] at hr
          exact hm_sub hr.1 hr.2 r.2)] with ω hω _ r hr using hω r hr
    · exact ae_of_all _ fun ω h => absurd h hk
  have hS : ∀ᵐ ω ∂P, ∀ K : ℕ, K ≤ N → ∀ r ∈ idxS K,
      len21 ξ (fun x => phiVer W P δ 1 x ω) K (hmS K r.1.1 r.1.2 r.2) ≤ XS ξ W P δ q K ω := by
    refine ae_all_iff.2 fun K => ?_
    by_cases hK : K ≤ N
    · filter_upwards [ae_len21_le hW hξ hδ (hδN.trans (inv_two_pow_anti hK)) hq (idxS K)
        (fun r => hmS K r.1.1 r.1.2 r.2) (fun r hr => by
          simp only [idxS, Finset.mem_product, Finset.mem_range, Finset.mem_univ,
            and_true] at hr
          exact hmS_sub (by omega) (by omega) r.2)] with ω hω _ r hr using hω r hr
    · exact ae_of_all _ fun ω h => absurd h hK
  filter_upwards [hH, hS] with ω hωH hωS K hK1 hKN E hE x hx y hy hre him
  have hφ := isPhiVersion_phiVer hW hδ (hδN.trans (pow_le_one₀ (by norm_num) (by norm_num)))
  have h := chain_restr (ξ := ξ) (hφ.cont ω) (m := N - 1) hK1 (by omega)
    (fun k => XH ξ W P δ q k ω)
    (fun k _ hk2 i hi j hj e => hωH k (by omega) ((i, j), e) (by
      simp only [idxSet, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
      exact ⟨hi, hj⟩))
    (XS ξ W P δ q K ω)
    (fun i j hi hj e => hωS K (by omega) ((i, j), e) (by
      simp only [idxS, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
      exact ⟨by omega, by omega⟩))
    hE hx hy hre him
  refine h.trans (le_of_eq ?_)
  simp only [RK]; ring

end S6P28U
end DDDF
end LQGMetric
