/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P26Mul at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Sup
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DDen
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P21Path

/-!
# DDDF (5.75): the pathwise weak supermultiplicativity (task P2-DDDF6b)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 1314–1328 (Prop 26, Step 2). DDDF: "Using a slightly easier argument than (5.67) (since we
just have the field `φ` here), we have
`L^{(n+k)}_{1,1} ≥ e^{-ξ max osc} (min_{P, i} L^{(k,k+n)}(R_i^S(P))) Σ_{P ∈ π^k_{n+k}} e^{ξφ_{0,k}(P)}`
… Furthermore, by using a similar argument to (`eq:CoarseToPath`), we have
`Σ_{P ∈ π^k_{n+k}} e^{ξφ_{0,k}(P)} ≥ e^{-ξ max osc} 2^k L^{(k)}_{1,1}`."

* first inequality: the proof of (5.67) (`dddf_t20_step4_den`, T20DDen.lean) with `ψ` replaced by
  `φ` (so `X = 0`): `T20D.piece_lower` on every visited block (`φ_{0,n+k} = φ_{0,k} + φ_{k,n+k}`,
  `|φ_{0,k}(x) − φ_{0,k}(c_P)| ≤ 3 Obig` on `\hat P`, `T20D.osc_hatBox_le`) and the bounded overlap
  `T20D.sum_pieces_le`; the geodesic `π_{n+k}` is replaced by a crossing of length `< 2 L^{(n+k)}_{1,1}`.
* second inequality: (`eq:CoarseToPath`) = `S6.rectLen_le_coarse` (S6P21Path.lean) with weights
  `e^{ξφ_{0,k}(c_P) + 3ξ Obig}`.

Constants: `C₁ = 164 + 6ξ`, `k₀ = 2`, `J'` the four short rectangles of every block of `blkIdx k`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise LFPP T20C T20D

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DDDF (5.75)** (`eq:WeakSuperMul`, l. 1314–1328), pathwise. -/
theorem s6_eq5_75 (hW : IsWhiteNoise P W) {ξ : ℝ} (hξ : 0 < ξ) : S6Eq5_75 ξ W P := by
  classical
  refine ⟨164 + 6 * ξ, by positivity, 2, fun k hk n hn => ?_⟩
  set J' : Finset (Circle × ℂ) := (T20.blkIdx k).biUnion (shortJ k) with hJ'def
  have hJ' : J'.Nonempty := by
    refine Finset.biUnion_nonempty.2 ⟨(0, 0), ?_, ?_⟩
    · simp [T20.blkIdx]
    · simp [shortJ]
  refine ⟨J', hJ', ?_, fun Y hY hYc => ?_⟩
  · calc (J'.card : ℝ) ≤ ∑ b ∈ T20.blkIdx k, ((shortJ k b).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ T20.blkIdx k, (4 : ℝ) :=
          Finset.sum_le_sum fun b _ => by exact_mod_cast card_shortJ_le k b
      _ = 4 * (T20.blkIdx k).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 4 * (9 * 4 ^ k) := by gcongr; exact card_blkIdx_le k
      _ ≤ (164 + 6 * ξ) * 4 ^ k := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) k]
  have hk2 : 2 ≤ k := hk
  have hkn : k ≤ n + k := by omega
  have hφK := isPhiVersion_phiMN hW (Nat.zero_le k)
  have hφN := isPhiVersion_phiMN hW (Nat.zero_le (n + k))
  have hYeq : ∀ᵐ ω ∂P, ∀ x, Y x ω = phiMN W P 0 k x ω := by
    refine T20C.ae_forall_eq_of_cont (fun ω => (hYc ω).continuous) hφK.cont fun x => ?_
    have e : phi W ((2 : ℝ)⁻¹ ^ k) ((2 : ℝ)⁻¹ ^ 0) x = phi W ((2 : ℝ) ^ k)⁻¹ 1 x := by
      rw [inv_pow, pow_zero]
    exact (hY x).trans (by rw [← e]; exact (hφK.ae_eq x).symm)
  filter_upwards [ae_phiMN_add hW hkn, hYeq] with ω hadd hYω
  set O := Obig k Y ω
  set m := minShort ξ W P k (n + k) J' hJ' ω
  have hO0 : 0 ≤ O := Obig_nonneg k Y ω
  have hm0 : 0 ≤ m := Finset.le_inf' _ _ fun j _ => ENNReal.toReal_nonneg
  set f₀ : ℂ → ℝ := fun x => phiMN W P 0 (n + k) x ω
  set g : ℂ → ℝ := fun x => phiMN W P 0 k x ω
  -- a crossing of length `< 2 L^{(n+k)}_{1,1}`
  have hfin : rectLen ξ f₀ (rectAB 1 1) ≠ ⊤ :=
    rectLen_ne_top _ (by norm_num [rectAB]) (by norm_num [rectAB]) (hφN.cont ω)
  have hpos : 0 < rectLen ξ f₀ (rectAB 1 1) :=
    rectLen_pos _ (by norm_num [rectAB, MarkedRect.crossWidth]) (hφN.cont ω)
  have hlt : rectLen ξ f₀ (rectAB 1 1) < 2 * rectLen ξ f₀ (rectAB 1 1) := by
    calc rectLen ξ f₀ (rectAB 1 1) = 1 * rectLen ξ f₀ (rectAB 1 1) := (one_mul _).symm
      _ < 2 * rectLen ξ f₀ (rectAB 1 1) :=
          ENNReal.mul_lt_mul_left hpos.ne' hfin (by norm_num)
  obtain ⟨γ, hγadm, hγlen⟩ := exists_admPath_lt hlt
  -- the centre values and the oscillation on `\hat P`
  have hosc : ∀ b ∈ T20.coarseBlocks k γ, ∀ x ∈ hatBox k b,
      |g x - g (T20.dyCenter k b)| ≤ 3 * O := by
    intro b hb x hx
    have := osc_hatBox_le hk2 (hYc ω) (Finset.mem_filter.1 hb).1 hx
    simp only [g]; rw [← hYω, ← hYω]; exact this
  set E : ℤ × ℤ → ℝ := fun b => Real.exp (ξ * g (T20.dyCenter k b)) * Real.exp (-(ξ * (3 * O)))
  -- first inequality: pieces of `γ` crossing the short rectangles
  have hpiece : ∀ b ∈ T20.coarseBlocks k γ, ∃ a c, Icc a c ⊆ Icc (0 : ℝ) 1 ∧
      (∀ r ∈ Icc a c, γ r ∈ hatBox k b) ∧ ENNReal.ofReal (E b * m) ≤
        ∫⁻ r in Icc a c, lenDens ξ f₀ γ r := by
    intro b hb
    have hbI : b ∈ T20.blkIdx k := (Finset.mem_filter.1 hb).1
    refine piece_lower hk2 hγadm hb (by positivity) (fun x _ hxb => ?_) fun j hj =>
      Finset.inf'_le _ (Finset.mem_biUnion.2 ⟨b, hbI, hj⟩)
    have h3 := abs_le.1 (hosc b hb x hxb)
    have h4 := hadd x
    simp only [E]
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : g (T20.dyCenter k b) - 3 * O + phiMN W P k (n + k) x ω ≤ f₀ x := by
      simp only [f₀, g] at h3 ⊢; linarith [h3.1]
    nlinarith
  have hsum := sum_pieces_le (K := k) (γ := γ) (T20.coarseBlocks k γ)
    (lenDens ξ f₀ γ) (fun b => ENNReal.ofReal (E b * m)) hpiece
  rw [← lfppLen_eq] at hsum
  have hbound : ∑ b ∈ T20.coarseBlocks k γ, ENNReal.ofReal (E b * m) ≤
      ENNReal.ofReal 32 * rectLen ξ f₀ (rectAB 1 1) := by
    refine hsum.trans ?_
    rw [show (32 : ℝ) = 16 * 2 by norm_num, ENNReal.ofReal_mul (by norm_num), mul_assoc]
    gcongr
    · norm_num
    · rw [ENNReal.ofReal_ofNat]; exact hγlen.le
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hbound
  rw [ENNReal.toReal_sum (fun b _ => ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)] at hreal
  have hreal' : ∑ b ∈ T20.coarseBlocks k γ, E b * m ≤ 32 * lenN ξ W P 1 1 (n + k) ω := by
    refine le_trans (le_of_eq ?_) hreal
    exact Finset.sum_congr rfl fun b _ => (ENNReal.toReal_ofReal (by positivity)).symm
  -- second inequality: (`eq:CoarseToPath`)
  set w : ℤ × ℤ → ℝ := fun b => Real.exp (ξ * g (T20.dyCenter k b)) * Real.exp (ξ * (3 * O))
  have hw : ∀ b ∈ T20.coarseBlocks k γ, ∀ x ∈ hatBox k b, Real.exp (ξ * g x) ≤ w b := by
    intro b hb x hx
    have h3 := abs_le.1 (hosc b hb x hx)
    simp only [w]; rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [h3.2]
  have hcoarse := S6.rectLen_le_coarse hγadm hw
  have hLk : lenN ξ W P 1 1 k ω ≤ 4 * (2 : ℝ)⁻¹ ^ k * ∑ b ∈ T20.coarseBlocks k γ, w b := by
    have h0 : 0 ≤ 4 * (2 : ℝ)⁻¹ ^ k * ∑ b ∈ T20.coarseBlocks k γ, w b := by positivity
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcoarse
    rwa [ENNReal.toReal_ofReal h0] at this
  -- combination
  set S₀ := ∑ b ∈ T20.coarseBlocks k γ, Real.exp (ξ * g (T20.dyCenter k b))
  have hS0 : 0 ≤ S₀ := Finset.sum_nonneg fun b _ => (Real.exp_pos _).le
  have hw' : ∑ b ∈ T20.coarseBlocks k γ, w b = Real.exp (ξ * (3 * O)) * S₀ := by
    simp only [w, S₀, Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
  have hE' : ∑ b ∈ T20.coarseBlocks k γ, E b * m = Real.exp (-(ξ * (3 * O))) * m * S₀ := by
    simp only [E, S₀, Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
  rw [hw'] at hLk
  rw [hE'] at hreal'
  have hL0 : 0 ≤ lenN ξ W P 1 1 k ω := ENNReal.toReal_nonneg
  have h2k : (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ k = 1 := by rw [← mul_pow]; norm_num
  have hexp : Real.exp (-((164 + 6 * ξ) * O)) ≤
      Real.exp (-(ξ * (3 * O))) * Real.exp (-(ξ * (3 * O))) := by
    rw [← Real.exp_add]; refine Real.exp_le_exp.2 ?_; nlinarith
  have hee : Real.exp (-(ξ * (3 * O))) * Real.exp (ξ * (3 * O)) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hA : 0 ≤ (2 : ℝ) ^ k * m := by positivity
  calc Real.exp (-((164 + 6 * ξ) * O)) * ((2 : ℝ) ^ k * m) * lenN ξ W P 1 1 k ω
      ≤ Real.exp (-(ξ * (3 * O))) * Real.exp (-(ξ * (3 * O))) * ((2 : ℝ) ^ k * m) *
          (4 * (2 : ℝ)⁻¹ ^ k * (Real.exp (ξ * (3 * O)) * S₀)) := by
        gcongr
    _ = 4 * ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ k) *
          (Real.exp (-(ξ * (3 * O))) * Real.exp (ξ * (3 * O))) *
          (Real.exp (-(ξ * (3 * O))) * m * S₀) := by ring
    _ = 4 * (Real.exp (-(ξ * (3 * O))) * m * S₀) := by rw [h2k, hee]; ring
    _ ≤ 4 * (32 * lenN ξ W P 1 1 (n + k) ω) := by gcongr
    _ ≤ (164 + 6 * ξ) * lenN ξ W P 1 1 (n + k) ω := by
        have : 0 ≤ lenN ξ W P 1 1 (n + k) ω := ENNReal.toReal_nonneg
        nlinarith

end DDDF
end LQGMetric
