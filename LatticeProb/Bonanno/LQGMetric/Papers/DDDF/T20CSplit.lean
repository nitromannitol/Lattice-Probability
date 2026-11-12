/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20CSplit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CMain
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BMain

/-!
# DDDF Theorem 20, Step 4: the pathwise bound from (5.66) and (5.67) (task P2-DDDFT20c)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1095–1155. The pathwise bound `T20Step4Pathwise`
is split into DDDF's two displayed estimates:

* `T20Step4Num` = (5.65)+(5.66) (`eq:Ineq`, `eq:Num`, l. 1103–1123): for a visited block `b`,
  `(log L^b − log L)_+ ≤ η + C K^{d} e^{CX} e^{C K^{ε₀} O} e^{ξψ_{0,K}(P')} max L(R^L) / L`,
  `P'` a block of `π^K` at index distance `≤ C(K+1)` from `b` (DDDF evaluate `ψ_{0,K}` at
  the centre of `b` itself; `b` need not meet the near-geodesic, so we pass to a block `P'` of
  `π^K` near `b`, at the cost of the oscillation factor); `η` from `(1+η)`-near-geodesics;
* `T20Step4Den` = (5.67) (`eq:Denum`, l. 1131–1146):
  `e^{-CX} e^{-C K^{ε₀} O} min L(R^S) Σ_{P ∈ π^K} e^{ξψ_{0,K}(P)} ≤ C L`.

`t20Step4Pathwise_of_num_den` gathers them as DDDF l. 1150–1155: `(a+b)² ≤ 2a² + 2b²`,
`|nearIdx K| ≤ 16·4^K`, and each `P ∈ π^K` serves at most `(2C(K+1)+1)²` blocks `b`
(`T20C.sum_fiber_le`). `dddf_thm20_of_num_den` is DDDF Theorem 20 from (5.66), (5.67) and
Condition (T).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

namespace T20C

/-- `L_n(ψ) = L^{(n)}_{1,1}(ψ)` -/
def lenPsi (ξ : ℝ) (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (n : ℕ) (ω : Ω) : ℝ :=
  (rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 1 1)).toReal

/-- `max_{J} L^{(K,n)}(R^L, φ)` over long rectangles `u 2^{-K} R_{3,1} + c` -/
def maxLong (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (K n : ℕ) (J : Finset (Circle × ℂ))
    (hJ : J.Nonempty) (ω : Ω) : ℝ :=
  J.sup' hJ fun j => T20B.mrectLen ξ (fun x => phiMN W P K n x ω) K j.1 j.2 3 1

/-- `min_{J'} L^{(K,n)}(R^S, φ)` over short rectangles `u 2^{-K} R_{1,3} + c` -/
def minShort (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (K n : ℕ) (J' : Finset (Circle × ℂ))
    (hJ' : J'.Nonempty) (ω : Ω) : ℝ :=
  J'.inf' hJ' fun j => T20B.mrectLen ξ (fun x => phiMN W P K n x ω) K j.1 j.2 1 3

/-- each block of `t` serves at most `(2m₀+1)²` indices at distance `≤ m₀` -/
lemma sum_fiber_le {s t : Finset (ℤ × ℤ)} (g : ℤ × ℤ → ℤ × ℤ) (hg : ∀ b ∈ s, g b ∈ t)
    (m₀ : ℕ) (hcl : ∀ b ∈ s, |((b.1 - (g b).1 : ℤ) : ℝ)| ≤ m₀ ∧ |((b.2 - (g b).2 : ℤ) : ℝ)| ≤ m₀)
    (f : ℤ × ℤ → ℝ)
    (hf : ∀ j, 0 ≤ f j) :
    ∑ b ∈ s, f (g b) ≤ ((2 * m₀ + 1 : ℕ) : ℝ) ^ 2 * ∑ j ∈ t, f j := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to' hg, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hf j)
  have hsub : s.filter (fun i => g i = j) ⊆
      Finset.Icc (j.1 - m₀) (j.1 + m₀) ×ˢ Finset.Icc (j.2 - m₀) (j.2 + m₀) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨h1, h2⟩ := hcl i hi.1
    rw [hi.2] at h1 h2
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    rw [abs_le] at h1 h2
    have a1 : -(m₀ : ℤ) ≤ i.1 - j.1 := by exact_mod_cast h1.1
    have a2 : i.1 - j.1 ≤ (m₀ : ℤ) := by exact_mod_cast h1.2
    have a3 : -(m₀ : ℤ) ≤ i.2 - j.2 := by exact_mod_cast h2.1
    have a4 : i.2 - j.2 ≤ (m₀ : ℤ) := by exact_mod_cast h2.2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_product, Int.card_Icc, Int.card_Icc] at hc
  have e : ∀ a : ℤ, (a + m₀ + 1 - (a - m₀)).toNat = 2 * m₀ + 1 := fun a => by omega
  rw [e, e] at hc
  have : ((s.filter (fun i => g i = j)).card : ℝ) ≤ ((2 * m₀ + 1) * (2 * m₀ + 1) : ℕ) := by
    exact_mod_cast hc
  rw [sq]; push_cast at this ⊢; linarith

lemma card_nearIdx_le (K : ℕ) : ((T20B.nearIdx K).card : ℝ) ≤ 16 * 4 ^ K := by
  unfold T20B.nearIdx
  rw [Finset.card_product, Int.card_Icc]
  have h2 : (1 : ℤ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  have e : (2 ^ (K + 1) + 1 - -(2 : ℤ) ^ K).toNat ≤ 4 * 2 ^ K := by
    rw [pow_succ]
    have : (2 : ℤ) ^ K * 2 + 1 - -2 ^ K ≤ 4 * 2 ^ K := by linarith
    have h0 : (0 : ℤ) ≤ 2 ^ K * 2 + 1 - -2 ^ K := by linarith
    have := Int.toNat_le_toNat this
    have e2 : ((4 : ℤ) * 2 ^ K).toNat = 4 * 2 ^ K := by
      rw [show (4 : ℤ) * 2 ^ K = ((4 * 2 ^ K : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
    omega
  have e' : (((2 ^ (K + 1) + 1 - -(2 : ℤ) ^ K).toNat * (2 ^ (K + 1) + 1 - -(2 : ℤ) ^ K).toNat : ℕ) : ℝ)
      ≤ ((4 * 2 ^ K) * (4 * 2 ^ K) : ℕ) := by exact_mod_cast Nat.mul_le_mul e e
  calc _ ≤ (((4 * 2 ^ K) * (4 * 2 ^ K) : ℕ) : ℝ) := e'
    _ = 16 * 4 ^ K := by push_cast; rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring

end T20C

end DDDF
end LQGMetric
