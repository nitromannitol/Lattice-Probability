/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.ChainInf at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.Chain

/-!
# The LFPP infimum as a countable infimum over chains; countable dense vertex sets

Task P2-LFPP, item 2. For continuous `φ`, convex `S` and a dense `C ⊆ S`,
`D^φ(z, w; S) = inf_{N, q : Fin N → C} Σ_i segCost(v_i, v_{i+1})` (`lfppDOn_eq_iInf_chain`),
and the side-to-side infimum reduces to countable dense subsets of the sides
(`iInf_sides_eq`). Own elementary arguments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace LFPP

variable {ξ : ℝ} {φ : ℂ → ℝ} {S : Set ℂ}

/-- the vertices `z, q₀, …, q_{N-1}, w` of a chain -/
def chainV (z w : ℂ) {C : Set ℂ} (N : ℕ) (q : Fin N → C) (i : ℕ) : ℂ :=
  if h0 : i = 0 then z else if h : i ≤ N then (q ⟨i - 1, by omega⟩ : ℂ) else w

/-- the cost of a chain -/
def chainCost (ξ : ℝ) (φ : ℂ → ℝ) (z w : ℂ) {C : Set ℂ} (N : ℕ) (q : Fin N → C) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (N + 1), segCost ξ φ (chainV z w N q i) (chainV z w N q (i + 1))

theorem chainV_zero (z w : ℂ) {C : Set ℂ} (N : ℕ) (q : Fin N → C) : chainV z w N q 0 = z := by
  simp [chainV]

theorem chainV_last (z w : ℂ) {C : Set ℂ} (N : ℕ) (q : Fin N → C) :
    chainV z w N q (N + 1) = w := by
  simp [chainV]

/-- **The LFPP distance as an infimum over chains.** -/
theorem lfppDOn_eq_iInf_chain (hφ : Continuous φ) (hS : Convex ℝ S) {C : Set ℂ} (hCS : C ⊆ S)
    (hC : ∀ x ∈ S, ∀ ρ > 0, ∃ q ∈ C, ‖q - x‖ < ρ) {z w : ℂ} (hz : z ∈ S) (hw : w ∈ S) :
    lfppDOn ξ φ S z w = ⨅ (N : ℕ) (q : Fin N → C), chainCost ξ φ z w N q := by
  refine le_antisymm (le_iInf fun N => le_iInf fun q => ?_) (le_iInf fun P => ?_)
  · have hv : ∀ i, chainV z w N q i ∈ S := by
      intro i
      simp only [chainV]
      split_ifs
      · exact hz
      · exact hCS (q _).2
      · exact hw
    have := lfppDOn_le_sum_segCost (ξ := ξ) (φ := φ) hS (chainV z w N q) hv (N + 1)
    rwa [chainV_zero, chainV_last] at this
  · refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    obtain ⟨N, v, hv0, hvN, hvC, hsum⟩ :=
      exists_chain_le (ξ := ξ) hφ hC P.2.1 P.2.2 (δ := δ) (by exact_mod_cast hδ)
    let q : Fin N → C := fun i => ⟨v (i + 1), hvC _ (by omega) (by omega)⟩
    have hvq : ∀ i, i ≤ N + 1 → chainV z w N q i = v i := by
      intro i hi
      simp only [chainV]
      split_ifs with h1 h2
      · rw [h1, hv0]
      · simp only [q]; congr 1; omega
      · rw [show i = N + 1 by omega, hvN]
    refine (iInf_le_of_le N (iInf_le_of_le q ?_)).trans (hsum.trans_eq (by simp))
    refine (Finset.sum_congr rfl fun i hi => ?_).le
    have hi' := Finset.mem_range.1 hi
    rw [hvq i (by omega), hvq (i + 1) (by omega)]

/-! ### Countable dense sets -/

/-- Gaussian rationals -/
def gaussRat : Set ℂ := range fun q : ℚ × ℚ => (q.1 : ℂ) + (q.2 : ℂ) * Complex.I

theorem gaussRat_countable : gaussRat.Countable := countable_range _

theorem mk_mem_gaussRat (a b : ℚ) : ((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I ∈ gaussRat :=
  ⟨(a, b), by simp⟩

theorem exists_rat_near_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) {r : ℝ} (hr : 0 < r) :
    ∃ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) 1 ∧ |(q : ℝ) - x| < r := by
  obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show max 0 (x - r) < min 1 (x + r) by
    simp only [max_lt_iff, lt_min_iff]; refine ⟨⟨one_pos, ?_⟩, ?_, ?_⟩ <;> linarith [hx.1, hx.2])
  simp only [max_lt_iff, lt_min_iff] at h1 h2
  exact ⟨q, ⟨h1.1.le, h2.1.le⟩, abs_lt.2 ⟨by linarith, by linarith⟩⟩

theorem norm_mk_sub_le (a b : ℝ) (x : ℂ) :
    ‖((a : ℂ) + (b : ℂ) * Complex.I) - x‖ ≤ |a - x.re| + |b - x.im| := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans_eq ?_
  simp

theorem gaussRat_dense (x : ℂ) {ρ : ℝ} (hρ : 0 < ρ) : ∃ q ∈ gaussRat, ‖q - x‖ < ρ := by
  obtain ⟨a, ha⟩ := exists_rat_btwn (show x.re - ρ / 2 < x.re + ρ / 2 by linarith)
  obtain ⟨b, hb⟩ := exists_rat_btwn (show x.im - ρ / 2 < x.im + ρ / 2 by linarith)
  refine ⟨_, mk_mem_gaussRat a b, (norm_mk_sub_le _ _ x).trans_lt ?_⟩
  have := abs_lt.2 (⟨by linarith [ha.1], by linarith [ha.2]⟩ : -(ρ / 2) < (a : ℝ) - x.re ∧ _)
  have := abs_lt.2 (⟨by linarith [hb.1], by linarith [hb.2]⟩ : -(ρ / 2) < (b : ℝ) - x.im ∧ _)
  linarith

theorem gaussRat_square_dense {x : ℂ} (hx : x ∈ Blueprint.closedUnitSquare) {ρ : ℝ}
    (hρ : 0 < ρ) : ∃ q ∈ gaussRat ∩ Blueprint.closedUnitSquare, ‖q - x‖ < ρ := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨a, ha, ha'⟩ := exists_rat_near_Icc ⟨hx1, hx2⟩ (half_pos hρ)
  obtain ⟨b, hb, hb'⟩ := exists_rat_near_Icc ⟨hx3, hx4⟩ (half_pos hρ)
  refine ⟨_, ⟨mk_mem_gaussRat a b, ?_⟩, (norm_mk_sub_le _ _ x).trans_lt (by linarith)⟩
  simp only [Blueprint.closedUnitSquare, mem_ofPred_eq, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
    add_zero, Complex.add_im, Complex.mul_im, zero_add]
  exact ⟨ha.1, ha.2, hb.1, hb.2⟩

/-- rational points of a vertical side `{c} × [0,1]` -/
def sideRat (c : ℝ) : Set ℂ :=
  range fun q : {q : ℚ // (q : ℝ) ∈ Icc (0 : ℝ) 1} => (c : ℂ) + ((q.1 : ℝ) : ℂ) * Complex.I

theorem sideRat_countable (c : ℝ) : (sideRat c).Countable := countable_range _

theorem sideRat_subset (c : ℝ) : sideRat c ⊆ {z : ℂ | z.re = c ∧ 0 ≤ z.im ∧ z.im ≤ 1} := by
  rintro _ ⟨q, rfl⟩
  simpa using q.2

theorem sideRat_dense {c : ℝ} {x : ℂ} (hx : x ∈ {z : ℂ | z.re = c ∧ 0 ≤ z.im ∧ z.im ≤ 1})
    {ρ : ℝ} (hρ : 0 < ρ) : ∃ q ∈ sideRat c, ‖q - x‖ < ρ := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨b, hb, hb'⟩ := exists_rat_near_Icc ⟨hx2, hx3⟩ hρ
  refine ⟨_, ⟨⟨b, hb⟩, rfl⟩, (norm_mk_sub_le _ _ x).trans_lt ?_⟩
  rw [hx1, sub_self, abs_zero, zero_add]
  exact hb'

end LFPP
end LQGMetric
