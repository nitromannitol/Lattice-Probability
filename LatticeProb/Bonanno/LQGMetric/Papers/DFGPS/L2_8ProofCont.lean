/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8ProofCont at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1Ratio
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyUnif

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.8: continuity of `D_h^ε(·,·;S)` and the bi-Lipschitz bound for `h + f`

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`):
* T:872–875: the internal metrics `𝔞_ε⁻¹ D_h^ε(·,·;S)` are random continuous functions on
  `S × S` (implicit in "tight w.r.t. the uniform topology on `S × S`"). For continuous `h*_ε`
  this is the elementary bound `D(z,w;S) ≤ (max_{S'} e^{ξ h*_ε}) |z − w|` (segment path) plus the
  triangle inequality (own elementary argument, DEVIATIONS).
* T:897–898: "the metrics `D_{h+f}^ε` and `D_h^ε` are bi-Lipschitz equivalent, with Lipschitz
  constants `e^{±ξ‖f‖_∞}`" (`lfppDOn_toReal_le_of_abs_sub_le`, from
  `DFGPS.lfppDOn_le_of_abs_sub_le`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP

theorem convex_closedSq (a : ℂ) (s : ℝ) : Convex ℝ (closedSq a s) := by
  intro x hx y hy u v hu hv huv
  obtain ⟨h1, h2, h3, h4⟩ := hx
  obtain ⟨k1, k2, k3, k4⟩ := hy
  simp only [closedSq, mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero]
  have e : ∀ t : ℝ, t = u * t + v * t := fun t => by rw [← add_mul, huv, one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e a.re]; nlinarith [mul_le_mul_of_nonneg_left h1 hu, mul_le_mul_of_nonneg_left k1 hv]
  · rw [e (a.re + s)]; nlinarith [mul_le_mul_of_nonneg_left h2 hu, mul_le_mul_of_nonneg_left k2 hv]
  · rw [e a.im]; nlinarith [mul_le_mul_of_nonneg_left h3 hu, mul_le_mul_of_nonneg_left k3 hv]
  · rw [e (a.im + s)]; nlinarith [mul_le_mul_of_nonneg_left h4 hu, mul_le_mul_of_nonneg_left k4 hv]

theorem closedSq_subset_closedBall (a : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    closedSq a s ⊆ closedBall (0 : ℂ) (‖a‖ + 2 * s) := by
  intro x ⟨h1, h2, h3, h4⟩
  rw [mem_closedBall, dist_zero_right]
  have hre : |(x - a).re| ≤ s := by rw [Complex.sub_re, abs_le]; constructor <;> linarith
  have him : |(x - a).im| ≤ s := by rw [Complex.sub_im, abs_le]; constructor <;> linarith
  calc ‖x‖ = ‖a + (x - a)‖ := by ring_nf
    _ ≤ ‖a‖ + ‖x - a‖ := norm_add_le _ _
    _ ≤ ‖a‖ + (|(x - a).re| + |(x - a).im|) := by
        gcongr; exact Complex.norm_le_abs_re_add_abs_im _
    _ ≤ ‖a‖ + 2 * s := by linarith

theorem isCompact_closedSq (a : ℂ) {s : ℝ} (hs : 0 ≤ s) : IsCompact (closedSq a s) := by
  refine (isCompact_closedBall (0 : ℂ) (‖a‖ + 2 * s)).of_isClosed_subset ?_
    (closedSq_subset_closedBall a hs)
  have e : closedSq a s = (Complex.re ⁻¹' Icc a.re (a.re + s)) ∩ (Complex.im ⁻¹' Icc a.im (a.im + s)) := by
    ext x; simp only [closedSq, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Icc]; tauto
  rw [e]
  exact (isClosed_Icc.preimage Complex.continuous_re).inter
    (isClosed_Icc.preimage Complex.continuous_im)

/-- **Linear bound** `D(x,y;S) ≤ B |x − y|` for continuous `φ` and bounded convex `S`. -/
theorem exists_lfppDOn_le_mul_norm {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) {S : Set ℂ}
    (hS : Convex ℝ S) {R : ℝ} (hSR : S ⊆ closedBall (0 : ℂ) R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ S, ∀ y ∈ S, lfppDOn ξ φ S x y ≤ ENNReal.ofReal (B * ‖y - x‖) := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) (3 * R)).exists_bound_of_continuousOn
    (f := fun x => Real.exp (ξ * φ x)) (by fun_prop)
  refine ⟨max B 0, le_max_right _ _, fun x hx y hy => ?_⟩
  refine (lfppDOn_le_segCost hS hx hy).trans (segCost_le fun u hu => ?_)
  have hx' := mem_closedBall_zero_iff.1 (hSR hx)
  have hy' := mem_closedBall_zero_iff.1 (hSR hy)
  have hu' : u ∈ closedBall (0 : ℂ) (3 * R) := by
    rw [mem_closedBall_zero_iff]
    rw [mem_closedBall, dist_eq_norm] at hu
    calc ‖u‖ = ‖x + (u - x)‖ := by ring_nf
      _ ≤ ‖x‖ + ‖u - x‖ := norm_add_le _ _
      _ ≤ R + ‖y - x‖ := by linarith
      _ ≤ R + (‖y‖ + ‖x‖) := by linarith [norm_sub_le y x]
      _ ≤ 3 * R := by linarith
  have := hB u hu'
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at this
  exact this.trans (le_max_left _ _)

/-- **Continuity of `(x, y) ↦ c · D(x, y; S)`** on `S × S` for continuous `φ` and bounded convex
`S`, together with finiteness. -/
theorem continuous_lfppDOn_toReal {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) {S : Set ℂ}
    (hS : Convex ℝ S) {R : ℝ} (hSR : S ⊆ closedBall (0 : ℂ) R) (c : ℝ) :
    Continuous fun p : S × S => c * (lfppDOn ξ φ S p.1 p.2).toReal := by
  obtain ⟨B, hB0, hB⟩ := exists_lfppDOn_le_mul_norm (ξ := ξ) hφ hS hSR
  set D : S → S → ℝ := fun x y => (lfppDOn ξ φ S x y).toReal
  have hfin : ∀ x y : S, lfppDOn ξ φ S x y ≠ ⊤ := fun x y =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hB x x.2 y y.2)
  have hle : ∀ x y : S, D x y ≤ B * ‖(y : ℂ) - x‖ := fun x y =>
    ENNReal.toReal_le_of_le_ofReal (by positivity) (hB x x.2 y y.2)
  have htri : ∀ x y z : S, D x z ≤ D x y + D y z := fun x y z => by
    simp only [D]
    rw [← ENNReal.toReal_add (hfin x y) (hfin y z)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin x y, hfin y z⟩)
      (lfppDOn_triangle _ _ _)
  have hlip : ∀ p q : S × S, D p.1 p.2 - D q.1 q.2 ≤ 2 * B * dist p q := by
    intro p q
    have h1 := htri p.1 q.1 p.2
    have h2 := htri q.1 q.2 p.2
    have e1 : D p.1 q.1 ≤ B * dist p q := (hle _ _).trans (mul_le_mul_of_nonneg_left (by
      rw [← dist_eq_norm, dist_comm, ← Subtype.dist_eq, Prod.dist_eq]; exact le_max_left _ _) hB0)
    have e2 : D q.2 p.2 ≤ B * dist p q := (hle _ _).trans (mul_le_mul_of_nonneg_left (by
      rw [← dist_eq_norm, ← Subtype.dist_eq, Prod.dist_eq]; exact le_max_right _ _) hB0)
    linarith
  have hL : LipschitzWith (Real.toNNReal (2 * B)) fun p : S × S => D p.1 p.2 := by
    refine LipschitzWith.of_dist_le_mul fun p q => ?_
    rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, abs_le]
    constructor
    · have := hlip q p; rw [dist_comm] at this; linarith
    · exact hlip p q
  exact continuous_const.mul hL.continuous

/-- **The first conjunct of DFGPS Lemma 2.8**: for each `ε ∈ (0,1)`, a.s. the rescaled internal
LFPP metric is continuous on `S × S`. -/
theorem lem2_8_continuous {γ : ℝ} {a : ℂ} {s : ℝ} (hs : 0 < s) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsGFFPlusBddCont h P) :
    ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, Continuous fun p : closedSq a s × closedSq a s =>
      (aEpsDF (xiGamma γ) ε)⁻¹ *
        (LFPP.lfppDOn (xiGamma γ) (heatMollify ε (h ω)) (closedSq a s) p.1 p.2).toReal := by
  intro ε hε
  filter_upwards [hh.ae_tendstoLocallyUniformly_heatMollify ε hε.1.ne'] with ω hω
  exact continuous_lfppDOn_toReal hω.2 (convex_closedSq a s) (closedSq_subset_closedBall a hs.le) _

/-- **Bi-Lipschitz bound** (DFGPS T:897–898): if `|φ' − φ| ≤ δ` on `S` and `D_φ(·,·;S)` is finite,
then `D_{φ'}(x,y;S) ≤ e^{|ξ| δ} D_φ(x,y;S)` (as real numbers). -/
theorem lfppDOn_toReal_le_of_abs_sub_le {ξ : ℝ} {φ φ' : ℂ → ℝ} {S : Set ℂ} {δ : ℝ}
    (hδ : ∀ x ∈ S, |φ' x - φ x| ≤ δ) {z w : ℂ} (hfin : lfppDOn ξ φ S z w ≠ ⊤) :
    (lfppDOn ξ φ' S z w).toReal ≤ Real.exp (|ξ| * δ) * (lfppDOn ξ φ S z w).toReal := by
  have h := lfppDOn_le_of_abs_sub_le (ξ := ξ) hδ z w
  have hfin' : ENNReal.ofReal (Real.exp (|ξ| * δ)) * lfppDOn ξ φ S z w ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  calc (lfppDOn ξ φ' S z w).toReal
      ≤ (ENNReal.ofReal (Real.exp (|ξ| * δ)) * lfppDOn ξ φ S z w).toReal :=
        ENNReal.toReal_mono hfin' h
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]

end LQGMetric.DFGPS
