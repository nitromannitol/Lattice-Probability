/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8FinAsm at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinSetup

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.8, GFF case on the unit square (T:876–891)

`lem2_8Gff_unitSq`: for a whole-plane GFF `g` the laws of `𝔞_ε⁻¹ D_g^ε(·,·;[0,1]²)`,
`ε ∈ (0,1)`, are tight and every subsequential limit (`ε_n → 0`) is a.s. positive off the
diagonal (the case `S = [0,1]²` of `Lem2_8Gff`, DFGPS T:891 "the statement of the lemma holds in
the special case when `h = g` and `S = [0,1]²`"; the additive constant of `g` is arbitrary).

* tightness: `isTightMeasureSet_of_le_mul_ev'` with `A_ε = λ_ε⁻¹ D_{Y_{ε²}}` (tight, `zb_step`),
  domination `B_ε ≤ e^{|ξ|M} C A_ε` on the event `sup |g*_ε − Y_{ε²}| ≤ M` for `ε` below a
  threshold, and `lem2_8_tight_far'` above it;
* positivity: `ae_posOffDiag_of_dominated` with the reverse domination `A_ε ≤ e^{|ξ|M} C B_ε`.

`closedUnitSquare` and `closedSq 0 1` are equal sets (`closedUnitSquare_eq`); statements uniform
in the square are transported by rewriting.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal NNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP HeatSq WhiteNoise DDDF

lemma lfppSqC_apply_unitSq {ξ ε : ℝ} {g : DistC} (hc : Continuous (heatMollify ε g))
    (p : closedUnitSquare × closedUnitSquare) :
    lfppSqC ξ ε g closedUnitSquare p =
      (aEpsDF ξ ε)⁻¹ * (lfppDOn ξ (heatMollify ε g) closedUnitSquare p.1 p.2).toReal := by
  revert p
  rw [closedUnitSquare_eq]
  exact lfppSqC_apply_of_continuous hc one_pos

lemma aemeasurable_lfppSqC_unitSq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hm : Measurable h) {ξ ε : ℝ}
    (hc : ∀ᵐ ω ∂P, Continuous (heatMollify ε (h ω))) :
    AEMeasurable (fun ω => lfppSqC ξ ε (h ω) closedUnitSquare) P := by
  have key := aemeasurable_lfppSqC (a := 0) (s := 1) (ξ := ξ) hm hc one_pos
  rw [← closedUnitSquare_eq] at key
  exact key

lemma lfppSqC_unitSq_mem_pmetSet {ξ ε : ℝ} {g : DistC} (hc : Continuous (heatMollify ε g)) :
    lfppSqC ξ ε g closedUnitSquare ∈ pmetSet closedUnitSquare := by
  obtain ⟨B, -, hB⟩ := exists_lfppDOn_le_mul_norm (ξ := ξ) hc convex_closedUnitSquare
    closedUnitSquare_subset_closedBall
  have hfin : ∀ x y : closedUnitSquare,
      lfppDOn ξ (heatMollify ε g) closedUnitSquare x y ≠ ⊤ := fun x y =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hB x x.2 y y.2)
  refine ⟨fun x => ?_, fun x y z => ?_⟩
  · rw [lfppSqC_apply_unitSq hc, lfppDOn_self convex_closedUnitSquare x.2, ENNReal.toReal_zero,
      mul_zero]
  · rw [lfppSqC_apply_unitSq hc (x, z), lfppSqC_apply_unitSq hc (x, y),
      lfppSqC_apply_unitSq hc (y, z), ← mul_add, ← ENNReal.toReal_add (hfin x y) (hfin y z)]
    exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨hfin x y, hfin y z⟩) (lfppDOn_triangle _ _ _))
      (inv_nonneg.2 (aEpsDF_nonneg_sq ξ ε))

/-- the two dominations on the good event -/
lemma unitSq_dom {ξ ε M C lam : ℝ} {g : DistC} {f : ℂ → ℝ} (hc : Continuous (heatMollify ε g))
    (hf : Continuous f) (hC : 0 < C) (hlam : 0 < lam) (h1 : C⁻¹ * lam ≤ aEpsDF ξ ε)
    (h2 : aEpsDF ξ ε ≤ C * lam)
    (hd : ∀ x ∈ closedUnitSquare, |heatMollify ε g x - f x| ≤ M)
    (p : closedUnitSquare × closedUnitSquare) :
    lfppSqC ξ ε g closedUnitSquare p ≤ Real.exp (|ξ| * M) * C * sqMetricC ξ lam f p ∧
      sqMetricC ξ lam f p ≤ Real.exp (|ξ| * M) * C * lfppSqC ξ ε g closedUnitSquare p := by
  set a := aEpsDF ξ ε
  have ha : 0 < a := lt_of_lt_of_le (by positivity) h1
  set K := Real.exp (|ξ| * M)
  set Dh := (lfppDOn ξ (heatMollify ε g) closedUnitSquare p.1 p.2).toReal
  set Df := (lfppDOn ξ f closedUnitSquare p.1 p.2).toReal
  have hDh : 0 ≤ Dh := ENNReal.toReal_nonneg
  have hDf : 0 ≤ Df := ENNReal.toReal_nonneg
  have e1 : Dh ≤ K * Df := lfppDOn_toReal_le_of_abs_sub_le hd (lfppDOn_unitSq_ne_top hf p)
  have e2 : Df ≤ K * Dh := lfppDOn_toReal_le_of_abs_sub_le
    (fun x hx => by rw [abs_sub_comm]; exact hd x hx) (lfppDOn_unitSq_ne_top hc p)
  rw [lfppSqC_apply_unitSq hc, sqMetricC_apply hf]
  have hinv1 : a⁻¹ ≤ C * lam⁻¹ := by
    have := inv_anti₀ (by positivity : 0 < C⁻¹ * lam) h1
    rwa [mul_inv, inv_inv] at this
  have hinv2 : lam⁻¹ ≤ C * a⁻¹ := by
    have := inv_anti₀ ha h2
    rw [mul_inv] at this
    calc lam⁻¹ = C * (C⁻¹ * lam⁻¹) := by field_simp
      _ ≤ C * a⁻¹ := mul_le_mul_of_nonneg_left this hC.le
  have hK : 0 < K := Real.exp_pos _
  constructor
  · calc a⁻¹ * Dh ≤ a⁻¹ * (K * Df) := mul_le_mul_of_nonneg_left e1 (by positivity)
      _ ≤ (C * lam⁻¹) * (K * Df) := mul_le_mul_of_nonneg_right hinv1 (by positivity)
      _ = K * C * (lam⁻¹ * Df) := by ring
  · calc lam⁻¹ * Df ≤ lam⁻¹ * (K * Dh) := mul_le_mul_of_nonneg_left e2 (by positivity)
      _ ≤ (C * a⁻¹) * (K * Dh) := mul_le_mul_of_nonneg_right hinv2 (by positivity)
      _ = K * C * (a⁻¹ * Dh) := by ring

end LQGMetric.DFGPS
