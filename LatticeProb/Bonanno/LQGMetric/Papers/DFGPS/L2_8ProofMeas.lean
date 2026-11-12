/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8ProofMeas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8ProofCont
import LatticeProb.Bonanno.LQGMetric.LFPP.Measurable

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.8: measurability of `ω ↦ 𝔞_ε⁻¹ D_h^ε(·,·;S)` as a `C(S × S, ℝ)`-valued map

The laws in DFGPS Lemma 2.8 (T:872–875) are laws of random elements of `C(S × S, ℝ)`. For
continuous `h*_ε` the internal distance on the closed square `S` is an infimum over chains through
the countable dense set `ℚ[i] ∩ S` (`LFPP.lfppDOn_eq_iInf_chain`), hence measurable in the field;
the `C(S × S, ℝ)`-valued map is then a.e.-measurable by `ContinuousMap.measurable_iff_eval`
(as in `DG.aemeasurable_toContMap`). Own elementary argument (DEVIATIONS).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP

theorem exists_rat_near_Icc' {c d x : ℝ} (hcd : c < d) (hx : x ∈ Icc c d) {r : ℝ} (hr : 0 < r) :
    ∃ q : ℚ, (q : ℝ) ∈ Icc c d ∧ |(q : ℝ) - x| < r := by
  obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show max c (x - r) < min d (x + r) by
    simp only [max_lt_iff, lt_min_iff]; refine ⟨⟨hcd, ?_⟩, ?_, ?_⟩ <;> linarith [hx.1, hx.2])
  simp only [max_lt_iff, lt_min_iff] at h1 h2
  exact ⟨q, ⟨h1.1.le, h2.1.le⟩, abs_lt.2 ⟨by linarith, by linarith⟩⟩

theorem gaussRat_closedSq_dense {a : ℂ} {s : ℝ} (hs : 0 < s) {x : ℂ} (hx : x ∈ closedSq a s)
    {ρ : ℝ} (hρ : 0 < ρ) : ∃ q ∈ gaussRat ∩ closedSq a s, ‖q - x‖ < ρ := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨u, hu, hu'⟩ := exists_rat_near_Icc' (by linarith : a.re < a.re + s) ⟨hx1, hx2⟩
    (half_pos hρ)
  obtain ⟨v, hv, hv'⟩ := exists_rat_near_Icc' (by linarith : a.im < a.im + s) ⟨hx3, hx4⟩
    (half_pos hρ)
  refine ⟨_, ⟨mk_mem_gaussRat u v, ?_⟩, (norm_mk_sub_le _ _ x).trans_lt (by linarith)⟩
  simp only [closedSq, mem_ofPred_eq, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
    add_zero, Complex.add_im, Complex.mul_im, zero_add]
  exact ⟨hu.1, hu.2, hv.1, hv.2⟩

theorem toCMap_apply_of_continuous {X : Type*} [TopologicalSpace X] {g : X → ℝ}
    (hg : Continuous g) (x : X) : toCMap g x = g x := by
  simp [toCMap, hg]

/-- `lfppSqC` evaluates to the rescaled distance when `h*_ε` is continuous. -/
theorem lfppSqC_apply_of_continuous {ξ ε : ℝ} {g : DistC} (hc : Continuous (heatMollify ε g))
    {a : ℂ} {s : ℝ} (hs : 0 < s) (p : closedSq a s × closedSq a s) :
    lfppSqC ξ ε g (closedSq a s) p =
      (aEpsDF ξ ε)⁻¹ * (lfppDOn ξ (heatMollify ε g) (closedSq a s) p.1 p.2).toReal :=
  toCMap_apply_of_continuous (continuous_lfppDOn_toReal hc (convex_closedSq a s)
    (closedSq_subset_closedBall a hs.le) _) p

/-- **A.e.-measurability of the random internal metric** on a closed square. -/
theorem aemeasurable_lfppSqC {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hm : Measurable h) {ξ ε : ℝ} (hc : ∀ᵐ ω ∂P, Continuous (heatMollify ε (h ω))) {a : ℂ}
    {s : ℝ} (hs : 0 < s) :
    AEMeasurable (fun ω => lfppSqC ξ ε (h ω) (closedSq a s)) P := by
  set S := closedSq a s
  haveI : CompactSpace S := isCompact_iff_compactSpace.1 (isCompact_closedSq a hs.le)
  have hC : (gaussRat ∩ S).Countable := gaussRat_countable.mono inter_subset_left
  have key : @Measurable (NullMeasurableSpace Ω P) C(S × S, ℝ) _ _
      (fun ω => lfppSqC ξ ε (h ω) S) := by
    refine (ContinuousMap.measurable_iff_eval (Z := NullMeasurableSpace Ω P)).2 fun p => ?_
    have h1 : AEMeasurable (fun ω => lfppSqC ξ ε (h ω) S p) P := by
      refine ⟨fun ω => (aEpsDF ξ ε)⁻¹ * (⨅ (N : ℕ) (q : Fin N → (gaussRat ∩ S : Set ℂ)),
        chainCost ξ (heatMollify ε (h ω)) p.1 p.2 N q).toReal,
        (ENNReal.measurable_toReal.comp ((measurable_iInf_chainCost ξ ε hC p.1 p.2).comp
          hm)).const_mul _, ?_⟩
      filter_upwards [hc] with ω hω
      rw [lfppSqC_apply_of_continuous hω hs p, lfppDOn_eq_iInf_chain hω (convex_closedSq a s)
        inter_subset_right (fun x hx ρ hρ => gaussRat_closedSq_dense hs hx hρ) p.1.2 p.2.2]
    exact fun t ht => h1.nullMeasurable ht
  exact (show NullMeasurable (fun ω => lfppSqC ξ ε (h ω) S) P from fun t ht => key ht).aemeasurable

end LQGMetric.DFGPS
