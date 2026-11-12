/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6TailsAB at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6TailsDec

/-!
# DDDF (6.102)/(6.103) for `[0,A] × [0,B]`: decoupling (task P2-DDDF6e)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1639–1647 ("using the same argument as in the two
previous paragraphs", i.e. l. 1608–1613): the unit-square decoupling of `S6TailsDec`
(`S6.low_sup_tail_quant`, `S6.law_hi`, `S6.len_cmp`, `S6.tail_decomp`) for a general rectangle
`rectAB A B`; the sup of the coarse field is taken over the box `[0,m]²` (`A, B ≤ m`), with the
Fernique bound of `DGo.box_sup_tail` (increment constant `8m` instead of `8`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace LQGMetric
namespace DDDF
namespace S6AB

open WhiteNoise SupTail S6

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

lemma rectAB_toSet_sub {A B m : ℝ} (hA : A ≤ m) (hB : B ≤ m) :
    (rectAB A B).toSet ⊆ ferniqueBox 0 m := by
  intro z hz
  simp only [MarkedRect.toSet, rectAB, Complex.mem_reProdIm, mem_Icc, zero_add] at hz
  simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc, Complex.zero_re, Complex.zero_im,
    zero_add]
  exact ⟨⟨hz.1.1, hz.1.2.trans hA⟩, hz.2.1, hz.2.2.trans hB⟩

/-- Gaussian sup tail of `φ_{a,1}` on the box `[0,m]²`, uniformly in `a ∈ [1/2,1]` -/
theorem low_sup_tail_box (hW : IsWhiteNoise P W) {m : ℝ} (hm : 0 < m) {u : ℝ} (hu0 : 0 ≤ u)
    {a : ℝ} (ha12 : 1 / 2 ≤ a) (ha1 : a ≤ 1) :
    P {ω | ¬ ∀ x ∈ ferniqueBox 0 m, |phiVer W P a 1 x ω| ≤
        ferniqueCF * Real.sqrt (8 * m * m) + u}
      ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * 1 ^ 2))) := by
  have hP := hW.isProbabilityMeasure
  set M : ℝ := ferniqueCF * Real.sqrt (8 * m * m) + u
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha12
  have hY := isPhiVersion_phiVer hW ha0 ha1
  set Y := phiVer W P a 1
  have hint0 : ∀ v, ∫ ω, Y v ω ∂P = 0 := fun v => by
    rw [integral_congr_ae (hY.ae_eq v)]; exact integral_phi hW a 1 v
  have hX : IsGaussianProcess Y P :=
    (isGaussianProcess_phi_comp hW a 1 (fun v : ℂ => v)).congr fun v => (hY.ae_eq v).symm
  have hinc : ∀ u ∈ ferniqueBox 0 m, ∀ v ∈ ferniqueBox 0 m,
      ∫ ω, (Y v ω - Y u ω) ^ 2 ∂P ≤ 8 * m * ‖u - v‖ := by
    intro u hu v hv
    have hm' : AEMeasurable (fun ω => phi W a 1 v ω - phi W a 1 u ω) P :=
      ((measurable_phi hW a 1 v).sub (measurable_phi hW a 1 u)).aemeasurable
    have h0 : ∫ ω, (phi W a 1 v ω - phi W a 1 u ω) ∂P = 0 := by
      rw [integral_sub ((memLp_phi hW a 1 v).integrable one_le_two)
        ((memLp_phi hW a 1 u).integrable one_le_two), integral_phi hW, integral_phi hW, sub_zero]
    have hae2 : (fun ω => (Y v ω - Y u ω) ^ 2) =ᵐ[P]
        fun ω => (phi W a 1 v ω - phi W a 1 u ω) ^ 2 := by
      filter_upwards [hY.ae_eq u, hY.ae_eq v] with ω h1 h2; rw [h1, h2]
    rw [integral_congr_ae hae2, ← variance_of_integral_eq_zero hm' h0]
    have h1 := DZZ.dzz_variance_hat_sub_le hW ha0 ha1 v u
    have hr := DZZ.norm_sub_le_of_mem_ferniqueBox hu hv
    have hr0 := norm_nonneg (u - v)
    rw [norm_sub_rev] at h1
    have ha2 : (1 / 4 : ℝ) ≤ a ^ 2 := by nlinarith
    calc _ ≤ ‖u - v‖ ^ 2 / a ^ 2 := h1
      _ ≤ ‖u - v‖ ^ 2 / (1 / 4) := div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) ha2
      _ ≤ 8 * m * ‖u - v‖ := by nlinarith
  have hvar : ∀ v ∈ ferniqueBox 0 m, Var[Y v; P] ≤ 1 ^ 2 := by
    intro v _
    rw [variance_congr (hY.ae_eq v), variance_phi hW ha0 ha1, one_pow]
    have h2 : 1 / a ≤ 2 := by rw [div_le_iff₀ ha0]; linarith
    have := Real.log_le_sub_one_of_pos (show 0 < 1 / a by positivity)
    linarith
  have hYc : ∀ ω, ContinuousOn (fun v => Y v ω) (ferniqueBox 0 m) :=
    fun ω => (hY.cont ω).continuousOn
  have hXn : IsGaussianProcess (fun v ω => -Y v ω) P := by
    have := hX.smul (fun _ => (-1 : ℝ))
    simpa [smul_eq_mul] using this
  have h8 : (0 : ℝ) < 8 * m := by positivity
  have h1 := DGo.box_sup_tail hX hint0 (y := 0) hm h8 hYc hinc hvar hu0
  have h2 := DGo.box_sup_tail hXn (fun v => by rw [integral_neg, hint0, neg_zero]) (y := 0) hm
    h8 (fun ω => (hYc ω).neg)
    (fun u hu v hv => by
      have := hinc u hu v hv
      refine le_of_eq_of_le ?_ this
      congr 1; funext ω; ring)
    (σ := 1) (fun v hv => by
      rw [show (fun ω => -Y v ω) = -(Y v) from rfl, variance_neg]; exact hvar v hv) hu0
  have hB : IsCompact (ferniqueBox 0 m) := isCompact_ferniqueBox 0 m
  have hsub : {ω | ¬ ∀ x ∈ ferniqueBox 0 m, |Y x ω| ≤ M} ⊆
      {ω | ferniqueCF * Real.sqrt (8 * m * m) + u ≤ ⨆ v : ferniqueBox 0 m, Y v ω} ∪
        {ω | ferniqueCF * Real.sqrt (8 * m * m) + u ≤ ⨆ v : ferniqueBox 0 m, -Y v ω} := by
    intro ω hω
    simp only [mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨x, hx, hlt⟩ := hω
    have bd1 : BddAbove (range fun v : ferniqueBox 0 m => Y v ω) :=
      (hB.image (hY.cont ω)).bddAbove.mono (by rintro _ ⟨v, rfl⟩; exact ⟨v, v.2, rfl⟩)
    have bd2 : BddAbove (range fun v : ferniqueBox 0 m => -Y v ω) :=
      (hB.image (hY.cont ω).neg).bddAbove.mono (by rintro _ ⟨v, rfl⟩; exact ⟨v, v.2, rfl⟩)
    rcases lt_abs.1 hlt with h | h
    · left
      exact (le_of_lt h).trans (le_ciSup (f := fun v : ferniqueBox 0 m => Y v ω) bd1 ⟨x, hx⟩)
    · right
      exact (le_of_lt h).trans (le_ciSup (f := fun v : ferniqueBox 0 m => -Y v ω) bd2 ⟨x, hx⟩)
  calc P {ω | ¬ ∀ x ∈ ferniqueBox 0 m, |Y x ω| ≤ M}
      ≤ P {ω | ferniqueCF * Real.sqrt (8 * m * m) + u ≤ ⨆ v : ferniqueBox 0 m, Y v ω} +
        P {ω | ferniqueCF * Real.sqrt (8 * m * m) + u ≤ ⨆ v : ferniqueBox 0 m, -Y v ω} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (Real.exp (-u ^ 2 / (2 * 1 ^ 2))) +
          ENNReal.ofReal (Real.exp (-u ^ 2 / (2 * 1 ^ 2))) := by
        gcongr
        · rw [← ofReal_measureReal (measure_ne_top _ _)]
          exact ENNReal.ofReal_le_ofReal h1
        · rw [← ofReal_measureReal (measure_ne_top _ _)]
          exact ENNReal.ofReal_le_ofReal h2
    _ = ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * 1 ^ 2))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end S6AB
end DDDF
end LQGMetric
