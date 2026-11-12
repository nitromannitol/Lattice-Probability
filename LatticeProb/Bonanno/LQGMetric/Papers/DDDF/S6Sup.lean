/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Sup at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.GaussianTail
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2HatTail
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiField

/-!
# DDDF (6.98): the low-frequency field `φ_{2^{-r},1}`, `r ∈ [0,1]` (task P2-DDDF6)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 1613: "with high probability `sup_{[0,1]²} |φ_{0,r}| ≤ C_r ≤ C`". `low_sup_tail` makes the
uniformity in `r` explicit: for `a = 2^{-r} ∈ [1/2, 1]`, `φ_{a,1}` has `Var ≤ log 2 ≤ 1` and
`E(φ_{a,1}(v) − φ_{a,1}(u))² ≤ |u − v|²/a² ≤ 8|u − v|` on `[0,1]²` (`DZZ.dzz_variance_hat_sub_le`),
so Fernique + Borell–TIS on one box (`DGo.box_sup_tail`, applied to `±φ`) give a tail bound
uniform in `a`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace LQGMetric
namespace DDDF
namespace S6

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Uniform sup tail of `φ_{a,1}`, `a ∈ [1/2, 1]`** (DDDF l. 1613). -/
theorem low_sup_tail (hW : IsWhiteNoise P W) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : ℝ, 1 / 2 ≤ a → a ≤ 1 →
      P {ω | ¬ ∀ x ∈ (rectAB 1 1).toSet, |phiVer W P a 1 x ω| ≤ M} ≤ ENNReal.ofReal ε := by
  have hP := hW.isProbabilityMeasure
  set m : ℝ := max 0 (Real.log (2 / ε))
  set u : ℝ := √(2 * m)
  have hm0 : 0 ≤ m := le_max_left _ _
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = 2 * m := Real.sq_sqrt (by positivity)
  have hexp : Real.exp (-u ^ 2 / (2 * 1 ^ 2)) ≤ ε / 2 := by
    rw [hu2, show -(2 * m) / (2 * 1 ^ 2) = -m by ring]
    calc Real.exp (-m) ≤ Real.exp (-Real.log (2 / ε)) := Real.exp_le_exp.2 (by
          simp only [m]; linarith [le_max_right 0 (Real.log (2 / ε))])
      _ = ε / 2 := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  set M : ℝ := ferniqueCF * Real.sqrt (8 * 1) + u
  have hM0 : 0 ≤ M := by have := ferniqueCF_pos; positivity
  refine ⟨M, hM0, fun a ha12 ha1 => ?_⟩
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha12
  have hY := isPhiVersion_phiVer hW ha0 ha1
  set Y := phiVer W P a 1
  have hint0 : ∀ v, ∫ ω, Y v ω ∂P = 0 := fun v => by
    rw [integral_congr_ae (hY.ae_eq v)]; exact integral_phi hW a 1 v
  have hX : IsGaussianProcess Y P :=
    (isGaussianProcess_phi_comp hW a 1 (fun v : ℂ => v)).congr fun v => (hY.ae_eq v).symm
  have hinc : ∀ u ∈ ferniqueBox 0 1, ∀ v ∈ ferniqueBox 0 1,
      ∫ ω, (Y v ω - Y u ω) ^ 2 ∂P ≤ 8 * ‖u - v‖ := by
    intro u hu v hv
    have hm : AEMeasurable (fun ω => phi W a 1 v ω - phi W a 1 u ω) P :=
      ((measurable_phi hW a 1 v).sub (measurable_phi hW a 1 u)).aemeasurable
    have h0 : ∫ ω, (phi W a 1 v ω - phi W a 1 u ω) ∂P = 0 := by
      rw [integral_sub ((memLp_phi hW a 1 v).integrable one_le_two)
        ((memLp_phi hW a 1 u).integrable one_le_two), integral_phi hW, integral_phi hW, sub_zero]
    have hae2 : (fun ω => (Y v ω - Y u ω) ^ 2) =ᵐ[P]
        fun ω => (phi W a 1 v ω - phi W a 1 u ω) ^ 2 := by
      filter_upwards [hY.ae_eq u, hY.ae_eq v] with ω h1 h2; rw [h1, h2]
    rw [integral_congr_ae hae2, ← variance_of_integral_eq_zero hm h0]
    have h1 := DZZ.dzz_variance_hat_sub_le hW ha0 ha1 v u
    have hr := DZZ.norm_sub_le_of_mem_ferniqueBox hu hv
    have hr0 := norm_nonneg (u - v)
    rw [norm_sub_rev] at h1
    have ha2 : (1 / 4 : ℝ) ≤ a ^ 2 := by nlinarith
    calc _ ≤ ‖u - v‖ ^ 2 / a ^ 2 := h1
      _ ≤ ‖u - v‖ ^ 2 / (1 / 4) := div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) ha2
      _ ≤ 8 * ‖u - v‖ := by nlinarith
  have hvar : ∀ v ∈ ferniqueBox 0 1, Var[Y v; P] ≤ 1 ^ 2 := by
    intro v _
    rw [variance_congr (hY.ae_eq v), variance_phi hW ha0 ha1, one_pow]
    have h2 : 1 / a ≤ 2 := by rw [div_le_iff₀ ha0]; linarith
    have := Real.log_le_sub_one_of_pos (show 0 < 1 / a by positivity)
    linarith
  have hYc : ∀ ω, ContinuousOn (fun v => Y v ω) (ferniqueBox 0 1) :=
    fun ω => (hY.cont ω).continuousOn
  -- the same for `−Y`
  have hXn : IsGaussianProcess (fun v ω => -Y v ω) P := by
    have := hX.smul (fun _ => (-1 : ℝ))
    simpa [smul_eq_mul] using this
  have h1 := DGo.box_sup_tail hX hint0 (y := 0) one_pos (by norm_num : (0 : ℝ) < 8) hYc hinc hvar
    hu0
  have h2 := DGo.box_sup_tail hXn (fun v => by rw [integral_neg, hint0, neg_zero]) (y := 0) one_pos
    (by norm_num : (0 : ℝ) < 8) (fun ω => (hYc ω).neg)
    (fun u hu v hv => by
      have := hinc u hu v hv
      refine le_of_eq_of_le ?_ this
      congr 1; funext ω; ring)
    (σ := 1) (fun v hv => by
      rw [show (fun ω => -Y v ω) = -(Y v) from rfl, variance_neg]; exact hvar v hv) hu0
  -- the event is in the union of the two sup events
  have hB : IsCompact (ferniqueBox 0 1) := isCompact_ferniqueBox 0 1
  have hsub : {ω | ¬ ∀ x ∈ (rectAB 1 1).toSet, |Y x ω| ≤ M} ⊆
      {ω | ferniqueCF * Real.sqrt (8 * 1) + u ≤ ⨆ v : ferniqueBox 0 1, Y v ω} ∪
        {ω | ferniqueCF * Real.sqrt (8 * 1) + u ≤ ⨆ v : ferniqueBox 0 1, -Y v ω} := by
    intro ω hω
    simp only [mem_ofPred_eq, not_forall, not_le, rectAB_one_toSet] at hω
    obtain ⟨x, hx, hlt⟩ := hω
    have bd1 : BddAbove (range fun v : ferniqueBox 0 1 => Y v ω) :=
      (hB.image (hY.cont ω)).bddAbove.mono (by rintro _ ⟨v, rfl⟩; exact ⟨v, v.2, rfl⟩)
    have bd2 : BddAbove (range fun v : ferniqueBox 0 1 => -Y v ω) :=
      (hB.image (hY.cont ω).neg).bddAbove.mono (by rintro _ ⟨v, rfl⟩; exact ⟨v, v.2, rfl⟩)
    rcases lt_abs.1 hlt with h | h
    · left
      exact (le_of_lt h).trans (le_ciSup (f := fun v : ferniqueBox 0 1 => Y v ω) bd1 ⟨x, hx⟩)
    · right
      exact (le_of_lt h).trans (le_ciSup (f := fun v : ferniqueBox 0 1 => -Y v ω) bd2 ⟨x, hx⟩)
  calc P {ω | ¬ ∀ x ∈ (rectAB 1 1).toSet, |Y x ω| ≤ M}
      ≤ P {ω | ferniqueCF * Real.sqrt (8 * 1) + u ≤ ⨆ v : ferniqueBox 0 1, Y v ω} +
        P {ω | ferniqueCF * Real.sqrt (8 * 1) + u ≤ ⨆ v : ferniqueBox 0 1, -Y v ω} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
        gcongr
        · rw [← ofReal_measureReal (measure_ne_top _ _)]
          exact ENNReal.ofReal_le_ofReal (h1.trans hexp)
        · rw [← ofReal_measureReal (measure_ne_top _ _)]
          exact ENNReal.ofReal_le_ofReal (h2.trans hexp)
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end S6
end DDDF
end LQGMetric
