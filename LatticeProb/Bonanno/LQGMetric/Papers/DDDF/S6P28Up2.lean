/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P28Up2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28Sup
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Thm11
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DiamMean

/-!
# DDDF Prop 28, Part 1 Step 2, for the family `δ ∈ (0,1)` (task P2-DDDF6f)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1438–1446 (Part 1, Step 2), for the family
`δ = 2^{-n-r}` (l. 1648): pairs at distance `≤ δ`. For such `x, x'`,
`d_δ(x,x') ≤ λ_δ⁻¹ e^{ξ sup_{[0,1]²} φ_δ} |x − x'|` (straight segment), `|x−x'|^{1−β} ≤ 2^{-n(1−β)}`,
`λ_δ ≥ e^{-C} λ_n ≥ c 2^{-n(1−ξQ+ζ)}` ((6.98), (5.54)), so the event forces
`sup |φ_δ| ≥ C_F√6 + 2(n+1) log 2 + m`, whose probability is `≤ e^{-2m}`
(`S6P28.phiVer_sup_tail_unif`, the uniform form of (2.11)).

`upper_small`: for `0 < β ≤ 1`, `β < ξ(q − 2)` and `ε > 0` there is `C` with
`P(∃ x, x' ∈ [0,1]², |x − x'| ≤ δ, C |x − x'|^β < d_δ(x,x')) ≤ ε` for all `δ ∈ (0,1)`.
(The restriction `β ≤ 1` is DDDF's `1 − β > 0`, l. 1442, which DDDF derive from `1 − ξQ ≥ −2ξ`;
here it is a hypothesis, harmless since (UpperHolder) is only needed for some `β > 0`.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace LQGMetric
namespace DDDF
namespace S6P28

open WhiteNoise SupTail Blueprint LFPP

/-- the segment bound with the weight bounded on a convex set containing the segment -/
lemma lfppDOn_le_of_bound_on {ξ : ℝ} {φ : ℂ → ℝ} {S : Set ℂ} (hS : Convex ℝ S) {z w : ℂ}
    (hz : z ∈ S) (hw : w ∈ S) {B : ℝ} (hB : ∀ x ∈ S, Real.exp (ξ * φ x) ≤ B) :
    lfppDOn ξ φ S z w ≤ ENNReal.ofReal (B * ‖w - z‖) := by
  refine (lfppDOn_le_segCost hS hz hw).trans ?_
  rw [segCost, lfppLen_eq]
  calc ∫⁻ t in Icc (0 : ℝ) 1, lenDens ξ φ (segPath z w) t
      ≤ ∫⁻ _ in Icc (0 : ℝ) 1, ENNReal.ofReal (B * ‖w - z‖) := by
        refine setLIntegral_mono measurable_const fun u hu => ?_
        rw [lenDens_segPath]
        exact ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (hB _ (segPath_mem hS hz hw hu)) (norm_nonneg _))
    _ = ENNReal.ofReal (B * ‖w - z‖) := by simp

/-- `d_f(x,y) ≤ e^{ξ M} |x − y|` on `[0,1]²` if `|f| ≤ M` there (`ξ ≥ 0`) -/
lemma lenMetricOn_le_exp {ξ M : ℝ} (hξ : 0 ≤ ξ) {f : ℂ → ℝ}
    (hM : ∀ x ∈ closedUnitSquare, |f x| ≤ M) {z w : ℂ} (hz : z ∈ closedUnitSquare)
    (hw : w ∈ closedUnitSquare) :
    lenMetricOn ξ f closedUnitSquare z w ≤ Real.exp (ξ * M) * ‖w - z‖ := by
  simp only [lenMetricOn, DFGPS.crossLenIn_singleton]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity)
    (lfppDOn_le_of_bound_on DFGPS.convex_closedUnitSquare hz hw fun x hx => ?_)
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hM x hx)) hξ)

lemma closedUnitSquare_sub_box : closedUnitSquare ⊆ ferniqueBox 0 1 := by
  intro z ⟨h1, h2, h3, h4⟩
  simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc, Complex.zero_re, Complex.zero_im,
    zero_add]
  exact ⟨⟨h1, h2⟩, h3, h4⟩

/-- `δ = 2^{-(n+r)}` lies in `[2^{-n}/2, 2^{-n}]` -/
lemma split_bounds (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ((2 : ℝ) ^ n)⁻¹ ≤ 2 * (2 : ℝ) ^ (-((n : ℝ) + r)) ∧
      (2 : ℝ) ^ (-((n : ℝ) + r)) ≤ ((2 : ℝ) ^ n)⁻¹ := by
  have e : (2 : ℝ) ^ (-((n : ℝ) + r)) = ((2 : ℝ) ^ n)⁻¹ * (2 : ℝ) ^ (-r) := by
    rw [neg_add, Real.rpow_add (by norm_num), Real.rpow_neg (by norm_num), Real.rpow_natCast]
  have h1 : (2 : ℝ) ^ (-r) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h2 : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-r) := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (-1 : ℝ) ≤ -r by linarith)
    rwa [Real.rpow_neg_one, ← one_div] at this
  have hp : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
  rw [e]
  constructor <;> nlinarith

/-- **DDDF Prop 28, Part 1 Step 2 for the family** (l. 1438–1446, 1648): small pairs. -/
theorem upper_small {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {ξ q : ℝ} (hξ : 0 < ξ) (h554 : S6Eq5_54 ξ q W P)
    (h698 : S6Eq6_98 ξ W P) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hβ : β < ξ * (q - 2)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1,
      P {ω | ∃ x y : closedUnitSquare, ‖(x : ℂ) - y‖ ≤ δ ∧ C * ‖(x : ℂ) - y‖ ^ β <
        (lambdaDelta ξ W P δ)⁻¹ * lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y}
        ≤ ENNReal.ofReal ε := by
  intro ε hε
  have hP := hW.isProbabilityMeasure
  set ζ := (ξ * (q - 2) - β) / 2 with hζ_def
  have hζ : 0 < ζ := by rw [hζ_def]; linarith
  obtain ⟨c, hc, hlam⟩ := S6D.lambdaN_lower_of_554 hW h554 hζ
  obtain ⟨C0, hC0⟩ := h698
  set m := |Real.log ε| / 2 with hm_def
  have hm : 0 ≤ m := by positivity
  have hεm : Real.exp (-(2 * m)) ≤ ε := by
    calc Real.exp (-(2 * m)) = Real.exp (-|Real.log ε|) := by congr 1; rw [hm_def]; ring
      _ ≤ Real.exp (Real.log ε) := Real.exp_le_exp.2 (neg_abs_le _)
      _ = ε := Real.exp_log hε
  set T := ferniqueCF * Real.sqrt 6 + 2 * Real.log 2 + m with hT_def
  refine ⟨Real.exp (ξ * T + C0) / c, fun δ hδ => ?_⟩
  obtain ⟨n, r, hr0, hr1, hδr⟩ := S6.exists_split hδ.1 hδ.2
  obtain ⟨hδa, hδb⟩ := split_bounds n hr0 hr1
  rw [← hδr] at hδa hδb
  have hY := isPhiVersion_phiVer hW hδ.1 hδ.2.le
  set L := Real.log 2 with hL_def
  have hL : 0 < L := Real.log_pos (by norm_num)
  set Λ := Real.exp (-C0) * (c * Real.exp (-L * (1 - ξ * q + ζ) * n)) with hΛ_def
  have hΛ : Λ ≤ lambdaDelta ξ W P δ := by
    rw [hδr]
    exact (mul_le_mul_of_nonneg_left (hlam n) (Real.exp_pos _).le).trans (hC0 n r hr0 hr1).1
  have hΛ0 : 0 < Λ := by positivity
  set S' := T + 2 * n * L with hS'_def
  have hsub : {ω | ∃ x y : closedUnitSquare, ‖(x : ℂ) - y‖ ≤ δ ∧
      Real.exp (ξ * T + C0) / c * ‖(x : ℂ) - y‖ ^ β <
        (lambdaDelta ξ W P δ)⁻¹ * lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y}
      ⊆ {ω | ferniqueCF * Real.sqrt 6 + (2 * (n + 1) * Real.log 2 + m) ≤
        ⨆ z : ferniqueBox 0 1, |phiVer W P δ 1 z ω|} := by
    rintro ω ⟨x, y, hxy, hlt⟩
    by_contra hcon
    simp only [mem_ofPred_eq, not_le] at hcon
    have hbdd : BddAbove (range fun v : ferniqueBox 0 1 => |phiVer W P δ 1 v ω|) := by
      have := (isCompact_ferniqueBox 0 1).bddAbove_image
        (continuous_abs.comp (hY.cont ω)).continuousOn
      rwa [Set.image_eq_range] at this
    have hM : ∀ z ∈ closedUnitSquare, |phiVer W P δ 1 z ω| ≤ S' := fun z hz => by
      have := le_ciSup hbdd ⟨z, closedUnitSquare_sub_box hz⟩
      rw [hS'_def, hT_def]
      have e : ferniqueCF * Real.sqrt 6 + (2 * (n + 1) * Real.log 2 + m) =
          ferniqueCF * Real.sqrt 6 + 2 * L + m + 2 * n * L := by rw [hL_def]; ring
      rw [e] at hcon
      exact this.trans hcon.le
    have hlen := lenMetricOn_le_exp hξ.le hM x.2 y.2
    rw [norm_sub_rev] at hlen
    set a := ‖(x : ℂ) - y‖ with ha_def
    have ha0 : 0 ≤ a := norm_nonneg _
    have h4 : ((2 : ℝ) ^ n)⁻¹ ^ (1 - β) = Real.exp (-(n * L * (1 - β))) := by
      rw [Real.rpow_def_of_pos (by positivity), Real.log_inv, Real.log_pow, hL_def]; congr 1
      ring
    have hpow : a ≤ a ^ β * Real.exp (-(n * L * (1 - β))) := by
      rcases ha0.eq_or_lt with h | h
      · rw [← h, Real.zero_rpow hβ0.ne', zero_mul]
      · have e : a = a ^ β * a ^ (1 - β) := by rw [← Real.rpow_add h]; simp
        have h2 : a ^ (1 - β) ≤ δ ^ (1 - β) := Real.rpow_le_rpow ha0 hxy (by linarith)
        have h3 : δ ^ (1 - β) ≤ ((2 : ℝ) ^ n)⁻¹ ^ (1 - β) :=
          Real.rpow_le_rpow hδ.1.le hδb (by linarith)
        calc a = a ^ β * a ^ (1 - β) := e
          _ ≤ a ^ β * Real.exp (-(n * L * (1 - β))) := by
            gcongr; exact (h2.trans h3).trans h4.le
    have hlen0 : 0 ≤ lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y :=
      ENNReal.toReal_nonneg
    have hE : ξ * S' + -(n * L * (1 - β)) - (-C0 + -L * (1 - ξ * q + ζ) * n) =
        ξ * T + C0 + -(ζ * n * L) := by
      rw [hS'_def, hζ_def]; ring
    have hid : Λ⁻¹ * (Real.exp (ξ * S') * (a ^ β * Real.exp (-(n * L * (1 - β))))) =
        Real.exp (ξ * T + C0) / c * a ^ β * Real.exp (-(ζ * n * L)) := by
      have key : Real.exp (ξ * S') * Real.exp (-(n * L * (1 - β))) =
          Real.exp (ξ * T + C0) * Real.exp (-(ζ * n * L)) *
            (Real.exp (-C0) * Real.exp (-L * (1 - ξ * q + ζ) * n)) := by
        simp only [← Real.exp_add]; congr 1; linear_combination hE
      have e1 : Real.exp (-C0) ≠ 0 := (Real.exp_pos _).ne'
      have e2 : Real.exp (-L * (1 - ξ * q + ζ) * n) ≠ 0 := (Real.exp_pos _).ne'
      calc Λ⁻¹ * (Real.exp (ξ * S') * (a ^ β * Real.exp (-(n * L * (1 - β)))))
          = (Real.exp (ξ * S') * Real.exp (-(n * L * (1 - β)))) * a ^ β /
              (Real.exp (-C0) * (c * Real.exp (-L * (1 - ξ * q + ζ) * n))) := by
            rw [hΛ_def, div_eq_mul_inv]; ring
        _ = Real.exp (ξ * T + C0) * Real.exp (-(ζ * n * L)) *
              (Real.exp (-C0) * Real.exp (-L * (1 - ξ * q + ζ) * n)) * a ^ β /
              (Real.exp (-C0) * (c * Real.exp (-L * (1 - ξ * q + ζ) * n))) := by rw [key]
        _ = Real.exp (ξ * T + C0) / c * a ^ β * Real.exp (-(ζ * n * L)) := by
            field_simp
    have hexp : Real.exp (-(ζ * n * L)) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : 0 ≤ ζ * n * L := by positivity
      linarith)
    have key : (lambdaDelta ξ W P δ)⁻¹ *
        lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y ≤
        Real.exp (ξ * T + C0) / c * a ^ β := by
      calc _ ≤ Λ⁻¹ * (Real.exp (ξ * S') * a) :=
            mul_le_mul (inv_anti₀ hΛ0 hΛ) hlen hlen0 (inv_nonneg.2 hΛ0.le)
        _ ≤ Λ⁻¹ * (Real.exp (ξ * S') * (a ^ β * Real.exp (-(n * L * (1 - β))))) := by
            gcongr
        _ = Real.exp (ξ * T + C0) / c * a ^ β * Real.exp (-(ζ * n * L)) := hid
        _ ≤ Real.exp (ξ * T + C0) / c * a ^ β * 1 := by gcongr
        _ = _ := mul_one _
    exact absurd hlt (not_lt.2 key)
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal
    ((phiVer_sup_tail_unif hW n hδa hδb hδ.2 hm).trans hεm)

end S6P28
end DDDF
end LQGMetric
