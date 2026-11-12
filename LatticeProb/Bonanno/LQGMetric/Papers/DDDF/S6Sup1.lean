/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Sup1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Thm12Sq
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffCV
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont

/-!
# The sup bound `hsup` of `S6Thm.s6_thm12_tight_sq` (task P2-DDDF6f, O9 leaf, D-DDDF-13)

For the zero-boundary GFF `h̊` on `D = (−1,2)²` and continuous versions `Y δ` of `p_{δ/2} * h̊`,
`sup_{|x| ≤ 6} |Y δ x|` is tight uniformly in `δ ∈ [1/2, 1)`. DDDF (arXiv:1904.08021,
`tightness.tex` l. 1497–1506) obtain Theorem 1 (2) from Proposition 29, which covers only
`t ∈ (0,1/2)`; the range `δ ∈ [1/2,1)` is D-DDDF-13 (smoothed field with variance and Lipschitz
increments bounded uniformly in `δ`). own standard argument:

* single-point variance `Q(ρ,ρ) ≤ (2L²/π) 4C ∫|ρ|` from `DFGPS.zbVar_sq_le` with `σ = 0`
  (`zeroGFFTestCov U ρ 0 = 0`: the measures of the zero density vanish);
* increments from `DFGPS.zbVar_sq_le` and `DFGPS.integral_abs_heat_sub_le` (as in
  `DFGPS.exists_heat_contVersion_sq_of_pos`), constants uniform in `s = δ/2 ∈ [1/4, 1/2)`;
* Fernique (`DGo.box_sup_tail`) on the box `[−6,6]²` for `±Y δ`, as in `S6AB.low_sup_tail_box`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DDDF
namespace S6Sup

open QuantumZipper QuantumZipper.K3 HeatSq Blueprint DFGPS SupTail

lemma testMeasPos_zero : testMeasPos (0 : ℂ → ℝ) = 0 := by
  simp [testMeasPos]

lemma testMeasNeg_zero : testMeasNeg (0 : ℂ → ℝ) = 0 := by
  simp [testMeasNeg]

lemma dualCov_zero_right (D : Set ℂ) (V : Set (ℂ → ℝ)) (μ : Measure ℂ) :
    dualCov D V μ 0 = 0 := by
  have h0 : dualNormSq D V 0 = 0 := by simp [dualNormSq]
  simp [dualCov, h0]

/-- `Cov(⟨h,ρ⟩, ⟨h,0⟩) = 0` -/
lemma zeroGFFTestCov_zero_right (U : Set ℂ) (ρ : ℂ → ℝ) : zeroGFFTestCov U ρ 0 = 0 := by
  simp [zeroGFFTestCov, testMeasPos_zero, testMeasNeg_zero, dualCov_zero_right]

/-- the zero element of `BddOn U` -/
def bddZero (U : Set ℂ) : BddOn U := ⟨0, measurable_const, ⟨0, fun z => by simp⟩, fun _ _ => rfl⟩

/-- **single-point variance on a square**: `Q(ρ,ρ) ≤ (2L²/π) ∫ |ρ| · 4C` for `|ρ| ≤ C` -/
theorem zbVar_self_le {a L : ℝ} (hL : 0 < L) (ρ : BddOn (sqOpen a L)) {C : ℝ}
    (hC : ∀ z, |ρ.1 z| ≤ C) :
    zeroGFFTestCov (sqOpens a L) ρ.1 ρ.1 ≤ 2 * L ^ 2 / Real.pi * ∫ x, |ρ.1 x| * (4 * C) := by
  have h := zbVar_sq_le hL ρ (bddZero _) (C := C) (fun z => by
    simpa [bddZero] using hC z)
  simpa [bddZero, zeroGFFTestCov_zero_right] using h

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- variance of an increment of the extended zero-boundary GFF -/
lemma variance_sub_zbExt [IsProbabilityMeasure P] {D : TopologicalSpace.Opens ℂ}
    {Xh : BddOn (D : Set ℂ) → Ω → ℝ} (hX : IsZBGFFProcessExt D Xh P) (ρ σ : BddOn (D : Set ℂ)) :
    Var[fun ω => Xh ρ ω - Xh σ ω; P] = zeroGFFTestCov D ρ.1 ρ.1 - 2 * zeroGFFTestCov D ρ.1 σ.1 +
        zeroGFFTestCov D σ.1 σ.1 := by
  have h2 : ∀ τ, MemLp (Xh τ) 2 P := fun τ => (hX.gaussian.hasGaussianLaw_eval τ).memLp_two
  rw [variance_fun_sub (h2 ρ) (h2 σ), ← covariance_self (hX.measurable ρ).aemeasurable,
    ← covariance_self (hX.measurable σ).aemeasurable, hX.covariance_eq, hX.covariance_eq,
    hX.covariance_eq]

lemma abs_heatBdd_le {a L s : ℝ} (hs : 0 < s) (x z : ℂ) :
    |(heatBdd (sqOpens a L) s x).1 z| ≤ (2 * Real.pi * s)⁻¹ := by
  have hU : MeasurableSet (sqOpens a L : Set ℂ) := measurableSet_sqOpen a L
  rw [heatBdd_val hU hs]
  by_cases hz : z ∈ (sqOpens a L : Set ℂ)
  · show |_| ≤ _
    rw [indicator_of_mem hz, abs_of_nonneg (heatKernel_nonneg s hs.le x z)]
    exact KilledHeat.heatKernel_le_inv s hs.le x z
  · rw [indicator_of_notMem hz, abs_zero]; positivity

lemma integral_abs_heatBdd_le {a L s : ℝ} (hs : 0 < s) (x : ℂ) :
    ∫ z, |(heatBdd (sqOpens a L) s x).1 z| ≤ 1 := by
  have hU : MeasurableSet (sqOpens a L : Set ℂ) := measurableSet_sqOpen a L
  rw [heatBdd_val hU hs, ← integral_heatKernel s hs x]
  refine integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _)
    (integrable_heatKernel s hs x) (ae_of_all _ fun z => ?_)
  by_cases hz : z ∈ (sqOpens a L : Set ℂ)
  · show |_| ≤ _
    rw [indicator_of_mem hz, abs_of_nonneg (heatKernel_nonneg s hs.le x z)]
  · show |_| ≤ _
    rw [indicator_of_notMem hz, abs_zero]; exact heatKernel_nonneg s hs.le x z

lemma closedBall_sub_box6 : closedBall (0 : ℂ) 6 ⊆ ferniqueBox (-6 - 6 * Complex.I) 12 := by
  intro z hz
  rw [mem_closedBall, dist_zero_right] at hz
  have h1 := abs_le.1 ((Complex.abs_re_le_norm z).trans hz)
  have h2 := abs_le.1 ((Complex.abs_im_le_norm z).trans hz)
  simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc]
  norm_num
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- **Fernique tail of `sup_{|x| ≤ 6} |p_s * h̊|`** on `D = (−1,2)²`, uniformly in
`s ≥ 1/4` -/
theorem sup_tail_fixed [IsProbabilityMeasure P] {Xh : BddOn (sqOpens (-1) 3 : Set ℂ) → Ω → ℝ}
    (hX : IsZBGFFProcessExt (sqOpens (-1) 3) Xh P) {s : ℝ} (hs1 : 1 / 4 ≤ s)
    {Z : ℂ → Ω → ℝ} (hZ : IsContVersion (fun x => Xh (heatBdd (sqOpens (-1) 3) s x)) Z P)
    {u : ℝ} (hu : 0 ≤ u) :
    P {ω | ∃ x ∈ closedBall (0 : ℂ) 6, ferniqueCF * Real.sqrt (200 * 12) + u < |Z x ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * 5 ^ 2))) := by
  have hs : 0 < s := by linarith
  have hU : MeasurableSet (sqOpens (-1) 3 : Set ℂ) := measurableSet_sqOpen (-1) 3
  set ρ : ℂ → BddOn (sqOpens (-1) 3 : Set ℂ) := fun x => heatBdd (sqOpens (-1) 3) s x with hρ
  have hC1 : (2 * Real.pi * s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])
  have hC0 : 0 ≤ (2 * Real.pi * s)⁻¹ := by positivity
  have hpi : 2 * 3 ^ 2 / Real.pi ≤ 6 := by
    rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
  have hm : ∀ x, Measurable (Xh (ρ x)) := fun x => hX.measurable _
  have h2 : ∀ x, MemLp (Xh (ρ x)) 2 P := fun x =>
    (hX.gaussian.hasGaussianLaw_eval (ρ x)).memLp_two
  have hint0 : ∀ v, ∫ ω, Z v ω ∂P = 0 := fun v => by
    rw [integral_congr_ae (hZ.2.2 v)]; exact hX.centered _
  have hG : IsGaussianProcess Z P :=
    (hX.gaussian.comp_right ρ).congr fun v => (hZ.2.2 v).symm
  set B := ferniqueBox (-6 - 6 * Complex.I) 12
  have hinc : ∀ u ∈ B, ∀ v ∈ B, ∫ ω, (Z v ω - Z u ω) ^ 2 ∂P ≤ 200 * ‖u - v‖ := by
    intro u _ v _
    have hae : (fun ω => (Z v ω - Z u ω) ^ 2) =ᵐ[P]
        fun ω => (Xh (ρ v) ω - Xh (ρ u) ω) ^ 2 := by
      filter_upwards [hZ.2.2 u, hZ.2.2 v] with ω h1 h2; rw [h1, h2]
    have h0 : ∫ ω, (Xh (ρ v) ω - Xh (ρ u) ω) ∂P = 0 := by
      rw [integral_sub ((h2 v).integrable one_le_two) ((h2 u).integrable one_le_two),
        hX.centered, hX.centered, sub_zero]
    have hm' : AEMeasurable (fun ω => Xh (ρ v) ω - Xh (ρ u) ω) P :=
      ((hm v).sub (hm u)).aemeasurable
    rw [integral_congr_ae hae, ← variance_of_integral_eq_zero hm' h0, variance_sub_zbExt hX]
    have hb : ∀ z, |(ρ v).1 z - (ρ u).1 z| ≤ (2 * Real.pi * s)⁻¹ := fun z => by
      simp only [hρ]; rw [heatBdd_val hU hs, heatBdd_val hU hs]
      exact abs_indicator_heat_sub_le hs v u z
    refine (zbVar_sq_le (by norm_num : (0 : ℝ) < 3) _ _ hb).trans ?_
    rw [integral_mul_const]
    have hI : ∫ z, |(ρ v).1 z - (ρ u).1 z| ≤
        ‖v - u‖ * ((16 * Real.pi * s ^ 2)⁻¹ + 3 ^ 2 / 2) := by
      simp only [hρ]; rw [heatBdd_val hU hs, heatBdd_val hU hs]
      exact integral_abs_heat_sub_le (a := -1) (by norm_num) hs v u
    have hK : (16 * Real.pi * s ^ 2)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])
    have hI0 : 0 ≤ ∫ z, |(ρ v).1 z - (ρ u).1 z| := integral_nonneg fun _ => abs_nonneg _
    rw [norm_sub_rev] at hI
    have e1 : (∫ z, |(ρ v).1 z - (ρ u).1 z|) * (4 * (2 * Real.pi * s)⁻¹) ≤
        (‖u - v‖ * (1 + 3 ^ 2 / 2)) * (4 * 1) :=
      mul_le_mul (hI.trans (by gcongr)) (by gcongr) (by positivity) (by positivity)
    calc 2 * 3 ^ 2 / Real.pi * ((∫ z, |(ρ v).1 z - (ρ u).1 z|) * (4 * (2 * Real.pi * s)⁻¹))
        ≤ 6 * ((‖u - v‖ * (1 + 3 ^ 2 / 2)) * (4 * 1)) :=
          mul_le_mul hpi e1 (mul_nonneg hI0 (by positivity)) (by norm_num)
      _ ≤ 200 * ‖u - v‖ := by nlinarith [norm_nonneg (u - v)]
  have hvar : ∀ v ∈ B, Var[Z v; P] ≤ 5 ^ 2 := by
    intro v _
    rw [variance_congr (hZ.2.2 v), ← covariance_self (hm v).aemeasurable, hX.covariance_eq]
    refine (zbVar_self_le (a := -1) (L := 3) (by norm_num) (ρ v)
      (fun z => abs_heatBdd_le hs v z)).trans ?_
    rw [integral_mul_const]
    have h1 := integral_abs_heatBdd_le (a := -1) (L := 3) hs v
    calc 2 * 3 ^ 2 / Real.pi * ((∫ z, |(ρ v).1 z|) * (4 * (2 * Real.pi * s)⁻¹))
        ≤ 6 * (1 * (4 * 1)) :=
          mul_le_mul hpi (mul_le_mul h1 (by gcongr) (by positivity) zero_le_one)
            (mul_nonneg (integral_nonneg fun _ => abs_nonneg _) (by positivity)) (by norm_num)
      _ ≤ 5 ^ 2 := by norm_num
  have hZc : ∀ ω, ContinuousOn (fun v => Z v ω) B := fun ω => (hZ.1 ω).continuousOn
  have hXn : IsGaussianProcess (fun v ω => -Z v ω) P := by
    have := hG.smul (fun _ => (-1 : ℝ))
    simpa [smul_eq_mul] using this
  have h12 : (0 : ℝ) < 12 := by norm_num
  have h200 : (0 : ℝ) < 200 := by norm_num
  have e1 := DGo.box_sup_tail hG hint0 h12 h200 hZc hinc hvar hu
  have e2 := DGo.box_sup_tail hXn (fun v => by rw [integral_neg, hint0, neg_zero]) h12
    h200 (fun ω => (hZc ω).neg)
    (fun u hu v hv => by
      have := hinc u hu v hv
      refine le_of_eq_of_le ?_ this
      congr 1; funext ω; ring)
    (σ := 5) (fun v hv => by
      rw [show (fun ω => -Z v ω) = -(Z v) from rfl, variance_neg]; exact hvar v hv) hu
  have hB : IsCompact B := isCompact_ferniqueBox _ _
  set M : ℝ := ferniqueCF * Real.sqrt (200 * 12) + u
  have hsub : {ω | ∃ x ∈ closedBall (0 : ℂ) 6, M < |Z x ω|} ⊆
      {ω | M ≤ ⨆ v : B, Z v ω} ∪ {ω | M ≤ ⨆ v : B, -Z v ω} := by
    rintro ω ⟨x, hx0, hlt⟩
    have hx := closedBall_sub_box6 hx0
    have bd1 : BddAbove (range fun v : B => Z v ω) :=
      (hB.image (hZ.1 ω)).bddAbove.mono (by rintro _ ⟨v, rfl⟩; exact ⟨v, v.2, rfl⟩)
    have bd2 : BddAbove (range fun v : B => -Z v ω) :=
      (hB.image (hZ.1 ω).neg).bddAbove.mono (by rintro _ ⟨v, rfl⟩; exact ⟨v, v.2, rfl⟩)
    rcases lt_abs.1 hlt with h | h
    · left
      exact (le_of_lt h).trans (le_ciSup (f := fun v : B => Z v ω) bd1 ⟨x, hx⟩)
    · right
      exact (le_of_lt h).trans (le_ciSup (f := fun v : B => -Z v ω) bd2 ⟨x, hx⟩)
  calc P {ω | ∃ x ∈ closedBall (0 : ℂ) 6, M < |Z x ω|}
      ≤ P {ω | M ≤ ⨆ v : B, Z v ω} + P {ω | M ≤ ⨆ v : B, -Z v ω} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (Real.exp (-u ^ 2 / (2 * 5 ^ 2))) +
          ENNReal.ofReal (Real.exp (-u ^ 2 / (2 * 5 ^ 2))) := by
        gcongr
        · rw [← ofReal_measureReal (measure_ne_top _ _)]
          exact ENNReal.ofReal_le_ofReal e1
        · rw [← ofReal_measureReal (measure_ne_top _ _)]
          exact ENNReal.ofReal_le_ofReal e2
    _ = ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * 5 ^ 2))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

/-- **The sup bound `hsup` of `S6Thm.s6_thm12_tight_sq`** (DDDF Thm 1 (2) for
`δ ∈ [1/2, 1)`, D-DDDF-13): `sup_{|x| ≤ 6} |Y δ x|` is tight uniformly in `δ ∈ [1/2,1)`. -/
theorem s6_hsup {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Xh : BddOn (sqOpen (-1) 3) → Ω → ℝ) (hX : IsZBGFFProcessExt (sqOpens (-1) 3) Xh P)
    (Y : ℝ → ℂ → Ω → ℝ)
    (hY : ∀ δ ∈ Ioo (0 : ℝ) 1,
      IsContVersion (fun x => Xh (heatBdd (sqOpens (-1) 3) (δ / 2) x)) (Y δ) P) :
    ∀ ζ : ℝ, 0 < ζ → ∃ M : ℝ, ∀ δ ∈ Ico (1 / 2 : ℝ) 1,
      P {ω | ∃ x ∈ closedBall (0 : ℂ) 6, M < |Y δ x ω|} ≤ ENNReal.ofReal ζ := by
  intro ζ hζ
  set u : ℝ := Real.sqrt (50 * |Real.log (ζ / 2)|)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  refine ⟨ferniqueCF * Real.sqrt (200 * 12) + u, fun δ hδ => ?_⟩
  have hδ0 : δ ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_lt_of_le (by norm_num) hδ.1, hδ.2⟩
  refine (sup_tail_fixed hX (s := δ / 2) (by linarith [hδ.1]) (hY δ hδ0)
    hu).trans (ENNReal.ofReal_le_ofReal ?_)
  have e : -u ^ 2 / (2 * 5 ^ 2) = -|Real.log (ζ / 2)| := by
    rw [Real.sq_sqrt (by positivity)]; ring
  rw [e]
  have h3 : Real.exp (-|Real.log (ζ / 2)|) ≤ ζ / 2 := by
    calc Real.exp (-|Real.log (ζ / 2)|) ≤ Real.exp (Real.log (ζ / 2)) :=
          Real.exp_le_exp.2 (neg_abs_le _)
      _ = ζ / 2 := Real.exp_log (half_pos hζ)
  linarith

end S6Sup
end DDDF
end LQGMetric
