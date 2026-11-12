/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8FinSupMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinSup
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiSupTail
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldGrad

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Zero-boundary analogue of DFGPS Lemma 2.1, uniformly over `[0,1]²` (T:883–885)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:883–885): "Lemma 2.1 remains true
with `D_{h̊}^ε`, `D̂_{h̊}^ε` in place of `D_h^ε`, `D̂_h^ε` … with the same proof (actually, the
proof is simpler since one does not need Lemma 2.2)." We prove the needed estimate in the per-`ε`
form required by DDDF's per-`δ` versions `Y δ` (handoff P2-DFB34d, "Key design point"):

`zbLoc_sup_tail`: for all `η, ζ > 0` there is `ε₁ > 0` with, for `ε < ε₁`,
`P(∃ x ∈ [0,1]², |Y_{ε²}(x) − ĥ̊*_ε(x)| > η) ≤ ζ`.

Proof: `G(v) = Y_{ε²}(c v) − ĥ̊*_ε(c v)` (`c` the retraction onto `[0,1]²`) is a.s. equal to
`Xh(T_{c v})`, hence a continuous centred Gaussian field, with `Var G ≤ S(ε)` (`zbLoc_law`) and
`E(G v − G u)² ≤ A(ε)|u − v|` (`zbVar_sq_le` with `abs_zbTail_le`, `integral_abs_zbTail_sub_le`).
The sup bound DZZ Lemma 2.3 + Borell–TIS (`SupTail.tail_iSup_abs_box`, one box `[0,1]²`) gives
`P(sup |G| ≥ C_F √A(ε) + u) ≤ 2 e^{−u²/(2S(ε))}`, and `A(ε), S(ε) → 0`. Own route (the paper's
GFF proof uses the polar formula and Lemma 2.2, T:711–733; the zero-boundary case is "the same
proof"); see DEVIATIONS (proposed DEV-DFGPS-L28-SUP).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped NNReal ENNReal

namespace LQGMetric.DFGPS

open LFPP HeatSq Blueprint SupTail

/-- `A(ε)`: increment constant -/
def zbA (L₀ ε : ℝ) : ℝ :=
  2 * 3 ^ 2 / Real.pi * ((2 * kHeat ε + L₀ * (2 / Real.sqrt ε)) * (4 * (2 * cTail ε))) + ε

/-- `S(ε)`: variance bound -/
def zbS (ε : ℝ) : ℝ := 18 / Real.pi * ((2 * Real.exp (-(1 / (8 * ε)))) * (4 * cTail ε)) + ε

/-- **Per-`ε` sup tail.** -/
theorem zbLoc_sup_tail_eps {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {Xh : BddOn (sqOpen (-1) 3) → Ω → ℝ} (hX : IsZBGFFProcessExt (sqOpens (-1) 3) Xh P)
    {hz : Ω → DistC}
    (hlink : ∀ φ : TestOn (sqOpens (-1) 3), Xh φ.toBddOn =ᵐ[P]
      fun ω => restrictTo (sqOpens (-1) 3) (hz ω) φ)
    {L₀ : ℝ} (hL₀ : 0 ≤ L₀) (hL : ∀ y y' : ℂ,
      |(ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2 y -
        (ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2 y'| ≤ L₀ * ‖y - y'‖)
    {Y : ℂ → Ω → ℝ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hY : IsContVersion (fun x => Xh (heatBdd (sqOpens (-1) 3) (ε ^ 2 / 2) x)) Y P)
    {u : ℝ} (hu : 0 ≤ u) :
    P {ω | ∃ x ∈ closedUnitSquare,
        ferniqueCF * Real.sqrt (zbA L₀ ε) + u < |Y x ω - locMollify ε hε (hz ω) x|} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * zbS ε))) := by
  have hsq : Real.sqrt ε < 1 := by
    rw [Real.sqrt_lt' one_pos]; simpa using hε1
  have hball : ∀ v, closedBall (clampSq v) (Real.sqrt ε) ⊆ sqOpen (-1) 3 := fun v =>
    closedBall_subset_sqOpen (clampSq_mem v) hsq
  have hsupp : ∀ v, tsupport (locTest ε hε (clampSq v) : ℂ → ℝ) ⊆ (sqOpens (-1) 3 : Set ℂ) :=
    fun v => (tsupport_locTest_subset ε hε _).trans (hball v)
  set T : ℂ → BddOn (sqOpen (-1) 3) := fun v => zbTail hε (clampSq v) (hsupp v)
  set G : ℂ → Ω → ℝ := fun v ω => Y (clampSq v) ω - locMollify ε hε (hz ω) (clampSq v)
  have hGT : ∀ v, G v =ᵐ[P] Xh (T v) := fun v =>
    zbLoc_ae_tail hX hlink hε hY (clampSq v) (hsupp v)
  have hG : IsGaussianProcess G P :=
    (hX.gaussian.comp_right T).congr fun v => (hGT v).symm
  have h0 : ∀ v, ∫ ω, G v ω ∂P = 0 := fun v => by
    rw [integral_congr_ae (hGT v)]; exact hX.centered _
  have hc : ∀ ω, Continuous fun v => G v ω := fun ω =>
    ((hY.1 ω).comp continuous_clampSq).sub
      ((continuous_locMollify ε hε (hz ω)).comp continuous_clampSq)
  have hK : 0 ≤ 2 * kHeat ε + L₀ * (2 / Real.sqrt ε) := by
    have := kHeat_nonneg ε; positivity
  have hct := cTail_nonneg ε
  have hinc : ∀ u v, ∫ ω, (G v ω - G u ω) ^ 2 ∂P ≤ zbA L₀ ε * ‖u - v‖ := by
    intro u v
    have hae : (fun ω => (G v ω - G u ω) ^ 2) =ᵐ[P]
        fun ω => (Xh (T v) ω - Xh (T u) ω) ^ 2 := by
      filter_upwards [hGT u, hGT v] with ω h1 h2
      rw [h1, h2]
    have hsq2 := DDDF.integral_sq_of_hasLaw (U := fun ω => Xh (T v) ω - Xh (T u) ω)
      ⟨((hX.measurable _).sub (hX.measurable _)).aemeasurable, map_sub_zbExt hX _ _⟩
    rw [integral_congr_ae hae, hsq2, Real.coe_toNNReal']
    have hC : ∀ w, |(T v).1 w - (T u).1 w| ≤ 2 * cTail ε := fun w => by
      have a1 := abs_zbTail_le hε (clampSq v) (hsupp v) w
      have a2 := abs_zbTail_le hε (clampSq u) (hsupp u) w
      exact (abs_sub _ _).trans (by linarith)
    have hI := integral_abs_zbTail_sub_le hL₀ hL hε (clampSq v) (clampSq u) (hsupp v) (hsupp u)
      (hball u)
    have hI' : ∫ w, |(T v).1 w - (T u).1 w| ≤
        (2 * kHeat ε + L₀ * (2 / Real.sqrt ε)) * ‖u - v‖ :=
      hI.trans (mul_le_mul_of_nonneg_left
        (by rw [norm_sub_rev u v]; exact norm_clampSq_sub_le v u) hK)
    have hpos : 0 ≤ zbA L₀ ε * ‖u - v‖ := by
      unfold zbA; have := Real.pi_pos; positivity
    refine max_le ?_ hpos
    refine (zbVar_sq_le (by norm_num : (0 : ℝ) < 3) (T v) (T u) hC).trans ?_
    rw [integral_mul_const]
    have hn := norm_nonneg (u - v)
    calc 2 * 3 ^ 2 / Real.pi * ((∫ w, |(T v).1 w - (T u).1 w|) * (4 * (2 * cTail ε)))
        ≤ 2 * 3 ^ 2 / Real.pi * (((2 * kHeat ε + L₀ * (2 / Real.sqrt ε)) * ‖u - v‖) *
            (4 * (2 * cTail ε))) := by
          have := Real.pi_pos
          gcongr
      _ ≤ zbA L₀ ε * ‖u - v‖ := by
          unfold zbA
          linarith [mul_nonneg hε.le hn]
  have hSpos : 0 < zbS ε := by
    unfold zbS; have := Real.pi_pos; positivity
  have hvar : ∀ v, Var[G v; P] ≤ Real.sqrt (zbS ε) ^ 2 := by
    intro v
    obtain ⟨w, hw, hwle⟩ := zbLoc_law hX hlink hε hY (hball v)
    have hLaw : HasLaw (G v) (gaussianReal 0 w) P :=
      ⟨(hX.measurable _).aemeasurable.congr (hGT v).symm, hw⟩
    rw [hLaw.variance_eq, variance_id_gaussianReal, Real.sq_sqrt hSpos.le]
    have hw' : (w : ℝ) ≤ 18 / Real.pi * ((2 * Real.exp (-(1 / (8 * ε)))) * (4 * cTail ε)) := by
      unfold cTail; exact hwle
    unfold zbS; linarith
  have hApos : 0 < zbA L₀ ε := by
    unfold zbA; have := Real.pi_pos; positivity
  have hT := SupTail.tail_iSup_abs_box (x₀ := 0) one_pos hG h0 hc hApos hinc
    (Real.sqrt_pos.2 hSpos) hvar hu
  rw [mul_one, Real.sq_sqrt hSpos.le] at hT
  have : CompactSpace (ferniqueBox 0 1) :=
    isCompact_iff_compactSpace.1 (isCompact_ferniqueBox 0 1)
  have hsub : {ω | ∃ x ∈ closedUnitSquare,
      ferniqueCF * Real.sqrt (zbA L₀ ε) + u < |Y x ω - locMollify ε hε (hz ω) x|} ⊆
      {ω | ferniqueCF * Real.sqrt (zbA L₀ ε) + u ≤ ⨆ v : ferniqueBox 0 1, |G v ω|} := by
    rintro ω ⟨x, hx, hlt⟩
    have hxB : x ∈ ferniqueBox 0 1 := by
      obtain ⟨h1, h2, h3, h4⟩ := hx
      simp only [ferniqueBox, Complex.zero_re, Complex.zero_im, zero_add]
      exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    have hGx : G x ω = Y x ω - locMollify ε hε (hz ω) x := by
      simp only [G, clampSq_of_mem hx]
    have hbdd : BddAbove (range fun v : ferniqueBox 0 1 => |G v ω|) :=
      (isCompact_range ((continuous_abs.comp (hc ω)).comp continuous_subtype_val)).bddAbove
    refine hlt.le.trans ?_
    rw [← hGx]
    exact le_ciSup (f := fun v : ferniqueBox 0 1 => |G v ω|) hbdd ⟨x, hxB⟩
  calc P _ ≤ P {ω | ferniqueCF * Real.sqrt (zbA L₀ ε) + u ≤ ⨆ v : ferniqueBox 0 1, |G v ω|} :=
        measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | ferniqueCF * Real.sqrt (zbA L₀ ε) + u ≤
          ⨆ v : ferniqueBox 0 1, |G v ω|}) := (ofReal_measureReal).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hT

lemma tendsto_cTail : Tendsto cTail (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_inv_pow_mul_exp 2).const_mul Real.pi⁻¹
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  unfold cTail
  field_simp

lemma tendsto_zbS : Tendsto zbS (𝓝[>] 0) (𝓝 0) := by
  have h := ((tendsto_exp_neg_inv_eight.const_mul 2).mul (tendsto_cTail.const_mul 4)).const_mul
    (18 / Real.pi)
  have h2 := h.add (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (0 : ℝ))))
  simp only [mul_zero, zero_add] at h2
  exact h2

lemma tendsto_zbA (L₀ : ℝ) : Tendsto (zbA L₀) (𝓝[>] 0) (𝓝 0) := by
  -- `kHeat · cTail → 0`
  have h1 : Tendsto (fun ε => kHeat ε * cTail ε) (𝓝[>] 0) (𝓝 0) := by
    have h := ((tendsto_inv_pow_mul_exp 6).const_mul ((4 * Real.pi)⁻¹ * Real.pi⁻¹)).add
      ((tendsto_inv_pow_mul_exp 2).const_mul (9 / 2 * Real.pi⁻¹))
    rw [mul_zero, mul_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    unfold kHeat cTail
    field_simp
    ring
  -- `(2/√ε) · cTail → 0` (squeeze by `2 ε⁻¹ cTail`)
  have h2 : Tendsto (fun ε => 2 / Real.sqrt ε * cTail ε) (𝓝[>] 0) (𝓝 0) := by
    have hu := (tendsto_inv_pow_mul_exp 3).const_mul (2 * Real.pi⁻¹)
    rw [mul_zero] at hu
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have := cTail_nonneg ε
      positivity
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      have hε0 : 0 < ε := hε.1
      have hs0 := Real.sqrt_pos.2 hε0
      have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε.2.le
      have hss := Real.mul_self_sqrt hε0.le
      have hle : ε ≤ Real.sqrt ε := by nlinarith
      have hct := cTail_nonneg ε
      have hd : 2 / Real.sqrt ε ≤ 2 / ε := div_le_div_of_nonneg_left (by norm_num) hε0 hle
      calc 2 / Real.sqrt ε * cTail ε ≤ 2 / ε * cTail ε := mul_le_mul_of_nonneg_right hd hct
        _ = 2 * Real.pi⁻¹ * (ε⁻¹ ^ 3 * Real.exp (-(1 / (8 * ε)))) := by
          unfold cTail; field_simp
  have h := ((h1.const_mul 2).add (h2.const_mul L₀)).const_mul (2 * 3 ^ 2 / Real.pi * 8)
  have h' := h.add (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (0 : ℝ))))
  simp only [mul_zero, add_zero] at h'
  refine h'.congr fun ε => ?_
  unfold zbA
  simp only [id]
  ring

/-- **Zero-boundary analogue of DFGPS Lemma 2.1, sup over `[0,1]²`** (T:883–885), per `ε` with
bounds uniform in `ε`. -/
theorem zbLoc_sup_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Xh : BddOn (sqOpen (-1) 3) → Ω → ℝ} (hX : IsZBGFFProcessExt (sqOpens (-1) 3) Xh P)
    {hz : Ω → DistC}
    (hlink : ∀ φ : TestOn (sqOpens (-1) 3), Xh φ.toBddOn =ᵐ[P]
      fun ω => restrictTo (sqOpens (-1) 3) (hz ω) φ)
    {Y : ℝ → ℂ → Ω → ℝ}
    (hY : ∀ δ ∈ Ioo (0 : ℝ) 1,
      IsContVersion (fun x => Xh (heatBdd (sqOpens (-1) 3) (δ / 2) x)) (Y δ) P) :
    ∀ η > 0, ∀ ζ > 0, ∃ ε₁ > 0, ∀ ε (hε : 0 < ε), ε < ε₁ →
      P {ω | ∃ x ∈ closedUnitSquare, η < |Y (ε ^ 2) x ω - locMollify ε hε (hz ω) x|} ≤
        ENNReal.ofReal ζ := by
  intro η hη ζ hζ
  obtain ⟨L₀, hL₀, hL⟩ := exists_lipschitz_bumpBase
  have E1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ferniqueCF * Real.sqrt (zbA L₀ ε) < η / 2 := by
    have h := ((Real.continuous_sqrt.tendsto 0).comp (tendsto_zbA L₀)).const_mul ferniqueCF
    rw [Real.sqrt_zero, mul_zero] at h
    exact h.eventually (gt_mem_nhds (by linarith))
  have E2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 * Real.exp (-(η / 2) ^ 2 / (2 * zbS ε)) < ζ := by
    have hS' : Tendsto zbS (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_zbS, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      show 0 < zbS ε
      unfold zbS; have := Real.pi_pos; have := cTail_nonneg ε; positivity
    have h3 := (hS'.inv_tendsto_nhdsGT_zero).const_mul_atTop_of_neg
      (show -(η / 2) ^ 2 / 2 < 0 by
        have : 0 < (η / 2) ^ 2 := (by positivity)
        linarith)
    have h4 := (Real.tendsto_exp_atBot.comp h3).const_mul 2
    rw [mul_zero] at h4
    refine (h4.eventually (gt_mem_nhds hζ)).mono fun ε hε => ?_
    have e : -(η / 2) ^ 2 / (2 * zbS ε) = -(η / 2) ^ 2 / 2 * zbS⁻¹ ε := by
      simp only [Pi.inv_apply]; ring
    rw [e]
    exact hε
  have E3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)) fun ε hε => hε.2
  obtain ⟨ε₁, hε₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (E1.and (E2.and E3))
  refine ⟨ε₁, hε₁, fun ε hε hεε => ?_⟩
  obtain ⟨e1, e2, e3⟩ := hsub ⟨hε, hεε⟩
  have hδ : ε ^ 2 ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, by nlinarith⟩
  have hT := zbLoc_sup_tail_eps hX hlink hL₀ hL hε e3 (hY _ hδ) (u := η / 2) (by positivity)
  calc P _ ≤ P {ω | ∃ x ∈ closedUnitSquare, ferniqueCF * Real.sqrt (zbA L₀ ε) + η / 2 <
        |Y (ε ^ 2) x ω - locMollify ε hε (hz ω) x|} := by
        refine measure_mono fun ω ⟨x, hx, hlt⟩ => ⟨x, hx, ?_⟩
        linarith
    _ ≤ _ := hT
    _ ≤ ENNReal.ofReal ζ := ENNReal.ofReal_le_ofReal e2.le

end LQGMetric.DFGPS
