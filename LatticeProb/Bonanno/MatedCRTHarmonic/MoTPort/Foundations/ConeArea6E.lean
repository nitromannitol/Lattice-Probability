/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea6E at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea6D

/-!
`ConeArea5.ae_tight_logFactor`, `b3_of_supMoment`, `coneRefMeas_of_supMoment` and
`exists_isQuantumCone_of_supMoment` (ConeArea5C) re-run with the Cauchy–Schwarz form
`ConeArea6.WPSupMomentH` of the whole-plane sup-moment bound, proved in ConeArea6D. The only change
is the choice of the moment exponent: `p = min (1/2) (gap/(2γ²))` instead of `min 1 (gap/γ²)`, so
that `b p + (γ²p² − p(2 + γ²/2)) = p(γ²p − gap) < 0`. Results:

* **`coneRefMeas'`**: `ConeRefMeas γ W` for `0 < γ < 2`, `W > 0`;
* **`exists_isQuantumCone'`**: quantum cones of every weight `W > 0` exist (DMS Def. 4.10), for `0 < γ < 2`;
* **`isQuantumCone_iff_unguarded`**: given the (open) non-Dirac property `ConeRefNonDirac γ W` of
  the reference law, both measurability guards of `IsQuantumCone` (MEAS-1) are redundant: the
  reference guard is `coneRefMeas'`, the sample guard follows from the law identity
  (`aemeasurable_surfMapC_of_surfLawC_eq`; in this mathlib `Measure.map` of a map that is not
  a.e.-measurable is a Dirac mass).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea6

open QuantumZipper LQGMetric ConeArea4 ConeArea5

/-- **weighted tightness at `0`** for a whole-plane GFF (as `ConeArea5.ae_tight_logFactor`) -/
theorem ae_tight_logFactor' {γ c : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hc : c < Qc γ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → Field}
    (hX : IsWholePlaneGFF X P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ᶠ k in atTop, (areaApproxC γ (X ω) k).withDensity
        (fun w => ENNReal.ofReal (AtomlessUncond.logFactorA γ c 0 k w)) (ball 0 δ) ≤
          ENNReal.ofReal ε := by
  set gap : ℝ := 2 + γ ^ 2 / 2 - max c 0 * γ with hgap
  have hgap0 : 0 < gap := by
    have hQ : Qc γ * γ = 2 + γ ^ 2 / 2 := by unfold Qc; field_simp
    rcases le_total c 0 with h | h
    · rw [hgap, max_eq_right h, zero_mul, sub_zero]; positivity
    · rw [hgap, max_eq_left h]; nlinarith
  have hγ2' : 0 < γ ^ 2 := by positivity
  set p : ℝ := min (1 / 2) (gap / (2 * γ ^ 2)) with hp
  have hp0 : 0 < p := lt_min (by norm_num) (div_pos hgap0 (by positivity))
  have hp1 : p ≤ 1 / 2 := min_le_left _ _
  have hp1' : p ≤ 1 := by linarith
  have hpg : 2 * (γ ^ 2 * p) ≤ gap := by
    have := min_le_right (1 / 2 : ℝ) (gap / (2 * γ ^ 2))
    rw [← hp, le_div_iff₀ (by positivity)] at this; linarith
  set b : ℝ := LogSing.expB (2 * γ) c with hb
  set e : ℝ := γ ^ 2 * p ^ 2 - p * (2 + γ ^ 2 / 2) with he
  have hneg : b * p + e < 0 := by
    have : b * p + e = p * (γ ^ 2 * p - gap) := by
      rw [hb, he, hgap, LogSing.expB]; ring
    rw [this]
    exact mul_neg_of_pos_of_neg hp0 (by linarith)
  obtain ⟨C, hC, n₀, hbd⟩ := wpSupMomentH hγ hγ2 Ω inferInstance P X inferInstance hX p hp0 hp1
  set T : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (Real.exp (-(γ * circleAvg (X ω) 1 0))) *
    AtomlessUncond.annTC (areaApproxC γ (X ω)) 0 n with hT
  have hTm : ∀ n, Measurable (T n) := fun n => by
    refine (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((measurable_circleAvg_left 1 0).comp hX.measurable).const_mul γ).neg)).mul ?_
    unfold AtomlessUncond.annTC
    exact Measurable.iSup fun j => (Measure.measurable_coe measurableSet_closedBall).comp
      ((ConeArea.measurable_areaApproxC γ (j + n)).comp hX.measurable)
  have hsum := AtomlessUncond.ae_tsum_ne_top_of_moments (P := P) hTm hp0 hp1' hneg hC
    (n₀ := n₀) fun n hn => hbd n hn
  filter_upwards [hsum] with ω ⟨N, hN⟩
  set a := γ * circleAvg (X ω) 1 0
  have h1 : ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp (-a)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      ENNReal.ofReal_one]
  have hsum' : ∑' n, LogSing.annW (2 * γ) c (n + N) *
      AtomlessUncond.annTC (areaApproxC γ (X ω)) 0 (n + N) ≠ ⊤ := by
    have e : ∀ n, LogSing.annW (2 * γ) c (n + N) *
        AtomlessUncond.annTC (areaApproxC γ (X ω)) 0 (n + N) =
        ENNReal.ofReal (Real.exp a) *
          (ENNReal.ofReal (radius (n + N + 1) ^ (-b)) * T (n + N) ω) := fun n => by
      simp only [hT, LogSing.annW, hb]
      calc _ = ENNReal.ofReal (radius (n + N + 1) ^ (-LogSing.expB (2 * γ) c)) *
            AtomlessUncond.annTC (areaApproxC γ (X ω)) 0 (n + N) *
              (ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp (-a))) := by
            rw [h1, mul_one]
        _ = _ := by ring
    simp_rw [e]
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN
  exact AtomlessUncond.tight_of_balls (γ := γ) (α := c) hγ (z := 0)
    (νX := fun k => areaApproxC γ (X ω) k)
    (νY := fun k => (areaApproxC γ (X ω) k).withDensity
      (fun w => ENNReal.ofReal (AtomlessUncond.logFactorA γ c 0 k w)))
    (K1 := 0) (M1 := 0) (fun _ _ _ _ => rfl) hsum'

/-- **Cone-area tightness (b3)**, unconditionally (as `ConeArea5.b3_of_supMoment`) -/
theorem b3' {γ W : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hW : 0 < W) :
    ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → Field)
      (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsWholePlaneGFF X P' →
      IsConeProcess (coneAlpha γ W) (Qc γ) A P' →
      IndepFun X (fun ω t => A t ω) P' →
      ∀ᵐ ω ∂P', ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ᶠ k in atTop, areaApproxC γ
          (coneField (lateralPartC (X ω)) (fun t => A t ω) (Qc γ)) k
            (Metric.ball 0 δ) ≤ ENNReal.ofReal ε := by
  intro Ω' _ P' X A hP hX hA _
  set α := coneAlpha γ W with hα
  have hαQ : α < Qc γ := by
    rw [hα, coneAlpha]; have : 0 < W / (2 * γ) := by positivity
    linarith
  set η := (Qc γ - α) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hc : α + η < Qc γ := by rw [hη]; linarith
  filter_upwards [ae_tight_logFactor' hγ hγ2 hc hX, ae_radial_R2 hX,
    ae_locallyIntegrable_coneProfile hA, ConeArea3.ae_hasCircleAvgs hX,
    (ConeMeas2.aemeasurable_conePath hA).2, ae_coneShift_le hX hA]
    with ω htight ⟨R, hRc, _, hxR, hRl⟩ hAl hcirc hAc hgrow
  obtain ⟨C, hC⟩ := hgrow R hRc hxR η hη0
  rw [ConeArea3.coneField_eq_add_ofFunC hxR hRl hAl]
  exact tight_add_ofFunC hγ one_pos hcirc (hAl.sub hRl)
    (ConeArea3.continuousOn_coneShift hAc _ hRc) hC htight

end ConeArea6
end MatedCRTHarmonic.MoTPort
