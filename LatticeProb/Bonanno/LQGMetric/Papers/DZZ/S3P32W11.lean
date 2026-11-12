/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32W11 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W10
import Mathlib.Probability.Martingale.OptionalStopping

/-!
# D97, packet P-1: Doob's maximal inequality for the approximations of `M^W`

For a Borel set `E` of finite area, `X_n = wickMeas_n(E)` is a nonnegative martingale for the
white-noise filtration (`setLIntegral_wickMeas_eq`) with `E X_n = Leb(E)`. Hence (Doob,
`MeasureTheory.maximal_ineq`):

* **`measure_exists_wickMeas_gt`**: `ε · P(∃ n, X_n > ε) ≤ Leb(E)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper GMCIdent GMCIdent3 GMCIdent4 GMCIdent5

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {W : WNSpace → Ω' → ℝ}

lemma measurable_wickMeas_fil (hW : IsWhiteNoise P' W) (γ : ℝ) (n : ℕ) {E : Set ℂ}
    (hE : MeasurableSet E) : Measurable[wnFil hW n] fun ω => wickMeas W γ n ω E := by
  have hm := measurable_tildeVer hW n
  have hw := measurable_wnWeight hW γ n
  have hr := measurable_wickR γ
  simp_rw [wickMeas, withDensity_apply _ hE]
  let _ : MeasurableSpace Ω' := wnFil hW n
  have hj : Measurable fun p : Ω' × ℂ => ENNReal.ofReal (wickR γ p.2 * wnDens W γ n p.2 p.1) :=
    ENNReal.measurable_ofReal.comp ((hr.comp measurable_snd).mul ((hw.comp measurable_snd).mul
      (Real.measurable_exp.comp ((hm.comp measurable_swap).const_mul γ))))
  exact hj.lintegral_prod_right'

lemma measurable_wickMeas_apply (hW : IsWhiteNoise P' W) (γ : ℝ) (n : ℕ) {E : Set ℂ}
    (hE : MeasurableSet E) : Measurable fun ω => wickMeas W γ n ω E :=
  (measurable_wickMeas_fil hW γ n hE).mono (wnSigma_le hW _) le_rfl

lemma lintegral_wickMeas (hW : IsWhiteNoise P' W) (γ : ℝ) (n : ℕ) {E : Set ℂ}
    (hE : MeasurableSet E) : ∫⁻ ω, wickMeas W γ n ω E ∂P' = volume E := by
  rw [← lintegral_wickMeasC hW γ n hE]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_wickMeas_eq_wickMeasC hW γ] with ω h
  rw [h n]

/-- the real-valued process `X_n = wickMeas_n(E)` -/
def wickProc (W : WNSpace → Ω' → ℝ) (γ : ℝ) (E : Set ℂ) (n : ℕ) (ω : Ω') : ℝ :=
  (wickMeas W γ n ω E).toReal

theorem submartingale_wickProc (hW : IsWhiteNoise P' W) (γ : ℝ) {E : Set ℂ}
    (hE : MeasurableSet E) (hEf : volume E ≠ ⊤) :
    Submartingale (wickProc W γ E) (wnFil hW) P' := by
  have hP := hW.isProbabilityMeasure
  have hfin : ∀ n, ∀ᵐ ω ∂P', wickMeas W γ n ω E < ⊤ := fun n =>
    ae_lt_top (measurable_wickMeas_apply hW γ n hE) (by rw [lintegral_wickMeas hW γ n hE]; exact hEf)
  refine submartingale_of_setIntegral_le
    (fun n => (measurable_wickMeas_fil hW γ n hE).ennreal_toReal.stronglyMeasurable)
    (fun n => integrable_toReal_of_lintegral_ne_top
      (measurable_wickMeas_apply hW γ n hE).aemeasurable
      (by rw [lintegral_wickMeas hW γ n hE]; exact hEf)) (fun i j hij s hs => ?_)
  simp only [wickProc]
  rw [integral_toReal (measurable_wickMeas_apply hW γ i hE).aemeasurable
      (ae_restrict_of_ae (hfin i)),
    integral_toReal (measurable_wickMeas_apply hW γ j hE).aemeasurable
      (ae_restrict_of_ae (hfin j)), setLIntegral_wickMeas_eq hW γ hij hs hE]

/-- **Doob's maximal inequality** for `X_n = wickMeas_n(E)`. -/
theorem measure_exists_wickMeas_gt (hW : IsWhiteNoise P' W) (γ : ℝ) {E : Set ℂ}
    (hE : MeasurableSet E) (hEf : volume E ≠ ⊤) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * P' {ω | ∃ n, (ε : ℝ) < wickProc W γ E n ω} ≤ volume E := by
  have hP := hW.isProbabilityMeasure
  have hsub := submartingale_wickProc hW γ hE hEf
  have hnn : 0 ≤ wickProc W γ E := fun n ω => ENNReal.toReal_nonneg
  set S : ℕ → Set Ω' := fun N => {ω | (ε : ℝ) ≤
    (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one fun k => wickProc W γ E k ω}
  have hS : {ω | ∃ n, (ε : ℝ) < wickProc W γ E n ω} ⊆ ⋃ N, S N := by
    rintro ω ⟨n, hn⟩
    exact mem_iUnion.2 ⟨n, hn.le.trans (Finset.le_sup' (fun k => wickProc W γ E k ω)
      (Finset.self_mem_range_succ n))⟩
  have hmono : Monotone S := fun N N' h ω hω => by
    simp only [S, mem_ofPred_eq] at hω ⊢
    exact hω.trans (Finset.sup'_mono _ (Finset.range_mono (Nat.succ_le_succ h)) _)
  have hint : ∀ N, Integrable (wickProc W γ E N) P' := fun N => hsub.integrable N
  calc (ε : ℝ≥0∞) * P' {ω | ∃ n, (ε : ℝ) < wickProc W γ E n ω}
      ≤ (ε : ℝ≥0∞) * P' (⋃ N, S N) := by gcongr
    _ = ⨆ N, (ε : ℝ≥0∞) * P' (S N) := by rw [hmono.measure_iUnion, ENNReal.mul_iSup]
    _ ≤ volume E := iSup_le fun N => by
        refine (maximal_ineq hsub hnn N).trans ?_
        calc ENNReal.ofReal (∫ ω in S N, wickProc W γ E N ω ∂P')
            ≤ ENNReal.ofReal (∫ ω, wickProc W γ E N ω ∂P') :=
              ENNReal.ofReal_le_ofReal (setIntegral_le_integral (hint N)
                (Eventually.of_forall fun ω => hnn N ω))
          _ = volume E := by
              simp only [wickProc]
              rw [integral_toReal (measurable_wickMeas_apply hW γ N hE).aemeasurable
                (ae_lt_top (measurable_wickMeas_apply hW γ N hE)
                  (by rw [lintegral_wickMeas hW γ N hE]; exact hEf)),
                lintegral_wickMeas hW γ N hE, ENNReal.ofReal_toReal hEf]

end DZZ
end LQGMetric
