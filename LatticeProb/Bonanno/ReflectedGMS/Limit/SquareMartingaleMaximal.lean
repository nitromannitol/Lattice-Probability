/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.SquareMartingaleMaximal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.ContinuousTimeMaximal
import Mathlib.Probability.CondVar

/-!
The deterministic-horizon L² maximal inequality for real martingales. Squared
martingales are submartingales by mathlib's conditional-variance identity and
positivity of conditional expectation. Continuous time then uses the existing
strict-threshold maximal bound, with almost-sure cadlag paths only.
-/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A real martingale with finite second moments has a submartingale square.
The proof is the existing conditional-variance identity and its nonnegativity. -/
theorem martingale_square_submartingale {ι : Type*} [Preorder ι]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι m}
    {M : ι → Ω → ℝ} (hM : Martingale M F P)
    (h2 : ∀ t, MemLp (M t) 2 P) :
    Submartingale (fun t ω => (M t ω) ^ 2) F P := by
  refine ⟨fun t => (hM.stronglyMeasurable t).pow 2, ?_, fun t => (h2 t).integrable_sq⟩
  intro i j hij
  have hvar : 0 ≤ᵐ[P] condVar (F i) (M j) P := by
    unfold condVar
    exact condExp_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
  filter_upwards [hvar, condVar_ae_eq_condExp_sq_sub_sq_condExp (F.le i) (h2 j),
    hM.condExp_ae_eq hij] with ω hv he hm
  dsimp at hv he ⊢
  rw [hm] at he
  change (M i ω) ^ 2 ≤ P[M j ^ 2 | F i] ω
  exact sub_nonneg.mp (he ▸ hv)

/-- The continuous-time square maximal bound for an actual L² martingale. -/
theorem continuous_time_square_maximal
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) (h2 : ∀ t, MemLp (M t) 2 P)
    (hc : ∀ᵐ ω ∂P, IsCadlag (fun t => M t ω)) (T a : ℝ≥0) :
    a * P {ω | ∃ t ∈ Icc 0 T, (a : ℝ) < (M t ω) ^ 2} ≤
      ENNReal.ofReal (∫ ω, (M T ω) ^ 2 ∂P) := by
  have hc2 : ∀ᵐ ω ∂P, IsCadlag (fun t => (M t ω) ^ 2) :=
    hc.mono fun _ h => h.continuous_comp (continuous_pow 2)
  exact continuous_time_maximal_of_ae_cadlag (martingale_square_submartingale hM h2)
    (fun t ω => sq_nonneg _) hc2 T a

/-- The finite-horizon L² probability bound for strict exceedance of `|M|`.
No global path bound, completion, or continuous-path assumption is needed. -/
theorem continuous_time_abs_maximal
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) (h2 : ∀ t, MemLp (M t) 2 P)
    (hc : ∀ᵐ ω ∂P, IsCadlag (fun t => M t ω)) (T ε : ℝ≥0) :
    (ε : ℝ≥0∞) ^ 2 * P {ω | ∃ t ∈ Icc 0 T, (ε : ℝ) < |M t ω|} ≤
      ENNReal.ofReal (∫ ω, (M T ω) ^ 2 ∂P) := by
  have h := continuous_time_square_maximal hM h2 hc T (ε ^ 2)
  change (ε : ℝ≥0∞) ^ 2 * P {ω | ∃ t ∈ Icc 0 T,
    (ε : ℝ) ^ 2 < (M t ω) ^ 2} ≤ ENNReal.ofReal (∫ ω, (M T ω) ^ 2 ∂P) at h
  simpa only [sq_lt_sq, abs_of_nonneg ε.coe_nonneg] using h

end ReflectedGMS.MartingaleLimit
