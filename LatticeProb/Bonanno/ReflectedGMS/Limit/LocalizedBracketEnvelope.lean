/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.LocalizedBracketEnvelope at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.LocalizingExit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! A bounded stopped bracket converts a measurable ucp error into the L¹
error required by the martingale-array tightness estimate. The original error
need not be integrable. The loss of linear drift after stopping is retained. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit
variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Clipping a nonnegative error that vanishes in probability gives an
integrable error with vanishing mean. No integrability of `E` is needed. -/
theorem clipped_error_integrable_and_mean_tendsto_zero
    {P : Measure Ω} [IsFiniteMeasure P] {E : ℕ → Ω → ℝ}
    (hEmeas : ∀ n, AEStronglyMeasurable (E n) P)
    (hE0 : ∀ n, ∀ᵐ ω ∂P, 0 ≤ E n ω)
    (hElim : TendstoInMeasure P E atTop (fun _ => 0))
    {C : ℝ} (hC : 0 ≤ C) :
    (∀ n, Integrable (fun ω => min (E n ω) C) P) ∧
      Tendsto (fun n => ∫ ω, min (E n ω) C ∂P) atTop (𝓝 0) := by
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun ω => min (E n ω) C) P :=
    (continuous_id.min continuous_const).comp_aestronglyMeasurable (hEmeas n)
  have hbound (n : ℕ) : ∀ᵐ ω ∂P, ‖min (E n ω) C‖ ≤ C := by
    filter_upwards [hE0 n] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hω hC)]
    exact min_le_right _ _
  refine ⟨fun n => Integrable.mono' (integrable_const C) (hmeas n) (hbound n), ?_⟩
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hms⟩ := (hElim.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hlim : ∀ᵐ ω ∂P,
      Tendsto (fun k => min (E (ns (ms k)) ω) C) atTop (𝓝 0) := by
    filter_upwards [hms] with ω hω
    simpa only [Function.comp_apply, min_eq_left hC] using hω.min (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C))
  simpa using tendsto_integral_of_dominated_convergence (fun _ : Ω => C)
    (fun k => hmeas (ns (ms k))) (integrable_const C)
    (fun k => hbound (ns (ms k))) hlim

/-- Exact pointwise localization estimate for mathlib's indicator-stopped
bracket. The exit term pays for `v t - v (t ∧ τ)`, including `τ = 0`. -/
theorem indicator_stopped_bracket_error_le_clipped_add_exit
    (B : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0)
    (T : ℝ≥0) {v K E : ℝ} (hv : 0 ≤ v) (hK : 0 ≤ K)
    (hE : 0 ≤ E) (ω : Ω)
    (herror : ∀ t ≤ T, |B t ω - v * (t : ℝ)| ≤ E)
    (hbound : ∀ t ≤ T,
      |stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (B s)) τ t ω| ≤ K)
    (t : ℝ≥0) (ht : t ≤ T) :
    |stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (B s)) τ t ω -
        v * (t : ℝ)| ≤
      min E (K + v * (T : ℝ)) +
        {ω | τ ω ≤ T}.indicator (fun _ => v * (T : ℝ)) ω := by
  let s : ℝ≥0 := (min (t : WithTop ℝ≥0) (τ ω)).untopA
  have hst : s ≤ t := WithTop.untopA_le (min_le_left _ _)
  have hsT : s ≤ T := hst.trans ht
  have hstR : (s : ℝ) ≤ t := by exact_mod_cast hst
  have htR : (t : ℝ) ≤ T := by exact_mod_cast ht
  have hsTR : (s : ℝ) ≤ T := by exact_mod_cast hsT
  have hC : 0 ≤ K + v * (T : ℝ) := add_nonneg hK (mul_nonneg hv T.2)
  by_cases hpos : ⊥ < τ ω
  · have heq : stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (B s)) τ t ω =
        B s ω := by
      exact Set.indicator_of_mem (show ω ∈ {ω | ⊥ < τ ω} from hpos) _
    have hb : |B s ω| ≤ K := by simpa only [heq] using hbound t ht
    have hlocal : |B s ω - v * (s : ℝ)| ≤ min E (K + v * (T : ℝ)) := by
      refine le_min (herror s hsT) ?_
      calc
        |B s ω - v * (s : ℝ)| ≤ |B s ω| + |v * (s : ℝ)| := abs_sub _ _
        _ ≤ K + v * (T : ℝ) := by
          rw [abs_of_nonneg (show 0 ≤ v * (s : ℝ) from mul_nonneg hv s.2)]
          exact add_le_add hb (mul_le_mul_of_nonneg_left hsTR hv)
    rw [heq]
    by_cases hexit : τ ω ≤ T
    · rw [Set.indicator_of_mem (show ω ∈ {ω | τ ω ≤ T} from hexit)]
      have hgap : |v * (s : ℝ) - v * (t : ℝ)| ≤ v * (T : ℝ) := by
        rw [abs_of_nonpos (sub_nonpos.mpr (mul_le_mul_of_nonneg_left hstR hv))]
        have hsnonneg : 0 ≤ v * (s : ℝ) := mul_nonneg hv s.2
        have htupper : v * (t : ℝ) ≤ v * (T : ℝ) :=
          mul_le_mul_of_nonneg_left htR hv
        linarith only [hsnonneg, htupper]
      calc
        |B s ω - v * (t : ℝ)| ≤
            |B s ω - v * (s : ℝ)| + |v * (s : ℝ) - v * (t : ℝ)| := abs_sub_le _ _ _
        _ ≤ _ := add_le_add hlocal hgap
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | τ ω ≤ T} from hexit), add_zero]
      have hτ : (t : WithTop ℝ≥0) ≤ τ ω :=
        (WithTop.coe_le_coe.mpr ht).trans (le_of_lt (lt_of_not_ge hexit))
      have hseq : s = t := by
        dsimp only [s]
        rw [min_eq_left hτ]
        rfl
      simpa only [hseq] using hlocal
  · have heq : stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (B s)) τ t ω = 0 :=
      Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < τ ω} from hpos) _
    have hτzero : τ ω = ⊥ := le_bot_iff.mp (not_lt.mp hpos)
    have hexit : τ ω ≤ T := by rw [hτzero]; exact bot_le
    rw [heq, Set.indicator_of_mem (show ω ∈ {ω | τ ω ≤ T} from hexit), zero_sub, abs_neg,
      abs_of_nonneg (show 0 ≤ v * (t : ℝ) from mul_nonneg hv t.2)]
    exact (mul_le_mul_of_nonneg_left htR hv).trans
      (le_add_of_nonneg_left (le_min hE hC))

/-- A bounded actual indicator-stopped bracket and rare exits produce all
three envelope inputs of `isTightMeasureSet_interpolated_martingale_laws`.
The ucp envelope `E` is only measurable and convergent in probability. -/
theorem exists_integrable_localized_bracket_error
    {P : Measure Ω} [IsFiniteMeasure P]
    {B : ℕ → ℝ≥0 → Ω → ℝ} {τ : ℕ → Ω → WithTop ℝ≥0}
    (T : ℝ≥0) {v K : ℝ} (hv : 0 ≤ v) (hK : 0 ≤ K)
    {E : ℕ → Ω → ℝ} (hEmeas : ∀ n, AEStronglyMeasurable (E n) P)
    (hE0 : ∀ n, ∀ᵐ ω ∂P, 0 ≤ E n ω)
    (hElim : TendstoInMeasure P E atTop (fun _ => 0))
    (herror : ∀ n, ∀ᵐ ω ∂P, ∀ t ≤ T, |B n t ω - v * (t : ℝ)| ≤ E n ω)
    (hbound : ∀ n, ∀ᵐ ω ∂P, ∀ t ≤ T,
      |stoppedProcess (fun s => {ω | ⊥ < τ n ω}.indicator (B n s)) (τ n) t ω| ≤ K)
    (hexitmeas : ∀ n, MeasurableSet {ω | τ n ω ≤ T})
    (hexit : Tendsto (fun n => P {ω | τ n ω ≤ T}) atTop (𝓝 0)) :
    ∃ R : ℕ → Ω → ℝ, (∀ n, Integrable (R n) P) ∧
      (∀ n, ∀ᵐ ω ∂P, ∀ t ≤ T,
        |stoppedProcess (fun s => {ω | ⊥ < τ n ω}.indicator (B n s)) (τ n) t ω -
          v * (t : ℝ)| ≤ R n ω) ∧
      Tendsto (fun n => ∫ ω, R n ω ∂P) atTop (𝓝 0) := by
  let R : ℕ → Ω → ℝ := fun n ω => min (E n ω) (K + v * (T : ℝ)) +
    {ω | τ n ω ≤ T}.indicator (fun _ => v * (T : ℝ)) ω
  obtain ⟨hint, hlim⟩ := clipped_error_integrable_and_mean_tendsto_zero
    (C := K + v * (T : ℝ)) hEmeas hE0 hElim (add_nonneg hK (mul_nonneg hv T.2))
  have hi (n : ℕ) : Integrable
      ({ω | τ n ω ≤ T}.indicator (fun _ => v * (T : ℝ))) P :=
    (integrable_const _).indicator (hexitmeas n)
  refine ⟨R, fun n => (hint n).add (hi n), ?_, ?_⟩
  · intro n
    filter_upwards [hE0 n, herror n, hbound n] with ω hω0 hωe hωb
    exact fun t ht => indicator_stopped_bracket_error_le_clipped_add_exit
      (B n) (τ n) T hv hK hω0 ω hωe hωb t ht
  · have hreal : Tendsto (fun n => (P {ω | τ n ω ≤ T}).toReal) atTop (𝓝 0) :=
      ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top P _) |>.mpr hexit
    have hiexit : Tendsto (fun n => ∫ ω,
        {ω | τ n ω ≤ T}.indicator (fun _ => v * (T : ℝ)) ω ∂P) atTop (𝓝 0) := by
      simpa only [integral_indicator_const _ (hexitmeas _), smul_eq_mul,
        measureReal_def, zero_mul] using hreal.mul_const (v * (T : ℝ))
    have hsum (n : ℕ) : (∫ ω, R n ω ∂P) =
        (∫ ω, min (E n ω) (K + v * (T : ℝ)) ∂P) +
        ∫ ω, {ω | τ n ω ≤ T}.indicator (fun _ => v * (T : ℝ)) ω ∂P :=
      integral_add (hint n) (hi n)
    simpa only [hsum, add_zero] using hlim.add hiexit

end ReflectedGMS.MartingaleLimit
