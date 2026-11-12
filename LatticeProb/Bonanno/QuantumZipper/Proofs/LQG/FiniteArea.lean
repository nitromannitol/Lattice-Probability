/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.FiniteArea at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.FractionalMoments
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceAS
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSample

/-!
# M4-A3: fractional moments of the area measure near `ℝ` and finiteness of `μ(B(0,a) ∩ ℍ)`

Blueprint `M4_BLUEPRINT.md`, nodes M4-P3 (area version at boundary points) and M4-A3.

Fix `t ∈ ℝ`, `δ > 0` with `|t| + δ ≤ R`. As in `FractionalMoments` (boundary case) we split the
normalized field `Z = aZ X R` inside `B(t, δ)` as `Z_ρ(z) = Ω + Y_ρ(z)`, with
`Ω = Z(fc(t,δ))` and `Y` the (complex-centred) inner field, independent of `Ω`. For a set
`K ⊆ ℍ` with `Im z ≥ d` and `‖z − t‖ + 2^{-k} < δ` on `K`:

* `areaApprox_eq_omega_mul`: `μ_{2^{-k}}(K) = e^{γΩ} δ^{γ²/2} W_k(K)` a.s., with `W_k` a function
  of the inner field and `E W_k ≤ (δ/2d)^{γ²/2} |K|` (`lintegral_innerMassC_le`);
* (1) `lintegral_areaApprox_rpow_le`:
  `E μ_{2^{-k}}(K)^p ≤ δ^{pγ²/2} e^{(2 log R − 2 log δ)(pγ)²/2} ((δ/2d)^{γ²/2} |K|)^p`, and
  `lintegral_qAreaMeasure_rpow_le` the same for the limit `μ = qAreaMeasure` on open `U ⊆ K`
  (Fatou);
* (2) `ae_qAreaMeasure_ball_lt_top`: a.s. `μ_X(B(0,a) ∩ ℍ) < ∞` for every `a`;
* (3) `ae_qAreaMeasure_add_ofFun_ball_lt_top`: the same for `X + ofFun φ`, `φ` continuous on
  `Hbar`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace FinArea

open GaussTK TwoRadius KernelId

/-! ### Kernel identities for an interior circle inside a real-centred semicircle -/

/-! ### The complex inner field -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-! ### Covariances and laws -/

/-! ### Masses and the decomposition -/

/-! ### Fatou: the limit measure on open sets -/

/-- Test functions `min 1 (n · dist(z, Uᶜ))`, increasing to `1_U`. -/
def ramp (U : Set ℂ) (n : ℕ) (z : ℂ) : ℝ := min 1 (n * Metric.infDist z Uᶜ)

theorem continuous_ramp (U : Set ℂ) (n : ℕ) : Continuous (ramp U n) :=
  continuous_const.min (continuous_const.mul (Metric.continuous_infDist_pt _))

theorem ramp_nonneg (U : Set ℂ) (n : ℕ) (z : ℂ) : 0 ≤ ramp U n z :=
  le_min zero_le_one (mul_nonneg n.cast_nonneg Metric.infDist_nonneg)

theorem ramp_le_one (U : Set ℂ) (n : ℕ) (z : ℂ) : ramp U n z ≤ 1 := min_le_left _ _

theorem ramp_eq_zero {U : Set ℂ} (n : ℕ) {z : ℂ} (hz : z ∉ U) : ramp U n z = 0 := by
  unfold ramp
  rw [Metric.infDist_zero_of_mem (Set.mem_compl hz), mul_zero, min_eq_right zero_le_one]

theorem ramp_mono (U : Set ℂ) (z : ℂ) : Monotone fun n : ℕ => ramp U n z := fun n n' h =>
  min_le_min le_rfl (mul_le_mul_of_nonneg_right (by exact_mod_cast h) Metric.infDist_nonneg)

theorem exists_ramp_eq_one {U : Set ℂ} (hU : IsOpen U) (hne : Uᶜ.Nonempty) {z : ℂ}
    (hz : z ∈ U) : ∃ n : ℕ, ramp U n z = 1 := by
  have hpos : 0 < Metric.infDist z Uᶜ :=
    (hU.isClosed_compl.notMem_iff_infDist_pos hne).1 (Set.notMem_compl_iff.2 hz)
  obtain ⟨n, hn⟩ := exists_nat_ge (1 / Metric.infDist z Uᶜ)
  refine ⟨n, min_eq_left ?_⟩
  rw [div_le_iff₀ hpos] at hn
  linarith

/-- **Portmanteau (liminf form).** For a vague limit on `ℍ`, `U` open and `U ⊆ K ⊆ ℍ` with
`K` compact: `μ(U)^p ≤ liminf_k μ_k(K)^p`. -/
theorem rpow_le_liminf_of_isVagueLimitOn {μs : ℕ → Measure ℂ} {μ : Measure ℂ}
    (h : IsVagueLimitOn H μs μ) {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K)
    (hUK : U ⊆ K) (hKH : K ⊆ H) {p : ℝ} (hp : 0 < p) :
    μ U ^ p ≤ liminf (fun k => μs k K ^ p) atTop := by
  have hne : Uᶜ.Nonempty := ⟨0, fun h0 => by
    have := hKH (hUK h0)
    simp [H] at this⟩
  have hts : ∀ n, tsupport (ramp U n) ⊆ K := fun n =>
    closure_minimal (fun z hz => hUK (by by_contra hc; exact hz (ramp_eq_zero n hc)))
      hK.isClosed
  have hcs : ∀ n, HasCompactSupport (ramp U n) := fun n =>
    HasCompactSupport.intro hK fun z hz => ramp_eq_zero n fun h => hz (hUK h)
  set a : ℕ → ℝ≥0∞ := fun n => ∫⁻ z, ENNReal.ofReal (ramp U n z) ∂μ with ha
  have hamono : Monotone a := fun n n' h =>
    lintegral_mono fun z => ENNReal.ofReal_le_ofReal (ramp_mono U z h)
  have hsup : ⨆ n, a n = μ U := by
    show ⨆ n, ∫⁻ z, ENNReal.ofReal (ramp U n z) ∂μ = μ U
    rw [← lintegral_iSup (f := fun n z => ENNReal.ofReal (ramp U n z))
      (fun n => ENNReal.measurable_ofReal.comp (continuous_ramp U n).measurable)
      (fun n n' h z => ENNReal.ofReal_le_ofReal (ramp_mono U z h)),
      ← lintegral_indicator_one hU.measurableSet]
    congr 1
    funext z
    by_cases hz : z ∈ U
    · rw [Set.indicator_of_mem hz, Pi.one_apply]
      obtain ⟨n, hn⟩ := exists_ramp_eq_one hU hne hz
      refine le_antisymm (iSup_le fun m => ENNReal.ofReal_le_one.2 (ramp_le_one U m z)) ?_
      exact (le_iSup (fun m => ENNReal.ofReal (ramp U m z)) n).trans' (by simp [hn])
    · rw [Set.indicator_of_notMem hz]
      have h0 : ∀ m, ramp U m z = 0 := fun m => ramp_eq_zero m hz
      simp [h0]
  have hbound : ∀ n, a n ^ p ≤ liminf (fun k => μs k K ^ p) atTop := by
    intro n
    have hint : Integrable (ramp U n) μ :=
      GoodSample.integrable_of_tsupport (U := H) h.2.1 (continuous_ramp U n) (hcs n)
        ((hts n).trans hKH)
    have han : a n = ENNReal.ofReal (∫ z, ramp U n z ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (ramp_nonneg U n))).symm
    have ht : Tendsto (fun k => ENNReal.ofReal (∫ z, ramp U n z ∂μs k) ^ p) atTop
        (𝓝 (ENNReal.ofReal (∫ z, ramp U n z ∂μ) ^ p)) :=
      ((ENNReal.continuous_rpow_const (y := p)).tendsto _).comp
        (ENNReal.tendsto_ofReal (h.2.2 _ (continuous_ramp U n) (hcs n) ((hts n).trans hKH)))
    rw [han, ← ht.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun k => ?_)
    show ENNReal.ofReal (∫ z, ramp U n z ∂μs k) ^ p ≤ μs k K ^ p
    refine ENNReal.rpow_le_rpow ?_ hp.le
    by_cases hi : Integrable (ramp U n) (μs k)
    · rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (ramp_nonneg U n))]
      calc ∫⁻ z, ENNReal.ofReal (ramp U n z) ∂μs k ≤ ∫⁻ z, K.indicator 1 z ∂μs k :=
            lintegral_mono fun z => by
              by_cases hz : z ∈ K
              · rw [Set.indicator_of_mem hz, Pi.one_apply]
                exact ENNReal.ofReal_le_one.2 (ramp_le_one U n z)
              · rw [ramp_eq_zero n fun h => hz (hUK h), ENNReal.ofReal_zero]; exact bot_le
        _ = μs k K := lintegral_indicator_one hK.isClosed.measurableSet
    · rw [integral_undef hi, ENNReal.ofReal_zero]; exact bot_le
  have hT : Tendsto (fun n => a n ^ p) atTop (𝓝 (μ U ^ p)) := by
    rw [← hsup]
    exact ((ENNReal.continuous_rpow_const (y := p)).tendsto _).comp (tendsto_atTop_iSup hamono)
  exact le_of_tendsto' hT hbound

/-! ### (2) Finite area up to `ℝ` -/

/-! ### (3) Adding a continuous function -/

section OfFun

open GoodSample RegClosure CircleFubini

end OfFun

end FinArea
end QuantumZipper
