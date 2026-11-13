/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.ParabolicTemporalTransport at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TemporalMassTransport

/-!
# The degree `-2` temporal mass transport as a predicate on a rooted law

`ReflectedGMS/Temporal/TemporalMassTransport.lean` proves the temporal mass-transport identity
of `p:lem:timeMTP` from **full stationarity** `∀ r, MeasurePreserving (θ r) Q Q` of the
trajectory measure, for every time-shift covariant kernel.  That is the right hypothesis for
the σ-finite fixed-environment measure `𝕢_H = ∑_v a_v ℙ_H^v` of `p:eq:sigmapath`.

For the **annealed rooted probability law** the manuscript never asserts stationarity under a
fixed deterministic time shift.  What it proves (tex:1360-1397) — from the spatial mass
transport `s:eq:MTP`, which is itself "mass transport modulo scaling" over degree `-2`
similarity-covariant kernels — is the identity

```
  𝔼 ∫_ℝ V(Ω,0,t) dt = 𝔼 ∫_ℝ V(Ω,t,0) dt
```

only for kernels `V` that are covariant under time shifts **and have parabolic scaling degree
`-2`**: `V(S_C Ω, C²s, C²t) = C^{-2} V(Ω,s,t)`.  Downstream, `p:lem:timeconditional`,
`p:lem:timeconverge` and `p:prop:timeergodic` are all stated for functionals invariant under
the parabolic scaling `S_C`, and the σ-fields `𝒢_m` include invariance under common scaling.

This module states that annealed identity as a predicate, `ParabolicTemporalTransport Q θ S`,
and derives from it the same signed clause and integrability transfer that
`TemporalMassTransport` derives from stationarity — for kernels that carry the extra degree
`-2` covariance.  It is the hypothesis that replaces `∀ r, MeasurePreserving (θ r) (P.prod ν)`
(`RootChainSystem.flowInvariant`, the old `hθP`) in the bracket lane; see
`Temporal/ScaledConditionalTemporalAveraging` and `Limit/ScaledRootChainSystem`.

## Why the weakening matters

Stationarity of the annealed law under a fixed shift `θ_r` is **not** a consequence of the
manuscript's hypotheses.  Its natural proof applies the spatial mass transport to the kernel
`T_r(H,w,z) = a_{H_z}^{-1} p_r(H_w,H_z) 𝔼_H^{H_z}[G ∣ X_{-r} = H_w]`, which is translation
covariant but has no parabolic homogeneity (the deterministic `r` fixes a time scale), so it
lies outside the degree `-2` class of `s:eq:Tcov`; and laws satisfying `s:eq:MTP` but not the
ordinary translation mass transport exist (scale-conditioned Palm laws of a genuinely
multi-scale similarity-invariant tiling measure), for which the root cell's area lies in a
window while `X_r` leaves it with positive probability, so `θ_r` cannot preserve the law.
`parabolicTemporalTransport_of_measurePreserving` shows the new predicate is implied by the
old hypothesis, so nothing already proved is lost.

## What is proved

* `ParabolicCovariant`, `ParabolicCovariantReal` — degree `-2` parabolic covariance of an
  `ℝ≥0∞`-, resp. `ℝ`-valued, two-time kernel under a scaling action `S : ℝ → Ω → Ω`.
* `ParabolicTemporalTransport Q θ S` — the annealed identity of `p:lem:timeMTP`, for all
  measurable kernels that are time-shift covariant and degree `-2` covariant.
* `parabolicTemporalTransport_of_measurePreserving` — stationarity implies it (so it is
  strictly no stronger than `hθP`), and `parabolicTemporalTransport_id` exhibits an inhabitant.
* `integrable_incoming_of_outgoing`, `integrable_outgoing_iff_incoming`,
  `integral_prod_timeTransport`, `integral_integral_timeTransport` — the signed clause and the
  integrability transfer, verbatim the ones of `TemporalMassTransport` with the stationarity
  hypothesis replaced by the predicate and the kernel's parabolic covariance.

Nothing here constructs the annealed law or proves the predicate for it; the manuscript's
producer is `p:lem:timeMTP` (fixed-environment half `TemporalMassTransport`, annealed half
`AnnealedTemporalTransport`).  Nothing here certifies `p:lem:timeconverge`,
`p:prop:timeergodic`, `p:lem:bracketlimit`, `p:thm:areaclt` or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.ParabolicTransport

open ReflectedGMS.TemporalMassTransport

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Parabolic covariance of degree `-2`** of a nonnegative two-time kernel under the scaling
action `S`: `W(S_C ω, C²s, C²t) = C^{-2} W(ω,s,t)` for every `C > 0` (`p:lem:timeMTP`). -/
def ParabolicCovariant (S : ℝ → Ω → Ω) (W : Ω → ℝ → ℝ → ℝ≥0∞) : Prop :=
  ∀ C : ℝ, 0 < C → ∀ (ω : Ω) (s t : ℝ),
    W (S C ω) (C ^ 2 * s) (C ^ 2 * t) = ENNReal.ofReal ((C ^ 2)⁻¹) * W ω s t

/-- The real-valued form of `ParabolicCovariant`. -/
def ParabolicCovariantReal (S : ℝ → Ω → Ω) (W : Ω → ℝ → ℝ → ℝ) : Prop :=
  ∀ C : ℝ, 0 < C → ∀ (ω : Ω) (s t : ℝ),
    W (S C ω) (C ^ 2 * s) (C ^ 2 * t) = (C ^ 2)⁻¹ * W ω s t

/-- **The annealed temporal mass transport of `p:lem:timeMTP`, as a predicate on a law.**
For every measurable kernel that is covariant under the time flow `θ` and has parabolic
degree `-2` under the scaling `S`, the outgoing and incoming transports through time `0` have
the same `Q`-average.  Stated on the product `Q ⊗ volume`; the iterated form follows by
Tonelli.  Nothing is asserted about `Q` beyond this identity: in particular no invariance of
`Q` under any fixed time shift. -/
def ParabolicTemporalTransport (Q : Measure Ω) (θ S : ℝ → Ω → Ω) : Prop :=
  ∀ W : Ω → ℝ → ℝ → ℝ≥0∞, Measurable (fun p : Ω × ℝ × ℝ => W p.1 p.2.1 p.2.2) →
    TimeShiftCovariant θ W → ParabolicCovariant S W →
    ∫⁻ p : Ω × ℝ, W p.1 0 p.2 ∂(Q.prod volume) = ∫⁻ p : Ω × ℝ, W p.1 p.2 0 ∂(Q.prod volume)

/-! ### Covariance bookkeeping for the signed clause -/

omit [MeasurableSpace Ω] in
theorem parabolicCovariantReal_swap {S : ℝ → Ω → Ω} {W : Ω → ℝ → ℝ → ℝ}
    (h : ParabolicCovariantReal S W) : ParabolicCovariantReal S (fun ω s t => W ω t s) :=
  fun C hC ω s t => h C hC ω t s

omit [MeasurableSpace Ω] in
theorem parabolicCovariant_ofReal_norm {S : ℝ → Ω → Ω} {W : Ω → ℝ → ℝ → ℝ}
    (h : ParabolicCovariantReal S W) :
    ParabolicCovariant S (fun ω s t => ENNReal.ofReal ‖W ω s t‖) := by
  intro C hC ω s t
  have hnn : (0 : ℝ) ≤ (C ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg C)
  show ENNReal.ofReal ‖W (S C ω) (C ^ 2 * s) (C ^ 2 * t)‖
    = ENNReal.ofReal ((C ^ 2)⁻¹) * ENNReal.ofReal ‖W ω s t‖
  rw [h C hC ω s t, norm_mul, Real.norm_of_nonneg hnn, ENNReal.ofReal_mul hnn]

omit [MeasurableSpace Ω] in
theorem parabolicCovariant_ofReal {S : ℝ → Ω → Ω} {W : Ω → ℝ → ℝ → ℝ}
    (h : ParabolicCovariantReal S W) :
    ParabolicCovariant S (fun ω s t => ENNReal.ofReal (W ω s t)) := by
  intro C hC ω s t
  have hnn : (0 : ℝ) ≤ (C ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg C)
  show ENNReal.ofReal (W (S C ω) (C ^ 2 * s) (C ^ 2 * t))
    = ENNReal.ofReal ((C ^ 2)⁻¹) * ENNReal.ofReal (W ω s t)
  rw [h C hC ω s t, ENNReal.ofReal_mul hnn]

omit [MeasurableSpace Ω] in
theorem parabolicCovariant_ofReal_neg {S : ℝ → Ω → Ω} {W : Ω → ℝ → ℝ → ℝ}
    (h : ParabolicCovariantReal S W) :
    ParabolicCovariant S (fun ω s t => ENNReal.ofReal (-(W ω s t))) := by
  intro C hC ω s t
  have hnn : (0 : ℝ) ≤ (C ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg C)
  show ENNReal.ofReal (-(W (S C ω) (C ^ 2 * s) (C ^ 2 * t)))
    = ENNReal.ofReal ((C ^ 2)⁻¹) * ENNReal.ofReal (-(W ω s t))
  rw [h C hC ω s t, ← mul_neg, ENNReal.ofReal_mul hnn]

/-! ### The signed clause -/

section Signed

variable {Q : Measure Ω} {θ S : ℝ → Ω → Ω}

/-- Transfer of finite total mass from the outgoing to the incoming side, for a degree `-2`
covariant kernel, from the annealed transport identity alone. -/
theorem hasFiniteIntegral_incoming_of_outgoing (htr : ParabolicTemporalTransport Q θ S)
    (W : Ω → ℝ → ℝ → ℝ) (hW : Measurable fun p : Ω × ℝ × ℝ => W p.1 p.2.1 p.2.2)
    (hcov : TimeShiftCovariant θ W) (hpar : ParabolicCovariantReal S W)
    (h : HasFiniteIntegral (fun p : Ω × ℝ => W p.1 0 p.2) (Q.prod volume)) :
    HasFiniteIntegral (fun p : Ω × ℝ => W p.1 p.2 0) (Q.prod volume) := by
  have hcore := htr (fun ω s t => ENNReal.ofReal ‖W ω s t‖) hW.norm.ennreal_ofReal
    (fun r s t ω => congrArg (fun x : ℝ => ENNReal.ofReal ‖x‖) (hcov r s t ω))
    (parabolicCovariant_ofReal_norm hpar)
  rw [hasFiniteIntegral_iff_norm] at h
  have h' : ∫⁻ p : Ω × ℝ, ENNReal.ofReal ‖W p.1 p.2 0‖ ∂(Q.prod volume) < ∞ := by
    rw [← hcore]
    exact h
  rw [hasFiniteIntegral_iff_norm]
  exact h'

/-- The incoming transport of an integrable outgoing transport is integrable. -/
theorem integrable_incoming_of_outgoing (htr : ParabolicTemporalTransport Q θ S)
    (W : Ω → ℝ → ℝ → ℝ) (hW : Measurable fun p : Ω × ℝ × ℝ => W p.1 p.2.1 p.2.2)
    (hcov : TimeShiftCovariant θ W) (hpar : ParabolicCovariantReal S W)
    (hint : Integrable (fun p : Ω × ℝ => W p.1 0 p.2) (Q.prod volume)) :
    Integrable (fun p : Ω × ℝ => W p.1 p.2 0) (Q.prod volume) :=
  ⟨(measurable_incoming W hW).aestronglyMeasurable,
    hasFiniteIntegral_incoming_of_outgoing htr W hW hcov hpar hint.2⟩

/-- Integrability of the outgoing and of the incoming transport are equivalent. -/
theorem integrable_outgoing_iff_incoming (htr : ParabolicTemporalTransport Q θ S)
    (W : Ω → ℝ → ℝ → ℝ) (hW : Measurable fun p : Ω × ℝ × ℝ => W p.1 p.2.1 p.2.2)
    (hcov : TimeShiftCovariant θ W) (hpar : ParabolicCovariantReal S W) :
    Integrable (fun p : Ω × ℝ => W p.1 0 p.2) (Q.prod volume) ↔
      Integrable (fun p : Ω × ℝ => W p.1 p.2 0) (Q.prod volume) := by
  have hWswap : Measurable fun p : Ω × ℝ × ℝ => (fun ω s t => W ω t s) p.1 p.2.1 p.2.2 :=
    hW.comp (measurable_fst.prodMk (measurable_snd.snd.prodMk measurable_snd.fst))
  constructor
  · exact integrable_incoming_of_outgoing htr W hW hcov hpar
  · exact integrable_incoming_of_outgoing htr (fun ω s t => W ω t s) hWswap
      (timeShiftCovariant_swap hcov) (parabolicCovariantReal_swap hpar)

/-- **The annealed temporal mass-transport identity, signed form, on the product measure**,
for a degree `-2` covariant kernel with integrable outgoing transport. -/
theorem integral_prod_timeTransport [SFinite Q] (htr : ParabolicTemporalTransport Q θ S)
    (W : Ω → ℝ → ℝ → ℝ) (hW : Measurable fun p : Ω × ℝ × ℝ => W p.1 p.2.1 p.2.2)
    (hcov : TimeShiftCovariant θ W) (hpar : ParabolicCovariantReal S W)
    (hint : Integrable (fun p : Ω × ℝ => W p.1 0 p.2) (Q.prod volume)) :
    ∫ p : Ω × ℝ, W p.1 0 p.2 ∂(Q.prod volume) = ∫ p : Ω × ℝ, W p.1 p.2 0 ∂(Q.prod volume) := by
  have hint' : Integrable (fun p : Ω × ℝ => W p.1 p.2 0) (Q.prod volume) :=
    integrable_incoming_of_outgoing htr W hW hcov hpar hint
  have hpos := htr (fun ω s t => ENNReal.ofReal (W ω s t)) hW.ennreal_ofReal
    (fun r s t ω => congrArg (fun x : ℝ => ENNReal.ofReal x) (hcov r s t ω))
    (parabolicCovariant_ofReal hpar)
  have hnegpart := htr (fun ω s t => ENNReal.ofReal (-(W ω s t))) hW.neg.ennreal_ofReal
    (fun r s t ω => congrArg (fun x : ℝ => ENNReal.ofReal (-x)) (hcov r s t ω))
    (parabolicCovariant_ofReal_neg hpar)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint']
  congr 1
  · exact congrArg ENNReal.toReal hpos
  · exact congrArg ENNReal.toReal hnegpart

/-- **The annealed temporal mass-transport identity, signed form, as iterated integrals**:
`p:eq:timeMTP` for a signed degree `-2` kernel, from the predicate alone. -/
theorem integral_integral_timeTransport [SFinite Q] (htr : ParabolicTemporalTransport Q θ S)
    (W : Ω → ℝ → ℝ → ℝ) (hW : Measurable fun p : Ω × ℝ × ℝ => W p.1 p.2.1 p.2.2)
    (hcov : TimeShiftCovariant θ W) (hpar : ParabolicCovariantReal S W)
    (hint : Integrable (fun p : Ω × ℝ => W p.1 0 p.2) (Q.prod volume)) :
    ∫ ω, ∫ t, W ω 0 t ∂(volume : Measure ℝ) ∂Q =
      ∫ ω, ∫ t, W ω t 0 ∂(volume : Measure ℝ) ∂Q := by
  have hint' : Integrable (fun p : Ω × ℝ => W p.1 p.2 0) (Q.prod volume) :=
    integrable_incoming_of_outgoing htr W hW hcov hpar hint
  have hout : Integrable (Function.uncurry fun (ω : Ω) (t : ℝ) => W ω 0 t) (Q.prod volume) :=
    hint
  have hin : Integrable (Function.uncurry fun (ω : Ω) (t : ℝ) => W ω t 0) (Q.prod volume) :=
    hint'
  rw [integral_integral hout, integral_integral hin]
  exact integral_prod_timeTransport htr W hW hcov hpar hint

end Signed

end ReflectedGMS.ParabolicTransport
