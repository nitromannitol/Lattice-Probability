/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.TemporalMassTransport at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TwoSidedStationaryLaw
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Measure

/-! # The temporal mass-transport identity from time-shift invariance

This file proves the *temporal* half of the manuscript lemma `p:lem:timeMTP`
("Temporal mass transport"): for a transport kernel `W (ω, s, t) ≥ 0` that is
covariant under time shifts,

```
  W (θ r ω) (s - r) (t - r) = W ω s t,
```

the **outgoing** and **incoming** transports agree,

```
  ∫ ∫_ℝ W ω 0 t dt dQ(ω) = ∫ ∫_ℝ W ω t 0 dt dQ(ω),
```

whenever the underlying trajectory measure `Q` is invariant under every
deterministic time shift `θ r`.  This is exactly the step of the manuscript
proof that reads

> "For each deterministic `t`, shift the sigma-finite measure
> `Q_H = ∑_v a_v P_H^v` by `t`.  The last expression equals
> `E_H^o ∫_ℝ V(Ω,-t,0) dt = E_H^o ∫_ℝ V(Ω,s,0) ds`.  Tonelli justifies all
> exchanges."

Scope, stated exactly.

* `Q` is **only** assumed σ-finite (`SFinite`), never a probability measure and
  never of finite total mass: the intended `Q` is the area-biased σ-finite path
  mixture `∑_v a_v P_H^v` of `p:eq:sigmapath`.  No finite total area, no
  annealed stationarity and no abstract stationary *probability* law is used.
* Time is integrated against an arbitrary σ-finite reflection-invariant measure
  `ν` on an arbitrary additive time group `T`; the manuscript case is
  `T = ℝ` with `ν = volume`, i.e. genuine integration over real time
  (`lintegral_timeMassTransport_real`, `integral_timeMassTransport_real`).
* Both the **nonnegative** clause (`ℝ≥0∞`-valued `W`, no integrability at all,
  Tonelli only) and the **signed** clause (real-valued `W`, with the exact
  integrability hypothesis `Integrable (fun p => W p.1 0 p.2) (Q.prod ν)`) are
  proved; the signed clause comes with the transfer
  `integrable_incoming_of_outgoing`, so the integrability needed on the
  incoming side is *not* an extra assumption but a consequence.
* The manuscript's convention "values at nonvertex source or target times can be
  set to zero" is not a hypothesis here: it is a property of the kernel `W`
  chosen by the consumer, and any such `W` is admissible as long as it is
  measurable and covariant.
* The parabolic scaling hypothesis `V(S_C Ω, C²s, C²t) = C^{-2} V(Ω,s,t)` of
  `p:lem:timeMTP` is **not** used here and is not assumed.  It is needed only
  for the *other* half of the manuscript proof, namely the passage from the
  fixed-environment identity proved here to the **annealed** identity, which
  goes through the spatial transport `T(H,w,z)` of `p:eq:spacefromtime` and the
  spatial mass-transport principle `p:eq:mtp`.  Nothing here claims the annealed
  statement.

Connection to the invariance producer.  The hypothesis
`∀ r, MeasurePreserving (θ r) Q Q` is precisely what
`ReflectedGMS.TwoSided.measurePreserving_twoSidedShiftBy_of_cylinderShift`
produces for the σ-finite weighted two-sided law `twoSidedGridLaw PF w δ`, for an
arbitrary (in particular non-summable, area-type) vertex weight `w`, from the
single finite-cylinder input `TwoSidedCylinderShiftIdentity PF w δ`.  The last
section of this file carries that instantiation out in full
(`lintegral_timeMassTransport_twoSidedGridLaw`,
`integral_timeMassTransport_twoSidedGridLaw`), with the time index the grid
`ℤ` and `ν = Measure.count`; the σ-finiteness of the mixture itself is proved
here (`sfinite_twoSidedGridLaw`) rather than assumed.  The remaining producer
for the actual area clock is unchanged and is the one named in
`SigmaFiniteTwoSidedShift`: the area-weighted finite-cylinder shift identity.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ReflectedGMS.TemporalMassTransport

/-- **Time-shift covariance** of a two-time transport kernel, as in
`p:lem:timeMTP`: shifting the trajectory by `r` and both times by `r` does not
change the transported mass. -/
def TimeShiftCovariant {Ω T α : Type*} [Sub T] (θ : T → Ω → Ω) (W : Ω → T → T → α) : Prop :=
  ∀ (r s t : T) (ω : Ω), W (θ r ω) (s - r) (t - r) = W ω s t

section AbstractTime

variable {Ω : Type*} [MeasurableSpace Ω] {T : Type*} [MeasurableSpace T] [AddGroup T]
  {α : Type*} [MeasurableSpace α]

/-- The outgoing integrand `(ω, t) ↦ W ω 0 t` of a measurable transport
kernel is measurable. -/
theorem measurable_outgoing (W : Ω → T → T → α)
    (hW : Measurable fun p : Ω × T × T => W p.1 p.2.1 p.2.2) :
    Measurable fun p : Ω × T => W p.1 0 p.2 :=
  hW.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))

/-- The incoming integrand `(ω, s) ↦ W ω s 0` of a measurable transport kernel
is measurable. -/
theorem measurable_incoming (W : Ω → T → T → α)
    (hW : Measurable fun p : Ω × T × T => W p.1 p.2.1 p.2.2) :
    Measurable fun p : Ω × T => W p.1 p.2 0 :=
  hW.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))

/-- The covariant reflection of a transport kernel, `W' ω s t = W ω t s`.  It is
again covariant, and its outgoing integrand is the incoming integrand of `W`;
this is what turns the one-sided transport identity into an equivalence. -/
theorem timeShiftCovariant_swap {θ : T → Ω → Ω} {W : Ω → T → T → α}
    (hcov : TimeShiftCovariant θ W) :
    TimeShiftCovariant θ (fun ω s t => W ω t s) :=
  fun r s t ω => hcov r t s ω

/-- **The temporal mass-transport identity, nonnegative form, on the product
measure.**  If the trajectory measure `Q` is invariant under every time shift
`θ r`, and the time measure `ν` is invariant under reflection, then a measurable
time-shift covariant kernel transports the same total mass out of time `0` as it
transports into time `0`.

No integrability, no finiteness of `Q` and no scaling hypothesis is used: this
is Tonelli plus the shift invariance, exactly as in the manuscript proof. -/
theorem lintegral_prod_timeTransport (Q : Measure Ω) [SFinite Q] (ν : Measure T) [SFinite ν]
    (θ : T → Ω → Ω) (W : Ω → T → T → ℝ≥0∞)
    (hW : Measurable fun p : Ω × T × T => W p.1 p.2.1 p.2.2)
    (hcov : TimeShiftCovariant θ W)
    (hθ : ∀ r : T, MeasurePreserving (θ r) Q Q)
    (hneg : MeasurePreserving (fun t : T => -t) ν ν) :
    ∫⁻ p : Ω × T, W p.1 0 p.2 ∂(Q.prod ν) = ∫⁻ p : Ω × T, W p.1 p.2 0 ∂(Q.prod ν) := by
  have hout : Measurable fun p : Ω × T => W p.1 0 p.2 := measurable_outgoing W hW
  have hin : Measurable fun p : Ω × T => W p.1 p.2 0 := measurable_incoming W hW
  have hslice : ∀ t : T, Measurable fun ω : Ω => W ω (-t) 0 := fun t =>
    hin.comp (measurable_id.prodMk (measurable_const : Measurable fun _ : Ω => (-t)))
  -- The shift by the target time `t` turns the outgoing integrand at time `t`
  -- into the incoming integrand at time `-t`.
  have hinner : ∀ t : T, ∫⁻ ω, W ω 0 t ∂Q = ∫⁻ ω, W ω (-t) 0 ∂Q := by
    intro t
    have hpt : ∀ ω : Ω, W ω 0 t = W (θ t ω) (-t) 0 := by
      intro ω
      have h := hcov t 0 t ω
      rw [zero_sub, sub_self] at h
      exact h.symm
    calc ∫⁻ ω, W ω 0 t ∂Q = ∫⁻ ω, W (θ t ω) (-t) 0 ∂Q := lintegral_congr hpt
      _ = ∫⁻ ω, W ω (-t) 0 ∂Q := (hθ t).lintegral_comp (hslice t)
  have hmeasIn : Measurable fun s : T => ∫⁻ ω, W ω s 0 ∂Q := hin.lintegral_prod_left'
  rw [lintegral_prod_symm _ hout.aemeasurable, lintegral_prod_symm _ hin.aemeasurable]
  calc ∫⁻ t, ∫⁻ ω, W ω 0 t ∂Q ∂ν
      = ∫⁻ t, (fun s : T => ∫⁻ ω, W ω s 0 ∂Q) (-t) ∂ν := lintegral_congr hinner
    _ = ∫⁻ s, ∫⁻ ω, W ω s 0 ∂Q ∂ν := hneg.lintegral_comp hmeasIn

/-- **The temporal mass-transport identity, nonnegative form, as iterated
integrals**: the trajectory average of the outgoing time integral equals the
trajectory average of the incoming time integral.  This is the exact shape of
`p:eq:timeMTP` for a fixed environment. -/
theorem lintegral_lintegral_timeTransport (Q : Measure Ω) [SFinite Q] (ν : Measure T) [SFinite ν]
    (θ : T → Ω → Ω) (W : Ω → T → T → ℝ≥0∞)
    (hW : Measurable fun p : Ω × T × T => W p.1 p.2.1 p.2.2)
    (hcov : TimeShiftCovariant θ W)
    (hθ : ∀ r : T, MeasurePreserving (θ r) Q Q)
    (hneg : MeasurePreserving (fun t : T => -t) ν ν) :
    ∫⁻ ω, ∫⁻ t, W ω 0 t ∂ν ∂Q = ∫⁻ ω, ∫⁻ t, W ω t 0 ∂ν ∂Q := by
  have hout : Measurable fun p : Ω × T => W p.1 0 p.2 := measurable_outgoing W hW
  have hin : Measurable fun p : Ω × T => W p.1 p.2 0 := measurable_incoming W hW
  rw [← lintegral_prod _ hout.aemeasurable, ← lintegral_prod _ hin.aemeasurable]
  exact lintegral_prod_timeTransport Q ν θ W hW hcov hθ hneg

/-! ### The signed clause

For a real-valued transport kernel the identity needs absolute convergence.  The
integrability hypothesis is imposed on the *outgoing* side only; the incoming
side is then automatically integrable, because the identity of the previous
section applies to `ENNReal.ofReal ‖W ω s t‖`. -/

end AbstractTime

/-! ## Real time

The manuscript statement integrates over real time.  Lebesgue measure on `ℝ` is
σ-finite and reflection invariant, so the general identity specializes. -/

section RealTime

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Lebesgue measure on the time line is invariant under time reversal. -/
theorem measurePreserving_neg_volume :
    MeasurePreserving (fun t : ℝ => -t) volume volume := by
  refine ⟨measurable_neg, ?_⟩
  have h := Real.map_volume_mul_left (a := (-1 : ℝ)) (by norm_num)
  simp only [neg_one_mul] at h
  rw [h]
  have habs : |((-1 : ℝ))⁻¹| = 1 := by norm_num
  rw [habs, ENNReal.ofReal_one, one_smul]

end RealTime

/-! ## The σ-finite two-sided grid law as an instance

The invariance premise of the identities above is produced, for the σ-finite
weighted two-sided law of an **arbitrary** vertex weight (in particular a
non-summable area weight), by
`ReflectedGMS.TwoSided.measurePreserving_twoSidedShiftBy_of_cylinderShift`.  Here
that producer is plugged in, so that the temporal transport identity holds for
the two-sided grid law under its single remaining finite-cylinder input.  The
time index is the grid `ℤ` and the time measure is the counting measure. -/

section TwoSidedGrid

open ReflectedWalk FullNetworkForm ReflectedGMS.TwoSided

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

end TwoSidedGrid

end ReflectedGMS.TemporalMassTransport

/-! ## Remaining mathematical gap

What is proved here is the fixed-environment (quenched) temporal identity
`p:eq:timeMTP`: outgoing and incoming transports through the time origin agree
for any measurable time-shift covariant kernel, once the trajectory measure is
σ-finite and time-shift invariant, with both the nonnegative and the signed
integrability clauses and with genuine integration over real time.

Two inputs of the manuscript lemma are deliberately *not* claimed:

* the shift invariance itself for the actual area clock, which reduces (by
  `ReflectedGMS.Temporal.SigmaFiniteTwoSidedShift`) to the area-weighted
  finite-cylinder shift identity `TwoSidedCylinderShiftIdentity PF (cellArea F) δ`,
  staffed separately;
* the passage from the fixed environment to the **annealed** law, which is the
  part of the manuscript proof that uses the spatial transport
  `T(H,w,z) = a_{H_z}^{-1} E_H^{H_w} ∫ 1_{X_t = H_z} V(Ω,0,t) dt` of
  `p:eq:spacefromtime`, its parabolic scaling degree `-2`, and the spatial
  mass-transport principle `p:eq:mtp`.  The parabolic scaling hypothesis of
  `p:lem:timeMTP` is used only there, which is why it does not appear above.
-/
