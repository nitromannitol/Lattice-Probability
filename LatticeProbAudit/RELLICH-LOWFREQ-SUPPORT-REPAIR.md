# The low-frequency net residual is too strong

Audit of `LatticeProb/Analysis/Sobolev/SupportRepair.lean` and
`LatticeProb/Analysis/Sobolev/SupportProducer.lean` (branch `ds-rellich-freqtrunc`).

## Summary

`BandLimitedTestFnApproxOnDomain` (`SupportRepair.lean:46`) is **false as stated**, because a
nonzero band-limited function is never `H^{s₀}`-close to a test function on a fixed bounded domain.
The same obstruction refutes the support-repair half `BandCentreSupportRepair`
(`SupportProducer.lean:50`).  Consequently the two inputs of
`bandLimitedTestFnApproxOnDomain_of_jetNet_and_supportRepair` cannot both be discharged, and the
jet-net route to `rellichKondrachovNegSobolev_of_jetNet_and_supportRepair` is blocked at the
residual.

## The obstruction

Write `H^{s₀}_0(D) ⊆ H^{s₀}(ℝ^d)` for the closure of `C_c^∞(D)`.  A test function `ψ` on `D` has
`support ψ ⊆ tsupport ψ ⊆ D`, so `ψ = 0` off `D`; hence every `ψ ∈ C_c^∞(D)` lies in
`H^{s₀}_0(D)`, and — `D` being bounded — one has `H^{s₀}_0(D) = {f : support f ⊆ closure D}`.

Fix a test function `φ` on `D` with `φ ≠ 0` and `0 < Λ`.  The projection `bandProj d Λ … φ` is
band-limited: its Fourier transform is supported in `‖ξ‖ ≤ 2Λ`
(`fourier_bandTrunc_real_eq_zero`).  A nonzero band-limited function is the restriction of an
entire function of exponential type; if it vanished on `Dᶜ` (a nonempty open set, as `D` is
bounded) it would vanish identically, contradicting `φ ≠ 0`.  So
`support (bandProj φ) ⊄ closure D`, i.e.

```
ρ := dist_{H^{s₀}}(bandProj φ, H^{s₀}_0(D)) > 0.
```

Since `sobolevNormSq` is the square of the `H^{s₀}` norm,

```
sobolevNormSq d s₀ (bandProj φ - ψ) ≥ ρ² > 0     for every test function ψ on D.
```

Taking `δ < ρ²` refutes the existential of `BandLimitedTestFnApproxOnDomain` (`SupportRepair.lean`
lines 46–53) at this `φ`, hence the `Prop` itself is false.

## Consequences

* `BandCentreSupportRepair` (`SupportProducer.lean:50`) is false for the same reason: it is
  universally quantified in `g`, and any integrable `g` with mass off `D` — for instance the
  band-limited centre `bandProj φ` that `BandLimitedProjectionNet` is forced to supply — cannot be
  approximated by a test function on `D`, since the latter vanishes on `Dᶜ`.
* `bandLimitedTestFnApproxOnDomain_of_jetNet_and_supportRepair` (`SupportProducer.lean:77`) and its
  consumers `rkLowFreqNet_of_jetNet_and_supportRepair` and
  `rellichKondrachovNegSobolev_of_jetNet_and_supportRepair` rest on a hypothesis that cannot be
  discharged.  The theorems remain sound to state (they are conditional), but the chain cannot be
  completed through this residual.
* `BandLimitedProjectionNet` (`SupportProducer.lean:37`) is **not** obviously false: it asks only
  for *integrable* centres `g i` (e.g. band-limited ones) `H^{s₀}`-close to `bandProj φ`, which is a
  relative-compactness statement about the projected family.

## The fix

The residual must approximate the test function `φ` itself, not its band-projection:

```
∀ φ, IsTestFn D φ → sobolevNormSq d s φ ≤ 1 →
  ∃ ψ, IsTestFn D ψ ∧ sobolevNormSq d s₀ (fun x => φ x - ψ x) ≤ ENNReal.ofReal δ
```

this is the genuine Rellich–Kondrachov precompactness of the `H^s`-unit ball of `C_c^∞(D)` in
`H^{s₀}(ℝ^d)`, and it is true (it does not require `ψ` to match a band-limited centre).  The
consumption in `rkLowFreqNet_of_domainSupportRepair` (`SupportRepair.lean:98`) already supplies,
uniformly over the unit ball, the smallness of the high-frequency part at the truncation level
`Λ'` — `exists_sobolevNormSqHigh_le_truncation` together with `sobolevNormSq_sub_bandProj_le` — so
that `bandProj_{Λ'} φ` is `H^{s₀}`-close to `φ`.  The band-limited jet net is then a proof device
for the finiteness of the family, not a statement about the target of the approximation.

## Note on formalising the refutation

The quantitative content above reduces, for `s₀ = 0`, to `sobolevNormSq d 0 f = ∫ ‖f x‖²`
(Plancherel) together with `∫ ‖bandProj φ - ψ‖² ≥ ∫_{Dᶜ} ‖bandProj φ‖²`, the latter positive because
`bandProj φ` is nonzero on the open set `Dᶜ`.  Plancherel for the compactly supported smooth
difference is available as `SchwartzMap.integral_norm_sq_fourier`; the passage from the bare
function `f` to its Schwartz map `realToComplexSchwartz` and from `∫⁻` of `ENNReal.ofReal` to
`ENNReal.ofReal` of the integral (`ofReal_integral_eq_lintegral_ofReal`, whose `Integrable`
hypothesis is not immediate for `‖𝓕 f‖²`) was not completed under the present budget.  The
falsity of the residual does not depend on that formal step.
