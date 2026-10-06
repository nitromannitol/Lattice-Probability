/-
# The one-dimensional Gaussian log-Sobolev inequality: obstruction record

`LatticeProb.GaussianLogSobolev 1` is the standard Gaussian logarithmic Sobolev
inequality on `ℝ`, in the Herbst form: for a positive density `h` (with
`∫ h ∂γ = 1`, `γ = gaussianReal 0 1`) whose logarithm is `C`-Lipschitz,

    ∫ h log h ∂γ ≤ C² / 2 .

The `n = 0` instance `gaussianLogSobolev_zero` is proved in
`LatticeProb/External/GaussianLogSobolev.lean`.  This file records that the
`n = 1` instance is **not discharged here** and pinpoints why: it is not a
bounded Lean step from the current library, and the missing pieces are genuine
Mathlib gaps rather than local lemmas.  No theorem of this file hides a `sorry`;
there is no declaration here, only this record.

The mathematical statement is classical (Gross 1975; Bakry–Émery 1985) and has
three standard proofs: the Ornstein–Uhlenbeck / heat-flow entropy-dissipation
argument, Bobkov's isoperimetric argument, and optimal transport / entropic CLT.
All three rest on results that are absent from Mathlib and from this library.

## Why the entropy / heat-flow argument is the relevant route

Write `γ = gaussianReal 0 1` and `f = √h`, so `f² = h` and `∫ f² ∂γ = 1`.  The
Herbst form is then exactly the entropy form

    Ent_γ(f²) ≤ 2 ∫ (f')² ∂γ ,     Ent_γ(g) = ∫ g log g ∂γ .

The sharp constant is `2`, attained by `f(x) = e^{a x - a²/2}` (equivalently
`h = e^{a x - a²/2}`, the density of `gaussianReal a 1`), for which both sides
equal `a²/2`.  The heat-flow proof runs along the Mehler (Ornstein–Uhlenbeck)
semigroup

    P_t f x = ∫ z, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z) ∂γ(z) ,
    L = ∂² - x ∂ ,

with `w_t = P_t (f²)`, `Ent(t) = Ent_γ(w_t)`, `I(t) = ∫ (w_t')² / w_t ∂γ`:

1. measure preservation `∫ P_t f ∂γ = ∫ f ∂γ` and self-adjointness of `P_t`;
2. the intertwining `∂_x P_t f = e^{-t} P_t (∂_x f)` and the heat equation
   `∂_t P_t f = L P_t f`;
3. the **entropy dissipation** `Ent'(t) = -I(t)` (one integration by parts on `γ`);
4. the **Fisher decay** `I'(t) = -2 ∫ w_t ((log w_t)'')² ∂γ - 2 I(t) ≤ -2 I(t)`
   (two integrations by parts on `γ`; the identity is `Γ₂(log w) = ((log w)'')² +
   ((log w)')² ≥ ((log w)')²`, the 1-D Bakry–Émery curvature-1 condition);
5. Gronwall: `Ent(0) = ∫₀^∞ I(t) dt ≤ ∫₀^∞ e^{-2t} I(0) dt = I(0)/2`, and
   `I(0) = 4 ∫ (f')² ∂γ`;
6. a smooth-approximation step extending the identity from smooth `h` to the
   frozen class of merely Lipschitz `log h`.

Steps 1–2 are the Mehler-semigroup layer; 3–4 are the two integrations by parts
and the `Γ₂` identity; 6 is the `H¹(γ)`-density layer.  Steps 3–5 are the ones
with no library support.

## Alternative routes and why they do not shorten the work

* The exact expansion `Ent_γ(e^{u}) = ∫₀¹ t · Var_{γ_t}(u) ∂t`, where
  `γ_t ∝ e^{t u} γ`, is correct and reduces the LSI to `Var_{γ_t}(u) ≤ C²` for
  all `t ∈ [0,1]`.  That bound is a tilted-measure Poincaré/variance estimate of
  the same strength as the LSI (it is equivalent to it through the expansion),
  so it is not an easier target; in particular the naive consequence
  `Var_{γ_t}(u) ≤ C² Var_{γ_t}(x)` needs `Var_{γ_t}(x) ≤ 1`, which the tilt can
  violate.
* The Gaussian Poincaré inequality `Var_γ(f) ≤ ∫ (f')² ∂γ` alone cannot give the
  sharp constant: for `f = 1_A / √p` (`γ(A) = p`, so `∫ f² = 1`) one has
  `Ent_γ(f²) = log (1/p)` while `Var_γ(f) = 1 - p`, so no `Ent ≤ K·Var` can hold;
  the entropy is genuinely stronger than the variance.
* Bobkov's argument needs the Gaussian isoperimetric inequality; Brascamp–Lieb
  needs the Brascamp–Lieb inequality; the entropic CLT needs the Stam inequality
  and Barron's monotonicity.  Each is deeper than the OU argument and none is in
  Mathlib.

## Exact missing Mathlib pieces

1. **Real-valued entropy and its identification with `klDiv`.**
   `InformationTheory.klDiv` is `ℝ≥0∞`-valued; there is no `ℝ`-valued
   `MeasureTheory.entropy μ f = ∫ f log f ∂μ`, its chain rule, or the identity
   `InformationTheory.klDiv (h • γ) γ = ∫ h log h ∂γ` for `∫ h ∂γ = 1` that
   connects the library's KL lemmas (`LatticeProb.klDiv_*`) to the LSI's left
   side.

2. **The Ornstein–Uhlenbeck / Mehler semigroup on `L²(γ)`.**
   No `LatticeProb.ouSemigroup` (Mehler formula above), no
   `ouSemigroup_one`, `ouSemigroup_semigroup`, `integral_ouSemigroup`
   (measure preservation), `ouSemigroup_adjoint` (self-adjointness),
   `ouSemigroup_deriv` (`∂_x P_t f = e^{-t} P_t (∂_x f)`), or `ouSemigroup_heat`
   (`∂_t P_t f = L P_t f`).  Mathlib's Gaussian convolution lemmas
   (`ProbabilityTheory.gaussianReal_conv_gaussianReal`,
   `gaussianReal_add_gaussianReal_of_indepFun`) supply measure preservation but
   not the derivative/heat identities.

3. **Integration by parts against `γ`.**
   The assembled statement `∫ g · (h'' - x h') ∂γ = -∫ g' h' ∂γ` (with the
   Gaussian decay and integrability side conditions) is not in Mathlib.  The raw
   1-D integration-by-parts formula for Lebesgue measure and the density lemmas
   for `gaussianReal` exist, but the weighted statement used repeatedly in
   steps 3–4 does not.

4. **Carré du champ, `Γ₂`, and the Bakry–Émery identities.**
   Missing: the definitions `Γ(f) = (f')²`, `Γ₂(f) = (f'')² + (f')²`; the
   commutation `[L, ∂] = -∂`; `d/dt ∫ (P_t f)² ∂γ = -2 e^{-2t} ∫ (P_t f')² ∂γ`;
   `d/dt ∫ (P_t f')² ∂γ = -2 ∫ (P_t f'')² ∂γ - 2 ∫ (P_t f')² ∂γ`; and the entropy
   dissipation `d/dt Ent(P_t w) = -∫ (P_t w')² / (P_t w) ∂γ`.

5. **Smooth approximation / `H¹(γ)` density.**
   The frozen class is `log h` merely Lipschitz, not `C²`.  Missing: density of
   smooth positive functions in the relevant weighted Sobolev class, together
   with continuity of `h ↦ ∫ h log h` and `h ↦ ∫ (h')² / h` along the
   approximation, to transfer steps 3–5 from smooth `h` to the frozen class.

Estimated cost: items 2–5 are roughly 800–2000 lines of real analysis; items 3
and 4 (two integrations by parts plus `Γ₂`) are the hard/technical core, and
item 5 is a second independent layer.  No 1-D Gaussian LSI formalization exists
in Mathlib, in this repository, or in the sibling `LP-anchored-box` /
`Lattice-HC` libraries to port (the sibling `LP-anchored-box` only proves the
converse implication `GaussianLogSobolev n → GaussianHerbstBound n`,
`LatticeProb/Prob/HerbstFromLSI.lean`, 573 lines).

## What would make the packet bounded

Either (a) a Mathlib (or vendored) Ornstein–Uhlenbeck `Γ₂` package — the
semigroup, the heat equation, and the weighted integration by parts — after
which steps 3–5 are short; or (b) a Mathlib real-valued entropy with its chain
rule and density/persistence lemmas for the weighted Sobolev layer, after which
the Bobkov/transport route becomes plumbable.  Without one of these the 1-D LSI
is a multi-hundred-line real-analysis file in its own right, not a bounded
packet.
-/
import LatticeProb.External.GaussianLogSobolev

-- No declaration is introduced: the `n = 1` instance above is not proved here,
-- and stating it would require a `sorry`.
