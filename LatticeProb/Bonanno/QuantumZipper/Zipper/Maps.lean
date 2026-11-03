/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Zipper.Maps at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Zipper.Welding
import LatticeProb.Bonanno.QuantumZipper.Loewner.Forward
import LatticeProb.Bonanno.QuantumZipper.LQG.Surfaces

/-!
# The capacity zipper and length unzipping

`Z^LEN_ℓ`, `ℓ ≥ 0`, is in `Zipper/LengthZip.lean`.

`FOUNDATIONS.md` §7, `STATEMENT_SPEC.md` A8, A12, A13, `THEOREM_STATEMENTS_ENGLISH.md`
Corollary 1.5 and Theorem 1.8.

A configuration is a pair `c = (x, W) : FieldSample × (ℝ → ℝ)`: the field `h` on `ℍ` and the
driving function `W` of the curve `η` from `0` to `∞`. It encodes the pair of quantum surfaces
`((D₁,h|D₁),(D₂,h|D₂))` cut out by `η` (A8). Only the values of `W` on `[0,∞)` are meaningful.
All driving functions *produced* here are normalized to vanish on `(−∞,0]`, matching the
convention of `drive` (`SLE/Defs.lean`), so that laws of configurations can be compared as laws
of `ℝ → ℝ`-valued maps.

## Sign verification (reverse flow vs. forward flow)

The flows of `Loewner/Forward.lean` and `Loewner/Reverse.lean` are, in differential form,
`∂ₜ fₜ = 2/fₜ − Ẇₜ` (forward, `fₜ = gₜ − Wₜ`) and `∂ₜ uₜ = −2/uₜ − Ẇₜ` (reverse), with
`f₀ = u₀ = z` when `W 0 = 0`.

1. *Reverse map = inverse of a centered forward map.* Let `V` be a driver with `V 0 = 0`, `gᵣ`
   its uncentered forward maps, fix `t`, `w ∈ ℍ`, `z₀ := g_t⁻¹(w + V t)`, `Gᵣ := gᵣ(z₀)`, and
   `u s := G (t−s) − V (t−s)` for `s ∈ [0,t]`. Then `u 0 = w` and
   `u' s = −2/(G(t−s) − V(t−s)) − d/ds V(t−s) = −2/u s − U' s` with `U s := V(t−s) − V t`
   (normalized by `U 0 = 0`). Hence `revMap U t w = u t = z₀ = (fwdMap V t)⁻¹ w`: the reverse
   map driven by `U` at time `t` inverts the centered forward map driven by `V`. Conversely,
   given `W'`, the choice `V r := W'(t−r) − W' t` gives `V(t−s) − V t = W' s`, so
   `revMap W' t = (fwdMap V t)⁻¹` and `K_t = revHull W' t` is the forward hull of `V` at time
   `t`: the zipped segment is traced from `0` by the time-reversed driver `V`.
2. *Continuing with the image of `η`.* After zipping, the new curve is `K_t ∪ f(η)` with
   `f := revMap W' t`. Uniformize `ℍ \ (K_t ∪ f(η[0,r]))` by `ζ ↦ gᵣ^η(g_t^V(ζ) − V t)`; the
   half-plane capacities add (`2t + 2r`), so the uncentered Loewner map at time `t + r` is
   `ζ ↦ gᵣ^η(g_t^V(ζ) − V t) + V t`, and its driver (the image of the tip `f(η(r))`) is
   `gᵣ^η(η(r)) + V t = W r + V t = W r − W' t`. So for `s ≥ t` the new driver is
   `W (s − t) − W' t`; it is continuous at `s = t` (both sides equal `−W' t`) and `0` at `0`.
3. *Unzipping.* The remaining curve `f_t^η(η[t,∞))` is uniformized by
   `ζ ↦ g_{t+s}((g_t)⁻¹(ζ + W t)) − W t = ζ + 2s/ζ + …`, with driver `W (t+s) − W t`.
4. *Brownian rescaling.* `rescale x Q a = x(a·) + Q log a`, so a point `w` of the old picture
   is `w / a` in the new one: the new curve is (old remaining curve)`/a`. Since
   `hcap(K/a) = hcap(K)/a²`, `g^{η/a}_s(ζ) = g^η_{a²s}(aζ)/a`, with driver `W(a² s)/a`.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace QuantumZipper

/-- Zipping up by capacity time `t ≥ 0` (Corollary 1.5's `Z^CAP_t`, `t ≥ 0`). With
`W' := weldDriver γ x t` the driver of the welding-determined reverse flow `f = f^h_t :
ℍ → ℍ \ K_t`, the new field is the pushforward `h ∘ f⁻¹ + Q log|(f⁻¹)'|` (`Q = Qc γ`) and the
new driving function traces the zipped segment `K_t` from `0` by the time-reversed driver
`W'(t − s) − W' t` for `s ∈ [0,t]`, then the image `f(η)` of the old curve, with driver
`W (s − t) − W' t` for `s ≥ t` (see the sign verification in the module docstring). The driver
is normalized to `0` on `(−∞,0]`. -/
noncomputable def zipCapUp (γ t : ℝ) (c : FieldSample × (ℝ → ℝ)) :
    FieldSample × (ℝ → ℝ) :=
  let W' := weldDriver γ c.1 t
  (coordChange c.1 (revMapInv W' t) (Qc γ),
    fun s => if s ≤ t then W' (t - max s 0) - W' t else c.2 (s - t) - W' t)

/-- Unzipping by capacity time `t ≥ 0` (Corollary 1.5's `Z^CAP_{−t}`): the forward flow
`f^η_t : ℍ \ η[0,t] → ℍ` of `η` pushes the field forward to `h ∘ (f^η_t)⁻¹ + Q log|((f^η_t)⁻¹)'|`
and the remaining curve `f^η_t(η[t,∞))` has driving function `W (t + s) − W t`, normalized to
`0` for `s ≤ 0`. -/
noncomputable def zipCapDown (γ t : ℝ) (c : FieldSample × (ℝ → ℝ)) :
    FieldSample × (ℝ → ℝ) :=
  (coordChange c.1 (fwdMapInv c.2 t) (Qc γ), fun s => c.2 (t + max s 0) - c.2 t)

/-- The capacity quantum zipper `Z^CAP_t` of Corollary 1.5: zip up by `t` for `t ≥ 0`, unzip by
`−t` for `t < 0`. -/
noncomputable def zipCap (γ t : ℝ) : FieldSample × (ℝ → ℝ) → FieldSample × (ℝ → ℝ) :=
  if 0 ≤ t then zipCapUp γ t else zipCapDown γ (-t)

/-- The images `(O⁻_t, O⁺_t)` of the two sides `0⁻`, `0⁺` of the origin under the centered
forward map `f_t = g_t − W_t` (`STATEMENT_SPEC.md` A12): the one-sided limits of `f_t(x)` as
real `x → 0`. The segment `[O⁻_t, O⁺_t]` is the image of the two sides of `η[0,t]`. -/
noncomputable def sideImages (W : ℝ → ℝ) (t : ℝ) : ℝ × ℝ :=
  (limUnder (𝓝[<] (0 : ℝ)) (fun x : ℝ => (fwdMap W t x).re),
    limUnder (𝓝[>] (0 : ℝ)) (fun x : ℝ => (fwdMap W t x).re))

/-- The quantum lengths of `η[0,t]` measured from `D₁` and from `D₂` (Theorem 1.8, "well
defined by unzipping", `STATEMENT_SPEC.md` A12): with `x_t` the unzipped field
`h ∘ f_t⁻¹ + Q log|(f_t⁻¹)'|`, the `ν_{x_t}`-lengths of `[O⁻_t, 0]` and `[0, O⁺_t]`. -/
noncomputable def unzipLengths (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) (t : ℝ) : ℝ≥0∞ × ℝ≥0∞ :=
  let xt := coordChange c.1 (fwdMapInv c.2 t) (Qc γ)
  (qBoundaryMeasure γ xt (Set.Icc (sideImages c.2 t).1 0),
    qBoundaryMeasure γ xt (Set.Icc 0 (sideImages c.2 t).2))

/-- The length quantum zipper `Z^LEN_{−ℓ}` of Theorem 1.8, for `ℓ ≥ 0`: unzip up to the first
capacity time `t'` at which the quantum length of `η[0,t']` seen from `D₁` reaches `ℓ` (the
length seen from `D₂` agrees a.s., by Theorem 1.8's wedge decomposition), then rescale by (1.8)
with `a = scaleParam γ x'` so that `B₁(0) ∩ ℍ` has unit quantum area. The driving function of
the remaining curve, `W(t' + ·) − W t'`, transforms by Brownian scaling:
`s ↦ (W (t' + a² s) − W t') / a` (normalized to `0` for `s ≤ 0`). -/
noncomputable def zipLenDown (γ ℓ : ℝ) (c : FieldSample × (ℝ → ℝ)) :
    FieldSample × (ℝ → ℝ) :=
  let t' := sInf {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ (unzipLengths γ c s).1}
  let x' := coordChange c.1 (fwdMapInv c.2 t') (Qc γ)
  let a := scaleParam γ x'
  (rescale x' (Qc γ) a, fun s => (c.2 (t' + a ^ 2 * max s 0) - c.2 t') / a)

/-- Equality of regularized fields: all regularized circle averages `h_{2^{-k}}(z)` agree. By
`STATEMENT_SPEC.md` A13 the field is only meaningful through its regularization. -/
def RegEq (x y : FieldSample) : Prop := ∀ k z, avgReg x k z = avgReg y k z

theorem zipCap_of_nonneg {γ t : ℝ} (ht : 0 ≤ t) : zipCap γ t = zipCapUp γ t := by
  simp only [zipCap, ht, ↓reduceIte]

theorem zipCap_of_neg {γ t : ℝ} (ht : t < 0) : zipCap γ t = zipCapDown γ (-t) := by
  simp only [zipCap, not_le.mpr ht, ↓reduceIte]

end QuantumZipper
