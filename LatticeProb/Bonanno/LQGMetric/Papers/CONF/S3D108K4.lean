/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108K4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLength
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs

/-!
# S-cont-law: a Weyl-scaled quantity hits a fixed level with probability zero

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, C:667–669: "such functionals are a.s.
continuous at `D_h` since the probability that the supremum or infimum in question is exactly
equal to `c` is zero. This can be seen using Axiom III and the fact that adding a smooth compactly
supported function to `h` affects its law in an absolutely continuous way" (also C:1239–1241,
blueprint row CONF.S-cont-law).

CONF gives this argument in one sentence; here it is written out (own elementary measure
theory, following that sentence):
let `φ` be continuous with `φ = 1` on the open set `V` (in practice a bump supported in `U`), so
that by Axiom III `Y(x + tφ) = e^{ξt} Y(x)` for every `t`, where `Y(x)` is an internal diameter
in `V` (`internalDiam_addFun_const`). For a level `T ∈ (0, ∞)` the set `{t : e^{ξt} Y(x) = T}` has at
most one point, so by Fubini `∫ P[Y(X + tφ) = T] dt = 0`. Hence `P[Y(X + tφ) = T] = 0` for some
`t`, and absolute continuity of the law of `X` with respect to that of `X + tφ` (Cameron–Martin)
gives `P[Y(X) = T] = 0`.

* `measurable_addFun_smul`: `(t, x) ↦ x + tφ` is measurable;
* **`measure_level_eq_zero`**: the abstract statement (law `ν` on `𝒟'(ℂ)`, measurable
  `Y : 𝒟'(ℂ) → [0, ∞]`, a.e. scaling `Y(x + tφ) = e^{ξt} Y(x)`, `ν ≪ ν ∘ (· + tφ)⁻¹` for all `t`);
* `internalDiam_addFun_const`: at a field where Axiom III holds, if `φ = 1` on the open `V` then
  `diam(A; D_{k+tφ}(·,·;V)) = e^{ξt} diam(A; D_k(·,·;V))` (`internal_eq_of_eq_const`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- `(t, x) ↦ x + tφ` is measurable -/
lemma measurable_addFun_smul (φ : C(ℂ, ℝ)) :
    Measurable fun p : ℝ × DistC => addFun p.2 (p.1 • φ) := by
  refine GFFInv.measurable_distC_iff.2 fun ψ => ?_
  have e : ∀ p : ℝ × DistC, addFun p.2 (p.1 • φ) ψ = p.2 ψ + p.1 * ∫ x, ψ x * φ x := fun p => by
    simp only [addFun, add_apply, ofCont_apply, ContinuousMap.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    refine congrArg _ (funext fun x => by ring)
  simp only [e]
  exact ((GFFInv.measurable_pair ψ).comp measurable_snd).add
    (measurable_fst.mul measurable_const)

/-- a level `T ∈ (0, ∞)` is hit by `t ↦ e^{ξt} y` at most once -/
lemma subsingleton_level {ξ : ℝ} (hξ : ξ ≠ 0) (y : ℝ≥0∞) {T : ℝ≥0∞} (hT0 : T ≠ 0)
    (hTt : T ≠ ⊤) : {t : ℝ | ENNReal.ofReal (Real.exp (ξ * t)) * y = T}.Subsingleton := by
  intro t₁ h₁ t₂ h₂
  simp only [mem_ofPred_eq] at h₁ h₂
  have hy0 : y ≠ 0 := fun h => hT0 (by rw [← h₁, h, mul_zero])
  have hyt : y ≠ ⊤ := fun h => hTt (by
    rw [← h₁, h, ENNReal.mul_top (by simpa using Real.exp_pos (ξ * t₁))])
  have h := h₁.trans h₂.symm
  rw [ENNReal.mul_left_inj hy0 hyt, ENNReal.ofReal_eq_ofReal_iff (Real.exp_pos _).le
    (Real.exp_pos _).le, Real.exp_eq_exp] at h
  exact mul_left_cancel₀ hξ h

/-- **S-cont-law, abstract form** (CONF C:667–669): if `Y(x + tφ) = e^{ξt} Y(x)` for `ν`-a.e. `x`
and all `t`, and the law `ν` is absolutely continuous with respect to its shifts by `tφ`, then
`Y` hits any level `T ∈ (0, ∞)` with `ν`-probability `0`. -/
theorem measure_level_eq_zero {ν : Measure DistC} [SFinite ν] {φ : C(ℂ, ℝ)} {ξ : ℝ}
    (hξ : ξ ≠ 0) {Y : DistC → ℝ≥0∞} (hY : Measurable Y) {T : ℝ≥0∞} (hT0 : T ≠ 0) (hTt : T ≠ ⊤)
    (hscale : ∀ᵐ x ∂ν, ∀ t : ℝ, Y (addFun x (t • φ)) = ENNReal.ofReal (Real.exp (ξ * t)) * Y x)
    (hac : ∀ t : ℝ, ν ≪ ν.map fun x => addFun x (t • φ)) :
    ν {x | Y x = T} = 0 := by
  have hS := measurable_addFun_smul φ
  set E : Set (ℝ × DistC) := {p | Y (addFun p.2 (p.1 • φ)) = T} with hE
  have hEm : MeasurableSet E := (hY.comp hS) (measurableSet_singleton T)
  -- the `x`-sections have Lebesgue measure zero
  have h0 : (volume.prod ν) E = 0 := by
    rw [Measure.prod_apply_symm hEm]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [hscale] with x hx
    refine measure_mono_null (t := {t : ℝ | ENNReal.ofReal (Real.exp (ξ * t)) * Y x = T})
      (fun t ht => ?_) ((subsingleton_level hξ (Y x) hT0 hTt).countable.measure_zero volume)
    simp only [mem_preimage, hE, mem_ofPred_eq] at ht
    simp only [mem_ofPred_eq, ← hx t, ht]
  rw [Measure.prod_apply hEm] at h0
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), ν (Prod.mk t ⁻¹' E) = 0 :=
    (lintegral_eq_zero_iff (measurable_measure_prodMk_left hEm)).1 h0
  obtain ⟨t, ht⟩ := hae.exists
  have hmt : Measurable fun x : DistC => addFun x (t • φ) :=
    hS.comp (measurable_const.prodMk measurable_id)
  have hEx : MeasurableSet {x : DistC | Y x = T} := hY (measurableSet_singleton T)
  refine hac t ?_
  rw [Measure.map_apply hmt hEx]
  exact ht

variable {ξ : ℝ} {D : DistC → ContMetric} {k : DistC}

/-- Axiom III at `k` for every continuous function: `weylScale ξ f (D k) = D_{k+f}` -/
lemma internalDiam_addFun_const
    (hw : ∀ (f : C(ℂ, ℝ)) (z w : ℂ),
      weylScale ξ f (D k) z w = ENNReal.ofReal ((D (addFun k f)).1 (z, w)))
    {φ : C(ℂ, ℝ)} {V : Set ℂ} (hV : IsOpen V) (hφ : ∀ x ∈ V, φ x = 1) (A : Set ℂ) (t : ℝ) :
    internalDiam (D (addFun k (t • φ))) A V =
      ENNReal.ofReal (Real.exp (ξ * t)) * internalDiam (D k) A V := by
  have h := fun u v => internal_eq_of_eq_const (D (addFun k (t • φ)))
    (fun x y => (hw (t • φ) x y).symm) hV (c := ξ * t)
    (fun x hx => by simp [hφ x hx]) u v
  unfold internalDiam
  simp_rw [ENNReal.mul_iSup, h]

end LQGMetric.CONF
