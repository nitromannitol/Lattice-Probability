/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoiseVersion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseCont
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseLaw

/-!
# The continuous versions of `φ_{a,b}` keep additivity and independence (task P2-WN)

DDDF (arXiv:1904.08021, `tightness.tex` l. 283, 292) works with the continuous (smooth) versions
of the fields `φ_{a,b}` and uses `φ_{a,c} = φ_{a,b} + φ_{b,c}` with independent summands.
For continuous measurable modifications (`exists_continuous_modification_phi`):

* `IndepFun.of_modification`: independence passes to modifications (the joint law on
  `(S → ℝ) × (T → ℝ)` is determined by the finite-dimensional laws; mathlib
  `indepFun_iff_map_prod_eq_prod_map_map`, `MeasurableEquiv.sumPiEquivProdPi`).
* `indepFun_phi_version`: continuous versions of `φ_{a,b}` and `φ_{b,c}` are independent.
* `phi_version_add_ae`: a.s., `Y_{a,c}(x) = Y_{a,b}(x) + Y_{b,c}(x)` for **all** `x`
  (equality on a countable dense set, then continuity).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace LQGMetric
namespace WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Modifications have the same law (any index type). -/
theorem map_eq_of_modification' {T : Type*} {Y X : T → Ω → ℝ} [IsFiniteMeasure P]
    (hY : ∀ t, Measurable (Y t)) (hX : ∀ t, Measurable (X t)) (hYX : ∀ t, Y t =ᵐ[P] X t) :
    P.map (fun ω t => Y t ω) = P.map (fun ω t => X t ω) := by
  refine map_eq_of_forall_finset' (measurable_pi_iff.mpr hY).aemeasurable
    (measurable_pi_iff.mpr hX).aemeasurable fun I => ?_
  refine Measure.map_congr ?_
  have h : ∀ᵐ ω ∂P, ∀ i : I, Y i ω = X i ω := ae_all_iff.mpr fun i => hYX i
  filter_upwards [h] with ω hω
  funext i
  exact hω i

/-- Independence of two families passes to modifications. -/
theorem IndepFun.of_modification {S T : Type*} [IsFiniteMeasure P] {X₁ Y₁ : S → Ω → ℝ}
    {X₂ Y₂ : T → Ω → ℝ} (h : IndepFun (fun ω s => X₁ s ω) (fun ω t => X₂ t ω) P)
    (hX₁ : ∀ s, Measurable (X₁ s)) (hX₂ : ∀ t, Measurable (X₂ t))
    (hY₁ : ∀ s, Measurable (Y₁ s)) (hY₂ : ∀ t, Measurable (Y₂ t))
    (h₁ : ∀ s, Y₁ s =ᵐ[P] X₁ s) (h₂ : ∀ t, Y₂ t =ᵐ[P] X₂ t) :
    IndepFun (fun ω s => Y₁ s ω) (fun ω t => Y₂ t ω) P := by
  have mX₁ : Measurable fun ω s => X₁ s ω := measurable_pi_iff.mpr hX₁
  have mX₂ : Measurable fun ω t => X₂ t ω := measurable_pi_iff.mpr hX₂
  have mY₁ : Measurable fun ω s => Y₁ s ω := measurable_pi_iff.mpr hY₁
  have mY₂ : Measurable fun ω t => Y₂ t ω := measurable_pi_iff.mpr hY₂
  rw [indepFun_iff_map_prod_eq_prod_map_map mX₁.aemeasurable mX₂.aemeasurable] at h
  rw [indepFun_iff_map_prod_eq_prod_map_map mY₁.aemeasurable mY₂.aemeasurable,
    map_eq_of_modification' hY₁ hX₁ h₁, map_eq_of_modification' hY₂ hX₂ h₂, ← h]
  -- the pair is the image of the `S ⊕ T`-indexed process under `sumPiEquivProdPi`
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : S ⊕ T => ℝ)
  have hpair : ∀ (U₁ : S → Ω → ℝ) (U₂ : T → Ω → ℝ),
      (fun ω => ((fun s => U₁ s ω), (fun t => U₂ t ω))) =
        e ∘ fun ω i => Sum.elim U₁ U₂ i ω := by
    intro U₁ U₂; funext ω; rfl
  have hZ : P.map (fun ω i => Sum.elim Y₁ Y₂ i ω) = P.map (fun ω i => Sum.elim X₁ X₂ i ω) :=
    map_eq_of_modification' (fun i => by cases i <;> simp [hY₁, hY₂])
      (fun i => by cases i <;> simp [hX₁, hX₂]) fun i => by cases i <;> simp [h₁, h₂]
  rw [hpair, hpair, ← Measure.map_map e.measurable
      (measurable_pi_iff.mpr fun i => by cases i <;> simp [hY₁, hY₂]),
    ← Measure.map_map e.measurable
      (measurable_pi_iff.mpr fun i => by cases i <;> simp [hX₁, hX₂]), hZ]

variable {W : WNSpace → Ω → ℝ}

/-- **Independence of scales for the continuous versions.** -/
theorem indepFun_phi_version (hW : IsWhiteNoise P W) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {Y₁ Y₂ : ℂ → Ω → ℝ} (hm₁ : ∀ x, Measurable (Y₁ x)) (hm₂ : ∀ x, Measurable (Y₂ x))
    (h₁ : ∀ x, Y₁ x =ᵐ[P] phi W a b x) (h₂ : ∀ x, Y₂ x =ᵐ[P] phi W b c x) :
    IndepFun (fun ω x => Y₁ x ω) (fun ω x => Y₂ x ω) P := by
  have := hW.isProbabilityMeasure
  exact IndepFun.of_modification (indepFun_phi hW ha hab) (fun x => measurable_phi hW a b x)
    (fun x => measurable_phi hW b c x) hm₁ hm₂ h₁ h₂

/-- **Additivity everywhere for the continuous versions**: a.s., for all `x`,
`Y_{a,c}(x) = Y_{a,b}(x) + Y_{b,c}(x)`. -/
theorem phi_version_add_ae (hW : IsWhiteNoise P W) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbc : b ≤ c) {Y₁ Y₂ Y₃ : ℂ → Ω → ℝ} (hc₁ : ∀ ω, Continuous fun x => Y₁ x ω)
    (hc₂ : ∀ ω, Continuous fun x => Y₂ x ω) (hc₃ : ∀ ω, Continuous fun x => Y₃ x ω)
    (h₁ : ∀ x, Y₁ x =ᵐ[P] phi W a b x) (h₂ : ∀ x, Y₂ x =ᵐ[P] phi W b c x)
    (h₃ : ∀ x, Y₃ x =ᵐ[P] phi W a c x) :
    ∀ᵐ ω ∂P, ∀ x, Y₃ x ω = Y₁ x ω + Y₂ x ω := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have := hDc.to_subtype
  have hD : ∀ᵐ ω ∂P, ∀ x : D, Y₃ x ω = Y₁ x ω + Y₂ x ω := by
    refine ae_all_iff.mpr fun x => ?_
    filter_upwards [h₁ x, h₂ x, h₃ x, phi_add_ae hW ha hab hbc x] with ω e1 e2 e3 e4
    rw [e1, e2, e3, e4]
  filter_upwards [hD] with ω hω
  intro x
  have := Continuous.ext_on hDd (hc₃ ω) ((hc₁ ω).add (hc₂ ω)) (fun y hy => hω ⟨y, hy⟩)
  exact congrFun this x

end WhiteNoise
end LQGMetric
