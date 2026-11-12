/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17CoreBH at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreB
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreH

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: (eqn-internal-metric-truncate) (packet P-B of D80)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Step 2, T:1229–1231: "The restrictions of the fields `h − φ𝔥` and `h̊` to the set
`φ⁻¹(1) ⊃ W̄'` are identical. By the locality property (eqn-localized-property) of `D̂^ε_h`, if
`ε > 0` is small enough that `B_ε(W') ⊂ φ⁻¹(1)`, then
`D̂^ε_{h−φ𝔥}(·,·;W̄') ∈ σ(h̊)`" (eqn-internal-metric-truncate). Decision D80, packet P-B.

* `comap_le_aeClosure_of_restrictTo_ae_eq` — if `Y|_O = Y'|_O` a.s., then `σ(Y|_O)` is a.s.
  contained in `σ(Y')`.
* `comap_locSqC_sub_harm_le` — (eqn-internal-metric-truncate):
  `σ(D̂^ε_{h−φ𝔥}(·,·;W̄')) ≤ aeClosure σ(h̊)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric

namespace LQGMetric.DFGPS.L217

open Blueprint GM.Bilip LFPP

/-- if `Y|_O = Y'|_O` a.s., then `σ(Y|_O) ≤ aeClosure σ(Y')` -/
theorem comap_le_aeClosure_of_restrictTo_ae_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {Y Y' : Ω → DistC} {O : Opens ℂ}
    (hae : ∀ᵐ ω ∂P, restrictTo O (Y ω) = restrictTo O (Y' ω)) :
    fieldSigma Y O ≤ aeClosure P (MeasurableSpace.comap Y' inferInstance) := by
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨(fun ω => restrictTo O (Y' ω)) ⁻¹' t,
    ⟨restrictTo O ⁻¹' t, measurable_restrictTo O ht, rfl⟩, ?_⟩
  filter_upwards [hae] with ω hω
  simp only [mem_preimage, hω]

/-- **(eqn-internal-metric-truncate)** (T:1229–1231): if `h' − fn = h̊` on test functions
supported in the open `U₁` (a.s.) and `B̄_{√ε}(z) ⊆ U₁` for `z ∈ W̄'`, then
`σ(D̂^ε_{h'−fn}(·,·;W̄')) ≤ aeClosure σ(h̊)`. -/
theorem comap_locSqC_sub_harm_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (ξ : ℝ)
    {h' hz : Ω → DistC} {fn : Ω → C(ℂ, ℝ)} {U₁ : Set ℂ} (hU₁ : IsOpen U₁)
    (hagree : ∀ᵐ ω ∂P, ∀ ψ : TestC, tsupport (ψ : ℂ → ℝ) ⊆ U₁ →
      (h' ω - ofCont (fn ω)) ψ = hz ω ψ)
    {W : Set ℂ} (hW : IsDyadicDomain W) (hWc : IsConnected (closure W)) {ε : ℝ} (hε : 0 < ε)
    (hKO : ∀ z ∈ closure W, closedBall z (Real.sqrt ε) ⊆ U₁) :
    MeasurableSpace.comap (fun ω => locSqC ξ ε hε (h' ω - ofCont (fn ω)) (closure W))
        inferInstance ≤ aeClosure P (MeasurableSpace.comap hz inferInstance) := by
  set O : Opens ℂ := ⟨U₁, hU₁⟩
  refine (comap_locSqC_le_fieldSigma ξ hε hW hWc (O := O) hKO
    (fun ω => h' ω - ofCont (fn ω))).trans (comap_le_aeClosure_of_restrictTo_ae_eq ?_)
  filter_upwards [hagree] with ω hω
  ext φ
  show (h' ω - ofCont (fn ω)) (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := ⊤) φ) =
    hz ω (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := ⊤) φ)
  refine hω _ ?_
  have e : ((TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := ⊤) φ : TestC) :
      ℂ → ℝ) = φ := by
    rw [TestFunction.monoCLM_apply]
    simp only [le_refl, le_top, and_self, ite_true]
  rw [e]
  exact φ.tsupport_subset

end LQGMetric.DFGPS.L217
