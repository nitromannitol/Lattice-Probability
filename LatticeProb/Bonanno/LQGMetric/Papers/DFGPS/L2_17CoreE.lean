/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17CoreE at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreA
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Step4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: Step 4 bookkeeping (packet P-E of D80, first pieces)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Step 4 (T:1268–1282); decision D80 §3, packet P-E.

* `indep_iSup_iSup_of_monotone` — "Letting `W` increase to `V` and `W'` increase to
  `ℂ ∖ cl V`" (T:1278): independence of two increasing sequences of σ-algebras passes to their
  suprema (mathlib `indep_iSup_of_directed_le`, twice).
* `comap_le_aeClosure_sup_of_add` — "Since `h|_{ℂ∖cl V} = h̊ + 𝔥`, we get that `h` is a
  measurable function of `h̊` and `h|_{cl V}`" (T:1275): if `h' = 𝔥 + h̊` with `𝔥` a.s. equal to
  a `G`-measurable field, then `σ(h') ≤ aeClosure (G ∨ σ(h̊))`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace

namespace LQGMetric.DFGPS.L217

open Blueprint GM.Bilip

/-- `h' = 𝔥 + h̊` with `𝔥` a.s. `G`-measurable: `σ(h') ≤ aeClosure (G ∨ σ(h̊))` (T:1275) -/
theorem comap_le_aeClosure_sup_of_add {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {G : MeasurableSpace Ω} {h' hh hz G₀ : Ω → DistC} (hsum : ∀ ω, h' ω = hh ω + hz ω)
    (hG₀ : Measurable[G] G₀) (hae : hh =ᵐ[P] G₀) :
    MeasurableSpace.comap h' inferInstance ≤
      aeClosure P (G ⊔ MeasurableSpace.comap hz inferInstance) := by
  have hk : Measurable[G ⊔ MeasurableSpace.comap hz inferInstance] fun ω => G₀ ω + hz ω :=
    (@measurable_distOn_iff _ Ω (G ⊔ MeasurableSpace.comap hz inferInstance) _).2 fun φ => by
      show Measurable[G ⊔ MeasurableSpace.comap hz inferInstance] fun ω => G₀ ω φ + hz ω φ
      exact (((measurable_distOn_apply φ).comp hG₀).mono le_sup_left le_rfl).add
        (((measurable_distOn_apply φ).comp (comap_measurable hz)).mono le_sup_right le_rfl)
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨(fun ω => G₀ ω + hz ω) ⁻¹' t, hk ht, ?_⟩
  filter_upwards [hae] with ω hω
  simp only [mem_preimage, hsum ω, hω]

end LQGMetric.DFGPS.L217
