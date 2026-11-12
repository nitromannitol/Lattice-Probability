import Mathlib.Probability.Kernel.Representation
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Independence.Basic

/-!
# Lifting a random element along a measurable map on the same probability space

Let `ν` be a probability law on a standard Borel space `𝒱`, let `π : 𝒱 → 𝒴` be a measurable map into a standard Borel
space, and let `Y` be a random element of `𝒴` on a probability space `(Ω, P)` whose law is the image law `π_* ν`. If
`Ω` carries a uniform random variable `Z ∈ [0, 1]` independent of `Y`, then there is a random element `V` of `𝒱` on
the same space `Ω` with law `ν` and `π(V) = Y` almost surely (the transfer theorem of Kallenberg, *Foundations of Modern
Probability*, chapter on conditioning and disintegration).

The proof disintegrates the law of `(π(v), v)` under `ν` over its first coordinate
(`MeasureTheory.Measure.condKernel`) and realizes the conditional kernel as the image of the uniform law by a jointly
measurable map (`ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval`, Kallenberg Lemma 4.22), evaluated
at `(Y, Z)`. No assumption on `Ω` is needed.
-/

open MeasureTheory unitInterval Function

namespace ProbabilityTheory

variable {Ω 𝒱 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒱] [StandardBorelSpace 𝒱] [Nonempty 𝒱]
  [MeasurableSpace 𝒴] [StandardBorelSpace 𝒴] {P : Measure Ω}

omit [StandardBorelSpace 𝒱] [Nonempty 𝒱] [StandardBorelSpace 𝒴] in
/-- The image of the product of a finite measure `μ` and the uniform law on `[0, 1]` by `(y, z) ↦ (y, f y z)` is the
composition-product of `μ` with the kernel `y ↦ (f y)_* volume`. -/
lemma map_prod_volume_eq_compProd {μ : Measure 𝒴} [SFinite μ] {f : 𝒴 → I → 𝒱} (hf : Measurable (uncurry f))
    {κ : Kernel 𝒴 𝒱} [IsSFiniteKernel κ] (hfκ : ∀ y, volume.map (f y) = κ y) :
    (μ.prod (volume : Measure I)).map (fun p => (p.1, f p.1 p.2)) = μ ⊗ₘ κ := by
  have hg : Measurable fun p : 𝒴 × I => (p.1, f p.1 p.2) := measurable_fst.prodMk hf
  ext s hs
  rw [Measure.map_apply hg hs, Measure.prod_apply (hg hs), Measure.compProd_apply hs]
  refine lintegral_congr fun y => ?_
  have hfy : Measurable (f y) := hf.comp measurable_prodMk_left
  rw [← hfκ y, Measure.map_apply hfy (measurable_prodMk_left hs)]
  rfl

/-- **Same-space lift (transfer lemma).** Let `ν` be a probability law on a standard Borel space `𝒱` and
`π : 𝒱 → 𝒴` a measurable map into a standard Borel space. If `Y` is a random element of `𝒴` on `(Ω, P)` with law
`π_* ν`, and `Z` is a uniform random variable on `[0, 1]` independent of `Y`, then there is a measurable `V : Ω → 𝒱`
with law `ν` and `π(V) = Y` almost surely. -/
theorem exists_map_eq_and_ae_comp_eq [IsProbabilityMeasure P] {ν : Measure 𝒱} [IsProbabilityMeasure ν]
    {π : 𝒱 → 𝒴} (hπ : Measurable π) {Y : Ω → 𝒴} (hY : Measurable Y) (hYlaw : P.map Y = ν.map π)
    {Z : Ω → I} (hZ : Measurable Z) (hZlaw : P.map Z = volume) (hind : IndepFun Y Z P) :
    ∃ V : Ω → 𝒱, Measurable V ∧ P.map V = ν ∧ ∀ᵐ ω ∂P, π (V ω) = Y ω := by
  set ρ : Measure (𝒴 × 𝒱) := ν.map fun v => (π v, v) with hρ
  have hπid : Measurable fun v => (π v, v) := hπ.prodMk measurable_id
  have hρfst : ρ.fst = ν.map π := Measure.fst_map_prodMk hπ measurable_id'
  obtain ⟨f, hf, hfκ⟩ := Kernel.exists_measurable_map_eq_unitInterval ρ.condKernel
  refine ⟨fun ω => f (Y ω) (Z ω), hf.comp (hY.prodMk hZ), ?_⟩
  have hYV : Measurable fun ω => (Y ω, f (Y ω) (Z ω)) := hY.prodMk (hf.comp (hY.prodMk hZ))
  have hjoint : P.map (fun ω => (Y ω, f (Y ω) (Z ω))) = ρ := by
    have hYZ : P.map (fun ω => (Y ω, Z ω)) = (ν.map π).prod (volume : Measure I) := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable).1 hind, hYlaw, hZlaw]
    have hg : Measurable fun p : 𝒴 × I => (p.1, f p.1 p.2) := measurable_fst.prodMk hf
    have e : (fun ω => (Y ω, f (Y ω) (Z ω))) = (fun p : 𝒴 × I => (p.1, f p.1 p.2)) ∘ fun ω => (Y ω, Z ω) := rfl
    rw [e, ← Measure.map_map hg (hY.prodMk hZ), hYZ, ← hρfst, map_prod_volume_eq_compProd hf hfκ,
      Measure.disintegrate ρ ρ.condKernel]
  refine ⟨?_, ?_⟩
  · rw [← Measure.snd_map_prodMk (μ := P) (Y := fun ω => f (Y ω) (Z ω)) hY
      (hf.comp (hY.prodMk hZ)), hjoint, hρ,
      Measure.snd_map_prodMk hπ measurable_id', Measure.map_id']
  · have hD : MeasurableSet {p : 𝒴 × 𝒱 | π p.2 = p.1} :=
      measurableSet_eq_fun (hπ.comp measurable_snd) measurable_fst
    have hρD : ∀ᵐ p ∂ρ, π p.2 = p.1 := by
      rw [hρ, ae_map_iff hπid.aemeasurable hD]
      exact Filter.Eventually.of_forall fun v => rfl
    rw [← hjoint, ae_map_iff hYV.aemeasurable hD] at hρD
    exact hρD

end ProbabilityTheory
