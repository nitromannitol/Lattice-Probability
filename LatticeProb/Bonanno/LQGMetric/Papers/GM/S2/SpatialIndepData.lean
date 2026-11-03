/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.SpatialIndepData at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import Mathlib.Probability.Independence.Basic

/-!
# GM Lemma 2.7: the frozen data from the Markov decomposition

GM (`literature/src/1905.00383/uniqueness-final.tex`) l. 972–976 (proof of Lemma 2.7): with
`h = 𝔥 + h̊` the Markov decomposition on `U = ⋃_z B_{1+s}(z)` (`Blueprint.LMLem2_1`: `𝔥` a.s.
equal to a `σ(h|_{ℂ∖U})`-measurable `G`, `h̊` independent of `σ(h|_{ℂ∖U})`), the field data used by
`SpatialIndepCore.frozen_union_bound`:

* `indepFun_of_indep_comap` — `G ⟂ (h̊|_{D_i})_i` from `σ(h̊) ⟂ 𝓕` and `G` `𝓕`-measurable;
* `measurable_add_restrictTo` — `(w, y) ↦ (y + w)|_V` is measurable (so the sets
  `T_z = {(w,y) | (y + w)|_{B_1(z)} ∈ S_z}` are measurable);
* `exists_preimage_of_aeEventIn` — an event a.s. determined by `X|_V` is a.s. `X|_V ∈ S`.

Own elementary arguments (definitions unfolded; no source needed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace

namespace LQGMetric.GM

open Blueprint

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- an event a.s. determined by `X|_V` is a.s. of the form `{X|_V ∈ S}` -/
theorem exists_preimage_of_aeEventIn {X : Ω → DistC} {V : Opens ℂ} {E : Set Ω}
    (hE : AEEventIn P (fieldSigma X V) E) :
    ∃ S : Set (DistOn V), MeasurableSet S ∧ E =ᵐ[P] (fun ω => restrictTo V (X ω)) ⁻¹' S := by
  obtain ⟨F, hF, hEF⟩ := hE
  obtain ⟨S, hS, rfl⟩ := hF
  exact ⟨S, hS, hEF⟩

end LQGMetric.GM
