/-
The pushforward of an independent family along a map of the one-site space.

`LatticeProb.infinitePi_map_comp` and `infinitePi_map_comp'` read an
independent family along an injective family of INDICES and keep the one-site
law.  This is the orthogonal statement: the index set is kept and the one-site
law moves.  Applying a measurable `f` in every coordinate of an i.i.d. field
with one-site law `ν` gives the i.i.d. field with one-site law `ν.map f`.  The
proof is `Measure.eq_infinitePi` against cylinders: the preimage of the cylinder
`{η | ∀ i ∈ s, η i ∈ t i}` under the coordinatewise map is the cylinder
`{η | ∀ i ∈ s, η i ∈ f ⁻¹' t i}`.
-/
import Mathlib
import LatticeProb.IID

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

/-- **The coordinatewise pushforward of an independent family.**  Applying a
measurable map of the one-site space in every coordinate of an infinite product
of copies of `ν` gives the infinite product of copies of `ν.map f`. -/
theorem infinitePi_map_pi {ι α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) [IsProbabilityMeasure ν] {f : α → β} (hf : Measurable f) :
    (Measure.infinitePi fun _ : ι => ν).map (fun η i => f (η i))
      = Measure.infinitePi fun _ : ι => ν.map f := by
  classical
  have hF : Measurable (fun (η : ι → α) (i : ι) => f (η i)) :=
    measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i)
  have : IsProbabilityMeasure (ν.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  refine Measure.eq_infinitePi (fun _ : ι => ν.map f) fun s t ht => ?_
  have hpre : (fun (η : ι → α) (i : ι) => f (η i)) ⁻¹' (Set.pi ↑s t)
      = Set.pi ↑s (fun i => f ⁻¹' t i) := by
    ext η; simp [Set.mem_pi]
  rw [Measure.map_apply hF (MeasurableSet.pi (Set.to_countable _) fun i _ => ht i), hpre,
    Measure.infinitePi_pi _ fun i _ => hf (ht i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Measure.map_apply hf (ht i)]

/-- The lattice form: the coordinatewise pushforward of an i.i.d. field. -/
theorem iidLaw_map_pi (d : ℕ) {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) [IsProbabilityMeasure ν] {f : α → β} (hf : Measurable f) :
    (iidLaw d ν).map (fun η i => f (η i)) = iidLaw d (ν.map f) :=
  infinitePi_map_pi ν hf

end LatticeProb
