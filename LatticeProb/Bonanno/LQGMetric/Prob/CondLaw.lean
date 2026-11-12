/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Prob.CondLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Prob.CondCopies
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelRange
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelMetric

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Regular conditional laws given the field

The regular conditional law of a random continuous metric `D : Ω → ContMetric` given a random
distribution `h : Ω → DistOn U` (or of any standard Borel quantity given any data) is mathlib's
`condDistrib D h μ`. It exists because `ContMetric` is standard Borel
(`LQGMetric.standardBorelSpace_contMetric`) and nonempty (`euclidContMetric`, this file); the
same holds for `DistOn V` (`LQGMetric.standardBorelSpace_distOn`), so conditional laws of
restricted fields given other data (LM S3.3b, LM Lemma 3.3) are also `condDistrib`s.

Main results:
* `euclidContMetric`: the Euclidean metric as a `ContMetric`; `Nonempty ContMetric`;
* `map_field_metric_eq_compProd`: `law(h, D) = law(h) ⊗ condDistrib D h μ` (disintegration);
* `condDistrib_metric_ae_eq_of_compProd`: uniqueness of the conditional law;
* `condCopy_metric_law`, `condCopy_metric_triple`: the conditionally i.i.d. copy `D̃` of `D`
  given `h` (LM Theorem 1.7 and Corollary 1.8, tex:306–311, 317–332): `(h, D̃)` has the law of
  `(h, D)` (LM S1.8a) and `(h, D, D̃)` has law `law(h) ⊗ (κ × κ)`.

Mathlib sources: `Mathlib/Probability/Kernel/CondDistrib.lean` (`compProd_map_condDistrib`,
`condDistrib_ae_eq_of_measure_eq_compProd`).
-/

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter

namespace LQGMetric

/-- The Euclidean metric `(z, w) ↦ |z − w|` as a continuous metric. -/
noncomputable def euclidContMetric : ContMetric :=
  ⟨⟨fun p : ℂ × ℂ => ‖p.1 - p.2‖, by fun_prop⟩,
    { self_eq_zero := fun x => by simp
      eq_of_eq_zero := fun x y h => sub_eq_zero.mp (norm_eq_zero.mp h)
      symm := fun x y => norm_sub_rev x y
      triangle := fun x y z => norm_sub_le_norm_sub_add_norm_sub x y z
      euclidean_of_small := fun _ ε hε => ⟨ε, hε, fun _ h => h⟩ }⟩

instance : Nonempty ContMetric := ⟨euclidContMetric⟩

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {U : TopologicalSpace.Opens ℂ} {h : Ω → DistOn U} {D : Ω → ContMetric}

end LQGMetric
