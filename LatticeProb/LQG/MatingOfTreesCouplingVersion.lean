import LatticeProb.LQG.MatingOfTreesCouplingCongr
import LatticeProb.Gauss.BrownianCont

/-!
# A regular version of a mating-of-trees coupling

The Brownian coordinates of a mating-of-trees coupling are only required to have almost surely
continuous paths, and its uniform variable is not required to be measurable. This file replaces
them by versions with every path continuous and every coordinate measurable, almost surely equal to
the given ones, and checks that the result is again a mating-of-trees coupling. The Brownian
coordinates of the regular version are measurable random elements of `C(ℝ≥0, ℝ)`.

## Main results

* `ae_forall_eq_of_modification`: modifications with almost surely continuous paths are
  indistinguishable.
* `exists_continuous_version_of_isBrownianReal`: a standard Brownian motion has a version with
  every path continuous and measurable coordinates.
* `measurable_continuousMap_of_forall`: such a process is a measurable random element of
  `C(ℝ≥0, ℝ)`.
* `IsMatingOfTreesCoupling.aemeasurable_U`: the uniform variable is almost everywhere measurable.
* `IsMatingOfTreesCoupling.exists_regular_version`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- Two processes with almost surely continuous paths which are modifications of each other have
almost surely equal paths. -/
theorem ae_forall_eq_of_modification {B C : ℝ≥0 → Ω → ℝ}
    (hB : ∀ᵐ ω ∂P, Continuous fun t => B t ω) (hC : ∀ᵐ ω ∂P, Continuous fun t => C t ω)
    (hmod : ∀ t, B t =ᵐ[P] C t) : ∀ᵐ ω ∂P, ∀ t, B t ω = C t ω := by
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hs : ∀ᵐ ω ∂P, ∀ t ∈ s, B t ω = C t ω := (ae_ball_iff hsc).2 fun t _ => hmod t
  filter_upwards [hB, hC, hs] with ω h1 h2 h3
  intro t
  exact congrFun (Continuous.ext_on hsd h1 h2 fun t ht => h3 t ht) t

open Classical in
/-- **Continuous version of a Brownian motion.** A standard Brownian motion has a version with
every path continuous and every coordinate measurable, whose paths are almost surely those of the
given motion. -/
theorem exists_continuous_version_of_isBrownianReal {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∃ C : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => C t ω) ∧ (∀ t, Measurable (C t)) ∧
      ∀ᵐ ω ∂P, ∀ t, C t ω = B t ω := by
  have hBa : ∀ t, AEMeasurable (B t) P := hB.toIsPreBrownianReal.aemeasurable
  have hB₁m : ∀ t, Measurable ((hBa t).mk (B t)) := fun t => (hBa t).measurable_mk
  have hBB₁ : ∀ t, B t =ᵐ[P] (hBa t).mk (B t) := fun t => (hBa t).ae_eq_mk
  obtain ⟨C₁, hC₁m, hmod, hC₁⟩ :=
    LatticeProb.exists_isBrownianReal_modification (hB.toIsPreBrownianReal.congr hBB₁) hB₁m
  have hpath : ∀ᵐ ω ∂P, ∀ t, B t ω = C₁ t ω :=
    ae_forall_eq_of_modification hB.cont hC₁.cont fun t => (hBB₁ t).trans (hmod t)
  set N : Set Ω := toMeasurable P {ω | ¬ Continuous fun t => C₁ t ω} with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : P N = 0 := by
    rw [hN, measure_toMeasurable]
    exact ae_iff.1 hC₁.cont
  have hNc : ∀ᵐ ω ∂P, ω ∉ N := ae_iff.2 (by simpa only [not_not, Set.ofPred_mem_eq] using hN0)
  refine ⟨fun t ω => if ω ∈ N then 0 else C₁ t ω, fun ω => ?_, fun t => ?_, ?_⟩
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
      exact continuous_const
    · simp only [hω, ↓reduceIte]
      by_contra hc
      exact hω (subset_toMeasurable P _ hc)
  · exact Measurable.ite hNm measurable_const (hC₁m t)
  · filter_upwards [hNc, hpath] with ω h1 h2 t
    simp only [h1, ↓reduceIte]
    exact (h2 t).symm

/-- A process with every path continuous and measurable coordinates is a measurable random
element of `C(ℝ≥0, ℝ)`. -/
theorem measurable_continuousMap_of_forall {C : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, Continuous fun t => C t ω) (hm : ∀ t, Measurable (C t)) :
    Measurable fun ω => (⟨fun t => C t ω, hc ω⟩ : C(ℝ≥0, ℝ)) :=
  ContinuousMap.measurable_iff_eval.2 hm

variable {γ : ℝ} {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The uniform variable of a mating-of-trees coupling is almost everywhere measurable: its law is
the uniform law on an interval, which has no atom. -/
theorem IsMatingOfTreesCoupling.aemeasurable_U
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) : AEMeasurable U P := by
  have := hC.isProbabilityMeasure
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x : ℝ, P.map U = Measure.dirac x :=
    ⟨_, Measure.map_of_not_aemeasurable_of_ne_zero hne (IsProbabilityMeasure.ne_zero P)⟩
  have h1 : (volume[|Ico (0 : ℝ) (2 * Real.pi * igChi γ)]) {x} = 0 :=
    ProbabilityTheory.cond_absolutelyContinuous Real.volume_singleton
  rw [← hC.igField.2.1, hx, Measure.dirac_apply_of_mem (Set.mem_singleton x)] at h1
  exact one_ne_zero h1

/-- **A regular version of a mating-of-trees coupling.** The four Brownian coordinates can be
replaced by versions with every path continuous and every coordinate measurable, and the uniform
variable by a measurable version, each almost surely equal to the given one; the result is again a
mating-of-trees coupling with the same fields and curves. -/
theorem IsMatingOfTreesCoupling.exists_regular_version
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∃ (Bn Bn' B₀n B₀n' : ℝ≥0 → Ω → ℝ) (Un : Ω → ℝ),
      IsMatingOfTreesCoupling γ P X X₀ hIG₀ Bn Bn' B₀n B₀n' Un ηL η η₀ bm ∧
      (∀ ω, Continuous fun t => Bn t ω) ∧ (∀ ω, Continuous fun t => Bn' t ω) ∧
      (∀ ω, Continuous fun t => B₀n t ω) ∧ (∀ ω, Continuous fun t => B₀n' t ω) ∧
      (∀ t, Measurable (Bn t)) ∧ (∀ t, Measurable (Bn' t)) ∧ (∀ t, Measurable (B₀n t)) ∧
      (∀ t, Measurable (B₀n' t)) ∧ Measurable Un ∧
      (∀ᵐ ω ∂P, (∀ t, Bn t ω = B t ω) ∧ (∀ t, Bn' t ω = B' t ω) ∧ (∀ t, B₀n t ω = B₀ t ω) ∧
        (∀ t, B₀n' t ω = B₀' t ω) ∧ Un ω = U ω) := by
  obtain ⟨C, hCc, hCm, hCe⟩ := exists_continuous_version_of_isBrownianReal hC.bm_B
  obtain ⟨C', hC'c, hC'm, hC'e⟩ := exists_continuous_version_of_isBrownianReal hC.bm_B'
  obtain ⟨C₀, hC₀c, hC₀m, hC₀e⟩ := exists_continuous_version_of_isBrownianReal hC.bm_B₀
  obtain ⟨C₀', hC₀'c, hC₀'m, hC₀'e⟩ := exists_continuous_version_of_isBrownianReal hC.bm_B₀'
  have hU := hC.aemeasurable_U
  have hUe : ∀ᵐ ω ∂P, hU.mk U ω = U ω := hU.ae_eq_mk.mono fun _ h => h.symm
  refine ⟨C, C', C₀, C₀', hU.mk U, ?_, hCc, hC'c, hC₀c, hC₀'c, hCm, hC'm, hC₀m, hC₀'m,
    hU.measurable_mk, ?_⟩
  · exact hC.congr_ae hC.gff.measurable hC.gff₀.measurable hC.igField.1.1.measurable
      hC.measurable_curves.1 hC.measurable_curves.2.1 hC.measurable_curves.2.2.1
      hC.measurable_curves.2.2.2 (ae_of_all _ fun _ => rfl) (ae_of_all _ fun _ => rfl)
      (ae_of_all _ fun _ => rfl) hCe hC'e hC₀e hC₀'e hUe (ae_of_all _ fun _ => rfl)
      (ae_of_all _ fun _ => rfl) (ae_of_all _ fun _ => rfl) (ae_of_all _ fun _ => rfl)
  · filter_upwards [hCe, hC'e, hC₀e, hC₀'e, hUe] with ω h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩

end MatedCRT

end MatedCRTHarmonic
