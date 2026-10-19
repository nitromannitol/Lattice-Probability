/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/IndependentCoordinatePairs.lean, BouRabeeGwynne/BrownianWeakMarkov.lean,
BouRabeeGwynne/BrownianLawUniqueness.lean.
-/

import LatticeProb.Prob.BrownianPathSpace
import LatticeProb.Topology.ContinuousMapBorel
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Probability.HasLaw

/-!
# Future increments and uniqueness of the standard Brownian law on path space

Regrouping independent coordinate pairs shows that the complete vector-valued future increment
process at a deterministic time is independent of the complete vector-valued past of the path.
A standard Brownian law on continuous Euclidean paths is determined by its finite-dimensional
coordinate marginals, so it is unique. Consequently it is invariant under deterministic time
shifts of the path.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb

/-- If the pairs `(f i ω, g i ω)` are independent across the index `i`, and within each pair
`f i` and `g i` are independent, then the vector of first components is independent of the
vector of second components. -/
theorem indepFun_vectors_of_independent_coordinate_pairs
    {ι Ω X Y : Type*} [Fintype ι] [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : ι → Ω → X} {g : ι → Ω → Y}
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hpairs : iIndepFun (fun i ω ↦ (f i ω, g i ω)) μ)
    (hwithin : ∀ i, IndepFun (f i) (g i) μ) :
    IndepFun (fun ω i ↦ f i ω) (fun ω i ↦ g i ω) μ := by
  letI (i : ι) : IsProbabilityMeasure (μ.map (f i)) :=
    (Measure.isProbabilityMeasure_map_iff (hf i).aemeasurable).mpr inferInstance
  letI (i : ι) : IsProbabilityMeasure (μ.map (g i)) :=
    (Measure.isProbabilityMeasure_map_iff (hg i).aemeasurable).mpr inferInstance
  have hflaw (i : ι) : HasLaw (f i) (μ.map (f i)) μ := ⟨(hf i).aemeasurable, rfl⟩
  have hglaw (i : ι) : HasLaw (g i) (μ.map (g i)) μ := ⟨(hg i).aemeasurable, rfl⟩
  have hpairlaw (i : ι) : HasLaw (fun ω ↦ (f i ω, g i ω))
      ((μ.map (f i)).prod (μ.map (g i))) μ :=
    (hwithin i).hasLaw_prod (hflaw i) (hglaw i)
  have hflaws : HasLaw (fun ω i ↦ f i ω) (Measure.pi fun i ↦ μ.map (f i)) μ :=
    (hpairs.comp (fun _ ↦ Prod.fst) (fun _ ↦ measurable_fst)).hasLaw_pi hflaw
  have hglaws : HasLaw (fun ω i ↦ g i ω) (Measure.pi fun i ↦ μ.map (g i)) μ :=
    (hpairs.comp (fun _ ↦ Prod.snd) (fun _ ↦ measurable_snd)).hasLaw_pi hglaw
  apply (indepFun_iff_hasLaw_prodMk_prod hflaws hglaws).mpr
  exact (measurePreserving_arrowProdEquivProdArrow X Y ι
    (fun i ↦ μ.map (f i)) (fun i ↦ μ.map (g i))).hasLaw.comp
      (hpairs.hasLaw_pi hpairlaw)

/-- The increment of the path `ω` after time `t`, `s ↦ ω (t + s) - ω t`, as a continuous path
starting at zero. -/
def shiftedBrownianPath {d : ℕ} (t : ℝ≥0)
    (ω : BrownianPath d) : BrownianPath d where
  toFun s := ω (t + s) - ω t
  continuous_toFun := by fun_prop

/-- For a fixed time `t`, the map `ω ↦ shiftedBrownianPath t ω` is measurable for the Borel
sigma-algebra on paths. -/
lemma measurable_shiftedBrownianPath {d : ℕ} (t : ℝ≥0) :
    Measurable (shiftedBrownianPath (d := d) t) := by
  apply LatticeProb.ContinuousMapBorel.ContinuousMap.measurable_iff_eval.mpr
  intro s
  change Measurable (fun ω : BrownianPath d ↦ ω (t + s) - ω t)
  fun_prop

/-- Under the exact standard Brownian-law predicate, the complete future
increment process at a deterministic time is independent of the entire past. -/
theorem standardBrownianLaw_indepFun_shift {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0) :
    IndepFun (fun (ω : BrownianPath d) (s : ℝ≥0) ↦ ω (t + s) - ω t)
      (fun (ω : BrownianPath d) (s : Set.Iic t) ↦ ω s) μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  let f : Fin d → BrownianPath d → (ℝ≥0 → ℝ) :=
    fun i ω s ↦ ω (t + s) i - ω t i
  let g : Fin d → BrownianPath d → (Set.Iic t → ℝ) :=
    fun i ω s ↦ ω s i
  have hf (i : Fin d) : Measurable (f i) := by dsimp [f]; fun_prop
  have hg (i : Fin d) : Measurable (g i) := by
    apply measurable_pi_iff.mpr
    intro s
    exact (by fun_prop : Continuous (fun ω : BrownianPath d ↦ ω (s : ℝ≥0) i)).measurable
  have hpairs : iIndepFun (fun i ω ↦ (f i ω, g i ω)) μ :=
    hμ.2.2.comp
      (fun (_ : Fin d) (b : ℝ≥0 → ℝ) ↦
        ((fun s : ℝ≥0 ↦ b (t + s) - b t), (fun s : Set.Iic t ↦ b s)))
      (by intro i; fun_prop)
  have hwithin (i : Fin d) : IndepFun (f i) (g i) μ :=
    (hμ.2.1 i).toIsPreBrownianReal.indepFun_shift t
  have hvec := indepFun_vectors_of_independent_coordinate_pairs hf hg hpairs hwithin
  let assembleFuture : (Fin d → ℝ≥0 → ℝ) → (ℝ≥0 → Euc d) :=
    fun b s ↦ WithLp.toLp 2 (fun i ↦ b i s)
  let assemblePast : (Fin d → Set.Iic t → ℝ) → (Set.Iic t → Euc d) :=
    fun b s ↦ WithLp.toLp 2 (fun i ↦ b i s)
  have hmF : Measurable assembleFuture := by
    apply measurable_pi_lambda
    intro s
    exact (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).measurable.comp (by fun_prop)
  have hmP : Measurable assemblePast := by
    apply measurable_pi_lambda
    intro s
    exact (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).measurable.comp (by fun_prop)
  exact hvec.comp hmF hmP

/-- Each coordinate of a Brownian path, viewed as a function `ℝ≥0 → ℝ`, is a measurable
function of the path. -/
lemma measurable_brownianCoordinatePath {d : ℕ} (i : Fin d) :
    Measurable (fun (ω : BrownianPath d) (t : ℝ≥0) ↦ ω t i) := by
  apply measurable_pi_iff.mpr
  intro t
  exact (by fun_prop : Continuous (fun ω : BrownianPath d ↦ ω t i)).measurable

/-- All coordinates of a Brownian path, viewed as a function `Fin d → ℝ≥0 → ℝ`, form a
measurable function of the path. -/
lemma measurable_brownianCoordinates {d : ℕ} :
    Measurable (fun (ω : BrownianPath d) (i : Fin d) (t : ℝ≥0) ↦ ω t i) :=
  measurable_pi_iff.mpr measurable_brownianCoordinatePath

/-- The Borel sigma-algebra on paths is the one induced by the coordinate map to
`Fin d → ℝ≥0 → ℝ`. -/
private lemma measurableSpace_brownianPath_eq_comap {d : ℕ} :
    (inferInstance : MeasurableSpace (BrownianPath d)) =
      MeasurableSpace.comap (fun (ω : BrownianPath d) (i : Fin d) (t : ℝ≥0) ↦ ω t i)
        inferInstance := by
  let raw := fun (ω : BrownianPath d) (i : Fin d) (t : ℝ≥0) ↦ ω t i
  have hraw : Measurable raw := measurable_brownianCoordinates
  apply le_antisymm ?_ hraw.comap_le
  change (LatticeProb.continuousMapMeasurableSpace : MeasurableSpace C(ℝ≥0, Euc d)) ≤
    MeasurableSpace.comap raw inferInstance
  rw [LatticeProb.ContinuousMapBorel.ContinuousMap.measurableSpace_eq_iSup_comap_eval]
  refine iSup_le fun t ↦ ?_
  have heval : Measurable[MeasurableSpace.comap raw inferInstance]
      (fun ω : BrownianPath d ↦ ω t) := by
    letI : MeasurableSpace (BrownianPath d) := MeasurableSpace.comap raw inferInstance
    have hcoords : Measurable (fun (ω : BrownianPath d) (i : Fin d) ↦ ω t i) :=
      (show Measurable (fun (b : Fin d → ℝ≥0 → ℝ) (i : Fin d) ↦ b i t) by
        fun_prop).comp (comap_measurable raw)
    exact (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).measurable.comp hcoords
  exact heval.comap_le

/-- Two measures on a space whose sigma-algebra is the pullback along a measurable map `f` are
equal when their pushforwards along `f` agree. -/
private lemma measure_eq_of_map_eq_of_comap {X Y : Type*}
    [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {f : X → Y}
    (hgen : mX = mY.comap f) (hf : Measurable f) {μ ν : Measure X}
    (heq : μ.map f = ν.map f) : μ = ν := by
  ext s hs
  have hs' : MeasurableSet[mY.comap f] s := hgen ▸ hs
  obtain ⟨t, ht, rfl⟩ := hs'
  simpa only [Measure.map_apply hf ht] using congrArg (fun ρ : Measure Y ↦ ρ t) heq

/-- The law of the `i`-th coordinate process of a standard Brownian law has the centered
Gaussian projective family of Brownian motion as its finite-dimensional marginals. -/
private lemma standardBrownianLaw_coordinate_isProjectiveLimit {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (i : Fin d) :
    IsProjectiveLimit (μ.map (fun ω t ↦ ω t i)) BrownianReal.projectiveFamily := by
  intro I
  rw [Measure.map_map I.measurable_restrict (measurable_brownianCoordinatePath i)]
  exact ((hμ.2.1 i).hasLaw I).map_eq

/-- The exact standard Brownian predicate determines a unique probability law
on the actual continuous Euclidean path space. -/
theorem standardBrownianLaw_unique {d : ℕ} {μ ν : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) (hν : IsStandardBrownianLaw ν) : μ = ν := by
  apply measure_eq_of_map_eq_of_comap measurableSpace_brownianPath_eq_comap
    measurable_brownianCoordinates
  rw [hμ.2.2.map_fun_eq_pi_map (fun i ↦ (measurable_brownianCoordinatePath i).aemeasurable),
    hν.2.2.map_fun_eq_pi_map (fun i ↦ (measurable_brownianCoordinatePath i).aemeasurable)]
  congr 1
  funext i
  exact (standardBrownianLaw_coordinate_isProjectiveLimit hμ i).unique
    (standardBrownianLaw_coordinate_isProjectiveLimit hν i)

/-- The time-shifted path law of a standard Brownian law is again a standard Brownian law. -/
lemma standardBrownianLaw_shift {d : ℕ} {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0) :
    IsStandardBrownianLaw (μ.map (shiftedBrownianPath t)) := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hprob : IsProbabilityMeasure (μ.map (shiftedBrownianPath t)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_shiftedBrownianPath t).aemeasurable).mpr
      inferInstance
  letI := hprob
  refine ⟨hprob, fun i ↦ ?_, ?_⟩
  · refine { toIsPreBrownianReal := ?_, cont := ?_ }
    · constructor
      intro I
      have hm : Measurable (fun ω : BrownianPath d ↦ I.restrict (fun s ↦ ω s i)) :=
        I.measurable_restrict.comp (measurable_brownianCoordinatePath i)
      refine ⟨hm.aemeasurable, ?_⟩
      rw [Measure.map_map hm (measurable_shiftedBrownianPath t)]
      exact (((hμ.2.1 i).shift t).hasLaw I).map_eq
    · exact Filter.Eventually.of_forall fun ω ↦ by fun_prop
  · have hind := hμ.2.2.comp
      (fun (_ : Fin d) (b : ℝ≥0 → ℝ) ↦ fun s : ℝ≥0 ↦ b (t + s) - b t)
      (by intro i; fun_prop)
    rw [iIndepFun_iff_map_fun_eq_pi_map
      (fun i ↦ (measurable_brownianCoordinatePath i).aemeasurable)]
    rw [Measure.map_map measurable_brownianCoordinates (measurable_shiftedBrownianPath t)]
    simp_rw [Measure.map_map (measurable_brownianCoordinatePath _)
      (measurable_shiftedBrownianPath t)]
    exact hind.map_fun_eq_pi_map (fun i ↦
      ((measurable_brownianCoordinatePath i).comp
        (measurable_shiftedBrownianPath t)).aemeasurable)

/-- A deterministic future increment has exactly the same continuous-path law
as the original Brownian path. -/
theorem standardBrownianLaw_map_shift {d : ℕ} {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0) :
    μ.map (shiftedBrownianPath t) = μ :=
  standardBrownianLaw_unique (standardBrownianLaw_shift hμ t) hμ

namespace BrownianWeakMarkovPathExample

/-- The uniqueness theorem applied to two given standard Brownian laws. -/
theorem standardBrownianLaw_unique_of_laws {d : ℕ} (μ ν : Measure (BrownianPath d))
    (hμ : IsStandardBrownianLaw μ) (hν : IsStandardBrownianLaw ν) : μ = ν :=
  standardBrownianLaw_unique hμ hν

/-- The shift invariance applied to a given standard Brownian law and a time `t`. -/
theorem standardBrownianLaw_map_shift_of_law {d : ℕ} (μ : Measure (BrownianPath d))
    (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0) :
    μ.map (shiftedBrownianPath t) = μ :=
  standardBrownianLaw_map_shift hμ t

/-- The shifted path map at the concrete time `1` is measurable. -/
theorem measurable_shiftedBrownianPath_one (d : ℕ) :
    Measurable (shiftedBrownianPath (d := d) (1 : ℝ≥0)) :=
  measurable_shiftedBrownianPath 1

end BrownianWeakMarkovPathExample

end LatticeProb
