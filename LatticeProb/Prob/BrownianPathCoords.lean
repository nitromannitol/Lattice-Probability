module

public import LatticeProb.Prob.BrownianContAll
public import LatticeProb.Prob.BrownianPathSpace
public import LatticeProb.Prob.BrownianPathMap
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-!
# Continuous versions of Brownian motion on `ℝ ^ d` and their law on path space

A Brownian motion on `ℝ ^ d` whose paths are only almost surely continuous has a version with
every path continuous. Each coordinate `√d (B · i − x i)` is a real Brownian motion, so it has
a version with everywhere continuous paths; these versions assemble into a vector process `C`
with `C t = √d • (B t − x)` almost surely.

Pushing the law of `C` forward along the sample-path map `pathMap C` gives a probability measure
on the Brownian path space `BrownianPath d` under which the coordinate processes are independent
real Brownian motions, that is, a standard Brownian law (`IsStandardBrownianLaw`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- A real Brownian motion has a version with every path continuous, which agrees with it
at each time almost surely. -/
theorem IsBrownianReal.exists_continuous_indistinguishable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} (hX : IsBrownianReal X P) :
    ∃ D : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (D t)) ∧ IsBrownianReal D P ∧
      (∀ᵐ ω ∂P, ∀ t, X t ω = D t ω) ∧ ∀ ω, Continuous fun t => D t ω := by
  obtain ⟨C', hC'm, hC'B, hC'ind⟩ := exists_measurable_indistinguishable hX
  obtain ⟨D, hDm, hDmod, hDB, hDc⟩ :=
    exists_isBrownianReal_modification_all hC'B.toIsPreBrownianReal hC'm
  refine ⟨D, hDm, hDB, ?_, hDc⟩
  have hmod : ∀ t, X t =ᵐ[P] D t := fun t =>
    Filter.EventuallyEq.trans (hC'ind.mono fun ω hω => hω t) (hDmod t)
  exact ae_forall_eq_of_modification hmod hX.cont (Filter.Eventually.of_forall hDc)

/-- **A Brownian motion on `ℝ ^ d` has a version with every path continuous.** The version `C`
has measurable values at each time, continuous paths everywhere, the law `√d • (B t − x)` at
each time almost surely, and the same almost sure identity pathwise. Its coordinates are real
Brownian motions and are independent. -/
theorem IsBrownianSpace.exists_continuousVersion {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {d : ℕ} {x : EuclideanSpace ℝ (Fin d)} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hB : IsBrownianSpace d x B P) :
    ∃ C : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d),
      (∀ t, Measurable (C t)) ∧ (∀ ω, Continuous fun t => C t ω) ∧
      (∀ t, C t =ᵐ[P] fun ω => Real.sqrt d • (B t ω - x)) ∧
      (∀ᵐ ω ∂P, ∀ t, C t ω = Real.sqrt d • (B t ω - x)) ∧
      (∀ i : Fin d, IsBrownianReal (fun t ω => C t ω i) P) ∧
      iIndepFun (fun (i : Fin d) (ω : Ω) => fun t : ℝ≥0 => C t ω i) P := by
  choose D hDm hDB hDae hDc using fun i : Fin d =>
    IsBrownianReal.exists_continuous_indistinguishable (hB.coord i)
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d),
      ∀ t ω, C t ω = WithLp.toLp 2 (fun i => D i t ω) := ⟨_, fun _ _ => rfl⟩
  have hcoord : ∀ i t ω, C t ω i = D i t ω := fun i t ω => by rw [hCdef]
  have hae : ∀ᵐ ω ∂P, ∀ t, C t ω = Real.sqrt d • (B t ω - x) := by
    filter_upwards [ae_all_iff.2 hDae] with ω hω
    intro t
    ext i
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [hcoord]
    exact (hω i t).symm
  have hind : iIndepFun (fun (i : Fin d) (ω : Ω) => fun t : ℝ≥0 => C t ω i) P := by
    refine (iIndepFun_congr fun i => ?_).mp
      (hB.indep.comp (fun i (v : ℝ≥0 → ℝ) => fun t => Real.sqrt d * (v t - x i)) fun i => ?_)
    · filter_upwards [hDae i] with ω hω
      funext t
      rw [hcoord]
      exact hω t
    · exact measurable_pi_lambda _ fun t => ((measurable_pi_apply t).sub_const _).const_mul _
  refine ⟨C, fun t => ?_, fun ω => ?_, fun t => hae.mono fun ω hω => hω t, hae,
    fun i => ?_, hind⟩
  · have hfun : C t = (WithLp.toLp 2) ∘ fun ω i => D i t ω :=
      funext fun ω => hCdef t ω
    rw [hfun]
    exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp
      (measurable_pi_lambda _ fun i => hDm i t)
  · have hfun : (fun t => C t ω) = (WithLp.toLp 2) ∘ fun t i => D i t ω :=
      funext fun t => hCdef t ω
    rw [hfun]
    exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
      (continuous_pi fun i => hDc i ω)
  · have hfun : (fun t ω => C t ω i) = D i := funext fun t => funext fun ω => hcoord i t ω
    rw [hfun]
    exact hDB i

/-- The coordinate `γ ↦ γ t i` of a path is measurable in the path, for each time `t`
and coordinate `i`. -/
lemma measurable_pathCoord {d : ℕ} (i : Fin d) :
    Measurable fun γ : BrownianPath d => fun t : ℝ≥0 => γ t i := by
  refine measurable_pi_lambda _ fun t => ?_
  have hev : Measurable fun v : Euc d => v i := by fun_prop
  exact hev.comp (ContinuousMapBorel.ContinuousMap.measurable_eval t)

/-- **Transport of a law along a measurable map.** If `G` has law `ν` under `P` and `G = Φ ∘ F`
with `F` and `Φ` measurable, then `Φ` has law `ν` under the image measure `P.map F`. -/
lemma hasLaw_map_of_comp {Ω Γ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    [MeasurableSpace E] {P : Measure Ω} {F : Ω → Γ} {Φ : Γ → E} {G : Ω → E} {ν : Measure E}
    (hF : Measurable F) (hΦ : Measurable Φ) (hG : HasLaw G ν P) (hcomp : G = Φ ∘ F) :
    HasLaw Φ ν (P.map F) :=
  ⟨hΦ.aemeasurable, by rw [Measure.map_map hΦ hF, ← hcomp]; exact hG.map_eq⟩

/-- **The law of a continuous version of a Brownian motion on `ℝ ^ d` is a standard Brownian
law on path space.** Its image under the sample-path map is a probability measure on
`BrownianPath d` whose coordinate processes are independent real Brownian motions. -/
theorem isStandardBrownianLaw_map_pathMap {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {C : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hCm : ∀ t, Measurable (C t)) (hC : ∀ ω, Continuous fun t => C t ω)
    (hcoord : ∀ i : Fin d, IsBrownianReal (fun t ω => C t ω i) P)
    (hindep : iIndepFun (fun (i : Fin d) (ω : Ω) => fun t : ℝ≥0 => C t ω i) P) :
    IsStandardBrownianLaw (P.map (pathMap C hC)) := by
  have hF : Measurable (pathMap C hC) := measurable_pathMap C hCm hC
  have hprob : IsProbabilityMeasure (P.map (pathMap C hC)) :=
    Measure.isProbabilityMeasure_map hF.aemeasurable
  have hY := measurable_pathCoord (d := d)
  refine ⟨hprob, fun i => ?_, ?_⟩
  · have hΦ : ∀ I : Finset ℝ≥0,
        Measurable fun γ : BrownianPath d => I.restrict (fun t => γ t i) :=
      fun I => (Finset.measurable_restrict I).comp (hY i)
    refine ⟨⟨fun I => hasLaw_map_of_comp hF (hΦ I) ((hcoord i).toIsPreBrownianReal.hasLaw I)
      rfl⟩, Filter.Eventually.of_forall fun γ => ?_⟩
    exact (by fun_prop : Continuous fun v : Euc d => v i).comp γ.continuous
  · have hCi : ∀ i : Fin d, Measurable fun ω : Ω => fun t : ℝ≥0 => C t ω i := fun i =>
      measurable_pi_lambda _ fun t => (by fun_prop : Measurable fun v : Euc d => v i).comp
        (hCm t)
    have hYF : ∀ i : Fin d, (P.map (pathMap C hC)).map
        (fun γ : BrownianPath d => fun t : ℝ≥0 => γ t i) =
          P.map (fun ω => fun t => C t ω i) := fun i => Measure.map_map (hY i) hF
    have hZ : Measurable fun γ : BrownianPath d => fun i : Fin d => fun t : ℝ≥0 => γ t i :=
      measurable_pi_lambda _ fun i => hY i
    rw [iIndepFun_iff_map_fun_eq_pi_map fun i => (hY i).aemeasurable, Measure.map_map hZ hF]
    simp only [hYF]
    exact (iIndepFun_iff_map_fun_eq_pi_map fun i => (hCi i).aemeasurable).mp hindep

namespace BrownianPathCoordsExample

/-- **Nonvacuity of `IsStandardBrownianLaw` in dimension one.** There is a standard Brownian
law on the path space `BrownianPath 1`: take the continuous version of the Brownian motion on
`ℝ ^ 1` from `exists_isBrownianSpace_cont` and push its law forward along the path map. -/
theorem exists_isStandardBrownianLaw_one :
    ∃ μ : Measure (BrownianPath 1), IsStandardBrownianLaw μ := by
  obtain ⟨Ω, mΩ, P, B, hB, -, -⟩ := exists_isBrownianSpace_cont 1 0
  haveI : IsProbabilityMeasure P := hB.isProbabilityMeasure
  obtain ⟨C, hCm, hC, -, -, hcoord, hindep⟩ := hB.exists_continuousVersion
  exact ⟨P.map (pathMap C hC), isStandardBrownianLaw_map_pathMap hCm hC hcoord hindep⟩

end BrownianPathCoordsExample

end LatticeProb
