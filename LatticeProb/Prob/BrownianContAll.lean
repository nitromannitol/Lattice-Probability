/-
Brownian motion with every path continuous.

Kolmogorov-Chentsov as it is usually stated produces a modification whose ALMOST
every path is continuous, and that is what `IsBrownianReal` carries.  A statement
about the motion restarted at a random time needs more: the restarted path must
be a measurable map into path space, and that comes from the joint measurability
of `(t, ω) ↦ B t ω`, which asks for continuity in `t` for EVERY `ω`.

The library already proves Kolmogorov-Chentsov with every path continuous for a
process indexed by `Fin k → ℝ`, by setting the chained limit to zero off the
measurable set where the dyadic increment bounds hold from some level on.  A
process indexed by `ℝ≥0` is carried to one indexed by `Fin 1 → ℝ` along
`z ↦ X (Real.toNNReal (z 0))`; the Kolmogorov condition survives because
`Real.toNNReal` does not increase distances and the distance on `Fin 1 → ℝ` is the
distance of the single coordinate.  Reading the modification back at
`z = fun _ => t` gives a modification of the original process whose every path is
continuous, because `t ↦ (fun _ => (t : ℝ))` is continuous.

The consequence is that the hypotheses of the strong Markov property are not
vacuous: `exists_isBrownianSpace_cont` produces, for every dimension and every
starting point, a Brownian motion on `ℝ ^ d` whose values are measurable at each
time and whose every path is continuous.
-/
import Mathlib
import LatticeProb.Prob.ChentsovPiModification
import LatticeProb.Gauss.BrownianCont
import LatticeProb.Prob.BrownianExit
import LatticeProb.Prob.BrownianStrongMarkov

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem edist_toNNReal_le (a b : ℝ) :
    edist (Real.toNNReal a) (Real.toNNReal b) ≤ edist a b := by
  rw [edist_dist, edist_dist]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [NNReal.dist_eq, Real.dist_eq, Real.coe_toNNReal', Real.coe_toNNReal']
  exact abs_max_sub_max_le_abs a b 0

/-- **Kolmogorov-Chentsov on `ℝ≥0`, with every path continuous.** -/
theorem exists_continuous_modification_all [IsProbabilityMeasure P] {p q : ℝ} {M : ℝ≥0}
    {X : ℝ≥0 → Ω → ℝ} (hX : IsKolmogorovProcess X P p q M) (hq : 1 < q) :
    ∃ Y : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (Y t)) ∧ (∀ t, X t =ᵐ[P] Y t) ∧
      ∀ ω, Continuous fun t => Y t ω := by
  have hK : IsKolmogorovProcess (fun z : Fin 1 → ℝ => X (Real.toNNReal (z 0))) P p q M := by
    refine ⟨fun s t => hX.measurablePair _ _, fun s t => ?_, hX.p_pos, hX.q_pos⟩
    refine le_trans (hX.kolmogorovCondition _ _) ?_
    have hle : edist (Real.toNNReal (s 0)) (Real.toNNReal (t 0)) ≤ edist s t :=
      le_trans (edist_toNNReal_le _ _) (edist_le_pi_edist s t 0)
    gcongr
  obtain ⟨Y', hY'm, hY'mod, hY'cont⟩ :=
    exists_continuous_modification_pi_all hK (by simpa using hq)
  refine ⟨fun t ω => Y' (fun _ => (t : ℝ)) ω, fun t => hY'm _, fun t => ?_, fun ω => ?_⟩
  · have h := hY'mod (fun _ => (t : ℝ))
    simpa using h
  · exact (hY'cont ω).comp (by fun_prop : Continuous fun t : ℝ≥0 => (fun _ : Fin 1 => (t : ℝ)))

/-- **A pre-Brownian motion has a Brownian modification with EVERY path continuous.** -/
theorem exists_isBrownianReal_modification_all {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t)) :
    ∃ C : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (C t)) ∧ (∀ t, B t =ᵐ[P] C t) ∧ IsBrownianReal C P ∧
      ∀ ω, Continuous fun t => C t ω := by
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨C, hCm, hmod, hcont⟩ :=
    exists_continuous_modification_all (isKolmogorovProcess_of_isPreBrownianReal hB hm)
      (by norm_num)
  exact ⟨C, hCm, hmod,
    { toIsPreBrownianReal := hB.congr hmod, cont := Filter.Eventually.of_forall hcont }, hcont⟩

/-- **A real Brownian motion with every path continuous exists.** -/
theorem exists_isBrownianReal_cont :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @MeasureTheory.Measure Ω mΩ)
      (B : ℝ≥0 → Ω → ℝ), (∀ t, @Measurable Ω ℝ mΩ _ (B t)) ∧ @IsBrownianReal Ω mΩ B P ∧
      ∀ ω, Continuous fun t => B t ω := by
  obtain ⟨C, hCm, -, hC, hcont⟩ := exists_isBrownianReal_modification_all
    isPreBrownianReal_brownianOf (fun t => measurable_whiteNoise _ _)
  exact ⟨_, inferInstance, whiteNoiseLaw (volume : Measure ℝ), C, hCm, hC, hcont⟩

/-- **A Brownian motion on `ℝ ^ d` with measurable values and EVERY path continuous exists.**
This is what makes the hypotheses of the strong Markov property non-vacuous. -/
theorem exists_isBrownianSpace_cont (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @MeasureTheory.Measure Ω mΩ)
      (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)),
      @IsBrownianSpace Ω mΩ d x B P ∧
      (∀ t, @MeasureTheory.StronglyMeasurable _ _ _ mΩ (B t)) ∧
      ∀ ω, Continuous fun t => B t ω := by
  obtain ⟨Ω₀, mΩ₀, P₀, C, hCm, hC, hCcont⟩ := exists_isBrownianReal_cont
  haveI : IsProbabilityMeasure P₀ := hC.isGaussianProcess.isProbabilityMeasure
  refine ⟨Fin d → Ω₀, inferInstance, Measure.pi fun _ => P₀, dimBrownian d C x,
    ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · have hzero : ∀ i : Fin d, ∀ᵐ ω ∂(Measure.pi fun _ : Fin d => P₀), C 0 (ω i) = 0 := fun i =>
      (measurePreserving_eval (fun _ : Fin d => P₀) i).quasiMeasurePreserving.ae
        hC.eval_zero_ae_eq_zero
    rw [← ae_all_iff] at hzero
    filter_upwards [hzero] with ω hω
    ext i
    simp [dimBrownian, hω i]
  · intro i
    have hd : (0 : ℝ) < d := by
      have := i.pos
      exact_mod_cast this
    have hsq : Real.sqrt d * (Real.sqrt d)⁻¹ = 1 :=
      mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr hd)
    have hfun : (fun (t : ℝ≥0) (ω : Fin d → Ω₀) =>
        Real.sqrt d * (dimBrownian d C x t ω i - x i)) = fun t ω => C t (ω i) := by
      funext t ω
      show Real.sqrt d * (x i + (Real.sqrt d)⁻¹ * C t (ω i) - x i) = C t (ω i)
      rw [add_sub_cancel_left, ← mul_assoc, hsq, one_mul]
    rw [hfun]
    exact isBrownianReal_comp_eval hC i
  · have hrw : (fun (i : Fin d) (ω : Fin d → Ω₀) => fun t : ℝ≥0 => dimBrownian d C x t ω i)
        = fun (i : Fin d) (ω : Fin d → Ω₀) =>
          (fun ω₀ : Ω₀ => fun t : ℝ≥0 => x i + (Real.sqrt d)⁻¹ * C t ω₀) (ω i) := rfl
    rw [hrw]
    exact iIndepFun_pi fun i =>
      (measurable_pi_lambda _ fun t => (hCm t).const_mul _ |>.const_add _).aemeasurable
  · intro t
    refine Measurable.stronglyMeasurable ?_
    refine ((EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable).comp ?_
    exact measurable_pi_lambda _ fun i =>
      ((hCm t).comp (measurable_pi_apply i)).const_mul _ |>.const_add _
  · intro ω
    rw [continuous_induced_rng]
    refine continuous_pi fun i => ?_
    exact ((hCcont (ω i)).const_mul _).const_add _

/-- **The hypotheses of the strong Markov property are not vacuous**: for every dimension and
every starting point there is a Brownian motion on `ℝ ^ d` that satisfies them, and therefore a
motion whose restart at a stopping time is the centred motion, independent of the past. -/
theorem exists_hasStrongMarkovRestart (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @MeasureTheory.Measure Ω mΩ)
      (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
      (hm : ∀ t, @MeasureTheory.StronglyMeasurable _ _ _ mΩ (B t)),
      @IsBrownianSpace Ω mΩ d x B P ∧
      @HasStrongMarkovRestart Ω mΩ d B P (@natFiltration Ω mΩ d B hm) := by
  obtain ⟨Ω, mΩ, P, B, hB, hm, hcont⟩ := exists_isBrownianSpace_cont d x
  exact ⟨Ω, mΩ, P, B, hm, hB, hB.hasStrongMarkovRestart hm hcont⟩

end LatticeProb

end
