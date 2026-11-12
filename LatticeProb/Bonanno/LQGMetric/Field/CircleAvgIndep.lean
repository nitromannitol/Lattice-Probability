/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.CircleAvgIndep at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgProc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Almost sure limits of centred Gaussian processes (task P2-DFA7b)

If `Yₙ : T → Ω → ℝ` are centred Gaussian processes and `Yₙ t → Y t` almost surely for each `t`,
then `Y` is a centred Gaussian process (`isGaussianProcess_of_ae_tendsto`) and the covariances
converge (`tendsto_covariance_of_ae_tendsto`). This is the argument of
`CircleAvg.isGaussianProcess_incProc` / `CircleAvg.covariance_cInc` (Duplantier–Sheffield,
arXiv:0808.1560 §3.1) for an arbitrary index set: every linear functional of a finite subfamily is
an a.s. limit of centred Gaussians, hence centred Gaussian (`exists_gaussianReal_of_ae_tendsto`),
with the limit variance; covariances follow by polarization (`variance_add`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace LQGMetric
namespace CircleAvgIndep

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- a.s. limits of centred Gaussians: centred Gaussian, and the variances converge -/
theorem gaussian_of_ae_tendsto {Y : ℕ → Ω → ℝ} {Z : Ω → ℝ} (hY : ∀ n, HasGaussianLaw (Y n) P)
    (hc : ∀ n, P[Y n] = 0) (hZ : AEMeasurable Z P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω))) :
    HasGaussianLaw Z P ∧ P[Z] = 0 ∧ Tendsto (fun n => Var[Y n; P]) atTop (𝓝 Var[Z; P]) := by
  have hmap : ∀ n, P.map (Y n) = gaussianReal 0 (Var[Y n; P]).toNNReal := fun n => by
    rw [(hY n).map_eq_gaussianReal, hc]
  obtain ⟨V, hV, hZmap⟩ := exists_gaussianReal_of_ae_tendsto (fun n => (hY n).aemeasurable) hZ
    hmap hlim
  have hG : HasGaussianLaw Z P := ⟨hZ, by rw [hZmap]; infer_instance⟩
  refine ⟨hG, ?_, ?_⟩
  · have := integral_map (f := fun x : ℝ => x) hZ aestronglyMeasurable_id
    rw [hZmap, integral_id_gaussianReal] at this
    exact this.symm
  · rw [(CircleAvg.gaussianReal_facts hZ hZmap).1]
    exact hV.congr fun n => Real.coe_toNNReal _ (variance_nonneg _ _)

/-- **a.s. limits of centred Gaussian processes are centred Gaussian processes** -/
theorem isGaussianProcess_of_ae_tendsto {T : Type*} {Yn : ℕ → T → Ω → ℝ} {Y : T → Ω → ℝ}
    (hG : ∀ n, IsGaussianProcess (Yn n) P) (hc : ∀ n t, P[Yn n t] = 0)
    (hm : ∀ t, Measurable (Y t))
    (hlim : ∀ t, ∀ᵐ ω ∂P, Tendsto (fun n => Yn n t ω) atTop (𝓝 (Y t ω))) :
    IsGaussianProcess Y P := by
  classical
  refine ⟨fun I => ?_⟩
  set X : Ω → (I → ℝ) := fun ω => I.restrict (Y · ω)
  have hXm : Measurable X := measurable_pi_iff.mpr fun i => hm i.1
  refine ⟨hXm.aemeasurable, isGaussian_of_map_eq_gaussianReal fun L => ?_⟩
  rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable
    hXm.aemeasurable]
  set Xn : ℕ → Ω → (I → ℝ) := fun n ω => I.restrict (Yn n · ω)
  have hGn : ∀ n, HasGaussianLaw (fun ω => L (Xn n ω)) P := fun n =>
    ((hG n).hasGaussianLaw I).map_fun L
  have hmean : ∀ n, P[fun ω => L (Xn n ω)] = 0 := by
    intro n
    have e : ∀ ω, L (Xn n ω) = ∑ i : I, Xn n ω i * L (fun j => if i = j then 1 else 0) := by
      intro ω
      have := LinearMap.pi_apply_eq_sum_univ L.toLinearMap (Xn n ω)
      simpa [smul_eq_mul] using this
    simp_rw [e]
    rw [integral_finsetSum _ fun i _ =>
      ((((hG n).hasGaussianLaw_eval i.1).integrable).mul_const _)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_mul_const]
    simp only [Xn, Finset.restrict]
    rw [hc, zero_mul]
  have hall : ∀ᵐ ω ∂P, ∀ i : I, Tendsto (fun n => Yn n i.1 ω) atTop (𝓝 (Y i.1 ω)) := by
    rw [ae_all_iff]
    exact fun i => hlim i.1
  have hl : ∀ᵐ ω ∂P, Tendsto (fun n => L (Xn n ω)) atTop (𝓝 (L (X ω))) := by
    filter_upwards [hall] with ω hω
    exact (L.continuous.tendsto _).comp (tendsto_pi_nhds.mpr hω)
  obtain ⟨hGZ, hZ0, -⟩ := gaussian_of_ae_tendsto hGn hmean
    (L.continuous.measurable.comp hXm).aemeasurable hl
  refine ⟨0, Var[fun ω => L (X ω); P].toNNReal, ?_⟩
  have := hGZ.map_eq_gaussianReal
  rw [hZ0] at this
  exact this

/-- **covariances converge along a.s. limits of centred Gaussian processes** -/
theorem tendsto_covariance_of_ae_tendsto {T : Type*} {Yn : ℕ → T → Ω → ℝ} {Y : T → Ω → ℝ}
    (hG : ∀ n, IsGaussianProcess (Yn n) P) (hc : ∀ n t, P[Yn n t] = 0)
    (hm : ∀ t, Measurable (Y t))
    (hlim : ∀ t, ∀ᵐ ω ∂P, Tendsto (fun n => Yn n t ω) atTop (𝓝 (Y t ω))) (s t : T) :
    Tendsto (fun n => cov[Yn n s, Yn n t; P]) atTop (𝓝 cov[Y s, Y t; P]) := by
  have hGs : ∀ n, HasGaussianLaw (Yn n s) P := fun n => (hG n).hasGaussianLaw_eval s
  have hGt : ∀ n, HasGaussianLaw (Yn n t) P := fun n => (hG n).hasGaussianLaw_eval t
  have hGa : ∀ n, HasGaussianLaw (Yn n s + Yn n t) P := fun n =>
    (hG n).hasGaussianLaw_add (s := s) (t := t)
  have hca : ∀ n, P[Yn n s + Yn n t] = 0 := fun n => by
    rw [Pi.add_def, integral_add (hGs n).integrable (hGt n).integrable, hc, hc, add_zero]
  obtain ⟨hLs, -, hVs⟩ := gaussian_of_ae_tendsto hGs (fun n => hc n s) (hm s).aemeasurable
    (hlim s)
  obtain ⟨hLt, -, hVt⟩ := gaussian_of_ae_tendsto hGt (fun n => hc n t) (hm t).aemeasurable
    (hlim t)
  have hla : ∀ᵐ ω ∂P, Tendsto (fun n => (Yn n s + Yn n t) ω) atTop (𝓝 ((Y s + Y t) ω)) := by
    filter_upwards [hlim s, hlim t] with ω h1 h2
    exact h1.add h2
  obtain ⟨-, -, hVa⟩ := gaussian_of_ae_tendsto hGa hca ((hm s).add (hm t)).aemeasurable hla
  have key : ∀ (A B : Ω → ℝ), MemLp A 2 P → MemLp B 2 P →
      cov[A, B; P] = (Var[A + B; P] - Var[A; P] - Var[B; P]) / 2 := fun A B hA hB => by
    rw [variance_add hA hB]; ring
  rw [key _ _ hLs.memLp_two hLt.memLp_two]
  simp_rw [key _ _ (hGs _).memLp_two (hGt _).memLp_two]
  exact ((hVa.sub hVs).sub hVt).div_const 2

end CircleAvgIndep
end LQGMetric
