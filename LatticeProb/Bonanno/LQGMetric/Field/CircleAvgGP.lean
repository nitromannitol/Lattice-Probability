/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.CircleAvgGP at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgProc

/-!
# The circle-average increments form a Gaussian process

`isGaussianProcess_cInc`: for a whole-plane GFF, `((r, z), (s, w)) ↦ h_r(z) − h_s(w)`
(`r, s > 0`) is a centered Gaussian process (DS arXiv:0808.1560 §3.1), with covariance
`covariance_cInc`. Proof: every linear functional of a finite family of increments is the a.s.
limit of the same functional of the mollified increments, which are jointly Gaussian and
centered (`exists_gaussianReal_of_ae_tendsto`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace LQGMetric
namespace CircleAvg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- the index set: pairs of (radius `> 0`, centre) -/
abbrev IncIdx : Type := (Ioi (0 : ℝ) × ℂ) × (Ioi (0 : ℝ) × ℂ)

/-- the increment process `((r, z), (s, w)) ↦ h_r(z) − h_s(w)` -/
def incProc (h : Ω → DistC) (p : IncIdx) (ω : Ω) : ℝ :=
  cInc h p.1.1 p.1.2 p.2.1 p.2.2 ω

/-- its mollified version at level `n` -/
def incProcN (h : Ω → DistC) (n : ℕ) (p : IncIdx) (ω : Ω) : ℝ :=
  mInc h n p.1.1 p.1.2 p.2.1 p.2.2 ω

theorem isGaussianProcess_incProcN (hh : IsWholePlaneGFF h P) (n : ℕ) :
    IsGaussianProcess (incProcN h n) P := by
  have := (isGaussianProcess_mollAvg_sub hh).comp_right
    (fun p : IncIdx => ((n, p.1.2, (p.1.1 : ℝ)), (n, p.2.2, (p.2.1 : ℝ))))
  exact this

lemma integral_incProcN (hh : IsWholePlaneGFF h P) (n : ℕ) (p : IncIdx) :
    ∫ ω, incProcN h n p ω ∂P = 0 :=
  integral_mollAvg_sub hh _ _ _ _ _ _

/-- **The circle-average increments form a Gaussian process.** -/
theorem isGaussianProcess_incProc (hh : IsWholePlaneGFF h P) :
    IsGaussianProcess (incProc h) P := by
  have := hh.gaussian.isProbabilityMeasure
  refine ⟨fun I => ?_⟩
  set X : Ω → (I → ℝ) := fun ω => I.restrict (incProc h · ω)
  have hXm : Measurable X := by
    refine measurable_pi_iff.mpr fun i => ?_
    exact measurable_cInc hh _ _ _ _
  refine ⟨hXm.aemeasurable, isGaussian_of_map_eq_gaussianReal fun L => ?_⟩
  rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable
    hXm.aemeasurable]
  set Xn : ℕ → Ω → (I → ℝ) := fun n ω => I.restrict (incProcN h n · ω)
  have hG : ∀ n, HasGaussianLaw (fun ω => L (Xn n ω)) P := fun n =>
    ((isGaussianProcess_incProcN hh n).hasGaussianLaw I).map_fun L
  have hmean : ∀ n, P[fun ω => L (Xn n ω)] = 0 := by
    intro n
    have e : ∀ ω, L (Xn n ω) = ∑ i : I, Xn n ω i * L (fun j => if i = j then 1 else 0) := by
      intro ω
      have := LinearMap.pi_apply_eq_sum_univ L.toLinearMap (Xn n ω)
      simpa [smul_eq_mul] using this
    simp_rw [e]
    rw [integral_finsetSum _ fun i _ =>
      ((((isGaussianProcess_incProcN hh n).hasGaussianLaw_eval i.1).integrable).mul_const _)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_mul_const]
    simp only [Xn, Finset.restrict]
    rw [integral_incProcN hh, zero_mul]
  have hmap : ∀ n, P.map (fun ω => L (Xn n ω)) =
      gaussianReal 0 (Var[fun ω => L (Xn n ω); P]).toNNReal := by
    intro n
    rw [(hG n).map_eq_gaussianReal, hmean]
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => L (Xn n ω)) atTop (𝓝 (L (X ω))) := by
    have hall : ∀ᵐ ω ∂P, ∀ i : I, Tendsto (fun n => incProcN h n i.1 ω) atTop
        (𝓝 (incProc h i.1 ω)) := by
      rw [ae_all_iff]
      intro i
      exact ae_tendsto_mInc hh i.1.1.1.2 i.1.2.1.2 _ _
    filter_upwards [hall] with ω hω
    exact (L.continuous.tendsto _).comp (tendsto_pi_nhds.mpr hω)
  obtain ⟨V, -, hV⟩ := exists_gaussianReal_of_ae_tendsto (fun n => (hG n).aemeasurable)
    (L.continuous.measurable.comp hXm).aemeasurable hmap hlim
  exact ⟨0, V, hV⟩

end CircleAvg
end LQGMetric
