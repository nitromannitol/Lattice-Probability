/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovGauss at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGaussLim
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The Gaussian Hilbert space of a centred Gaussian process (task P2-MARKOV, part 1)

For a centred Gaussian process `X : T → Ω → ℝ` with square-integrable coordinates, its *Gaussian
space* `gaussSpace X` is the closure in `L²(P)` of the linear span of the classes `[X t]`. This
file proves the two facts of the Gaussian-Hilbert-space toolkit that the Markov property of the
GFF uses (Miller–Sheffield IG4 arXiv:1302.4738 Prop. 2.8 and Berestycki–Powell arXiv:2404.16642
Thm 1.52 both argue "the projections are jointly Gaussian, so orthogonal means independent"):

* `isCGauss_of_mem_gaussSpace` : every element of the Gaussian space is a centred Gaussian;
* `isGaussianProcess_of_mem_gaussSpace` : any family of elements of the Gaussian space is a
  (jointly) Gaussian process, also jointly with `X` (`isGaussianProcess_sumElim`);
* `indepFun_of_inner_eq_zero` : a family in the Gaussian space orthogonal to `X t` for all
  `t` in a sub-index set is independent of that subfamily of `X`.

Sources: Janson, *Gaussian Hilbert spaces* (CUP 1997), Thm 1.3 (closure of a Gaussian linear
space is Gaussian) and Thm 1.7/Cor. (orthogonal ⇒ independent). The Lean argument: span elements
are images of finite-dimensional Gaussian vectors under linear functionals; `L²` limits have an
a.s. convergent subsequence, and a.s. limits of centred Gaussians are centred Gaussian
(`exists_gaussianReal_of_ae_tendsto`, this library); independence is mathlib's
`IsGaussianProcess.indepFun_of_covariance_eq_zero`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovGauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `u ∈ L²(P)` is a centred real Gaussian. -/
def IsCGauss (P : Measure Ω) (u : Lp ℝ 2 P) : Prop :=
  HasGaussianLaw (u : Ω → ℝ) P ∧ P[(u : Ω → ℝ)] = 0

lemma IsCGauss.map_eq [IsProbabilityMeasure P] {u : Lp ℝ 2 P} (hu : IsCGauss P u) :
    ∃ v : NNReal, P.map (u : Ω → ℝ) = gaussianReal 0 v :=
  ⟨_, by rw [hu.1.map_eq_gaussianReal, hu.2]⟩

lemma isCGauss_of_map_eq [IsProbabilityMeasure P] {u : Lp ℝ 2 P} {v : NNReal}
    (h : P.map (u : Ω → ℝ) = gaussianReal 0 v) : IsCGauss P u := by
  have hm : AEMeasurable (u : Ω → ℝ) P := (Lp.aestronglyMeasurable u).aemeasurable
  refine ⟨⟨hm, by rw [h]; infer_instance⟩, ?_⟩
  have := integral_map (f := fun x : ℝ => x) hm aestronglyMeasurable_id
  rw [h, integral_id_gaussianReal] at this
  exact this.symm

/-- centred Gaussians form a closed subset of `L²`. -/
theorem isClosed_isCGauss [IsProbabilityMeasure P] : IsClosed {u : Lp ℝ 2 P | IsCGauss P u} := by
  refine isClosed_iff_clusterPt.2 fun u hu => ?_
  rw [clusterPt_principal_iff_frequently] at hu
  obtain ⟨w, hw, hwu⟩ : ∃ w : ℕ → Lp ℝ 2 P, (∀ n, IsCGauss P (w n)) ∧ Tendsto w atTop (𝓝 u) := by
    have := (mem_closure_iff_frequently.2 hu)
    obtain ⟨w, hw, hwu⟩ := mem_closure_iff_seq_limit.1 this
    exact ⟨w, hw, hwu⟩
  obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hwu).exists_seq_tendsto_ae
  choose v hv using fun n => (hw n).map_eq
  obtain ⟨V, -, hV⟩ := exists_gaussianReal_of_ae_tendsto (Y := fun k => (w (ns k) : Ω → ℝ))
    (v := fun k => v (ns k)) (fun k => (Lp.aestronglyMeasurable _).aemeasurable)
    (Lp.aestronglyMeasurable u).aemeasurable (fun k => hv (ns k)) hns
  exact isCGauss_of_map_eq hV

variable {T : Type*} (X : T → Ω → ℝ)

/-- the Gaussian space of `X`: the closure of the span of the `[X t]` in `L²(P)` -/
def gaussSpace (hX2 : ∀ t, MemLp (X t) 2 P) : Submodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ (Set.range fun t => (hX2 t).toLp (X t))).topologicalClosure

variable {X}

lemma toLp_mem_gaussSpace (hX2 : ∀ t, MemLp (X t) 2 P) (t : T) :
    (hX2 t).toLp (X t) ∈ gaussSpace X hX2 :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨t, rfl⟩)

/-- span elements are centred Gaussians -/
lemma isCGauss_of_mem_span [IsProbabilityMeasure P] (hX : IsGaussianProcess X P)
    (hc : ∀ t, P[X t] = 0) (hX2 : ∀ t, MemLp (X t) 2 P) {u : Lp ℝ 2 P}
    (hu : u ∈ Submodule.span ℝ (Set.range fun t => (hX2 t).toLp (X t))) : IsCGauss P u := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hu
  set s := c.support
  -- the finite-dimensional Gaussian vector and the functional
  let L : (s → ℝ) →L[ℝ] ℝ := ∑ i : s, c i • ContinuousLinearMap.proj i
  have hL : ∀ x : s → ℝ, L x = ∑ i : s, c i * x i := fun x => by
    simp [L, ContinuousLinearMap.sum_apply]
  have hG : HasGaussianLaw (fun ω => L (s.restrict (X · ω))) P :=
    (hX.hasGaussianLaw s).map_fun L
  have hae : (fun ω => L (s.restrict (X · ω))) =ᵐ[P]
      ((c.sum fun i a => a • (hX2 i).toLp (X i) : Lp ℝ 2 P) : Ω → ℝ) := by
    simp only [Finsupp.sum]
    have h1 := Lp.coeFn_fun_finsetSum (μ := P) (p := 2) s (fun i => c i • (hX2 i).toLp (X i))
    have h2 : ∀ i ∈ s, ((c i • (hX2 i).toLp (X i) : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P]
        fun ω => c i * X i ω := fun i _ => by
      filter_upwards [Lp.coeFn_smul (c i) ((hX2 i).toLp (X i)), (hX2 i).coeFn_toLp] with ω h3 h4
      rw [h3, Pi.smul_apply, h4, smul_eq_mul]
    have h2' : ∀ᵐ ω ∂P, ∀ i ∈ s, ((c i • (hX2 i).toLp (X i) : Lp ℝ 2 P) : Ω → ℝ) ω =
        c i * X i ω := (ae_ball_iff s.countable_toSet).2 fun i hi => h2 i hi
    filter_upwards [h1, h2'] with ω h3 h4
    rw [h3, hL]
    simp only [Finset.restrict]
    rw [← Finset.sum_coe_sort s]
    exact Finset.sum_congr rfl fun i _ => (h4 i i.2).symm
  refine ⟨hG.congr hae, ?_⟩
  rw [← integral_congr_ae hae]
  simp_rw [hL, Finset.restrict]
  rw [integral_finsetSum (s := Finset.univ) (f := fun (i : s) ω => c i * X i ω)
    fun i _ => ((hX2 (i : T)).integrable one_le_two).const_mul _]
  exact Finset.sum_eq_zero fun i _ => by rw [integral_const_mul, hc, mul_zero]

/-- **Janson Thm 1.3.** Every element of the Gaussian space is a centred Gaussian. -/
theorem isCGauss_of_mem_gaussSpace [IsProbabilityMeasure P] (hX : IsGaussianProcess X P)
    (hc : ∀ t, P[X t] = 0) (hX2 : ∀ t, MemLp (X t) 2 P) {u : Lp ℝ 2 P}
    (hu : u ∈ gaussSpace X hX2) : IsCGauss P u := by
  have hsub : (Submodule.span ℝ (Set.range fun t => (hX2 t).toLp (X t)) : Set (Lp ℝ 2 P)) ⊆
      {u | IsCGauss P u} := fun u hu => isCGauss_of_mem_span hX hc hX2 hu
  have hu' : u ∈ closure (Submodule.span ℝ (Set.range fun t => (hX2 t).toLp (X t)) :
      Set (Lp ℝ 2 P)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hu
  exact closure_minimal hsub isClosed_isCGauss hu'

/-- **Joint Gaussianity.** A family of elements of the Gaussian space is a Gaussian process. -/
theorem isGaussianProcess_of_mem_gaussSpace [IsProbabilityMeasure P] (hX : IsGaussianProcess X P)
    (hc : ∀ t, P[X t] = 0) (hX2 : ∀ t, MemLp (X t) 2 P) {S : Type*} (W : S → Lp ℝ 2 P)
    (hW : ∀ s, W s ∈ gaussSpace X hX2) :
    IsGaussianProcess (fun s => (W s : Ω → ℝ)) P := by
  classical
  refine ⟨fun I => ?_⟩
  set Y : Ω → (I → ℝ) := fun ω => I.restrict (fun s => (W s : Ω → ℝ) ω)
  have hYm : AEMeasurable Y P :=
    AEMeasurable.of_eval fun i => (Lp.aestronglyMeasurable (W i)).aemeasurable
  refine ⟨hYm, isGaussian_of_map_eq_gaussianReal fun L => ?_⟩
  rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hYm]
  set w : Lp ℝ 2 P := ∑ i : I, L (Pi.single i 1) • W i
  have hwmem : w ∈ gaussSpace X hX2 :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hW i)
  obtain ⟨v, hv⟩ := (isCGauss_of_mem_gaussSpace hX hc hX2 hwmem).map_eq
  refine ⟨0, v, ?_⟩
  rw [← hv]
  refine Measure.map_congr ?_
  have h1 := Lp.coeFn_fun_finsetSum (μ := P) (p := 2) Finset.univ
    (fun i : I => L (Pi.single i 1) • W i)
  have h2 : ∀ᵐ ω ∂P, ∀ i : I, ((L (Pi.single i 1) • W i : Lp ℝ 2 P) : Ω → ℝ) ω =
      L (Pi.single i 1) * (W i : Ω → ℝ) ω := by
    rw [ae_all_iff]
    intro i
    filter_upwards [Lp.coeFn_smul (L (Pi.single i 1)) (W i)] with ω h3
    rw [h3, Pi.smul_apply, smul_eq_mul]
  filter_upwards [h1, h2] with ω h3 h4
  simp only [Function.comp_apply, w]
  rw [h3]
  simp_rw [h4]
  have := LinearMap.pi_apply_eq_sum_univ L.toLinearMap (Y ω)
  simp only [ContinuousLinearMap.coe_coe] at this
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Y, Finset.restrict, smul_eq_mul]
  rw [mul_comm]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

/-- jointly Gaussian with `X` itself -/
theorem isGaussianProcess_sumElim [IsProbabilityMeasure P] (hX : IsGaussianProcess X P)
    (hc : ∀ t, P[X t] = 0) (hX2 : ∀ t, MemLp (X t) 2 P) {S : Type*} (W : S → Lp ℝ 2 P)
    (hW : ∀ s, W s ∈ gaussSpace X hX2) {T' : Type*} (ι : T' → T) :
    IsGaussianProcess (Sum.elim (fun s => (W s : Ω → ℝ)) (fun b => X (ι b))) P := by
  have h := isGaussianProcess_of_mem_gaussSpace hX hc hX2
    (Sum.elim W fun b => (hX2 (ι b)).toLp (X (ι b)))
    (fun x => by cases x with
      | inl s => exact hW s
      | inr b => exact toLp_mem_gaussSpace hX2 (ι b))
  refine h.congr fun x => ?_
  cases x with
  | inl s => exact Filter.EventuallyEq.rfl
  | inr b => exact (hX2 (ι b)).coeFn_toLp

/-- the `L²` inner product of centred variables is their covariance -/
lemma covariance_eq_inner [IsProbabilityMeasure P] (u : Lp ℝ 2 P) {Z : Ω → ℝ}
    (hZ : MemLp Z 2 P) (hu0 : P[(u : Ω → ℝ)] = 0) :
    cov[(u : Ω → ℝ), Z; P] = ⟪u, hZ.toLp Z⟫ := by
  rw [covariance_eq_sub (Lp.memLp u) hZ, hu0, zero_mul, sub_zero, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hZ.coeFn_toLp] with ω h
  rw [h, Pi.mul_apply, real_inner_eq_re_inner, RCLike.re_to_real]
  simp [mul_comm]

/-- **Janson Thm 1.7 (orthogonal ⇒ independent).** A family in the Gaussian space orthogonal
to every `X (ι b)` is independent of `(X (ι b))_b`. -/
theorem indepFun_of_inner_eq_zero [IsProbabilityMeasure P] (hX : IsGaussianProcess X P)
    (hc : ∀ t, P[X t] = 0) (hX2 : ∀ t, MemLp (X t) 2 P) {S : Type*} (W : S → Lp ℝ 2 P)
    (hW : ∀ s, W s ∈ gaussSpace X hX2) {T' : Type*} (ι : T' → T)
    (horth : ∀ s b, ⟪W s, (hX2 (ι b)).toLp (X (ι b))⟫ = 0) :
    IndepFun (fun ω s => (W s : Ω → ℝ) ω) (fun ω b => X (ι b) ω) P := by
  refine (isGaussianProcess_sumElim hX hc hX2 W hW ι).indepFun_of_covariance_eq_zero
    (fun s => (Lp.aestronglyMeasurable _).aemeasurable)
    (fun b => (hX.hasGaussianLaw_eval (ι b)).aemeasurable) fun s b => ?_
  rw [covariance_eq_inner (W s) (hX2 (ι b)) (isCGauss_of_mem_gaussSpace hX hc hX2 (hW s)).2,
    horth]

end MarkovGauss
end LQGMetric
