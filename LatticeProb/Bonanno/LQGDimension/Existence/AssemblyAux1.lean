/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Existence.AssemblyAux1 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Existence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Assembly of `GFFCircleAverageExists`, part 1: Gaussian building blocks

* `stdP`: the law of an i.i.d. standard Gaussian sequence, `infinitePi (gaussianReal 0 1)`.
* `hasLaw_sum_mul`: `Σ_{k<M} w_k ω_k` has law `N(0, Σ_{k<M} w_k²)` under `stdP`.
* `hasLaw_gaussianReal_of_tendsto`: a.e. limits of centered real Gaussians whose variances
  converge are centered Gaussian with the limit variance (characteristic functions and
  dominated convergence).
* `hasGaussianLaw_pi_of_forall_hasLaw`: a finite family whose linear combinations are all
  centered real Gaussians is a Gaussian vector (Cramér–Wold at the level of
  `isGaussian_of_map_eq_gaussianReal`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace LQGDimension.ExistAsm

/-! ### The i.i.d. Gaussian sequence -/

/-- The law of an i.i.d. standard Gaussian sequence. -/
def stdP : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => gaussianReal 0 1

instance : IsProbabilityMeasure stdP := by
  unfold stdP
  infer_instance

theorem hasLaw_eval (k : ℕ) : HasLaw (fun ω : ℕ → ℝ => ω k) (gaussianReal 0 1) stdP :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) k).hasLaw

theorem stdP_map_eval (k : ℕ) : stdP.map (fun ω => ω k) = gaussianReal 0 1 :=
  (hasLaw_eval k).map_eq

theorem iIndepFun_eval : iIndepFun (fun (k : ℕ) (ω : ℕ → ℝ) => ω k) stdP := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun k => measurable_pi_apply k)]
  change stdP.map id = Measure.infinitePi (fun i => stdP.map (fun ω => ω i))
  simp only [stdP_map_eval, Measure.map_id]
  rfl

theorem hasGaussianLaw_eval (k : ℕ) : HasGaussianLaw (fun ω : ℕ → ℝ => ω k) stdP :=
  (hasLaw_eval k).hasGaussianLaw

theorem integral_eval (k : ℕ) : ∫ ω, ω k ∂stdP = 0 := by
  rw [(hasLaw_eval k).integral_eq, integral_id_gaussianReal]

theorem variance_eval (k : ℕ) : Var[fun ω : ℕ → ℝ => ω k; stdP] = 1 := by
  rw [(hasLaw_eval k).variance_eq, variance_id_gaussianReal]
  simp

/-- `Σ_{k<M} w_k ω_k` is a centered Gaussian with variance `Σ_{k<M} w_k²`. -/
theorem hasLaw_sum_mul (w : ℕ → ℝ) (M : ℕ) :
    HasLaw (fun ω : ℕ → ℝ => ∑ k ∈ Finset.range M, w k * ω k)
      (gaussianReal 0 (∑ k ∈ Finset.range M, w k ^ 2).toNNReal) stdP := by
  set S : (ℕ → ℝ) → ℝ := fun ω => ∑ k ∈ Finset.range M, w k * ω k with hS
  have hind : iIndepFun (fun (k : ℕ) (ω : ℕ → ℝ) => w k * ω k) stdP :=
    iIndepFun_eval.comp (fun k x => w k * x) (fun k => measurable_const_mul (w k))
  have hG1 : ∀ k : ℕ, HasGaussianLaw (fun ω : ℕ → ℝ => w k * ω k) stdP := fun k => by
    simpa [smul_eq_mul] using (hasGaussianLaw_eval k).fun_smul (w k)
  have hindF : iIndepFun (fun (i : Fin M) (ω : ℕ → ℝ) => w i * ω i) stdP :=
    hind.precomp (g := (Fin.val : Fin M → ℕ)) Fin.val_injective
  have hGS : HasGaussianLaw S stdP := by
    have := iIndepFun.hasGaussianLaw_fun_sum (fun i : Fin M => hG1 i) hindF
    have e : S = fun ω => ∑ i : Fin M, w i * ω i := by
      funext ω
      simp only [hS]
      exact (Fin.sum_univ_eq_sum_range (fun k => w k * ω k) M).symm
    rw [e]
    exact this
  have hmean : ∫ ω, S ω ∂stdP = 0 := by
    simp only [hS]
    rw [integral_finsetSum]
    · simp [integral_const_mul, integral_eval]
    · intro k _
      exact (hG1 k).integrable
  have hvar : Var[S; stdP] = ∑ k ∈ Finset.range M, w k ^ 2 := by
    have e : S = ∑ k ∈ Finset.range M, (fun ω : ℕ → ℝ => w k * ω k) := by
      funext ω
      simp [hS, Finset.sum_apply]
    rw [e, IndepFun.variance_sum (fun k _ => (hG1 k).memLp_two)
      (fun i _ j _ hij => hind.indepFun hij)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [variance_const_mul, variance_eval, mul_one]
  have hmap := hGS.map_eq_gaussianReal
  refine ⟨hGS.aemeasurable, ?_⟩
  rw [hmap, hmean, hvar]

/-! ### Closure of centered Gaussian laws under a.e. limits -/

section Limit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem charFun_map_eq_integral {Z : Ω → ℝ} (hZ : AEMeasurable Z P) (u : ℝ) :
    charFun (P.map Z) u = ∫ ω, Complex.exp (u * Z ω * Complex.I) ∂P := by
  rw [charFun_apply_real, integral_map hZ]
  exact Continuous.aestronglyMeasurable (by fun_prop)

/-- **A.e. limits of centered real Gaussians** with converging variances are centered Gaussian
with the limit variance. -/
theorem hasLaw_gaussianReal_of_tendsto [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} {Y₀ : Ω → ℝ}
    {v : ℕ → ℝ} {v₀ : ℝ} (hY : ∀ n, HasLaw (Y n) (gaussianReal 0 (v n).toNNReal) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Y₀ ω)))
    (hv : Tendsto v atTop (𝓝 v₀)) :
    HasLaw Y₀ (gaussianReal 0 v₀.toNNReal) P := by
  have hmeas : ∀ n, AEMeasurable (Y n) P := fun n => (hY n).aemeasurable
  have hY₀ : AEMeasurable Y₀ P := aemeasurable_of_tendsto_metrizable_ae atTop hmeas hlim
  refine ⟨hY₀, ?_⟩
  apply Measure.ext_of_charFun
  funext u
  have hc : Continuous fun x : ℝ => Complex.exp (u * x * Complex.I) := by fun_prop
  have h1 : Tendsto (fun n => charFun (P.map (Y n)) u) atTop (𝓝 (charFun (P.map Y₀) u)) := by
    simp_rw [charFun_map_eq_integral (hmeas _), charFun_map_eq_integral hY₀]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => hc.comp_aestronglyMeasurable (hmeas n).aestronglyMeasurable)
      (integrable_const 1) (fun n => ae_of_all _ fun ω => ?_) ?_
    · have : (u : ℂ) * (Y n ω : ℂ) = ((u * Y n ω : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    · filter_upwards [hlim] with ω hω
      exact (hc.tendsto _).comp hω
  have h2 : Tendsto (fun n => charFun (P.map (Y n)) u) atTop
      (𝓝 (charFun (gaussianReal 0 v₀.toNNReal) u)) := by
    simp_rw [fun n => (hY n).map_eq, charFun_gaussianReal]
    have hv' : Tendsto (fun n => ((v n).toNNReal : ℝ)) atTop (𝓝 (v₀.toNNReal : ℝ)) :=
      (NNReal.continuous_coe.tendsto _).comp ((continuous_real_toNNReal.tendsto _).comp hv)
    have hv'' : Tendsto (fun n => (((v n).toNNReal : ℝ) : ℂ)) atTop
        (𝓝 ((v₀.toNNReal : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hv'
    refine (Complex.continuous_exp.tendsto _).comp ?_
    exact tendsto_const_nhds.sub ((hv''.mul tendsto_const_nhds).div_const 2)
  rw [tendsto_nhds_unique h1 h2]

end Limit

/-! ### Gaussian vectors from Gaussian linear combinations -/

/-- A finite family of real random variables all of whose linear combinations are centered
real Gaussians is a Gaussian vector. -/
theorem hasGaussianLaw_pi_of_forall_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} [Fintype ι] {Y : ι → Ω → ℝ} (hmeas : ∀ i, AEMeasurable (Y i) P)
    (h : ∀ c : ι → ℝ, ∃ v : NNReal,
      HasLaw (fun ω => ∑ i, c i * Y i ω) (gaussianReal 0 v) P) :
    HasGaussianLaw (fun ω i => Y i ω) P := by
  classical
  have hm : AEMeasurable (fun ω i => Y i ω) P := AEMeasurable.of_eval hmeas
  refine ⟨hm, isGaussian_of_map_eq_gaussianReal fun L => ?_⟩
  obtain ⟨v, hv⟩ := h (fun i => L (fun j => if i = j then 1 else 0))
  refine ⟨0, v, ?_⟩
  rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hm]
  rw [← hv.map_eq]
  congr 1
  funext ω
  simp only [Function.comp_apply]
  rw [show L (fun i => Y i ω) = L.toLinearMap (fun i => Y i ω) from rfl,
    LinearMap.pi_apply_eq_sum_univ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, mul_comm]
  rfl

end LQGDimension.ExistAsm
