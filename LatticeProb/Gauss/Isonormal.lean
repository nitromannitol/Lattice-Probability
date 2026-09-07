/-
The isonormal process: a linear isometry from a separable Hilbert space into the
square-integrable functions on a probability space, whose values are centred
Gaussians.

The coordinates of the product of countably many standard Gaussians are an
orthonormal family in `L²`, so an orthonormal family in the Hilbert space is
carried to it by a linear isometry.  What makes the image Gaussian is that the
partial sums are Gaussian by `map_gaussSum` and that Gaussian laws survive
almost sure limits.
-/
import Mathlib
import LatticeProb.Gauss.Coords
import LatticeProb.Prob.FiniteMarginal

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

/-! ### The coordinates as an orthonormal family in `L²` -/

theorem map_eval_gaussLaw (n : ℕ) :
    gaussLaw.map (fun ω : ℕ → ℝ => ω n) = gaussianReal 0 1 := by
  rw [gaussLaw, Measure.infinitePi_map_eval]

theorem hasGaussianLaw_eval (n : ℕ) :
    HasGaussianLaw (fun ω : ℕ → ℝ => ω n) gaussLaw := by
  refine ⟨?_⟩
  rw [map_eval_gaussLaw n]
  infer_instance

theorem hasGaussianLaw_gaussSum (c : ℕ → ℝ) (N : ℕ) :
    HasGaussianLaw (gaussSum c N) gaussLaw := by
  refine ⟨?_⟩
  rw [map_gaussSum c N]
  infer_instance

theorem memLp_gaussSum (c : ℕ → ℝ) (N : ℕ) : MemLp (gaussSum c N) 2 gaussLaw :=
  (hasGaussianLaw_gaussSum c N).memLp_two

theorem memLp_eval (n : ℕ) : MemLp (fun ω : ℕ → ℝ => ω n) 2 gaussLaw :=
  (hasGaussianLaw_eval n).memLp_two

/-- The second moment of a centred real Gaussian is its variance. -/
theorem integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral (by fun_prop), integral_id_gaussianReal] at h
  simpa using h

/-- The second moment of a finite linear combination of the coordinates. -/
theorem integral_gaussSum_sq (c : ℕ → ℝ) (N : ℕ) :
    ∫ ω, (gaussSum c N ω) ^ 2 ∂gaussLaw = ∑ k ∈ Finset.range N, c k ^ 2 := by
  have hnn : (0 : ℝ) ≤ ∑ k ∈ Finset.range N, c k ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hfm : AEStronglyMeasurable (fun x : ℝ => x ^ 2)
      (gaussLaw.map (gaussSum c N)) := by fun_prop
  have hmap : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 (∑ k ∈ Finset.range N, c k ^ 2).toNNReal)
      = ∫ ω, (gaussSum c N ω) ^ 2 ∂gaussLaw := by
    rw [← map_gaussSum c N, integral_map (measurable_gaussSum c N).aemeasurable hfm]
  rw [← hmap, integral_sq_gaussianReal, Real.coe_toNNReal _ hnn]

theorem integral_eval_sq (n : ℕ) : ∫ ω, (ω n) ^ 2 ∂gaussLaw = 1 := by
  have hfm : AEStronglyMeasurable (fun x : ℝ => x ^ 2)
      (gaussLaw.map (fun ω : ℕ → ℝ => ω n)) := by fun_prop
  have hmap : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = ∫ ω, (ω n) ^ 2 ∂gaussLaw := by
    rw [← map_eval_gaussLaw n, integral_map (measurable_pi_apply n).aemeasurable hfm]
  rw [← hmap, integral_sq_gaussianReal]
  simp

theorem integral_eval_mul_eval {n m : ℕ} (h : n ≠ m) :
    ∫ ω, ω n * ω m ∂gaussLaw = 0 := by
  classical
  set v : Fin 2 → ℕ := ![n, m] with hv
  have hv0 : v 0 = n := rfl
  have hv1 : v 1 = m := rfl
  have hvinj : Function.Injective v := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hmap : gaussLaw.map (fun (ω : ℕ → ℝ) (j : Fin 2) => ω (v j))
      = Measure.pi (fun _ : Fin 2 => (gaussianReal 0 1 : Measure ℝ)) := by
    rw [gaussLaw]
    exact infinitePi_map_comp _ v hvinj
  have hfm : AEStronglyMeasurable (fun x : Fin 2 → ℝ => x 0 * x 1)
      (gaussLaw.map (fun (ω : ℕ → ℝ) (j : Fin 2) => ω (v j))) := by
    rw [hmap]; fun_prop
  have h1 : ∫ x : Fin 2 → ℝ, x 0 * x 1
        ∂(Measure.pi fun _ : Fin 2 => (gaussianReal 0 1 : Measure ℝ))
      = ∫ ω, ω n * ω m ∂gaussLaw := by
    rw [← hmap, integral_map
      (measurable_pi_lambda _ fun j => measurable_pi_apply (v j)).aemeasurable hfm]
    rfl
  rw [← h1]
  have h2 : ∀ x : Fin 2 → ℝ, x 0 * x 1 = ∏ i : Fin 2, x i := fun x => (Fin.prod_univ_two x).symm
  rw [integral_congr_ae (Filter.Eventually.of_forall h2),
    integral_fintype_prod_eq_prod (fun (_ : Fin 2) (x : ℝ) => x)]
  simp [integral_id_gaussianReal]

/-! ### The coordinates as an orthonormal family -/

/-- The `n`-th coordinate, as an element of `L²` of the Gaussian sequence law. -/
def gaussCoord (n : ℕ) : Lp ℝ 2 gaussLaw := (memLp_eval n).toLp _

theorem inner_gaussCoord (n m : ℕ) :
    (inner ℝ (gaussCoord n) (gaussCoord m) : ℝ) = ∫ ω, ω n * ω m ∂gaussLaw := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_eval n).coeFn_toLp, (memLp_eval m).coeFn_toLp] with ω h1 h2
  simp only [gaussCoord, RCLike.inner_apply, conj_trivial]
  rw [h1, h2]
  ring

theorem orthonormal_gaussCoord : Orthonormal ℝ gaussCoord := by
  constructor
  · intro n
    have h : (inner ℝ (gaussCoord n) (gaussCoord n) : ℝ) = 1 := by
      rw [inner_gaussCoord]
      simpa [sq] using integral_eval_sq n
    have h2 : ‖gaussCoord n‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      exact h
    nlinarith [norm_nonneg (gaussCoord n), h2]
  · intro n m hnm
    rw [inner_gaussCoord]
    exact integral_eval_mul_eval hnm

/-! ### The isonormal process -/

/-- **The isonormal process.**  The linear isometry of `ℓ²(ℕ)` into `L²` of the
Gaussian sequence law that sends the standard basis to the coordinates. -/
def gaussIso : (lp (fun _ : ℕ => ℝ) 2) →ₗᵢ[ℝ] Lp ℝ 2 gaussLaw :=
  orthonormal_gaussCoord.orthogonalFamily.linearIsometry

theorem hasSum_gaussIso (f : lp (fun _ : ℕ => ℝ) 2) :
    HasSum (fun i => f i • gaussCoord i) (gaussIso f) := by
  have h := orthonormal_gaussCoord.orthogonalFamily.hasSum_linearIsometry f
  simpa [gaussIso, LinearIsometry.toSpanSingleton_apply] using h

/-- The partial sums of the isonormal series are the finite linear combinations
of the coordinates. -/
theorem coeFn_sum_smul_gaussCoord (c : ℕ → ℝ) (N : ℕ) :
    (⇑(∑ i ∈ Finset.range N, c i • gaussCoord i) : (ℕ → ℝ) → ℝ)
      =ᵐ[gaussLaw] gaussSum c N := by
  induction N with
  | zero =>
      have h0 : (gaussSum c 0) = (0 : (ℕ → ℝ) → ℝ) := by
        funext ω
        simp [gaussSum]
      rw [Finset.range_zero, Finset.sum_empty, h0]
      exact Lp.coeFn_zero ℝ 2 gaussLaw
  | succ N ih =>
      rw [Finset.sum_range_succ]
      filter_upwards [Lp.coeFn_add (∑ i ∈ Finset.range N, c i • gaussCoord i)
          (c N • gaussCoord N), ih, Lp.coeFn_smul (c N) (gaussCoord N),
        (memLp_eval N).coeFn_toLp] with ω h1 h2 h3 h4
      rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, gaussCoord, h4]
      simp [gaussSum, Finset.sum_range_succ]

/-- **The law of the isonormal process.**  The image of a square-summable
sequence is a centred Gaussian with variance the square of its norm. -/
theorem map_gaussIso (f : lp (fun _ : ℕ => ℝ) 2) :
    gaussLaw.map (⇑(gaussIso f)) = gaussianReal 0 (‖f‖ ^ 2).toNNReal := by
  set S : ℕ → Lp ℝ 2 gaussLaw := fun N => ∑ i ∈ Finset.range N, f i • gaussCoord i with hS
  have hSt : Filter.Tendsto S Filter.atTop (nhds (gaussIso f)) :=
    (hasSum_gaussIso f).tendsto_sum_nat
  have hnormsq : ∀ N, ‖S N‖ ^ 2 = ∑ i ∈ Finset.range N, f i ^ 2 := by
    intro N
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    have hcongr : ∫ a, (inner ℝ ((S N) a) ((S N) a) : ℝ) ∂gaussLaw
        = ∫ ω, (gaussSum (fun i => f i) N ω) ^ 2 ∂gaussLaw := by
      refine integral_congr_ae ?_
      filter_upwards [coeFn_sum_smul_gaussCoord (fun i => f i) N] with ω hω
      simp only [hS, RCLike.inner_apply, conj_trivial]
      rw [hω]
      ring
    rw [hcongr]
    exact integral_gaussSum_sq _ N
  have hvar : Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, f i ^ 2) Filter.atTop
      (nhds (‖f‖ ^ 2)) := by
    have h1 : Filter.Tendsto (fun N => ‖S N‖) Filter.atTop (nhds ‖gaussIso f‖) := hSt.norm
    rw [gaussIso.norm_map] at h1
    exact (h1.pow 2).congr fun N => hnormsq N
  have hmeas : TendstoInMeasure gaussLaw (fun N => ⇑(S N)) Filter.atTop (⇑(gaussIso f)) :=
    tendstoInMeasure_of_tendsto_Lp hSt
  obtain ⟨ns, hmono, hns⟩ := hmeas.exists_seq_tendsto_ae
  have hall : ∀ᵐ ω ∂gaussLaw, ∀ N, (⇑(S N)) ω = gaussSum (fun i => f i) N ω :=
    ae_all_iff.2 fun N => coeFn_sum_smul_gaussCoord _ N
  have hae : ∀ᵐ ω ∂gaussLaw, Filter.Tendsto
      (fun i => gaussSum (fun j => f j) (ns i) ω) Filter.atTop
      (nhds ((⇑(gaussIso f) : (ℕ → ℝ) → ℝ) ω)) := by
    filter_upwards [hns, hall] with ω h1 h2
    exact h1.congr fun i => h2 (ns i)
  have hYm : Measurable (⇑(gaussIso f) : (ℕ → ℝ) → ℝ) :=
    (Lp.stronglyMeasurable (gaussIso f)).measurable
  have hnn : ∀ N : ℕ, (0 : ℝ) ≤ ∑ i ∈ Finset.range N, f i ^ 2 :=
    fun N => Finset.sum_nonneg fun i _ => sq_nonneg _
  refine map_eq_gaussianReal_of_tendsto_ae
    (σ := fun i => (∑ k ∈ Finset.range (ns i), f k ^ 2).toNNReal)
    (fun i => measurable_gaussSum _ _) hYm (fun i => map_gaussSum _ _) hae ?_
  simp only [Real.coe_toNNReal _ (hnn _), Real.coe_toNNReal _ (sq_nonneg ‖f‖)]
  exact hvar.comp hmono.tendsto_atTop

end LatticeProb

end
