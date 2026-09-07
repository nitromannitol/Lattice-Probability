/-
The isonormal process as a Gaussian process indexed by a Hilbert space.

A Hilbert basis carries the space isometrically into `ℓ²`, and `gaussIso`
carries `ℓ²` isometrically into the square-integrable functions on the Gaussian
sequence space.  The composite is a family of centred Gaussians indexed by the
Hilbert space, linear in the index and with covariance the inner product; that
is white noise on the space, and Brownian motion is its restriction to the
indicators of intervals.
-/
import Mathlib
import LatticeProb.Gauss.Isonormal

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The isonormal process attached to a Hilbert basis: a centred Gaussian for
every vector, linear in the vector, with covariance the inner product. -/
def isoProc (b : HilbertBasis ℕ ℝ H) (h : H) : (ℕ → ℝ) → ℝ := ⇑(gaussIso (b.repr h))

theorem measurable_isoProc (b : HilbertBasis ℕ ℝ H) (h : H) : Measurable (isoProc b h) :=
  (Lp.stronglyMeasurable _).measurable

/-- **Each value of the isonormal process is a centred Gaussian**, with variance
the squared norm of the index. -/
theorem map_isoProc (b : HilbertBasis ℕ ℝ H) (h : H) :
    gaussLaw.map (isoProc b h) = gaussianReal 0 (‖h‖ ^ 2).toNNReal := by
  rw [isoProc, map_gaussIso, b.repr.norm_map]

theorem memLp_isoProc (b : HilbertBasis ℕ ℝ H) (h : H) : MemLp (isoProc b h) 2 gaussLaw := by
  have : HasGaussianLaw (isoProc b h) gaussLaw := by
    refine ⟨?_⟩
    rw [map_isoProc]
    infer_instance
  exact this.memLp_two

theorem integral_isoProc (b : HilbertBasis ℕ ℝ H) (h : H) :
    ∫ ω, isoProc b h ω ∂gaussLaw = 0 := by
  have hfm : AEStronglyMeasurable (fun x : ℝ => x) (gaussLaw.map (isoProc b h)) := by fun_prop
  have := integral_map (measurable_isoProc b h).aemeasurable hfm
  rw [map_isoProc] at this
  rw [← this, integral_id_gaussianReal]

/-- **The covariance of the isonormal process is the inner product.** -/
theorem integral_isoProc_mul (b : HilbertBasis ℕ ℝ H) (h g : H) :
    ∫ ω, isoProc b h ω * isoProc b g ω ∂gaussLaw = (inner ℝ h g : ℝ) := by
  have h1 : (inner ℝ (gaussIso (b.repr h)) (gaussIso (b.repr g)) : ℝ) = (inner ℝ h g : ℝ) := by
    rw [gaussIso.inner_map_map, b.repr.inner_map_map]
  rw [← h1, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [isoProc, RCLike.inner_apply, conj_trivial]
  ring

/-! ### Linearity in the index -/

theorem isoProc_add (b : HilbertBasis ℕ ℝ H) (h g : H) :
    isoProc b (h + g) =ᵐ[gaussLaw] fun ω => isoProc b h ω + isoProc b g ω := by
  have : gaussIso (b.repr (h + g)) = gaussIso (b.repr h) + gaussIso (b.repr g) := by
    rw [map_add, map_add]
  rw [isoProc, this]
  filter_upwards [Lp.coeFn_add (gaussIso (b.repr h)) (gaussIso (b.repr g))] with ω hω
  rw [hω]
  rfl

theorem isoProc_smul (b : HilbertBasis ℕ ℝ H) (a : ℝ) (h : H) :
    isoProc b (a • h) =ᵐ[gaussLaw] fun ω => a * isoProc b h ω := by
  have : gaussIso (b.repr (a • h)) = a • gaussIso (b.repr h) := by
    rw [map_smul, map_smul]
  rw [isoProc, this]
  filter_upwards [Lp.coeFn_smul a (gaussIso (b.repr h))] with ω hω
  rw [hω]
  rfl

/-- A finite linear combination of indices is the same linear combination of the
values, almost everywhere. -/
theorem isoProc_sum {κ : Type*} (b : HilbertBasis ℕ ℝ H) (s : Finset κ) (c : κ → ℝ)
    (v : κ → H) :
    ∀ᵐ ω ∂gaussLaw, isoProc b (∑ i ∈ s, c i • v i) ω = ∑ i ∈ s, c i * isoProc b (v i) ω := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h0 : isoProc b (0 : H) =ᵐ[gaussLaw] fun _ => (0 : ℝ) := by
        have : gaussIso (b.repr (0 : H)) = 0 := by simp
        rw [isoProc, this]
        exact Lp.coeFn_zero ℝ 2 gaussLaw
      filter_upwards [h0] with ω hω
      simpa using hω
  | insert i s hi ih =>
      have hsum : (∑ j ∈ insert i s, c j • v j) = c i • v i + ∑ j ∈ s, c j • v j :=
        Finset.sum_insert hi
      filter_upwards [ih, isoProc_add b (c i • v i) (∑ j ∈ s, c j • v j),
        isoProc_smul b (c i) (v i)] with ω h1 h2 h3
      rw [hsum, h2, h3, h1, Finset.sum_insert hi]

/-! ### The isonormal process is a Gaussian process -/

/-- **The isonormal process is a Gaussian process.**  Every finite-dimensional
law is Gaussian, because a continuous linear functional of finitely many values
is one value at a linear combination of the indices. -/
theorem isGaussianProcess_isoProc (b : HilbertBasis ℕ ℝ H) :
    IsGaussianProcess (isoProc b) gaussLaw := by
  classical
  refine ⟨fun I => ⟨?_⟩⟩
  have hvecm : Measurable (fun ω : ℕ → ℝ => I.restrict (fun t => isoProc b t ω)) :=
    measurable_pi_lambda _ fun t => measurable_isoProc b _
  refine isGaussian_of_map_eq_gaussianReal fun L => ?_
  set c : ↥I → ℝ := fun t => L (fun j => if t = j then (1 : ℝ) else 0) with hc
  have hL : ∀ x : ↥I → ℝ, L x = ∑ t, x t * c t := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_smul]
    simp [hc]
  have hmapmap : (gaussLaw.map (fun ω : ℕ → ℝ => I.restrict (fun t => isoProc b t ω))).map L
      = gaussLaw.map (fun ω : ℕ → ℝ => L (I.restrict (fun t => isoProc b t ω))) := by
    rw [Measure.map_map (by fun_prop) hvecm]
    rfl
  have hae : (fun ω : ℕ → ℝ => L (I.restrict (fun t => isoProc b t ω)))
      =ᵐ[gaussLaw] isoProc b (∑ t : ↥I, c t • (t : H)) := by
    filter_upwards [isoProc_sum b (Finset.univ : Finset ↥I) c
      (fun t : ↥I => (t : H))] with ω hω
    rw [hL, hω]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mul_comm]
    rfl
  rw [hmapmap, Measure.map_congr hae, map_isoProc]
  exact ⟨0, _, rfl⟩

end LatticeProb

end
