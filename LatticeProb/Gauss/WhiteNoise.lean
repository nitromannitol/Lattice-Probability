/-
White noise on a separable measure space.

Mathlib 4.32 has Gaussian processes and a projective family for Brownian motion
but no Kolmogorov extension theorem, so no Gaussian process indexed by an
infinite set exists there.  The isonormal process supplies one without any
extension theorem: `L²` of a separable measure is a separable Hilbert space, so
it has a countable orthonormal basis, and the product of standard Gaussians over
that basis carries it isometrically into `L²` of a probability space.  The image
of a test function is white noise evaluated at it.
-/
import Mathlib
import LatticeProb.Gauss.Process

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

/-! ### A separable Hilbert space has a countable orthonormal basis -/

/-- **An orthonormal family in a separable space is countable.**  Distinct
members are at distance `√2`, so a countable dense set separates them. -/
theorem countable_of_orthonormal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [TopologicalSpace.SeparableSpace E] {w : Set E}
    (hw : Orthonormal ℝ ((↑) : w → E)) : w.Countable := by
  classical
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense E
  haveI : Countable ↥D := hDc.to_subtype
  have hpick : ∀ x : w, ∃ y : ↥D, dist (x : E) (y : E) < 1 / 2 := by
    intro x
    obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.mp (hDd (x : E)) (1 / 2) (by norm_num)
    exact ⟨⟨y, hy⟩, hd⟩
  choose g hg using hpick
  have hfar : ∀ x y : w, x ≠ y → (1 : ℝ) < dist (x : E) (y : E) := by
    intro x y hxy
    have hnorm : ‖(x : E) - (y : E)‖ ^ 2 = 2 := by
      rw [norm_sub_sq_real, hw.1 x, hw.1 y, hw.2 hxy]
      norm_num
    have hd : dist (x : E) (y : E) ^ 2 = 2 := by
      rw [dist_eq_norm]
      exact hnorm
    nlinarith [dist_nonneg (x := (x : E)) (y := (y : E)), hd]
  have hinj : Function.Injective g := by
    intro x y hxy
    by_contra hne
    have h1 := hg x
    have h2 := hg y
    rw [hxy] at h1
    have := hfar x y hne
    have hd : dist (x : E) (y : E) ≤ dist (x : E) (g y : E) + dist (g y : E) (y : E) :=
      dist_triangle _ _ _
    rw [dist_comm (g y : E) (y : E)] at hd
    linarith
  rw [← Set.countable_coe_iff]
  exact hinj.countable

/-- A separable Hilbert space has a countable orthonormal basis. -/
theorem exists_countable_hilbertBasis (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E] :
    ∃ w : Set E, w.Countable ∧ Nonempty (HilbertBasis w ℝ E) := by
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis (𝕜 := ℝ) (E := E)
  refine ⟨w, ?_, ⟨b⟩⟩
  refine countable_of_orthonormal ?_
  rw [← hb]
  exact b.orthonormal

/-! ### White noise -/

section WhiteNoise

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The element of `L²` represented by a square-integrable function, and zero
otherwise. -/
def toLpOrZero (μ : Measure X) (f : X → ℝ) : Lp ℝ 2 μ := by
  classical
  exact if h : MemLp f 2 μ then h.toLp f else 0

theorem toLpOrZero_of_memLp {f : X → ℝ} (hf : MemLp f 2 μ) :
    toLpOrZero μ f = hf.toLp f := by
  classical
  rw [toLpOrZero, dif_pos hf]

theorem coeFn_toLpOrZero {f : X → ℝ} (hf : MemLp f 2 μ) :
    (⇑(toLpOrZero μ f) : X → ℝ) =ᵐ[μ] f := by
  rw [toLpOrZero_of_memLp hf]
  exact hf.coeFn_toLp

theorem toLpOrZero_add {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    toLpOrZero μ (f + g) = toLpOrZero μ f + toLpOrZero μ g := by
  rw [toLpOrZero_of_memLp (hf.add hg), toLpOrZero_of_memLp hf, toLpOrZero_of_memLp hg,
    MemLp.toLp_add]

theorem toLpOrZero_smul (a : ℝ) {f : X → ℝ} (hf : MemLp f 2 μ) :
    toLpOrZero μ (a • f) = a • toLpOrZero μ f := by
  rw [toLpOrZero_of_memLp (hf.const_smul a), toLpOrZero_of_memLp hf, MemLp.toLp_const_smul]

theorem inner_toLpOrZero {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (inner ℝ (toLpOrZero μ f) (toLpOrZero μ g) : ℝ) = ∫ y, f y * g y ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toLpOrZero hf, coeFn_toLpOrZero hg] with y h1 h2
  simp only [RCLike.inner_apply, conj_trivial]
  rw [h1, h2]
  ring

variable {w : Set (Lp ℝ 2 μ)} [Countable ↥w]

/-- **White noise on a measure space**, attached to a Hilbert basis of its `L²`:
a centred Gaussian for every square-integrable test function, linear in the test
function, with covariance the `L²` inner product. -/
def whiteNoise (b : HilbertBasis w ℝ (Lp ℝ 2 μ)) (f : X → ℝ) : (↥w → ℝ) → ℝ :=
  isoProc b (toLpOrZero μ f)

omit [Countable ↥w] in
theorem measurable_whiteNoise (b : HilbertBasis w ℝ (Lp ℝ 2 μ)) (f : X → ℝ) :
    Measurable (whiteNoise b f) := measurable_isoProc b _

theorem isGaussianProcess_whiteNoise (b : HilbertBasis w ℝ (Lp ℝ 2 μ)) :
    IsGaussianProcess (whiteNoise b) (gaussLaw ↥w) :=
  (isGaussianProcess_isoProc b).comp_right (toLpOrZero μ)

theorem integral_whiteNoise (b : HilbertBasis w ℝ (Lp ℝ 2 μ)) (f : X → ℝ) :
    ∫ ω, whiteNoise b f ω ∂(gaussLaw ↥w) = 0 := integral_isoProc b _

omit [Countable ↥w] in
theorem integral_whiteNoise_mul (b : HilbertBasis w ℝ (Lp ℝ 2 μ)) {f g : X → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ ω, whiteNoise b f ω * whiteNoise b g ω ∂(gaussLaw ↥w) = ∫ y, f y * g y ∂μ := by
  rw [whiteNoise, whiteNoise, integral_isoProc_mul, inner_toLpOrZero hf hg]

omit [Countable ↥w] in
theorem whiteNoise_add (b : HilbertBasis w ℝ (Lp ℝ 2 μ)) {f g : X → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    whiteNoise b (f + g) =ᵐ[gaussLaw ↥w] fun ω => whiteNoise b f ω + whiteNoise b g ω := by
  rw [whiteNoise, toLpOrZero_add hf hg]
  exact isoProc_add b _ _

omit [Countable ↥w] in
theorem whiteNoise_smul (b : HilbertBasis w ℝ (Lp ℝ 2 μ)) (a : ℝ) {f : X → ℝ}
    (hf : MemLp f 2 μ) :
    whiteNoise b (a • f) =ᵐ[gaussLaw ↥w] fun ω => a * whiteNoise b f ω := by
  rw [whiteNoise, toLpOrZero_smul a hf]
  exact isoProc_smul b a _

end WhiteNoise

end LatticeProb

end
