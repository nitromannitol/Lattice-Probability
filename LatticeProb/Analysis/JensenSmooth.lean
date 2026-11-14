import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Jensen's lemma for smooth functions

Let `φ` be continuous on the closed ball `closedBall c r`, of class `C²` in the open ball, with
`Δ φ ≥ -K` there. Suppose that for `‖p‖ < δ` every maximiser of `φ + ⟪p, ·⟫` over the closed ball
lies in the open ball. Then the set `S` of points of the closed ball that maximise `φ + ⟪p, ·⟫`
over the closed ball for some `‖p‖ < δ` satisfies `μ (ball 0 δ) ≤ K ^ dim E * μ S`
(`LatticeProb.PegdenSmart.jensen_smooth`).

The proof follows Crandall-Ishii-Lions: `S` is a countable union of compact sets; the map
`x ↦ -∇ φ x` sends `S` onto a set containing `ball 0 δ`; at points of `S` the Hessian is
nonpositive with trace at least `-K`, so its eigenvalues lie in `[-K, 0]` and the absolute value of
its determinant is at most `K ^ dim E`; the area formula for `C¹` maps finishes the argument.
-/

open MeasureTheory Metric Filter Topology Set
open scoped InnerProductSpace ContDiff
open Laplacian

namespace LatticeProb.PegdenSmart

/-- Second-order necessary condition at a local maximum of a function on `ℝ`. -/
theorem le_zero_of_isLocalMax_of_hasDerivAt {g k : ℝ → ℝ} {a : ℝ} (hmax : IsLocalMax g 0)
    (hg : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt g (k t) t) (hk : HasDerivAt k a 0) : a ≤ 0 := by
  by_contra ha
  replace ha : 0 < a := not_le.mp ha
  have hdg : deriv g =ᶠ[𝓝 0] k := hg.mono fun t ht => ht.deriv
  have h0 : deriv g 0 = 0 := hmax.deriv_eq_zero
  have h1 : deriv (deriv g) 0 = a := by rw [hdg.deriv_eq]; exact hk.deriv
  have hmin : IsLocalMin g 0 :=
    isLocalMin_of_deriv_deriv_pos (by rw [h1]; exact ha) h0 hg.self_of_nhds.continuousAt
  have heq : g =ᶠ[𝓝 0] fun _ => g 0 := by
    filter_upwards [hmin, hmax] with t h1 h2 using le_antisymm h2 h1
  have hdz : deriv g =ᶠ[𝓝 0] fun _ => (0 : ℝ) :=
    heq.eventuallyEq_nhds.mono fun t ht => by rw [ht.deriv_eq]; simp
  have h2 : deriv (deriv g) 0 = 0 := by rw [hdz.deriv_eq]; simp
  linarith

section LinearAlgebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A positive semidefinite symmetric operator of trace at most `K` has determinant at most
`K ^ dim E` in absolute value. -/
theorem abs_det_le_pow_of_trace_le {B : E →ₗ[ℝ] E} (hB : B.IsSymmetric)
    (hpos : ∀ v, 0 ≤ ⟪B v, v⟫_ℝ) {K : ℝ} (hK : LinearMap.trace ℝ E B ≤ K) :
    |LinearMap.det B| ≤ K ^ Module.finrank ℝ E := by
  have hn : Module.finrank ℝ E = Module.finrank ℝ E := rfl
  have hev : ∀ i, 0 ≤ hB.eigenvalues hn i := by
    intro i
    have h := hB.hasEigenvector_eigenvectorBasis hn i
    have h1 := hpos (hB.eigenvectorBasis hn i)
    rw [h.apply_eq_smul, real_inner_smul_left, real_inner_self_eq_norm_sq,
      OrthonormalBasis.norm_eq_one] at h1
    simpa using h1
  have htr : LinearMap.trace ℝ E B = ∑ i, hB.eigenvalues hn i := by
    simpa using hB.trace_eq_sum_eigenvalues hn
  have hdet : LinearMap.det B = ∏ i, hB.eigenvalues hn i := by
    simpa using hB.det_eq_prod_eigenvalues hn
  have hle : ∀ i, hB.eigenvalues hn i ≤ K := fun i =>
    (Finset.single_le_sum (fun j _ => hev j) (Finset.mem_univ i)).trans (htr ▸ hK)
  rw [hdet, abs_of_nonneg (Finset.prod_nonneg fun i _ => hev i)]
  calc ∏ i, hB.eigenvalues hn i ≤ ∏ _i : Fin (Module.finrank ℝ E), K :=
        Finset.prod_le_prod₀ (fun i _ => hev i) fun i _ => hle i
    _ = K ^ Module.finrank ℝ E := by simp

end LinearAlgebra

section Hessian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Hessian of `φ` at `x` as an endomorphism: `⟪hessianOp φ x v, w⟫ = D²φ(x)(v, w)`. -/
noncomputable def hessianOp (φ : E → ℝ) (x : E) : E →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    fderiv ℝ (fderiv ℝ φ) x

theorem inner_hessianOp (φ : E → ℝ) (x v w : E) :
    ⟪hessianOp φ x v, w⟫_ℝ = fderiv ℝ (fderiv ℝ φ) x v w := by
  simp [hessianOp]

theorem hasFDerivAt_gradient {φ : E → ℝ} {x : E} (h : DifferentiableAt ℝ (fderiv ℝ φ) x) :
    HasFDerivAt (gradient φ) (hessianOp φ x) x :=
  ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
    ).comp x h.hasFDerivAt

theorem isSymmetric_hessianOp {φ : E → ℝ} {x : E} (h : ContDiffAt ℝ 2 φ x) :
    (hessianOp φ x : E →ₗ[ℝ] E).IsSymmetric := by
  intro v w
  have hsymm := h.isSymmSndFDerivAt (by simp)
  simp only [ContinuousLinearMap.coe_coe]
  rw [inner_hessianOp, real_inner_comm, inner_hessianOp]
  exact hsymm v w

theorem trace_hessianOp (φ : E → ℝ) (x : E) :
    LinearMap.trace ℝ E (hessianOp φ x : E →ₗ[ℝ] E) = Δ φ x := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp only [ContinuousLinearMap.coe_coe, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [real_inner_comm, inner_hessianOp]

theorem gradient_eq_neg_of_isLocalMax {φ : E → ℝ} {x p : E} (hφ : DifferentiableAt ℝ φ x)
    (hmax : IsLocalMax (fun y => φ y + ⟪p, y⟫_ℝ) x) : gradient φ x = -p := by
  have h0 : fderiv ℝ (fun y => φ y + ⟪p, y⟫_ℝ) x = 0 := hmax.fderiv_eq_zero
  have hd : HasFDerivAt (fun y => φ y + ⟪p, y⟫_ℝ) (fderiv ℝ φ x + innerSL ℝ p) x :=
    hφ.hasFDerivAt.add (innerSL ℝ p).hasFDerivAt
  rw [hd.fderiv] at h0
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, inner_neg_left]
  have := congrArg (fun L => L v) h0
  simp at this
  linarith

omit [FiniteDimensional ℝ E] in
/-- At a local maximum of `φ + ⟪p, ·⟫`, the second derivative of `φ` is nonpositive on the diagonal. -/
theorem hessian_apply_self_nonpos {φ : E → ℝ} {x p : E}
    (hφ : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 φ y)
    (hmax : IsLocalMax (fun y => φ y + ⟪p, y⟫_ℝ) x) (v : E) :
    fderiv ℝ (fderiv ℝ φ) x v v ≤ 0 := by
  have hx : ContDiffAt ℝ 2 φ x := hφ.self_of_nhds
  have hFD : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hx.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  set γ : ℝ → E := fun t => x + t • v with hγ
  have hγd : ∀ t, HasDerivAt γ v t := fun t => by
    have h := ((hasDerivAt_id' t).smul_const v).const_add x
    rwa [one_smul] at h
  have hγ0 : γ 0 = x := by simp [hγ]
  have hγc : ContinuousAt γ 0 := (hγd 0).continuousAt
  have hmaxg : IsLocalMax (fun t => φ (γ t) + ⟪p, γ t⟫_ℝ) 0 := by
    have : IsLocalMax (fun y => φ y + ⟪p, y⟫_ℝ) (γ 0) := by rwa [hγ0]
    exact this.comp_continuous hγc
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 φ (γ t) := by
    have := hγc.eventually (hγ0 ▸ hφ)
    exact this
  have hg : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (fun t => φ (γ t) + ⟪p, γ t⟫_ℝ)
      (fderiv ℝ φ (γ t) v + ⟪p, v⟫_ℝ) t := by
    filter_upwards [hev] with t ht
    have h1 : HasFDerivAt (fun y => φ y + ⟪p, y⟫_ℝ) (fderiv ℝ φ (γ t) + innerSL ℝ p) (γ t) :=
      (ht.differentiableAt (by simp)).hasFDerivAt.add (innerSL ℝ p).hasFDerivAt
    have h2 := h1.comp_hasDerivAt t (hγd t)
    have h3 : (fderiv ℝ φ (γ t) + innerSL ℝ p) v = fderiv ℝ φ (γ t) v + ⟪p, v⟫_ℝ := by simp
    rw [h3] at h2
    exact h2
  have hk : HasDerivAt (fun t => fderiv ℝ φ (γ t) v + ⟪p, v⟫_ℝ)
      (fderiv ℝ (fderiv ℝ φ) x v v) 0 := by
    have h1 : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) x) (γ 0) := by
      rw [hγ0]; exact hFD.hasFDerivAt
    have h2 := h1.comp_hasDerivAt (0 : ℝ) (hγd 0)
    have h3 := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
    simpa using h3.add_const ⟪p, v⟫_ℝ
  exact le_zero_of_isLocalMax_of_hasDerivAt hmaxg hg hk

end Hessian

section Jensen

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The set of maximisers over a compact set `B` of `φ + ⟪p, ·⟫` with `‖p‖ < δ` is a countable
union of compact sets, hence measurable. -/
theorem measurableSet_maximisers [MeasurableSpace E] [BorelSpace E] {φ : E → ℝ} {B : Set E}
    (hB : IsCompact B) (hφ : ContinuousOn φ B) (δ : ℝ) :
    MeasurableSet {x ∈ B | ∃ p : E, ‖p‖ < δ ∧ ∀ y ∈ B, φ y + ⟪p, y⟫_ℝ ≤ φ x + ⟪p, x⟫_ℝ} := by
  set Z : ℕ → Set (E × E) := fun n => (B ×ˢ closedBall (0 : E) (δ - 1 / ((n : ℝ) + 1))) ∩
    ⋂ y ∈ B, ((B ×ˢ closedBall (0 : E) (δ - 1 / ((n : ℝ) + 1))) ∩
      (fun z : E × E => φ z.1 + ⟪z.2, z.1⟫_ℝ - φ y - ⟪z.2, y⟫_ℝ) ⁻¹' Ici 0) with hZ
  have hZc : ∀ n, IsCompact (Z n) := fun n => by
    have hs : IsCompact (B ×ˢ closedBall (0 : E) (δ - 1 / ((n : ℝ) + 1))) :=
      hB.prod (isCompact_closedBall _ _)
    refine hs.of_isClosed_subset ?_ inter_subset_left
    refine hs.isClosed.inter (isClosed_biInter fun y _ => ?_)
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ hs.isClosed isClosed_Ici
    have h1 : ContinuousOn (fun z : E × E => φ z.1) (B ×ˢ closedBall (0 : E) (δ - 1 / ((n : ℝ) + 1))) :=
      hφ.comp continuousOn_fst fun z hz => hz.1
    exact ((h1.add (continuous_snd.inner continuous_fst).continuousOn).sub
      continuousOn_const).sub (continuous_snd.inner continuous_const).continuousOn
  have hS : {x ∈ B | ∃ p : E, ‖p‖ < δ ∧ ∀ y ∈ B, φ y + ⟪p, y⟫_ℝ ≤ φ x + ⟪p, x⟫_ℝ} =
      ⋃ n : ℕ, Prod.fst '' Z n := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_image, hZ, mem_inter_iff, mem_prod, mem_closedBall,
      dist_zero_right, mem_iInter, mem_preimage, mem_Ici, Prod.exists, exists_and_right,
      exists_eq_right]
    constructor
    · rintro ⟨hxB, p, hp, hmax⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hp)
      refine ⟨n, p, ⟨⟨hxB, ?_⟩, fun y hy => ⟨⟨hxB, ?_⟩, ?_⟩⟩⟩
      · linarith
      · linarith
      · linarith [hmax y hy]
    · rintro ⟨n, p, ⟨⟨hxB, hp⟩, hmax⟩⟩
      refine ⟨hxB, p, ?_, fun y hy => ?_⟩
      · have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · linarith [(hmax y hy).2]
  rw [hS]
  exact MeasurableSet.iUnion fun n => ((hZc n).image continuous_fst).isClosed.measurableSet

/-- (P1) Jensen's lemma for a `C²` function: let `φ` be continuous on the closed ball
`closedBall c r`, of class `C²` in the open ball, with `Δ φ ≥ -K` there, and suppose that for
`‖p‖ < δ` every maximiser of `φ + ⟪p, ·⟫` over the closed ball lies in the open ball. Then the set
of points of the closed ball that maximise `φ + ⟪p, ·⟫` over the closed ball for some `‖p‖ < δ`
satisfies `μ (ball 0 δ) ≤ K ^ dim E * μ (that set)`. -/
theorem jensen_smooth [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (φ : E → ℝ) (c : E) (r K δ : ℝ) (hr : 0 < r) (hK : 0 ≤ K) (_hδ : 0 < δ)
    (hcont : ContinuousOn φ (closedBall c r)) (hC2 : ContDiffOn ℝ 2 φ (ball c r))
    (hΔ : ∀ x ∈ ball c r, -K ≤ Δ φ x)
    (hint : ∀ p : E, ‖p‖ < δ → ∀ x ∈ closedBall c r,
      (∀ y ∈ closedBall c r, φ y + ⟪p, y⟫_ℝ ≤ φ x + ⟪p, x⟫_ℝ) → x ∈ ball c r) :
    μ (ball (0 : E) δ) ≤
      ENNReal.ofReal K ^ Module.finrank ℝ E *
        μ {x ∈ closedBall c r | ∃ p : E, ‖p‖ < δ ∧
          ∀ y ∈ closedBall c r, φ y + ⟪p, y⟫_ℝ ≤ φ x + ⟪p, x⟫_ℝ} := by
  set S : Set E := {x ∈ closedBall c r | ∃ p : E, ‖p‖ < δ ∧
    ∀ y ∈ closedBall c r, φ y + ⟪p, y⟫_ℝ ≤ φ x + ⟪p, x⟫_ℝ} with hS
  have hSmeas : MeasurableSet S := measurableSet_maximisers (isCompact_closedBall c r) hcont δ
  have hCD : ∀ x ∈ ball c r, ContDiffAt ℝ 2 φ x := fun x hx =>
    hC2.contDiffAt (isOpen_ball.mem_nhds hx)
  have hFD : ∀ x ∈ ball c r, DifferentiableAt ℝ (fderiv ℝ φ) x := fun x hx =>
    ((hCD x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hloc : ∀ p : E, ‖p‖ < δ → ∀ x ∈ closedBall c r,
      (∀ y ∈ closedBall c r, φ y + ⟪p, y⟫_ℝ ≤ φ x + ⟪p, x⟫_ℝ) →
        x ∈ ball c r ∧ IsLocalMax (fun y => φ y + ⟪p, y⟫_ℝ) x := by
    intro p hp x hxB hmax
    have hx := hint p hp x hxB hmax
    exact ⟨hx, (isMaxOn_iff.2 hmax).isLocalMax
      (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)⟩
  have hcover : ball (0 : E) δ ⊆ (fun x => -gradient φ x) '' S := by
    intro p hp
    rw [mem_ball_zero_iff] at hp
    have hΦ : ContinuousOn (fun y => φ y + ⟪p, y⟫_ℝ) (closedBall c r) :=
      hcont.add (continuous_const.inner continuous_id).continuousOn
    obtain ⟨x, hxB, hxmax⟩ := (isCompact_closedBall c r).exists_isMaxOn
      ⟨c, mem_closedBall_self hr.le⟩ hΦ
    have hmax := isMaxOn_iff.1 hxmax
    obtain ⟨hx, hlm⟩ := hloc p hp x hxB hmax
    refine ⟨x, ⟨hxB, p, hp, hmax⟩, ?_⟩
    show -gradient φ x = p
    rw [gradient_eq_neg_of_isLocalMax ((hCD x hx).differentiableAt (by simp)) hlm, neg_neg]
  have hderiv : ∀ x ∈ S, HasFDerivWithinAt (fun y => -gradient φ y) (-(hessianOp φ x)) S x := by
    rintro x ⟨hxB, p, hp, hmax⟩
    have hx := (hloc p hp x hxB hmax).1
    exact (hasFDerivAt_gradient (hFD x hx)).neg.hasFDerivWithinAt
  have hdet : ∀ x ∈ S, |(-(hessianOp φ x)).det| ≤ K ^ Module.finrank ℝ E := by
    rintro x ⟨hxB, p, hp, hmax⟩
    obtain ⟨hx, hlm⟩ := hloc p hp x hxB hmax
    have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 φ y :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) fun y hy => hCD y hy
    have hsymm := isSymmetric_hessianOp (hCD x hx)
    show |LinearMap.det (-(hessianOp φ x : E →ₗ[ℝ] E))| ≤ _
    refine abs_det_le_pow_of_trace_le ?_ ?_ ?_
    · intro v w
      simp only [LinearMap.neg_apply, inner_neg_left, inner_neg_right]
      exact congrArg Neg.neg (hsymm v w)
    · intro v
      simp only [LinearMap.neg_apply, inner_neg_left, ContinuousLinearMap.coe_coe,
        inner_hessianOp]
      linarith [hessian_apply_self_nonpos hev hlm v]
    · rw [map_neg, trace_hessianOp]
      linarith [hΔ x hx]
  calc μ (ball (0 : E) δ) ≤ μ ((fun x => -gradient φ x) '' S) := measure_mono hcover
    _ ≤ ∫⁻ x in S, ENNReal.ofReal |(-(hessianOp φ x)).det| ∂μ :=
        addHaar_image_le_lintegral_abs_det_fderiv μ hSmeas hderiv
    _ ≤ ∫⁻ _ in S, ENNReal.ofReal (K ^ Module.finrank ℝ E) ∂μ :=
        setLIntegral_mono' hSmeas fun x hx => ENNReal.ofReal_le_ofReal (hdet x hx)
    _ = ENNReal.ofReal K ^ Module.finrank ℝ E * μ S := by
        rw [setLIntegral_const, ENNReal.ofReal_pow hK]

end Jensen

end LatticeProb.PegdenSmart
