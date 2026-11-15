import LatticeProb.Analysis.Elliptic.Dirichlet

/-!
# The zero-boundary first-order Sobolev graph

The ambient space is the Hilbert product of one scalar L² function and its coordinate
L² derivatives, with Lebesgue measure restricted to the domain. The zero-boundary space
is the closure of the graphs of smooth functions compactly supported inside the domain.
Its elements satisfy the distributional derivative identities. The weak Dirichlet equation
is an integrable identity against every such test function.
-/

namespace LatticeProb.Elliptic.WeakDirichlet

open MeasureTheory
open scoped ENNReal BigOperators Topology

noncomputable section

variable {d : ℕ}

/-- A real smooth function whose compact topological support lies inside `U`. -/
structure TestFunction (U : Set (Fin d → ℝ)) where
  val : (Fin d → ℝ) → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) val
  compact : HasCompactSupport val
  supported : tsupport val ⊆ U

/-- Differentiation preserves smoothness and compact support inside the domain. -/
def TestFunction.deriv {U : Set (Fin d → ℝ)} (φ : TestFunction U) (i : Fin d) :
    TestFunction U where
  val := partialDeriv i φ.val
  smooth := (φ.smooth.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  compact := φ.compact.fderiv_apply ℝ (Pi.single i 1)
  supported := (tsupport_fderiv_apply_subset ℝ _).trans φ.supported

/-- Every smooth compactly supported test is genuinely square integrable on `U`. -/
theorem TestFunction.memLp {U : Set (Fin d → ℝ)} (φ : TestFunction U) :
    MemLp φ.val 2 (volume.restrict U) :=
  (φ.smooth.continuous.memLp_of_hasCompactSupport φ.compact).mono_measure
    Measure.restrict_le_self

/-- The L² equivalence class of a test function, with no choice of representative. -/
def TestFunction.toL2 {U : Set (Fin d → ℝ)} (φ : TestFunction U) :
    Lp ℝ 2 (volume.restrict U) := φ.memLp.toLp φ.val

/-- One L² function coordinate together with `d` L² coordinates for derivatives.
The `PiLp 2` norm is the square root of the sum of the squared L² norms. -/
abbrev H1Product (U : Set (Fin d → ℝ)) :=
  PiLp 2 (fun _ : Fin (d + 1) => Lp ℝ 2 (volume.restrict U))

/-- The zeroth coordinate is the function; successor coordinates are its derivatives. -/
def TestFunction.graph {U : Set (Fin d → ℝ)} (φ : TestFunction U) : H1Product U :=
  WithLp.toLp 2 (Fin.cons φ.toL2 (fun i => (φ.deriv i).toL2))

/-- The squared product norm is exactly the H¹ sum of the squared L² norms. -/
theorem h1Product_norm_sq {U : Set (Fin d → ℝ)} (v : H1Product U) :
    ‖v‖ ^ 2 = ‖v 0‖ ^ 2 + ∑ i : Fin d, ‖v i.succ‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]

/-- Each L² norm is the square root of the actual Lebesgue integral on `U`. -/
theorem l2_norm_sq {U : Set (Fin d → ℝ)} (v : Lp ℝ 2 (volume.restrict U)) :
    ‖v‖ ^ 2 = ∫ x in U, (v x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change v x * v x = v x ^ 2
    ring

/-- Expanded H¹ norm: the function and all coordinate gradients use restricted volume. -/
theorem h1Product_norm_sq_integral {U : Set (Fin d → ℝ)} (v : H1Product U) :
    ‖v‖ ^ 2 = (∫ x in U, (v 0 x) ^ 2) +
      ∑ i : Fin d, ∫ x in U, (v i.succ x) ^ 2 := by
  rw [h1Product_norm_sq]
  simp_rw [l2_norm_sq]

/-- The literal H¹₀ graph: closure of actual smooth supported graphs in the H¹ norm.
No injection of its first coordinate or trace identification is asserted here. -/
def H10 (U : Set (Fin d → ℝ)) :=
  {v : H1Product U // v ∈ closure (Set.range (TestFunction.graph (U := U)))}

/-- Every actual smooth supported graph belongs to the zero-boundary closure. -/
def TestFunction.toH10 {U : Set (Fin d → ℝ)} (φ : TestFunction U) : H10 U :=
  ⟨φ.graph, subset_closure ⟨φ, rfl⟩⟩

/-- L² pairing with a test equals the literal integral of its smooth representative. -/
theorem inner_test {U : Set (Fin d → ℝ)} (v : Lp ℝ 2 (volume.restrict U))
    (φ : TestFunction U) :
    inner ℝ v φ.toL2 = ∫ x in U, v x * φ.val x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [φ.memLp.coeFn_toLp] with x hx
  change φ.toL2 x * v x = v x * φ.val x
  change φ.toL2 x = φ.val x at hx
  rw [hx, mul_comm]

/-- The products occurring in a distributional derivative test are integrable. -/
theorem integrable_mul_test {U : Set (Fin d → ℝ)}
    (v : Lp ℝ 2 (volume.restrict U)) (φ : TestFunction U) :
    Integrable (fun x => v x * φ.val x) (volume.restrict U) :=
  (Lp.memLp v).integrable_mul φ.memLp

/-- Smooth supported functions obey integration by parts on the domain. -/
theorem TestFunction.integration_by_parts {U : Set (Fin d → ℝ)}
    (φ ψ : TestFunction U) (i : Fin d) :
    (∫ x in U, φ.val x * (ψ.deriv i).val x) =
      -(∫ x in U, (φ.deriv i).val x * ψ.val x) := by
  have hleft : (∫ x in U, φ.val x * (ψ.deriv i).val x) =
      ∫ x, φ.val x * (ψ.deriv i).val x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (φ.supported h)), zero_mul]
  have hright : (∫ x in U, (φ.deriv i).val x * ψ.val x) =
      ∫ x, (φ.deriv i).val x * ψ.val x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (ψ.supported h)), mul_zero]
  rw [hleft, hright]
  dsimp only [TestFunction.deriv, partialDeriv]
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact ((φ.deriv i).smooth.continuous.mul ψ.smooth.continuous).integrable_of_hasCompactSupport
      ψ.compact.mul_left
  · exact (φ.smooth.continuous.mul (ψ.deriv i).smooth.continuous).integrable_of_hasCompactSupport
      φ.compact.mul_right
  · exact (φ.smooth.continuous.mul ψ.smooth.continuous).integrable_of_hasCompactSupport
      φ.compact.mul_right
  · intro x _
    exact φ.smooth.differentiable (by simp) x
  · intro x _
    exact ψ.smooth.differentiable (by simp) x

/-- Every closure element has the stated coordinate as a genuine weak derivative.
Both integrands are integrable by `integrable_mul_test`. -/
theorem distributional_derivative {U : Set (Fin d → ℝ)} (v : H10 U)
    (ψ : TestFunction U) (i : Fin d) :
    (∫ x in U, v.val 0 x * (ψ.deriv i).val x) =
      -(∫ x in U, v.val i.succ x * ψ.val x) := by
  have hc : IsClosed {w : H1Product U |
      inner ℝ (w 0) (ψ.deriv i).toL2 = -inner ℝ (w i.succ) ψ.toL2} :=
    isClosed_eq ((PiLp.continuous_apply 2 _ 0).inner continuous_const)
      (((PiLp.continuous_apply 2 _ i.succ).inner continuous_const).neg)
  have hs : Set.range (TestFunction.graph (U := U)) ⊆
      {w : H1Product U |
        inner ℝ (w 0) (ψ.deriv i).toL2 = -inner ℝ (w i.succ) ψ.toL2} := by
    rintro _ ⟨φ, rfl⟩
    change inner ℝ φ.toL2 (ψ.deriv i).toL2 =
      -inner ℝ (φ.deriv i).toL2 ψ.toL2
    rw [inner_test, inner_test]
    have hφ := φ.memLp.coeFn_toLp
    have hdφ := (φ.deriv i).memLp.coeFn_toLp
    calc
      (∫ x in U, φ.toL2 x * (ψ.deriv i).val x) =
          ∫ x in U, φ.val x * (ψ.deriv i).val x := by
        apply integral_congr_ae
        filter_upwards [hφ] with x hx
        change φ.toL2 x = φ.val x at hx
        exact congrArg (· * (ψ.deriv i).val x) hx
      _ = -(∫ x in U, (φ.deriv i).val x * ψ.val x) :=
        φ.integration_by_parts ψ i
      _ = -(∫ x in U, (φ.deriv i).toL2 x * ψ.val x) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hdφ] with x hx
        change (φ.deriv i).toL2 x = (φ.deriv i).val x at hx
        exact congrArg (· * ψ.val x) hx.symm
  have h := closure_minimal hs hc v.property
  change inner ℝ (v.val 0) (ψ.deriv i).toL2 =
    -inner ℝ (v.val i.succ) ψ.toL2 at h
  rw [inner_test, inner_test] at h
  exact h

/-- Literal weak equation against every real smooth compactly supported test.
Integrability is part of the predicate, so the integral cannot use its undefined-case value. -/
def IsWeakSolution (U : Set (Fin d → ℝ)) (μ a₀ : ℝ)
    (f : (Fin d → ℝ) → ℝ) (u : H10 U) : Prop :=
  ∀ φ : TestFunction U,
    Integrable (fun x => μ * u.val 0 x * φ.val x +
      a₀ * ∑ i : Fin d, u.val i.succ x * (φ.deriv i).val x) (volume.restrict U) ∧
    Integrable (fun x => f x * φ.val x) (volume.restrict U) ∧
    (∫ x in U, μ * u.val 0 x * φ.val x +
      a₀ * ∑ i : Fin d, u.val i.succ x * (φ.deriv i).val x) =
      ∫ x in U, f x * φ.val x

/-- The energy integrand is integrable for every H¹₀ graph and smooth test. -/
theorem integrable_energy {U : Set (Fin d → ℝ)} (u : H10 U)
    (μ a₀ : ℝ) (φ : TestFunction U) :
    Integrable (fun x => μ * u.val 0 x * φ.val x +
      a₀ * ∑ i : Fin d, u.val i.succ x * (φ.deriv i).val x) (volume.restrict U) := by
  have hm : Integrable (fun x => μ * u.val 0 x * φ.val x) (volume.restrict U) := by
    simpa only [mul_assoc] using (integrable_mul_test (u.val 0) φ).const_mul μ
  have hg : Integrable (fun x => a₀ * ∑ i : Fin d,
      u.val i.succ x * (φ.deriv i).val x) (volume.restrict U) :=
    (integrable_finsetSum Finset.univ
      (fun i _ => integrable_mul_test (u.val i.succ) (φ.deriv i))).const_mul a₀
  exact hm.add hg

/-- The manufactured forcing is the mass term minus diffusivity times the actual Laplacian. -/
def TestFunction.forcing {U : Set (Fin d → ℝ)} (φ : TestFunction U) (μ a₀ : ℝ)
    (x : Fin d → ℝ) : ℝ :=
  μ * φ.val x - a₀ * ∑ i : Fin d, ((φ.deriv i).deriv i).val x

/-- Manufactured forcing is genuinely smooth. -/
theorem TestFunction.smooth_forcing {U : Set (Fin d → ℝ)} (φ : TestFunction U)
    (μ a₀ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (φ.forcing μ a₀) := by
  exact (contDiff_const.mul φ.smooth).sub
    (contDiff_const.mul (ContDiff.sum fun i _ => ((φ.deriv i).deriv i).smooth))

/-- Integration by parts gives the manufactured weak equation on smooth representatives. -/
theorem TestFunction.energy_eq_forcing {U : Set (Fin d → ℝ)} (φ ψ : TestFunction U)
    (μ a₀ : ℝ) :
    (∫ x in U, μ * φ.val x * ψ.val x +
      a₀ * ∑ i : Fin d, (φ.deriv i).val x * (ψ.deriv i).val x) =
      ∫ x in U, φ.forcing μ a₀ x * ψ.val x := by
  have hm : Integrable (fun x => φ.val x * ψ.val x) (volume.restrict U) :=
    φ.memLp.integrable_mul ψ.memLp
  have hg (i : Fin d) : Integrable
      (fun x => (φ.deriv i).val x * (ψ.deriv i).val x) (volume.restrict U) :=
    (φ.deriv i).memLp.integrable_mul (ψ.deriv i).memLp
  have hh (i : Fin d) : Integrable
      (fun x => ((φ.deriv i).deriv i).val x * ψ.val x) (volume.restrict U) :=
    ((φ.deriv i).deriv i).memLp.integrable_mul ψ.memLp
  have hs := integrable_finsetSum Finset.univ (fun i _ => hg i)
  have ht := integrable_finsetSum Finset.univ (fun i _ => hh i)
  have hpoint (x : Fin d → ℝ) : φ.forcing μ a₀ x * ψ.val x =
      μ * (φ.val x * ψ.val x) -
        a₀ * ∑ i : Fin d, ((φ.deriv i).deriv i).val x * ψ.val x := by
    simp only [TestFunction.forcing, sub_mul, mul_assoc, Finset.sum_mul]
  simp_rw [hpoint, mul_assoc μ]
  rw [integral_add (hm.const_mul μ) (hs.const_mul a₀),
    integral_sub (hm.const_mul μ) (ht.const_mul a₀)]
  simp only [integral_const_mul]
  rw [integral_finsetSum _ (fun i _ => hg i),
    integral_finsetSum _ (fun i _ => hh i)]
  simp_rw [TestFunction.integration_by_parts (φ.deriv _) ψ _]
  rw [Finset.sum_neg_distrib]
  ring

/-- Every actual smooth supported graph solves its manufactured equation. -/
theorem TestFunction.isWeakSolution_forcing {U : Set (Fin d → ℝ)}
    (φ : TestFunction U) (μ a₀ : ℝ) :
    IsWeakSolution U μ a₀ (φ.forcing μ a₀) φ.toH10 := by
  intro ψ
  refine ⟨integrable_energy φ.toH10 μ a₀ ψ, ?_, ?_⟩
  · have hc := (φ.smooth_forcing μ a₀).continuous.mul ψ.smooth.continuous
    exact (hc.integrable_of_hasCompactSupport ψ.compact.mul_left).restrict
  · have hvalue : φ.toH10.val 0 = φ.toL2 := rfl
    have hgrad (i : Fin d) : φ.toH10.val i.succ = (φ.deriv i).toL2 := rfl
    calc
      _ = ∫ x in U, μ * φ.val x * ψ.val x +
          a₀ * ∑ i : Fin d, (φ.deriv i).val x * (ψ.deriv i).val x := by
        apply integral_congr_ae
        have ha : ∀ᵐ x ∂volume.restrict U, ∀ i : Fin d,
            (φ.deriv i).toL2 x = (φ.deriv i).val x :=
          ae_all_iff.mpr (fun i => (φ.deriv i).memLp.coeFn_toLp)
        filter_upwards [φ.memLp.coeFn_toLp, ha] with x hx hg
        change φ.toL2 x = φ.val x at hx
        simp only [hvalue, hgrad, hx, hg]
      _ = _ := φ.energy_eq_forcing ψ μ a₀

/-- The smooth graph represents the supplied function almost everywhere on the domain. -/
theorem TestFunction.toH10_value {U : Set (Fin d → ℝ)} (φ : TestFunction U) :
    (fun x => φ.toH10.val 0 x) =ᵐ[volume.restrict U] φ.val :=
  φ.memLp.coeFn_toLp

/-- Each gradient coordinate is the actual coordinate derivative almost everywhere. -/
theorem TestFunction.toH10_deriv {U : Set (Fin d → ℝ)} (φ : TestFunction U)
    (i : Fin d) :
    (fun x => φ.toH10.val i.succ x) =ᵐ[volume.restrict U] partialDeriv i φ.val :=
  (φ.deriv i).memLp.coeFn_toLp

/-- The manufactured forcing agrees with the existing coordinate Hessian Laplacian. -/
theorem TestFunction.forcing_eq_laplacian {U : Set (Fin d → ℝ)}
    (φ : TestFunction U) (μ a₀ : ℝ) (x : Fin d → ℝ) :
    φ.forcing μ a₀ x = μ * φ.val x - a₀ * laplacian φ.val x := by
  unfold TestFunction.forcing laplacian
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  have htwo : ContDiff ℝ 2 φ.val :=
    φ.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [secondPartial_eq_fderiv_partialDeriv htwo]
  rfl

/-- The zero test function has compact support inside every domain, including the empty one. -/
def zeroTest (U : Set (Fin d → ℝ)) : TestFunction U where
  val := fun _ => 0
  smooth := contDiff_const
  compact := HasCompactSupport.zero
  supported := by
    change tsupport (0 : (Fin d → ℝ) → ℝ) ⊆ U
    rw [tsupport_zero]
    exact Set.empty_subset U

/-- The zero graph solves the zero-forcing equation at every mass and diffusivity. -/
theorem zeroTest_isWeakSolution (U : Set (Fin d → ℝ)) (μ a₀ : ℝ) :
    IsWeakSolution U μ a₀ (fun _ => 0) (zeroTest U).toH10 := by
  have hf : (zeroTest U).forcing μ a₀ = fun _ => 0 := by
    have hd (i : Fin d) : partialDeriv i (fun _ : Fin d → ℝ => (0 : ℝ)) =
        fun _ => 0 := by
      funext x
      unfold partialDeriv
      rw [fderiv_fun_const]
      rfl
    funext x
    change μ * 0 - a₀ * ∑ i : Fin d,
      partialDeriv i (partialDeriv i (fun _ : Fin d → ℝ => 0)) x = 0
    simp only [hd, mul_zero, Finset.sum_const_zero, sub_zero]
  rw [← hf]
  exact (zeroTest U).isWeakSolution_forcing μ a₀

/-- The Euclidean unit ball is written with the sum of coordinate squares, not the Pi norm. -/
def unitBall (d : ℕ) : Set (Fin d → ℝ) := {x | ∑ i : Fin d, x i ^ 2 < 1}

/-- The Euclidean unit ball is open in the ordinary coordinate topology. -/
theorem isOpen_unitBall (d : ℕ) : IsOpen (unitBall d) :=
  isOpen_lt (by fun_prop) continuous_const

/-- A genuine nonzero smooth supported solution exists in the Euclidean unit ball.
Its L² function is nonzero, its gradients are actual derivatives, and its manufactured
forcing is smooth for every mass and diffusivity, including zero mass. -/
theorem exists_nonzero_unitBall (d : ℕ) :
    ∃ φ : TestFunction (unitBall d), φ.val 0 = 1 ∧ φ.toL2 ≠ 0 ∧
      ∀ μ a₀ : ℝ, IsWeakSolution (unitBall d) μ a₀ (φ.forcing μ a₀) φ.toH10 := by
  have hzero : (0 : Fin d → ℝ) ∈ unitBall d := by simp [unitBall]
  obtain ⟨f, hsupp, hcompact, hsmooth, _, hone⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) ((isOpen_unitBall d).mem_nhds hzero)
  let φ : TestFunction (unitBall d) := ⟨f, hsmooth, hcompact, hsupp⟩
  refine ⟨φ, hone, ?_, fun μ a₀ => φ.isWeakSolution_forcing μ a₀⟩
  intro hz
  have hae : φ.val =ᵐ[volume.restrict (unitBall d)] (fun _ => (0 : ℝ)) := by
    have hp := φ.memLp.coeFn_toLp
    change (φ.toL2 : (Fin d → ℝ) → ℝ) =ᵐ[volume.restrict (unitBall d)] φ.val at hp
    rw [hz] at hp
    exact hp.symm.trans (Lp.coeFn_zero _ _ _)
  have heq := Measure.eqOn_open_of_ae_eq hae (isOpen_unitBall d)
    φ.smooth.continuous.continuousOn continuous_const.continuousOn
  have h0 := heq hzero
  change f 0 = 0 at h0
  rw [hone] at h0
  exact one_ne_zero h0

end

end LatticeProb.Elliptic.WeakDirichlet
