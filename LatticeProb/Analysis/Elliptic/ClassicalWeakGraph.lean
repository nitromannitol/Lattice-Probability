import LatticeProb.External.GilbargTrudingerSobolev
import LatticeProb.Analysis.Elliptic.Examples

/-!
# Classical functions in the first-order Sobolev graph

A globally twice continuously differentiable function on a bounded domain determines
its actual L² function and derivative coordinates. Compactly supported tests give
integration by parts without any support assumption on the classical function.
-/

namespace LatticeProb.Elliptic.WeakDirichlet

open MeasureTheory
open scoped ENNReal BigOperators Topology

noncomputable section

variable {d : ℕ} {U : Set (Fin d → ℝ)} {v : (Fin d → ℝ) → ℝ}

/-- Continuity on a compact closure gives square integrability on a bounded domain. -/
theorem memLp_of_continuous_bounded (hv : Continuous v) (hU : Bornology.IsBounded U) :
    MemLp v 2 (volume.restrict U) := by
  apply (memLp_two_iff_integrable_sq hv.aestronglyMeasurable).2
  exact ((hv.pow 2).continuousOn.integrableOn_compact hU.isCompact_closure).mono_set
    subset_closure

/-- First coordinate derivatives of a C² function are C¹. -/
theorem contDiff_partialDeriv (hv : ContDiff ℝ 2 v) (i : Fin d) :
    ContDiff ℝ 1 (partialDeriv i v) :=
  (hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- The genuine Sobolev graph, formed directly from the function and every first partial. -/
def classicalGraph (hv : ContDiff ℝ 2 v) (hU : Bornology.IsBounded U) : H1Product U :=
  WithLp.toLp 2 (Fin.cons
    ((memLp_of_continuous_bounded hv.continuous hU).toLp v)
    (fun i => (memLp_of_continuous_bounded (contDiff_partialDeriv hv i).continuous hU).toLp
      (partialDeriv i v)))

/-- The value coordinate is the original function almost everywhere. -/
theorem classicalGraph_value (hv : ContDiff ℝ 2 v) (hU : Bornology.IsBounded U) :
    (fun x => classicalGraph hv hU 0 x) =ᵐ[volume.restrict U] v :=
  (memLp_of_continuous_bounded hv.continuous hU).coeFn_toLp

/-- Every derivative coordinate is its actual partial derivative almost everywhere. -/
theorem classicalGraph_deriv (hv : ContDiff ℝ 2 v) (hU : Bornology.IsBounded U)
    (i : Fin d) :
    (fun x => classicalGraph hv hU i.succ x) =ᵐ[volume.restrict U] partialDeriv i v :=
  (memLp_of_continuous_bounded (contDiff_partialDeriv hv i).continuous hU).coeFn_toLp

/-- Equality of every coordinate characterizes the graph uniquely. -/
theorem eq_classicalGraph_iff (hv : ContDiff ℝ 2 v) (hU : Bornology.IsBounded U)
    (w : H1Product U) :
    w = classicalGraph hv hU ↔
      (fun x => w 0 x) =ᵐ[volume.restrict U] v ∧
      ∀ i : Fin d, (fun x => w i.succ x) =ᵐ[volume.restrict U] partialDeriv i v := by
  constructor
  · rintro rfl
    exact ⟨classicalGraph_value hv hU, classicalGraph_deriv hv hU⟩
  · rintro ⟨hval, hder⟩
    apply PiLp.ext
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact Lp.ext (hval.trans (classicalGraph_value hv hU).symm)
    · exact Lp.ext ((hder i).trans (classicalGraph_deriv hv hU i).symm)

/-- A C¹ function integrates by parts against every smooth supported test on the domain. -/
theorem integration_by_parts_classical (hv : ContDiff ℝ 1 v)
    (ψ : TestFunction U) (i : Fin d) :
    (∫ x in U, v x * (ψ.deriv i).val x) =
      -(∫ x in U, partialDeriv i v x * ψ.val x) := by
  have hd : Continuous (partialDeriv i v) :=
    ((hv.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous
  have hleft : (∫ x in U, v x * (ψ.deriv i).val x) =
      ∫ x, v x * (ψ.deriv i).val x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx ((ψ.deriv i).supported h)), mul_zero]
  have hright : (∫ x in U, partialDeriv i v x * ψ.val x) =
      ∫ x, partialDeriv i v x * ψ.val x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (ψ.supported h)), mul_zero]
  rw [hleft, hright]
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (hd.mul ψ.smooth.continuous).integrable_of_hasCompactSupport ψ.compact.mul_left
  · exact (hv.continuous.mul (ψ.deriv i).smooth.continuous).integrable_of_hasCompactSupport
      (ψ.deriv i).compact.mul_left
  · exact (hv.continuous.mul ψ.smooth.continuous).integrable_of_hasCompactSupport
      ψ.compact.mul_left
  · intro x _
    exact hv.differentiable (by norm_num) x
  · intro x _
    exact ψ.smooth.differentiable (by simp) x

/-- The diagonal second partials are continuous for a globally C² function. -/
theorem continuous_second_partial (hv : ContDiff ℝ 2 v) (i : Fin d) :
    Continuous (partialDeriv i (partialDeriv i v)) :=
  (((contDiff_partialDeriv hv i).fderiv_right (m := 0) (by norm_num)).clm_apply
    contDiff_const).continuous

/-- Classical integration by parts gives the actual Laplacian energy identity. -/
theorem classical_energy_eq (hv : ContDiff ℝ 2 v) (ψ : TestFunction U) (μ a₀ : ℝ) :
    (∫ x in U, μ * v x * ψ.val x +
      a₀ * ∑ i : Fin d, partialDeriv i v x * (ψ.deriv i).val x) =
      ∫ x in U, (μ * v x - a₀ * laplacian v x) * ψ.val x := by
  have hm : Integrable (fun x => v x * ψ.val x) (volume.restrict U) :=
    ((hv.continuous.mul ψ.smooth.continuous).integrable_of_hasCompactSupport
      ψ.compact.mul_left).restrict
  have hg (i : Fin d) : Integrable
      (fun x => partialDeriv i v x * (ψ.deriv i).val x) (volume.restrict U) :=
    (((contDiff_partialDeriv hv i).continuous.mul
      (ψ.deriv i).smooth.continuous).integrable_of_hasCompactSupport
        (ψ.deriv i).compact.mul_left).restrict
  have hh (i : Fin d) : Integrable
      (fun x => partialDeriv i (partialDeriv i v) x * ψ.val x) (volume.restrict U) :=
    (((continuous_second_partial hv i).mul
      ψ.smooth.continuous).integrable_of_hasCompactSupport ψ.compact.mul_left).restrict
  have hlap (x : Fin d → ℝ) : laplacian v x =
      ∑ i : Fin d, partialDeriv i (partialDeriv i v) x := by
    unfold laplacian
    apply Finset.sum_congr rfl
    intro i _
    exact secondPartial_eq_fderiv_partialDeriv hv i i x
  have hpoint (x : Fin d → ℝ) : (μ * v x - a₀ * laplacian v x) * ψ.val x =
      μ * (v x * ψ.val x) -
        a₀ * ∑ i : Fin d, partialDeriv i (partialDeriv i v) x * ψ.val x := by
    simp only [hlap, sub_mul, mul_assoc, Finset.sum_mul]
  have hs := integrable_finsetSum Finset.univ (fun i _ => hg i)
  have ht := integrable_finsetSum Finset.univ (fun i _ => hh i)
  simp_rw [hpoint, mul_assoc μ]
  rw [integral_add (hm.const_mul μ) (hs.const_mul a₀),
    integral_sub (hm.const_mul μ) (ht.const_mul a₀)]
  simp only [integral_const_mul]
  rw [integral_finsetSum _ (fun i _ => hg i),
    integral_finsetSum _ (fun i _ => hh i)]
  simp_rw [integration_by_parts_classical (contDiff_partialDeriv hv _) ψ _]
  rw [Finset.sum_neg_distrib]
  ring

/-- A pointwise classical PDE gives the integrable weak equation for the actual graph.
No closure membership or boundary approximation is used in this analytic identity. -/
theorem classicalGraph_weak_equation (hv : ContDiff ℝ 2 v) (hU : Bornology.IsBounded U)
    (hopen : IsOpen U) (μ a₀ : ℝ) (f : (Fin d → ℝ) → ℝ)
    (hpde : ∀ x ∈ U, μ * v x - a₀ * laplacian v x = f x) (ψ : TestFunction U) :
    Integrable (fun x => μ * classicalGraph hv hU 0 x * ψ.val x +
      a₀ * ∑ i : Fin d, classicalGraph hv hU i.succ x * (ψ.deriv i).val x)
        (volume.restrict U) ∧
    Integrable (fun x => f x * ψ.val x) (volume.restrict U) ∧
    (∫ x in U, μ * classicalGraph hv hU 0 x * ψ.val x +
      a₀ * ∑ i : Fin d, classicalGraph hv hU i.succ x * (ψ.deriv i).val x) =
      ∫ x in U, f x * ψ.val x := by
  have hae : ∀ᵐ x ∂volume.restrict U,
      μ * classicalGraph hv hU 0 x * ψ.val x +
        a₀ * ∑ i : Fin d, classicalGraph hv hU i.succ x * (ψ.deriv i).val x =
      μ * v x * ψ.val x + a₀ * ∑ i : Fin d, partialDeriv i v x * (ψ.deriv i).val x := by
    have hg := ae_all_iff.mpr (classicalGraph_deriv hv hU)
    filter_upwards [classicalGraph_value hv hU, hg] with x hx hd
    simp only [hx, hd]
  have hi : Integrable (fun x => μ * classicalGraph hv hU 0 x * ψ.val x +
      a₀ * ∑ i : Fin d, classicalGraph hv hU i.succ x * (ψ.deriv i).val x)
        (volume.restrict U) := by
    have hm : Integrable (fun x => μ * classicalGraph hv hU 0 x * ψ.val x)
        (volume.restrict U) := by
      simpa only [mul_assoc] using
        (integrable_mul_test (classicalGraph hv hU 0) ψ).const_mul μ
    have hg : Integrable (fun x => a₀ * ∑ i : Fin d,
        classicalGraph hv hU i.succ x * (ψ.deriv i).val x) (volume.restrict U) :=
      (integrable_finsetSum Finset.univ
      (fun i _ => integrable_mul_test (classicalGraph hv hU i.succ) (ψ.deriv i))).const_mul a₀
    exact hm.add hg
  have hforce : Integrable (fun x => (μ * v x - a₀ * laplacian v x) * ψ.val x)
      (volume.restrict U) := by
    have hc : Continuous (fun x => μ * v x - a₀ * laplacian v x) := by
      have hlap : laplacian v = fun x => ∑ i : Fin d,
          partialDeriv i (partialDeriv i v) x := by
        funext x
        unfold laplacian
        exact Finset.sum_congr rfl (fun i _ => secondPartial_eq_fderiv_partialDeriv hv i i x)
      rw [hlap]
      exact (continuous_const.mul hv.continuous).sub
        (continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_second_partial hv i))
    exact ((hc.mul ψ.smooth.continuous).integrable_of_hasCompactSupport
      ψ.compact.mul_left).restrict
  have hp : (fun x => (μ * v x - a₀ * laplacian v x) * ψ.val x) =ᵐ[volume.restrict U]
      (fun x => f x * ψ.val x) := by
    filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
    rw [hpde x hx]
  refine ⟨hi, hforce.congr hp, ?_⟩
  calc
    _ = ∫ x in U, μ * v x * ψ.val x +
        a₀ * ∑ i : Fin d, partialDeriv i v x * (ψ.deriv i).val x := integral_congr_ae hae
    _ = _ := classical_energy_eq hv ψ μ a₀
    _ = _ := integral_congr_ae hp

/-- Every graph coordinate satisfies its distributional derivative identity. -/
theorem classicalGraph_distributional_derivative (hv : ContDiff ℝ 2 v)
    (hU : Bornology.IsBounded U) (ψ : TestFunction U) (i : Fin d) :
    (∫ x in U, classicalGraph hv hU 0 x * (ψ.deriv i).val x) =
      -(∫ x in U, classicalGraph hv hU i.succ x * ψ.val x) := by
  calc
    _ = ∫ x in U, v x * (ψ.deriv i).val x := by
      apply integral_congr_ae
      filter_upwards [classicalGraph_value hv hU] with x hx
      rw [hx]
    _ = -(∫ x in U, partialDeriv i v x * ψ.val x) :=
      integration_by_parts_classical (hv.of_le (by norm_num)) ψ i
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [classicalGraph_deriv hv hU i] with x hx
      rw [hx]

/-- The cited zero-boundary approximation puts the actual classical graph in H¹₀. -/
def classicalH10 (happrox : External.GilbargTrudingerZeroBoundaryApproximation)
    (hd : 0 < d) (hv : ContDiff ℝ 2 v) (hU : Bornology.IsBounded U)
    (hopen : IsOpen U) (hconn : IsConnected U)
    (hzero : Set.EqOn v (fun _ => 0) (frontier U)) : H10 U :=
  ⟨classicalGraph hv hU, happrox d hd U hopen hconn hU (classicalGraph hv hU)
    (classicalGraph_distributional_derivative hv hU) v hv.continuous.continuousOn hzero
    (classicalGraph_value hv hU)⟩

/-- A classical zero-boundary solution gives the actual H¹₀ weak solution, modulo only
Gilbarg–Trudinger's zero-boundary approximation input. -/
theorem classicalH10_isWeakSolution
    (happrox : External.GilbargTrudingerZeroBoundaryApproximation)
    (hd : 0 < d) (hv : ContDiff ℝ 2 v) (hU : Bornology.IsBounded U)
    (hopen : IsOpen U) (hconn : IsConnected U)
    (hzero : Set.EqOn v (fun _ => 0) (frontier U)) (μ a₀ : ℝ)
    (f : (Fin d → ℝ) → ℝ) (hpde : ∀ x ∈ U, μ * v x - a₀ * laplacian v x = f x) :
    IsWeakSolution U μ a₀ f (classicalH10 happrox hd hv hU hopen hconn hzero) :=
  classicalGraph_weak_equation hv hU hopen μ a₀ f hpde

/-- All coordinates characterize the zero-boundary classical graph, including its value. -/
theorem eq_classicalH10_iff
    (happrox : External.GilbargTrudingerZeroBoundaryApproximation)
    (hd : 0 < d) (hv : ContDiff ℝ 2 v) (hU : Bornology.IsBounded U)
    (hopen : IsOpen U) (hconn : IsConnected U)
    (hzero : Set.EqOn v (fun _ => 0) (frontier U)) (w : H10 U) :
    w = classicalH10 happrox hd hv hU hopen hconn hzero ↔
      (fun x => w.val 0 x) =ᵐ[volume.restrict U] v ∧
      ∀ i : Fin d, (fun x => w.val i.succ x) =ᵐ[volume.restrict U] partialDeriv i v := by
  constructor
  · intro hw
    exact (eq_classicalGraph_iff hv hU w.val).mp (congrArg Subtype.val hw)
  · intro hw
    exact Subtype.ext ((eq_classicalGraph_iff hv hU w.val).mpr hw)

/-- The global quadratic belongs to H¹₀ and solves the zero-mass equation on the
Euclidean unit ball. Its source function has value one at the origin. -/
theorem quadratic_classicalH10
    (happrox : External.GilbargTrudingerZeroBoundaryApproximation) (hd : 0 < d)
    (a₀ : ℝ) :
    ∃ u : H10 (LatticeProb.Elliptic.unitBall d),
      IsWeakSolution (LatticeProb.Elliptic.unitBall d) 0 a₀ (fun _ => 2 * d * a₀) u ∧
      (fun x => u.val 0 x) =ᵐ[volume.restrict (LatticeProb.Elliptic.unitBall d)]
        (fun x => 1 - ∑ i : Fin d, x i ^ 2) ∧
      (∀ i : Fin d, (fun x => u.val i.succ x)
        =ᵐ[volume.restrict (LatticeProb.Elliptic.unitBall d)]
          partialDeriv i (fun x => 1 - ∑ j : Fin d, x j ^ 2)) ∧ u.val 0 ≠ 0 := by
  have hv : ContDiff ℝ 2 (fun x : Fin d → ℝ => 1 - ∑ i, x i ^ 2) := by fun_prop
  have hdomain := isC2HolderDomain_unitBall (d := d) 0
  have hclass := quadratic_isClassicalDirichletSolution (d := d) 0 a₀
  have hz : Set.EqOn (fun x : Fin d → ℝ => 1 - ∑ i, x i ^ 2) (fun _ => 0)
      (frontier (LatticeProb.Elliptic.unitBall d)) := hclass.2.2.1
  let u := classicalH10 happrox hd hv hdomain.2.2.1 hdomain.1 hdomain.2.1 hz
  have hcoords := (eq_classicalH10_iff happrox hd hv hdomain.2.2.1 hdomain.1
    hdomain.2.1 hz u).mp rfl
  refine ⟨u, ?_, hcoords.1, hcoords.2, ?_⟩
  · apply classicalH10_isWeakSolution
    intro x hx
    simpa only [zero_mul, zero_add] using hclass.2.2.2 x hx
  · intro heq
    have hae : (fun x : Fin d → ℝ => 1 - ∑ i, x i ^ 2)
        =ᵐ[volume.restrict (LatticeProb.Elliptic.unitBall d)] (fun _ => 0) := by
      have hval := hcoords.1
      rw [heq] at hval
      exact hval.symm.trans (Lp.coeFn_zero _ _ _)
    have hopen := hdomain.1
    have hzero : (0 : Fin d → ℝ) ∈ LatticeProb.Elliptic.unitBall d := by
      rw [mem_unitBall_iff]
      simp
    have he := Measure.eqOn_open_of_ae_eq hae hopen hv.continuous.continuousOn
      continuous_const.continuousOn hzero
    simp at he

/-- On bounded domains the constructed graph agrees in every coordinate with the
existing graph of any smooth compactly supported test. -/
theorem classicalGraph_testFunction (φ : TestFunction U) (hU : Bornology.IsBounded U) :
    classicalGraph (φ.smooth.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hU = φ.graph := by
  symm
  apply (eq_classicalGraph_iff _ hU φ.graph).mpr
  exact ⟨φ.memLp.coeFn_toLp, fun i => (φ.deriv i).memLp.coeFn_toLp⟩

/-- Manufactured forcing retains compact support. -/
theorem TestFunction.compact_forcing (φ : TestFunction U) (μ a₀ : ℝ) :
    HasCompactSupport (φ.forcing μ a₀) := by
  have hs := HasCompactSupport.finset_sum
    (s := Finset.univ) (fun i _ => ((φ.deriv i).deriv i).compact)
  have hc := (φ.compact.mul_left (f := fun _ => μ)).sub
    (hs.mul_left (f := fun _ => a₀))
  convert hc using 1 <;> first
  | rfl
  | funext x
    simp only [TestFunction.forcing, Pi.sub_apply, Pi.mul_apply, Finset.sum_apply]

/-- Positive mass and nonnegative diffusivity give nonzero manufactured forcing
whenever the supported solution has a nonzero L² value. -/
theorem TestFunction.forcing_ne_zero (φ : TestFunction U) (hn : φ.toL2 ≠ 0)
    {μ a₀ : ℝ} (hμ : 0 < μ) (ha : 0 ≤ a₀) : φ.forcing μ a₀ ≠ (fun _ => 0) := by
  intro hz
  have he := φ.energy_eq_forcing φ μ a₀
  rw [hz] at he
  simp only [zero_mul, integral_zero] at he
  have hm : Integrable (fun x => φ.val x * φ.val x) (volume.restrict U) :=
    φ.memLp.integrable_mul φ.memLp
  have hg : Integrable (fun x => ∑ i : Fin d, (φ.deriv i).val x * (φ.deriv i).val x)
      (volume.restrict U) := integrable_finsetSum Finset.univ
    (fun i _ => (φ.deriv i).memLp.integrable_mul (φ.deriv i).memLp)
  have hmass : Integrable (fun x => μ * φ.val x * φ.val x) (volume.restrict U) := by
    simpa only [mul_assoc] using hm.const_mul μ
  rw [integral_add hmass (hg.const_mul a₀)] at he
  have hgrad : 0 ≤ ∫ x in U, a₀ * ∑ i : Fin d, (φ.deriv i).val x * (φ.deriv i).val x :=
    integral_nonneg fun x => mul_nonneg ha
      (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  have hsq : (∫ x in U, φ.val x * φ.val x) = ‖φ.toL2‖ ^ 2 := by
    rw [l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [φ.memLp.coeFn_toLp] with x hx
    change φ.toL2 x = φ.val x at hx
    rw [hx, pow_two]
  simp_rw [mul_assoc μ] at he
  rw [integral_const_mul, hsq] at he
  have hnorm : 0 < ‖φ.toL2‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hn)
  have hpos := mul_pos hμ hnorm
  linarith

/-- A nonzero compactly supported smooth forcing has an actual weak solution
at unit mass and every positive diffusivity. -/
theorem exists_nonzero_compact_forcing (d : ℕ) (a₀ : ℝ) (ha : 0 < a₀) :
    ∃ φ : TestFunction (unitBall d), φ.val 0 = 1 ∧
      HasCompactSupport (φ.forcing 1 a₀) ∧ φ.forcing 1 a₀ ≠ (fun _ => 0) ∧
      IsWeakSolution (unitBall d) 1 a₀ (φ.forcing 1 a₀) φ.toH10 := by
  obtain ⟨φ, hone, hn, hweak⟩ := exists_nonzero_unitBall d
  exact ⟨φ, hone, φ.compact_forcing 1 a₀,
    φ.forcing_ne_zero hn (by norm_num) ha.le, hweak 1 a₀⟩

end

end LatticeProb.Elliptic.WeakDirichlet
