import LatticeProb.External.GilbargTrudingerSobolev

/-!
# Linear algebra of the zero-boundary Sobolev graph

Supported smooth graphs form a linear subspace. Its closure is stable under
subtraction, coordinate by coordinate. The weak equation subtracts with its
forcing, and the homogeneous book input yields uniqueness for the same data.
-/

namespace LatticeProb.Elliptic.WeakDirichlet

open MeasureTheory
open scoped ENNReal BigOperators Topology

noncomputable section

variable {d : ℕ} {U : Set (Fin d → ℝ)}

/-- Addition of actual supported smooth tests. -/
def TestFunction.add (φ ψ : TestFunction U) : TestFunction U where
  val := φ.val + ψ.val
  smooth := φ.smooth.add ψ.smooth
  compact := φ.compact.add ψ.compact
  supported := (tsupport_add φ.val ψ.val).trans
    (Set.union_subset φ.supported ψ.supported)

/-- Scalar multiplication of an actual supported smooth test. -/
def TestFunction.smul (c : ℝ) (φ : TestFunction U) : TestFunction U where
  val := c • φ.val
  smooth := φ.smooth.const_smul c
  compact := φ.compact.smul_left
  supported := (tsupport_smul_subset_right (fun _ => c) φ.val).trans φ.supported

/-- Coordinate differentiation commutes with addition of tests. -/
theorem TestFunction.deriv_add_val (φ ψ : TestFunction U) (i : Fin d) :
    ((φ.add ψ).deriv i).val = (φ.deriv i).val + (ψ.deriv i).val := by
  funext x
  change fderiv ℝ (φ.val + ψ.val) x (Pi.single i 1) = _
  rw [fderiv_add (φ.smooth.differentiable (by simp) x)
    (ψ.smooth.differentiable (by simp) x)]
  rfl

/-- Coordinate differentiation commutes with scalar multiplication of tests. -/
theorem TestFunction.deriv_smul_val (c : ℝ) (φ : TestFunction U) (i : Fin d) :
    ((φ.smul c).deriv i).val = c • (φ.deriv i).val := by
  funext x
  change fderiv ℝ (c • φ.val) x (Pi.single i 1) = _
  rw [fderiv_const_smul (φ.smooth.differentiable (by simp) x) c]
  rfl

/-- The L² class of a sum of tests is the sum of their L² classes. -/
theorem TestFunction.toL2_add (φ ψ : TestFunction U) :
    (φ.add ψ).toL2 = φ.toL2 + ψ.toL2 := rfl

/-- The L² class respects scalar multiplication of tests. -/
theorem TestFunction.toL2_smul (c : ℝ) (φ : TestFunction U) :
    (φ.smul c).toL2 = c • φ.toL2 := rfl

/-- Equal smooth representatives give equal L² classes. -/
theorem TestFunction.toL2_eq_of_val_eq {φ ψ : TestFunction U}
    (h : φ.val = ψ.val) : φ.toL2 = ψ.toL2 := by
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall (congrFun h)

/-- The actual smooth Sobolev graph preserves addition in every coordinate. -/
theorem TestFunction.graph_add (φ ψ : TestFunction U) :
    (φ.add ψ).graph = φ.graph + ψ.graph := by
  apply PiLp.ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact φ.toL2_add ψ
  · change ((φ.add ψ).deriv i).toL2 = (φ.deriv i).toL2 + (ψ.deriv i).toL2
    rw [← TestFunction.toL2_add]
    exact TestFunction.toL2_eq_of_val_eq (φ.deriv_add_val ψ i)

/-- The actual smooth Sobolev graph preserves scalar multiplication. -/
theorem TestFunction.graph_smul (c : ℝ) (φ : TestFunction U) :
    (φ.smul c).graph = c • φ.graph := by
  apply PiLp.ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact φ.toL2_smul c
  · change ((φ.smul c).deriv i).toL2 = c • (φ.deriv i).toL2
    rw [← TestFunction.toL2_smul]
    exact TestFunction.toL2_eq_of_val_eq (φ.deriv_smul_val c i)

/-- The zero test represents the zero element of the full Sobolev product. -/
theorem zeroTest_graph (U : Set (Fin d → ℝ)) : (zeroTest U).graph = 0 := by
  apply PiLp.ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · rfl
  · change ((zeroTest U).deriv i).toL2 = 0
    have h : ((zeroTest U).deriv i).val = (zeroTest U).val := by
      funext x
      change fderiv ℝ (fun _ : Fin d → ℝ => (0 : ℝ)) x (Pi.single i 1) = 0
      rw [fderiv_fun_const]
      rfl
    exact (TestFunction.toL2_eq_of_val_eq h).trans rfl

/-- The range of actual smooth graphs is a linear subspace, with its literal range carrier. -/
def testGraphSubmodule (U : Set (Fin d → ℝ)) : Submodule ℝ (H1Product U) where
  carrier := Set.range TestFunction.graph
  zero_mem' := ⟨zeroTest U, zeroTest_graph U⟩
  add_mem' := by
    rintro _ _ ⟨φ, rfl⟩ ⟨ψ, rfl⟩
    exact ⟨φ.add ψ, φ.graph_add ψ⟩
  smul_mem' := by
    rintro c _ ⟨φ, rfl⟩
    exact ⟨φ.smul c, φ.graph_smul c⟩

/-- Subtraction in the literal closure defining H¹₀. -/
def H10.sub (u v : H10 U) : H10 U :=
  ⟨u.val - v.val, (testGraphSubmodule U).topologicalClosure.sub_mem u.property v.property⟩

/-- All L² coordinates of H¹₀ subtraction are the corresponding L² differences. -/
theorem H10.sub_coord (u v : H10 U) (j : Fin (d + 1)) :
    (u.sub v).val j = u.val j - v.val j := rfl

/-- All coordinate representatives of subtraction agree almost everywhere. -/
theorem H10.sub_coord_ae (u v : H10 U) (j : Fin (d + 1)) :
    (fun x => (u.sub v).val j x) =ᵐ[volume.restrict U]
      (fun x => u.val j x - v.val j x) := Lp.coeFn_sub _ _


/-- The constant-coefficient bilinear form on the full L² Sobolev product. -/
def energyPair (μ a₀ : ℝ) (u v : H1Product U) : ℝ :=
  μ * inner ℝ (u 0) (v 0) + a₀ * ∑ i : Fin d, inner ℝ (u i.succ) (v i.succ)

/-- The bilinear form equals the literal integrable energy on a smooth test. -/
theorem energyPair_test (μ a₀ : ℝ) (u : H10 U) (φ : TestFunction U) :
    energyPair μ a₀ u.val φ.graph =
      ∫ x in U, μ * u.val 0 x * φ.val x +
        a₀ * ∑ i : Fin d, u.val i.succ x * (φ.deriv i).val x := by
  have hm := (integrable_mul_test (u.val 0) φ).const_mul μ
  have hg (i : Fin d) := integrable_mul_test (u.val i.succ) (φ.deriv i)
  have hs := (integrable_finsetSum Finset.univ (fun i _ => hg i)).const_mul a₀
  change μ * inner ℝ (u.val 0) φ.toL2 +
    a₀ * ∑ i : Fin d, inner ℝ (u.val i.succ) (φ.deriv i).toL2 = _
  simp_rw [inner_test]
  simp_rw [mul_assoc μ]
  rw [integral_add hm hs, integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun i _ => hg i)]

/-- Subtracting the first argument subtracts the bilinear forms. -/
theorem energyPair_sub_left (μ a₀ : ℝ) (u v w : H1Product U) :
    energyPair μ a₀ (u - v) w = energyPair μ a₀ u w - energyPair μ a₀ v w := by
  simp only [energyPair, PiLp.sub_apply, inner_sub_left, Finset.sum_sub_distrib]
  ring

/-- For fixed Sobolev data, the energy form is a continuous functional on the graph product. -/
theorem continuous_energyPair (μ a₀ : ℝ) (u : H1Product U) :
    Continuous (energyPair μ a₀ u) := by
  exact (continuous_const.mul
    (continuous_const.inner (PiLp.continuous_apply 2 _ 0))).add
    (continuous_const.mul (continuous_finsetSum _ fun i _ =>
      continuous_const.inner (PiLp.continuous_apply 2 _ i.succ)))

/-- The homogeneous equation extends from supported smooth tests to every H¹₀ test.
This is the continuous-functional passage used in (8.7), p. 178 of the book. -/
theorem IsWeakSolution.energyPair_eq_zero (μ a₀ : ℝ) (u : H10 U)
    (hu : IsWeakSolution U μ a₀ (fun _ => 0) u) (v : H10 U) :
    energyPair μ a₀ u.val v.val = 0 := by
  have hc : IsClosed {w : H1Product U | energyPair μ a₀ u.val w = 0} :=
    isClosed_eq (continuous_energyPair μ a₀ u.val) continuous_const
  apply closure_minimal (s := Set.range (TestFunction.graph (U := U))) ?_ hc v.property
  rintro _ ⟨φ, rfl⟩
  change energyPair μ a₀ u.val φ.graph = 0
  rw [energyPair_test, (hu φ).2.2]
  simp only [zero_mul, integral_zero]

/-- Two weak equations subtract, including the genuine integrability of their forcing. -/
theorem IsWeakSolution.sub {μ a₀ : ℝ} {f g : (Fin d → ℝ) → ℝ}
    {u v : H10 U} (hu : IsWeakSolution U μ a₀ f u)
    (hv : IsWeakSolution U μ a₀ g v) :
    IsWeakSolution U μ a₀ (fun x => f x - g x) (u.sub v) := by
  intro φ
  have hf := (hu φ).2.1
  have hg := (hv φ).2.1
  refine ⟨integrable_energy _ _ _ _, ?_, ?_⟩
  · exact (hf.sub hg).congr
      (Filter.Eventually.of_forall fun x => (sub_mul (f x) (g x) (φ.val x)).symm)
  · rw [← energyPair_test]
    change energyPair μ a₀ (u.val - v.val) φ.graph = _
    rw [energyPair_sub_left, energyPair_test, energyPair_test,
      (hu φ).2.2, (hv φ).2.2]
    simp_rw [sub_mul]
    exact (integral_sub hf hg).symm

/-- Equal forcing leaves a literal homogeneous equation for the H¹₀ difference. -/
theorem IsWeakSolution.sub_same {μ a₀ : ℝ} {f : (Fin d → ℝ) → ℝ}
    {u v : H10 U} (hu : IsWeakSolution U μ a₀ f u)
    (hv : IsWeakSolution U μ a₀ f v) :
    IsWeakSolution U μ a₀ (fun _ => 0) (u.sub v) := by
  simpa only [sub_self] using hu.sub hv

/-- The homogeneous Corollary 8.2 input gives same-data uniqueness, including at zero mass. -/
theorem IsWeakSolution.eq_of_same_data
    (hGT : LatticeProb.External.GilbargTrudingerWeakHomogeneousUniqueness)
    (hd : 0 < d) (hopen : IsOpen U) (hconn : IsConnected U)
    (hbounded : Bornology.IsBounded U) {μ a₀ : ℝ} (ha : 0 < a₀) (hμ : 0 ≤ μ)
    {f : (Fin d → ℝ) → ℝ} {u v : H10 U}
    (hu : IsWeakSolution U μ a₀ f u) (hv : IsWeakSolution U μ a₀ f v) : u = v := by
  apply Subtype.ext
  exact sub_eq_zero.mp (hGT d hd U hopen hconn hbounded a₀ μ ha hμ
    (u.sub v) (hu.sub_same hv))

end

end LatticeProb.Elliptic.WeakDirichlet
