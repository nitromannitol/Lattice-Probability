/-
The discrete Gaussian free field with zero boundary values on a finite set of a graph.

The field is the centred Gaussian vector on `C` whose covariance is the killed Green function
`g_C(x, y)`.  Mathlib's `multivariateGaussian` builds a Gaussian with any positive semidefinite
covariance, so the one piece of mathematics is that `g_C` is positive semidefinite on `C`: for a
vector `c`, the function `u = ∑_o c_o g_C(o, ·)` vanishes off `C` and has `-Δu = c` on `C`
(`laplacian_killedGreenReal`), so `∑ c_x g_C(x, y) c_y = ∑ u (-Δu)`, which is half the Dirichlet
energy of `u` (`energyOn_eq_neg_two_mul`) and therefore nonnegative (`energyOn_nonneg`).
-/
import LatticeProb.Network.KilledGreen
import LatticeProb.Network.Variational
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open ProbabilityTheory MeasureTheory

open Matrix

namespace LatticeProb.Network

open LatticeProb.Graph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

/-- The killed Green function of `C`, as a matrix indexed by the sites of `C`. -/
noncomputable def killedGreenMatrix (G : SimpleGraph V) [G.LocallyFinite] (C : Finset V) :
    Matrix C C ℝ :=
  Matrix.of fun x y => killedGreenReal G (C : Set V) x y

omit [DecidableEq V] in
/-- The graph Laplacian is additive. -/
theorem laplacian_add (f g : V → ℝ) (x : V) :
    laplacian G (f + g) x = laplacian G f x + laplacian G g x := by
  simp only [laplacian, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

omit [DecidableEq V] in
/-- The graph Laplacian commutes with scalars. -/
theorem laplacian_smul (a : ℝ) (f : V → ℝ) (x : V) :
    laplacian G (a • f) x = a * laplacian G f x := by
  simp only [laplacian, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ y ∈ G.neighborFinset x, (a * f y - a * f x)) = (∑ y ∈ G.neighborFinset x, a * (f y - f x)) := by
      refine Finset.sum_congr rfl fun y _ => by ring
    _ = a * (∑ y ∈ G.neighborFinset x, (f y - f x)) := by rw [Finset.mul_sum]
    _ = a * laplacian G f x := rfl

omit [DecidableEq V] in
/-- The graph Laplacian of a finite sum. -/
theorem laplacian_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → V → ℝ) (x : V) :
    laplacian G (∑ i ∈ s, f i) x = ∑ i ∈ s, laplacian G (f i) x := by
  induction s using Finset.induction with
  | empty => simp [laplacian]
  | insert i s his ih =>
    simp [Finset.sum_insert his, laplacian_add, ih]

/-- The killed Green function is positive semidefinite on `C`. -/
theorem killedGreenMatrix_posSemidef (hG : G.Connected) (C : Finset V) {q : V} (hq : q ∉ C) :
    (killedGreenMatrix G C).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · -- Hermitian (symmetric for ℝ)
    refine Matrix.IsHermitian.ext ?_
    intro i j
    simp [killedGreenMatrix, killedGreenReal_symm hG C hq i j]
  · -- nonnegative dot product with any vector x : C → ℝ
    intro x
    -- define u(v) = ∑_{o∈C} x_o * g_C(o, v)
    let u : V → ℝ := fun v => ∑ o ∈ C.attach, x o * killedGreenReal G (C : Set V) (o : V) v
    have hu_support : ∀ v, v ∉ C → u v = 0 := by
      intro v hv
      simp [u, killedGreenReal_eq_zero_of_not_mem hG C hq hv]
    have h_nbhd : C ⊆ nbhd G C := subset_nbhd C
    have h_nb : ∀ x' ∈ C, ∀ y, G.Adj x' y → y ∈ nbhd G C := by
      intro x' hx' y hxy
      exact mem_nbhd_of_adj hx' hxy
    -- compute laplacian of u on C
    have hu_laplacian : ∀ (v : V) (hv : v ∈ C), laplacian G u v = -x ⟨v, hv⟩ := by
      intro v hv
      have hv_set : v ∈ (C : Set V) := by exact_mod_cast hv
      calc
        laplacian G u v = laplacian G (fun w => ∑ o ∈ C.attach, x o * killedGreenReal G (C : Set V) (o : V) w) v := rfl
        _ = laplacian G (∑ o ∈ C.attach, (fun w => x o * killedGreenReal G (C : Set V) (o : V) w)) v := by
          have h_eq : (fun w => ∑ o ∈ C.attach, x o * killedGreenReal G (C : Set V) (o : V) w) =
              (∑ o ∈ C.attach, fun w => x o * killedGreenReal G (C : Set V) (o : V) w) := by
            ext w; simp
          rw [h_eq]
        _ = ∑ o ∈ C.attach, laplacian G (fun w => x o * killedGreenReal G (C : Set V) (o : V) w) v := by
          rw [laplacian_sum]
        _ = ∑ o ∈ C.attach, x o * laplacian G (killedGreenReal G (C : Set V) (o : V)) v := by
          refine Finset.sum_congr rfl fun o ho => ?_
          have : (fun w => x o * killedGreenReal G (C : Set V) (o : V) w) = (x o) • killedGreenReal G (C : Set V) (o : V) := by
            ext w; simp
          rw [this, laplacian_smul]
        _ = ∑ o ∈ C.attach, x o * (-(if v = (o : V) then (1 : ℝ) else 0)) := by
          refine Finset.sum_congr rfl fun o ho => ?_
          have h := laplacian_killedGreenReal hG C (ho := o.2) hq (v := v) hv_set
          simp [h]
        _ = -x ⟨v, hv⟩ := by
          have hsum : (∑ o ∈ C.attach, (if v = (o : V) then x o else 0)) = x ⟨v, hv⟩ := by
            have : (C.attach.filter (fun (o : Subtype (· ∈ C)) => v = (o : V))) = {⟨v, hv⟩} := by
              ext o
              simp [Subtype.ext_iff, Finset.mem_attach, eq_comm]
            calc
              (∑ o ∈ C.attach, (if v = (o : V) then x o else 0)) = 
                  (∑ o ∈ C.attach.filter (fun (o : Subtype (· ∈ C)) => v = (o : V)), x o) := by
                rw [Finset.sum_filter]
              _ = (∑ o ∈ ({⟨v, hv⟩} : Finset (Subtype (· ∈ C))), x o) := by rw [this]
              _ = x ⟨v, hv⟩ := by simp
          have : (∑ o ∈ C.attach, x o * (-(if v = (o : V) then (1 : ℝ) else 0))) = -x ⟨v, hv⟩ := by
            calc
              (∑ o ∈ C.attach, x o * (-(if v = (o : V) then (1 : ℝ) else 0))) = 
                  -(∑ o ∈ C.attach, x o * (if v = (o : V) then (1 : ℝ) else 0)) := by
                simp
              _ = -(∑ o ∈ C.attach, (if v = (o : V) then x o else 0)) := by
                refine congrArg (fun t => -t) (Finset.sum_congr rfl fun o _ => ?_)
                by_cases h : v = (o : V)
                · simp [h]
                · simp [h]
              _ = -x ⟨v, hv⟩ := by rw [hsum]
          exact this
    -- now relate the quadratic form to the energy
    have h_quadform : dotProduct (star x) ((killedGreenMatrix G C).mulVec x) = (1/2 : ℝ) * energyOn G (unitCond G) (nbhd G C) u := by
      calc
        dotProduct (star x) ((killedGreenMatrix G C).mulVec x) = ∑ i ∈ C.attach, x i * (∑ j ∈ C.attach, (killedGreenMatrix G C) i j * x j) := by
          simp [dotProduct, Matrix.mulVec]
        _ = ∑ i ∈ C.attach, x i * u i := by
          simp [u, killedGreenMatrix, killedGreenReal_symm hG C hq, mul_comm]
        _ = ∑ i ∈ C.attach, (-laplacian G u i) * u i := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi_mem : (i : V) ∈ C := i.2
          have h := hu_laplacian (i : V) hi_mem
          rw [h]
          ring
        _ = ∑ i ∈ C.attach, u i * (-laplacian G u i) := by
          simp [mul_comm]
        _ = (1/2 : ℝ) * energyOn G (unitCond G) (nbhd G C) u := by
          have h_energy := energyOn_eq_neg_two_mul isCond_unitCond (nbhd G C) C u hu_support h_nbhd h_nb
          have h_netlaplacian : ∀ w, netLaplacian G (unitCond G) u w = laplacian G u w := by
            intro w
            rw [netLaplacian_unitCond]
          have h_energy' : energyOn G (unitCond G) (nbhd G C) u = -2 * ∑ x ∈ C, u x * laplacian G u x := by
            simpa [h_netlaplacian] using h_energy
          calc
            ∑ i ∈ C.attach, u i * (-laplacian G u i) = -(∑ i ∈ C.attach, u i * laplacian G u i) := by
              simp [mul_comm]
            _ = (1/2 : ℝ) * (-2 * ∑ i ∈ C.attach, u i * laplacian G u i) := by ring
            _ = (1/2 : ℝ) * energyOn G (unitCond G) (nbhd G C) u := by
              rw [h_energy']
              congr 1
              rw [Finset.sum_attach C (fun x => u x * laplacian G u x)]
    have h_energy_nonneg : 0 ≤ energyOn G (unitCond G) (nbhd G C) u :=
      energyOn_nonneg isCond_unitCond (nbhd G C) u
    rw [h_quadform]
    nlinarith

/-- The discrete Gaussian free field on `C` with zero boundary values. -/
noncomputable def gff (G : SimpleGraph V) [G.LocallyFinite] (C : Finset V) :
    Measure (EuclideanSpace ℝ C) :=
  multivariateGaussian 0 (killedGreenMatrix G C)

/-- The field is centred. -/
theorem integral_gff (C : Finset V) : ∫ φ, φ ∂(gff G C) = 0 := by
  simp [gff]

/-- The covariance of the field is the killed Green function. -/
theorem covariance_gff_of_posSemidef (C : Finset V) (hpsd : (killedGreenMatrix G C).PosSemidef) (x y : C) :
    cov[fun φ : EuclideanSpace ℝ C => φ x, fun φ => φ y; gff G C]
      = killedGreenReal G (C : Set V) x y := by
  simpa [gff, killedGreenMatrix, Matrix.of_apply] using covariance_eval_multivariateGaussian hpsd x y

/-- The covariance of the field is the killed Green function. -/
theorem covariance_gff (hG : G.Connected) (C : Finset V) {q : V} (hq : q ∉ C) (x y : C) :
    cov[fun φ : EuclideanSpace ℝ C => φ x, fun φ => φ y; gff G C]
      = killedGreenReal G (C : Set V) x y :=
  covariance_gff_of_posSemidef C (killedGreenMatrix_posSemidef hG C hq) x y

end LatticeProb.Network
