/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2SignKernel at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2RayKnight
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2GaussDensity
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2SignDecomp
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2Griffiths

 









set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos

namespace WiredConductances

variable {W : Type*} [Fintype W] [DecidableEq W] (G : WiredConductances W)

 
def constVec (u : ℝ) : EuclideanSpace ℝ W := WithLp.toLp 2 fun _ => u

 
def shiftDensity (u : ℝ) (z : EuclideanSpace ℝ W) : ℝ :=
  Real.exp (-(1 / 2) * ((z - constVec u).ofLp ⬝ᵥ (G.precision *ᵥ (z - constVec u).ofLp)))

theorem shiftDensity_pos (u : ℝ) (z : EuclideanSpace ℝ W) : 0 < G.shiftDensity u z :=
  Real.exp_pos _

theorem continuous_shiftDensity (u : ℝ) : Continuous (G.shiftDensity u) := by
  unfold shiftDensity
  refine Real.continuous_exp.comp (continuous_const.mul ?_)
  have hc : Continuous fun z : EuclideanSpace ℝ W => (z - constVec u).ofLp :=
    (PiLp.continuous_ofLp 2 _).comp (continuous_id.sub continuous_const)
  unfold dotProduct Matrix.mulVec dotProduct
  refine continuous_finsetSum _ fun i _ => ?_
  refine ((continuous_apply i).comp hc).mul ?_
  exact continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).comp hc)

 
def shiftLaw (u : ℝ) : Measure (EuclideanSpace ℝ W) := G.gff.map (· + constVec u)
theorem shiftLaw_eq_withDensity (hK : G.precision.PosDef) (u : ℝ) :
    ∃ C : ℝ, 0 < C ∧ G.shiftLaw u =
      volume.withDensity fun z => ENNReal.ofReal (C * G.shiftDensity u z) := by
  obtain ⟨C, hC, h⟩ := multivariateGaussian_eq_withDensity hK.inv (constVec u)
  refine ⟨C, hC, ?_⟩
  have hmap : G.shiftLaw u = multivariateGaussian (constVec u) G.precision⁻¹ := by
    unfold shiftLaw gff multivariateGaussian
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    simp only [Function.comp, zero_add]
    rw [add_comm]
  rw [hmap, h, Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hK.isUnit)]
  rfl

theorem isProbabilityMeasure_shiftLaw (hK : G.precision.PosDef) (u : ℝ) :
    IsProbabilityMeasure (G.shiftLaw u) := by
  unfold shiftLaw
  infer_instance

theorem signApply_ofLp (s : W → Bool) (a : EuclideanSpace ℝ W) (i : W) :
    (signApply s a) i = spin (s i) * a i := by
  unfold signApply
  by_cases h : s i <;> simp [h, spin]

 

theorem shiftDensity_signApply (u : ℝ) (a : EuclideanSpace ℝ W) (s : W → Bool) :
    G.shiftDensity u (signApply s a) =
      isingWeight (fun i => G.boundary i * u * a i) (fun i j => G.edge i j * a i * a j) s *
        Real.exp (-(1 / 2) * ((∑ i, G.boundary i * (a i ^ 2 + u ^ 2)) +
          (1 / 2) * ∑ i, ∑ j, G.edge i j * (a i ^ 2 + a j ^ 2))) := by
  unfold shiftDensity isingWeight
  rw [← Real.exp_add]
  congr 1
  rw [G.precision_energy]
  have hx : ∀ i, (signApply s a - constVec u).ofLp i = spin (s i) * a i - u := by
    intro i
    simp [constVec, signApply_ofLp]
  simp_rw [hx]
  have hσ : ∀ i, spin (s i) ^ 2 = 1 := fun i => by rw [sq, spin_mul_self]
  have h1 : ∀ i, G.boundary i * (spin (s i) * a i - u) ^ 2 =
      G.boundary i * (a i ^ 2 + u ^ 2) - 2 * (G.boundary i * u * a i * spin (s i)) := by
    intro i
    have := hσ i
    linear_combination G.boundary i * a i ^ 2 * this
  have h2 : ∀ i j, G.edge i j * (spin (s i) * a i - u - (spin (s j) * a j - u)) ^ 2 =
      G.edge i j * (a i ^ 2 + a j ^ 2) -
        2 * (G.edge i j * a i * a j * (spin (s i) * spin (s j))) := by
    intro i j
    have hi := hσ i
    have hj := hσ j
    linear_combination G.edge i j * a i ^ 2 * hi + G.edge i j * a j ^ 2 * hj
  simp_rw [h1, h2, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  ring

 
theorem signKernel_shiftDensity (C : ℝ) (hC : 0 < C) (u : ℝ) (a : EuclideanSpace ℝ W)
    (s : W → Bool) :
    signKernel (fun z => C * G.shiftDensity u z) a s =
      isingProb (fun i => G.boundary i * u * a i) (fun i j => G.edge i j * a i * a j) s := by
  unfold signKernel isingProb
  simp_rw [G.shiftDensity_signApply]
  set D := Real.exp (-(1 / 2) * ((∑ i, G.boundary i * (a i ^ 2 + u ^ 2)) +
    (1 / 2) * ∑ i, ∑ j, G.edge i j * (a i ^ 2 + a j ^ 2)))
  have hD : 0 < D := Real.exp_pos _
  have hden : ∑ s', C * (isingWeight (fun i => G.boundary i * u * a i)
      (fun i j => G.edge i j * a i * a j) s' * D) =
      C * D * ∑ s', isingWeight (fun i => G.boundary i * u * a i)
        (fun i j => G.edge i j * a i * a j) s' := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s' _
    ring
  rw [hden, show C * (isingWeight (fun i => G.boundary i * u * a i)
      (fun i j => G.edge i j * a i * a j) s * D) = (C * D) * isingWeight
        (fun i => G.boundary i * u * a i) (fun i j => G.edge i j * a i * a j) s by ring,
    mul_div_mul_left _ _ (by positivity)]

 
theorem signKernel_disagree_le (C : ℝ) (hC : 0 < C) {u : ℝ} (hu : 0 ≤ u)
    (a : EuclideanSpace ℝ W) (ha : ∀ i, 0 ≤ a i) {v w : W} (hvw : v ≠ w) :
    ∑ s : W → Bool, (if s v = s w then 0 else signKernel (fun z => C * G.shiftDensity u z) a s)
      ≤ Real.exp (-2 * (G.edge v w * a v * a w)) := by
  simp_rw [G.signKernel_shiftDensity C hC u a]
  exact isingProb_disagree_le _ _ (fun i => mul_nonneg (mul_nonneg (G.boundary_nonneg i) hu) (ha i))
    (fun i j => mul_nonneg (mul_nonneg (G.edge_nonneg i j) (ha i)) (ha j))
    (fun i j => by rw [G.edge_symm]; ring) hvw

 
theorem signKernel_neg_le (C : ℝ) (hC : 0 < C) {u : ℝ} (hu : 0 ≤ u)
    (a : EuclideanSpace ℝ W) (ha : ∀ i, 0 ≤ a i) (v : W) :
    ∑ s : W → Bool, (if s v then 0 else signKernel (fun z => C * G.shiftDensity u z) a s)
      ≤ Real.exp (-2 * (G.boundary v * u * a v)) := by
  simp_rw [G.signKernel_shiftDensity C hC u a]
  exact isingProb_neg_le _ _ (fun i => mul_nonneg (mul_nonneg (G.boundary_nonneg i) hu) (ha i))
    (fun i j => mul_nonneg (mul_nonneg (G.edge_nonneg i j) (ha i)) (ha j)) v

end WiredConductances

end SupercriticalLQGUniqueness.B2.QPos
