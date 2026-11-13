/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.FiniteDirichlet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.DiscretePDEAlgebra
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Relation
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open scoped BigOperators Classical

namespace BouRabeeGwynne
namespace FiniteConductanceNetwork

variable {V : Type*} [Fintype V] (N : FiniteConductanceNetwork V)

/-- Each interior vertex reaches the complement by a finite path of edges with
positive conductance. This is a graph condition, not an assumption about a solver. -/
def BoundaryAccessible (A : Set V) : Prop :=
  ∀ v ∈ A, ∃ w, w ∉ A ∧
    Relation.ReflTransGen (fun v w => 0 < N.a v w) v w

/-- The finite Dirichlet problem, with all vertices outside `A` carrying boundary data. -/
def SolvesDirichlet (A : Set V) (g f : V → ℝ) : Prop :=
  (∀ v ∈ A, N.laplacian f v = 0) ∧ ∀ v, v ∉ A → f v = g v

lemma laplacian_add (f g : V → ℝ) (v : V) :
    N.laplacian (f + g) v = N.laplacian f v + N.laplacian g v := by
  classical
  simp only [laplacian, Pi.add_apply, add_sub_add_comm, mul_add,
    Finset.sum_add_distrib]

lemma laplacian_smul (c : ℝ) (f : V → ℝ) (v : V) :
    N.laplacian (c • f) v = c * N.laplacian f v := by
  classical
  simp only [laplacian, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  ring

lemma laplacian_neg (f : V → ℝ) (v : V) :
    N.laplacian (-f) v = -N.laplacian f v := by
  simpa only [neg_one_smul, neg_one_mul] using N.laplacian_smul (-1) f v

lemma laplacian_sub (f g : V → ℝ) (v : V) :
    N.laplacian (f - g) v = N.laplacian f v - N.laplacian g v := by
  classical
  simp only [laplacian, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  ring

/-- A subharmonic function at a global maximum has the same value at every
positive-conductance neighbor. -/
lemma eq_of_subharmonic_at_max (f : V → ℝ) {v w : V}
    (hmax : ∀ z, f z ≤ f v) (hsub : 0 ≤ N.laplacian f v)
    (hvw : 0 < N.a v w) : f w = f v := by
  classical
  have hterms : ∀ z ∈ (Finset.univ : Finset V), N.a v z * (f z - f v) ≤ 0 := by
    intro z _
    exact mul_nonpos_of_nonneg_of_nonpos (N.nonneg v z) (sub_nonpos.mpr (hmax z))
  have hsum : (∑ z, N.a v z * (f z - f v)) = 0 :=
    le_antisymm (Finset.sum_nonpos hterms) hsub
  have hterm := (Finset.sum_eq_zero_iff_of_nonpos hterms).mp hsum w (Finset.mem_univ w)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left hvw.ne')

/-- The maximum principle follows from finite geometry and boundary accessibility. -/
theorem maximum_principle (A : Set V) (haccess : N.BoundaryAccessible A)
    (f : V → ℝ) (M : ℝ) (hsub : ∀ v ∈ A, 0 ≤ N.laplacian f v)
    (hboundary : ∀ v, v ∉ A → f v ≤ M) : ∀ v, f v ≤ M := by
  classical
  intro v
  by_contra hv
  have hvM : M < f v := lt_of_not_ge hv
  obtain ⟨m, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset V) f
    ⟨v, Finset.mem_univ v⟩
  have hmax' : ∀ w, f w ≤ f m := fun w => hmax w (Finset.mem_univ w)
  have hmM : M < f m := hvM.trans_le (hmax' v)
  have hmA : m ∈ A := by
    by_contra hmA
    exact (not_lt_of_ge (hboundary m hmA)) hmM
  obtain ⟨w, hwA, hpath⟩ := haccess m hmA
  have hreach : ∀ {z}, Relation.ReflTransGen (fun v w => 0 < N.a v w) m z →
      f z = f m := by
    intro z hz
    induction hz with
    | refl => rfl
    | @tail y z _ hyz ih =>
      have hyA : y ∈ A := by
        by_contra hyA
        have hybound := hboundary y hyA
        rw [ih] at hybound
        exact (not_lt_of_ge hybound) hmM
      have hymax : ∀ t, f t ≤ f y := fun t => (hmax' t).trans_eq ih.symm
      exact (N.eq_of_subharmonic_at_max f hymax (hsub y hyA) hyz).trans ih
  have hwbound := hboundary w hwA
  rw [hreach hpath] at hwbound
  exact (not_lt_of_ge hwbound) hmM

/-- A harmonic function with zero boundary values vanishes everywhere. -/
theorem homogeneous_solution_eq_zero (A : Set V) (haccess : N.BoundaryAccessible A)
    (f : V → ℝ) (hL : ∀ v ∈ A, N.laplacian f v = 0)
    (hboundary : ∀ v, v ∉ A → f v = 0) : f = 0 := by
  have hu : ∀ v, f v ≤ 0 := N.maximum_principle A haccess f 0
    (fun v hv => le_of_eq (hL v hv).symm)
    (fun v hv => le_of_eq (hboundary v hv))
  have hl : ∀ v, (-f) v ≤ 0 := N.maximum_principle A haccess (-f) 0
    (fun v hv => by simp only [N.laplacian_neg, hL v hv, neg_zero, le_refl])
    (fun v hv => by simp only [Pi.neg_apply, hboundary v hv, neg_zero, le_refl])
  funext v
  exact le_antisymm (hu v) (neg_nonpos.mp (hl v))

/-- The square linear system for the Dirichlet problem: Laplacian rows in `A`
and identity rows on its complement. -/
noncomputable def dirichletOperator (A : Set V) : (V → ℝ) →ₗ[ℝ] (V → ℝ) := by
  classical
  refine
    { toFun := fun f v => if v ∈ A then N.laplacian f v else f v
      map_add' := ?_
      map_smul' := ?_ }
  · intro f g
    funext v
    by_cases hv : v ∈ A
    · simp only [hv, ite_true, Pi.add_apply, N.laplacian_add]
    · simp only [hv, ite_false, Pi.add_apply]
  · intro c f
    funext v
    by_cases hv : v ∈ A
    · simp only [hv, ite_true, Pi.smul_apply, smul_eq_mul, N.laplacian_smul,
        RingHom.id_apply]
    · simp only [hv, ite_false, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

@[simp] lemma dirichletOperator_apply (A : Set V) (f : V → ℝ) (v : V) :
    N.dirichletOperator A f v = if v ∈ A then N.laplacian f v else f v := by
  classical
  rfl

theorem dirichletOperator_injective (A : Set V) (haccess : N.BoundaryAccessible A) :
    Function.Injective (N.dirichletOperator A) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  apply N.homogeneous_solution_eq_zero A haccess f
  · intro v hv
    have hval := congr_fun hf v
    simpa only [dirichletOperator_apply, hv, ite_true, Pi.zero_apply] using hval
  · intro v hv
    have hval := congr_fun hf v
    simpa only [dirichletOperator_apply, hv, ite_false, Pi.zero_apply] using hval

theorem dirichlet_unique (A : Set V) (haccess : N.BoundaryAccessible A)
    {g f₁ f₂ : V → ℝ} (h₁ : N.SolvesDirichlet A g f₁)
    (h₂ : N.SolvesDirichlet A g f₂) : f₁ = f₂ := by
  classical
  apply N.dirichletOperator_injective A haccess
  funext v
  by_cases hv : v ∈ A
  · simp only [dirichletOperator_apply, hv, ite_true, h₁.1 v hv, h₂.1 v hv]
  · simp only [dirichletOperator_apply, hv, ite_false, h₁.2 v hv, h₂.2 v hv]

/-- Existence is derived from injectivity of the actual finite-dimensional
Dirichlet operator, not assumed as extra network data. -/
theorem existsUnique_dirichlet (A : Set V) (haccess : N.BoundaryAccessible A)
    (g : V → ℝ) : ∃! f : V → ℝ, N.SolvesDirichlet A g f := by
  classical
  have hsurj : Function.Surjective (N.dirichletOperator A) :=
    LinearMap.injective_iff_surjective.mp (N.dirichletOperator_injective A haccess)
  obtain ⟨f, hf⟩ := hsurj (fun v => if v ∈ A then 0 else g v)
  have hsol : N.SolvesDirichlet A g f := by
    constructor
    · intro v hv
      have hval := congr_fun hf v
      simpa only [dirichletOperator_apply, hv, ite_true] using hval
    · intro v hv
      have hval := congr_fun hf v
      simpa only [dirichletOperator_apply, hv, ite_false] using hval
  exact ⟨f, hsol, fun f' hf' => N.dirichlet_unique A haccess hf' hsol⟩

/-- The genuine finite Dirichlet solution, selected from the proved existence theorem. -/
noncomputable def dirichletSolution (A : Set V) (haccess : N.BoundaryAccessible A)
    (g : V → ℝ) : V → ℝ :=
  Classical.choose (N.existsUnique_dirichlet A haccess g).exists

theorem dirichletSolution_spec (A : Set V) (haccess : N.BoundaryAccessible A)
    (g : V → ℝ) : N.SolvesDirichlet A g (N.dirichletSolution A haccess g) :=
  Classical.choose_spec (N.existsUnique_dirichlet A haccess g).exists

/-- Uniform perturbations of boundary data cause no larger perturbation of
the corresponding harmonic extensions. -/
theorem dirichlet_stability (A : Set V) (haccess : N.BoundaryAccessible A)
    {g₁ g₂ f₁ f₂ : V → ℝ} (h₁ : N.SolvesDirichlet A g₁ f₁)
    (h₂ : N.SolvesDirichlet A g₂ f₂) {η : ℝ}
    (hboundary : ∀ v, v ∉ A → |g₁ v - g₂ v| ≤ η) :
    ∀ v, |f₁ v - f₂ v| ≤ η := by
  have hu : ∀ v, (f₁ - f₂) v ≤ η :=
    N.maximum_principle A haccess (f₁ - f₂) η
      (fun v hv => by simp only [N.laplacian_sub, h₁.1 v hv, h₂.1 v hv,
        sub_self, le_refl])
      (fun v hv => by
        change f₁ v - f₂ v ≤ η
        rw [h₁.2 v hv, h₂.2 v hv]
        exact (abs_le.mp (hboundary v hv)).2)
  have hl : ∀ v, (f₂ - f₁) v ≤ η :=
    N.maximum_principle A haccess (f₂ - f₁) η
      (fun v hv => by simp only [N.laplacian_sub, h₂.1 v hv, h₁.1 v hv,
        sub_self, le_refl])
      (fun v hv => by
        change f₂ v - f₁ v ≤ η
        rw [h₂.2 v hv, h₁.2 v hv]
        have h := (abs_le.mp (hboundary v hv)).1
        linarith)
  intro v
  apply abs_le.mpr
  constructor
  · have h := hl v
    change f₂ v - f₁ v ≤ η at h
    linarith
  · exact hu v

theorem dirichletSolution_stability (A : Set V) (haccess : N.BoundaryAccessible A)
    (g₁ g₂ : V → ℝ) {η : ℝ}
    (hboundary : ∀ v, v ∉ A → |g₁ v - g₂ v| ≤ η) :
    ∀ v, |N.dirichletSolution A haccess g₁ v - N.dirichletSolution A haccess g₂ v| ≤ η :=
  N.dirichlet_stability A haccess (N.dirichletSolution_spec A haccess g₁)
    (N.dirichletSolution_spec A haccess g₂) hboundary

/-- A strictly subharmonic function rules out a positive-conductance component
contained entirely in the interior. This criterion supplies boundary accessibility
from a Laplacian computation, without assuming existence of a Dirichlet solver. -/
theorem boundaryAccessible_of_strict_subharmonic (A : Set V) (f : V → ℝ)
    (hstrict : ∀ v ∈ A, 0 < N.laplacian f v) : N.BoundaryAccessible A := by
  classical
  intro v _
  by_contra hno
  have hinside : ∀ w,
      Relation.ReflTransGen (fun v w => 0 < N.a v w) v w → w ∈ A := by
    intro w hw
    by_contra hwA
    exact hno ⟨w, hwA, hw⟩
  let R : Finset V := Finset.univ.filter
    (fun w => Relation.ReflTransGen (fun v w => 0 < N.a v w) v w)
  have hvR : v ∈ R :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ v, Relation.ReflTransGen.refl⟩
  obtain ⟨m, hmR, hmax⟩ := Finset.exists_max_image R f ⟨v, hvR⟩
  have hmreach : Relation.ReflTransGen (fun v w => 0 < N.a v w) v m :=
    (Finset.mem_filter.mp hmR).2
  have hnonpos : N.laplacian f m ≤ 0 := by
    apply Finset.sum_nonpos
    intro w _
    by_cases ha : N.a m w = 0
    · simp only [ha, zero_mul, le_refl]
    · have hpos : 0 < N.a m w := lt_of_le_of_ne (N.nonneg m w) (fun h => ha h.symm)
      have hwR : w ∈ R := Finset.mem_filter.mpr
        ⟨Finset.mem_univ w, hmreach.tail hpos⟩
      exact mul_nonpos_of_nonneg_of_nonpos (N.nonneg m w)
        (sub_nonpos.mpr (hmax w hwR))
  exact (not_lt_of_ge hnonpos) (hstrict m (hinside m hmreach))

end FiniteConductanceNetwork
end BouRabeeGwynne
