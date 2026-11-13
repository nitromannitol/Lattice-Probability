/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.Resolvent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.HilbertEnergySpace
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The 1-resolvent of the full network form

Let `J` be the bounded inclusion of the complete full energy Hilbert space into
weighted vertex `L²`. Its existing Hilbert-space adjoint gives the unique weak
solution `J.adjoint f`; the vertex-space resolvent is `J ∘ J.adjoint`.

The variational identity below is tested against the entire full energy domain.
Its function-level form uses the original half-ordered-pair `dirichletForm`.
No process association or semigroup representation is asserted here.
-/

set_option autoImplicit false

open scoped InnerProductSpace

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

/-- The bounded inclusion into weighted vertex `L²`, using the existing projection. -/
noncomputable def valueInclusion (m : V → ℝ) :
    hilbertDomain G m →L[ℝ] ValueSpace V :=
  (WithLp.fstL 2 ℝ (ValueSpace V) (GradientSpace V)).comp (hilbertDomain G m).subtypeL

/-- The full normalized gradient projection. -/
noncomputable def gradientInclusion (m : V → ℝ) :
    hilbertDomain G m →L[ℝ] GradientSpace V :=
  (WithLp.sndL 2 ℝ (ValueSpace V) (GradientSpace V)).comp (hilbertDomain G m).subtypeL

/-- The value inclusion is a contraction in the actual Hilbert graph norm. -/
theorem valueInclusion_norm_le (m : V → ℝ) (u : hilbertDomain G m) :
    ‖valueInclusion G m u‖ ≤ ‖u‖ :=
  WithLp.norm_fst_le (ValueSpace V) (u : EnergyAmbient V)

/-- The Hilbert inner product is exactly the sum of value and gradient pairings. -/
theorem hilbertDomain_inner (m : V → ℝ) (u v : hilbertDomain G m) :
    ⟪u, v⟫_ℝ = ⟪valueInclusion G m u, valueInclusion G m v⟫_ℝ +
      ⟪gradientInclusion G m u, gradientInclusion G m v⟫_ℝ := rfl

/-- Every element of the Hilbert domain has full finite energy after decoding. -/
theorem hilbertDomain_hasFiniteEnergy (m : V → ℝ) (u : hilbertDomain G m) :
    G.HasFiniteEnergy (unweight m (valueInclusion G m u)) :=
  (exists_gradient_iff G m (valueInclusion G m u)).1
    ⟨gradientInclusion G m u, u.property⟩

/-- The abstract gradient coordinate is exactly the existing weighted gradient. -/
theorem gradientInclusion_eq (m : V → ℝ) (u : hilbertDomain G m) :
    gradientInclusion G m u =
      weightedGradient G (unweight m (valueInclusion G m u))
        (hilbertDomain_hasFiniteEnergy G m u) := by
  apply lp.ext
  funext p
  exact u.property p

@[simp] theorem valueInclusion_inHilbertDomain (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (f : V → ℝ) (hL2 : HasSpeedL2 m f) (hE : G.HasFiniteEnergy f) :
    valueInclusion G m (inHilbertDomain G m hm f hL2 hE) = weightedValue m f hL2 := rfl

@[simp] theorem gradientInclusion_inHilbertDomain (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (f : V → ℝ) (hL2 : HasSpeedL2 m f) (hE : G.HasFiniteEnergy f) :
    gradientInclusion G m (inHilbertDomain G m hm f hL2 hE) =
      weightedGradient G f hE := rfl

/-- The gradient pairing has the manuscript's half-ordered-edge normalization. -/
theorem weightedGradient_inner (f g : V → ℝ)
    (hf : G.HasFiniteEnergy f) (hg : G.HasFiniteEnergy g) :
    ⟪weightedGradient G f hf, weightedGradient G g hg⟫_ℝ = G.dirichletForm f g := by
  rw [lp.inner_eq_tsum]
  change (∑' p : V × V,
    (Real.sqrt (G.c p.1 p.2 / 2) * (g p.2 - g p.1)) *
      (Real.sqrt (G.c p.1 p.2 / 2) * (f p.2 - f p.1))) =
    (∑' p : V × V, G.gradProd f g p) / 2
  rw [← tsum_div_const]
  apply tsum_congr
  intro p
  calc
    _ = (Real.sqrt (G.c p.1 p.2 / 2)) ^ 2 *
        ((f p.2 - f p.1) * (g p.2 - g p.1)) := by ring
    _ = G.gradProd f g p / 2 := by
      rw [Real.sq_sqrt (div_nonneg (G.c_nonneg _ _) (by norm_num))]
      unfold ReflectedWalk.ConductanceGraph.gradProd
      ring

/-- The Riesz solution of the full form's 1-resolvent equation. -/
noncomputable def oneResolventLift (m : V → ℝ) :
    ValueSpace V →L[ℝ] hilbertDomain G m := (valueInclusion G m).adjoint

/-- The actual bounded 1-resolvent acting on weighted vertex `L²`. -/
noncomputable def oneResolvent (m : V → ℝ) : ValueSpace V →L[ℝ] ValueSpace V :=
  (valueInclusion G m).comp (oneResolventLift G m)

/-- The variational identity holds against every full-domain test vector. -/
theorem oneResolventLift_weak (m : V → ℝ) (f : ValueSpace V)
    (v : hilbertDomain G m) :
    ⟪valueInclusion G m (oneResolventLift G m f), valueInclusion G m v⟫_ℝ +
      ⟪gradientInclusion G m (oneResolventLift G m f), gradientInclusion G m v⟫_ℝ =
      ⟪f, valueInclusion G m v⟫_ℝ := by
  rw [← hilbertDomain_inner]
  exact (valueInclusion G m).adjoint_inner_left v f

/-- No other element of the full domain solves this variational equation. -/
theorem oneResolventLift_unique (m : V → ℝ) (f : ValueSpace V)
    (u : hilbertDomain G m)
    (hu : ∀ v : hilbertDomain G m,
      ⟪valueInclusion G m u, valueInclusion G m v⟫_ℝ +
        ⟪gradientInclusion G m u, gradientInclusion G m v⟫_ℝ =
        ⟪f, valueInclusion G m v⟫_ℝ) :
    u = oneResolventLift G m f := by
  apply ext_inner_right ℝ
  intro v
  rw [hilbertDomain_inner, hilbertDomain_inner]
  exact (hu v).trans (oneResolventLift_weak G m f v).symm

/-- Decode the weighted `L²` resolvent to the actual vertex function. -/
noncomputable def oneResolventFunction (m : V → ℝ) (f : ValueSpace V) : V → ℝ :=
  unweight m (oneResolvent G m f)

theorem oneResolventFunction_hasFiniteEnergy (m : V → ℝ) (f : ValueSpace V) :
    G.HasFiniteEnergy (oneResolventFunction G m f) :=
  hilbertDomain_hasFiniteEnergy G m (oneResolventLift G m f)

/-- Strictly positive atomic speeds make every weighted `lp 2` vector an actual
speed-`L²` vertex function. -/
theorem hasSpeedL2_unweight (m : V → ℝ) (hm : ∀ v, 0 < m v) (u : ValueSpace V) :
    HasSpeedL2 m (unweight m u) := by
  change Memℓp (fun v => Real.sqrt (m v) * (u v / Real.sqrt (m v))) 2
  have heq : (fun v => Real.sqrt (m v) * (u v / Real.sqrt (m v))) = (u : V → ℝ) := by
    funext v
    exact mul_div_cancel₀ (u v) (Real.sqrt_pos.2 (hm v)).ne'
  rw [heq]
  exact u.property

theorem oneResolventFunction_hasSpeedL2 (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (f : ValueSpace V) : HasSpeedL2 m (oneResolventFunction G m f) :=
  hasSpeedL2_unweight m hm (oneResolvent G m f)

/-- The concrete weak resolvent equation with the original network form and
all speed-`L²`, full finite-energy vertex functions as tests. -/
theorem oneResolventFunction_weak (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (f : ValueSpace V) (g : V → ℝ) (hL2 : HasSpeedL2 m g) (hE : G.HasFiniteEnergy g) :
    ⟪oneResolvent G m f, weightedValue m g hL2⟫_ℝ +
      G.dirichletForm (oneResolventFunction G m f) g =
      ⟪f, weightedValue m g hL2⟫_ℝ := by
  have h := oneResolventLift_weak G m f (inHilbertDomain G m hm g hL2 hE)
  rw [valueInclusion_inHilbertDomain, gradientInclusion_inHilbertDomain,
    gradientInclusion_eq, weightedGradient_inner] at h
  exact h

end ReflectedGMS.FullNetworkForm
