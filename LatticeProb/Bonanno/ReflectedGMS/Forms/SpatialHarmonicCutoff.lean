/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.SpatialHarmonicCutoff at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.BoundedEnergyAlgebra
import LatticeProb.Bonanno.ReflectedGMS.Forms.Resolvent
import LatticeProb.Bonanno.ReflectedGMS.StatementIngredients

/-!
# A full-domain representative of a spatially local potential

The explicit radial cutoff below uses a collar of width one. Its hypotheses
are local energy of the radius and potential on an enclosing patch, a local
bound on the potential, and containment of edges touching the cutoff support.
No global finite energy of the uncropped potential, finite support, or
existence of an extension is assumed. The geometric producer of local radius
energy from the manuscript's diameter-weighted conductance mass is separate.
-/

set_option autoImplicit false

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*}

/-- A radial cutoff equal to one on the closed radius-R ball and zero outside
its radius-(R+1) collar. -/
noncomputable def spatialRadialCutoff (z : V → Plane) (R : ℝ) (v : V) : ℝ :=
  unitIntervalProjection (R + 1 - ‖z v‖)

/-- The actual global vertex function used to localize a scalar coordinate. -/
noncomputable def spatialHarmonicCutoff (z : V → Plane) (R : ℝ) (f : V → ℝ) : V → ℝ :=
  spatialRadialCutoff z R * f

theorem spatialRadialCutoff_mem (z : V → Plane) (R : ℝ) (v : V) :
    spatialRadialCutoff z R v ∈ Set.Icc (0 : ℝ) 1 :=
  unitIntervalProjection_mem _

theorem spatialRadialCutoff_eq_one (z : V → Plane) (R : ℝ) (v : V)
    (hv : ‖z v‖ ≤ R) : spatialRadialCutoff z R v = 1 := by
  simp only [spatialRadialCutoff, unitIntervalProjection]
  rw [Set.projIcc_of_right_le _ (by linarith)]

theorem spatialRadialCutoff_eq_zero (z : V → Plane) (R : ℝ) (v : V)
    (hv : R + 1 ≤ ‖z v‖) : spatialRadialCutoff z R v = 0 := by
  simp only [spatialRadialCutoff, unitIntervalProjection]
  rw [Set.projIcc_of_le_left _ (by linarith)]

theorem spatialHarmonicCutoff_eqOn (z : V → Plane) (R : ℝ) (f : V → ℝ) :
    Set.EqOn (spatialHarmonicCutoff z R f) f {v | ‖z v‖ ≤ R} := by
  intro v hv
  simp [spatialHarmonicCutoff, spatialRadialCutoff_eq_one z R v hv]

/-- Local boundedness suffices for boundedness of the global cutoff. -/
theorem spatialHarmonicCutoff_abs_le (z : V → Plane) (R : ℝ) (f : V → ℝ)
    (A : Set V) {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ v, ‖z v‖ < R + 1 → v ∈ A)
    (hf : ∀ v ∈ A, |f v| ≤ B) :
    ∀ v, |spatialHarmonicCutoff z R f v| ≤ B := by
  intro v
  by_cases hv : ‖z v‖ < R + 1
  · have he := spatialRadialCutoff_mem z R v
    simp only [spatialHarmonicCutoff, Pi.mul_apply, abs_mul, abs_of_nonneg he.1]
    exact (mul_le_mul_of_nonneg_right he.2 (abs_nonneg _)).trans
      (by simpa using hf v (hA v hv))
  · simp [spatialHarmonicCutoff,
      spatialRadialCutoff_eq_zero z R v (le_of_not_gt hv), hB]

/-- Restriction energy transfers to the full graph when all nonzero edge
increments have both endpoints in the patch. The patch may be infinite. -/
theorem hasFiniteEnergy_of_restriction_of_edge_support
    (G : ReflectedWalk.ConductanceGraph V) (A : Set V) (u : V → ℝ)
    (hu : (restrictGraph G A).HasFiniteEnergy (fun v => u v.1))
    (hs : ∀ v w, v ∉ A ∨ w ∉ A → G.gradSq u (v, w) = 0) :
    G.HasFiniteEnergy u := by
  let e : A × A → V × V := fun p => (p.1.1, p.2.1)
  have he : Function.Injective e := by
    intro p q hpq
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hpq))
      (Subtype.ext (congrArg Prod.snd hpq))
  apply (he.summable_iff (f := G.gradSq u) ?_).mp hu
  intro p hp
  apply hs p.1 p.2
  by_contra hn
  push_neg at hn
  exact hp ⟨(⟨p.1, hn.1⟩, ⟨p.2, hn.2⟩), rfl⟩

/-- A genuine full finite-energy extension from local radius and potential
energy. The collar condition is a geometric statement about ordinary edges. -/
theorem spatialHarmonicCutoff_hasFiniteEnergy
    (G : ReflectedWalk.ConductanceGraph V) (z : V → Plane) (R : ℝ)
    (f : V → ℝ) (A : Set V) {B : ℝ}
    (hf : ∀ v ∈ A, |f v| ≤ B)
    (hrE : (restrictGraph G A).HasFiniteEnergy (fun v => ‖z v.1‖))
    (hfE : (restrictGraph G A).HasFiniteEnergy (fun v => f v.1))
    (hcollar : ∀ v w, G.c v w ≠ 0 →
      (‖z v‖ < R + 1 ∨ ‖z w‖ < R + 1) → v ∈ A ∧ w ∈ A) :
    G.HasFiniteEnergy (spatialHarmonicCutoff z R f) := by
  have hetaE : (restrictGraph G A).HasFiniteEnergy
      (fun v => spatialRadialCutoff z R v.1) :=
    hasFiniteEnergy_contraction (restrictGraph G A)
      (fun v => R + 1 - ‖z v.1‖) unitIntervalProjection_lipschitz
      (((restrictGraph G A).hasFiniteEnergy_const (R + 1)).sub hrE)
  have hlocal : (restrictGraph G A).HasFiniteEnergy
      (fun v => spatialHarmonicCutoff z R f v.1) := by
    apply hasFiniteEnergy_mul_of_bounded (restrictGraph G A)
      (A := 1) (B := B) _ (fun v => hf v.1 v.2) hetaE hfE
    intro v
    have he := spatialRadialCutoff_mem z R v.1
    simpa only [abs_of_nonneg he.1] using he.2
  apply hasFiniteEnergy_of_restriction_of_edge_support G A _ hlocal
  intro v w hvw
  by_cases hc : G.c v w = 0
  · simp [ReflectedWalk.ConductanceGraph.gradSq, hc]
  have hout : ¬ (‖z v‖ < R + 1 ∨ ‖z w‖ < R + 1) := by
    intro hin
    have hh := hcollar v w hc hin
    exact hvw.elim (fun hv => hv hh.1) (fun hw => hw hh.2)
  push_neg at hout
  simp [ReflectedWalk.ConductanceGraph.gradSq, spatialHarmonicCutoff,
    spatialRadialCutoff_eq_zero z R v hout.1,
    spatialRadialCutoff_eq_zero z R w hout.2]

/-- The cutoff enters the actual full Hilbert domain for every summable positive
speed and agrees with the original coordinate throughout the inner region. -/
theorem exists_spatialHarmonicCutoff_hilbertDomain
    (G : ReflectedWalk.ConductanceGraph V) (z : V → Plane) (R : ℝ)
    (f : V → ℝ) (A : Set V) {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ v, ‖z v‖ < R + 1 → v ∈ A)
    (hf : ∀ v ∈ A, |f v| ≤ B)
    (hrE : (restrictGraph G A).HasFiniteEnergy (fun v => ‖z v.1‖))
    (hfE : (restrictGraph G A).HasFiniteEnergy (fun v => f v.1))
    (hcollar : ∀ v w, G.c v w ≠ 0 →
      (‖z v‖ < R + 1 ∨ ‖z w‖ < R + 1) → v ∈ A ∧ w ∈ A)
    (m : V → ℝ) (hm : ∀ v, 0 < m v) (hmsum : Summable m) :
    ∃ U : hilbertDomain G m,
      unweight m (valueInclusion G m U) = spatialHarmonicCutoff z R f ∧
      Set.EqOn (unweight m (valueInclusion G m U)) f {v | ‖z v‖ ≤ R} := by
  have hL2 := hasSpeedL2_of_abs_le hm hmsum
    (spatialHarmonicCutoff_abs_le z R f A hB hA hf)
  have hE := spatialHarmonicCutoff_hasFiniteEnergy G z R f A hf hrE hfE hcollar
  refine ⟨inHilbertDomain G m hm _ hL2 hE, ?_, ?_⟩
  · simp only [valueInclusion_inHilbertDomain, unweight_weightedValue m hm]
  · simpa only [valueInclusion_inHilbertDomain, unweight_weightedValue m hm] using
      spatialHarmonicCutoff_eqOn z R f

end ReflectedGMS.FullNetworkForm
