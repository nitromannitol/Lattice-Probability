import LatticeProb.Prob.Percolation.LatticeOrderZeroApproximation
import LatticeProb.Prob.Percolation.LatticeBondTranslationLaw
import LatticeProb.Prob.Percolation.OpenComponentTranslationIso

/-! Translate origin-centered order-zero approximation to all lattice centers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped BigOperators
namespace LatticeProb.Percolation
noncomputable section
variable {d : ℕ} {ω : Configuration d}

/-- The lattice embedding preserves addition. -/
theorem latticeEuclideanEmbedding_add (x y : Vertex d) :
    latticeEuclideanEmbedding (x + y) =
      latticeEuclideanEmbedding x + latticeEuclideanEmbedding y := by
  ext i
  simp [latticeEuclideanEmbedding]

/-- Translation preserves membership in a component ball. -/
theorem mem_componentEuclideanBall_translation (z a : Vertex d) (C : OpenComponent ω)
    (r : ℝ) (x : C) :
    openComponentTranslationIso z C x ∈
      componentEuclideanBall (openComponentTranslation z ω C) (a + z) r ↔
        x ∈ componentEuclideanBall C a r := by
  simp only [mem_componentEuclideanBall, openComponentTranslationIso_val,
    latticeEuclideanEmbedding_add, dist_add_right]

/-- A translated component ball is the image of the original finite ball. -/
theorem componentEuclideanBall_translation (z a : Vertex d) (C : OpenComponent ω) (r : ℝ) :
    (componentEuclideanBall C a r).map (openComponentTranslationIso z C).toEquiv.toEmbedding =
      componentEuclideanBall (openComponentTranslation z ω C) (a + z) r := by
  classical
  ext y
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_componentEuclideanBall_translation z a C r x).mpr hx
  · intro hy
    refine ⟨(openComponentTranslationIso z C).symm y, ?_,
      (openComponentTranslationIso z C).apply_symm_apply y⟩
    apply (mem_componentEuclideanBall_translation z a C r _).mp
    simpa only [(openComponentTranslationIso z C).apply_symm_apply] using hy

/-- Translation preserves the normalized component-ball L² expression. -/
theorem componentBallL2_translation (z a : Vertex d) (C : OpenComponent ω) (r : ℝ)
    (u : C → ℝ) :
    componentBallL2 (openComponentTranslation z ω C) (a + z) r
      (fun y => u ((openComponentTranslationIso z C).symm y)) = componentBallL2 C a r u := by
  classical
  rw [componentBallL2, ← componentEuclideanBall_translation z a C r]
  simp only [Finset.sum_map, Finset.card_map, componentBallL2]
  congr 2
  apply Finset.sum_congr rfl
  intro x hx
  change u ((openComponentTranslationIso z C).symm
    (openComponentTranslationIso z C x)) ^ 2 = u x ^ 2
  rw [(openComponentTranslationIso z C).symm_apply_apply]

/-- An origin-centered approximation transports to the corresponding center. -/
theorem origin_constant_approximation_translation (z : Vertex d)
    (h : HasUniqueInfiniteOpenComponent ω) (X C : ℝ)
    (happ : ∀ (R : ℝ), 2 * X ≤ R →
      ∀ u : uniqueInfiniteComponent
          ((hasUniqueInfiniteOpenComponent_translation_iff (-z) ω).mpr h) → ℝ,
        (∀ x ∈ componentEuclideanBall _ 0 R,
          (∀ y, (componentGraph _).Adj x y → y ∈ componentEuclideanBall _ 0 R) →
            componentLaplacian _ u x = 0) →
        ∃ c : ℝ, ∀ r : ℝ, X ≤ r → r ≤ R / 2 →
          componentBallL2 _ 0 r (u - fun _ => c) ≤ C * (r / R) * componentBallL2 _ 0 R u) :
    ∀ (R : ℝ), 2 * X ≤ R → ∀ u : uniqueInfiniteComponent h → ℝ,
      (∀ x ∈ componentEuclideanBall _ z R,
        (∀ y, (componentGraph _).Adj x y → y ∈ componentEuclideanBall _ z R) →
          componentLaplacian _ u x = 0) →
      ∃ c : ℝ, ∀ r : ℝ, X ≤ r → r ≤ R / 2 →
        componentBallL2 _ z r (u - fun _ => c) ≤ C * (r / R) * componentBallL2 _ z R u := by
  classical
  have heq := openComponentTranslation_uniqueInfiniteComponent (-z) h
  rw [← heq] at happ
  intro R hR u hu
  let e := openComponentTranslationIso (-z) (uniqueInfiniteComponent h)
  let v : openComponentTranslation (-z) ω (uniqueInfiniteComponent h) → ℝ :=
    fun y => u (e.symm y)
  have hv : ∀ x ∈ componentEuclideanBall _ 0 R,
      (∀ y, (componentGraph _).Adj x y → y ∈ componentEuclideanBall _ 0 R) →
        componentLaplacian _ v x = 0 := by
    intro x hx hinside
    let x' := e.symm x
    have hx' : x' ∈ componentEuclideanBall (uniqueInfiniteComponent h) z R := by
      apply (mem_componentEuclideanBall_translation (-z) z _ R x').mp
      simpa [e, x'] using hx
    have hi : ∀ y, (componentGraph (uniqueInfiniteComponent h)).Adj x' y →
        y ∈ componentEuclideanBall (uniqueInfiniteComponent h) z R := by
      intro y hy
      apply (mem_componentEuclideanBall_translation (-z) z _ R y).mp
      have hadj : (componentGraph _).Adj x (e y) := by
        simpa [x'] using e.map_rel_iff.mpr hy
      have hy' := hinside (e y) hadj
      simpa using hy'
    have hl := componentLaplacian_translation (-z) (uniqueInfiniteComponent h) u x'
    simpa [v, e, x'] using hl.trans (hu x' hx' hi)
  obtain ⟨c, hc⟩ := happ R hR v hv
  refine ⟨c, ?_⟩
  intro r hr hrr
  have h1 := componentBallL2_translation (-z) z (uniqueInfiniteComponent h) r (u - fun _ => c)
  have h2 := componentBallL2_translation (-z) z (uniqueInfiniteComponent h) R u
  simp only [add_neg_cancel] at h1 h2
  rw [← h1, ← h2]
  have hvsub : v - (fun _ => c) = (fun y => u (e.symm y) - c) := by
    funext y
    rfl
  rw [hvsub] at hc
  simpa [v, e] using (hc r hr hrr)

/-- The order-zero input gives one event of constant approximation at all centers. -/
theorem exists_all_centers_constant_approximation
    (input : LatticeProb.External.ArmstrongDarioOrderZero)
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ (s θ C : ℝ), 0 < s ∧ 0 < θ ∧ 0 < C ∧
      ∃ X : Vertex d → Configuration d → ℝ,
        (∀ z, Measurable (X z)) ∧ (∀ z ω, 0 ≤ X z ω) ∧
        (∀ z, Integrable (fun ω => Real.exp (Real.rpow (X z ω / θ) s))
          (latticeBondLaw d p)) ∧
        (∀ z, (∫ ω, Real.exp (Real.rpow (X z ω / θ) s) ∂latticeBondLaw d p) ≤ 2) ∧
        ∀ᵐ ω ∂latticeBondLaw d p,
          ∃ _h : HasUniqueInfiniteOpenComponent ω,
            ∀ h' : HasUniqueInfiniteOpenComponent ω, ∀ z : Vertex d,
              ∀ (R : ℝ), 2 * X z ω ≤ R →
                ∀ u : uniqueInfiniteComponent h' → ℝ,
                  (∀ x ∈ componentEuclideanBall (uniqueInfiniteComponent h') z R,
                    (∀ y : uniqueInfiniteComponent h',
                      (componentGraph (uniqueInfiniteComponent h')).Adj x y →
                        y ∈ componentEuclideanBall (uniqueInfiniteComponent h') z R) →
                    componentLaplacian (uniqueInfiniteComponent h') u x = 0) →
                  ∃ c : ℝ, ∀ r : ℝ, X z ω ≤ r → r ≤ R / 2 →
                    componentBallL2 (uniqueInfiniteComponent h') z r (u - fun _ => c) ≤
                      C * (r / R) * componentBallL2 (uniqueInfiniteComponent h') z R u := by
  obtain ⟨s, θ, C, hs, hθ, hC, X, hXm, hXn, hXi, hXb, hAE⟩ :=
    exists_origin_constant_approximation input d hd p hp hp1
  let Y : Vertex d → Configuration d → ℝ := fun z ω => X (configurationTranslation (-z) ω)
  refine ⟨s, θ, C, hs, hθ, hC, Y, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    exact hXm.comp (configurationTranslationMeasurableEquiv (-z)).measurable
  · intro z ω
    exact hXn _
  · intro z
    exact (measurePreserving_configurationTranslation p (-z)).integrable_comp_of_integrable hXi
  · intro z
    have he := (measurePreserving_configurationTranslation p (-z)).integral_comp
      (configurationTranslationMeasurableEquiv (-z)).measurableEmbedding
      (fun ω => Real.exp (Real.rpow (X ω / θ) s))
    exact he.trans_le hXb
  · have hall := ae_all_iff.mpr (fun z : Vertex d =>
      (measurePreserving_configurationTranslation p (-z)).quasiMeasurePreserving.ae hAE)
    filter_upwards [hAE, hall] with ω hω hz
    obtain ⟨h, _⟩ := hω
    refine ⟨h, ?_⟩
    intro h' z
    have ht := (hasUniqueInfiniteOpenComponent_translation_iff (-z) ω).mpr h'
    exact origin_constant_approximation_translation z h' (Y z ω) C ((hz z).2 ht)

end
end LatticeProb.Percolation
