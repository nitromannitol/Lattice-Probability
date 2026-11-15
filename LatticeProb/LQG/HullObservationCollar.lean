import LatticeProb.LQG.CollarOpenContainment
import LatticeProb.LQG.MeasurableHullCofinal
import LatticeProb.LQG.UniformCollarHull

/-! # Dyadic hull observations inside compact collars -/

set_option autoImplicit false

noncomputable section

open MeasureTheory MeasurableSpace Set Metric TopologicalSpace LQGMetric
open LQGMetric.Blueprint LQGMetric.LocalEvent LQGMetric.CONF SmallGammaGeodesics

namespace LatticeProb.LQG

/-- The hit sigma-field of a compact set is observed by its collar code. -/
theorem setSigma_le_collarFieldCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k : ℕ) :
    setSigma (fun ω => (K ω : Set ℂ)) ≤
      MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k) inferInstance := by
  let : MeasurableSpace Ω := MeasurableSpace.comap
    (collarFieldCode h K localDenseTest ψ hp k) inferInstance
  have hK : Measurable K :=
    (comap_measurable (collarFieldCode h K localDenseTest ψ hp k)).fst
  apply MeasurableSpace.generateFrom_le
  rintro E ⟨U, hU, rfl⟩
  exact (TopologicalSpace.NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU).measurableSet.preimage hK

/-- A fixed-open mean-zero field event, restricted to a measurable event on
which the open set lies in the collar, is observable from the collar code. -/
theorem measurableSet_inter_fieldSigma0On_of_collarFieldCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k : ℕ) (O : Opens ℂ) (E F : Set Ω)
    (hE : MeasurableSet[MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp k) inferInstance] E)
    (hO : ∀ ω ∈ E, (O : Set ℂ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    (hF : MeasurableSet[fieldSigma0On h O] F) :
    MeasurableSet[MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp k) inferInstance] (E ∩ F) := by
  let : MeasurableSpace Ω := MeasurableSpace.comap
    (collarFieldCode h K localDenseTest ψ hp k) inferInstance
  have hcode : collarFieldCode (fun ω : E => h ω) (fun ω : E => K ω)
      localDenseTest ψ hp k = (collarFieldCode h K localDenseTest ψ hp k) ∘ Subtype.val := by
    funext ω
    simp only [collarFieldCode, Function.comp_apply]
    apply Prod.ext rfl
    apply Prod.ext ?_ rfl
    funext i
    simp only [Set.indicator]
  have hlocal : fieldSigma0On (fun ω : E => h ω) O ≤ (inferInstance : MeasurableSpace E) := by
    unfold fieldSigma0On
    apply Measurable.comap_le
    apply measurable_pi_iff.mpr
    intro φ
    have hm := measurable_pairing_of_collarFieldCode
      (fun ω : E => h ω) (fun ω : E => K ω) ψ hp k O
      (fun ω => hO ω ω.property) φ.1.1 φ.2 φ.1.2
    rw [hcode, ← MeasurableSpace.comap_comp] at hm
    exact hm
  have hF' : MeasurableSet ((Subtype.val : E → Ω) ⁻¹' F) := by
    apply hlocal
    have heq : fieldSigma0On (fun ω : E => h ω) O =
        MeasurableSpace.comap (Subtype.val : E → Ω) (fieldSigma0On h O) := by
      unfold fieldSigma0On
      rw [MeasurableSpace.comap_comp]
      rfl
    rw [heq]
    exact hF.preimage (comap_measurable _)
  have hm := hE.subtype_image hF'
  simpa only [Subtype.image_preimage_coe] using hm

/-- If a dyadic hull is contained in the collar, its mean-zero field
observation is measurable from the collar code. -/
theorem hullSigma0_le_collarFieldCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k n : ℕ)
    (hsub : ∀ ω, dyadicHull n (K ω : Set ℂ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)) :
    hullSigma0 h (fun ω => (K ω : Set ℂ)) n ≤
      MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k) inferInstance := by
  let A : Ω → Set ℂ := fun ω => K ω
  let m : MeasurableSpace Ω := MeasurableSpace.comap
    (collarFieldCode h K localDenseTest ψ hp k) inferInstance
  have hset : setSigma A ≤ m := setSigma_le_collarFieldCode h K ψ hp k
  unfold hullSigma0
  apply sup_le hset
  apply MeasurableSpace.generateFrom_le
  rintro T ⟨S, F, hF, rfl⟩
  have hE : MeasurableSet[m] {ω | dyadicHull n (A ω) = S} :=
    hset _ (measurableSet_hull_eq (fun ω => (K ω).isCompact.isClosed) n S)
  exact measurableSet_inter_fieldSigma0On_of_collarFieldCode h K ψ hp k
    ⟨interior S, isOpen_interior⟩ _ F hE
    (fun ω hω => by
      change dyadicHull n (K ω : Set ℂ) = S at hω
      rw [← hω]
      exact interior_subset.trans (hsub ω)) hF

end LatticeProb.LQG
