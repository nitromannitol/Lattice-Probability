import LatticeProb.LQG.HullCollarGerm

/-! # Pullbacks of hull and collar observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set TopologicalSpace LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- The hit sigma algebra is preserved by pulling back the random set. -/
theorem comap_setSigma {X Ω : Type} (f : X → Ω) (A : Ω → Set ℂ) :
    MeasurableSpace.comap f (setSigma A) = setSigma (A ∘ f) := by
  unfold setSigma
  rw [MeasurableSpace.comap_generateFrom]
  congr 1
  ext E
  constructor
  · rintro ⟨F, ⟨U, hU, rfl⟩, rfl⟩
    exact ⟨U, hU, rfl⟩
  · rintro ⟨U, hU, rfl⟩
    exact ⟨_, ⟨U, hU, rfl⟩, rfl⟩

/-- Mean-zero field observations commute with arbitrary pullbacks. -/
theorem comap_fieldSigma0On {X Ω : Type} (f : X → Ω) (h : Ω → DistC)
    (V : Set ℂ) :
    MeasurableSpace.comap f (fieldSigma0On h V) = fieldSigma0On (h ∘ f) V := by
  unfold fieldSigma0On
  rw [MeasurableSpace.comap_comp]
  rfl

/-- The mean-zero hull observation commutes with arbitrary pullbacks. -/
theorem comap_hullSigma0 {X Ω : Type} (f : X → Ω) (h : Ω → DistC)
    (A : Ω → Set ℂ) (n : ℕ) :
    MeasurableSpace.comap f (hullSigma0 h A n) = hullSigma0 (h ∘ f) (A ∘ f) n := by
  unfold hullSigma0
  rw [MeasurableSpace.comap_sup, comap_setSigma, MeasurableSpace.comap_generateFrom]
  congr 1
  apply congrArg MeasurableSpace.generateFrom
  ext E
  constructor
  · rintro ⟨G, ⟨S, F, hF, rfl⟩, rfl⟩
    refine ⟨S, f ⁻¹' F, ?_, ?_⟩
    · rw [← comap_fieldSigma0On]
      exact ⟨F, hF, rfl⟩
    · rfl
  · rintro ⟨S, F, hF, rfl⟩
    rw [← comap_fieldSigma0On] at hF
    obtain ⟨G, hG, rfl⟩ := hF
    refine ⟨{ω | dyadicHull n (A ω) = S} ∩ G, ⟨S, G, hG, rfl⟩, ?_⟩
    rfl

/-- The gated phase hull observation commutes with arbitrary pullbacks. -/
theorem comap_localHullFieldSigma {X Ω : Type} (f : X → Ω) (h : Ω → DistC)
    (A : Ω → Set ℂ) (n : ℕ) (a : TestC) {p : ℝ} (hp : 0 < p) :
    MeasurableSpace.comap f (localHullFieldSigma h A n a hp) =
      localHullFieldSigma (h ∘ f) (A ∘ f) n a hp := by
  unfold localHullFieldSigma
  rw [MeasurableSpace.comap_sup, comap_hullSigma0, MeasurableSpace.comap_comp]
  congr 1

/-- The compact collar code commutes with arbitrary pullbacks, gates included. -/
theorem collarFieldCode_comp {X Ω : Type} {I : Type*} (f : X → Ω)
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (φ : I → TestC)
    (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p) (k : ℕ) :
    collarFieldCode (h ∘ f) (K ∘ f) φ ψ hp k = collarFieldCode h K φ ψ hp k ∘ f := by
  classical
  funext x
  simp only [collarFieldCode, Function.comp_apply]
  congr 2

/-- The sigma algebra of a compact collar code commutes with pullback. -/
theorem comap_collarFieldCode {X Ω : Type} {I : Type*}
    [MeasurableSpace (NonemptyCompacts ℂ)] (f : X → Ω)
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (φ : I → TestC)
    (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p) (k : ℕ) :
    MeasurableSpace.comap f (MeasurableSpace.comap (collarFieldCode h K φ ψ hp k)
      inferInstance) = MeasurableSpace.comap (collarFieldCode (h ∘ f) (K ∘ f) φ ψ hp k)
        inferInstance := by
  rw [MeasurableSpace.comap_comp, collarFieldCode_comp]

end LatticeProb.LQG
