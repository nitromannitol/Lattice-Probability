import LatticeProb.Prob.ContinuousPathStepTimes

/-!
# Successive displacement times of a time-changed path

If `φ : ℝ≥0 ≃o ℝ≥0` is an increasing bijection of the time axis, the successive displacement times
(`LatticeProb.stepTime`) of the time-changed path `g ∘ φ` are the images of those of `g` under `φ⁻¹`,
the value `⊤` being fixed.

* `LatticeProb.ennrealMap ψ`: the extension of `ψ : ℝ≥0 → ℝ≥0` to `ℝ≥0∞` with `⊤ ↦ ⊤`.
* `LatticeProb.stepTimeReparam_comp_orderIso`: `stepTime (g ∘ φ) r j = ennrealMap φ.symm (stepTime g r j)`.
* `LatticeProb.stepTimeReparam_comp_orderIso_eq_top_iff`, `LatticeProb.stepTimeReparam_comp_orderIso_of_eq_coe`,
  `LatticeProb.stepTimeReparam_comp_orderIso_toNNReal`: the same, for finite times.
* `LatticeProb.stepTime_eq_ennrealMap_comp_orderIso`: the converse formula
  `stepTime g r j = ennrealMap φ (stepTime (g ∘ φ) r j)`.
-/

open Set Filter Topology
open scoped NNReal ENNReal

namespace LatticeProb

section Reparam

/-- The extension of a self-map `ψ` of `ℝ≥0` to `ℝ≥0∞` by `ψ ⊤ = ⊤`. -/
def ennrealMap (ψ : ℝ≥0 → ℝ≥0) : ℝ≥0∞ → ℝ≥0∞ := WithTop.map ψ

@[simp] lemma ennrealMap_coe (ψ : ℝ≥0 → ℝ≥0) (a : ℝ≥0) :
    ennrealMap ψ (a : ℝ≥0∞) = ((ψ a : ℝ≥0) : ℝ≥0∞) := rfl

@[simp] lemma ennrealMap_top (ψ : ℝ≥0 → ℝ≥0) : ennrealMap ψ ⊤ = ⊤ := rfl

lemma ennrealMap_ennrealMap (ψ χ : ℝ≥0 → ℝ≥0) (x : ℝ≥0∞) :
    ennrealMap ψ (ennrealMap χ x) = ennrealMap (ψ ∘ χ) x := by
  induction x using ENNReal.recTopCoe <;> rfl

lemma ennrealMap_eq_top_iff {ψ : ℝ≥0 → ℝ≥0} {x : ℝ≥0∞} : ennrealMap ψ x = ⊤ ↔ x = ⊤ := by
  induction x using ENNReal.recTopCoe <;> simp

variable {E : Type*} [NormedAddCommGroup E]

/-- The displacement set of the time-changed path `g ∘ φ` at the time `a` is the image under `φ⁻¹`
of the displacement set of `g` at the time `φ a`. -/
lemma stepSetReparam_comp_orderIso (g : ℝ≥0 → E) (φ : ℝ≥0 ≃o ℝ≥0) (r : ℝ) (a : ℝ≥0) :
    stepSet (g ∘ φ) r a = φ.symm '' stepSet g r (φ a) := by
  ext t
  constructor
  · rintro ⟨hat, hr⟩
    exact ⟨φ t, ⟨φ.monotone hat, hr⟩, φ.symm_apply_apply t⟩
  · rintro ⟨u, ⟨hau, hr⟩, rfl⟩
    refine ⟨φ.le_symm_apply.2 hau, ?_⟩
    simpa using hr

/-- An increasing bijection of `ℝ≥0` commutes with the infimum of a nonempty set. -/
lemma orderIso_sInf (φ : ℝ≥0 ≃o ℝ≥0) {S : Set ℝ≥0} (hS : S.Nonempty) :
    sInf (φ.symm '' S) = φ.symm (sInf S) :=
  (φ.symm.isGLB_image'.2 (isGLB_csInf hS (OrderBot.bddBelow S))).csInf_eq (hS.image _)

/-- The first displacement time of the time-changed path `g ∘ φ` after `a` is the image under `φ⁻¹`
of the first displacement time of `g` after `φ a` (`⊤` being fixed). -/
lemma nextStepReparam_comp_orderIso (g : ℝ≥0 → E) (φ : ℝ≥0 ≃o ℝ≥0) (r : ℝ) (a : ℝ≥0) :
    nextStep (g ∘ φ) r a = ennrealMap φ.symm (nextStep g r (φ a)) := by
  by_cases hne : (stepSet g r (φ a)).Nonempty
  · have hne' : (stepSet (g ∘ φ) r a).Nonempty := by
      rw [stepSetReparam_comp_orderIso]
      exact hne.image _
    simp only [nextStep, hne, hne', ↓reduceIte]
    rw [stepSetReparam_comp_orderIso, orderIso_sInf φ hne]
    rfl
  · have hne' : ¬ (stepSet (g ∘ φ) r a).Nonempty := by
      rw [stepSetReparam_comp_orderIso]
      simpa using hne
    simp only [nextStep, hne, hne', ↓reduceIte]
    rfl

/-- **Successive displacement times under a change of time.**  For an increasing bijection `φ` of
`ℝ≥0`, `σ_j (g ∘ φ) = φ⁻¹ (σ_j g)` with `φ⁻¹ ⊤ = ⊤`. -/
theorem stepTimeReparam_comp_orderIso (g : ℝ≥0 → E) (φ : ℝ≥0 ≃o ℝ≥0) (r : ℝ) (j : ℕ) :
    stepTime (g ∘ φ) r j = ennrealMap φ.symm (stepTime g r j) := by
  induction j with
  | zero =>
    have h0 : (0 : ℝ≥0∞) = ((0 : ℝ≥0) : ℝ≥0∞) := rfl
    rw [stepTime_zero, stepTime_zero, h0, ennrealMap_coe, show φ.symm 0 = 0 from φ.symm.map_bot]
  | succ k ih =>
    by_cases hk : stepTime g r k = ⊤
    · rw [stepTime_succ_of_eq_top hk,
        stepTime_succ_of_eq_top (f := g ∘ φ) (by rw [ih, hk]; rfl)]
      rfl
    · have hk' : stepTime (g ∘ φ) r k ≠ ⊤ := by
        rw [ih]
        exact fun h => hk (ennrealMap_eq_top_iff.1 h)
      rw [stepTime_succ_of_ne_top hk, stepTime_succ_of_ne_top hk', ih,
        nextStepReparam_comp_orderIso]
      obtain ⟨b, hb⟩ : ∃ b : ℝ≥0, stepTime g r k = (b : ℝ≥0∞) :=
        ⟨_, (ENNReal.coe_toNNReal hk).symm⟩
      rw [hb]
      simp

/-- The displacement times of `g ∘ φ` are infinite exactly when those of `g` are. -/
theorem stepTimeReparam_comp_orderIso_eq_top_iff (g : ℝ≥0 → E) (φ : ℝ≥0 ≃o ℝ≥0) (r : ℝ) (j : ℕ) :
    stepTime (g ∘ φ) r j = ⊤ ↔ stepTime g r j = ⊤ := by
  rw [stepTimeReparam_comp_orderIso, ennrealMap_eq_top_iff]

/-- A finite displacement time of `g` at `b` gives the finite displacement time `φ⁻¹ b` of
`g ∘ φ`. -/
theorem stepTimeReparam_comp_orderIso_of_eq_coe (g : ℝ≥0 → E) (φ : ℝ≥0 ≃o ℝ≥0) (r : ℝ) (j : ℕ) {b : ℝ≥0}
    (h : stepTime g r j = (b : ℝ≥0∞)) : stepTime (g ∘ φ) r j = ((φ.symm b : ℝ≥0) : ℝ≥0∞) := by
  rw [stepTimeReparam_comp_orderIso, h, ennrealMap_coe]

/-- The finite parts of the displacement times of `g ∘ φ` and `g` correspond under `φ⁻¹`
(`toNNReal` sends `⊤` to `0` and `φ⁻¹ 0 = 0`). -/
theorem stepTimeReparam_comp_orderIso_toNNReal (g : ℝ≥0 → E) (φ : ℝ≥0 ≃o ℝ≥0) (r : ℝ) (j : ℕ) :
    (stepTime (g ∘ φ) r j).toNNReal = φ.symm (stepTime g r j).toNNReal := by
  by_cases h : stepTime g r j = ⊤
  · have h' : stepTime (g ∘ φ) r j = ⊤ := (stepTimeReparam_comp_orderIso_eq_top_iff g φ r j).2 h
    rw [h, h']
    simp [show φ.symm 0 = 0 from φ.symm.map_bot]
  · obtain ⟨b, hb⟩ : ∃ b : ℝ≥0, stepTime g r j = (b : ℝ≥0∞) :=
      ⟨_, (ENNReal.coe_toNNReal h).symm⟩
    rw [stepTimeReparam_comp_orderIso_of_eq_coe g φ r j hb, hb]
    simp

/-- The displacement times of `g` are the images under `φ` of those of `g ∘ φ`. -/
theorem stepTime_eq_ennrealMap_comp_orderIso (g : ℝ≥0 → E) (φ : ℝ≥0 ≃o ℝ≥0) (r : ℝ) (j : ℕ) :
    stepTime g r j = ennrealMap φ (stepTime (g ∘ φ) r j) := by
  rw [stepTimeReparam_comp_orderIso, ennrealMap_ennrealMap]
  induction h : stepTime g r j using ENNReal.recTopCoe with
  | top => rfl
  | coe a => simp

end Reparam

end LatticeProb
