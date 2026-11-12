/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L9 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L8

/-!
# DZZ Corollary 3.9: the LGD at two values of `δ` (P2-DZZ3C, WP-113 part 3)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, Corollary 3.9 (`cor-LGD-two-deltas`,
l. 1235–1244): "follows immediately from Proposition 3.2 and Lemma 3.5".

* `IsXiAdmissibleAt ξ δ A B`: the conditions of a `ξ`-admissible pair at one value of `δ`
  (DZZ l. 791–797); `IsXiAdmissibleAt.mono`: admissible at `δ` ⇒ admissible at every `δ' ≤ δ`
  (`δ'^ξ ≤ δ^ξ`).
* `DZZProp32 P γ W μ ξ`: the statement of DZZ Proposition 3.2 (l. 807–812) for a family of
  measures `μ ω` (the LQG measure `M_γ` in DZZ), and `DZZLemma35 P γ W ξ`: the statement of DZZ
  Lemma 3.5 (l. 907–916). Both are hypotheses here (P3.2 is open, L3.5 is P2-DZZ3B's task).
* `DZZProp32.uniform`: the constant `c = c(γ, ξ)` of P3.2 is uniform in the sequence, hence a
  single `δ₀` works for all pairs admissible at `δ` (choice of a worst sequence).
* **`dzz_cor39`**: Corollary 3.9 with the factor that the cited proof gives:
  `min D_{δ'} ≤ min D_δ · (δ/δ')³ e^{(log δ⁻¹)^{0.9} + (log δ⁻¹)^{0.8} + (log δ'⁻¹)^{0.9}}`
  (P3.2 lower bound at `δ`, L3.5 from `δ` to `δ'`, P3.2 upper bound at `δ'`). DZZ state the factor
  `e^{(log δ⁻¹)^{0.9}} (δ/δ')³`, which the three cited bounds do not give (the three
  sub-exponential factors add up); DEVIATIONS entry proposed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- The conditions of a `ξ`-admissible pair at one value of `δ` (DZZ l. 791–797), with the
diameter exponent `ξd` separated from the location parameter `ξ` (DZZ: `ξd = ξ`). -/
structure IsXiAdmissibleAt (ξ ξd δ : ℝ) (A B : Set ℂ) : Prop where
  subset_left : A ⊆ dzzVXi ξ
  subset_right : B ⊆ dzzVXi ξ
  adm_left : IsXiAdmissibleSet ξd δ A
  adm_right : IsXiAdmissibleSet ξd δ B
  dist_ge : ∀ a ∈ A, ∀ b ∈ B, ξ ≤ dist a b

/-- Pairs `(A_δ, B_δ)` admissible at every `δ ∈ (0,1)`; for `ξd = ξ` these are DZZ's
`ξ`-admissible pairs (`isXiAdmissible_iff`). -/
def IsXiAdmissibleSeq (ξ ξd : ℝ) (A B : ℝ → Set ℂ) : Prop :=
  ∀ δ ∈ Ioo (0 : ℝ) 1, IsXiAdmissibleAt ξ ξd δ (A δ) (B δ)

lemma isXiAdmissible_iff {ξ : ℝ} {A B : ℝ → Set ℂ} :
    IsXiAdmissible ξ A B ↔ IsXiAdmissibleSeq ξ ξ A B :=
  ⟨fun h δ hδ => ⟨h.subset_left δ hδ, h.subset_right δ hδ, h.adm_left δ hδ, h.adm_right δ hδ,
    h.dist_ge δ hδ⟩, fun h => ⟨fun δ hδ => (h δ hδ).1, fun δ hδ => (h δ hδ).2,
    fun δ hδ => (h δ hδ).3, fun δ hδ => (h δ hδ).4, fun δ hδ => (h δ hδ).5⟩⟩

lemma IsXiAdmissibleSet.of_rpow_le {ξ₁ ξ₂ δ₁ δ₂ : ℝ} (h : δ₂ ^ ξ₂ ≤ δ₁ ^ ξ₁) {A : Set ℂ}
    (hA : IsXiAdmissibleSet ξ₁ δ₁ A) : IsXiAdmissibleSet ξ₂ δ₂ A := by
  rcases hA with hA | ⟨hc, hd⟩
  · exact Or.inl hA
  · exact Or.inr ⟨hc, h.trans hd⟩

lemma IsXiAdmissibleAt.of_rpow_le {ξ ξ₁ ξ₂ δ₁ δ₂ : ℝ} (h : δ₂ ^ ξ₂ ≤ δ₁ ^ ξ₁) {A B : Set ℂ}
    (hAB : IsXiAdmissibleAt ξ ξ₁ δ₁ A B) : IsXiAdmissibleAt ξ ξ₂ δ₂ A B :=
  ⟨hAB.1, hAB.2, hAB.3.of_rpow_le h, hAB.4.of_rpow_le h, hAB.5⟩

lemma IsXiAdmissibleAt.mono {ξ ξd δ δ' : ℝ} (hξ : 0 ≤ ξd) (hδ' : 0 ≤ δ') (h : δ' ≤ δ)
    {A B : Set ℂ} (hAB : IsXiAdmissibleAt ξ ξd δ A B) : IsXiAdmissibleAt ξ ξd δ' A B :=
  hAB.of_rpow_le (Real.rpow_le_rpow hδ' h hξ)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The event of DZZ Proposition 3.2 at `δ` for the sets `A, B`:
`min D' · e^{−(log δ⁻¹)^{0.9}} ≤ min D ≤ min D' · e^{(log δ⁻¹)^{0.9}}`. -/
def prop32Event (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (δ : ℝ) (A B : Set ℂ) :
    Set Ω :=
  {ω | ((approxLGDSet γ W δ A B ω : ℕ∞) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(Real.log δ⁻¹) ^ (0.9 : ℝ))) ≤
        ((lgdMinSet (μ ω) δ A B : ℕ∞) : ℝ≥0∞) ∧
      ((lgdMinSet (μ ω) δ A B : ℕ∞) : ℝ≥0∞) ≤
        ((approxLGDSet γ W δ A B ω : ℕ∞) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp ((Real.log δ⁻¹) ^ (0.9 : ℝ)))}

/-- The event (eq-280318) of DZZ Lemma 3.5 for `δ' < δ`. -/
def lem35Event (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ δ' : ℝ) (A B : Set ℂ) : Set Ω :=
  {ω | ((approxLGDSet γ W δ' A B ω : ℕ∞) : ℝ≥0∞) ≤
      ((approxLGDSet γ W δ A B ω : ℕ∞) : ℝ≥0∞) *
        ENNReal.ofReal ((δ / δ') ^ 3 * Real.exp ((Real.log δ⁻¹) ^ (0.8 : ℝ)))}

/-- The event of DZZ Corollary 3.9 with the factor given by its proof. -/
def cor39Event (μ : Ω → Measure ℂ) (δ δ' : ℝ) (A B : Set ℂ) : Set Ω :=
  {ω | ((lgdMinSet (μ ω) δ' A B : ℕ∞) : ℝ≥0∞) ≤ ((lgdMinSet (μ ω) δ A B : ℕ∞) : ℝ≥0∞) *
      ENNReal.ofReal ((δ / δ') ^ 3 * Real.exp ((Real.log δ⁻¹) ^ (0.9 : ℝ) +
        (Real.log δ⁻¹) ^ (0.8 : ℝ) + (Real.log δ'⁻¹) ^ (0.9 : ℝ)))}

/-- P3.2, uniform form: one `δ₀` for all pairs admissible at `δ`. -/
def DZZProp32U (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ)
    (ξ ξd : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ A B : Set ℂ,
    IsXiAdmissibleAt ξ ξd δ A B → P (prop32Event γ W μ δ A B)ᶜ ≤ ENNReal.ofReal (δ ^ c)

/-- L3.5, uniform form. -/
def DZZLemma35U (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (ξ ξd : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ δ' ∈ Ioo (0 : ℝ) δ,
    ∀ A B : Set ℂ, IsXiAdmissibleAt ξ ξd δ A B →
      P (lem35Event γ W δ δ' A B)ᶜ ≤ ENNReal.ofReal (δ ^ c)

variable {P : Measure Ω}

/-- The deterministic chain of the proof of Corollary 3.9 (l. 1242). -/
lemma cor39_chain {m m' n n' : ℝ≥0∞} {x y z r : ℝ} (hr : 0 ≤ r)
    (E1 : m' * ENNReal.ofReal (Real.exp (-x)) ≤ m) (E2 : n ≤ n' * ENNReal.ofReal (Real.exp z))
    (E3 : n' ≤ m' * ENNReal.ofReal (r * Real.exp y)) :
    n ≤ m * ENNReal.ofReal (r * Real.exp (x + y + z)) := by
  have hm' : m' ≤ m * ENNReal.ofReal (Real.exp x) := by
    calc m' = m' * ENNReal.ofReal (Real.exp (-x)) * ENNReal.ofReal (Real.exp x) := by
          rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
            neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, mul_one]
      _ ≤ m * ENNReal.ofReal (Real.exp x) := by gcongr
  calc n ≤ n' * ENNReal.ofReal (Real.exp z) := E2
    _ ≤ m' * ENNReal.ofReal (r * Real.exp y) * ENNReal.ofReal (Real.exp z) := by gcongr
    _ ≤ m * ENNReal.ofReal (Real.exp x) * ENNReal.ofReal (r * Real.exp y) *
          ENNReal.ofReal (Real.exp z) := by gcongr
    _ = m * ENNReal.ofReal (r * Real.exp (x + y + z)) := by
          rw [mul_assoc, mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), Real.exp_add, Real.exp_add]
          congr 2
          ring

end DZZ
end LQGMetric
