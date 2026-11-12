/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43Out at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43CM

/-!
# GM Lemma 5.4 for the σ-algebra of `h|_{ℂ∖B_{3r}}` modulo constants (task P2-M2N, WP-M2n)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`.
GM's proof of Lemma 5.4 (l. 2801) normalizes the field ("the occurrence of the events `E_r` and
`𝔈_r` is unaffected by adding a constant to `h`, so we can assume without loss of generality that
`h` is normalized …"): for a whole-plane GFF defined modulo constants (`IsWholePlaneGFF` only
fixes the mean-zero pairings) the conditioning σ-algebra is that of `h|_{ℂ∖B_{3r}}` modulo
constants. Here:

* `fieldSigma0On h V` : the σ-algebra of the mean-zero pairings `⟨h, ψ⟩`, `supp ψ ⊆ V`;
  `fieldSigmaClosed0 h K := ⋂_{ε>0} fieldSigma0On h (B_ε(K))` (as `fieldSigmaClosed`, LM l. 164);
* `shiftInv_fieldSigmaClosed0` : its events are shift invariant for test functions `φ` with
  support at positive distance from `K` (GM: `φ` supported in `𝔸_{r/4,3r}(0)`, compactly);
* `condExp_le_cm_out` : GM Lemma 5.4 (abstract form, `condExp_le_cm`) for this σ-algebra.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace LQGMetric.GM

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

-- `fieldSigma0On`, `fieldSigmaClosed0` are defined in `Papers/GM/S3/SigmaMod.lean` (D79)

lemma fieldSigma0On_le (hh : IsWholePlaneGFF h P) (V : Set ℂ) : fieldSigma0On h V ≤ mΩ := by
  rw [fieldSigma0On, ← measurable_iff_comap_le]
  exact measurable_pi_iff.2 fun ψ => (measurable_evalDist ψ.1.1).comp hh.measurable

lemma fieldSigmaClosed0_le (hh : IsWholePlaneGFF h P) (K : Set ℂ) :
    fieldSigmaClosed0 h K ≤ mΩ :=
  (iInf₂_le (1 : ℝ) one_pos).trans (fieldSigma0On_le hh _)

/-- a finite family of test functions with supports at positive distance from `K` avoids a
common neighbourhood `B_ε(K)` -/
lemma exists_eps_disjoint_cm (K : Set ℂ) (G : Finset TestC)
    (hG : ∀ φ ∈ G, ∃ ε > 0, Disjoint (tsupport (φ : ℂ → ℝ)) (Metric.thickening ε K)) :
    ∃ ε > 0, ∀ φ ∈ G, Disjoint (tsupport (φ : ℂ → ℝ)) (Metric.thickening ε K) := by
  classical
  induction G using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun φ hφ => absurd hφ (Finset.notMem_empty φ)⟩
  | insert a s _ ih =>
    obtain ⟨ε₁, hε₁, h₁⟩ := ih fun φ hφ => hG φ (Finset.mem_insert_of_mem hφ)
    obtain ⟨ε₂, hε₂, h₂⟩ := hG a (Finset.mem_insert_self a s)
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun φ hφ => ?_⟩
    rcases Finset.mem_insert.1 hφ with rfl | hφ
    · exact h₂.mono_right (Metric.thickening_mono (min_le_right _ _) _)
    · exact (h₁ φ hφ).mono_right (Metric.thickening_mono (min_le_left _ _) _)

/-- pairings against test functions supported in `V` do not see `φ` supported off `V` -/
lemma pair0_subTest_of_disjoint (g : DistC) (φ : TestC) {V : Set ℂ}
    (hφ : Disjoint (tsupport (φ : ℂ → ℝ)) V) (ψ : TestC0) (hψ : tsupport (ψ.1 : ℂ → ℝ) ⊆ V) :
    pair0 (subTest g φ) ψ = pair0 g ψ := by
  rw [subTest_eq_addFun_neg_cm, pair0_addFun]
  have : ∀ x, ψ.1 x * testCont (-φ) x = 0 := by
    intro x
    by_cases hx : ψ.1 x = 0
    · rw [hx, zero_mul]
    · have hxV : x ∈ V := hψ (subset_tsupport _ hx)
      have hxφ : x ∉ tsupport (φ : ℂ → ℝ) := fun h' => Set.disjoint_left.1 hφ h' hxV
      have : (φ : ℂ → ℝ) x = 0 := image_eq_zero_of_notMem_tsupport hxφ
      show ψ.1 x * (-φ) x = 0
      have e : ((-φ : TestC) : ℂ → ℝ) x = -(φ : ℂ → ℝ) x := rfl
      rw [e, this, neg_zero, mul_zero]
  convert add_zero (pair0 g ψ) using 2
  exact integral_eq_zero_of_ae (Filter.Eventually.of_forall this)

/-- the events of `σ(h|_K)` modulo constants are invariant under `h ↦ h − φ`, `φ ∈ G`, when the
supports of `G` are at positive distance from `K` -/
theorem shiftInv_fieldSigmaClosed0 (K : Set ℂ) (G : Finset TestC)
    (hG : ∀ φ ∈ G, ∃ ε > 0, Disjoint (tsupport (φ : ℂ → ℝ)) (Metric.thickening ε K)) :
    ∀ B, MeasurableSet[fieldSigmaClosed0 h K] B → ∃ C : Set (TestC0 → ℝ), MeasurableSet C ∧
      B = (fun ω => pair0 (h ω)) ⁻¹' C ∧ ∀ φ ∈ G, ∀ g : DistC,
        (pair0 (subTest g φ) ∈ C ↔ pair0 g ∈ C) := by
  intro B hB
  obtain ⟨ε, hε, hεG⟩ := exists_eps_disjoint_cm K G hG
  have hB' : MeasurableSet[fieldSigma0On h (Metric.thickening ε K)] B := by
    have := (MeasurableSpace.measurableSet_iInf.1 hB) ε
    exact MeasurableSpace.measurableSet_iInf.1 this hε
  obtain ⟨C', hC', hC'e⟩ := hB'
  let proj : (TestC0 → ℝ) →
      ({ψ : TestC0 // tsupport (ψ.1 : ℂ → ℝ) ⊆ Metric.thickening ε K} → ℝ) :=
    fun ξ ψ => ξ ψ.1
  have hproj : Measurable proj := measurable_pi_iff.2 fun ψ => measurable_pi_apply ψ.1
  refine ⟨proj ⁻¹' C', hproj hC', ?_, fun φ hφ g => ?_⟩
  · rw [← hC'e]; rfl
  · have e : proj (pair0 (subTest g φ)) = proj (pair0 g) := by
      funext ψ
      exact pair0_subTest_of_disjoint g φ (hεG φ hφ) ψ.1 ψ.2
    show proj (pair0 (subTest g φ)) ∈ C' ↔ proj (pair0 g) ∈ C'
    rw [e]

/-- **GM Lemma 5.4** (abstract form, l. 2792–2835) conditioning on `h|_K` modulo constants: for a
finite family `G` of test functions supported at positive distance from `K` (GM: `K = ℂ∖B_{3r}`,
`supp φ` compact in `𝔸_{r/4,3r}`), a random `φc ∈ G` which is `σ(h|_K)`-measurable (GM: "`φ` is
determined by `h|_{ℂ∖B_{3r}}`"), (5.7) a.s. on `X` and `M ≤ Λ` on the target `C_T` (5.5):
`Λ⁻¹ P[X | h|_K] ≤ P[pair0 h ∈ C_T | h|_K]` a.s. -/
theorem condExp_le_cm_out (hh : IsWholePlaneGFF h P) (K : Set ℂ) (G : Finset TestC)
    (hG : ∀ φ ∈ G, ∃ ε > 0, Disjoint (tsupport (φ : ℂ → ℝ)) (Metric.thickening ε K))
    (φc : Ω → TestC) (hφcG : ∀ ω, φc ω ∈ G)
    (hφcm : ∀ φ ∈ G, MeasurableSet[fieldSigmaClosed0 h K] {ω | φc ω = φ})
    {CT : Set (TestC0 → ℝ)} (hCT : MeasurableSet CT) {Λ : ℝ} (hΛ0 : 0 < Λ)
    (hΛ : ∀ φ ∈ G, ∀ ξ ∈ CT, cmDensity (-φ) ξ ≤ Λ) {X : Set Ω} (hXm : MeasurableSet X)
    (hX : ∀ᵐ ω ∂P, ω ∈ X → pair0 (subTest (h ω) (φc ω)) ∈ CT) :
    (fun ω => Λ⁻¹ * (P[X.indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K]) ω) ≤ᵐ[P]
      P[{ω | pair0 (h ω) ∈ CT}.indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K] :=
  condExp_le_cm hh (fieldSigmaClosed0_le hh K) G φc hφcG hφcm
    (shiftInv_fieldSigmaClosed0 K G hG) hCT hΛ0 hΛ hXm hX

end LQGMetric.GM
