/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cM.Bundle at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cM.FailSet
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4FO.Assembly

/-!
# [18] Lemma 4.3, measurable form, on the frozen coupling

Source: [18], Lemma 4.3: "for each open `V ⊂ ℂ`,
`DA^ε(z) 1(B̄^ε_z ⊂ V)` is a.s. determined by `h|_V` and `η`".

**Main result** `lemma43MeasurableGuarded_holds`: for every frozen coupling `D` and `γ ∈ (0, 2)`, the local
failure set `failSet γ V ε D f A tol R r` is null-measurable under the laws of the γ-cone and 0-cone local data
`(h|_V, η_L)`, for every open `V ⊆ 𝔻` and all parameters with `0 < ε`, `0 ≤ r`, `D ⊆ R`, `B̄_{4r}(z) ⊆ V` for
`z ∈ R` ([18]'s condition `B̄^ε_z ⊂ V`), `D`, `R` Borel and `f` a.e.-measurable on `D`.

This is the named input `GMS4FO.Lemma43Measurable D` with these guards (: the text quantifies
over arbitrary sets `D, R`, arbitrary `f` and parameters violating `B̄_{4r}(z) ⊆ V`; for those the localized
quantities are not [18]'s and no measurability is claimed by the source). Every application in
`GMS4FO/{Assembly,Final}.lean` satisfies the guards; the restricted target `BundleSec4.Lemma43MeasurableM`
follows (`GMS4cM/BundleSec4Link.lean`).

Proof: almost surely the cone data have a witness of `GMS4cM.L43MRel` — the cone field itself (its dyadic
approximations converge vaguely and are eventually finite on `closure V`) and the area-time change `φ` of
`η = η_L ∘ φ`; the GMC area is the push-forward of Lebesgue measure under `η_L ∘ φ` (`eq_map_volume`). Hence
`l43mNoWitness` is null and `nullMeasurableSet_failSet` applies.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4cM

open MatedCRTHarmonic LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT GMS4FO

/-- **A witness from the bridge data of a field.** -/
theorem exists_l43mRel_of_bridge {γ : ℝ} {h : DistC} {μ : Measure ℂ}
    (hμ : CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ h) μ) {c : C(ℝ, ℂ)} {φ : ℝ ≃o ℝ}
    (hsurj : Function.Surjective c) (htr : Tendsto c (cocompact ℝ) (cocompact ℂ))
    {V : Opens ℂ} (hV1 : (V : Set ℂ) ⊆ ball (0 : ℂ) 1) (H : BridgeHyp μ c φ V)
    (hfin : ∀ᶠ k in atTop, CellScaling.lqgAreaApprox γ h k (closure (V : Set ℂ)) < ⊤) :
    ∃ w, L43MRel γ V (restrictTo V h, c) w := by
  let ψ : C(ℝ, ℝ) := ⟨φ, φ.continuous⟩
  have hsurjη : Function.Surjective (c.comp ψ) := hsurj.comp φ.surjective
  have harea : ∀ s t : ℝ, s ≤ t → μ ((c.comp ψ) '' Icc s t) = ENNReal.ofReal (t - s) :=
    fun s t hst => H.area s t hst
  have hμeq : μ = volume.map (c.comp ψ) := eq_map_volume (c.comp ψ).continuous hsurjη harea
  refine ⟨(h, ψ), rfl, ?_, ?_⟩
  · have hvl := GMS4FO.isVagueLimitOn_restrict_of_global hμ V
    rw [hμeq] at hvl
    exact cert_of_isVagueLimitOn V.isOpen hV1 hvl hfin
  · refine ⟨φ.strictMono, φ.surjective, htr, hsurj.denseRange, ?_⟩
    rw [← hμeq]
    exact harea

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- Almost surely the γ-cone local data have a witness. -/
theorem ae_exists_l43mRel_cone (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (V : Opens ℂ) (hV1 : (V : Set ℂ) ⊆ ball (0 : ℂ) 1) :
    ∀ᵐ ω ∂P, ∃ w, L43MRel γ V (restrictTo V (coneField (X ω) (coneRadial γ γ (fun t => B t ω)
      (fun t => B' t ω))), ηL ω) w := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hVb : Bornology.IsBounded (V : Set ℂ) := isBounded_ball.subset hV1
  filter_upwards [ae_bridge_cone D hγ, D.spaceFilling,
    GMS4c.ae_cone_areaApprox_finite_eventually hγ.1 hγ.2 (MesoModel.FrozenIdentities.lt_lqgQ hγ) D.gff D.bm_B
      D.bm_B' hVb.isCompact_closure] with ω hbr hsf hfin
  obtain ⟨μ, hμ, φ, -, hB⟩ := hbr
  exact exists_l43mRel_of_bridge hμ hsf.1 hsf.2.1 hV1 (hB V hVb) hfin

/-- Almost surely the 0-cone local data have a witness. -/
theorem ae_exists_l43mRel_zeroCone (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (V : Opens ℂ) (hV1 : (V : Set ℂ) ⊆ ball (0 : ℂ) 1) :
    ∀ᵐ ω ∂P, ∃ w, L43MRel γ V (restrictTo V (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω)
      (fun t => B₀' t ω))), ηL ω) w := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hVb : Bornology.IsBounded (V : Set ℂ) := isBounded_ball.subset hV1
  filter_upwards [ae_bridge_zeroCone D hγ, D.spaceFilling,
    GMS4c.ae_cone_areaApprox_finite_eventually hγ.1 hγ.2 (MesoModel.FrozenIdentities.lqgQ_pos hγ.1) D.gff₀
      D.bm_B₀ D.bm_B₀' hVb.isCompact_closure] with ω hbr hsf hfin
  obtain ⟨μ, hμ, φ, -, hB⟩ := hbr
  exact exists_l43mRel_of_bridge hμ hsf.1 hsf.2.1 hV1 (hB V hVb) hfin

/-- The no-witness set is null under the γ-cone law. -/
theorem map_l43mNoWitness_cone (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (V : Opens ℂ) (hV1 : (V : Set ℂ) ⊆ ball (0 : ℂ) 1) :
    (P.map fun ω => (restrictTo V (coneField (X ω) (coneRadial γ γ (fun t => B t ω)
      (fun t => B' t ω))), ηL ω)) (l43mNoWitness γ V) = 0 := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hF : AEMeasurable (fun ω => (restrictTo V (coneField (X ω) (coneRadial γ γ (fun t => B t ω)
      (fun t => B' t ω))), ηL ω)) P :=
    ((measurable_restrictTo _).comp_aemeasurable (GMSCase.aemeasurable_coneField D hγ)).prodMk
      D.measurable_curves.1.aemeasurable
  rw [Measure.map_apply₀ hF ((um_l43mNoWitness γ V).nullMeasurableSet _)]
  exact ae_iff.1 (ae_exists_l43mRel_cone D hγ V hV1)

/-- The no-witness set is null under the 0-cone law. -/
theorem map_l43mNoWitness_zeroCone
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (V : Opens ℂ) (hV1 : (V : Set ℂ) ⊆ ball (0 : ℂ) 1) :
    (P.map fun ω => (restrictTo V (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω)
      (fun t => B₀' t ω))), ηL ω)) (l43mNoWitness γ V) = 0 := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hF : AEMeasurable (fun ω => (restrictTo V (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω)
      (fun t => B₀' t ω))), ηL ω)) P :=
    ((measurable_restrictTo _).comp_aemeasurable (GMS4.aemeasurable_prop48ZeroConeField D)).prodMk
      D.measurable_curves.1.aemeasurable
  rw [Measure.map_apply₀ hF ((um_l43mNoWitness γ V).nullMeasurableSet _)]
  exact ae_iff.1 (ae_exists_l43mRel_zeroCone D hγ V hV1)

/-- **[18] Lemma 4.3, measurable form, with [18]'s guards**: the `Lemma43Measurable D` for open
`V ⊆ 𝔻`, `0 < ε`, `0 ≤ r`, `D ⊆ R`, `B̄_{4r}(z) ⊆ V` on `R`, Borel `D`, `R` and a.e.-measurable `f` on `D`. -/
def Lemma43MeasurableGuarded (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    Prop :=
  ∀ (V : Opens ℂ), (V : Set ℂ) ⊆ ball (0 : ℂ) 1 →
    ∀ (ε : ℝ) (Dm : Set ℂ) (g : ℂ → ℝ) (A tol : ℝ) (R : Set ℂ) (r : ℝ),
      0 < ε → 0 ≤ r → Dm ⊆ R → (∀ z ∈ R, closedBall z (4 * r) ⊆ V) → MeasurableSet Dm →
        MeasurableSet R → AEMeasurable g (volume.restrict Dm) →
      NullMeasurableSet (failSet γ V ε Dm g A tol R r)
          (P.map fun ω => (restrictTo V (coneField (X ω) (coneRadial γ γ (fun t => B t ω)
            (fun t => B' t ω))), ηL ω)) ∧
        NullMeasurableSet (failSet γ V ε Dm g A tol R r)
          (P.map fun ω => (restrictTo V (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω)
            (fun t => B₀' t ω))), ηL ω))

/-- **[18] Lemma 4.3, measurable form, holds on every frozen coupling.** -/
theorem lemma43MeasurableGuarded_holds
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    Lemma43MeasurableGuarded D := by
  intro V hV1 ε Dm g A tol R r hε hr hDR hRV hD hR hg
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  exact ⟨nullMeasurableSet_failSet hV1 (map_l43mNoWitness_cone D hγ V hV1) hε hr hDR hRV hD hR hg,
    nullMeasurableSet_failSet hV1 (map_l43mNoWitness_zeroCone D hγ V hV1) hε hr hDR hRV hD hR hg⟩

end Coupling

end MatedCRTHarmonic.GMS4cM
