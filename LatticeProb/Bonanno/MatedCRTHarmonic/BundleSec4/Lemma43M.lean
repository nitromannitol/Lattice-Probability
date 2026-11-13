/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.BundleSec4.Lemma43M at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4FO.Final
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.MesoModelInputs

/-!
# The restricted Lemma 4.3 measurability input `Lemma43MeasurableM`

`GMS4FO.Lemma43Measurable D` asks null-measurability of `GMS4FO.failSet γ V ε Dm g A tol R r` for ARBITRARY
`Dm : Set ℂ`, `g : ℂ → ℝ`, `R : Set ℂ` (for non-measurable data, sample measurability of the integrals in
`LocalGood` is unavailable). the Proposition 4.10 argument uses it at exactly two places (`GMS4FO.cone_le_case2`, γ-cone law, at the
translated test `((· − z₀) '' Dm, g (· + z₀), (· − z₀) '' R)`; `GMS4FO.case2_smallRoot_failSet_le`, 0-cone law), always
at admissible test data: `ε > 0` a dyadic mesh, `Dm` open with `Dm ⊆ R`, `g` continuous on `Dm` with
`0 ≤ g ≤ M` there, `A, tol ≥ 0`, `R` open, `r ≥ 0`, and the degree balls `B̄(z, 4r)`, `z ∈ R`, inside `V`.

* **`Lemma43MeasurableM D`** — the restricted statement, exactly these hypotheses (the required measurability statement);
  `lemma43MeasurableM_of_lemma43Measurable` (the unrestricted one implies it);
* `cone_le_case2M`, `case2_smallRoot_failSet_leM`, `prop410Bad_le_at_meshM`, **`prop410At_of_inputsM`** — the
  four `hL`-consuming theorems re-proved verbatim from `Lemma43MeasurableM` (the remaining steps are imported),
  the instance facts threaded through;
* `InputsMForAllBundles`, `prop410AtForAllBundles_of_inputsM`;
* **`TwoInputsMForAllBundles`** (H4 + `Lemma43MeasurableM`) ⇒ **the companion map conclusion**,
  `exists_cellModel_of_matingOfTrees_of_twoInputsM`; `twoInputsMForAllBundles_of_twoInputs`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4FO

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **[18] Lemma 4.3, measurable form, at admissible test data** (restriction of `GMS4FO.Lemma43Measurable`;
The measurability statement): for every open `V ⊆ 𝔻` and every admissible test (`ε > 0`; `Dm` open, `Dm ⊆ R`; `g`
continuous on `Dm`, `0 ≤ g ≤ M` on `Dm`; `A, tol ≥ 0`; `R` open; `r ≥ 0`; `B̄(z, 4r) ⊆ V` for `z ∈ R`), the local
failure set is null-measurable for the laws of the γ-cone and of the 0-cone local data `(h|_V, ηL)`. -/
def Lemma43MeasurableM (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) : Prop :=
  ∀ (V : Opens ℂ), (V : Set ℂ) ⊆ ball (0 : ℂ) 1 →
    ∀ (ε : ℝ) (Dm : Set ℂ) (g : ℂ → ℝ) (A tol : ℝ) (R : Set ℂ) (r : ℝ),
      0 < ε → IsOpen Dm → ContinuousOn g Dm → (∃ M : ℝ, ∀ z ∈ Dm, 0 ≤ g z ∧ g z ≤ M) →
      0 ≤ A → 0 ≤ tol → IsOpen R → Dm ⊆ R → 0 ≤ r → (∀ z ∈ R, closedBall z (4 * r) ⊆ V) →
        NullMeasurableSet (failSet γ V ε Dm g A tol R r)
            (P.map fun ω => (restrictTo V (coneField (X ω) (coneRadial γ γ (fun t => B t ω)
              (fun t => B' t ω))), ηL ω)) ∧
          NullMeasurableSet (failSet γ V ε Dm g A tol R r)
            (P.map fun ω => (restrictTo V (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω)
              (fun t => B₀' t ω))), ηL ω))

/-- `0 ≤ pairBd M j` for `M ≥ 0`. -/
theorem bundle_pairBd_nonneg {M : ℝ} (hM : 0 ≤ M) (j : Fin 3) : 0 ≤ pairBd M j := by
  fin_cases j <;> simp [pairBd, hM]

/-- **the per-root chain from `Lemma43MeasurableM`** (`GMS4FO.cone_le_case2` with the admissibility of the
test threaded through; the restricted input is applied at the translated test). -/
theorem cone_le_case2M (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) [Fact (0 < 2 * Real.pi * igChi γ)] (hL : Lemma43MeasurableM D)
    {r₀ r₁ : ℝ} (hr₁ : 0 < r₁) {z₀ : ℂ} (hz₀ : ‖z₀‖ + r₁ ≤ 1)
    (hr₀₁ : r₀ + ‖z₀‖ ≤ r₁) {ε : ℝ} (hε : 0 < ε) {Dm R : Set ℂ} {g : ℂ → ℝ} {A tol r : ℝ}
    (hr : 0 ≤ r) (hDR : Dm ⊆ R) (hRV : ∀ z ∈ R, closedBall z (4 * r) ⊆ ball (0 : ℂ) r₀)
    (hDo : IsOpen Dm) (hgc : ContinuousOn g Dm) (hgb : ∃ M : ℝ, ∀ z ∈ Dm, 0 ≤ g z ∧ g z ≤ M)
    (hA : 0 ≤ A) (htol : 0 ≤ tol) (hRo : IsOpen R) :
    P {ω | ¬ GlobalGood (η ω) ε ((fun z => z - z₀) '' Dm) (fun u => g (u + z₀)) A tol
        ((fun z => z - z₀) '' R) r} ≤
      P {ω | (restrictTo (ballO (0 : ℂ) r₀) (GMSCase1.wpField X₀ ω +
          CellScaling.ofFunC (fun w => -γ * Real.log ‖w - z₀‖)), ηL ω) ∈
        failSet γ (ballO (0 : ℂ) r₀) ε Dm g A tol R r} := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hD : MeasurableSet Dm := hDo.measurableSet
  have hVcball : (ballO (-z₀) r₀ : Set ℂ) ⊆ ball (0 : ℂ) r₁ := ball_neg_subset hr₀₁
  have hVc1 : (ballO (-z₀) r₀ : Set ℂ) ⊆ ball (0 : ℂ) 1 :=
    hVcball.trans (ball_subset_ball (by linarith [norm_nonneg z₀]))
  have hUV := mem_ball_neg_iff z₀ r₀
  -- the translated test is admissible
  have hRV' : ∀ z ∈ (fun z => z - z₀) '' R, closedBall z (4 * r) ⊆ (ballO (-z₀) r₀ : Set ℂ) := by
    rintro _ ⟨w, hw, rfl⟩ x hx
    have hx' : x + z₀ ∈ closedBall w (4 * r) := by
      rw [mem_closedBall, dist_eq_norm] at hx ⊢
      rwa [show x + z₀ - w = x - (w - z₀) by ring]
    exact (hUV x).2 (hRV w hw hx')
  have hgc' : ContinuousOn (fun u => g (u + z₀)) ((fun z => z - z₀) '' Dm) := by
    have hadd : Continuous fun u : ℂ => u + z₀ := continuous_id.add continuous_const
    refine hgc.comp hadd.continuousOn ?_
    rintro _ ⟨w, hw, rfl⟩
    simpa using hw
  have hgb' : ∃ M : ℝ, ∀ u ∈ (fun z => z - z₀) '' Dm, 0 ≤ g (u + z₀) ∧ g (u + z₀) ≤ M := by
    obtain ⟨M, hM⟩ := hgb
    refine ⟨M, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    simpa using hM w hw
  -- step 1: the γ-cone side, through the bridge
  have hstep1 : P {ω | ¬ GlobalGood (η ω) ε ((fun z => z - z₀) '' Dm) (fun u => g (u + z₀)) A tol
      ((fun z => z - z₀) '' R) r} ≤
      P {ω | (restrictTo (ballO (-z₀) r₀)
        (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))), ηL ω) ∈
          failSet γ (ballO (-z₀) r₀) ε ((fun z => z - z₀) '' Dm) (fun u => g (u + z₀)) A tol
            ((fun z => z - z₀) '' R) r} := by
    refine measure_mono_ae ?_
    filter_upwards [ae_bridge_cone D hγ] with ω hω hfail
    obtain ⟨μ, hμ, φ, hηφ, hbr⟩ := hω
    have hfail' : ¬ GlobalGood ((ηL ω) ∘ φ) ε ((fun z => z - z₀) '' Dm) (fun u => g (u + z₀)) A tol
        ((fun z => z - z₀) '' R) r := by
      rw [← hηφ]; exact hfail
    exact mem_failSet_of_globalFail hμ (hbr (ballO (-z₀) r₀) isBounded_ball) hε hr (image_mono hDR) hRV'
      (measurableSet_image_sub hD z₀) hfail'
  -- step 2: the restricted law
  have hπc : AEMeasurable (fun ω => (restrictTo (ballO (-z₀) r₀)
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))), ηL ω)) P :=
    ((measurable_restrictTo _).comp_aemeasurable (GMSCase.aemeasurable_coneField D hγ)).prodMk
      D.measurable_curves.1.aemeasurable
  have hπs : AEMeasurable (fun ω => (restrictTo (ballO (-z₀) r₀)
      (GMSCase.shiftedCase2Field γ (GMSCase1.wpField X₀ ω) z₀),
        MatedCRT.affineReroot z₀ 1 0 (ηL ω))) P := by
    have hc : Measurable fun ω => MatedCRT.affineReroot z₀ 1 0 (ηL ω) := by
      have hp : Measurable fun ω => ((z₀, ηL ω) : ℂ × C(ℝ, ℂ)) :=
        measurable_const.prodMk D.measurable_curves.1
      have e : Measurable ((fun p : ℂ × C(ℝ, ℂ) => GMSCase.caseCurve 1 p.1 p.2) ∘
          fun ω => ((z₀, ηL ω) : ℂ × C(ℝ, ℂ))) :=
        (GMSCase.measurable_caseCurve 1).comp hp
      exact e
    exact (measurable_shiftedField D _ z₀).aemeasurable.prodMk hc.aemeasurable
  have hmaps := map_cone_eq_shifted D hγ hr₁ hz₀ (V := ballO (-z₀) r₀) hVcball
  have hnull := (hL (ballO (-z₀) r₀) hVc1 ε ((fun z => z - z₀) '' Dm) (fun u => g (u + z₀)) A tol
    ((fun z => z - z₀) '' R) r hε (isOpen_image_sub hDo z₀) hgc' hgb' hA htol (isOpen_image_sub hRo z₀)
    (image_mono hDR) hr hRV').1
  have hstep2 := (Measure.map_apply₀ hπc hnull).symm.trans
    ((congrArg (fun m : Measure (DistOn (ballO (-z₀) r₀) × C(ℝ, ℂ)) => m _) hmaps).trans
      (Measure.map_apply₀ hπs (hmaps ▸ hnull)))
  -- step 3: recentring
  refine hstep1.trans (hstep2.le.trans (measure_mono_ae ?_))
  filter_upwards [D.spaceFilling] with ω hsf hmem
  have hfv : HasFirstVisits (ηL ω) := hasFirstVisits_of_surjective hsf.1 hsf.2.1
  have hmem' : (restrictTo (ballO (-z₀) r₀) (affineComp 1 z₀ (GMSCase1.wpField X₀ ω +
      CellScaling.ofFunC (fun w => -γ * Real.log ‖w - z₀‖))), MatedCRT.affineReroot z₀ 1 0 (ηL ω)) ∈
      failSet γ (ballO (-z₀) r₀) ε ((fun z => z - z₀) '' Dm) (fun u => g (u + z₀)) A tol
        ((fun z => z - z₀) '' R) r := by
    rw [GMSCase.affineComp_one_case2_eq]
    exact hmem
  have := mem_failSet_translate hUV hfv hmem'
  rw [image_add_image_sub, image_add_image_sub] at this
  simpa only [sub_add_cancel] using this

/-- **the Cases 0 → 1 → 2 on `failSet` from `Lemma43MeasurableM`** (`GMS4FO.case2_smallRoot_failSet_le` with
The admissibility of the test as hypotheses). -/
theorem case2_smallRoot_failSet_leM (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (hL : Lemma43MeasurableM D) {V₀ : Opens ℂ}
    (hV₀ : (V₀ : Set ℂ) ⊆ ball (0 : ℂ) 1) {ε : ℝ} {Dm R : Set ℂ} {g : ℂ → ℝ} {A tol r : ℝ}
    (hε : 0 < ε) (hDo : IsOpen Dm) (hgc : ContinuousOn g Dm) (hgb : ∃ M : ℝ, ∀ z ∈ Dm, 0 ≤ g z ∧ g z ≤ M)
    (hA : 0 ≤ A) (htol : 0 ≤ tol) (hRo : IsOpen R) (hDR : Dm ⊆ R) (hr : 0 ≤ r)
    (hRV : ∀ z ∈ R, closedBall z (4 * r) ⊆ V₀)
    {p q : ℝ} (hpq : p.HolderConjugate q) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) {δ : ℝ≥0∞}
    (hbad : P {ω | (restrictTo V₀ (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω)
        (fun t => B₀' t ω))), ηL ω) ∈ failSet γ V₀ ε Dm g A tol R r} ≤ δ) :
    (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω κ]
        {v : Ω × ℂ | (restrictTo V₀ (GMSCase1.wpField X₀ v.1 +
          CellScaling.ofFunC (fun w => -γ * Real.log ‖w - v.2‖)), ηL v.1) ∈
            failSet γ V₀ ε Dm g A tol R r} ≤
      GMSCase1.case1Moment D hγ p ^ (1 / p) * δ ^ (1 / q) / ENNReal.ofReal (κ ^ 2) := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  set F := failSet γ V₀ ε Dm g A tol R r with hF
  set G₀ : Set (DistOn V₀ × GMSCase1.AuxData) := {x | (x.1, x.2.2) ∈ F} with hG₀
  set π₀ : Ω → DistOn V₀ × GMSCase1.AuxData := fun ω =>
    GMSCase1.restrictData V₀ (GMSCase1.zeroConeData γ X₀ hIG₀ B₀ B₀' U ηL ω) with hπ₀
  have hπ₀m : AEMeasurable π₀ P :=
    (GMSCase1.measurable_restrictData V₀).comp_aemeasurable
      ((GMS4.aemeasurable_prop48ZeroConeField D).prodMk (GMSCase1.aemeasurable_wpAux D hγ))
  set G := toMeasurable (P.map π₀) G₀ with hG
  have hGm : MeasurableSet G := measurableSet_toMeasurable _ _
  have proj_m : Measurable fun x : DistOn V₀ × GMSCase1.AuxData => (x.1, x.2.2) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have hlaw : (P.map π₀).map (fun x : DistOn V₀ × GMSCase1.AuxData => (x.1, x.2.2)) =
      P.map fun ω => (restrictTo V₀ (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω)
        (fun t => B₀' t ω))), ηL ω) := by
    rw [AEMeasurable.map_map_of_aemeasurable proj_m.aemeasurable hπ₀m]
    rfl
  have hG₀null : NullMeasurableSet G₀ (P.map π₀) := by
    have h := (hL V₀ hV₀ ε Dm g A tol R r hε hDo hgc hgb hA htol hRo hDR hr hRV).2
    rw [← hlaw] at h
    exact h.preimage (proj_m.quasiMeasurePreserving _)
  have hV₀le : V₀ ≤ Blueprint.ballO (0 : ℂ) 1 := hV₀
  have hbad' : P ((fun ω => GMSCase1.restrictData V₀ (GMSCase1.wpData X₀ hIG₀ U ηL ω)) ⁻¹' G) ≤ δ := by
    rw [← GMSCase1.measure_restrictData_zeroConeData_preimage D hγ V₀ hV₀le hGm,
      ← Measure.map_apply_of_aemeasurable hπ₀m hGm, hG, measure_toMeasurable,
      Measure.map_apply₀ hπ₀m hG₀null]
    exact hbad
  refine le_trans (measure_mono_ae ?_) (GMSCase1.case2_smallRoot_local_event_le D hγ V₀ hV₀ hGm hpq hbad'
    hκ0 hκ1)
  have hac : (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω κ] ≪ Canon.rootedLaw P :=
    cond_absolutelyContinuous
  filter_upwards [hac.ae_le (GMSCase1.ae_case2Field_eq D)] with v hv hmem
  change GMSCase1.restrictData V₀ (GMSCase1.case2WPData γ X₀ hIG₀ U ηL v) ∈ G
  apply subset_toMeasurable
  change (restrictTo V₀ (Canon.case2Field γ (GMSCase1.wpField X₀ v.1) v.2),
    (GMSCase1.wpAux hIG₀ U ηL v.1).2) ∈ F
  rw [hv]
  exact hmem


end Coupling

/-! ### The mated-CRT map conclusion from the restricted input -/

end MatedCRTHarmonic.BundleSec4
