/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.BundleSec4.ZeroConeCase0 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.ZeroConeL46
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.Case0
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4FO.Final

/-!
# The named input `ZeroConeCase0At` from the lower-integral Case 0 and the 0-cone Proposition 4.5

The Proposition 4.10 argument (`GMS4FO/Final.lean`) proves `BundleSec4.Prop410At P η (3/4) 100`, hence both frozen mated-CRT map conclusions, from two named inputs for every frozen coupling: `GMS4FO.ZeroConeCase0At D (13/16)` ([18] (4.40)
for the 0-cone, in the `GlobalGood` form: windows `≤ ε^q` on `B_ρ(0)` AND the integral bound) and
`GMS4FO.Lemma43Measurable D`.

This file closes the first input from

* the window part of [18] Proposition 4.5 on the 0-cone, now unconditional (`BundleSec4.zeroCone_prop45_holds`, with
  the measurable Lemma 4.3 instance and the circle-average versions), and
* the integral part in the lower-integral carrier `BundleSec4.Prop48ZeroConeLintegral P η₀` (the
  Bochner-form Proposition 4.8 output converts to it by `BundleSec4.prop48ZeroConeLintegral_of_bochner`).

A test in the Proposition 4.10 argument `(D, g)` (`D` open, `g` continuous on `D` with `0 ≤ g ≤ M`) becomes the [18] (4.1) test pair
`(D, 1_D g)` (`bundle_prop48TestPairAdmissible_indicator`), whose sup norm is `≤ M`.

* **`zeroConeCase0At_of_lintegral`** — `Prop48ZeroConeLintegral P η₀ → ZeroConeCase0At D ρ` for every `ρ ∈ (0,1)`;
* `Case0LintegralForAllBundles` — the two remaining inputs, for every frozen coupling on a standard Borel space;
* `inputsForAllBundles_of_case0Lintegral`, `exists_cellModel_of_matingOfTrees_of_case0Lintegral`,
  **the companion map conclusion** — the `InputsForAllBundles` and both frozen v3
  conclusions of the mated-CRT map conclusion from them.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic

/-! ### Tests in the Proposition 4.10 argument as [18] (4.1) test pairs -/

/-- A test in the Proposition 4.10 argument (open `D ⊆ B_ρ(0)`, `g` continuous on `D`, `0 ≤ g ≤ M` on `D`) extended by zero is an admissible
[18] (4.1) test pair. -/
theorem bundle_prop48TestPairAdmissible_indicator {ρ : ℝ} {Dm : Set ℂ} {g : ℂ → ℝ} {M : ℝ}
    (hDo : IsOpen Dm) (hDsub : Dm ⊆ ball (0 : ℂ) ρ) (hgc : ContinuousOn g Dm)
    (hgb : ∀ z ∈ Dm, 0 ≤ g z ∧ g z ≤ M) :
    GMS4.Prop48TestPairAdmissible ρ Dm (Dm.indicator g) := by
  classical
  have hmeas : Measurable (Dm.indicator g) := by
    have h := ContinuousOn.measurable_piecewise hgc (continuous_zero.continuousOn (s := Dmᶜ))
      hDo.measurableSet
    rwa [Set.piecewise_eq_indicator] at h
  refine ⟨hDo.measurableSet, hDsub, hmeas.comp measurable_subtype_coe,
    fun z _ => Set.indicator_nonneg (fun w hw => (hgb w hw).1) z, ⟨max M 0, fun z _ => ?_⟩⟩
  by_cases hz : z ∈ Dm
  · rw [Set.indicator_of_mem hz, abs_of_nonneg (hgb z hz).1]
    exact le_max_of_le_left (hgb z hz).2
  · rw [Set.indicator_of_notMem hz, abs_zero]
    exact le_max_right _ _

/-- The [18] (4.1) sup norm of the extended test is at most `M` (for `M ≥ 0`). -/
theorem bundle_prop48TestSupNorm_indicator_le {ρ : ℝ} {Dm : Set ℂ} {g : ℂ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hgb : ∀ z ∈ Dm, 0 ≤ g z ∧ g z ≤ M) :
    GMS4.prop48TestSupNorm ρ (Dm.indicator g) ≤ M := by
  classical
  refine csSup_le (Set.insert_nonempty _ _) ?_
  rintro x (rfl | ⟨z, -, rfl⟩)
  · exact hM
  · by_cases hz : z ∈ Dm
    · simp only [Set.indicator_of_mem hz, abs_of_nonneg (hgb z hz).1]
      exact (hgb z hz).2
    · simp only [Set.indicator_of_notMem hz, abs_zero]
      exact hM

/-! ### The adapter -/

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- One mesh, one test: the Proposition 4.10 argument failure event is covered by the failure of the 0-cone Proposition 4.5 event
(windows) and the lower-integral Case 0 failure for the extended test. -/
theorem bundle_not_globalGood_subset {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) {ρ q ζ α α₀ A M : ℝ}
    (hα₀ : α₀ ≤ α) {Dm : Set ℂ} {g : ℂ → ℝ} (hDo : IsOpen Dm)
    (hgb : ∀ z ∈ Dm, 0 ≤ g z ∧ g z ≤ M) (H HIG : ℝ → ℂ → Ω → ℝ)
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    {ω | ¬ GMS4FO.GlobalGood (η₀ ω) ε Dm g A (ε ^ α₀ * M) (ball (0 : ℂ) ρ) (ε ^ q)} ⊆
      (GMS4b.prop45Event (GMS4b.l46tZeroConeCellModel D hγ) H HIG ε ρ q ζ)ᶜ ∪
        Prop410Bad η₀ ε Dm (Dm.indicator g) A (ε ^ α * GMS4.prop48TestSupNorm ρ (Dm.indicator g)) := by
  classical
  intro ω hω
  by_contra hcon
  have h45 : ω ∈ GMS4b.prop45Event (GMS4b.l46tZeroConeCellModel D hγ) H HIG ε ρ q ζ := by
    by_contra h
    exact hcon (Or.inl h)
  have hbad : ω ∉ Prop410Bad η₀ ε Dm (Dm.indicator g) A
      (ε ^ α * GMS4.prop48TestSupNorm ρ (Dm.indicator g)) := fun h => hcon (Or.inr h)
  apply hω
  refine ⟨fun z hz => (h45.1 z hz).1, ?_⟩
  rcases Dm.eq_empty_or_nonempty with hE | ⟨z₀, hz₀⟩
  · subst hE
    simp
  have hM : 0 ≤ M := (hgb z₀ hz₀).1.trans (hgb z₀ hz₀).2
  have hgood : (∫⁻ z in Dm, ENNReal.ofReal (Dm.indicator g z) * GMS4b.uStar ε (η₀ ω) z) ≤
      ENNReal.ofReal A * (∫⁻ z in Dm, ENNReal.ofReal (Dm.indicator g z)) +
        ENNReal.ofReal (ε ^ α * GMS4.prop48TestSupNorm ρ (Dm.indicator g)) := by
    by_contra h
    exact hbad h
  have hcongr1 : (∫⁻ z in Dm, ENNReal.ofReal (Dm.indicator g z) * GMS4b.uStar ε (η₀ ω) z) =
      ∫⁻ z in Dm, ENNReal.ofReal (g z) * GMS4b.uStar ε (η₀ ω) z :=
    setLIntegral_congr_fun hDo.measurableSet fun z hz => by
      simp only [Set.indicator_of_mem hz]
  have hcongr2 : (∫⁻ z in Dm, ENNReal.ofReal (Dm.indicator g z)) = ∫⁻ z in Dm, ENNReal.ofReal (g z) :=
    setLIntegral_congr_fun hDo.measurableSet fun z hz => by
      simp only [Set.indicator_of_mem hz]
  rw [hcongr1, hcongr2] at hgood
  refine hgood.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
  have hpow : ε ^ α ≤ ε ^ α₀ := Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2.le hα₀
  have hsup := bundle_prop48TestSupNorm_indicator_le (ρ := ρ) hM hgb
  have hsup0 : 0 ≤ GMS4.prop48TestSupNorm ρ (Dm.indicator g) :=
    bundle_prop48TestSupNorm_nonneg ⟨max M 0, fun z _ => by
      by_cases hz : z ∈ Dm
      · rw [Set.indicator_of_mem hz, abs_of_nonneg (hgb z hz).1]
        exact le_max_of_le_left (hgb z hz).2
      · rw [Set.indicator_of_notMem hz, abs_zero]
        exact le_max_right _ _⟩
  exact mul_le_mul hpow hsup hsup0 (Real.rpow_nonneg hε.1.le _)

/-- **the named input `ZeroConeCase0At D ρ` from the lower-integral Case 0** (and the unconditional 0-cone
Proposition 4.5 for the windows), for every `ρ ∈ (0, 1)`; window exponent `q = (2+γ)^{-2}`. -/
theorem zeroConeCase0At_of_lintegral
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (h48 : Prop48ZeroConeLintegral P η₀) :
    GMS4FO.ZeroConeCase0At D ρ := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨α, hα, h48⟩ := h48
  obtain ⟨A, hA, C, hC, hbd⟩ := h48 ρ hρ
  obtain ⟨H, HIG, -, -, -, h45⟩ := zeroCone_prop45_holds D hγ
  have hγ2 : 0 < (2 + γ) ^ 2 := by have := hγ.1; positivity
  set q : ℝ := 1 / (2 + γ) ^ 2 with hqdef
  have hq0 : 0 < q := by positivity
  have hq : q ∈ Ioo (0 : ℝ) (2 / (2 + γ) ^ 2) :=
    ⟨hq0, by rw [hqdef]; exact div_lt_div_of_pos_right (by norm_num) hγ2⟩
  have hζ : q / 8 ∈ Ioo (0 : ℝ) (q / 4) := ⟨by positivity, by linarith⟩
  obtain ⟨α', hα', C', hC'⟩ := h45 ρ hρ q hq (q / 8) hζ
  refine ⟨q, min α α', A, C + max C' 0, hq0, lt_min hα hα', hA.le,
    add_nonneg hC (le_max_right _ _), ?_⟩
  intro k hk Dm g M hDo hDsub hgc hgb
  have hε : CellFamily.mesh k ∈ Ioo (0 : ℝ) 1 := ⟨bundle_mesh_pos k, GMSLemma27.mesh_lt_one (by omega)⟩
  have hadm := bundle_prop48TestPairAdmissible_indicator (ρ := ρ) hDo hDsub hgc hgb
  have hsub := bundle_not_globalGood_subset hε (ρ := ρ) (q := q) (ζ := q / 8) (A := A)
    (min_le_left α α') hDo hgb H (fun r z ω => HIG r z ω + T ω) D hγ
  have hpow' : CellFamily.mesh k ^ α' ≤ CellFamily.mesh k ^ min α α' :=
    Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2.le (min_le_right _ _)
  have hpow : CellFamily.mesh k ^ α ≤ CellFamily.mesh k ^ min α α' :=
    Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2.le (min_le_left _ _)
  have hpos : 0 ≤ CellFamily.mesh k ^ α' := Real.rpow_nonneg hε.1.le _
  calc P {ω | ¬ GMS4FO.GlobalGood (η₀ ω) (CellFamily.mesh k) Dm g A (CellFamily.mesh k ^ min α α' * M)
          (ball (0 : ℂ) ρ) (CellFamily.mesh k ^ q)}
      ≤ P ((GMS4b.prop45Event (GMS4b.l46tZeroConeCellModel D hγ) H (fun r z ω => HIG r z ω + T ω)
            (CellFamily.mesh k) ρ q (q / 8))ᶜ ∪
          Prop410Bad η₀ (CellFamily.mesh k) Dm (Dm.indicator g) A
            (CellFamily.mesh k ^ α * GMS4.prop48TestSupNorm ρ (Dm.indicator g))) := measure_mono hsub
    _ ≤ ENNReal.ofReal (C' * CellFamily.mesh k ^ α') + ENNReal.ofReal (C * CellFamily.mesh k ^ α) :=
        (measure_union_le _ _).trans (add_le_add (hC' _ hε) (hbd _ hε Dm (Dm.indicator g) hadm))
    _ ≤ ENNReal.ofReal (max C' 0 * CellFamily.mesh k ^ min α α') +
          ENNReal.ofReal (C * CellFamily.mesh k ^ min α α') :=
        add_le_add (ENNReal.ofReal_le_ofReal
            ((mul_le_mul_of_nonneg_right (le_max_left C' 0) hpos).trans
              (mul_le_mul_of_nonneg_left hpow' (le_max_right _ _))))
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow hC))
    _ = ENNReal.ofReal ((C + max C' 0) * CellFamily.mesh k ^ min α α') := by
        rw [← ENNReal.ofReal_add (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hε.1.le _))
          (mul_nonneg hC (Real.rpow_nonneg hε.1.le _))]
        congr 1
        ring

end Bundle

/-! ### The mated-CRT map conclusion from the two remaining inputs -/

end MatedCRTHarmonic.BundleSec4
