/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.EpsACase0 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.MesoModelFinal

/-!
# [18] (4.40) for the 0-quantum cone at every real mesh `ε ∈ (0, 1)`

G4FO's named input `GMS4FO.ZeroConeCase0At D ρ` (the zero-cone Case 0 of [18] Proposition 4.10, in G4FO's
`GlobalGood` form: windows `≤ ε^q` on `B_ρ(0)` and the integral bound) quantifies over the dyadic meshes `2^{-k}`,
`k ≥ 1`, only. Its producer `BundleSec4.zeroConeCase0At_of_lintegral` never uses dyadic-ness: both of its inputs, the
lower-integral Proposition 4.8 `BundleSec4.Prop48ZeroConeLintegral P η₀` and the unconditional zero-cone Proposition 4.5
`BundleSec4.zeroCone_prop45_holds`, are stated for every real `ε ∈ (0, 1)`, and the one-mesh event inclusion
`BundleSec4.bundle_not_globalGood_subset` takes any `ε ∈ (0, 1)`. The dyadic mesh entered only through
`GMSLemma27.mesh_lt_one`. This file states and proves the real-mesh form.

* `EpsAZeroConeCase0 D ρ` — `ZeroConeCase0At D ρ` with `∀ ε ∈ (0, 1)` in place of `∀ k ≥ 1, ε = 2^{-k}`;
* **`epsA_zeroConeCase0_of_lintegral`** — `Prop48ZeroConeLintegral P η₀ → EpsAZeroConeCase0 D ρ`, every `ρ ∈ (0, 1)`;
* **`epsA_zeroConeCase0_holds`** — the same with no premise (from the triple-centred zero-cone estimate);
* `epsA_zeroConeCase0At_of_real` — the real form gives G4FO's dyadic form.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain

open MatedCRTHarmonic

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **[18] (4.40) for the 0-cone at radius `ρ`, every real mesh** (G4FO's `GMS4FO.ZeroConeCase0At` with
`∀ ε ∈ (0, 1)` in place of the dyadic meshes `2^{-k}`, `k ≥ 1`). -/
def EpsAZeroConeCase0 (_D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (ρ : ℝ) : Prop :=
  ∃ q α₀ A₀ C₀ : ℝ, 0 < q ∧ 0 < α₀ ∧ 0 ≤ A₀ ∧ 0 ≤ C₀ ∧
    ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 → ∀ (Dm : Set ℂ) (g : ℂ → ℝ) (M : ℝ), IsOpen Dm → Dm ⊆ ball (0 : ℂ) ρ →
      ContinuousOn g Dm → (∀ z ∈ Dm, 0 ≤ g z ∧ g z ≤ M) →
        P {ω | ¬ GMS4FO.GlobalGood (η₀ ω) ε Dm g A₀ (ε ^ α₀ * M) (ball (0 : ℂ) ρ) (ε ^ q)} ≤
          ENNReal.ofReal (C₀ * ε ^ α₀)

/-- **The zero-cone Case 0 at every real mesh from the lower-integral Case 0** (and the unconditional 0-cone
Proposition 4.5 for the windows), for every `ρ ∈ (0, 1)`; window exponent `q = (2+γ)^{-2}`. The proof of
`BundleSec4.zeroConeCase0At_of_lintegral` with `ε` in place of `2^{-k}`. -/
theorem epsA_zeroConeCase0_of_lintegral
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (h48 : BundleSec4.Prop48ZeroConeLintegral P η₀) :
    EpsAZeroConeCase0 D ρ := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨α, hα, h48⟩ := h48
  obtain ⟨A, hA, C, hC, hbd⟩ := h48 ρ hρ
  obtain ⟨H, HIG, -, -, -, h45⟩ := BundleSec4.zeroCone_prop45_holds D hγ
  have hγ2 : 0 < (2 + γ) ^ 2 := by have := hγ.1; positivity
  set q : ℝ := 1 / (2 + γ) ^ 2 with hqdef
  have hq0 : 0 < q := by positivity
  have hq : q ∈ Ioo (0 : ℝ) (2 / (2 + γ) ^ 2) :=
    ⟨hq0, by rw [hqdef]; exact div_lt_div_of_pos_right (by norm_num) hγ2⟩
  have hζ : q / 8 ∈ Ioo (0 : ℝ) (q / 4) := ⟨by positivity, by linarith⟩
  obtain ⟨α', hα', C', hC'⟩ := h45 ρ hρ q hq (q / 8) hζ
  refine ⟨q, min α α', A, C + max C' 0, hq0, lt_min hα hα', hA.le,
    add_nonneg hC (le_max_right _ _), ?_⟩
  intro ε hε Dm g M hDo hDsub hgc hgb
  have hadm := BundleSec4.bundle_prop48TestPairAdmissible_indicator (ρ := ρ) hDo hDsub hgc hgb
  have hsub := BundleSec4.bundle_not_globalGood_subset hε (ρ := ρ) (q := q) (ζ := q / 8) (A := A)
    (min_le_left α α') hDo hgb H (fun r z ω => HIG r z ω + U ω) D hγ
  have hpow' : ε ^ α' ≤ ε ^ min α α' :=
    Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2.le (min_le_right _ _)
  have hpow : ε ^ α ≤ ε ^ min α α' :=
    Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2.le (min_le_left _ _)
  have hpos : 0 ≤ ε ^ α' := Real.rpow_nonneg hε.1.le _
  calc P {ω | ¬ GMS4FO.GlobalGood (η₀ ω) ε Dm g A (ε ^ min α α' * M) (ball (0 : ℂ) ρ) (ε ^ q)}
      ≤ P ((GMS4b.prop45Event (GMS4b.l46tZeroConeCellModel D hγ) H (fun r z ω => HIG r z ω + U ω)
            ε ρ q (q / 8))ᶜ ∪
          BundleSec4.Prop410Bad η₀ ε Dm (Dm.indicator g) A
            (ε ^ α * GMS4.prop48TestSupNorm ρ (Dm.indicator g))) := measure_mono hsub
    _ ≤ ENNReal.ofReal (C' * ε ^ α') + ENNReal.ofReal (C * ε ^ α) :=
        (measure_union_le _ _).trans (add_le_add (hC' _ hε) (hbd _ hε Dm (Dm.indicator g) hadm))
    _ ≤ ENNReal.ofReal (max C' 0 * ε ^ min α α') + ENNReal.ofReal (C * ε ^ min α α') :=
        add_le_add (ENNReal.ofReal_le_ofReal
            ((mul_le_mul_of_nonneg_right (le_max_left C' 0) hpos).trans
              (mul_le_mul_of_nonneg_left hpow' (le_max_right _ _))))
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow hC))
    _ = ENNReal.ofReal ((C + max C' 0) * ε ^ min α α') := by
        rw [← ENNReal.ofReal_add (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hε.1.le _))
          (mul_nonneg hC (Real.rpow_nonneg hε.1.le _))]
        congr 1
        ring

/-- **The zero-cone Case 0 at every real mesh and every radius, with no premise**: the lower-integral Case 0 from
The triple-centred estimate (`BundleSec4.h4TripleForAllBundles_holds`) through the bridge theorem
(`GMS4.Canonical.prop48ZeroConeLintegral_of_tripleH4`). -/
theorem epsA_zeroConeCase0_holds
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    EpsAZeroConeCase0 D ρ := by
  obtain ⟨q, ζ, hq, hζ, H4⟩ :=
    BundleSec4.h4TripleForAllBundles_holds γ hγ Ω inferInstance hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D
  exact epsA_zeroConeCase0_of_lintegral D hγ hρ
    (GMS4.Canonical.prop48ZeroConeLintegral_of_tripleH4 D hγ q ζ hq hζ H4)

end Bundle

end MatedCRTHarmonic.GMSMain
