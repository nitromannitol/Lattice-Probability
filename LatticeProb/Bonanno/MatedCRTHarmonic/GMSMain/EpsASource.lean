/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.EpsASource at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsAProp45U
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsAProp210

/-!
# [18] Propositions 4.10 and 2.10 in the source's quantifier order, every real mesh

Source: [18] Proposition 2.10 : "There exists `α = α(γ) > 0` and
`β = β(γ) > 0`, and `A = A(ρ, γ) > 0` such that … Let `C > 1` … with the rate of the `O_ε(ε^α)` depending only on
`C, ρ, γ`" — the order `∃ α β, ∀ ρ, ∃ A, ∀ C > 1, ∃ Cfail, ∀ ε ∈ (0, 1), ∀ (D, f)`. Proposition 4.10
is the same statement with `u_*^ε`.

The fixed-parameter forms (`EpsAProp410At`, `EpsAProp210At`) have exponents `β = α = α₀/(16 p′)` where `p` depends
on `γ` only and `α₀` is the zero-cone Case 0 exponent. `α₀ = min(α_{4.8}, α_{4.5})`: `Prop48ZeroConeLintegral` has its exponent before `ρ`, and `epsA_zeroCone_prop45_uniform` gives Proposition 4.5's
exponent before `ρ`. So the exponents are uniform in `ρ` and in `C`, and the source order holds. `A = A₀(ρ + (1−ρ)/8)`
is the Proposition 4.8 threshold at the enlarged radius, independent of `C`.

* `EpsAZeroConeCase0Uniform`, **`epsA_zeroConeCase0Uniform_holds`** — Case 0 with `∃ q α₀, ∀ ρ, ∃ A₀ > 0, C₀`;
* **`EpsAProp410Source P η`**, **`epsA_prop410Source`** — [18] Proposition 4.10, source order, every real mesh;
* **`EpsAProp210Source P bm η`**, **`epsA_prop210Source`** — [18] Proposition 2.10, source order, every real mesh,
  on the mated-CRT map of every frozen coupling;
* `epsA_bundle_prop410Source`, `epsA_bundle_prop210Source` — the dyadic source-order statements
  `BundleSec4.Prop410Source P η` and `BundleSec4.Prop210Source` (MTC's family) as corollaries.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain

open MatedCRTHarmonic

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **[18] (4.40) for the 0-cone at every real mesh, exponents uniform in the radius**: `∃ q, α₀`, then for each
`ρ ∈ (0, 1)` a threshold `A₀ > 0` and a rate `C₀`. -/
def EpsAZeroConeCase0Uniform (_D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    Prop :=
  ∃ q α₀ : ℝ, 0 < q ∧ 0 < α₀ ∧ ∀ ρ : ℝ, ρ ∈ Ioo (0 : ℝ) 1 → ∃ A₀ C₀ : ℝ, 0 < A₀ ∧ 0 ≤ C₀ ∧
    ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 → ∀ (Dm : Set ℂ) (g : ℂ → ℝ) (M : ℝ), IsOpen Dm → Dm ⊆ ball (0 : ℂ) ρ →
      ContinuousOn g Dm → (∀ z ∈ Dm, 0 ≤ g z ∧ g z ≤ M) →
        P {ω | ¬ GMS4FO.GlobalGood (η₀ ω) ε Dm g A₀ (ε ^ α₀ * M) (ball (0 : ℂ) ρ) (ε ^ q)} ≤
          ENNReal.ofReal (C₀ * ε ^ α₀)

/-- **The zero-cone Case 0 with radius-uniform exponents, from the lower-integral Case 0** (and the uniform 0-cone
Proposition 4.5 `epsA_zeroCone_prop45_uniform`); window exponent `q = (2+γ)^{-2}`, `ζ = q/8`. -/
theorem epsA_zeroConeCase0Uniform_of_lintegral
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (h48 : BundleSec4.Prop48ZeroConeLintegral P η₀) :
    EpsAZeroConeCase0Uniform D := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨α, hα, h48⟩ := h48
  obtain ⟨H, HIG, h45⟩ := epsA_zeroCone_prop45_uniform D hγ
  have hγ2 : 0 < (2 + γ) ^ 2 := by have := hγ.1; positivity
  set q : ℝ := 1 / (2 + γ) ^ 2 with hqdef
  have hq0 : 0 < q := by positivity
  have hq : q ∈ Ioo (0 : ℝ) (2 / (2 + γ) ^ 2) :=
    ⟨hq0, by rw [hqdef]; exact div_lt_div_of_pos_right (by norm_num) hγ2⟩
  have hζ : q / 8 ∈ Ioo (0 : ℝ) (q / 4) := ⟨by positivity, by linarith⟩
  obtain ⟨α', hα', h45⟩ := h45 q hq (q / 8) hζ
  refine ⟨q, min α α', hq0, lt_min hα hα', fun ρ hρ => ?_⟩
  obtain ⟨A, hA, C, hC, hbd⟩ := h48 ρ hρ
  obtain ⟨C', hC'⟩ := h45 ρ hρ
  refine ⟨A, C + max C' 0, hA, add_nonneg hC (le_max_right _ _), ?_⟩
  intro ε hε Dm g M hDo hDsub hgc hgb
  have hadm := BundleSec4.bundle_prop48TestPairAdmissible_indicator (ρ := ρ) hDo hDsub hgc hgb
  have hsub := BundleSec4.bundle_not_globalGood_subset hε (ρ := ρ) (q := q) (ζ := q / 8) (A := A)
    (min_le_left α α') hDo hgb H HIG D hγ
  have hpow' : ε ^ α' ≤ ε ^ min α α' :=
    Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2.le (min_le_right _ _)
  have hpow : ε ^ α ≤ ε ^ min α α' :=
    Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2.le (min_le_left _ _)
  have hpos : 0 ≤ ε ^ α' := Real.rpow_nonneg hε.1.le _
  calc P {ω | ¬ GMS4FO.GlobalGood (η₀ ω) ε Dm g A (ε ^ min α α' * M) (ball (0 : ℂ) ρ) (ε ^ q)}
      ≤ P ((GMS4b.prop45Event (GMS4b.l46tZeroConeCellModel D hγ) H HIG ε ρ q (q / 8))ᶜ ∪
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

/-- **The radius-uniform zero-cone Case 0 at every real mesh, with no premise.** -/
theorem epsA_zeroConeCase0Uniform_holds
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) : EpsAZeroConeCase0Uniform D := by
  obtain ⟨q, ζ, hq, hζ, H4⟩ :=
    BundleSec4.h4TripleForAllBundles_holds γ hγ Ω inferInstance hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D
  exact epsA_zeroConeCase0Uniform_of_lintegral D hγ
    (GMS4.Canonical.prop48ZeroConeLintegral_of_tripleH4 D hγ q ζ hq hζ H4)

end Bundle

/-! ### The source-order statements -/

/-- **[18] Proposition 4.10 in the source's quantifier order at every real mesh** for the area-parametrized curve
`η`: `∃ α > 0, β > 0, ∀ ρ ∈ (0, 1), ∃ A > 0, ∀ C > 1, ∃ Cfail ≥ 0`, for every `ε ∈ (0, 1)` and every pair `(V, f)`
admissible at `(ε, ρ, C, β)`, the failure of `∫⁻_V f u_*^ε ≤ A ∫⁻_V f + ε^α` has outer probability `≤ Cfail ε^α`
(`BundleSec4.Prop410Source` with `∀ ε ∈ (0, 1)` in place of the dyadic meshes). -/
def EpsAProp410Source {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (η : Ω → C(ℝ, ℂ)) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ A : ℝ, 0 < A ∧
      ∀ C : ℝ, 1 < C → ∃ Cfail : ℝ, 0 ≤ Cfail ∧
        ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 → ∀ (V : Set ℂ) (f : ℂ → ℝ), GMS4.Prop210Admissible ε ρ C β V f →
          P (BundleSec4.Prop410Bad η ε V f A (ε ^ α)) ≤ ENNReal.ofReal (Cfail * ε ^ α)

/-- **[18] Proposition 2.10 in the source's quantifier order at every real mesh** for the mated-CRT maps
`MatedCRT.graph ε (bm ·)` with the cells of `η` (failure event `EpsAProp210Bad`: an embedding with the curve cells
exists and every such embedding satisfies G3's `Prop210Bound`). -/
def EpsAProp210Source {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (bm : Ω → MatedCRT.Path2)
    (η : Ω → C(ℝ, ℂ)) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ A : ℝ, 0 < A ∧
      ∀ C : ℝ, 1 < C → ∃ Cfail : ℝ, 0 ≤ Cfail ∧
        ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 → ∀ (V : Set ℂ) (f : ℂ → ℝ), GMS4.Prop210Admissible ε ρ C β V f →
          P (EpsAProp210Bad bm η ε V f A (ε ^ α)) ≤ ENNReal.ofReal (Cfail * ε ^ α)

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **[18] Proposition 4.10, source order, every real mesh, from the radius-uniform zero-cone Case 0 and
`Lemma43MeasurableM`**: `α = β = α₀/(16 p′)` (`p ∈ (1, 4/γ²)` fixed by `γ`), `A = A₀(ρ + (1−ρ)/8)`. -/
theorem epsA_prop410Source_of_inputs (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (h0 : EpsAZeroConeCase0Uniform D) (hL : BundleSec4.Lemma43MeasurableM D) :
    EpsAProp410Source P η := by
  obtain ⟨q, α₀, hq, hα₀, h0⟩ := h0
  obtain ⟨p, hp1, hp4⟩ := GMSCase1.exists_case1_exponent hγ
  have hq' : 0 < p.conjExponent := (Real.HolderConjugate.conjExponent hp1).symm.pos
  refine ⟨α₀ / (4 * p.conjExponent) / 4, by positivity, α₀ / (4 * p.conjExponent) / 4, by positivity,
    fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨A₀, C₀, hA₀, hC₀, h0ρ⟩ := h0 (ρ + (1 - ρ) / 8) ⟨by linarith, by linarith⟩
  refine ⟨A₀, hA₀, fun C hC => ?_⟩
  obtain ⟨Cfail, hCfail, h⟩ :=
    epsA_prop410_explicit D hγ hρ0 hρ1 hq hα₀ hA₀.le hC₀ h0ρ hL hp1 hp4 hC
  exact ⟨Cfail, hCfail, fun ε _ => h ε⟩

/-- **[18] Proposition 4.10 in the source's quantifier order, at every real mesh `ε ∈ (0, 1)`, for the bundle's
γ-cone curve of every frozen coupling on a standard Borel space** (no premise). -/
theorem epsA_prop410Source (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) : EpsAProp410Source P η :=
  epsA_prop410Source_of_inputs D hγ (epsA_zeroConeCase0Uniform_holds D hstd hγ)
    (GMS4cM.lemma43MeasurableM_holds D hγ)

/-- **[18] Proposition 2.10 from Proposition 4.10 and (4.20), source order, every real mesh**: exponent `α/2`,
the same `β`, threshold `2A`, rate `Cfail + 2`. -/
theorem epsA_prop210Source_of_prop410Source
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (h : EpsAProp410Source P η) : EpsAProp210Source P bm η := by
  obtain ⟨α, hα, β, hβ, h⟩ := h
  refine ⟨α / 2, by positivity, β, hβ, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨A, hA, hCh⟩ := h ρ hρ0 hρ1
  refine ⟨2 * A, by positivity, fun C hC => ?_⟩
  obtain ⟨Cfail, hCfail, hbound⟩ := hCh C hC
  exact ⟨Cfail + 2, by positivity, fun ε hε V f hadm =>
    epsA_prop210Bad_le_of_prop410Bad D hε hadm.2.2.2.2.2.2.1.measurableSet hα hCfail (hbound ε hε V f hadm)⟩

/-- **[18] Proposition 2.10 in the source's quantifier order, at every real mesh `ε ∈ (0, 1)`, for the mated-CRT
map of every frozen coupling on a standard Borel space** (no premise): `∃ α(γ), β(γ) > 0, ∀ ρ ∈ (0, 1),
∃ A(ρ, γ) > 0, ∀ C > 1, ∃ Cfail(ρ, C, γ)`, for every `ε ∈ (0, 1)` and every admissible `(V, f)`,
`P (EpsAProp210Bad bm η ε V f A ε^α) ≤ Cfail ε^α`. -/
theorem epsA_prop210Source (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) : EpsAProp210Source P bm η :=
  epsA_prop210Source_of_prop410Source D (epsA_prop410Source D hstd hγ)

end Coupling

end MatedCRTHarmonic.GMSMain
