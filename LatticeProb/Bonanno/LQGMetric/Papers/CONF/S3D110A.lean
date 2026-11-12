/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D110A at commit fdb5cad; only the module paths of local imports are changed.
   Changed: docstring wording of the module and isHarmPart0_addConst_iff. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108A
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate3Norm
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEventRandom
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate2FiltA
import LatticeProb.Bonanno.LQGMetric.Field.HarmLocC

/-!
# D110: the random additive constant and the conditioning σ-algebras (adapters)

Source: CONF = Gwynne–Miller, arXiv:1905.00381, `literature/src/1905.00381/confluence-final.tex`:
`h` normalized (C:347), events unaffected by constants (C:1154), conditioning on `h|_{ℂ∖U}` with
`h` normalized away from `U` (C:1187); GM arXiv:1905.00383 l. 214, 1200–1205. Decision
`decisions/DEC-110.md`.

`IsWholePlaneGFF` allows a random additive constant, so `σ(h|_K)` (`fieldSigmaClosed`) and
`σ(A, h|_A)` (`localSigma`) can contain information about `h` inside `K`/`A` through the constant
(DEC-110 §1). This file provides the objects read modulo additive constants and the cheap
adapters:

* `IsHarmPart0`, `harmPart0`: the harmonic part of `h|_U` with the conditioning σ-algebra read
  modulo additive constants (`fieldSigmaClosed0 h Uᶜ`, D79), and `isHarmPart0_addConst_iff`: it
  is constant-covariant (`𝔥^{U}_{h+c} = 𝔥^U_h + c`). Since D110 P1 these are abbreviations of
  `Blueprint.IsHarmPart`, `Blueprint.harmPart` (which now condition on `fieldSigmaClosed0`); the
  raw form is `HarmLoc.IsHarmPartRaw`.
* invariance of the mod-constant σ-algebras under random constants (`fieldSigma0On_addConst`,
  `fieldSigmaClosed0_addConst`, `localSigma0_addConst`) and the inclusions into the raw ones
  (`fieldSigma0On_le_fieldSigma`, `fieldSigmaClosed0_le_fieldSigmaClosed`,
  `localSigma0_le_localSigma`, `filledBallSigmaAt0_le`).
* **inside normalization** (D79's far normalization, now with the normalizing test function `ψ₀`
  inside the conditioning region): for `normIn h ψ₀ := h − h(ψ₀)`,
  `fieldSigmaClosed (normIn h ψ₀) K = fieldSigmaClosed0 h K` (`supp ψ₀ ⊆ K`) and
  `localSigma (normIn h ψ₀) A = localSigma0 h A` (`supp ψ₀ ⊆ int A ω` for all `ω`). Hence
  every raw statement proved for an arbitrary `IsWholePlaneGFF` transfers to the mod-constant
  statement for `h` by applying it to `normIn h ψ₀` (also a whole-plane GFF, `isWholePlaneGFF_normIn`);
  `isHarmPart0_of_isHarmPart_normIn` is the instance for the harmonic part.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter TopologicalSpace Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint GM

section Sigma0Adapters
variable {Ω : Type} [MeasurableSpace Ω]

/-- mean-zero pairings are unchanged by a random additive constant -/
theorem fieldSigma0On_addConst (h : Ω → DistC) (c : Ω → ℝ) (V : Set ℂ) :
    fieldSigma0On (fun ω => addConst (h ω) (c ω)) V = fieldSigma0On h V := by
  unfold fieldSigma0On
  congr 1
  funext ω ψ
  rw [GFFInv.addConst_apply, ψ.1.2, zero_mul, add_zero]

theorem fieldSigmaClosed0_addConst (h : Ω → DistC) (c : Ω → ℝ) (K : Set ℂ) :
    fieldSigmaClosed0 (fun ω => addConst (h ω) (c ω)) K = fieldSigmaClosed0 h K := by
  unfold fieldSigmaClosed0
  simp_rw [fieldSigma0On_addConst]

omit [MeasurableSpace Ω] in
/-- `σ(h|_V mod constants) ⊆ σ(h|_V)` -/
theorem fieldSigma0On_le_fieldSigma (h : Ω → DistC) {V : Set ℂ} (hV : IsOpen V) :
    fieldSigma0On h V ≤ fieldSigma h (toOpens V hV) := by
  unfold fieldSigma0On
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  exact iSup_le fun ψ => MeasurableSpace.comap_comp.le.trans
    (measurable_iff_comap_le.1 (measurable_pair_fieldSigma h ψ.1.1 ψ.2))

theorem fieldSigmaClosed0_le_fieldSigmaClosed (h : Ω → DistC) (K : Set ℂ) :
    fieldSigmaClosed0 h K ≤ fieldSigmaClosed h K :=
  iInf_mono fun _ε => iInf_mono fun _ => fieldSigma0On_le_fieldSigma h isOpen_thickening

theorem hullSigma0_le_hullSigma (h : Ω → DistC) (A : Ω → Set ℂ) (n : ℕ) :
    hullSigma0 h A n ≤ hullSigma h A n := by
  unfold hullSigma0 hullSigma
  refine sup_le_sup_left (MeasurableSpace.generateFrom_mono ?_) _
  rintro E ⟨S, F, hF, rfl⟩
  exact ⟨S, F, fieldSigma0On_le_fieldSigma h isOpen_interior F hF, rfl⟩

theorem localSigma0_le_localSigma (h : Ω → DistC) (A : Ω → Set ℂ) :
    localSigma0 h A ≤ localSigma h A :=
  iInf_mono fun n => hullSigma0_le_hullSigma h A n

theorem filledBallSigmaAt0_le (D : DistC → ContMetric) (h : Ω → DistC) (z₀ : ℂ) (T : Ω → ℝ≥0∞) :
    filledBallSigmaAt0 D h z₀ T ≤ filledBallSigmaAt D h z₀ T :=
  localSigma0_le_localSigma h _

/-! ### Inside normalization -/

/-- the field normalized at the test function `ψ₀`: `h − h(ψ₀)` -/
def normIn (h : Ω → DistC) (ψ₀ : TestC) : Ω → DistC := fun ω => addConst (h ω) (-(h ω ψ₀))

theorem normIn_apply_psi (h : Ω → DistC) {ψ₀ : TestC} (hψ₀ : ∫ x, ψ₀ x = 1) (ω : Ω) :
    normIn h ψ₀ ω ψ₀ = 0 := by
  rw [normIn, GFFInv.addConst_apply, hψ₀, one_mul, add_neg_cancel]

theorem isWholePlaneGFF_normIn {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (ψ₀ : TestC) : IsWholePlaneGFF (normIn h ψ₀) P :=
  hh.addConst ((measurable_evalDist ψ₀).comp hh.measurable).neg

theorem fieldSigma0On_normIn (h : Ω → DistC) (ψ₀ : TestC) (V : Set ℂ) :
    fieldSigma0On (normIn h ψ₀) V = fieldSigma0On h V :=
  fieldSigma0On_addConst h _ V

/-- `σ((h − h(ψ₀))|_K) = σ(h|_K mod constants)` for `supp ψ₀ ⊆ K` (D79 (1), inside form) -/
theorem fieldSigmaClosed_normIn_eq (h : Ω → DistC) {ψ₀ : TestC} (hψ₀ : ∫ x, ψ₀ x = 1)
    {K : Set ℂ} (hK : tsupport (ψ₀ : ℂ → ℝ) ⊆ K) :
    fieldSigmaClosed (normIn h ψ₀) K = fieldSigmaClosed0 h K := by
  rw [fieldSigmaClosed_eq_fieldSigmaClosed0 hψ₀ (normIn_apply_psi h hψ₀) hK]
  exact fieldSigmaClosed0_addConst h _ K

end Sigma0Adapters

/-! ## The harmonic part modulo additive constants -/

section HarmPart0
variable {Ω : Type} [MeasurableSpace Ω]

/-- the mod-constant harmonic part (D110): since D110 P1 this is `Blueprint.IsHarmPart`
(conditioning on `fieldSigmaClosed0 h Uᶜ`; CONF l. 1138, C:347, 1187) -/
abbrev IsHarmPart0 (P : Measure Ω) (h : Ω → DistC) (U : Set ℂ) (H : Ω → ℂ → ℝ) : Prop :=
  IsHarmPart P h U H

/-- a chosen version of the mod-constant harmonic part: `Blueprint.harmPart` (D110 P1) -/
abbrev harmPart0 (P : Measure Ω) (h : Ω → DistC) (U : Set ℂ) : Ω → ℂ → ℝ :=
  harmPart P h U

theorem isHarmPart0_harmPart0 {P : Measure Ω} {h : Ω → DistC} {U : Set ℂ}
    (hex : ∃ H, IsHarmPart0 P h U H) : IsHarmPart0 P h U (harmPart0 P h U) := by
  unfold harmPart0 harmPart
  rw [dif_pos hex]
  exact hex.choose_spec

/-- a function harmonic on a neighbourhood of `U` times a test function supported in `U` is
integrable -/
theorem integrable_harm_mul_test {U : Set ℂ} {H : ℂ → ℝ}
    (hH : InnerProductSpace.HarmonicOnNhd H U) (φ : TestC) (hφ : tsupport (φ : ℂ → ℝ) ⊆ U) :
    Integrable fun x => H x * φ x := by
  have hc : Continuous fun x => H x * φ x := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    by_cases hx : x ∈ U
    · exact ((hH x hx).1.continuousAt).mul φ.continuous.continuousAt
    · have hx' : x ∉ tsupport (φ : ℂ → ℝ) := fun hx' => hx (hφ hx')
      have hev : ∀ᶠ y in 𝓝 x, H y * φ y = 0 := by
        filter_upwards [(isClosed_tsupport (φ : ℂ → ℝ)).isOpen_compl.mem_nhds hx'] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
      exact (continuousAt_const (y := (0 : ℝ))).congr (hev.mono fun y hy => hy.symm) |>.congr
        (Eventually.of_forall fun y => rfl)
  exact hc.integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left

/-- **the mod-constant harmonic part is constant-covariant**: `𝔥^U_{h+c} = 𝔥^U_h + c` for a random
constant `c` (CONF C:1187; DEC-110 §1) -/
theorem isHarmPart0_addConst_iff {P : Measure Ω} (h : Ω → DistC) (c : Ω → ℝ) (U : Set ℂ)
    (H : Ω → ℂ → ℝ) :
    IsHarmPart0 P (fun ω => addConst (h ω) (c ω)) U (fun ω x => H ω x + c ω) ↔
      IsHarmPart0 P h U H := by
  unfold IsHarmPart0 IsHarmPart
  rw [fieldSigmaClosed0_addConst]
  have e1 : ∀ ω, InnerProductSpace.HarmonicOnNhd (fun x => H ω x + c ω) U ↔
      InnerProductSpace.HarmonicOnNhd (H ω) U := by
    intro ω
    constructor
    · intro hH
      have e : H ω = fun x => (H ω x + c ω) + (-c ω) := by funext x; ring
      rw [e]
      exact hH.add (InnerProductSpace.harmonicOnNhd_const (s := U) (-c ω))
    · intro hH
      exact hH.add (InnerProductSpace.harmonicOnNhd_const (s := U) (c ω))
  have e2 : ∀ φ ψ : TestC, tsupport ⇑φ ⊆ U → ∫ x, ψ x = 1 →
      ((fun ω => addConst (h ω) (c ω) (φ - (∫ x, φ x) • ψ)) =
        fun ω => h ω (φ - (∫ x, φ x) • ψ)) ∧
      ((∀ ω, InnerProductSpace.HarmonicOnNhd (H ω) U) →
        (fun ω => (∫ x, (H ω x + c ω) * φ x) - (∫ x, φ x) * addConst (h ω) (c ω) ψ) =
          fun ω => (∫ x, H ω x * φ x) - (∫ x, φ x) * h ω ψ) := by
    intro φ ψ hφ hψ1
    have hint : ∫ x, (φ - (∫ x, φ x) • ψ) x = 0 := by
      have e : ((φ - (∫ x, φ x) • ψ : TestC) : ℂ → ℝ) = fun x => φ x - (∫ x, φ x) * ψ x := by
        ext x; simp
      rw [e, integral_sub (gm_integrable_testC φ) ((gm_integrable_testC ψ).const_mul _),
        integral_const_mul, hψ1, mul_one, sub_self]
    refine ⟨funext fun ω => ?_, fun hH => funext fun ω => ?_⟩
    · rw [GFFInv.addConst_apply, hint, zero_mul, add_zero]
    · rw [GFFInv.addConst_apply, hψ1, one_mul]
      have e : (fun x => (H ω x + c ω) * φ x) = fun x => H ω x * φ x + c ω * φ x := by
        ext x; ring
      rw [e, integral_add (integrable_harm_mul_test (hH ω) φ hφ)
        ((gm_integrable_testC φ).const_mul _), integral_const_mul]
      ring
  constructor
  · rintro ⟨hH, hc⟩
    have hH' : ∀ ω, InnerProductSpace.HarmonicOnNhd (H ω) U := fun ω => (e1 ω).1 (hH ω)
    refine ⟨hH', fun φ ψ hφ hψ hψ1 => ?_⟩
    have := hc φ ψ hφ hψ hψ1
    rwa [(e2 φ ψ hφ hψ1).1, (e2 φ ψ hφ hψ1).2 hH'] at this
  · rintro ⟨hH, hc⟩
    refine ⟨fun ω => (e1 ω).2 (hH ω), fun φ ψ hφ hψ hψ1 => ?_⟩
    rw [(e2 φ ψ hφ hψ1).1, (e2 φ ψ hφ hψ1).2 hH]
    exact hc φ ψ hφ hψ hψ1

end HarmPart0

end LQGMetric.CONF
