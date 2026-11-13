/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.Theorem44 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.DegOutMeasurable

/-!
# [18] Theorem 4.4: ε-independent moments of the localized quantities

Source: [18] Theorem 4.4 : for the circle-average embedding `h` of a
`0`-quantum cone and the space-filling SLE `η` parametrized by `μ_h`-mass with `η(0) = 0`,
`E[DA^ε(0)^p] ≍ 1` (`p ≥ 1`), `E[deg^ε_in(0)^p] ≍ 1` (`p ∈ [1, 4/γ²)`), `E[deg^ε_out(0)^p] ≍ 1` (`p ≥ 1`), with
constants depending only on `p`.

Proof (as in the source): the case `ε = 1` is [20] Propositions 4.4 and 4.6 (the bundle field
`cellMoments`, here `UnitCellMoments`). For general `ε`, `η^ε(t) := η(εt)/R_ε` has the law of `η`
(`CurveScaleInvariant`, `[18]`), and the localized quantities of `η` at mesh `ε` are those of `η^ε` at mesh `1`
(`locDA_affine` etc., "the definitions … are unaffected by spatial scaling"). They are Borel functions of the curve
(`measurable_locDA`, `measurable_locDegIn`, `measurable_locDegOut`), so their joint law does not depend on `ε`
(`theorem44_law_holds`) and the moments at mesh `ε` equal those at mesh `1` (`theorem44_holds`).

The quantities are taken at root time `0`; [18] uses `τ_0 = inf {t : η(t) = 0}`, which is `0` almost surely
(`theorem44_hitTime_holds` under `RootHitOnce`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4b

/-! ## The rescaled curve -/

/-- `η^ε(t) = R⁻¹ η(εt)` (`[18]`, with `R = R_ε`). -/
def curveRescale (R ε : ℝ) (c : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  ((R⁻¹ : ℝ) : ℂ) • c.comp ⟨fun t => ε * t, by fun_prop⟩

theorem curveRescale_apply (R ε : ℝ) (c : C(ℝ, ℂ)) (t : ℝ) :
    curveRescale R ε c t = ((R⁻¹ : ℝ) : ℂ) * c (ε * t) := rfl

theorem coe_curveRescale (R ε : ℝ) (c : C(ℝ, ℂ)) :
    (curveRescale R ε c : ℝ → ℂ) = affineCurve ((R⁻¹ : ℝ) : ℂ) 0 c 0 ε := by
  funext t
  simp [curveRescale_apply, affineCurve]

theorem measurable_curveRescale (ε : ℝ) :
    Measurable fun p : ℝ × C(ℝ, ℂ) => curveRescale p.1 ε p.2 := by
  have hsmul : Continuous fun q : ℂ × C(ℝ, ℂ) => q.1 • q.2 := continuous_smul
  have h1 : Measurable fun p : ℝ × C(ℝ, ℂ) => (((p.1⁻¹ : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (measurable_inv.comp measurable_fst)
  have h2 : Measurable fun p : ℝ × C(ℝ, ℂ) =>
      p.2.comp (⟨fun t => ε * t, by fun_prop⟩ : C(ℝ, ℝ)) :=
    ((ContinuousMap.continuous_precomp _).measurable).comp measurable_snd
  exact hsmul.measurable.comp (h1.prodMk h2)

/-- The localized quantities of `η` at mesh `ε` and root time `0` are those of `η^ε` at mesh `1`. -/
theorem locDA_curveRescale {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (c : C(ℝ, ℂ)) :
    locDA 1 (curveRescale R ε c) 0 = locDA ε c 0 := by
  have hA : ((R⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (inv_pos.mpr hR).ne'
  rw [coe_curveRescale, ← div_self hε.ne', locDA_affine _ _ hA c hε, mul_zero, add_zero]

theorem locDegIn_curveRescale {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (c : C(ℝ, ℂ)) :
    locDegIn 1 (curveRescale R ε c) 0 = locDegIn ε c 0 := by
  have hA : ((R⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (inv_pos.mpr hR).ne'
  rw [coe_curveRescale, ← div_self hε.ne', locDegIn_affine _ _ hA c hε, mul_zero, add_zero]

theorem locDegOut_curveRescale {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (c : C(ℝ, ℂ)) :
    locDegOut 1 (curveRescale R ε c) 0 = locDegOut ε c 0 := by
  have hA : ((R⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (inv_pos.mpr hR).ne'
  rw [coe_curveRescale, ← div_self hε.ne', locDegOut_affine _ _ hA c hε, mul_zero, add_zero]

/-! ## Named inputs -/

/-- **Input (SLE-free + bundle; `[18]`)** — scale invariance of the curve law: for each `ε > 0` there is a
positive random scale `R_ε` with `law(t ↦ R_ε⁻¹ η(εt)) = law(η)` on `C(ℝ, ℂ)` (Borel σ-algebra). Source: "let
`R_ε := sup {r > 0 : h_r(0) + Q log r = γ⁻¹ log ε}` … and `η^ε(t) := η(εt)/R_ε`. By [DMS14, Proposition 4.13(i)],
`h^ε =ᵈ h`. By the γ-LQG coordinate change formula (2.6), `μ_h(X) = ε μ_{h^ε}(X/R_ε)` …, hence `η^ε` is parameterized by
γ-quantum mass with respect to `h^ε`. From this and the scale invariance of the law of space-filling SLE_{κ'}, we get
`(h^ε, η^ε) =ᵈ (h, η)`" (the curve marginal is stated here, with `R_ε` any positive measurable scale; the curve-space formulation: the curve
space is `C(ℝ, ℂ)`, not paths modulo reparametrization). Producers: DMS Prop 4.13(i) for the `0`-cone (SLE-free; proved in this library), the coordinate change (SLE-free; LR1), the scale invariance of whole-plane space-filling SLE and its
independence from the field (IGC from the bundle fields `igMap`, `indep_curve`), and `areaParam₀`. -/
def CurveScaleInvariant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (η : Ω → C(ℝ, ℂ)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : Ω → ℝ, Measurable R ∧ (∀ ω, 0 < R ω) ∧
    P.map (fun ω => curveRescale (R ω) ε (η ω)) = P.map η

/-- ** bundle input** — [20] Proposition 4.4 and Proposition 4.6 for
the `0`-quantum cone with `η(0) = 0`: `E[DA(H₀)^p] < ∞` for `p ≥ 1`, `E[deg_in(H₀)^p] < ∞` for `p ∈ [1, 4/γ²)`,
`E[deg_out(H₀)^p] < ∞` for `p ≥ 1`, where `DA(H₀)`, `deg_in(H₀)`, `deg_out(H₀)` are [18]'s localized quantities at
`ε = 1`, `z = 0`. This is the bundle field `cellMoments` (`MatedCRT.diamAreaSup`, `degInner`, `degOuter`;
equal to `locDA 1 · 0`, `locDegIn 1 · 0`, `locDegOut 1 · 0` on curves with `η(0) = 0`, `GMS4b.BundleAdapter`). -/
def UnitCellMoments {Ω : Type*} [MeasurableSpace Ω] (γ : ℝ) (P : Measure Ω) (η : Ω → C(ℝ, ℂ)) : Prop :=
  (∀ p : ℝ, 1 ≤ p → ∫⁻ ω, locDA 1 (η ω) 0 ^ p ∂P < ⊤) ∧
    (∀ p : ℝ, 1 ≤ p → p < 4 / γ ^ 2 → ∫⁻ ω, ((locDegIn 1 (η ω) 0 : ℕ∞) : ℝ≥0∞) ^ p ∂P < ⊤) ∧
    (∀ p : ℝ, 1 ≤ p → ∫⁻ ω, ((locDegOut 1 (η ω) 0 : ℕ∞) : ℝ≥0∞) ^ p ∂P < ⊤)

/-! ## Theorem 4.4 -/

/-- The triple `(DA, deg_in, deg_out)` at mesh `ε`, root time `0`. -/
def localTriple (ε : ℝ) (c : C(ℝ, ℂ)) : ℝ≥0∞ × ℕ∞ × ℕ∞ :=
  (locDA ε c 0, locDegIn ε c 0, locDegOut ε c 0)

theorem measurable_localTriple {ε : ℝ} (hε : 0 ≤ ε) : Measurable (localTriple ε) :=
  (measurable_locDA ε 0).prodMk ((measurable_locDegIn ε 0).prodMk (measurable_locDegOut hε 0))

/-- **[18] Theorem 4.4, law form** (`[18]`, "the laws of these three quantities do not depend on `ε`"): under
`CurveScaleInvariant`, the joint law of `(DA^ε(0), deg^ε_in(0), deg^ε_out(0))` (root time `0`) is the same for every
`ε > 0`. -/
theorem theorem44_law_holds {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {η : Ω → C(ℝ, ℂ)}
    (hη : Measurable η) (hscale : CurveScaleInvariant P η) {ε : ℝ} (hε : 0 < ε) :
    P.map (fun ω => localTriple ε (η ω)) = P.map (fun ω => localTriple 1 (η ω)) := by
  obtain ⟨R, hRm, hRpos, hlaw⟩ := hscale ε hε
  have hpath : (fun ω => localTriple ε (η ω)) =
      localTriple 1 ∘ fun ω => curveRescale (R ω) ε (η ω) := by
    funext ω
    simp only [Function.comp_apply, localTriple, locDA_curveRescale (hRpos ω) hε,
      locDegIn_curveRescale (hRpos ω) hε, locDegOut_curveRescale (hRpos ω) hε]
  have hmeas : Measurable fun ω => curveRescale (R ω) ε (η ω) :=
    (measurable_curveRescale ε).comp (hRm.prodMk hη)
  rw [hpath, ← Measure.map_map (measurable_localTriple zero_le_one) hmeas, hlaw,
    Measure.map_map (measurable_localTriple zero_le_one) hη]
  rfl

/-- The moments at mesh `ε` equal the moments at mesh `1`, for every measurable test function of the triple. -/
theorem lintegral_localTriple_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {η : Ω → C(ℝ, ℂ)}
    (hη : Measurable η) (hscale : CurveScaleInvariant P η) {ε : ℝ} (hε : 0 < ε)
    {F : ℝ≥0∞ × ℕ∞ × ℕ∞ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (localTriple ε (η ω)) ∂P = ∫⁻ ω, F (localTriple 1 (η ω)) ∂P := by
  have h1 := lintegral_map (μ := P) hF ((measurable_localTriple hε.le).comp hη)
  have h2 := lintegral_map (μ := P) hF ((measurable_localTriple zero_le_one).comp hη)
  simp only [Function.comp_def] at h1 h2
  rw [← h1, ← h2]
  exact congrArg (fun μ => ∫⁻ x, F x ∂μ) (theorem44_law_holds hη hscale hε)

/-- **[18] Theorem 4.4**, at root time `0`. For every `ε > 0`, the moments of `DA^ε(0)`
(`p ≥ 1`), `deg^ε_in(0)` (`p ∈ [1, 4/γ²)`) and `deg^ε_out(0)` (`p ≥ 1`) are *equal* to their (finite) values at
`ε = 1`; in particular they are bounded by constants depending only on `p`. Moreover `deg^ε_in(0) ≥ 1`, so the inner
moments are `≥ 1` (the lower half of `≍` for the inner degree). -/
theorem theorem44_holds {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {η : Ω → C(ℝ, ℂ)} {γ : ℝ}
    (hη : Measurable η) (hscale : CurveScaleInvariant P η) (hmom : UnitCellMoments γ P η) :
    (∀ p : ℝ, 1 ≤ p → ∀ ε : ℝ, 0 < ε →
      ∫⁻ ω, locDA ε (η ω) 0 ^ p ∂P = ∫⁻ ω, locDA 1 (η ω) 0 ^ p ∂P ∧
        ∫⁻ ω, locDA 1 (η ω) 0 ^ p ∂P < ⊤) ∧
    (∀ p : ℝ, 1 ≤ p → p < 4 / γ ^ 2 → ∀ ε : ℝ, 0 < ε →
      ∫⁻ ω, ((locDegIn ε (η ω) 0 : ℕ∞) : ℝ≥0∞) ^ p ∂P =
          ∫⁻ ω, ((locDegIn 1 (η ω) 0 : ℕ∞) : ℝ≥0∞) ^ p ∂P ∧
        ∫⁻ ω, ((locDegIn 1 (η ω) 0 : ℕ∞) : ℝ≥0∞) ^ p ∂P < ⊤) ∧
    (∀ p : ℝ, 1 ≤ p → ∀ ε : ℝ, 0 < ε →
      ∫⁻ ω, ((locDegOut ε (η ω) 0 : ℕ∞) : ℝ≥0∞) ^ p ∂P =
          ∫⁻ ω, ((locDegOut 1 (η ω) 0 : ℕ∞) : ℝ≥0∞) ^ p ∂P ∧
        ∫⁻ ω, ((locDegOut 1 (η ω) 0 : ℕ∞) : ℝ≥0∞) ^ p ∂P < ⊤) ∧
    (∀ ε : ℝ, 0 ≤ ε → ∀ ω, 1 ≤ locDegIn ε (η ω) 0) := by
  have hcoe : Measurable fun n : ℕ∞ => (n : ℝ≥0∞) := measurable_of_countable _
  refine ⟨fun p hp ε hε => ⟨?_, hmom.1 p hp⟩, fun p hp hp' ε hε => ⟨?_, hmom.2.1 p hp hp'⟩,
    fun p hp ε hε => ⟨?_, hmom.2.2 p hp⟩, fun ε hε ω => one_le_locDegIn (η ω).continuous hε⟩
  · exact lintegral_localTriple_eq hη hscale hε (F := fun x => x.1 ^ p)
      ((ENNReal.continuous_rpow_const.measurable).comp measurable_fst)
  · exact lintegral_localTriple_eq hη hscale hε (F := fun x => ((x.2.1 : ℕ∞) : ℝ≥0∞) ^ p)
      ((ENNReal.continuous_rpow_const.measurable).comp (hcoe.comp (measurable_fst.comp measurable_snd)))
  · exact lintegral_localTriple_eq hη hscale hε (F := fun x => ((x.2.2 : ℕ∞) : ℝ≥0∞) ^ p)
      ((ENNReal.continuous_rpow_const.measurable).comp (hcoe.comp (measurable_snd.comp measurable_snd)))

end MatedCRTHarmonic.GMS4b
