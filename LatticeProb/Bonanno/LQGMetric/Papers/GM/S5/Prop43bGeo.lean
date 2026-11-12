/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43bGeo at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43bL54
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.GeodesicsCM

/-!
# GM (5.7) for the selector: `h − φ` lies in the constant-invariant `𝔈_r` (task P2-M2N2)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Lemma 5.4, l. 2819–2832: on `E_r ∩ {P ∩ B_{2r} ≠ ∅}`, Prop 5.2 (C) gives (5.4) for
`P^φ`, the `D_{h−φ}`-geodesic, and (B) gives (5.5) at `h − φ`; so `h − φ ∈ 𝔈_r`.

In Lean `P^φ = sel 𝕫 𝕨 (h − φ)`, and two a.s. facts at the field `h − φ` are needed:
* `ae_isGeod_sel_addFun` : `sel 𝕫 𝕨 (h + φ)` is a.s. a `D_{h+φ}`-geodesic (GM: "the a.s. unique
  `D_{h−φ}`-geodesic"). Proof: the law of `h + φ` is absolutely continuous w.r.t. that of `h` on
  the mean-zero pairings (Cameron–Martin, `ae_notMem_addFun_of_ae`, GM l. 2808); the bad event
  is Borel (`measurableSet_geodRel`, `sel` measurable, D79 (4)) and invariant under recentring
  (`sel` constant-invariant, Weyl scaling for constants); this is the argument of
  `gm_S1_2_addFun` (GeodesicsCM.lean) with `sel` in place of uniqueness.
* the Weyl scaling for constants at `h − φ` (`IsWeakLQGMetric.ae_dist_addConst`, `h − φ` is a GFF
  plus a continuous function), which makes `𝔈_r` at `h − φ` constant-invariant
  (`frkE_addConst_iff`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

omit [IsProbabilityMeasure P] in
lemma isGFFPlusCont_addFun_test (hh : IsWholePlaneGFF h P) (φ : TestC) :
    IsGFFPlusCont (fun ω => addFun (h ω) (testCont φ)) P :=
  ⟨(measurable_addFun_left _).comp hh.measurable, fun _ => testCont φ, measurable_const,
    by simpa [addFun] using hh⟩

/-- `sel 𝕫 𝕨 (h + φ)` is a.s. a `D_{h+φ}`-geodesic (Cameron–Martin transfer) -/
theorem ae_isGeod_sel_addFun {γ : ℝ} {D : DistC → ContMetric} {c₀ : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c₀) {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)}
    (hsel : ∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g)
    (hselm : ∀ a b : ℂ, Measurable (sel a b))
    (hgeo : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ a b : ℂ, a ≠ b →
        ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) a b (sel a b (h ω)))
    (hh : IsWholePlaneGFF h P) (φ : TestC) {a b : ℂ} (hab : a ≠ b) :
    ∀ᵐ ω ∂P, IsGeod01 (D (addFun (h ω) (testCont φ))) a b
      (sel a b (addFun (h ω) (testCont φ))) := by
  have hρ := GFFLaw.integral_bumpTest 0 0
  set B : Set DistC := {g | ¬ IsGeod01 (D g) a b (sel a b g)} with hBdef
  have hBm : MeasurableSet B := by
    have h1 := (measurableSet_geodRel D hD.measurable a b).preimage
      (measurable_id.prodMk (hselm a b))
    exact h1.compl
  have hB : UMeasurableSet B := fun μ _ => hBm.nullMeasurableSet
  have hinv : ∀ {g : Ω → DistC}, IsGFFPlusCont g P → ∀ᵐ ω ∂P,
      (g ω ∈ B ↔ GFFLaw.recenter (bumpTest 0 0) (g ω) ∈ B) := by
    intro g hg
    filter_upwards [hD.ae_dist_addConst hg] with ω hω
    show ¬ IsGeod01 (D (g ω)) a b (sel a b (g ω)) ↔
      ¬ IsGeod01 (D (addConst (g ω) (-(g ω (bumpTest 0 0))))) a b
        (sel a b (addConst (g ω) (-(g ω (bumpTest 0 0)))))
    rw [hsel, isGeod01_iff_of_scale (Real.exp_pos _) (hω _)]
  have h0 : ∀ᵐ ω ∂P, h ω ∉ B := by
    filter_upwards [hgeo P h hh a b hab] with ω hω
    exact fun hb => hb hω
  filter_upwards [ae_notMem_addFun_of_ae hh φ hρ hB h0 (hinv (Tight.isGFFPlusCont_of_wp hh))
    (hinv (isGFFPlusCont_addFun_test hh φ))] with ω hω
  by_contra hc
  exact hω hc

end LQGMetric.GM
