/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43bL54 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43bInv
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43Out

/-!
# GM Lemma 5.4 (`lem-E-frkE-compare`) in the form of condition (4) of `GeoIterateHyp`
(task P2-M2N2, WP-M2n round 2)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
Lemma 5.4 and its proof, l. 2792–2835. We follow GM's proof:

* l. 2801: "the occurrence of `E_r`, `𝔈_r` is unaffected by adding a constant to `h`": the target
  event is replaced by the a.s. equal, constant-invariant, measurable event
  `{normPsi h ∈ 𝔈_r ∩ {P ∩ B_{2r} ≠ ∅}}` (`Prop43bInv.lean`), which is `{pair0 h ∈ C_T}`;
* l. 2803–2818: the Radon–Nikodym bound `M_h ≤ Λ` on `𝔈_r` and the conditional Cameron–Martin
  comparison given `h|_{ℂ∖B_{3r}}` (modulo constants, D79 (1)): `condExp_le_cm_out` (P2-M2N);
* l. 2820–2832: the inclusion (5.7) `E_r ∩ {P ∩ B_{2r} ≠ ∅} ⊂ 𝔈_r^φ ∩ {P^φ ∩ B_{2r} ≠ ∅}` is the
  hypothesis `hX` (a.s.); it comes from Prop 5.2 (B), (C) via `subTest_mem_frkE`.

Main results:
* `condExp_le_of_invTarget` : the abstract comparison with an invariant measurable target;
* `gm_L5_4_cond4` : condition (4) of `GeoIterateHyp` at one `(z, r, 𝕫, 𝕨)` for
  `Ef = constCore 𝔈_r` (the constant-invariant core, a.s. equal to `𝔈_r`).
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

/-- **GM l. 2803–2818**: conditional Cameron–Martin comparison with a target event that is a.s.
`{h ∈ T}` for a measurable set `T` of fields, invariant under constants, on which `M ≤ Λ` -/
theorem condExp_le_of_invTarget (hh : IsWholePlaneGFF h P) (K : Set ℂ) (G : Finset TestC)
    (hG : ∀ φ ∈ G, ∃ ε > 0, Disjoint (tsupport (φ : ℂ → ℝ)) (Metric.thickening ε K))
    (φc : Ω → TestC) (hφcG : ∀ ω, φc ω ∈ G)
    (hφcm : ∀ φ ∈ G, MeasurableSet[fieldSigmaClosed0 h K] {ω | φc ω = φ})
    {T : Set DistC} (hTm : MeasurableSet T)
    (hTinv : ∀ (g : DistC) (c : ℝ), addConst g c ∈ T ↔ g ∈ T)
    {Λ : ℝ} (hΛ0 : 0 < Λ) (hΛ : ∀ φ ∈ G, ∀ g ∈ T, cmDensity (-φ) (pair0 g) ≤ Λ)
    {X Y : Set Ω} (hXm : NullMeasurableSet X P) (hY : ∀ᵐ ω ∂P, ω ∈ Y ↔ h ω ∈ T)
    (hX : ∀ᵐ ω ∂P, ω ∈ X → subTest (h ω) (φc ω) ∈ T) :
    (fun ω => Λ⁻¹ * (P[X.indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K]) ω) ≤ᵐ[P]
      P[Y.indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K] := by
  obtain ⟨CT, hCT, hCTe⟩ := exists_pair0_preimage hTm hTinv
  set CT' : Set (TestC0 → ℝ) := CT ∩ ⋂ φ ∈ G, {ξ | cmDensity (-φ) ξ ≤ Λ} with hCT'
  have hCT'm : MeasurableSet CT' :=
    hCT.inter (Finset.measurableSet_biInter G fun φ _ =>
      measurableSet_le (measurable_cmDensity (-φ)) measurable_const)
  have hmemT : ∀ g : DistC, pair0 g ∈ CT' ↔ g ∈ T := by
    intro g
    constructor
    · exact fun hg => (hCTe g).2 hg.1
    · intro hg
      refine ⟨(hCTe g).1 hg, ?_⟩
      simp only [mem_iInter]
      exact fun φ hφ => hΛ φ hφ g hg
  have hΛ' : ∀ φ ∈ G, ∀ ξ ∈ CT', cmDensity (-φ) ξ ≤ Λ := by
    intro φ hφ ξ hξ
    have := hξ.2
    simp only [mem_iInter] at this
    exact this φ hφ
  set X' := toMeasurable P X
  have hXX' : X =ᵐ[P] X' := (NullMeasurableSet.toMeasurable_ae_eq hXm).symm
  have hX' : ∀ᵐ ω ∂P, ω ∈ X' → pair0 (subTest (h ω) (φc ω)) ∈ CT' := by
    filter_upwards [hX, hXX'] with ω hω hωe hω'
    exact (hmemT _).2 (hω (hωe.symm ▸ hω' : ω ∈ X))
  have main := condExp_le_cm_out hh K G hG φc hφcG hφcm hCT'm hΛ0 hΛ'
    (measurableSet_toMeasurable P X) hX'
  have e1 : P[X.indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K] =ᵐ[P]
      P[X'.indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K] :=
    condExp_congr_ae (indicator_ae_eq_of_ae_eq_set hXX')
  have hYe : Y =ᵐ[P] {ω | pair0 (h ω) ∈ CT'} := by
    filter_upwards [hY] with ω hω
    exact propext (hω.trans (hmemT _).symm)
  have e2 : P[Y.indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K] =ᵐ[P]
      P[{ω | pair0 (h ω) ∈ CT'}.indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K] :=
    condExp_congr_ae (indicator_ae_eq_of_ae_eq_set hYe)
  filter_upwards [main, e1, e2] with ω h1 h2 h3
  rw [h2, h3]
  exact h1

/-- a compact set inside an open set `U` is at positive distance from `Uᶜ` -/
lemma exists_disjoint_thickening_compl {S U : Set ℂ} (hS : IsCompact S) (hU : IsOpen U)
    (hSU : S ⊆ U) : ∃ ε > 0, Disjoint S (Metric.thickening ε Uᶜ) := by
  obtain ⟨δ, hδ, hδU⟩ := hS.exists_thickening_subset_open hU hSU
  refine ⟨δ, hδ, Set.disjoint_left.2 fun x hxS hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Metric.mem_thickening_iff.1 hx
  exact hy (hδU (Metric.mem_thickening_iff.2 ⟨x, hxS, by rwa [dist_comm]⟩))

/-- the event `{P^{𝕫,𝕨} ∩ B_ρ(z) ≠ ∅}` as a set of fields is measurable -/
lemma measurableSet_hitSet {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)} {a b : ℂ}
    (hselm : Measurable (sel a b)) (z : ℂ) (ρ : ℝ) :
    MeasurableSet {g : DistC | (range (sel a b g) ∩ Metric.ball z ρ).Nonempty} := by
  have hO : IsOpen {η : C(unitInterval, ℂ) | (range η ∩ Metric.ball z ρ).Nonempty} := by
    have : {η : C(unitInterval, ℂ) | (range η ∩ Metric.ball z ρ).Nonempty} =
        ⋃ t : unitInterval, (fun η : C(unitInterval, ℂ) => η t) ⁻¹' Metric.ball z ρ := by
      ext η
      simp only [mem_ofPred_eq, mem_iUnion, mem_preimage]
      constructor
      · rintro ⟨_, ⟨t, rfl⟩, ht⟩; exact ⟨t, ht⟩
      · rintro ⟨t, ht⟩; exact ⟨η t, ⟨t, rfl⟩, ht⟩
    rw [this]
    exact isOpen_iUnion fun t => (Metric.isOpen_ball).preimage (continuous_eval_const t)
  exact hselm hO.measurableSet

end LQGMetric.GM
