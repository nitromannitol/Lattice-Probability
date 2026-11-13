/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.EpsALemma27 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsAProp210

/-!
# [18] Lemma 2.7 at every real mesh `ε ∈ (0, 1)`, in the consumer shapes of `GMSLemma27/Consumers.lean`

Source: [18] Lemma 2.7 : for `q ∈ (0, 2/(2+γ)²)`, `ρ ∈ (0, 1)`,
"for each `ε ∈ (0, 1)`", with probability `1 − O_ε(ε^α)` every cell `H^ε_x` meeting `B_ρ(0)` has diameter `≤ ε^q`.

L27's `GMSLemma27.lemma27_segments` already holds at every real `ε ∈ (0, 1)` on any `CellModel`; only its consumers
(`GMSLemma27.lemma27_cells_transfer`, `lemma27CellDiam_of_cellModel`, `cellDiamBound_of_cellModel`,
`ae_eventually_cellDiamBound_of_cellModel`) are written for the dyadic meshes `2^{-k}` of a `RandomCellFamily`. The
first three use dyadic-ness only as notation (and `mesh 0 = 1` to absorb `k = 0`); the last one uses it for a
Borel–Cantelli sum `Σ_k 2^{-kα} < ∞`, which has no real-`ε` analogue. Here:

* `epsA_lemma27_cells_transfer` — Lemma 2.7 at every real mesh for cell maps `J ε ω x` identified a.s. with the
  model's cells along a measure-preserving map (the real-mesh `lemma27_cells_transfer`);
* `epsA_lemma27_closedBall_transfer` — the closed-disk form (the `Lemma27CellDiam` shape, at `ρ' = (1+ρ)/2`);
* **`epsA_lemma27_segments_coupling`**, **`epsA_lemma27_coupling`** — for the γ-cone curve `η` of every frozen coupling:
  all segments `η([a, b])`, `b − a ≤ ε` (resp. all cells `η([ε(x−1), εx])`) meeting `B_ρ(0)` have diameter `≤ ε^q`,
  outer failure probability `≤ C ε^α` for every `α < α(q, γ)`; `epsA_lemma27_closedBall_coupling` (closed disk);
* **`EpsALemma27Bad`**, **`epsA_lemma27Bad_coupling`** — G3's `GMS3.CellDiamBound H ρ ε^q` for EVERY cellular
  embedding `H` of `MatedCRT.graph ε (bm ω) h` with the curve cells (and existence of one);
* **`epsA_ae_eventually_lemma27_coupling`** — the real-`ε` replacement of the Borel–Cantelli consumer, by the dyadic
  comparison: almost surely, for all small real `ε > 0`, every segment of length `≤ ε` meeting `B_ρ(0)` (in
  particular every cell `H^ε_x`) has diameter `≤ ε^q` (dyadic mesh `2^{-k} ≥ ε` with a slightly larger `q′`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain

open MatedCRTHarmonic MatedCRTHarmonic.GMSLemma27

variable {γ : ℝ}

/-! ### Transfer along a cell-model identification (real-mesh `lemma27_cells_transfer`) -/

/-! ### The γ-cone curve of a frozen coupling -/

section Coupling

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **[18] Lemma 2.7 for all segments of the γ-cone curve, at every real mesh**: for `q ∈ (0, 2/(2+γ)²)`,
`ρ ∈ (0, 1)` and `α < α(q, γ)`, there is `C` with: for every `ε ∈ (0, 1)`, the outer probability that some segment
`η([a, b])` with `b − a ≤ ε` meets `B_ρ(0)` and has diameter `> ε^q` is at most `C ε^α`. -/
theorem epsA_lemma27_segments_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) {q ρ α : ℝ} (hq : 0 < q)
    (hq' : q < 2 / (2 + γ) ^ 2) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hα : α < lemma27Exponent q γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 →
      P {ω | ∀ a b : ℝ, b - a ≤ ε → (η ω '' Icc a b ∩ ball (0 : ℂ) ρ).Nonempty →
        diam (η ω '' Icc a b) ≤ ε ^ q}ᶜ ≤ ENNReal.ofReal (C * ε ^ α) := by
  have hpar := MesoModel.final_areaParametrization_of_coupling D hstd hγ
  set M := (MoTInput.coneRealizationOfCoupling D hstd hγ).toCellModel hpar with hM
  obtain ⟨C, hC⟩ := lemma27_segments M (MesoModel.final_segmentsContainBalls_of_coupling D hstd hγ hpar)
    (GMCFacts.gmcLowerTail_holds hγ.1 hγ.2)
    (GMCFacts.areaDominates_toCellModel (MoTInput.coneRealizationOfCoupling D hstd hγ) hpar hγ.1 hγ.2)
    hγ.1 hq hq' hρ.1 hρ.2 hα
  refine ⟨max C 0, le_max_right _ _, fun ε hε => ?_⟩
  have hsub : {ω | ∀ a b : ℝ, b - a ≤ ε → (η ω '' Icc a b ∩ ball (0 : ℂ) ρ).Nonempty →
      diam (η ω '' Icc a b) ≤ ε ^ q}ᶜ ≤ᵐ[P] (segmentDiamGood M ε q ρ)ᶜ := by
    filter_upwards [MoTInput.ae_bundleCurve_eq D] with ω hω
    intro hbad hgood
    apply hbad
    have hc : MoTInput.bundleCurve (D := D) ω = η ω := hω
    have hg : ∀ a b : ℝ, b - a ≤ ε → ((MoTInput.bundleCurve (D := D) ω : ℝ → ℂ) '' Icc a b ∩
        ball (0 : ℂ) ρ).Nonempty → diam ((MoTInput.bundleCurve (D := D) ω : ℝ → ℂ) '' Icc a b) ≤ ε ^ q :=
      hgood
    rw [hc] at hg
    exact hg
  calc P {ω | ∀ a b : ℝ, b - a ≤ ε → (η ω '' Icc a b ∩ ball (0 : ℂ) ρ).Nonempty →
        diam (η ω '' Icc a b) ≤ ε ^ q}ᶜ
      ≤ P (segmentDiamGood M ε q ρ)ᶜ := measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (C * ε ^ α) := hC ε hε
    _ ≤ ENNReal.ofReal (max C 0 * ε ^ α) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg hε.1.le _))

/-- **[18] Lemma 2.7 for the cells of the γ-cone curve, at every real mesh** ([18] (2.9)): every cell
`H^ε_x = η([ε(x−1), εx])` meeting `B_ρ(0)` has diameter `≤ ε^q`, outer failure probability `≤ C ε^α`. -/
theorem epsA_lemma27_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) {q ρ α : ℝ} (hq : 0 < q)
    (hq' : q < 2 / (2 + γ) ^ 2) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hα : α < lemma27Exponent q γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 →
      P {ω | ∀ x : ℤ, (η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩ ball (0 : ℂ) ρ).Nonempty →
        diam (η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ≤ ε ^ q}ᶜ ≤ ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨C, hC0, hC⟩ := epsA_lemma27_segments_coupling D hstd hγ hq hq' hρ hα
  refine ⟨C, hC0, fun ε hε => (measure_mono (compl_subset_compl.mpr ?_)).trans (hC ε hε)⟩
  intro ω hω x hx
  exact hω _ _ (le_of_eq (by ring)) hx

end Coupling

/-- **The failure event of [18] Lemma 2.7 at mesh `ε` in G3's form** for the mated-CRT map `MatedCRT.graph ε (bm ω) h`
with the cells of `η`: the complement of "the map is locally finite and the curve cells form a cellular embedding of
it, and EVERY such embedding `H` satisfies `GMS3.CellDiamBound H ρ ε^q`" (cells meeting `B_ρ(0)` have diameter
`≤ ε^q`). -/
def EpsALemma27Bad {Ω : Type*} (bm : Ω → MatedCRT.Path2) (η : Ω → C(ℝ, ℂ)) (ε q ρ : ℝ) : Set Ω :=
  {ω | ¬ ((∃ (hlf : MatedCRT.IsLocallyFinite ε (bm ω)) (H : CellularEmbedding (MatedCRT.graph ε (bm ω) hlf) 0),
        ∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
      ∀ (hlf : MatedCRT.IsLocallyFinite ε (bm ω)) (H : CellularEmbedding (MatedCRT.graph ε (bm ω) hlf) 0),
        (∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) → GMS3.CellDiamBound H ρ (ε ^ q))}

section Coupling

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **[18] Lemma 2.7 in G3's `CellDiamBound` form at every real mesh, for every frozen coupling** (the real-mesh
`cellDiamBound_of_cellModel`): for `q ∈ (0, 2/(2+γ)²)`, `ρ ∈ (0, 1)`, `α < α(q, γ)`, there is `C ≥ 0` with
`P (EpsALemma27Bad bm η ε q ρ) ≤ C ε^α` for every `ε ∈ (0, 1)`. -/
theorem epsA_lemma27Bad_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) {q ρ α : ℝ} (hq : 0 < q)
    (hq' : q < 2 / (2 + γ) ^ 2) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hα : α < lemma27Exponent q γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 →
      P (EpsALemma27Bad bm η ε q ρ) ≤ ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨C, hC0, hC⟩ := epsA_lemma27_coupling D hstd hγ hq hq' hρ hα
  refine ⟨C, hC0, fun ε hε => ?_⟩
  set N : Set Ω := {ω | ¬ ∃ (hlf : MatedCRT.IsLocallyFinite ε (bm ω))
      (H : CellularEmbedding (MatedCRT.graph ε (bm ω) hlf) 0),
        ∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)} with hN
  have hN0 : P N = 0 := ae_iff.mp (epsA_ae_exists_cellularEmbedding D hε.1)
  have hsub : EpsALemma27Bad bm η ε q ρ ⊆
      {ω | ∀ x : ℤ, (η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩ ball (0 : ℂ) ρ).Nonempty →
        diam (η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ≤ ε ^ q}ᶜ ∪ N := by
    intro ω hbad
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
    obtain ⟨hgood, hex⟩ := hcon
    apply hbad
    refine ⟨not_not.mp hex, fun hlf H hcell x hx => ?_⟩
    rw [hcell x] at hx
    have h := hgood x hx
    unfold GMS3.cellDiam
    rw [hcell x]
    exact h
  calc P (EpsALemma27Bad bm η ε q ρ)
      ≤ P {ω | ∀ x : ℤ, (η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩ ball (0 : ℂ) ρ).Nonempty →
          diam (η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ≤ ε ^ q}ᶜ + P N :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ = P {ω | ∀ x : ℤ, (η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩ ball (0 : ℂ) ρ).Nonempty →
          diam (η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ≤ ε ^ q}ᶜ := by rw [hN0, add_zero]
    _ ≤ ENNReal.ofReal (C * ε ^ α) := hC ε hε

end Coupling

end MatedCRTHarmonic.GMSMain
