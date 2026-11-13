/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.MainResultsInputs at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.MainResultsAdapters

/-!
# Inputs to the main results of [18] and their adapters

The draft anchors of surface v5 (`MainResultsStatements`) are proved in `MainResultsAnchors` from **three** named inputs, one for each result needed at every real mesh `ε ∈ (0, 1)`. Each input quantifies
over every frozen mating-of-trees coupling (every witness of `MatedCRT.MatingOfTreesInput γ`, `γ ∈ (0, 2)`), with the
explicit `hγ : γ ∈ Ioo 0 2` and `hstd : StandardBorelSpace Ω` of the per-coupling theorems, so that a theorem `foo D hstd hγ` discharges it as `fun γ hγ Ω _ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D => foo D hstd hγ`.

* `Theorem32Input` — [18] Theorem 3.2 at every real `ε`, using the energy and Green-function vocabulary (`RawEnergyGood`, the
  `T13RawEnergyGood` event of `GMSMain/T13Raw.lean` with the additive error `ε^α` of (3.10): cellular embedding with
  the curve cells, `IsGMSDirichletSolution`, `GMS3.energy` on `vFin`, `GMS3.eucEnergy`, `BoundedConvexityWith`).
  The real-mesh proof uses `epsA_prop210At` and `lemma27_cellAt`.
* `Theorem14GreenInput` — [18] Theorem 1.4 (1.8) at every real `ε`, using the energy and Green-function vocabulary (`RawGreenGood` =
  the body of `T13RawGreenGood`, `GMS3.green` on `vFin`, `log ε⁻¹/A · deg(0) ≤ Gr`). The same real-mesh inputs apply.
* `Theorem15Input` — [18] Theorem 1.5 (main form, (a)) at every real `ε`, in the draft's vocabulary (= the
  hypothesis `h15` of T16D's `corollary16_tendsto_of_theorem15`, for every coupling). The proof uses the real-mesh estimate (3.35). `theorem15Input_of_sSup` accepts T15B's `sSup` form of (1.6) instead.

Adapters (per coupling, every `ω`, deterministic): `rawEnergyGood_imp` / `theorem32Body_of_raw` and
`rawGreenGood_imp` / `theorem14GreenBody_of_raw` turn the input events into the stated good events
(`MainResultsAdapters`: `energyOn = ofReal ∘ GMS3.energy`, `exitGreen = GMS3.green`, (1.8) normalization, existence of
`f_ε` from T16D's Dirichlet layer).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.MainResults

open MatedCRTHarmonic GMS3

/-! ### Input events -/

/-- **The event (3.10) of [18] Theorem 3.2 using the corresponding definitions** at mesh `ε` for the mated-CRT map of the Brownian
path `b` with the cells `c([ε(x−1), εx])`: `MatedCRT.graph ε b` is locally finite and has the cellular embedding with
these cells, and every `f_ε` with the boundary data (1.6), discrete harmonic on `V(D) \ V(∂D)`, has
`Energy(f_ε; G^ε(D)) ≤ A Energy(f; D) + tol`. With `tol = 0` this is T13I's `T13RawEnergyGood`. -/
def RawEnergyGood (ε : ℝ) (b : MatedCRT.Path2) (c : C(ℝ, ℂ)) (Dom : Set ℂ) (f : ℂ → ℝ) (A tol : ℝ) : Prop :=
  ∃ (h : MatedCRT.IsLocallyFinite ε b) (H : CellularEmbedding (MatedCRT.graph ε b h) 0),
    (∀ x : ℤ, H.cell x = c '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
      ∀ fε : ℤ → ℝ, GMSMain.IsGMSDirichletSolution H Dom f fε →
        ENNReal.ofReal (energy (MatedCRT.graph ε b h) (vFin H Dom) fε) ≤
          ENNReal.ofReal A * eucEnergy f Dom + ENNReal.ofReal tol

variable {Ω : Type} [MeasurableSpace Ω]

/-- **[18] Theorem 3.2 at every real `ε` for one coupling, using the corresponding definitions** (same quantifier order and
hypotheses as the draft anchor `matedCRT_energy_le_add_of_matingOfTrees`). -/
def Theorem32RawBody (P : Measure Ω) (η : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ C : ℝ, 1 ≤ C →
    ∃ A : ℝ, 0 < A ∧ ∃ Cr : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ →
      (∀ r ∈ Ioo (0 : ℝ) 1, volume (thickening r (frontier D)) ≤ ENNReal.ofReal (C * r)) →
      GMSMain.BoundedConvexityWith C D →
      ∀ f : ℂ → ℝ, DifferentiableOn ℝ f D →
        (∀ z ∈ D, ∀ w ∈ D, ‖fderiv ℝ f z - fderiv ℝ f w‖ ≤ ε ^ (-β) * dist z w) →
        (∀ z ∈ D, |f z| ≤ ε ^ (-β)) → (∀ z ∈ D, ‖fderiv ℝ f z‖ ≤ ε ^ (-β)) →
        ContinuousOn f (closure D) →
          P {ω | ¬ RawEnergyGood ε (bm ω) (η ω) D f A (ε ^ α)} ≤ ENNReal.ofReal (Cr * ε ^ α)

/-! ### The three named inputs (every coupling) -/

/-- **Named input 1: [18] Theorem 3.2 at every real `ε ∈ (0, 1)`**, for every frozen coupling. -/
def Theorem32Input : Prop :=
  ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 2 → ∀ (Ω : Type) [MeasurableSpace Ω], StandardBorelSpace Ω →
    ∀ (P : Measure Ω) (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
      (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
      MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm → Theorem32RawBody P η bm

/-! ### Adapters from input events to the stated good events -/

/-- **T13I's (3.10) event gives the draft's good event of Theorem 3.2** (every `ω`; `D` bounded, `f` continuous on
`∂D`): local finiteness, existence of `f_ε` (T16D's walk solution), and the energy bound for every `f_ε` of the draft
(1.6) (`isGMSDirichletSolution_of_isHarmonicExtension`, `energyOn_verticesMeeting`). -/
theorem rawEnergyGood_imp {ε : ℝ} {b : MatedCRT.Path2} {c : C(ℝ, ℂ)} {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D)
    {f : ℂ → ℝ} (hfc : ContinuousOn f (frontier D)) (hf : DifferentiableOn ℝ f D) {A tol : ℝ}
    (hraw : RawEnergyGood ε b c D f A tol) :
    ∃ h : MatedCRT.IsLocallyFinite ε b,
      (∃ g : ℤ → ℝ, IsHarmonicExtension (MatedCRT.graph ε b h) (cell ε c) D f g) ∧
      ∀ g : ℤ → ℝ, IsHarmonicExtension (MatedCRT.graph ε b h) (cell ε c) D f g →
        energyOn (MatedCRT.graph ε b h) (verticesMeeting (cell ε c) D) g ≤
          ENNReal.ofReal A * dirichletEnergy f D hDo hf + ENNReal.ofReal tol := by
  obtain ⟨h, H, hcell, hb⟩ := hraw
  have hHc : H.cell = cell ε c := funext hcell
  refine ⟨h, ?_, fun g hg => ?_⟩
  · rw [← hHc]
    exact ⟨_, T16D.isHarmonicExtension_dirichletSol H hDb hfc⟩
  · rw [← hHc] at hg ⊢
    rw [energyOn_verticesMeeting H hDb]
    exact hb g (isGMSDirichletSolution_of_isHarmonicExtension H hDb hg)

/-- **Theorem 3.2: T13I's form ⇒ the draft body** (one coupling). -/
theorem theorem32Body_of_raw {P : Measure Ω} {η : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (h32 : Theorem32RawBody P η bm) : Theorem32Body P η bm := by
  obtain ⟨α, hα, β, hβ, h32⟩ := h32
  refine ⟨α, hα, β, hβ, fun ρ hρ0 hρ1 C hC => ?_⟩
  obtain ⟨A, hA, Cr, h32⟩ := h32 ρ hρ0 hρ1 C hC
  refine ⟨A, hA, Cr, fun ε hε0 hε1 D hDo hDsub hbdry hbc f hf hL hfM hdfM hfc => ?_⟩
  refine le_trans (measure_mono ?_) (h32 ε hε0 hε1 D hDo hDsub hbdry hbc f hf hL hfM hdfM hfc)
  intro ω hω hraw
  exact hω (rawEnergyGood_imp hDo (isBounded_ball.subset hDsub) (hfc.mono frontier_subset_closure) hf hraw)

end MatedCRTHarmonic.GMSMain.MainResults
