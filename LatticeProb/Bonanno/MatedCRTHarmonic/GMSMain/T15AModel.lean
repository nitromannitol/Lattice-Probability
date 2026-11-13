/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T15AModel at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15ACore
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.MesoModelFinal
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.Annulus38Bad

/-!
# T15A: [18] Lemma 3.11 for the embedded mated-CRT map of every frozen mating-of-trees coupling

Source: [18] Lemma 3.11, display (3.35). Conditional on
the frozen bundle `MatedCRT.MatingOfTreesInput γ` : stated for the mesh family
`F = (MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family` of a frozen coupling `D` — almost surely its mesh-`2⁻ᵏ`
multigraph *is* the mated-CRT multigraph `MatedCRT.graph (2⁻ᵏ) (bm ω)` (`coupled.meshGraph_eq`) and its cells are the
SLE/LQG cells `η([ε(x−1), εx])`, so `walkLaw` is the simple random walk `P^ε_x` of [18].

* `lemma311Bad_of_cellFamily` — abstract: the grid annulus-disconnection bad-event bound (frozen `ScaledGridControl` at
  ambient radius `ρ₂`) and almost-sure connectivity give `Lemma311Bad F ρ` for every `ρ < ρ₂` (grid approximation,
  `T15ACore.lemma311Holds_of_scaledGridControl`, plus the coarse meshes absorbed into the constant).
* `cellFamilyCompl_at` — the grid annulus-disconnection estimate on the bundle's family at any ambient radius `ρ₂ < ρ'`, given
  [18] Proposition 2.10 at `(ρ', 100)` (`BundleSec4.Prop210At`): every interface is produced from the preceding estimates
  (L27 at `ρ₂` and `ρ'`, the one-scale Lemma 3.8 at `ρ₂`, WSMP's waypoint input, Route M separation, the lattice
  count, connectivity and looplessness), with the radii as parameters instead of MTC's fixed `ρ = 1/2`.
* `lemma311Bad_of_prop210At` — [18] Lemma 3.11 at every `ρ < ρ' < 1` from Proposition 2.10 at `(ρ', 100)`.
* **`lemma311Bad_of_coupling`** — [18] Lemma 3.11 at every `ρ ∈ (0, 3/4)`, with no premise beyond the coupling:
  Proposition 2.10 at `(3/4, 100)` is the coupling instance (`BundleSec4.h4TripleForAllBundles_holds` →
  `BundleSec4.Prop410AtForAllBundles` → `BundleSec4.Prop210At`).
* **`lemma311_of_matingOfTrees`** — the bundle-level form: every γ ∈ (0, 2), every frozen coupling.

**Radii.** The coupling Proposition 4.10/2.10 instance is hard-wired at `(ρ, C) = (3/4, 100)`, hence the range
`ρ ∈ (0, 3/4)` here. [18] states Lemma 3.11 for every `ρ ∈ (0, 1)`: that is `T15AAllRho.lemma311Bad_of_coupling_all`,
from T13I's all-radius Proposition 2.10 (`GMSMain.t13_prop210At`) and `lemma311Bad_of_prop210At`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.T15A

open MatedCRTHarmonic

private theorem mesh_pos (k : ℕ) : 0 < CellFamily.mesh k := zpow_pos (by norm_num) _
private theorem mesh_le_one (k : ℕ) : CellFamily.mesh k ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by simp)

private theorem mesh_antitone : Antitone CellFamily.mesh := by
  intro a b hab
  exact zpow_le_zpow_right₀ (by norm_num) (by simpa using hab)

private theorem eventually_mesh_rpow_lt {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ k : ℕ in atTop, CellFamily.mesh k ^ a < c := by
  have hm : Tendsto CellFamily.mesh atTop (𝓝 0) := by
    have hp : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    convert tendsto_inv_atTop_zero.comp hp using 1
    ext k
    simp [CellFamily.mesh, zpow_neg, zpow_natCast]
  have hcont : ContinuousAt (fun x : ℝ => x ^ a) 0 := Real.continuousAt_rpow_const 0 a (Or.inr ha.le)
  have ht : Tendsto (fun k : ℕ => CellFamily.mesh k ^ a) atTop (𝓝 0) := by
    simpa [Function.comp_def, Real.zero_rpow ha.ne'] using hcont.tendsto.comp hm
  exact ht.eventually (Iio_mem_nhds hc)

/-! ### From the grid annulus-disconnection estimate to [18] Lemma 3.11 -/

/-- **[18] Lemma 3.11 from the grid annulus-disconnection estimate.** If almost every mesh graph of `F` is connected and the
frozen grid annulus-disconnection event `ScaledGridControl 1 (2⁻ᵏ) χ β q ρ₂ p` fails with outer probability `≤ C 2^{−kα}`, with
`0 < β < min χ q`, then `Lemma311Bad F ρ` holds for every `ρ < ρ₂` (with the same `α, β, p`). -/
theorem lemma311Bad_of_cellFamily (F : CellFamily.RandomCellFamily) (hconn : CellFamily.GraphConnected F)
    {χ β α p C q ρ₂ ρ : ℝ} (hβ : 0 < β) (hβχ : β < χ) (hβq : β < q) (hα : 0 < α) (hp : 0 < p)
    (hρ : ρ < ρ₂)
    (h26 : ∀ k, F.P {ω | (F.H k ω).ScaledGridControl 1 (CellFamily.mesh k) χ β q ρ₂ p}ᶜ ≤
      ENNReal.ofReal (C * CellFamily.mesh k ^ α)) :
    Lemma311Bad F ρ := by
  have hgap : 0 < ρ₂ - ρ := by linarith
  have hev : ∀ᶠ k : ℕ in atTop,
      CellFamily.mesh k ^ (q - β) < 1 / 18 ∧ CellFamily.mesh k ^ (χ - β) < 1 / 18 ∧
        CellFamily.mesh k ^ q < (ρ₂ - ρ) / 7 ∧ CellFamily.mesh k ^ χ < (ρ₂ - ρ) / 7 :=
    (eventually_mesh_rpow_lt (by linarith) (by norm_num)).and
      ((eventually_mesh_rpow_lt (by linarith) (by norm_num)).and
        ((eventually_mesh_rpow_lt (by linarith) (by linarith)).and
          (eventually_mesh_rpow_lt (by linarith) (by linarith))))
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  refine ⟨α, hα, β, hβ, p, hp, max C 0 + (CellFamily.mesh K ^ α)⁻¹, fun k => ?_⟩
  have hm0 := mesh_pos k
  have hpowα : 0 ≤ CellFamily.mesh k ^ α := Real.rpow_nonneg hm0.le _
  rcases lt_or_ge k K with hkK | hkK
  · -- coarse meshes: the bound is `≥ 1`
    have hKk : CellFamily.mesh K ^ α ≤ CellFamily.mesh k ^ α :=
      Real.rpow_le_rpow (mesh_pos K).le (mesh_antitone hkK.le) hα.le
    have hKpos : 0 < CellFamily.mesh K ^ α := Real.rpow_pos_of_pos (mesh_pos K) _
    have hone : 1 ≤ (max C 0 + (CellFamily.mesh K ^ α)⁻¹) * CellFamily.mesh k ^ α := by
      have h1 : 1 ≤ (CellFamily.mesh K ^ α)⁻¹ * CellFamily.mesh k ^ α := by
        rw [inv_mul_eq_div, le_div_iff₀ hKpos, one_mul]
        exact hKk
      have h2 : 0 ≤ max C 0 * CellFamily.mesh k ^ α := mul_nonneg (le_max_right _ _) hpowα
      nlinarith
    calc F.P (Lemma311Good F k ρ β p)ᶜ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hone
  · -- fine meshes: (3.35) holds on the grid annulus-disconnection event of a connected graph
    obtain ⟨h1, h2, h3, h4⟩ := hK k hkK
    have hs : 0 < CellFamily.mesh k ^ χ := Real.rpow_pos_of_pos hm0 _
    have hd : 0 ≤ CellFamily.mesh k ^ q := Real.rpow_nonneg hm0.le _
    have hβpow : 0 < CellFamily.mesh k ^ β := Real.rpow_pos_of_pos hm0 _
    have hsmall : 5 * CellFamily.mesh k ^ q + 13 * CellFamily.mesh k ^ χ ≤ CellFamily.mesh k ^ β := by
      have hq' : CellFamily.mesh k ^ q = CellFamily.mesh k ^ β * CellFamily.mesh k ^ (q - β) := by
        rw [← Real.rpow_add hm0]
        ring_nf
      have hχ' : CellFamily.mesh k ^ χ = CellFamily.mesh k ^ β * CellFamily.mesh k ^ (χ - β) := by
        rw [← Real.rpow_add hm0]
        ring_nf
      rw [hq', hχ']
      nlinarith
    have hroom : 2 * CellFamily.mesh k ^ q + 5 * CellFamily.mesh k ^ χ < ρ₂ - ρ := by linarith
    have hsub : (Lemma311Good F k ρ β p)ᶜ ⊆
        {ω | (F.H k ω).ScaledGridControl 1 (CellFamily.mesh k) χ β q ρ₂ p}ᶜ ∪
          {ω | ¬ (F.G k ω).adj.Connected} := by
      intro ω hω
      by_contra hnot
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, not_or, not_not] at hnot
      exact hω (lemma311Holds_of_scaledGridControl (F.H k ω) hnot.2 hnot.1 hs hd hsmall hroom)
    have hnull : F.P {ω | ¬ (F.G k ω).adj.Connected} = 0 := ae_iff.mp (hconn k)
    calc F.P (Lemma311Good F k ρ β p)ᶜ
        ≤ F.P ({ω | (F.H k ω).ScaledGridControl 1 (CellFamily.mesh k) χ β q ρ₂ p}ᶜ ∪
            {ω | ¬ (F.G k ω).adj.Connected}) := measure_mono hsub
      _ ≤ F.P {ω | (F.H k ω).ScaledGridControl 1 (CellFamily.mesh k) χ β q ρ₂ p}ᶜ +
            F.P {ω | ¬ (F.G k ω).adj.Connected} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (C * CellFamily.mesh k ^ α) := by rw [hnull, add_zero]; exact h26 k
      _ ≤ ENNReal.ofReal ((max C 0 + (CellFamily.mesh K ^ α)⁻¹) * CellFamily.mesh k ^ α) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_right _ hpowα
          have := inv_nonneg.mpr (Real.rpow_nonneg (mesh_pos K).le α)
          linarith [le_max_left C 0]

/-! ### The bundle model -/

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **The grid annulus-disconnection estimate on the bundle's mesh family at ambient radius `ρ₂`**, from [18]
Proposition 2.10 at `(ρ', 100)` with `ρ₂ < ρ' < 1`. The interfaces are produced from the preceding estimates
(`MesoModel.cellFamilyCompl_of_interfaces`, `Lemma38Source.annulus38OneScaleBadBound_of_proposition210_at_mtc`), with the two radii as
parameters. -/
theorem cellFamilyCompl_at
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) {ρ₂ ρ' : ℝ} (hρ₂ : 0 < ρ₂) (hρ₂ρ' : ρ₂ < ρ')
    (hρ' : ρ' < 1)
    (h210 : BundleSec4.Prop210At (MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family ρ' 100) :
    ∃ χ β α p C : ℝ, 0 < χ ∧ 0 < β ∧ β < min χ (MoTInput.unitMesoModelOfCoupling D hstd hγ).q ∧
      0 < α ∧ 0 < p ∧
      ∀ k, (MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family.P
        {ω | ((MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family.H k ω).ScaledGridControl 1
          (CellFamily.mesh k) χ β (MoTInput.unitMesoModelOfCoupling D hstd hγ).q ρ₂ p}ᶜ ≤
          ENNReal.ofReal (C * CellFamily.mesh k ^ α) := by
  let M := MoTInput.unitMesoModelOfCoupling D hstd hγ
  let C := MoTInput.coneRealizationOfCoupling D hstd hγ
  let hpar : CellScaling.AreaParametrization C := MesoModel.final_areaParametrization_of_coupling D hstd hγ
  let S := C.toCellModelGraphCoupling hpar
  let F := M.coupled.family
  have hSLE := MesoModel.final_segmentsContainBalls_of_coupling D hstd hγ hpar
  have hGMC := GMCFacts.gmcLowerTail_holds hγ.1 hγ.2
  have hdom := GMCFacts.areaDominates_toCellModel C hpar hγ.1 hγ.2
  have hq : 0 < M.q := M.hq.1
  have hden : 0 < (2 + γ) ^ 2 := by
    have htwo : 0 < 2 + γ := by linarith [hγ.1]
    positivity
  have hq1 : M.q < 1 := by
    have hfrac : 2 / (2 + γ) ^ 2 < 1 := (div_lt_iff₀ hden).mpr (by nlinarith [sq_nonneg γ, hγ.1])
    exact M.hq.2.trans hfrac
  -- [18] Lemma 2.7 at the radius of the grid annulus-disconnection estimate `ρ₂`
  have h27 : CellFamily.Lemma27CellDiamBad F M.q ρ₂ :=
    CellScaling.lemma27CellDiamBad_of_cellModel hSLE hGMC hdom hγ.1 F id (MeasurePreserving.id _)
      (C.ae_familyCell_eq_toCellModel hpar) hq M.hq.2 hρ₂.le (hρ₂ρ'.trans hρ')
  -- [18] Lemma 2.7 at the Proposition 2.10 radius `ρ'`, in G3's form
  have hα27pos : 0 < GMSLemma27.lemma27Exponent M.q γ := GMSLemma27.lemma27Exponent_pos hγ.1 hq M.hq.2
  have hα27lt : GMSLemma27.lemma27Exponent M.q γ / 2 < GMSLemma27.lemma27Exponent M.q γ := by linarith
  obtain ⟨C27, hC27, h27'⟩ := GMSLemma27.cellDiamBound_of_cellModel (C.toCellModel hpar) hSLE hGMC hdom
    hγ.1 S.toRandomCellFamily S.modelMap S.measurePreserving_modelMap S.ae_cell_eq hq M.hq.2
    ⟨hρ₂.trans hρ₂ρ', hρ'⟩ hα27lt
  have hpeano : CellFamily.PeanosphereG0 F := MesoModel.final_peanosphereG0_of_coupling D hstd hγ
  -- [18] Lemma 3.8 at `ρ₂` (from Proposition 2.10 at `ρ'`)
  obtain ⟨betaG4, A, α210, Cfail, hbetaG4, hα210, hA, hCfail, h210'⟩ := h210
  have hAnnulus38 : MesoModel.Annulus38OneScaleBadBound F ρ₂ :=
    Lemma38Source.annulus38OneScaleBadBound_of_L27_G4 F hρ₂ hρ₂ρ' hρ' hq hq1 hbetaG4 hα210 (by linarith) hA hC27 hCfail
      hpeano (fun k => h27' k) h210'
  have h38 : CellFamily.Lemma38AnnulusHitBad F ρ₂ := MesoModel.lemma38AnnulusHitBad_of_oneScaleBadBound F ρ₂ hAnnulus38
  have hConnected : CellFamily.GraphConnected F :=
    CellFamily.graphConnected_ofCellCoupling M.coupled.toCellCoupledRandomFamily
  have hLoopless : CellFamily.GraphLoopless F := M.coupled.ae_loopless
  have hSeparation := CellFamily.templateSeparation_of_peanosphereG0 F hpeano
  have hItinerary := CellFamily.itineraryEstimateBad_of_lemma38Bad_fixed2 F M.q ρ₂ h27 h38 hConnected hLoopless hq
    (CellFamily.waypointStrongMarkovInputFixed2_holds F M.q ρ₂)
  exact CellFamily.cellFamily_compl_of_interfaces_bad F γ ρ₂ M.q hγ ⟨hρ₂, hρ₂ρ'.trans hρ'⟩ M.hq h27 hItinerary
    (CellFamily.finiteGridCount_holds ρ₂) hConnected hSeparation

end Coupling

end MatedCRTHarmonic.GMSMain.T15A
