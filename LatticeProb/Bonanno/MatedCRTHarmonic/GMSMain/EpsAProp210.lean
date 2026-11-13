/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.EpsAProp210 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsAProp410

/-!
# [18] Proposition 2.10 at every real mesh `ε ∈ (0, 1)` on the mated-CRT map of every frozen coupling

Source: [18] Proposition 2.10 : "For `ε ∈ (0, 1)` … with probability
`1 − O_ε(ε^α)`, `∫_D f u^ε ≤ A ∫_D f + ε^α`", and [18], "Proposition 2.10 is an immediate consequence of
Proposition 4.10 and (4.20)".

`BundleSec4.prop210At_of_prop410At` works on MTC's dyadic random cell family (`CellFamily.RandomCellFamily`, indexed by
`k : ℕ`), whose (4.20) comparison `BundleSec4.ae_uDens_le_two_uStar` intersects countably many almost-sure events
(`MoTInput.ae_sideStrict_allMeshes`, `ae_meshCellularEmbeddings`, …). At ONE fixed real mesh `ε` every ingredient is
almost sure on its own: the Brownian side condition `MatedCRT.ae_sideStrict` and local finiteness
`ae_isLocallyFinite_holds` are stated for every `ε > 0`, the Peanosphere event and the interiors of curve segments
do not depend on `ε`, and the degree bound (4.7) `GMS4F.matedCRT_degree_le_two_local_degrees`, the coefficient bound
`Canon.selectedCell_rawCoef_le_two_uStar` and the curve-cell embedding `MoTInput.cellularEmbeddingOfCurveAt` are
deterministic at every `ε > 0`. So no family is needed: the statement is made directly for the coupling's
mated-CRT map `MatedCRT.graph ε (bm ω) h` with ANY cellular embedding whose cells are the curve cells
`H^ε_x = η([ε(x−1), εx])` ([18] (1.3); `MatedCRT.cell`).

* `epsA_ae_rawCoef_le_two_uStar` — (4.5)+(4.7) at one real mesh;
* `epsA_uDens_le_two_uStar` — deterministic (4.20) for any embedding with the curve cells;
* `epsA_ae_exists_cellularEmbedding` — at one real mesh, a.s. the map is locally finite and the curve cells form a
  cellular embedding;
* **`EpsAProp210Bad bm η ε V f A tol`** — the failure of: "an embedding with the curve cells exists, and EVERY such
  embedding `H` satisfies G3's `Prop210Bound H V f A tol`" (`∫⁻_V f u^ε ≤ A ∫⁻_V f + tol`);
* **`EpsAProp210At P bm η ρ C`** — `∃ β A α Cfail`, every `ε ∈ (0, 1)`, every admissible `(V, f)`:
  `P (EpsAProp210Bad bm η ε V f A ε^α) ≤ Cfail ε^α`;
* `epsA_prop210Bad_le_of_prop410Bad`, `epsA_prop210At_of_prop410At` — Proposition 4.10 + (4.20) ⇒ Proposition 2.10
  (threshold `2A`, exponent `α/2`, rate `Cfail + 2`);
* **`epsA_prop210At`** — `EpsAProp210At P bm η ρ C` for every frozen coupling, `ρ ∈ (0, 1)`, `C > 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain

open MatedCRTHarmonic

/-! ### The deterministic (4.20) at one real mesh -/

/-- **[18] (4.20) at one real mesh, deterministically**: for a Peanosphere pair `(w, c)`, a locally finite mesh-`ε`
mated-CRT map and ANY cellular embedding `H` of it whose cells are the curve cells `c([ε(x−1), εx])`, if the
selected-cell coefficient is at most `2 u_*^ε` everywhere, then `u^ε ≤ 2 u_*^ε` Lebesgue-a.e. -/
theorem epsA_uDens_le_two_uStar {ε : ℝ} (hε : 0 < ε) {c : C(ℝ, ℂ)} {w : MatedCRT.Path2}
    (hP : RouteM.Peanosphere w c) (hlf : MatedCRT.IsLocallyFinite ε w)
    (H : CellularEmbedding (MatedCRT.graph ε w hlf) 0)
    (hcell : ∀ x : ℤ, H.cell x = c '' Icc (ε * ((x : ℝ) - 1)) (ε * x))
    (hcoef : ∀ z : ℂ, Canon.rawCellCoef ε c w (Canon.selectedIndex ε c z) ≤ 2 * GMS4b.uStar ε c z) :
    ∀ᵐ z ∂volume, GMS3.uDens H z ≤ 2 * GMS4b.uStar ε c z := by
  have hcellC : ∀ x : ℤ, H.cell x = Canon.cell ε c x := fun x => by rw [hcell x]; rfl
  have hc : ∀ z, z ∈ H.cell (Canon.selectedIndex ε c z) := by
    intro z
    rw [hcell]
    exact BundleSec4.bundle_mem_cellOf_selectedIndex hε hP.surj hP.transient z
  filter_upwards [GMS3.uDens_ae_eq H (fun z => Canon.selectedIndex ε c z) hc] with z hz
  have hcoefH : GMS3.uCoef H (Canon.selectedIndex ε c z) =
      Canon.rawCellCoef ε c w (Canon.selectedIndex ε c z) :=
    (Canon.rawCellCoef_eq_uCoef ε c w hlf H _ (hcellC _)).symm
  rw [hz, hcoefH]
  exact hcoef z

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- The Brownian side condition at one real mesh, on the bundle's sample space. -/
theorem epsA_ae_sideStrict (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ε : ℝ} (hε : 0 < ε) : ∀ᵐ ω ∂P, RouteM.SideStrict ε (bm ω) :=
  ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable (MatedCRT.ae_sideStrict D.boundaryLawBM ε hε)

/-- Local finiteness at one real mesh, on the bundle's sample space. -/
theorem epsA_ae_isLocallyFinite (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ε : ℝ} (hε : 0 < ε) : ∀ᵐ ω ∂P, MatedCRT.IsLocallyFinite ε (bm ω) :=
  ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable
    (MatedCRTHarmonic.ae_isLocallyFinite_holds γ (P.map bm) D.boundaryLawBM ε hε)

/-- **(4.5) + (4.7) at one real mesh**: almost surely, for every local-finiteness witness and every point `z`, the
selected-cell coefficient `diam(H_x)² deg(x)/area(H_x)` of the γ-cone curve is at most `2 u_*^ε(z)`. -/
theorem epsA_ae_rawCoef_le_two_uStar
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ (_hlf : MatedCRT.IsLocallyFinite ε (bm ω)) (z : ℂ),
      Canon.rawCellCoef ε (η ω) (bm ω) (Canon.selectedIndex ε (η ω) z) ≤ 2 * GMS4b.uStar ε (η ω) z := by
  filter_upwards [MoTInput.ae_peanosphere D, epsA_ae_sideStrict D hε,
    MoTInput.ae_curve_intervals_have_interior D] with ω hP hs hInt
  intro hlf z
  have hWinInt : (interior (GMS4b.locWindow ε (η ω) (GMS4b.hitTime (η ω) z))).Nonempty := by
    simpa only [GMS4b.locWindow] using
      hInt (GMS4b.hitTime (η ω) z - ε) (GMS4b.hitTime (η ω) z + ε) (by linarith)
  have hD := GMS4F.diam_locWindow_pos_of_interior_nonempty (η ω).continuous hWinInt
  exact Canon.selectedCell_rawCoef_le_two_uStar hε (η ω) (bm ω) hlf z
    (GMS4F.matedCRT_degree_le_two_local_degrees hε hP hs hlf (η ω).continuous _ hD)

/-- **The concrete (4.20) at one real mesh**: almost surely, for every local-finiteness witness and every cellular
embedding of the mesh-`ε` mated-CRT map with the curve cells, `u^ε ≤ 2 u_*^ε` Lebesgue-a.e. -/
theorem epsA_ae_uDens_le_two_uStar
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ (hlf : MatedCRT.IsLocallyFinite ε (bm ω))
      (H : CellularEmbedding (MatedCRT.graph ε (bm ω) hlf) 0),
      (∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) →
        ∀ᵐ z ∂volume, GMS3.uDens H z ≤ 2 * GMS4b.uStar ε (η ω) z := by
  filter_upwards [MoTInput.ae_peanosphere D, epsA_ae_rawCoef_le_two_uStar D hε] with ω hP hcoef
  intro hlf H hcell
  exact epsA_uDens_le_two_uStar hε hP hlf H hcell (hcoef hlf)

/-- **The curve cells form a cellular embedding at one real mesh, almost surely**: the mesh-`ε` mated-CRT map is
locally finite and `x ↦ η([ε(x−1), εx])` is a cellular embedding of it rooted at `0`. -/
theorem epsA_ae_exists_cellularEmbedding
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∃ (hlf : MatedCRT.IsLocallyFinite ε (bm ω))
      (H : CellularEmbedding (MatedCRT.graph ε (bm ω) hlf) 0),
        ∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x) := by
  filter_upwards [epsA_ae_isLocallyFinite D hε, MoTInput.ae_peanosphere D, epsA_ae_sideStrict D hε,
    MoTInput.ae_curve_intervals_have_interior D, D.areaParam, D.spaceFilling]
    with ω hlf hP hs hInt harea hspace
  rcases harea with ⟨⟨φ, hφ0, hη⟩, _⟩
  rcases hspace with ⟨_, _, hηL0, hvol⟩
  have hη0 : η ω 0 = 0 := by rw [hη, hφ0, hηL0]
  exact ⟨hlf, MoTInput.cellularEmbeddingOfCurveAt hε hlf hP hs hη0
    (fun x => hInt _ _ (by nlinarith [hε]))
    (fun x y hxy => MoTInput.volume_inter_mesh_cells_zero hε hη hvol hxy), fun x => rfl⟩

end Coupling

/-! ### The real-mesh Proposition 2.10 event -/

/-- **The failure event of [18] Proposition 2.10 at mesh `ε` for the mated-CRT map `MatedCRT.graph ε (bm ω) h`
with the cells of the area-parametrized curve `η`**: the complement of "the map is locally finite and the curve cells
`η([ε(x−1), εx])` form a cellular embedding of it (rooted at `0`), and EVERY such embedding `H` satisfies G3's
`Prop210Bound H V f A tol`, i.e. `∫⁻_V f u^ε ≤ A ∫⁻_V f + tol` with `u^ε` the selection-free density (2.12)". -/
def EpsAProp210Bad {Ω : Type*} (bm : Ω → MatedCRT.Path2) (η : Ω → C(ℝ, ℂ)) (ε : ℝ) (V : Set ℂ) (f : ℂ → ℝ)
    (A tol : ℝ) : Set Ω :=
  {ω | ¬ ((∃ (hlf : MatedCRT.IsLocallyFinite ε (bm ω)) (H : CellularEmbedding (MatedCRT.graph ε (bm ω) hlf) 0),
        ∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
      ∀ (hlf : MatedCRT.IsLocallyFinite ε (bm ω)) (H : CellularEmbedding (MatedCRT.graph ε (bm ω) hlf) 0),
        (∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) → GMS3.Prop210Bound H V f A tol)}

/-- **One fixed-parameter instance of [18] Proposition 2.10 at every real mesh** for the mated-CRT maps
`MatedCRT.graph ε (bm ·)` with the cells of `η`, at ambient radius `ρ` and test constant `C`: `∃ β, A, α, Cfail`,
for every `ε ∈ (0, 1)` and every pair `(V, f)` admissible at `(ε, ρ, C, β)` (`GMS4.Prop210Admissible`: `V ⊂ B_ρ(0)`
open connected, `area(B_r(∂V)) ≤ C r` for `r ∈ (0, 1)`, `0 ≤ f ≤ C ε^{-β}`, `f` `C ε^{-β}`-Lipschitz), the
outer probability of `EpsAProp210Bad bm η ε V f A ε^α` is at most `Cfail ε^α`. -/
def EpsAProp210At {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (bm : Ω → MatedCRT.Path2)
    (η : Ω → C(ℝ, ℂ)) (ρ C : ℝ) : Prop :=
  ∃ β A α Cfail : ℝ, 0 < β ∧ 0 < α ∧ 0 ≤ A ∧ 0 ≤ Cfail ∧
    ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 → ∀ (V : Set ℂ) (f : ℂ → ℝ), GMS4.Prop210Admissible ε ρ C β V f →
      P (EpsAProp210Bad bm η ε V f A (ε ^ α)) ≤ ENNReal.ofReal (Cfail * ε ^ α)

/-- On the good event, the bound holds for any given embedding with the curve cells. -/
theorem epsA_prop210Bound_of_not_mem_bad {Ω : Type*} {bm : Ω → MatedCRT.Path2} {η : Ω → C(ℝ, ℂ)} {ε : ℝ}
    {V : Set ℂ} {f : ℂ → ℝ} {A tol : ℝ} {ω : Ω} (hω : ω ∉ EpsAProp210Bad bm η ε V f A tol)
    (hlf : MatedCRT.IsLocallyFinite ε (bm ω)) (H : CellularEmbedding (MatedCRT.graph ε (bm ω) hlf) 0)
    (hcell : ∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) :
    GMS3.Prop210Bound H V f A tol := by
  have h : ¬ ¬ _ := hω
  exact (not_not.mp h).2 hlf H hcell

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **One test of [18] Proposition 2.10 at a real mesh from the same test of Proposition 4.10 and (4.20)**: if the
Proposition 4.10 failure (threshold `A`, tolerance `ε^α`) has outer probability `≤ Cfail ε^α`, then the
Proposition 2.10 failure `EpsAProp210Bad` (threshold `2A`, tolerance `ε^{α/2}`) has outer probability
`≤ (Cfail + 2) ε^{α/2}` (small meshes by (4.20) and `2ε^α ≤ ε^{α/2}`, the others since the bound exceeds one). -/
theorem epsA_prop210Bad_le_of_prop410Bad
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) {V : Set ℂ} {f : ℂ → ℝ}
    {A α Cfail : ℝ} (hV : MeasurableSet V) (hα : 0 < α) (hCfail : 0 ≤ Cfail)
    (hbound : P (BundleSec4.Prop410Bad η ε V f A (ε ^ α)) ≤ ENNReal.ofReal (Cfail * ε ^ α)) :
    P (EpsAProp210Bad bm η ε V f (2 * A) (ε ^ (α / 2))) ≤ ENNReal.ofReal ((Cfail + 2) * ε ^ (α / 2)) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hε0 := hε.1
  have ht0 : 0 < ε ^ (α / 2) := Real.rpow_pos_of_pos hε0 _
  have htt : ε ^ α = ε ^ (α / 2) * ε ^ (α / 2) := by rw [← Real.rpow_add hε0, add_halves]
  have hpow : ε ^ α ≤ ε ^ (α / 2) := Real.rpow_le_rpow_of_exponent_ge hε0 hε.2.le (by linarith)
  by_cases hsmall : 2 * ε ^ α ≤ ε ^ (α / 2)
  · -- small mesh: (4.20) and absorption of the doubled tolerance
    set N₁ : Set Ω := {ω | ¬ ∃ (hlf : MatedCRT.IsLocallyFinite ε (bm ω))
      (H : CellularEmbedding (MatedCRT.graph ε (bm ω) hlf) 0),
        ∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)} with hN₁
    set N₂ : Set Ω := {ω | ¬ ∀ (hlf : MatedCRT.IsLocallyFinite ε (bm ω))
      (H : CellularEmbedding (MatedCRT.graph ε (bm ω) hlf) 0),
      (∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) →
        ∀ᵐ z ∂volume, GMS3.uDens H z ≤ 2 * GMS4b.uStar ε (η ω) z} with hN₂
    have hN₁0 : P N₁ = 0 := ae_iff.mp (epsA_ae_exists_cellularEmbedding D hε0)
    have hN₂0 : P N₂ = 0 := ae_iff.mp (epsA_ae_uDens_le_two_uStar D hε0)
    have hsub : EpsAProp210Bad bm η ε V f (2 * A) (ε ^ (α / 2)) ⊆
        BundleSec4.Prop410Bad η ε V f A (ε ^ α) ∪ (N₁ ∪ N₂) := by
      intro ω hbad
      by_contra hcon
      simp only [mem_union, not_or] at hcon
      obtain ⟨h410, hn₁, hn₂⟩ := hcon
      have hex : ∃ (hlf : MatedCRT.IsLocallyFinite ε (bm ω))
          (H : CellularEmbedding (MatedCRT.graph ε (bm ω) hlf) 0),
            ∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x) := not_not.mp hn₁
      have hcmp := not_not.mp hn₂
      have hgood410 : (∫⁻ z in V, ENNReal.ofReal (f z) * GMS4b.uStar ε (η ω) z) ≤
          ENNReal.ofReal A * (∫⁻ z in V, ENNReal.ofReal (f z)) + ENNReal.ofReal (ε ^ α) :=
        not_not.mp h410
      apply hbad
      refine ⟨hex, fun hlf H hcell => ?_⟩
      have hb := GMS4.prop210Bound_of_localized_integral_ae H hV f
        (fun z => GMS4b.uStar ε (η ω) z) (ae_restrict_of_ae (hcmp hlf H hcell)) hgood410
      exact BundleSec4.bundle_prop210Bound_mono_tol H hsmall hb
    calc P (EpsAProp210Bad bm η ε V f (2 * A) (ε ^ (α / 2)))
        ≤ P (BundleSec4.Prop410Bad η ε V f A (ε ^ α)) + (P N₁ + P N₂) :=
          (measure_mono hsub).trans ((measure_union_le _ _).trans
            (add_le_add le_rfl (measure_union_le _ _)))
      _ = P (BundleSec4.Prop410Bad η ε V f A (ε ^ α)) := by rw [hN₁0, hN₂0, add_zero, add_zero]
      _ ≤ ENNReal.ofReal (Cfail * ε ^ α) := hbound
      _ ≤ ENNReal.ofReal ((Cfail + 2) * ε ^ (α / 2)) := by
          apply ENNReal.ofReal_le_ofReal
          calc Cfail * ε ^ α ≤ Cfail * ε ^ (α / 2) := mul_le_mul_of_nonneg_left hpow hCfail
            _ ≤ (Cfail + 2) * ε ^ (α / 2) := mul_le_mul_of_nonneg_right (by linarith) ht0.le
  · -- large mesh: the bound exceeds one
    have hhalf : 1 / 2 < ε ^ (α / 2) := by
      rw [htt, not_le] at hsmall
      nlinarith
    calc P (EpsAProp210Bad bm η ε V f (2 * A) (ε ^ (α / 2))) ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal ((Cfail + 2) * ε ^ (α / 2)) := by
          apply ENNReal.ofReal_le_ofReal
          nlinarith

/-- **[18] Proposition 2.10 from Proposition 4.10 and (4.20) at every real mesh**, for the coupling's mated-CRT
maps: threshold `2A`, exponent `α/2`, rate `Cfail + 2`, the same `β`. -/
theorem epsA_prop210At_of_prop410At
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) {ρ C : ℝ}
    (h : EpsAProp410At P η ρ C) : EpsAProp210At P bm η ρ C := by
  obtain ⟨β, A, α, Cfail, hβ, hα, hA, hCfail, h⟩ := h
  refine ⟨β, 2 * A, α / 2, Cfail + 2, hβ, by positivity, by positivity, by positivity,
    fun ε hε V f hadm => ?_⟩
  exact epsA_prop210Bad_le_of_prop410Bad D hε hadm.2.2.2.2.2.2.1.measurableSet hα hCfail (h ε hε V f hadm)

/-- **[18] Proposition 2.10 at every real mesh `ε ∈ (0, 1)`, every `ρ ∈ (0, 1)` and every `C > 1`, for the
mated-CRT map of every frozen coupling on a standard Borel space** (no premise). -/
theorem epsA_prop210At (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) {ρ C : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hC : 1 < C) :
    EpsAProp210At P bm η ρ C :=
  epsA_prop210At_of_prop410At D (epsA_prop410At D hstd hγ hρ0 hρ1 hC)

end Coupling

end MatedCRTHarmonic.GMSMain
