/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSLemma27.Consumers at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Lemma27
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Interfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Lemma31

/-!
# [18] Lemma 2.7 in the forms consumed by the cell-family estimate and G3

* `lemma27_cells_transfer` — [18] Lemma 2.7 at the dyadic meshes `ε_k = 2⁻ᵏ` (the cell-family estimate's `mesh`), for any family of cell maps
  `J k ω x` that agrees almost surely with the model cells `η([ε_k(x−1), ε_k x])` along a measure-preserving map
  `e : Ω' → M.Ω` (the cell-model identification of a random cell family).
* `lemma27CellDiam_of_cellModel` — the cell-family estimate's interface `CellFamily.Lemma27CellDiam F q ρ` (closed disk, the closed-disk formulation: Lemma 2.7
  applied at `ρ' = (1+ρ)/2 ∈ (ρ, 1)`), for a `RandomCellFamily` whose cells are the model's cells.
* `cellDiamBound_of_cellModel`, `ae_eventually_cellDiamBound_of_cellModel` — G3's event `GMS3.CellDiamBound` with
  `δ = ε_k^q`: with probability `≥ 1 − C ε_k^α` for every `α < α(q, γ)`, and almost surely for all large `k`
  (Borel–Cantelli, `Σ_k ε_k^α < ∞`).

The identification hypotheses (`he`, `hcell`) are the definition of "the family's cells are the model's cells" (the
same identification as the cell-family estimate's `PeanosphereG0`, `H'.cell x = η '' Icc (mesh k * (x − 1)) (mesh k * x)`), not a proof
step. The inputs are those of `lemma27`: `SegmentsContainBalls M` ( bundle input), `GMCLowerTail γ` and
`AreaDominatesWholePlaneGFF M` (SLE-free, to prove).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMSLemma27

open MatedCRTHarmonic.CellFamily (mesh RandomCellFamily Lemma27CellDiam)

theorem mesh_pos (k : ℕ) : 0 < mesh k := by
  unfold mesh; positivity

theorem mesh_lt_one {k : ℕ} (hk : k ≠ 0) : mesh k < 1 := by
  unfold mesh
  exact zpow_lt_one_of_neg₀ one_lt_two (by omega)

theorem mesh_zero : mesh 0 = 1 := by simp [mesh]

/-- `ε_k^α = (2^{−α})^k`. -/
theorem mesh_rpow_eq (k : ℕ) (α : ℝ) : mesh k ^ α = ((2 : ℝ) ^ (-α)) ^ k := by
  calc mesh k ^ α = ((2 : ℝ) ^ (((-(k : ℤ) : ℤ)) : ℝ)) ^ α := by
        rw [Real.rpow_intCast]; rfl
    _ = (2 : ℝ) ^ ((((-(k : ℤ) : ℤ)) : ℝ) * α) := (Real.rpow_mul zero_le_two _ _).symm
    _ = ((2 : ℝ) ^ (-α)) ^ (k : ℝ) := by
        rw [← Real.rpow_mul zero_le_two]; congr 1; push_cast; ring
    _ = ((2 : ℝ) ^ (-α)) ^ k := Real.rpow_natCast _ _

variable {γ : ℝ}

/-- **[18] Lemma 2.7 at the dyadic meshes, transferred to cell maps identified with the model's cells.** -/
theorem lemma27_cells_transfer (M : CellModel γ) (hSLE : SegmentsContainBalls M)
    (hGMC : GMCLowerTail γ) (hdom : AreaDominatesWholePlaneGFF M) (hγ : 0 < γ)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (e : Ω' → M.Ω) (he : MeasurePreserving e P' M.P) (J : ℕ → Ω' → ℤ → Set ℂ)
    (hJ : ∀ k, ∀ᵐ ω ∂P', ∀ x, J k ω x = M.cell (mesh k) (e ω) x)
    {q ρ α : ℝ} (hq : 0 < q) (hq' : q < 2 / (2 + γ) ^ 2) (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (hα : α < lemma27Exponent q γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      P' {ω | ∀ x, (J k ω x ∩ ball (0 : ℂ) ρ).Nonempty → diam (J k ω x) ≤ mesh k ^ q}ᶜ ≤
        ENNReal.ofReal (C * mesh k ^ α) := by
  obtain ⟨C, hC⟩ := lemma27_segments M hSLE hGMC hdom hγ hq hq' hρ.1 hρ.2 hα
  refine ⟨max C 1, zero_le_one.trans (le_max_right _ _), fun k => ?_⟩
  rcases eq_or_ne k 0 with rfl | hk
  · refine prob_le_one.trans ?_
    rw [mesh_zero, Real.one_rpow, mul_one, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hsub : {ω | ∀ x, (J k ω x ∩ ball (0 : ℂ) ρ).Nonempty → diam (J k ω x) ≤ mesh k ^ q}ᶜ ≤ᵐ[P']
      e ⁻¹' (segmentDiamGood M (mesh k) q ρ)ᶜ := by
    filter_upwards [hJ k] with ω hω
    intro hbad hgood
    apply hbad
    intro x hx
    rw [hω x] at hx ⊢
    exact segmentDiamGood_subset_cellDiamGood M (mesh k) q ρ hgood x hx
  calc P' {ω | ∀ x, (J k ω x ∩ ball (0 : ℂ) ρ).Nonempty → diam (J k ω x) ≤ mesh k ^ q}ᶜ
      ≤ P' (e ⁻¹' (segmentDiamGood M (mesh k) q ρ)ᶜ) := measure_mono_ae hsub
    _ ≤ M.P (segmentDiamGood M (mesh k) q ρ)ᶜ := he.measure_preimage_le _
    _ ≤ ENNReal.ofReal (C * mesh k ^ α) := hC _ ⟨mesh_pos k, mesh_lt_one hk⟩
    _ ≤ ENNReal.ofReal (max C 1 * mesh k ^ α) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (mesh_pos k).le _))

/-- **Producer of the cell-family estimate's `Lemma27CellDiam F q ρ`** ([18] Lemma 2.7 on the closed disk `B̄_ρ(0)`, applied at
`ρ' = (1+ρ)/2`; the closed-disk formulation) for a random cell family whose cells are, along a measure-preserving map `e`, almost
surely the cells `η([ε_k(x−1), ε_k x])` of the cell model, `ε_k = mesh k`. The rate is `α = α(q, γ)/2 > 0`. -/
theorem lemma27CellDiam_of_cellModel (M : CellModel γ) (hSLE : SegmentsContainBalls M)
    (hGMC : GMCLowerTail γ) (hdom : AreaDominatesWholePlaneGFF M) (hγ : 0 < γ)
    (F : RandomCellFamily) (e : F.Ω → M.Ω) (he : MeasurePreserving e F.P M.P)
    (hcell : ∀ k, ∀ᵐ ω ∂F.P, ∀ x, (F.H k ω).cell x = M.cell (mesh k) (e ω) x)
    {q ρ : ℝ} (hq : 0 < q) (hq' : q < 2 / (2 + γ) ^ 2) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Lemma27CellDiam F q ρ := by
  have hpos := lemma27Exponent_pos hγ hq hq'
  obtain ⟨C, -, hC⟩ := lemma27_cells_transfer M hSLE hGMC hdom hγ e he
    (fun k ω x => (F.H k ω).cell x) hcell hq hq' (ρ := (1 + ρ) / 2) ⟨by linarith, by linarith⟩
    (α := lemma27Exponent q γ / 2) (by linarith)
  refine ⟨lemma27Exponent q γ / 2, by linarith, C, fun k => ?_⟩
  refine one_sub_le_measure_of_compl_le ((measure_mono ?_).trans (hC k))
  refine compl_subset_compl.mpr ?_
  intro ω hω x hx
  refine hω x ?_
  obtain ⟨w, hw1, hw2⟩ := hx
  refine ⟨w, hw1, ?_⟩
  rw [mem_closedBall, dist_zero_right] at hw2
  rw [mem_ball, dist_zero_right]
  linarith

/-- **G3's `CellDiamBound` with polynomially high probability** ([18] Lemma 2.7 at the dyadic meshes): for every
`α < α(q, γ)` there is `C ≥ 0` with `P[CellDiamBound (F.H k ω) ρ (ε_k^q)] ≥ 1 − C ε_k^α` for all `k`. -/
theorem cellDiamBound_of_cellModel (M : CellModel γ) (hSLE : SegmentsContainBalls M)
    (hGMC : GMCLowerTail γ) (hdom : AreaDominatesWholePlaneGFF M) (hγ : 0 < γ)
    (F : RandomCellFamily) (e : F.Ω → M.Ω) (he : MeasurePreserving e F.P M.P)
    (hcell : ∀ k, ∀ᵐ ω ∂F.P, ∀ x, (F.H k ω).cell x = M.cell (mesh k) (e ω) x)
    {q ρ α : ℝ} (hq : 0 < q) (hq' : q < 2 / (2 + γ) ^ 2) (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (hα : α < lemma27Exponent q γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, F.P {ω | GMS3.CellDiamBound (F.H k ω) ρ (mesh k ^ q)}ᶜ ≤
      ENNReal.ofReal (C * mesh k ^ α) :=
  lemma27_cells_transfer M hSLE hGMC hdom hγ e he (fun k ω x => (F.H k ω).cell x) hcell hq hq' hρ hα

end MatedCRTHarmonic.GMSLemma27
