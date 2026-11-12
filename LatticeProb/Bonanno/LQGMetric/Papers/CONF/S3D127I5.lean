/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127I5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127I4

/-!
# CONF Lemma 2.10 at the domains `confU` (the leaf `CONFLem2_10AtConfU`, D127, P2-HEATI)

`confLem2_10AtConfU_of hL1`: from (L1) in the form of `zbHeatRepr_confU` (P2-HEATF), the model
`confZBCoarseModel_of` (S3D127I4) with (L2) `coarseKer_holder_confU` (S3D127G6) and
`confLem2_10At_of_model` (S3Sec3W2) give CONF Lemma 2.10 (C:712–742) at every
`U = confU r δ z T`. (L1) and (L2) are proved for `r, δ > 0`; for the other parameters
`confU r δ z T` is `∅` (`r ≤ 0`, the annulus is empty) or the full annulus `confU r 1 z ∅`
(`δ ≤ 0`: the "squares" of side `δ r ≤ 0` are empty or the centre `z`), where (L1)–(L2) are
trivial resp. the case `δ = 1`, `T = ∅`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal

namespace LQGMetric.CONF.ZBM

open KilledHeat WhiteNoise DZZ Blueprint

lemma zbHeatRepr_empty : ZBHeatRepr ∅ := by
  intro φ ψ
  have h : ∀ μ, QuantumZipper.dualNormSq ∅ (QuantumZipper.zeroSpace ∅) μ = 0 := fun μ => by
    simp [QuantumZipper.dualNormSq, QuantumZipper.dirichletEnergyOn]
  simp [QuantumZipper.zeroGFFTestCov, QuantumZipper.dualCov, h]

lemma coarseKerHolder_empty : CoarseKerHolder ∅ := fun t ht =>
  ⟨0, 1, le_rfl, one_pos, fun x x' => by
    rw [wndKernelL2_eq_zero_of_not_mem (Ioi_subset_Ioi ht.le) (notMem_empty x),
      wndKernelL2_eq_zero_of_not_mem (Ioi_subset_Ioi ht.le) (notMem_empty x')]
    simp⟩

lemma confU_eq_empty {r : ℝ} (hr : r ≤ 0) (δ : ℝ) (z : ℂ) (T : Finset (ℤ × ℤ)) :
    confU r δ z T = ∅ := by
  ext w
  simp only [mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, h2⟩, -⟩
  linarith

lemma confU_eq_annulus {r δ : ℝ} (hr : 0 < r) (hδ : δ ≤ 0) (z : ℂ) (T : Finset (ℤ × ℤ)) :
    confU r δ z T = confU r 1 z ∅ := by
  ext w
  simp only [confU, mem_diff, Finset.notMem_empty, iUnion_of_empty, iUnion_empty,
    notMem_empty, not_false_eq_true, and_true, mem_iUnion, not_exists, and_iff_left_iff_imp]
  intro hw k _ hk
  have hε : δ * r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hδ hr.le
  obtain ⟨a1, a2, a3, a4⟩ := hk
  have h0 : δ * r = 0 := by nlinarith
  rw [h0] at a1 a2 a3 a4
  have hre : w.re = z.re := by linarith
  have him : w.im = z.im := by linarith
  have hwz : w = z := Complex.ext hre him
  have := hw.1
  rw [hwz, sub_self, norm_zero] at this
  linarith

/-- **CONF Lemma 2.10 at the domains `confU`** from (L1) (`zbHeatRepr_confU`) -/
theorem confLem2_10AtConfU_of
    (hL1 : ∀ r δ : ℝ, 0 < r → 0 < δ → ∀ (z : ℂ) (T : Finset (ℤ × ℤ)),
      ZBHeatRepr (confU r δ z T)) :
    CONFLem2_10AtConfU := by
  intro r δ z T
  refine confLem2_10At_of_model ?_
  have key : ∀ r δ : ℝ, ∀ T : Finset (ℤ × ℤ), 0 < r → 0 < δ →
      CONFZBCoarseModel (toOpens (confU r δ z T) (isOpen_confU r δ z T)) := fun r δ T hr hδ =>
    confZBCoarseModel_of (isOpen_confU r δ z T) (by positivity : (0 : ℝ) ≤ 4 * r)
      (confU_subset_ball r δ z T) (hL1 r δ hr hδ z T)
      (fun t ht => coarseKer_holder_confU hr hδ z T ht)
  rcases le_or_gt r 0 with hr | hr
  · have e : toOpens (confU r δ z T) (isOpen_confU r δ z T) = toOpens ∅ isOpen_empty :=
      TopologicalSpace.Opens.ext (confU_eq_empty hr δ z T)
    rw [e]
    exact confZBCoarseModel_of isOpen_empty le_rfl (empty_subset (ball (0 : ℂ) 0))
      zbHeatRepr_empty coarseKerHolder_empty
  rcases le_or_gt δ 0 with hδ | hδ
  · have e : toOpens (confU r δ z T) (isOpen_confU r δ z T) =
        toOpens (confU r 1 z ∅) (isOpen_confU r 1 z ∅) :=
      TopologicalSpace.Opens.ext (confU_eq_annulus hr hδ z T)
    rw [e]
    exact key r 1 ∅ hr one_pos
  · exact key r δ T hr hδ

end LQGMetric.CONF.ZBM
