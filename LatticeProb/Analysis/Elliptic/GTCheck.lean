import LatticeProb.External.GilbargTrudinger
import LatticeProb.Analysis.Elliptic.Examples

/-!
# Sanity checks for the cited elliptic inputs

The nonzero quadratic solution on the Euclidean unit ball satisfies the input hypotheses.
Application lemmas exercise each candidate proposition explicitly; they do not prove the
cited inputs. The example's finite second order norm is proved independently.
-/

namespace LatticeProb.Elliptic

open LatticeProb.External
open LatticeProb.Euclidean.Lattice
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-- Restriction to a smaller set decreases the supremum norm. -/
theorem supNorm_mono {S T : Set (Fin d → ℝ)} (hST : S ⊆ T)
    (f : (Fin d → ℝ) → ℝ) : supNorm S f ≤ supNorm T f := by
  exact iSup_le fun x => iSup_le fun hx =>
    le_iSup_of_le x (le_iSup_of_le (hST hx) le_rfl)

/-- Restriction to a smaller set decreases the Euclidean Hölder seminorm. -/
theorem holderSeminorm_mono (σ : ℝ) {S T : Set (Fin d → ℝ)} (hST : S ⊆ T)
    (f : (Fin d → ℝ) → ℝ) : holderSeminorm σ S f ≤ holderSeminorm σ T f := by
  exact iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy =>
    iSup_le fun hxy => le_iSup_of_le x (le_iSup_of_le (hST hx)
      (le_iSup_of_le y (le_iSup_of_le (hST hy) (le_iSup_of_le hxy le_rfl))))

/-- Restriction to a smaller set decreases the zeroth order Hölder norm. -/
theorem c0HolderNorm_mono (σ : ℝ) {S T : Set (Fin d → ℝ)} (hST : S ⊆ T)
    (f : (Fin d → ℝ) → ℝ) : c0HolderNorm σ S f ≤ c0HolderNorm σ T f :=
  add_le_add (supNorm_mono hST f) (holderSeminorm_mono σ hST f)

/-- The quadratic solution has finite second order norm independently of any cited input. -/
theorem quadratic_c2HolderNorm_lt_top (σ : ℝ) :
    c2HolderNorm σ (unitBall d) (fun x => 1 - ∑ k, x k ^ 2) < ⊤ := by
  have heq : (fun x : Fin d → ℝ => 1 - ∑ k, x k ^ 2) =
      (fun x => 1 + (-1) * ∑ k, x k ^ 2) := by
    ext x
    ring
  rw [heq]
  exact c2HolderNorm_affine_sum_sq_lt_top σ 1 (-1) (isBounded_radius_sublevel 1)

/-- The quadratic datum is bounded on the open ball by its independently finite closure norm. -/
theorem quadratic_datum_supNorm_lt_top {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    (μ a₀ : ℝ) :
    supNorm (unitBall d)
      (fun x => μ * (1 - ∑ k, x k ^ 2) + 2 * d * a₀) < ⊤ := by
  have h := quadratic_datum_c0HolderNorm_lt_top (d := d) hσ hσ1 μ a₀
  exact lt_of_le_of_lt ((supNorm_mono subset_closure _).trans le_self_add) h

/-- The unit ball and a nonzero quadratic satisfy all solution and norm hypotheses in
Theorems 6.19, 6.6 and 3.7, with positive diffusion and nonnegative mass. -/
theorem quadratic_gt_hypotheses (hd : 2 ≤ d) {σ μ a₀ : ℝ} (hσ : 0 < σ)
    (hσ1 : σ < 1) (hμ : 0 ≤ μ) (ha₀ : 0 < a₀) :
    IsC2HolderDomain σ (unitBall d) ∧
      IsClassicalDirichletSolution (unitBall d) μ a₀
        (fun x => μ * (1 - ∑ k, x k ^ 2) + 2 * d * a₀)
        (fun x => 1 - ∑ k, x k ^ 2) ∧
      c0HolderNorm σ (closure (unitBall d))
        (fun x => μ * (1 - ∑ k, x k ^ 2) + 2 * d * a₀) < ⊤ ∧
      c2HolderNorm σ (unitBall d) (fun x => 1 - ∑ k, x k ^ 2) < ⊤ ∧
      supNorm (unitBall d)
        (fun x => μ * (1 - ∑ k, x k ^ 2) + 2 * d * a₀) < ⊤ ∧
      (0 : Fin d → ℝ) ∈ unitBall d ∧
      (1 - ∑ k : Fin d, (0 : Fin d → ℝ) k ^ 2) = 1 ∧
      0 < μ * (1 - ∑ k : Fin d, (0 : Fin d → ℝ) k ^ 2) + 2 * d * a₀ := by
  obtain ⟨hU, hsol, hf, hmem, hu, hfpos⟩ :=
    quadratic_nonvacuity (by omega : 1 ≤ d) hσ hσ1 hμ ha₀
  exact ⟨hU, hsol, hf, quadratic_c2HolderNorm_lt_top σ,
    quadratic_datum_supNorm_lt_top hσ hσ1 μ a₀, hmem, hu, hfpos⟩

/-- Unit diffusion and zero mass lie in every permitted coefficient interval. -/
theorem unit_coefficients_mem {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    (1 : ℝ) ∈ Set.Icc Λ⁻¹ Λ ∧ (0 : ℝ) ∈ Set.Icc 0 Λ :=
  ⟨⟨inv_le_one_of_one_le₀ hΛ, hΛ⟩, ⟨le_rfl, zero_le_one.trans hΛ⟩⟩

/-- The regularity input discharges the a priori regularity premise of the Schauder input. -/
theorem dirichlet_schauder_of_gt (hreg : GilbargTrudingerBoundaryRegularity)
    (hest : GilbargTrudingerSchauderEstimate) (hd : 2 ≤ d) {σ : ℝ}
    (hσ : 0 < σ) (hσ1 : σ < 1) {U : Set (Fin d → ℝ)}
    (hU : IsC2HolderDomain σ U) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a₀ μ : ℝ),
      a₀ ∈ Set.Icc Λ⁻¹ Λ → μ ∈ Set.Icc 0 Λ →
      ∀ (f u : (Fin d → ℝ) → ℝ), c0HolderNorm σ (closure U) f < ⊤ →
        IsClassicalDirichletSolution U μ a₀ f u →
        c2HolderNorm σ U u ≤
          ENNReal.ofReal C * (supNorm U u + c0HolderNorm σ (closure U) f) := by
  obtain ⟨C, hC, hbound⟩ := hest d hd σ hσ hσ1 U hU Λ hΛ
  refine ⟨C, hC, fun a₀ μ ha₀ hμ f u hf hsol => ?_⟩
  have hapos : 0 < a₀ := (inv_pos.mpr (zero_lt_one.trans_le hΛ)).trans_le ha₀.1
  exact hbound a₀ μ ha₀ hμ f u hf hsol
    (hreg d hd σ hσ hσ1 U hU a₀ μ hapos hμ.1 f u hf hsol)

/-- Applying the regularity input to the actual nonzero quadratic is well typed. -/
theorem quadratic_regularity_of_gt (hGT : GilbargTrudingerBoundaryRegularity)
    (hd : 2 ≤ d) {σ μ a₀ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    (hμ : 0 ≤ μ) (ha₀ : 0 < a₀) :
    c2HolderNorm σ (unitBall d) (fun x => 1 - ∑ k, x k ^ 2) < ⊤ :=
  hGT d hd σ hσ hσ1 (unitBall d) (isC2HolderDomain_unitBall σ) a₀ μ ha₀ hμ
    _ _ (quadratic_datum_c0HolderNorm_lt_top hσ hσ1 μ a₀)
    (quadratic_isClassicalDirichletSolution μ a₀)

/-- The Schauder input supplies one constant for all admissible quadratic equations. -/
theorem quadratic_schauder_of_gt (hGT : GilbargTrudingerSchauderEstimate)
    (hd : 2 ≤ d) {σ Λ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a₀ μ : ℝ),
      a₀ ∈ Set.Icc Λ⁻¹ Λ → μ ∈ Set.Icc 0 Λ →
      c2HolderNorm σ (unitBall d) (fun x => 1 - ∑ k, x k ^ 2) ≤
        ENNReal.ofReal C * (supNorm (unitBall d) (fun x => 1 - ∑ k, x k ^ 2) +
          c0HolderNorm σ (closure (unitBall d))
            (fun x => μ * (1 - ∑ k, x k ^ 2) + 2 * d * a₀)) := by
  obtain ⟨C, hC, hbound⟩ :=
    hGT d hd σ hσ hσ1 (unitBall d) (isC2HolderDomain_unitBall σ) Λ hΛ
  exact ⟨C, hC, fun a₀ μ ha₀ hμ => hbound a₀ μ ha₀ hμ _ _
    (quadratic_datum_c0HolderNorm_lt_top hσ hσ1 μ a₀)
    (quadratic_isClassicalDirichletSolution μ a₀) (quadratic_c2HolderNorm_lt_top σ)⟩

/-- The supremum input gives the correct inverse diffusion factor, uniformly in the mass. -/
theorem quadratic_sup_of_gt (hGT : GilbargTrudingerSupEstimate) (hd : 2 ≤ d)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a₀ μ : ℝ), 0 < a₀ → 0 ≤ μ →
      supNorm (unitBall d) (fun x => 1 - ∑ k, x k ^ 2) ≤
        ENNReal.ofReal (C / a₀) * supNorm (unitBall d)
          (fun x => μ * (1 - ∑ k, x k ^ 2) + 2 * d * a₀) := by
  have hU := isC2HolderDomain_unitBall (d := d) σ
  obtain ⟨C, hC, hbound⟩ := hGT d hd (unitBall d) hU.1 hU.2.1 hU.2.2.1
  exact ⟨C, hC, fun a₀ μ ha₀ hμ => hbound a₀ μ ha₀ hμ _ _
    (quadratic_datum_supNorm_lt_top hσ hσ1 μ a₀)
    (quadratic_isClassicalDirichletSolution μ a₀)⟩

/-- The extension input applies to the quadratic in any open neighborhood of the closed ball. -/
theorem quadratic_extension_of_gt (hGT : GilbargTrudingerHolderExtension)
    (hd : 2 ≤ d) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    {U' : Set (Fin d → ℝ)} (hU' : IsOpen U') (hsub : closure (unitBall d) ⊆ U') :
    ∃ (C : ℝ) (v : (Fin d → ℝ) → ℝ), 0 < C ∧
      ContDiff ℝ 2 v ∧ HasCompactSupport v ∧ tsupport v ⊆ U' ∧
        Set.EqOn v (fun x => 1 - ∑ k, x k ^ 2) (unitBall d) ∧
        c2HolderNorm σ U' v ≤ ENNReal.ofReal C *
          c2HolderNorm σ (unitBall d) (fun x => 1 - ∑ k, x k ^ 2) := by
  obtain ⟨C, hC, hext⟩ :=
    hGT d hd σ hσ hσ1 (unitBall d) (isC2HolderDomain_unitBall σ) U' hU' hsub
  obtain ⟨v, hv⟩ := hext _ (quadratic_isClassicalDirichletSolution 0 1).1
    (quadratic_c2HolderNorm_lt_top σ)
  exact ⟨C, v, hC, hv⟩

end

end LatticeProb.Elliptic
