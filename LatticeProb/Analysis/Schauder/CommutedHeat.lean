import LatticeProb.Analysis.Schauder.IBPTwice
import LatticeProb.Analysis.Schauder.DirDerivComm
import LatticeProb.Analysis.Schauder.KernelDerivSpace
import LatticeProb.Analysis.Schauder.KernelL1

/-!
# Commuting the Laplacian of the heat kernel with a second derivative

For the heat kernel `p = p_t`, a second derivative `∂_a ∂_b` of a `C²` function `w` with bounded
derivatives can be exchanged against the Laplacian: with `Δ = Σ_i ∂_i²`,
`∫ Δp(y) ∂_a∂_b w(x - y) dy = ∫ ∂_a∂_b p(y) Δw(x - y) dy`.

For each coordinate direction `e_i`, two integrations by parts move `∂_a∂_b` from `w` onto
`∂_i² p`; since `p` is smooth the derivatives commute, so `∂_b∂_a∂_i² p = ∂_i²∂_b∂_a p`; and two
integrations by parts in the opposite direction move `∂_i²` from `∂_b∂_a p` onto `w`. Summing over
`i` turns `∂_i²` into the Laplacian on both sides.
-/

namespace LatticeProb.Analysis.Schauder

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The Laplacian of the heat kernel can be traded for the Laplacian of a `C²` function with
bounded derivatives: `∫ Δp_t(y) ∂_a∂_b w(x − y) dy = ∫ ∂_a∂_b p_t(y) Δw(x − y) dy`. The third and
fourth derivatives of the heat kernel are assumed integrable. -/
theorem integral_laplacianSum_heatKernel_mul_comp_sub {t : ℝ} (ht : 0 < t) {w : Euc d → ℝ}
    (hw : BoundedDerivs 2 w)
    (h3 : ∀ a b c : Euc d,
      Integrable (dirDeriv a (dirDeriv b (dirDeriv c (heatKernel d t)))))
    (h4 : ∀ a b c e : Euc d,
      Integrable (dirDeriv a (dirDeriv b (dirDeriv c (dirDeriv e (heatKernel d t))))))
    (x a b : Euc d) :
    ∫ y, laplacianSum (heatKernel d t) y * dirDeriv a (dirDeriv b w) (x - y) =
      ∫ y, dirDeriv a (dirDeriv b (heatKernel d t)) y * laplacianSum w (x - y) := by
  have hp : ContDiff ℝ (⊤ : ℕ∞) (heatKernel d t) :=
    (contDiff_heatKernel t).of_le le_top
  have hsub : Continuous fun y : Euc d => x - y := continuous_const.sub continuous_id
  have hsm : ∀ g : Euc d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → ContDiff ℝ 2 g :=
    fun g hg => hg.of_le (WithTop.coe_le_coe.2 le_top)
  have hcomm : ∀ (g : Euc d → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → ∀ e e' : Euc d,
      dirDeriv e (dirDeriv e' g) = dirDeriv e' (dirDeriv e g) :=
    fun g hg e e' => dirDeriv_comm (hsm g hg) e e'
  have hw2 : ContDiff ℝ 2 w := by exact_mod_cast hw.1
  -- an integrable kernel against a bounded continuous function composed with `x - ·`
  have hmul : ∀ K : Euc d → ℝ, Integrable K → ∀ g : Euc d → ℝ, BoundedDerivs 0 g →
      Integrable (fun y => K y * g (x - y)) := by
    intro K hK g hg
    obtain ⟨A, hA⟩ := hg.exists_abs_le
    exact hK.mul_bdd (hg.continuous.comp hsub).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hA (x - y))
  have hG : BoundedDerivs 0 (dirDeriv a (dirDeriv b w)) := (hw.dirDeriv b).dirDeriv a
  have hKab : Integrable (dirDeriv b (dirDeriv a (heatKernel d t))) :=
    integrable_dirDeriv_dirDeriv_heatKernel ht a b
  -- the identity for a single coordinate direction
  have key : ∀ e : Euc d,
      ∫ y, dirDeriv e (dirDeriv e (heatKernel d t)) y * dirDeriv a (dirDeriv b w) (x - y) =
        ∫ y, dirDeriv b (dirDeriv a (heatKernel d t)) y * dirDeriv e (dirDeriv e w) (x - y) := by
    intro e
    have hs1 : ContDiff ℝ (⊤ : ℕ∞) (dirDeriv e (heatKernel d t)) := contDiff_dirDeriv hp e
    have hs2 : ContDiff ℝ (⊤ : ℕ∞) (dirDeriv e (dirDeriv e (heatKernel d t))) :=
      contDiff_dirDeriv hs1 e
    have hs1' : ContDiff ℝ (⊤ : ℕ∞) (dirDeriv a (heatKernel d t)) := contDiff_dirDeriv hp a
    have hs2' : ContDiff ℝ (⊤ : ℕ∞) (dirDeriv b (dirDeriv a (heatKernel d t))) :=
      contDiff_dirDeriv hs1' b
    -- move `∂_a ∂_b` from `w` onto `∂_e² p`
    have step1 := integral_mul_dirDeriv_dirDeriv_comp_sub (hsm _ hs2)
      (integrable_dirDeriv_dirDeriv_heatKernel ht e e) (fun e' => h3 e' e e)
      (fun e₁ e₂ => h4 e₂ e₁ e e) hw x a b
    -- commute the derivatives of the smooth kernel
    have hcom : dirDeriv b (dirDeriv a (dirDeriv e (dirDeriv e (heatKernel d t)))) =
        dirDeriv e (dirDeriv e (dirDeriv b (dirDeriv a (heatKernel d t)))) := by
      rw [hcomm _ hs1 a e, hcomm _ hp a e, hcomm (dirDeriv e (dirDeriv a (heatKernel d t)))
        (contDiff_dirDeriv hs1' e) b e, hcomm _ hs1' b e]
    -- move `∂_e²` from `∂_b ∂_a p` onto `w`
    have step2 := integral_mul_dirDeriv_dirDeriv_comp_sub (hsm _ hs2') hKab
      (fun e' => h3 e' b a) (fun e₁ e₂ => h4 e₂ e₁ b a) hw x e e
    rw [step1, hcom]
    exact step2.symm
  have hlapp : ∀ y, laplacianSum (heatKernel d t) y = ∑ i : Fin d,
      dirDeriv (EuclideanSpace.single i 1) (dirDeriv (EuclideanSpace.single i 1)
        (heatKernel d t)) y := fun y => laplacianSum_eq_sum_dirDeriv_of_contDiff (hsm _ hp) y
  have hlapw : ∀ z, laplacianSum w z = ∑ i : Fin d,
      dirDeriv (EuclideanSpace.single i 1) (dirDeriv (EuclideanSpace.single i 1) w) z :=
    fun z => laplacianSum_eq_sum_dirDeriv_of_contDiff hw2 z
  have hL : ∫ y, laplacianSum (heatKernel d t) y * dirDeriv a (dirDeriv b w) (x - y) =
      ∑ i : Fin d, ∫ y, dirDeriv (EuclideanSpace.single i 1)
        (dirDeriv (EuclideanSpace.single i 1) (heatKernel d t)) y *
          dirDeriv a (dirDeriv b w) (x - y) := by
    simp_rw [hlapp, Finset.sum_mul]
    exact integral_finsetSum _ fun i _ =>
      hmul _ (integrable_dirDeriv_dirDeriv_heatKernel ht _ _) _ hG
  have hR : ∫ y, dirDeriv b (dirDeriv a (heatKernel d t)) y * laplacianSum w (x - y) =
      ∑ i : Fin d, ∫ y, dirDeriv b (dirDeriv a (heatKernel d t)) y *
        dirDeriv (EuclideanSpace.single i 1) (dirDeriv (EuclideanSpace.single i 1) w) (x - y) := by
    simp_rw [hlapw, Finset.mul_sum]
    exact integral_finsetSum _ fun i _ =>
      hmul _ hKab _ ((hw.dirDeriv _).dirDeriv _)
  rw [hL, Finset.sum_congr rfl fun i _ => key _, ← hR, hcomm _ hp a b]

end

end LatticeProb.Analysis.Schauder
