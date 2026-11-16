import LatticeProb.Analysis.Elliptic.HolderTrace
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Regularity of Hölder jets on a closed half-space

Continuous traces of coordinate derivatives determine derivatives on the closure.
-/

namespace LatticeProb.Elliptic.HolderExtension

open Set Filter LatticeProb.Euclidean.Lattice
open scoped Topology ENNReal NNReal ContDiff BigOperators

noncomputable section

private def jetMap {d : ℕ} (g : Fin d → E d → ℝ) (x : E d) : E d →L[ℝ] ℝ :=
  ∑ j, (g j x) • ContinuousLinearMap.proj j

private theorem jetMap_apply {d : ℕ} (g : Fin d → E d → ℝ) (x v : E d) :
    jetMap g x v = ∑ j, g j x * v j := by
  simp [jetMap]

private theorem jetMap_eq {d : ℕ} (g : Fin d → E d → ℝ) (x : E d)
    (L : E d →L[ℝ] ℝ) (h : ∀ j, g j x = L (Pi.single j 1)) :
    jetMap g x = L := by
  ext v
  rw [jetMap_apply]
  have hv : v = ∑ j : Fin d, (v j) • Pi.single j (1 : ℝ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [h j, mul_comm]

private theorem jetMap_continuousOn {d : ℕ} {s : Set (E d)}
    {g : Fin d → E d → ℝ} (hg : ∀ j, ContinuousOn (g j) s) :
    ContinuousOn (jetMap g) s := by
  unfold jetMap
  exact continuousOn_finsetSum _ (fun j _ => (hg j).smul continuousOn_const)

private theorem extend_derivative {d : ℕ} {s : Set (E d)} {f F : E d → ℝ}
    {g : Fin d → E d → ℝ}
    (hs : IsOpen s) (hc : Convex ℝ s) (hf : DifferentiableOn ℝ f s)
    (hF : ContinuousOn F (closure s)) (heq : EqOn F f s)
    (hg : ∀ j, ContinuousOn (g j) (closure s))
    (hgeq : ∀ j x, x ∈ s → g j x = partialDeriv j f x) :
    ∀ x ∈ closure s, HasFDerivWithinAt F (jetMap g x) (closure s) x := by
  have hdiff : DifferentiableOn ℝ F s := hf.congr heq
  have hderiv : ∀ x ∈ s, fderiv ℝ F x = jetMap g x := by
    intro x hx
    apply (jetMap_eq g x (fderiv ℝ F x) ?_).symm
    intro j
    rw [hgeq j x hx, partialDeriv]
    have he : F =ᶠ[𝓝 x] f := by
      filter_upwards [hs.mem_nhds hx] with y hy
      exact heq hy
    exact congrArg (fun L : E d →L[ℝ] ℝ => L (Pi.single j 1))
      (he.fderiv_eq (𝕜 := ℝ)).symm
  intro x hx
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv hdiff hc hs
  · intro y hy
    exact (hF y hy).mono subset_closure
  · have hlim := (jetMap_continuousOn hg x hx).mono subset_closure
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hderiv y hy).symm

/-- Finite Hölder norm extends twice differentiable functions to the closed half-space. -/
theorem halfSpace_contDiffOn_closure {d : ℕ} (i : Fin d) {σ : ℝ}
    (hσ : 0 < σ) (hσ' : σ < 1) (u : E d → ℝ)
    (hu : ContDiffOn ℝ 2 u (halfSpace i))
    (hn : c2HolderNorm σ (halfSpace i) u < ⊤) :
    ∃ F : E d → ℝ, ContDiffOn ℝ 2 F (closure (halfSpace i)) ∧ Set.EqOn F u (halfSpace i) := by
  have hopen : IsOpen (halfSpace i) := isOpen_lt continuous_const (continuous_apply i)
  have hconv : Convex ℝ (halfSpace i) := by
    change Convex ℝ ((LinearMap.proj i : E d →ₗ[ℝ] ℝ) ⁻¹' Set.Ioi 0)
    exact (convex_Ioi (0 : ℝ)).linear_preimage (LinearMap.proj i : E d →ₗ[ℝ] ℝ)
  have hnonempty : (interior (closure (halfSpace i))).Nonempty := by
    refine ⟨Pi.single i 1, ?_⟩
    apply interior_mono subset_closure
    rw [hopen.interior_eq]
    simp [halfSpace]
  have hunique : UniqueDiffOn ℝ (closure (halfSpace i)) :=
    uniqueDiffOn_convex hconv.closure hnonempty
  obtain ⟨f, g, h, hf, hg, hh, hfeq, hgeq, hheq⟩ :=
    halfSpace_jet_traces i hσ hσ' u hu hn
  have hdu (j : Fin d) : ContDiffOn ℝ 1 (partialDeriv j u) (halfSpace i) :=
    (hu.fderiv_of_isOpen hopen (by norm_num)).clm_apply contDiffOn_const
  have hsecond (j k : Fin d) (x : E d) (hx : x ∈ halfSpace i) :
      secondPartial j k u x = partialDeriv j (partialDeriv k u) x := by
    have hlocal := hu.contDiffAt (hopen.mem_nhds hx)
    have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
      (hlocal.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    simp only [secondPartial, partialDeriv, iteratedFDeriv_two_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    change ((fderiv ℝ (fderiv ℝ u) x) (Pi.single j 1)) (Pi.single k 1) =
      (fderiv ℝ (fun y => (fderiv ℝ u y) (Pi.single k 1)) x) (Pi.single j 1)
    rw [fderiv_clm_apply hd (differentiableAt_const (Pi.single k 1))]
    simp
  have hgdiff (j : Fin d) : ContDiffOn ℝ 1 (g j) (closure (halfSpace i)) := by
    rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
      contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hunique]
    refine ⟨by simp, jetMap (fun k => h k j), ?_, ?_⟩
    · exact contDiffOn_zero.mpr (jetMap_continuousOn (fun k => hh k j))
    · apply extend_derivative hopen hconv ((hdu j).differentiableOn (by norm_num))
        (hg j) (hgeq j) (fun k => hh k j)
      intro k x hx
      rw [hheq k j hx, hsecond k j x hx]
  have hjet : ContDiffOn ℝ 1 (jetMap g) (closure (halfSpace i)) := by
    unfold jetMap
    exact ContDiffOn.sum (fun j _ => (hgdiff j).smul contDiffOn_const)
  refine ⟨f, ?_, hfeq⟩
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hunique]
  refine ⟨by simp, jetMap g, hjet, ?_⟩
  exact extend_derivative hopen hconv (hu.differentiableOn (by norm_num)) hf hfeq hg
    (fun j x hx => hgeq j hx)

end
end LatticeProb.Elliptic.HolderExtension
