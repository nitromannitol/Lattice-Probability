import LatticeProb.Analysis.Elliptic.OneDimExistence

/-!
# One-dimensional domains and nonnegative-mass Dirichlet existence

Bounded connected open domains on the one-coordinate carrier are intervals.
Double integration supplies the zero-mass case of classical Dirichlet existence;
the positive-mass case uses the interval ODE construction.
-/

namespace LatticeProb.Elliptic

open Set Filter
open scoped Topology

noncomputable section

/-- A one-dimensional `C^{2,σ}` domain is a nonempty bounded open interval. -/
theorem eq_interval_of_isC2HolderDomain {σ : ℝ} {U : Set (Fin 1 → ℝ)}
    (hU : LatticeProb.Elliptic.IsC2HolderDomain σ U) :
    ∃ α β : ℝ, α < β ∧ U = {x : Fin 1 → ℝ | α < x 0 ∧ x 0 < β} := by
  let e : (Fin 1 → ℝ) ≃ₜ ℝ := Homeomorph.funUnique (Fin 1) ℝ
  let S : Set ℝ := e '' U
  have hopen : IsOpen S := e.isOpenMap U hU.1
  have hconn : IsConnected S := hU.2.1.image e e.continuous.continuousOn
  have hbounded : Bornology.IsBounded S :=
    hU.2.2.1.image_eval 0
  have hbelow : BddBelow S := hbounded.bddBelow
  have habove : BddAbove S := hbounded.bddAbove
  have hinterval : S = Ioo (sInf S) (sSup S) := by
    apply Subset.antisymm
    · rw [← interior_Icc]
      exact hopen.subset_interior_iff.mpr (subset_Icc_csInf_csSup hbelow habove)
    · exact hconn.Ioo_csInf_csSup_subset hbelow habove
  obtain ⟨y, hy⟩ := hconn.nonempty
  have hyinterval : sInf S < y ∧ y < sSup S := by
    rwa [hinterval] at hy
  refine ⟨sInf S, sSup S, hyinterval.1.trans hyinterval.2, ?_⟩
  ext x
  change x ∈ U ↔ e x ∈ Ioo (sInf S) (sSup S)
  rw [← hinterval]
  exact (e.injective.mem_set_image).symm


/-- Zero mass admits a scalar Dirichlet solution by taking two primitives. -/
theorem exists_scalar_dirichlet_zero {α β a : ℝ} {f : ℝ → ℝ}
    (hαβ : α < β) (ha : 0 < a) (hf : ContinuousOn f (Icc α β)) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧ v α = 0 ∧ v β = 0 ∧
      ∀ x ∈ Ioo α β, -a * deriv (deriv v) x = f x := by
  let g : ℝ → ℝ := fun x => f (projIcc α β hαβ.le x)
  have hg : Continuous g := hf.restrict.comp continuous_projIcc
  let G : ℝ → ℝ := fun x => ∫ t in α..x, g t
  let P : ℝ → ℝ := fun x => ∫ t in α..x, G t
  have hGc : ContDiff ℝ 1 G := contDiff_one_interval_primitive hg α
  have hPc : ContDiff ℝ 1 P := contDiff_one_interval_primitive hGc.continuous α
  have hG (x : ℝ) : HasDerivAt G (g x) x :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hP (x : ℝ) : HasDerivAt P (G x) x :=
    intervalIntegral.integral_hasDerivAt_right (hGc.continuous.intervalIntegrable _ _)
      hGc.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hGc.continuous.continuousAt
  have hPderiv : deriv P = G := funext fun x => (hP x).deriv
  have hPc2 : ContDiff ℝ 2 P := by
    apply (contDiff_succ_iff_deriv (n := 1)).mpr
    exact ⟨hPc.differentiable (by norm_num), by norm_num, hPderiv.symm ▸ hGc⟩
  let b : ℝ := P β / (β - α)
  let v : ℝ → ℝ := fun x => (b * (x - α) - P x) / a
  have hv (x : ℝ) : HasDerivAt v ((b - G x) / a) x := by
    simpa only [v, Pi.sub_apply, id_eq, mul_one] using
      ((((hasDerivAt_id x).sub_const α).const_mul b).sub (hP x)).div_const a
  have hvderiv : deriv v = fun x => (b - G x) / a := funext fun x => (hv x).deriv
  refine ⟨v, (by dsimp [v]; fun_prop), ?_, ?_, ?_⟩
  · simp [v, P]
  · dsimp [v, b]
    rw [div_mul_cancel₀ _ (sub_pos.mpr hαβ).ne', sub_self, zero_div]
  · intro x hx
    rw [hvderiv, (((hG x).const_sub b).div_const a).deriv]
    have hg_eq : g x = f x := by
      dsimp [g]
      rw [projIcc_of_mem hαβ.le (Ioo_subset_Icc_self hx)]
    rw [hg_eq]
    field_simp [ha.ne']


/-- Scalar interval Dirichlet existence includes zero mass. -/
theorem exists_scalar_dirichlet_nonneg {α β μ a : ℝ} {f : ℝ → ℝ}
    (hαβ : α < β) (hμ : 0 ≤ μ) (ha : 0 < a) (hf : ContinuousOn f (Icc α β)) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧ v α = 0 ∧ v β = 0 ∧
      ∀ x ∈ Ioo α β, μ * v x - a * deriv (deriv v) x = f x := by
  rcases hμ.eq_or_lt with hzero | hpos
  · subst μ
    obtain ⟨v, hvc, hvα, hvβ, hve⟩ := exists_scalar_dirichlet_zero hαβ ha hf
    refine ⟨v, hvc, hvα, hvβ, ?_⟩
    intro x hx
    simpa only [zero_mul, zero_sub, neg_mul] using hve x hx
  · exact exists_scalar_dirichlet_pos hαβ hpos ha hf

/-- Every continuous datum on a closed interval has a classical one-dimensional
Dirichlet solution for nonnegative mass and positive diffusivity. -/
theorem exists_classicalDirichletSolution_one_nonneg {α β μ a₀ : ℝ}
    {f : (Fin 1 → ℝ) → ℝ} (hαβ : α < β) (hμ : 0 ≤ μ) (ha : 0 < a₀)
    (hf : ContinuousOn f (closure {x : Fin 1 → ℝ | α < x 0 ∧ x 0 < β})) :
    ∃ u, IsClassicalDirichletSolution {x : Fin 1 → ℝ | α < x 0 ∧ x 0 < β}
      μ a₀ f u := by
  let e : (Fin 1 → ℝ) ≃L[ℝ] ℝ := ContinuousLinearEquiv.piUnique ℝ (fun _ => ℝ)
  let U : Set (Fin 1 → ℝ) := {x | α < x 0 ∧ x 0 < β}
  have hclosure : closure U = e ⁻¹' Icc α β := by
    change closure (e.toHomeomorph ⁻¹' Ioo α β) = e.toHomeomorph ⁻¹' Icc α β
    rw [← e.toHomeomorph.preimage_closure, closure_Ioo hαβ.ne]
  have hfrontier : frontier U = e ⁻¹' {α, β} := by
    change frontier (e.toHomeomorph ⁻¹' Ioo α β) = e.toHomeomorph ⁻¹' {α, β}
    rw [← e.toHomeomorph.preimage_frontier, frontier_Ioo hαβ]
  have hfc : ContinuousOn (fun t : ℝ => f (fun _ => t)) (Icc α β) := by
    apply hf.comp (show Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) by
      fun_prop).continuousOn
    intro t ht
    change (fun _ => t) ∈ closure U
    rw [hclosure]
    exact ht
  obtain ⟨v, hvc, hvα, hvβ, hve⟩ := exists_scalar_dirichlet_nonneg hαβ hμ ha hfc
  let u : (Fin 1 → ℝ) → ℝ := fun x => v (x 0)
  have huc : ContDiff ℝ 2 u := hvc.comp (by fun_prop)
  refine ⟨u, huc.contDiffOn, huc.continuous.continuousOn, ?_, ?_⟩
  · intro x hx
    change x ∈ frontier U at hx
    rw [hfrontier] at hx
    rcases hx with hx | hx
    · change x 0 = α at hx
      change v (x 0) = 0
      rw [hx, hvα]
    · change x 0 = β at hx
      change v (x 0) = 0
      rw [hx, hvβ]
  · intro x hx
    have hxconst : (fun _ : Fin 1 => x 0) = x := by
      ext i
      exact congrArg x (Subsingleton.elim 0 i)
    have hlap := laplacian_one_dim u (x 0)
    rw [hxconst] at hlap
    rw [hlap]
    change μ * v (x 0) - a₀ * deriv (deriv v) (x 0) = f x
    simpa only [hxconst] using hve (x 0) hx


end

end LatticeProb.Elliptic
