import LatticeProb.Analysis.Elliptic.OneDimDomain
import LatticeProb.External.GilbargTrudingerExistence
import Mathlib.Topology.Piecewise

/-!
# Canonical zero-extended classical Dirichlet solutions

For positive diffusivity and nonnegative mass, Hölder data on a smooth bounded
domain admit a unique globally continuous classical solution that vanishes outside
the domain. Existence in dimensions at least two uses the cited GT 6.14 input;
uniqueness there uses the cited GT 3.7 input. Dimension one uses interval ODE proofs.
-/

namespace LatticeProb.Elliptic

open Set Filter LatticeProb.Euclidean.Lattice
open scoped Topology ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-- Finite Euclidean Hölder norm with positive exponent implies continuity on its carrier. -/
theorem continuousOn_of_c0HolderNorm_lt_top {σ : ℝ} (hσ : 0 < σ)
    {S : Set (Fin d → ℝ)} {f : (Fin d → ℝ) → ℝ}
    (hf : c0HolderNorm σ S f < ⊤) : ContinuousOn f S := by
  intro x hx
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hr : Tendsto (fun y : Fin d → ℝ => radius (y - x) ^ σ)
      (𝓝[S] x) (𝓝 0) := by
    have hc : ContinuousAt (fun y : Fin d → ℝ => radius (y - x) ^ σ) x :=
      (((radius_continuous d).comp
        (continuous_id.sub continuous_const)).continuousAt).rpow_const (Or.inr hσ.le)
    have hz : radius (x - x) ^ σ = 0 := by simp [radius, hσ.ne']
    simpa only [hz] using hc.continuousWithinAt.tendsto (s := S)
  have hb : Tendsto
      (fun y : Fin d → ℝ => (holderSeminorm σ S f).toReal * radius (y - x) ^ σ)
      (𝓝[S] x) (𝓝 ((holderSeminorm σ S f).toReal * 0)) :=
    tendsto_const_nhds.mul hr
  rw [mul_zero] at hb
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _ hb
  filter_upwards [self_mem_nhdsWithin] with y hy
  simpa only [Real.dist_eq] using abs_sub_le_holderSeminorm_toReal hf hy hx

/-- The coordinate Laplacian respects subtraction at points with two derivatives. -/
theorem laplacian_sub_of_contDiffAt {u v : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    laplacian (u - v) x = laplacian u x - laplacian v x := by
  simp only [laplacian, secondPartial, iteratedFDeriv_sub_apply hu hv,
    sub_apply, Finset.sum_sub_distrib]

/-- Subtraction of two classical solutions gives the difference of their data. -/
theorem IsClassicalDirichletSolution.sub {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {μ a : ℝ} {f g u v : (Fin d → ℝ) → ℝ}
    (hu : IsClassicalDirichletSolution U μ a f u)
    (hv : IsClassicalDirichletSolution U μ a g v) :
    IsClassicalDirichletSolution U μ a (f - g) (u - v) := by
  refine ⟨hu.1.sub hv.1, hu.2.1.sub hv.2.1, ?_, ?_⟩
  · intro x hx
    simp only [Pi.sub_apply, hu.2.2.1 x hx, hv.2.2.1 x hx, sub_self]
  · intro x hx
    rw [laplacian_sub_of_contDiffAt (hu.1.contDiffAt (hU.mem_nhds hx))
      (hv.1.contDiffAt (hU.mem_nhds hx))]
    change μ * (u x - v x) - a * (laplacian u x - laplacian v x) = f x - g x
    rw [← hu.2.2.2 x hx, ← hv.2.2.2 x hx]
    ring

/-- The two classical solutions agree on the closure once their interior difference
has zero supremum norm. -/
theorem eqOn_closure_of_sub_supNorm_eq_zero {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {μ a : ℝ} {f u v : (Fin d → ℝ) → ℝ}
    (hu : IsClassicalDirichletSolution U μ a f u)
    (hv : IsClassicalDirichletSolution U μ a f v)
    (hzero : supNorm U (u - v) = 0) : EqOn u v (closure U) := by
  intro x hx
  by_cases hxin : x ∈ U
  · have hb := abs_le_supNorm_toReal
      (show supNorm U (u - v) < ⊤ by rw [hzero]; exact ENNReal.zero_lt_top) hxin
    rw [hzero, ENNReal.toReal_zero] at hb
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hb (abs_nonneg _)))
  · have hfront : x ∈ frontier U := by
      rw [hU.frontier_eq]
      exact ⟨hx, hxin⟩
    rw [hu.2.2.1 x hfront, hv.2.2.1 x hfront]

/-- On a smooth bounded domain of positive dimension, classical Dirichlet solutions
are unique on the closure, including the zero-mass case. -/
theorem IsClassicalDirichletSolution.eqOn_closure
    (h37 : LatticeProb.External.GilbargTrudingerSupEstimate)
    (hd : 1 ≤ d) {σ : ℝ} {U : Set (Fin d → ℝ)} (hU : IsC2HolderDomain σ U)
    {μ a : ℝ} (hμ : 0 ≤ μ) (ha : 0 < a) {f u v : (Fin d → ℝ) → ℝ}
    (hu : IsClassicalDirichletSolution U μ a f u)
    (hv : IsClassicalDirichletSolution U μ a f v) : EqOn u v (closure U) := by
  have hdiff : IsClassicalDirichletSolution U μ a (fun _ => 0) (u - v) := by
    have h := hu.sub hU.1 hv
    have hdata : f - f = fun _ => 0 := by
      ext x
      exact sub_self (f x)
    rw [hdata] at h
    exact h
  have hz : supNorm U (fun _ : (Fin d → ℝ) => (0 : ℝ)) = 0 := by
    simp [supNorm]
  apply eqOn_closure_of_sub_supNorm_eq_zero hU.1 hu hv
  apply le_antisymm _ zero_le
  by_cases hone : d = 1
  · subst d
    obtain ⟨α, β, hαβ, hinterval⟩ := eq_interval_of_isC2HolderDomain hU
    rw [hinterval] at hdiff hz ⊢
    have hb := supNorm_le_one_dim_dirichlet hαβ hμ ha
      (show supNorm {x : Fin 1 → ℝ | α < x 0 ∧ x 0 < β} (fun _ => 0) < ⊤ by
        rw [hz]; exact ENNReal.zero_lt_top) hdiff
    simpa only [hz, mul_zero] using hb
  · have htwo : 2 ≤ d := by omega
    obtain ⟨C, _, hsup⟩ := h37 d htwo U hU.1 hU.2.1 hU.2.2.1
    have hb := hsup a μ ha hμ (fun _ => 0) (u - v)
      (by rw [hz]; exact ENNReal.zero_lt_top) hdiff
    simpa only [hz, mul_zero] using hb

/-- Zero extension of a classical solution is continuous globally and preserves
the full classical equation and boundary regularity. -/
theorem IsClassicalDirichletSolution.zero_extension {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) {μ a : ℝ} {f u : (Fin d → ℝ) → ℝ}
    (hu : IsClassicalDirichletSolution U μ a f u) :
    ∃ v, IsClassicalDirichletSolution U μ a f v ∧ Continuous v ∧
      (∀ x ∉ U, v x = 0) ∧ EqOn v u (closure U) := by
  classical
  let v : (Fin d → ℝ) → ℝ := U.piecewise u (fun _ => 0)
  have hvc : Continuous v :=
    continuous_piecewise hu.2.2.1 hu.2.1 continuousOn_const
  have heq : EqOn v u (closure U) := by
    intro x hx
    by_cases hxin : x ∈ U
    · exact piecewise_eq_of_mem U u (fun _ => 0) hxin
    · have hfront : x ∈ frontier U := by
        rw [hU.frontier_eq]
        exact ⟨hx, hxin⟩
      simp only [v, piecewise_eq_of_notMem U u (fun _ => 0) hxin,
        hu.2.2.1 x hfront]
  refine ⟨v, ⟨hu.1.congr (fun x hx => heq (subset_closure hx)),
    hvc.continuousOn, ?_, ?_⟩, hvc, ?_, heq⟩
  · intro x hx
    rw [heq (frontier_subset_closure hx), hu.2.2.1 x hx]
  · intro x hx
    have hevent : v =ᶠ[𝓝 x] u := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact heq (subset_closure hy)
    have hlap : laplacian v x = laplacian u x := by
      unfold laplacian secondPartial
      rw [(hevent.iteratedFDeriv ℝ 2).eq_of_nhds]
    rw [heq (subset_closure hx), hlap]
    exact hu.2.2.2 x hx
  · intro x hx
    exact piecewise_eq_of_notMem U u (fun _ => 0) hx

/-- Every Hölder datum has exactly one globally continuous, literally zero-extended
classical Dirichlet solution. The only assumptions from PDE books are GT 6.14 and 3.7. -/
theorem existsUnique_zero_extended_classicalDirichletSolution
    (h614 : LatticeProb.External.GilbargTrudingerExistence)
    (h37 : LatticeProb.External.GilbargTrudingerSupEstimate)
    (hd : 1 ≤ d) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    {U : Set (Fin d → ℝ)} (hU : IsC2HolderDomain σ U)
    {μ a : ℝ} (hμ : 0 ≤ μ) (ha : 0 < a)
    {f : (Fin d → ℝ) → ℝ} (hf : c0HolderNorm σ (closure U) f < ⊤) :
    ∃! u, IsClassicalDirichletSolution U μ a f u ∧ Continuous u ∧
      ∀ x ∉ U, u x = 0 := by
  have hex : ∃ u, IsClassicalDirichletSolution U μ a f u := by
    by_cases hone : d = 1
    · subst d
      obtain ⟨α, β, hαβ, hinterval⟩ := eq_interval_of_isC2HolderDomain hU
      rw [hinterval] at hf ⊢
      exact exists_classicalDirichletSolution_one_nonneg hαβ hμ ha
        (continuousOn_of_c0HolderNorm_lt_top hσ hf)
    · exact exists_classicalDirichletSolution_of_gt h614 (by omega) hσ hσ1 hU ha hμ hf
  obtain ⟨u, hu⟩ := hex
  obtain ⟨v, hv, hvc, hvzero, _⟩ := hu.zero_extension hU.1
  refine ⟨v, ⟨hv, hvc, hvzero⟩, ?_⟩
  rintro w ⟨hw, _, hwzero⟩
  have heq := hw.eqOn_closure h37 hd hU hμ ha hv
  ext x
  by_cases hx : x ∈ closure U
  · exact heq hx
  · rw [hwzero x (fun hxin => hx (subset_closure hxin)),
      hvzero x (fun hxin => hx (subset_closure hxin))]

/-- A nonzero solution on the Euclidean unit ball satisfies the global zero-extension
carrier in every dimension, without any cited PDE input. Its value at the origin is one. -/
theorem exists_zero_extended_quadratic (d : ℕ) :
    ∃ u : (Fin d → ℝ) → ℝ,
      IsClassicalDirichletSolution (unitBall d) 1 1
        (fun x => 1 * (1 - ∑ k, x k ^ 2) + 2 * d * 1) u ∧
      Continuous u ∧ (∀ x ∉ unitBall d, u x = 0) ∧ u 0 = 1 := by
  have hU := isC2HolderDomain_unitBall (d := d) (1 / 2)
  obtain ⟨u, hu, hc, hz, heq⟩ :=
    (quadratic_isClassicalDirichletSolution (d := d) 1 1).zero_extension hU.1
  refine ⟨u, hu, hc, hz, ?_⟩
  have horigin : (0 : Fin d → ℝ) ∈ closure (unitBall d) := by
    apply subset_closure
    rw [mem_unitBall_iff]
    simp only [Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
    exact zero_lt_one
  rw [heq horigin]
  simp only [Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, sub_zero]

end

end LatticeProb.Elliptic
