import LatticeProb.Analysis.Elliptic.OneDimODE
import LatticeProb.External.GilbargTrudinger

/-!
# A supremum estimate for classical Dirichlet solutions

The estimate follows from a quadratic barrier and the maximum principle.
-/

namespace LatticeProb.External

open LatticeProb.Elliptic Set Filter
open scoped Topology ENNReal BigOperators

noncomputable section

private theorem secondPartial_nonpos_of_localMax {d : ℕ} {v : (Fin d → ℝ) → ℝ}
    {x : Fin d → ℝ} (hv : ContDiffAt ℝ 2 v x) (hm : IsLocalMax v x)
    (i : Fin d) : secondPartial i i v x ≤ 0 := by
  let e : Fin d → ℝ := Pi.single i 1
  let g : ℝ → (Fin d → ℝ) := fun t => x + t • e
  have hg (t : ℝ) : HasDerivAt g e t := by
    simpa [g] using ((hasDerivAt_id t).smul_const e).const_add x
  have hg0 : g 0 = x := by simp [g]
  have hgt : Tendsto g (𝓝 0) (𝓝 x) := by
    rw [← hg0]
    exact (hg 0).continuousAt
  have hm' : IsLocalMax (v ∘ g) 0 := by
    have hh := hgt.eventually hm
    change ∀ᶠ t in 𝓝 0, v (g t) ≤ v (g 0)
    simpa only [hg0] using hh
  have hcont : ContinuousAt (v ∘ g) 0 := by
    apply ContinuousAt.comp _ (hg 0).continuousAt
    rw [hg0]
    exact hv.continuousAt
  have heq : deriv (v ∘ g) =ᶠ[𝓝 0] fun t => fderiv ℝ v (g t) e := by
    filter_upwards [hgt.eventually (hv.eventually (by norm_num))] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hg t)).deriv
  have hdiff : DifferentiableAt ℝ (fderiv ℝ v) x :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hder : HasDerivAt (fun t => fderiv ℝ v (g t) e)
      ((fderiv ℝ (fderiv ℝ v) x e) e) 0 := by
    have hdg : DifferentiableAt ℝ (fderiv ℝ v) (g 0) := by simpa only [hg0] using hdiff
    have h := (hdg.hasFDerivAt.comp_hasDerivAt 0 (hg 0))
    have hh := h.clm_apply (hasDerivAt_const 0 e)
    simpa [hg0] using hh
  have hsecond := deriv_deriv_nonpos_of_localMax hm' hcont
  rw [heq.deriv_eq, hder.deriv] at hsecond
  simpa [secondPartial, iteratedFDeriv_two_apply, e] using hsecond

private theorem le_zero_of_strict_elliptic {d : ℕ} {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) (hb : Bornology.IsBounded U) {μ a : ℝ}
    (hμ : 0 ≤ μ) (ha : 0 < a) {v : (Fin d → ℝ) → ℝ}
    (hv : ContDiffOn ℝ 2 v U) (hc : ContinuousOn v (closure U))
    (hfront : ∀ x ∈ frontier U, v x ≤ 0)
    (hstrict : ∀ x ∈ U, μ * v x - a * laplacian v x < 0) :
    ∀ x ∈ U, v x ≤ 0 := by
  intro x hx
  obtain ⟨y, hy, hmax⟩ := hb.isCompact_closure.exists_isMaxOn
    ⟨x, subset_closure hx⟩ hc
  have hyzero : v y ≤ 0 := by
    by_contra! hypos
    have hyU : y ∈ U := by
      by_contra hyU
      have hyfront : y ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hy, hyU⟩
      exact (not_lt_of_ge (hfront y hyfront)) hypos
    have hlocal : IsLocalMax v y := hmax.isLocalMax
      (mem_of_superset (hU.mem_nhds hyU) subset_closure)
    have hs : laplacian v y ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      exact secondPartial_nonpos_of_localMax
        (hv.contDiffAt (hU.mem_nhds hyU)) hlocal i
    have hmass := mul_nonneg hμ hypos.le
    have hdiff := mul_nonpos_of_nonneg_of_nonpos ha.le hs
    linarith [hstrict y hyU]
  exact (hmax (subset_closure hx)).trans hyzero

private theorem le_quadratic_barrier {d : ℕ} (hd : 0 < (d : ℝ))
    {U : Set (Fin d → ℝ)} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    {B F δ μ a : ℝ} (hF : 0 ≤ F) (hδ : 0 < δ)
    (hμ : 0 ≤ μ) (ha : 0 < a)
    (hbound : ∀ x ∈ closure U, ∑ i, (x i) ^ 2 ≤ B)
    {v : (Fin d → ℝ) → ℝ} (hv : ContDiffOn ℝ 2 v U)
    (hc : ContinuousOn v (closure U)) (hfront : ∀ x ∈ frontier U, v x ≤ 0)
    (hforcing : ∀ x ∈ U, μ * v x - a * laplacian v x ≤ F)
    {x : Fin d → ℝ} (hx : x ∈ U) :
    v x ≤ ((F + δ) / (2 * d * a)) * B := by
  let k : ℝ := (F + δ) / (2 * d * a)
  let w : (Fin d → ℝ) → ℝ := fun y => k * B + (-k) * ∑ i, (y i) ^ 2
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hw : ContDiff ℝ 2 w := by dsimp [w]; fun_prop
  have hwnonneg (y : Fin d → ℝ) (hy : y ∈ closure U) : 0 ≤ w y := by
    have hh := mul_nonneg hk (sub_nonneg.mpr (hbound y hy))
    dsimp [w]
    nlinarith
  have hlap (y : Fin d → ℝ) : laplacian w y = -(F + δ) / a := by
    dsimp [w]
    rw [laplacian_affine_sum_sq]
    dsimp [k]
    field_simp
  have hsub (y : Fin d → ℝ) (hy : y ∈ U) :
      laplacian (fun z => v z - w z) y = laplacian v y - laplacian w y := by
    unfold laplacian secondPartial
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    change (iteratedFDeriv ℝ 2 (v - w) y) _ = _
    rw [iteratedFDeriv_sub_apply (hv.contDiffAt (hU.mem_nhds hy)) hw.contDiffAt]
    rfl
  have hle := le_zero_of_strict_elliptic hU hb hμ ha
    (hv.sub hw.contDiffOn) (hc.sub hw.continuous.continuousOn)
    (v := fun y => v y - w y)
    (fun y hy => by
      have := hwnonneg y (frontier_subset_closure hy)
      have := hfront y hy
      linarith)
    (fun y hy => by
      rw [hsub y hy, hlap y]
      have hn := mul_nonneg hμ (hwnonneg y (subset_closure hy))
      have he : a * ((F + δ) / a) = F + δ := mul_div_cancel₀ _ ha.ne'
      have he' : a * (-(F + δ) / a) = -(F + δ) := by
        field_simp
      have hf := hforcing y hy
      nlinarith) x hx
  have hsq : 0 ≤ ∑ i, (x i) ^ 2 := Finset.sum_nonneg fun i hi => sq_nonneg _
  have hkw := mul_nonneg hk hsq
  dsimp [w] at hle
  dsimp [k] at *
  nlinarith

private theorem le_sup_bound {d : ℕ} (hd : 0 < (d : ℝ))
    {U : Set (Fin d → ℝ)} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    {B F μ a : ℝ} (hB : 0 < B) (hF : 0 ≤ F) (hμ : 0 ≤ μ) (ha : 0 < a)
    (hbound : ∀ x ∈ closure U, ∑ i, (x i) ^ 2 ≤ B)
    {v : (Fin d → ℝ) → ℝ} (hv : ContDiffOn ℝ 2 v U)
    (hc : ContinuousOn v (closure U)) (hfront : ∀ x ∈ frontier U, v x ≤ 0)
    (hforcing : ∀ x ∈ U, μ * v x - a * laplacian v x ≤ F)
    {x : Fin d → ℝ} (hx : x ∈ U) :
    v x ≤ (B / (2 * d) / a) * F := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε * (2 * d * a) / B
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hh := le_quadratic_barrier hd hU hb hF hδ hμ ha hbound hv hc hfront hforcing hx
  have he : ((F + δ) / (2 * d * a)) * B = (B / (2 * d) / a) * F + ε := by
    dsimp [δ]
    field_simp
  rwa [he] at hh

/-- The zero-boundary supremum estimate of Gilbarg–Trudinger, Theorem 3.7. -/
theorem gilbargTrudingerSupEstimate_holds : GilbargTrudingerSupEstimate := by
  intro d hd U hU _ hb
  have hd' : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hq : Continuous (fun x : Fin d → ℝ => ∑ i, (x i) ^ 2) := by fun_prop
  obtain ⟨M, hM⟩ := hb.isCompact_closure.exists_bound_of_continuousOn hq.continuousOn
  let B : ℝ := |M| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound (x : Fin d → ℝ) (hx : x ∈ closure U) : ∑ i, (x i) ^ 2 ≤ B := by
    have hh := hM x hx
    rw [Real.norm_eq_abs] at hh
    have := le_abs_self (∑ i, (x i) ^ 2)
    dsimp [B]
    linarith [le_abs_self M]
  refine ⟨B / (2 * d), by positivity, ?_⟩
  intro a μ ha hμ f u hf hu
  let F : ℝ := (supNorm U f).toReal
  have hF : 0 ≤ F := ENNReal.toReal_nonneg
  have hforce (x : Fin d → ℝ) (hx : x ∈ U) :
      |μ * u x - a * laplacian u x| ≤ F := by
    rw [hu.2.2.2 x hx]
    exact abs_le_supNorm_toReal hf hx
  have hupp (x : Fin d → ℝ) (hx : x ∈ U) :
      u x ≤ (B / (2 * d) / a) * F :=
    le_sup_bound hd' hU hb hB hF hμ ha hbound hu.1 hu.2.1
      (fun x hx => le_of_eq (hu.2.2.1 x hx))
      (fun x hx => (le_abs_self _).trans (hforce x hx)) hx
  have hlapneg (x : Fin d → ℝ) : laplacian (fun y => -u y) x = -laplacian u x := by
    change laplacian (-u) x = -laplacian u x
    simp [laplacian, secondPartial, iteratedFDeriv_neg_apply, Finset.sum_neg_distrib]
  have hlow (x : Fin d → ℝ) (hx : x ∈ U) :
      -u x ≤ (B / (2 * d) / a) * F := by
    apply le_sup_bound hd' hU hb hB hF hμ ha hbound hu.1.neg hu.2.1.neg
      (v := fun y => -u y) _ _ hx
    · intro y hy
      rw [hu.2.2.1 y hy, neg_zero]
    · intro y hy
      rw [hlapneg]
      have hh := (abs_le.mp (hforce y hy)).1
      linarith
  have hpt (x : Fin d → ℝ) (hx : x ∈ U) :
      |u x| ≤ (B / (2 * d) / a) * F := by
    rw [abs_le]
    constructor
    · linarith [hlow x hx]
    · exact hupp x hx
  unfold supNorm
  apply iSup_le fun x => iSup_le fun hx => ?_
  calc
    ENNReal.ofReal |u x| ≤ ENNReal.ofReal ((B / (2 * d) / a) * F) :=
      ENNReal.ofReal_le_ofReal (hpt x hx)
    _ = ENNReal.ofReal (B / (2 * d) / a) * ENNReal.ofReal F :=
      ENNReal.ofReal_mul (by positivity)
    _ = ENNReal.ofReal (B / (2 * d) / a) * supNorm U f := by
      rw [show ENNReal.ofReal F = supNorm U f from ENNReal.ofReal_toReal hf.ne]

end
end LatticeProb.External
