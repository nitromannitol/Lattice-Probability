/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMomentPos2Dec at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentPos2Exp
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentPos2Ros
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Decoupling of a checkerboard group by Kahane's inequality (P2-KAHANE3)

For a group `G` of level-`m` squares of one parity class (pairwise at distance `≥ 2^{-m}`),
`DGMC.LogCorr.integral_group_rpow_le` compares the `q`-th moment of the total mass of `G` at
scale `2^{-(m+l)}` with the `q`-th moment of a sum of **independent** copies of
`4^{-m} gM_l([0,1]²)`, realized on the product space `(G → Ω, P^{⊗G})`:

`E (∑_{u ∈ G} gM_{m+l}(S_u))^q ≤ e^{q(q−1)(β m log 2 + 2c)/2} E (∑_{u ∈ G} 4^{-m} gM_l^{(u)})^q`.

Covariances: inside one square the two-sided log bound gives
`Cov Z_{m+l} ≤ Cov Z_l(rescaled) + β m log 2 + 2c` (`LogCorr.cov_sh_le`, the exact-scaling
relation (scalingeps) of Berestycki–Powell arXiv:2404.16642, `GMCproperties.tex` l. 1230–1250);
across squares `Cov Z_{m+l} ≤ β m log 2 + c` (`cov_sh_le_of_par`, BP l. 1335–1338), while the
copies are independent. Kahane's inequality with an additive constant
(`Kahane.kahane_rpow_le_add_const`; Kahane 1985, RV arXiv:1305.6221 Thm 2.1) then applies.
This decoupling replaces BP's direct off-diagonal computation (l. 1327–1430); the i.i.d. sum is
bounded by `integral_sum_pi_rpow_le`. Own arrangement of the standard argument (DEVIATIONS).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal

namespace LQGMetric

namespace DGMC

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

section Pi

variable [IsProbabilityMeasure P] {G : Type*} [Fintype G]

lemma covariance_comp_eval {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) (u : G) :
    cov[fun ω' : G → Ω => f (ω' u), fun ω' => g (ω' u); Measure.pi fun _ : G => P] =
      cov[f, g; P] := by
  have hmap := (measurePreserving_eval (fun _ : G => P) u).map_eq
  rw [← covariance_map_fun (μ := Measure.pi fun _ : G => P) (Z := fun ω' : G → Ω => ω' u)
    (X := f) (Y := g) (by rw [hmap]; exact hf.aestronglyMeasurable)
    (by rw [hmap]; exact hg.aestronglyMeasurable) (measurable_pi_apply u).aemeasurable, hmap]

lemma variance_comp_eval {f : Ω → ℝ} (hf : Measurable f) (u : G) :
    Var[fun ω' : G → Ω => f (ω' u); Measure.pi fun _ : G => P] = Var[f; P] := by
  have hmap := (measurePreserving_eval (fun _ : G => P) u).map_eq
  have h := variance_map (μ := Measure.pi fun _ : G => P) (Y := fun ω' : G → Ω => ω' u)
    (X := f) (by rw [hmap]; exact hf.aemeasurable) (measurable_pi_apply u).aemeasurable
  rw [hmap] at h
  exact h.symm

end Pi

variable {Z : ℕ → ℂ → Ω → ℝ} {β c : ℝ}

/-- **decoupling of a checkerboard group** (`q ≥ 1`, or `q ≤ 0` for negative moments) -/
theorem LogCorr.integral_group_rpow_le (hZ : LogCorr Z P β c) (hβ : 0 ≤ β) {q : ℝ}
    (hq : q ≤ 0 ∨ 1 ≤ q)
    (m l k : ℕ) {G : Finset (ℕ × ℕ)} (hG : G ⊆ grid m)
    (hpar : ∀ u ∈ G, ∀ v ∈ G, par u = par v) (hne : G.Nonempty) :
    ∫ ω, (∑ u ∈ G, gM (Z (m + l)) P (m + k) (sub k u) ω) ^ q ∂P ≤
      Real.exp (q * (q - 1) * (β * (m * Real.log 2) + 2 * c) / 2) *
        ∫ ω', (∑ u : ↥G, (4 : ℝ)⁻¹ ^ m * gM (Z l) P k (grid k) (ω' u)) ^ q
          ∂(Measure.pi fun _ : ↥G => P) := by
  have hP := hZ.isProb
  have hc := hZ.c_nonneg
  have hne' : Nonempty (↥G × ↥(grid k)) :=
    ⟨(⟨_, hne.choose_spec⟩, ⟨(0, 0), mem_grid.2 ⟨by positivity, by positivity⟩⟩)⟩
  set Q := Measure.pi fun _ : ↥G => P
  set c' : ℝ≥0 := ⟨β * (m * Real.log 2) + 2 * c, by positivity⟩
  -- the two Gaussian vectors
  set f : Ω → ↥(grid k) → ℝ := fun ω a => Z l (cpt k a) ω
  have hfm : Measurable f := measurable_pi_iff.mpr fun a => hZ.meas l _
  have hfG : HasGaussianLaw f P := hasGaussianLaw_fintype (hZ.gauss l) (fun a : ↥(grid k) => cpt k a)
  have hmap : ∀ u : ↥G, Q.map (fun ω' : ↥G → Ω => ω' u) = P := fun u =>
    (measurePreserving_eval (fun _ : ↥G => P) u).map_eq
  have hB : ∀ u : ↥G, HasGaussianLaw (fun ω' : ↥G → Ω => f (ω' u)) Q := fun u =>
    ⟨(hfm.comp (measurable_pi_apply u)).aemeasurable, by
      rw [show (fun ω' : ↥G → Ω => f (ω' u)) = f ∘ (fun ω' => ω' u) from rfl,
        ← Measure.map_map hfm (measurable_pi_apply u), hmap u]
      exact hfG.isGaussian_map⟩
  have hind : iIndepFun (fun (u : ↥G) (ω' : ↥G → Ω) => f (ω' u)) Q :=
    iIndepFun_pi (X := fun _ => f) fun _ => hfm.aemeasurable
  have hYb : HasGaussianLaw (fun ω' (u : ↥G) => f (ω' u)) Q := hind.hasGaussianLaw hB
  let L : (↥G → ↥(grid k) → ℝ) →L[ℝ] (↥G × ↥(grid k) → ℝ) :=
    ContinuousLinearMap.pi fun p =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥(grid k) => ℝ) p.2).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥G => ↥(grid k) → ℝ) p.1)
  have hY : HasGaussianLaw (fun (ω' : ↥G → Ω) (p : ↥G × ↥(grid k)) =>
      Z l (cpt k p.2) (ω' p.1)) Q := hYb.map L
  have hX : HasGaussianLaw (fun ω (p : ↥G × ↥(grid k)) =>
      Z (m + l) (cpt (m + k) (sh k p.1 p.2)) ω) P :=
    hasGaussianLaw_fintype (hZ.gauss (m + l)) (fun p : ↥G × ↥(grid k) => cpt (m + k) (sh k p.1 p.2))
  have hYm : ∀ p : ↥G × ↥(grid k), ∫ ω', Z l (cpt k p.2) (ω' p.1) ∂Q = 0 := fun p => by
    rw [integral_comp_eval (f := Z l (cpt k p.2)) (hZ.meas l _) p.1]; exact hZ.mean _ _
  have hmem : ∀ x, MemLp (Z l x) 2 P := fun x => (hZ.hasGaussianLaw l x).memLp_two
  have hcov : ∀ p p' : ↥G × ↥(grid k),
      cov[fun ω => Z (m + l) (cpt (m + k) (sh k p.1 p.2)) ω,
        fun ω => Z (m + l) (cpt (m + k) (sh k p'.1 p'.2)) ω; P] ≤
      cov[fun ω' => Z l (cpt k p.2) (ω' p.1), fun ω' => Z l (cpt k p'.2) (ω' p'.1); Q] + c' := by
    rintro ⟨u, a⟩ ⟨v, b⟩
    show _ ≤ _ + (β * (m * Real.log 2) + 2 * c)
    by_cases huv : u = v
    · subst huv
      rw [covariance_comp_eval (G := ↥G) (hZ.meas l _) (hZ.meas l _) u]
      exact hZ.cov_sh_le m l k (hG u.2) a.2 b.2
    · have hi : IndepFun (fun ω' : ↥G → Ω => Z l (cpt k a) (ω' u))
          (fun ω' : ↥G → Ω => Z l (cpt k b) (ω' v)) Q :=
        (hind.indepFun huv).comp (measurable_pi_apply a) (measurable_pi_apply b)
      have hu' : (u : ℕ × ℕ) ≠ v := fun h => huv (Subtype.ext h)
      rw [hi.covariance_eq_zero
        ((hmem _).comp_measurePreserving (measurePreserving_eval (fun _ : ↥G => P) u))
        ((hmem _).comp_measurePreserving (measurePreserving_eval (fun _ : ↥G => P) v)), zero_add]
      have := cov_sh_le_of_par hZ hβ (n := m + l) (hG u.2) (hG v.2) hu' (hpar _ u.2 _ v.2) a.2 b.2
      linarith
  have hK := Kahane.kahane_rpow_le_add_const hq
    (p := fun _ : ↥G × ↥(grid k) => (4 : ℝ)⁻¹ ^ m * (4 : ℝ)⁻¹ ^ k)
    (fun _ => by positivity) hX hY (fun p => hZ.mean _ _) hYm c' hcov
  -- identify both sides
  have hL : ∀ ω, ∑ u ∈ G, gM (Z (m + l)) P (m + k) (sub k u) ω =
      ∑ p : ↥G × ↥(grid k), (4 : ℝ)⁻¹ ^ m * (4 : ℝ)⁻¹ ^ k *
        Real.exp (Z (m + l) (cpt (m + k) (sh k p.1 p.2)) ω -
          Var[fun ω => Z (m + l) (cpt (m + k) (sh k p.1 p.2)) ω; P] / 2) := fun ω => by
    rw [← Finset.sum_coe_sort G, Fintype.sum_prod_type]
    refine Fintype.sum_congr _ _ fun u => ?_
    rw [gM_sub, Finset.mul_sum]
    refine Fintype.sum_congr _ _ fun a => ?_
    rw [mul_assoc]
  have hR : ∀ ω' : ↥G → Ω, ∑ p : ↥G × ↥(grid k), (4 : ℝ)⁻¹ ^ m * (4 : ℝ)⁻¹ ^ k *
        Real.exp (Z l (cpt k p.2) (ω' p.1) -
          Var[fun ω' : ↥G → Ω => Z l (cpt k p.2) (ω' p.1); Q] / 2) =
      ∑ u : ↥G, (4 : ℝ)⁻¹ ^ m * gM (Z l) P k (grid k) (ω' u) := fun ω' => by
    rw [Fintype.sum_prod_type]
    refine Fintype.sum_congr _ _ fun u => ?_
    rw [gM_grid, Finset.mul_sum]
    refine Fintype.sum_congr _ _ fun a => ?_
    rw [variance_comp_eval (G := ↥G) (hZ.meas l _) u, mul_assoc]
  simp_rw [hL]
  simp_rw [hR] at hK
  exact hK

end DGMC

end LQGMetric
