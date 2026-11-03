/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMomentNeg at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentPos2Main

/-!
# Negative moments of discrete GMC sums: the bootstrap step (P2-KAHANE3)

* `DGMC.LogCorr.integrable_gM_rpow_nonpos` : `gM(S)^q` is integrable for `q ≤ 0` (`S ≠ ∅`),
  by the AM–GM inequality `gM(S) ≥ W exp(∑ (w/W)(Z − Var/2))` and Gaussian exponential moments;
* `DGMC.LogCorr.integral_gM_neg_le` : the bootstrap step of Berestycki–Powell
  (arXiv:2404.16642, Theorem `T:negmom`, `GMCproperties.tex` l. 1719–1745, after Molchan):
  for `q ≤ 0`, with `N` the number of level-`m` squares of the parity class `(0,0)`,
  `E gM_{m+l}([0,1]²)^q ≤ e^{q(q−1)(β m log 2 + 2c)/2} (N 4^{-m})^q (E gM_l([0,1]²)^{q/N})^N`.
  `gM ≥` the mass of one checkerboard group; decoupling by Kahane (`integral_group_rpow_le`
  with `q ≤ 0`, BP l. 1736–1743: the comparison field with independent pieces dominates the
  covariance); AM–GM `∑_u a_u ≥ N ∏_u a_u^{1/N}` (BP uses it with two pieces); the product
  measure factorizes. BP use two pieces `D₁, D₂`; we use the `N` squares of one group.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal

namespace LQGMetric

namespace DGMC

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : ℕ → ℂ → Ω → ℝ} {β c : ℝ}

/-- AM–GM lower bound for `gM` -/
lemma gM_ge_exp (Zn : ℂ → Ω → ℝ) (j : ℕ) {S : Finset (ℕ × ℕ)} (hS : S.Nonempty) (ω : Ω) :
    (S.card : ℝ) * (4 : ℝ)⁻¹ ^ j * Real.exp (∑ i ∈ S, (S.card : ℝ)⁻¹ *
      (Zn (cpt j i) ω - Var[Zn (cpt j i); P] / 2)) ≤ gM Zn P j S ω := by
  have hN : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have h := Real.geom_mean_le_arith_mean_weighted S (fun _ => (S.card : ℝ)⁻¹)
    (fun i => Real.exp (Zn (cpt j i) ω - Var[Zn (cpt j i); P] / 2)) (fun _ _ => by positivity)
    (by rw [sum_const, nsmul_eq_mul, mul_inv_cancel₀ hN.ne']) (fun _ _ => by positivity)
  have e : ∏ i ∈ S, Real.exp (Zn (cpt j i) ω - Var[Zn (cpt j i); P] / 2) ^ (S.card : ℝ)⁻¹ =
      Real.exp (∑ i ∈ S, (S.card : ℝ)⁻¹ * (Zn (cpt j i) ω - Var[Zn (cpt j i); P] / 2)) := by
    rw [Real.exp_sum]
    refine prod_congr rfl fun i _ => ?_
    rw [← Real.exp_mul, mul_comm]
  rw [e] at h
  set Xs := ∑ i ∈ S, Real.exp (Zn (cpt j i) ω - Var[Zn (cpt j i); P] / 2)
  have h' : Real.exp (∑ i ∈ S, (S.card : ℝ)⁻¹ * (Zn (cpt j i) ω - Var[Zn (cpt j i); P] / 2)) ≤
      (S.card : ℝ)⁻¹ * Xs := by rw [Finset.mul_sum]; exact h
  have : gM Zn P j S ω = (4 : ℝ)⁻¹ ^ j * Xs := by
    rw [gM, Finset.mul_sum]
  rw [this]
  calc (S.card : ℝ) * (4 : ℝ)⁻¹ ^ j * Real.exp (∑ i ∈ S, (S.card : ℝ)⁻¹ *
        (Zn (cpt j i) ω - Var[Zn (cpt j i); P] / 2))
      ≤ (S.card : ℝ) * (4 : ℝ)⁻¹ ^ j * ((S.card : ℝ)⁻¹ * Xs) :=
        mul_le_mul_of_nonneg_left h' (by positivity)
    _ = _ := by
        rw [mul_comm (S.card : ℝ), mul_assoc, ← mul_assoc (S.card : ℝ),
          mul_inv_cancel₀ hN.ne', one_mul]

/-- **integrability of negative powers of `gM`** -/
theorem LogCorr.integrable_gM_rpow_nonpos (hZ : LogCorr Z P β c) (n j : ℕ)
    {S : Finset (ℕ × ℕ)} (hS : S.Nonempty) {q : ℝ} (hq : q ≤ 0) :
    Integrable (fun ω => gM (Z n) P j S ω ^ q) P := by
  have hP := hZ.isProb
  set w : ℝ := (S.card : ℝ)⁻¹
  set Vb : ℝ := ∑ i ∈ S, w * (Var[Z n (cpt j i); P] / 2)
  set Sm : Ω → ℝ := fun ω => ∑ i ∈ S, Z n (cpt j i) ω
  have hSG : HasGaussianLaw Sm P :=
    ((hZ.gauss n).comp_right fun i : ℕ × ℕ => cpt j i).hasGaussianLaw_fun_sum (I := S)
  have hS0 : ∫ ω, Sm ω ∂P = 0 := by
    simp only [Sm]
    rw [integral_finsetSum _ fun i _ => (hZ.hasGaussianLaw n _).integrable]
    exact sum_eq_zero fun i _ => hZ.mean n _
  obtain ⟨hi, -⟩ := integral_exp_mul_of_hasGaussianLaw hSG hS0 (q * w)
  set K : ℝ := ((S.card : ℝ) * (4 : ℝ)⁻¹ ^ j) ^ q * Real.exp (-(q * Vb))
  refine Integrable.mono' (hi.const_mul K) ((hZ.measurable_gM n j S).pow_const q).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  have hpos : 0 < (S.card : ℝ) * (4 : ℝ)⁻¹ ^ j *
      Real.exp (∑ i ∈ S, w * (Z n (cpt j i) ω - Var[Z n (cpt j i); P] / 2)) := by
    have : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    positivity
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (gM_nonneg _ _ _ _) _)]
  refine (Real.rpow_le_rpow_of_nonpos hpos (gM_ge_exp (Z n) j hS ω) hq).trans_eq ?_
  have hexp : (∑ i ∈ S, w * (Z n (cpt j i) ω - Var[Z n (cpt j i); P] / 2)) * q =
      -(q * Vb) + q * w * Sm ω := by
    simp only [Sm, Vb]
    rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul, hexp, Real.exp_add]
  simp only [K]
  ring

/-- the level-`m` squares of the parity class `(0,0)` -/
def grp0 (m : ℕ) : Finset (ℕ × ℕ) := (grid m).filter fun u => par u = (0, 0)

lemma grp0_nonempty (m : ℕ) : (grp0 m).Nonempty :=
  ⟨(0, 0), mem_filter.2 ⟨mem_grid.2 ⟨by positivity, by positivity⟩, rfl⟩⟩

lemma sub_nonempty (k : ℕ) (u : ℕ × ℕ) : (sub k u).Nonempty :=
  (Finset.Nonempty.image ⟨(0, 0), mem_grid.2 ⟨by positivity, by positivity⟩⟩ _)

lemma gM_pos (Zn : ℂ → Ω → ℝ) (j : ℕ) {S : Finset (ℕ × ℕ)} (hS : S.Nonempty) (ω : Ω) :
    0 < gM Zn P j S ω :=
  Finset.sum_pos (fun _ _ => by positivity) hS

/-- **bootstrap step for negative moments** (BP Theorem `T:negmom`, Molchan) -/
theorem LogCorr.integral_gM_neg_le (hZ : LogCorr Z P β c) (hβ : 0 ≤ β) {q : ℝ} (hq : q ≤ 0)
    (m l k : ℕ) :
    ∫ ω, gM (Z (m + l)) P (m + k) (grid (m + k)) ω ^ q ∂P ≤
      Real.exp (q * (q - 1) * (β * (m * Real.log 2) + 2 * c) / 2) *
        (((grp0 m).card : ℝ) * (4 : ℝ)⁻¹ ^ m) ^ q *
          (∫ ω, gM (Z l) P k (grid k) ω ^ (q / (grp0 m).card) ∂P) ^ (grp0 m).card := by
  have hP := hZ.isProb
  set G := grp0 m
  set N : ℕ := G.card
  have hN : (0 : ℝ) < N := by exact_mod_cast (grp0_nonempty m).card_pos
  set T : Ω → ℝ := fun ω => ∑ u ∈ G, gM (Z (m + l)) P (m + k) (sub k u) ω
  have hTpos : ∀ ω, 0 < T ω := fun ω =>
    Finset.sum_pos (fun u _ => gM_pos _ _ (sub_nonempty k u) ω) (grp0_nonempty m)
  have hTle : ∀ ω, T ω ≤ gM (Z (m + l)) P (m + k) (grid (m + k)) ω := fun ω => by
    rw [gM_grid_eq_sum_sub]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => gM_nonneg _ _ _ _
  -- integrability of `T^q`
  obtain ⟨u₀, hu₀⟩ := grp0_nonempty m
  have hTq : Integrable (fun ω => T ω ^ q) P := by
    refine Integrable.mono' (hZ.integrable_gM_rpow_nonpos (m + l) (m + k) (sub_nonempty k u₀) hq)
      ((Finset.measurable_sum _ fun u _ => hZ.measurable_gM _ _ _).pow_const q).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hTpos ω).le _)]
    exact Real.rpow_le_rpow_of_nonpos (gM_pos _ _ (sub_nonempty k u₀) ω)
      (single_le_sum (f := fun u => gM (Z (m + l)) P (m + k) (sub k u) ω)
        (fun _ _ => gM_nonneg _ _ _ _) hu₀) hq
  have hdec := hZ.integral_group_rpow_le hβ (Or.inl hq) m l k (filter_subset _ _)
    (fun u hu v hv => by rw [(mem_filter.1 hu).2, (mem_filter.1 hv).2]) (grp0_nonempty m)
  -- AM-GM on the product space
  set A : Ω → ℝ := fun ω => (4 : ℝ)⁻¹ ^ m * gM (Z l) P k (grid k) ω
  have hApos : ∀ ω, 0 < A ω := fun ω => mul_pos (by positivity)
    (gM_pos _ _ ⟨(0, 0), mem_grid.2 ⟨by positivity, by positivity⟩⟩ ω)
  have hcardG : Fintype.card ↥G = N := Fintype.card_coe G
  have hamgm : ∀ ω' : ↥G → Ω, (∑ u : ↥G, A (ω' u)) ^ q ≤
      (N : ℝ) ^ q * ∏ u : ↥G, A (ω' u) ^ (q / N) := by
    intro ω'
    have h := Real.geom_mean_le_arith_mean_weighted (univ : Finset ↥G) (fun _ => (N : ℝ)⁻¹)
      (fun u => A (ω' u)) (fun _ _ => by positivity)
      (by rw [sum_const, card_univ, hcardG, nsmul_eq_mul, mul_inv_cancel₀ hN.ne'])
      (fun u _ => (hApos _).le)
    rw [← Finset.mul_sum] at h
    have hprod : 0 < ∏ u : ↥G, A (ω' u) ^ (N : ℝ)⁻¹ :=
      Finset.prod_pos fun u _ => Real.rpow_pos_of_pos (hApos _) _
    have h2 : (N : ℝ) * ∏ u : ↥G, A (ω' u) ^ (N : ℝ)⁻¹ ≤ ∑ u : ↥G, A (ω' u) := by
      have := mul_le_mul_of_nonneg_left h hN.le
      rwa [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul] at this
    refine (Real.rpow_le_rpow_of_nonpos (by positivity) h2 hq).trans_eq ?_
    rw [Real.mul_rpow hN.le hprod.le, ← Real.finset_prod_rpow _ _ fun u _ =>
      Real.rpow_nonneg (hApos _).le _]
    congr 1
    refine prod_congr rfl fun u _ => ?_
    rw [← Real.rpow_mul (hApos _).le, inv_mul_eq_div]
  have hAint : Integrable (fun ω => A ω ^ (q / N)) P := by
    have e : (fun ω => A ω ^ (q / N)) = fun ω =>
        ((4 : ℝ)⁻¹ ^ m) ^ (q / N) * gM (Z l) P k (grid k) ω ^ (q / N) := by
      funext ω; exact Real.mul_rpow (by positivity) (gM_nonneg _ _ _ _)
    rw [e]
    exact (hZ.integrable_gM_rpow_nonpos l k ⟨(0, 0), mem_grid.2 ⟨by positivity, by positivity⟩⟩
      (div_nonpos_of_nonpos_of_nonneg hq hN.le)).const_mul _
  have hprodint : Integrable (fun ω' : ↥G → Ω => (N : ℝ) ^ q * ∏ u : ↥G, A (ω' u) ^ (q / N))
      (Measure.pi fun _ : ↥G => P) :=
    (Integrable.fintype_prod (f := fun _ ω => A ω ^ (q / N)) fun _ => hAint).const_mul _
  have hpi : ∫ ω', (N : ℝ) ^ q * ∏ u : ↥G, A (ω' u) ^ (q / N) ∂(Measure.pi fun _ : ↥G => P) =
      (N : ℝ) ^ q * (∫ ω, A ω ^ (q / N) ∂P) ^ N := by
    rw [integral_const_mul, integral_fintype_prod_eq_pow (fun ω => A ω ^ (q / N)), hcardG]
  have hAeq : ∫ ω, A ω ^ (q / N) ∂P =
      ((4 : ℝ)⁻¹ ^ m) ^ (q / N) * ∫ ω, gM (Z l) P k (grid k) ω ^ (q / N) ∂P := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun ω => Real.mul_rpow (by positivity)
      (gM_nonneg _ _ _ _))
  calc ∫ ω, gM (Z (m + l)) P (m + k) (grid (m + k)) ω ^ q ∂P
      ≤ ∫ ω, T ω ^ q ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω =>
          Real.rpow_nonneg (gM_nonneg _ _ _ _) _) hTq (Eventually.of_forall fun ω =>
          Real.rpow_le_rpow_of_nonpos (hTpos ω) (hTle ω) hq)
    _ ≤ _ := hdec
    _ ≤ Real.exp (q * (q - 1) * (β * (m * Real.log 2) + 2 * c) / 2) *
          ((N : ℝ) ^ q * (∫ ω, A ω ^ (q / N) ∂P) ^ N) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        rw [← hpi]
        exact integral_mono_of_nonneg (Eventually.of_forall fun ω' =>
          Real.rpow_nonneg (Finset.sum_nonneg fun u _ => (hApos _).le) _) hprodint
          (Eventually.of_forall hamgm)
    _ = _ := by
        rw [hAeq, mul_pow, ← Real.rpow_natCast (((4 : ℝ)⁻¹ ^ m) ^ (q / N)),
          ← Real.rpow_mul (by positivity), div_mul_cancel₀ _ hN.ne',
          Real.mul_rpow hN.le (by positivity)]
        ring

end DGMC

end LQGMetric
