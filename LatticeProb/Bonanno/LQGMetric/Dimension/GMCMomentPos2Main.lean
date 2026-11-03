/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMomentPos2Main at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentPos2Dec

/-!
# Uniform positive moments of discrete GMC sums (P2-KAHANE3)

`DGMC.LogCorr.exists_uniform_moment`: for a `β`-log-correlated family `Z` (`LogCorr Z P β c`,
`β > 0`) and `1 < q < 4/β`, `sup_{n ≤ j} E gM_n([0,1]²)^q < ∞`, where `gM_n` is the level-`j`
dyadic Riemann sum of the chaos `e^{Z_n − Var Z_n/2}` (with `β = γ²` and `d = 2`, the range is
`q < 2d/γ² = 4/γ²`).

Berestycki–Powell, *Gaussian free field and Liouville quantum gravity* (arXiv:2404.16642),
Theorem 3.23 (`T:finiteposmoments`), `GMCproperties.tex` l. 1270–1430: decompose `[0,1]²` into
the `4^m` squares of level `m`, split them into the `2^d = 4` checkerboard groups, bound
`(∑_g T_g)^q ≤ 4^{q−1} ∑_g T_g^q`, estimate each group (here: decoupling by Kahane,
`LogCorr.integral_group_rpow_le`, and the i.i.d. bound `integral_sum_pi_rpow_le`), giving
`M_{m+l} ≤ θ_m M_l + D_m` with `θ_m = O(2^{−m(q−1)(2 − qβ/2)}) → 0`; choose `m` with
`θ_m ≤ 1/2` and conclude by induction on the scale (BP l. 1345–1360), the scales `n < m` being
covered by the a priori bound `LogCorr.integral_gM_grid_rpow_le_apriori`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal

namespace LQGMetric

namespace DGMC

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- the level-`(m+k)` grid is the disjoint union of the level-`k` grids of the level-`m` squares -/
lemma gM_grid_eq_sum_sub (Z : ℂ → Ω → ℝ) (m k : ℕ) (ω : Ω) :
    gM Z P (m + k) (grid (m + k)) ω = ∑ u ∈ grid m, gM Z P (m + k) (sub k u) ω := by
  have h2 : 0 < 2 ^ k := by positivity
  simp only [gM, sub]
  simp_rw [sum_image fun a _ b _ h => sh_injective k _ h]
  rw [← sum_product (grid m) (grid k)
    (fun p => (4 : ℝ)⁻¹ ^ (m + k) * Real.exp (Z (cpt (m + k) (sh k p.1 p.2)) ω -
      Var[Z (cpt (m + k) (sh k p.1 p.2)); P] / 2))]
  symm
  refine sum_nbij' (fun p => sh k p.1 p.2)
    (fun i => ((i.1 / 2 ^ k, i.2 / 2 ^ k), (i.1 % 2 ^ k, i.2 % 2 ^ k))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨u, a⟩ h
    rw [mem_product] at h
    exact sh_mem_grid h.1 h.2
  · intro i hi
    rw [mem_grid, pow_add] at hi
    rw [mem_product, mem_grid, mem_grid]
    refine ⟨⟨?_, ?_⟩, Nat.mod_lt _ h2, Nat.mod_lt _ h2⟩
    · exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hi.1)
    · exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hi.2)
  · rintro ⟨u, a⟩ h
    rw [mem_product, mem_grid, mem_grid] at h
    simp only [sh]
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> simp only
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ h2, Nat.div_eq_of_lt h.2.1, zero_add]
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ h2, Nat.div_eq_of_lt h.2.2, zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h.2.1]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h.2.2]
  · intro i _
    simp only [sh]
    exact Prod.ext (Nat.div_add_mod' _ _) (Nat.div_add_mod' _ _)
  · intro _ _; rfl

/-- grouping the level-`m` squares by parity class -/
lemma gM_grid_eq_sum_par (Z : ℂ → Ω → ℝ) (m k : ℕ) (ω : Ω) :
    gM Z P (m + k) (grid (m + k)) ω =
      ∑ g : Fin 2 × Fin 2, ∑ u ∈ grid m with par u = g, gM Z P (m + k) (sub k u) ω := by
  rw [gM_grid_eq_sum_sub, sum_fiberwise]

/-- the contraction factor of the recursion -/
def thetaR (β c q : ℝ) (m : ℕ) : ℝ :=
  4 ^ q * Real.exp (q * (q - 1) * (β * (m * Real.log 2) + 2 * c) / 2) *
    (2 ^ q * 4 ^ m * ((4 : ℝ)⁻¹ ^ m) ^ q)

/-- the additive constant of the recursion -/
def constR (β c q : ℝ) (m : ℕ) : ℝ :=
  4 ^ q * Real.exp (q * (q - 1) * (β * (m * Real.log 2) + 2 * c) / 2) *
    (2 ^ q * (2 ^ q * 2) ^ (q - 1))

variable {Z : ℕ → ℂ → Ω → ℝ} {β c : ℝ}

lemma LogCorr.measurable_gM (hZ : LogCorr Z P β c) (n j : ℕ) (S : Finset (ℕ × ℕ)) :
    Measurable (fun ω => gM (Z n) P j S ω) := by
  unfold gM
  exact Finset.measurable_sum _ fun i _ => ((hZ.meas n _).sub_const _).exp.const_mul _

/-- **one step of the recursion** (BP l. 1340–1350): `M_{m+l} ≤ θ_m M_l + D_m` -/
theorem LogCorr.recursion (hZ : LogCorr Z P β c) (hβ : 0 ≤ β) {q : ℝ} (hq : 1 ≤ q)
    (m l k : ℕ) :
    ∫ ω, gM (Z (m + l)) P (m + k) (grid (m + k)) ω ^ q ∂P ≤
      thetaR β c q m * ∫ ω, gM (Z l) P k (grid k) ω ^ q ∂P + constR β c q m := by
  have hP := hZ.isProb
  set R' := ∫ ω, gM (Z l) P k (grid k) ω ^ q ∂P
  have hR' : 0 ≤ R' := integral_nonneg fun ω => Real.rpow_nonneg (gM_nonneg _ _ _ _) _
  set E := Real.exp (q * (q - 1) * (β * (m * Real.log 2) + 2 * c) / 2)
  set D0 : ℝ := 2 ^ q * (2 ^ q * 2) ^ (q - 1)
  have hD0 : 0 ≤ D0 := by positivity
  set Gs : Fin 2 × Fin 2 → Finset (ℕ × ℕ) := fun g => (grid m).filter (fun u => par u = g)
  set T : Fin 2 × Fin 2 → Ω → ℝ := fun g ω => ∑ u ∈ Gs g, gM (Z (m + l)) P (m + k) (sub k u) ω
  have hT0 : ∀ g ω, 0 ≤ T g ω := fun g ω => sum_nonneg fun _ _ => gM_nonneg _ _ _ _
  have hTle : ∀ g ω, T g ω ≤ gM (Z (m + l)) P (m + k) (grid (m + k)) ω := fun g ω => by
    rw [gM_grid_eq_sum_sub]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => gM_nonneg _ _ _ _
  have hTm : ∀ g, Measurable (T g) := fun g =>
    Finset.measurable_sum _ fun u _ => hZ.measurable_gM _ _ _
  have hTq : ∀ g, Integrable (fun ω => T g ω ^ q) P := fun g =>
    Integrable.mono' (hZ.integrable_gM_grid_rpow (m + l) (m + k) hq)
      ((hTm g).pow_const q).aestronglyMeasurable (Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (hT0 g ω) _)]
        exact Real.rpow_le_rpow (hT0 g ω) (hTle g ω) (by linarith))
  -- per-group bound
  have hgrp : ∀ g, ∫ ω, T g ω ^ q ∂P ≤ E * (2 ^ q * 4 ^ m * ((4 : ℝ)⁻¹ ^ m) ^ q * R' + D0) := by
    intro g
    by_cases hne : (Gs g).Nonempty
    · have hdec := hZ.integral_group_rpow_le hβ (Or.inr hq) m l k (filter_subset _ _)
        (fun u hu v hv => by rw [(mem_filter.1 hu).2, (mem_filter.1 hv).2]) hne
      set A : Ω → ℝ := fun ω => (4 : ℝ)⁻¹ ^ m * gM (Z l) P k (grid k) ω
      have hAm : Measurable A := (hZ.measurable_gM _ _ _).const_mul _
      have hA0 : ∀ ω, 0 ≤ A ω := fun ω => mul_nonneg (by positivity) (gM_nonneg _ _ _ _)
      have hApow : ∀ ω, A ω ^ q = ((4 : ℝ)⁻¹ ^ m) ^ q * gM (Z l) P k (grid k) ω ^ q := fun ω =>
        Real.mul_rpow (by positivity) (gM_nonneg _ _ _ _)
      have hAq : Integrable (fun ω => A ω ^ q) P := by
        simp_rw [hApow]; exact (hZ.integrable_gM_grid_rpow l k hq).const_mul _
      have hros := integral_sum_pi_rpow_le (ι := ↥(Gs g)) (P := P) hAm hA0 hq hAq
      have ha : ∫ ω, A ω ^ q ∂P = ((4 : ℝ)⁻¹ ^ m) ^ q * R' := by
        simp_rw [hApow]; rw [integral_const_mul]
      have hb : ∫ ω, A ω ∂P = (4 : ℝ)⁻¹ ^ m := by
        simp only [A]
        rw [integral_const_mul, hZ.integral_gM, card_grid, inv_pow (4 : ℝ) k,
          inv_mul_cancel₀ (by positivity), mul_one]
      have hN : (Fintype.card ↥(Gs g) : ℝ) ≤ 4 ^ m := by
        rw [Fintype.card_coe, ← card_grid m]
        exact_mod_cast card_filter_le _ _
      have hN0 : (0 : ℝ) ≤ Fintype.card ↥(Gs g) := Nat.cast_nonneg _
      have hNb : (Fintype.card ↥(Gs g) : ℝ) * (4 : ℝ)⁻¹ ^ m ≤ 1 := by
        calc (Fintype.card ↥(Gs g) : ℝ) * (4 : ℝ)⁻¹ ^ m ≤ 4 ^ m * (4 : ℝ)⁻¹ ^ m :=
              mul_le_mul_of_nonneg_right hN (by positivity)
          _ = 1 := by rw [inv_pow, mul_inv_cancel₀ (by positivity)]
      have hNb0 : 0 ≤ (Fintype.card ↥(Gs g) : ℝ) * (4 : ℝ)⁻¹ ^ m := by positivity
      rw [ha, hb] at hros
      refine hdec.trans (mul_le_mul_of_nonneg_left (hros.trans ?_) (Real.exp_pos _).le)
      have t1 : 2 ^ q * ((Fintype.card ↥(Gs g) : ℝ) * (((4 : ℝ)⁻¹ ^ m) ^ q * R')) ≤
          2 ^ q * 4 ^ m * ((4 : ℝ)⁻¹ ^ m) ^ q * R' := by
        rw [mul_assoc (2 ^ q * 4 ^ m), mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN (by positivity))
          (by positivity)
      have t2 : 2 ^ q * ((Fintype.card ↥(Gs g) : ℝ) * (4 : ℝ)⁻¹ ^ m) *
          (2 ^ q * ((Fintype.card ↥(Gs g) : ℝ) * (4 : ℝ)⁻¹ ^ m + 1)) ^ (q - 1) ≤ D0 := by
        refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · exact (mul_le_mul_of_nonneg_left hNb (by positivity)).trans_eq (mul_one _)
        · refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have h0 : ∀ ω, T g ω ^ q = 0 := fun ω => by
        simp only [T, hne, sum_empty]; exact Real.zero_rpow (by linarith)
      simp_rw [h0, integral_zero]
      positivity
  -- assemble
  have hpt : ∀ ω, gM (Z (m + l)) P (m + k) (grid (m + k)) ω ^ q ≤
      4 ^ (q - 1) * ∑ g, T g ω ^ q := fun ω => by
    rw [gM_grid_eq_sum_par]
    have := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (univ : Finset (Fin 2 × Fin 2)) hq
      (f := fun g => T g ω) fun g _ => hT0 g ω
    rw [card_univ] at this
    simpa using this
  calc ∫ ω, gM (Z (m + l)) P (m + k) (grid (m + k)) ω ^ q ∂P
      ≤ ∫ ω, 4 ^ (q - 1) * ∑ g, T g ω ^ q ∂P :=
        integral_mono (hZ.integrable_gM_grid_rpow _ _ hq)
          ((integrable_finsetSum _ fun g _ => hTq g).const_mul _) hpt
    _ = 4 ^ (q - 1) * ∑ g, ∫ ω, T g ω ^ q ∂P := by
        rw [integral_const_mul, integral_finsetSum _ fun g _ => hTq g]
    _ ≤ 4 ^ (q - 1) * ∑ _g : Fin 2 × Fin 2, E * (2 ^ q * 4 ^ m * ((4 : ℝ)⁻¹ ^ m) ^ q * R' + D0) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun g _ => hgrp g) (by positivity)
    _ = thetaR β c q m * R' + constR β c q m := by
        rw [sum_const, card_univ]
        simp only [Fintype.card_prod, Fintype.card_fin, thetaR, constR, nsmul_eq_mul]
        have h4 : (4 : ℝ) ^ (q - 1) * (((2 * 2 : ℕ) : ℝ)) = 4 ^ q := by
          rw [Real.rpow_sub_one (by norm_num)]; push_cast; field_simp
        rw [← h4]
        ring

lemma thetaR_eq (β c q : ℝ) (m : ℕ) :
    thetaR β c q m = 4 ^ q * Real.exp (q * (q - 1) * c) * 2 ^ q *
      (Real.exp (Real.log 2 * ((q - 1) * (q * β / 2 - 2)))) ^ m := by
  have h4 : ((4 : ℝ)⁻¹ ^ m) ^ q = Real.exp (-(2 * Real.log 2) * q) ^ m := by
    rw [← Real.exp_nat_mul, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      Real.rpow_def_of_pos (by norm_num), Real.log_inv,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    congr 1; push_cast; ring
  have h4' : (4 : ℝ) ^ m = Real.exp (2 * Real.log 2) ^ m := by
    rw [← Real.log_rpow (by norm_num), Real.exp_log (by norm_num)]; norm_num
  have he : Real.exp (q * (q - 1) * (β * (m * Real.log 2) + 2 * c) / 2) =
      Real.exp (q * (q - 1) * c) * Real.exp (q * (q - 1) * β * Real.log 2 / 2) ^ m := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have hρ : Real.exp (Real.log 2 * ((q - 1) * (q * β / 2 - 2))) =
      Real.exp (q * (q - 1) * β * Real.log 2 / 2) * Real.exp (2 * Real.log 2) *
        Real.exp (-(2 * Real.log 2) * q) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [thetaR, h4, h4', he, hρ, mul_pow, mul_pow]
  ring

lemma exists_thetaR_le {β c q : ℝ} (hβ : 0 < β) (hq1 : 1 < q) (hq : q < 4 / β) :
    ∃ m : ℕ, 1 ≤ m ∧ thetaR β c q m ≤ 1 / 2 := by
  set ρ := Real.exp (Real.log 2 * ((q - 1) * (q * β / 2 - 2)))
  have hqβ : q * β < 4 := by rwa [lt_div_iff₀ hβ] at hq
  have hρ1 : ρ < 1 := by
    have hneg : Real.log 2 * ((q - 1) * (q * β / 2 - 2)) < 0 :=
      mul_neg_of_pos_of_neg (Real.log_pos (by norm_num))
        (mul_neg_of_pos_of_neg (by linarith) (by linarith))
    have := Real.exp_lt_exp.2 hneg
    rwa [Real.exp_zero] at this
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le hρ1).const_mul
    (4 ^ q * Real.exp (q * (q - 1) * c) * 2 ^ q)
  rw [mul_zero] at ht
  obtain ⟨M, hM⟩ := (ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists_forall_of_atTop
  exact ⟨M + 1, by omega, by rw [thetaR_eq]; exact hM _ (by omega)⟩

/-- **uniform positive moments of the discrete chaos** (BP Theorem 3.23 for the Riemann sums) -/
theorem LogCorr.exists_uniform_moment (hZ : LogCorr Z P β c) (hβ : 0 < β) {q : ℝ} (hq1 : 1 < q)
    (hq : q < 4 / β) :
    ∃ C : ℝ, ∀ n j : ℕ, n ≤ j → ∫ ω, gM (Z n) P j (grid j) ω ^ q ∂P ≤ C := by
  obtain ⟨m, hm1, hθ⟩ := exists_thetaR_le (c := c) hβ hq1 hq
  set D := constR β c q m
  set B := max (Real.exp (q * (q - 1) * (β * (m * Real.log 2) + c) / 2)) (2 * D)
  refine ⟨B, fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro j hnj
    by_cases hnm : n < m
    · refine (hZ.integral_gM_grid_rpow_le_apriori hβ.le n j hq1.le).trans (le_trans ?_ (le_max_left _ _))
      refine Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ (by norm_num))
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by linarith) (by linarith))
      have : (n : ℝ) ≤ m := by exact_mod_cast hnm.le
      have := mul_le_mul_of_nonneg_right this (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
      nlinarith
    · push_neg at hnm
      obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hnm
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (hnm.trans hnj)
      have hlk : l ≤ k := by omega
      have hrec := hZ.recursion hβ.le hq1.le m l k
      have hIH := ih l (by omega) k hlk
      have hD : 2 * D ≤ B := le_max_right _ _
      have := mul_le_mul hθ hIH (integral_nonneg fun ω => Real.rpow_nonneg (gM_nonneg _ _ _ _) _)
        (by norm_num)
      linarith

end DGMC

end LQGMetric
