/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.RecordVarianceAux3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordVarianceAux2

/-!
# Node `V47`, auxiliary file 3: pairwise covariances and geometric summation

* `circCov` is bilinear under concatenation, so the variance of `sumComb c l` is the double
  sum of the pairwise covariances (`circCov_sumComb`);
* Lemma 3.1 with the *fine* pair on the left (`circCov_twoScale_bound_rev`): by the heat-kernel
  averaging `circCov_eq_avg` and the symmetry of `logCov`;
* the pairwise bound for configurations satisfying `CfgGood` (`pair_bound`, `pair_arith`);
* the geometric Schur test `Σ_{i,j} X_ij ≤ 3 D Σ_i A_i²` when
  `|X_ij|, |X_ji| ≤ D A_i A_j 2^{-(j-i)}` for `i ≤ j` (`quad_sum_le`).
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension.RecVar

open Blueprint.Draft

/-! ## Bilinearity -/

lemma circCov_append_left (ε : ℝ) (c₁ c₂ c' : SegComb) :
    SegComb.circCov ε (c₁ ++ c₂) c' = c₁.circCov ε c' + c₂.circCov ε c' := by
  simp [SegComb.circCov, List.map_append, List.sum_append]

lemma circCov_append_right (ε : ℝ) (c c₁ c₂ : SegComb) :
    c.circCov ε (c₁ ++ c₂) = c.circCov ε c₁ + c.circCov ε c₂ := by
  unfold SegComb.circCov
  simp only [List.map_append, List.sum_append]
  exact TwoScale.list_sum_map_add' c _ _

lemma sumComb_succ (c : ℕ → Config) (l : ℕ) :
    sumComb c (l + 1) = sumComb c l ++ cfgComb (c l) := by
  simp [sumComb, List.range_succ, List.flatten_append]

lemma circCov_sumComb_left (ε : ℝ) (c : ℕ → Config) (d : SegComb) (l : ℕ) :
    (sumComb c l).circCov ε d = ∑ i ∈ Finset.range l, (cfgComb (c i)).circCov ε d := by
  induction l with
  | zero => simp [sumComb, SegComb.circCov]
  | succ l ih => rw [sumComb_succ, circCov_append_left, ih, Finset.sum_range_succ]

lemma circCov_sumComb_right (ε : ℝ) (c : ℕ → Config) (d : SegComb) (l : ℕ) :
    d.circCov ε (sumComb c l) = ∑ j ∈ Finset.range l, d.circCov ε (cfgComb (c j)) := by
  induction l with
  | zero => simp [sumComb, SegComb.circCov]
  | succ l ih => rw [sumComb_succ, circCov_append_right, ih, Finset.sum_range_succ]

lemma circCov_sumComb (ε : ℝ) (c : ℕ → Config) (l : ℕ) :
    (sumComb c l).circCov ε (sumComb c l) =
      ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range l,
        (cfgComb (c i)).circCov ε (cfgComb (c j)) := by
  rw [circCov_sumComb_left]
  exact Finset.sum_congr rfl fun i _ => circCov_sumComb_right ε c _ l

/-! ## Lemma 3.1 with the fine pair on the left -/

lemma nondeg_trans (τ : ℂ) {c : SegComb} (hc : c.Nondeg) : (TwoScale.trans τ c).Nondeg := by
  intro p hp hp0
  simp only [TwoScale.trans, SegComb.image, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  intro h
  exact hc q hq hp0 (add_right_cancel h)

/-- **Lemma 3.1, reversed order** (fine pair on the left), for the regularized field. -/
theorem circCov_twoScale_bound_rev {μR νR μr νr : SegComb} {L R u v : ℝ}
    (hμR : μR.IsProb) (hνR : νR.IsProb) (hμr : μr.IsProb) (hνr : νr.IsProb)
    (hR : 0 < R) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hGμ : GrowthBound μR.toMeasure L R) (hGν : GrowthBound νR.toMeasure L R)
    (hcR : CoupledWithin μR.toMeasure νR.toMeasure u)
    (hcr : CoupledWithin μr.toMeasure νr.toMeasure v) (hNd : (μr.sub νr).Nondeg) (ε : ℝ) :
    |(μr.sub νr).circCov ε (μR.sub νR)| ≤ 256 * L * Real.sqrt (u * v) / R := by
  have hm : (μR.sub νR).mass = 0 := by rw [TwoScale.mass_sub, hμR.2, hνR.2]; ring
  have hm' : (μr.sub νr).mass = 0 := by rw [TwoScale.mass_sub, hμr.2, hνr.2]; ring
  rw [TwoScale.circCov_eq_avg ε _ _ hNd hm' hm]
  set B := 256 * L * Real.sqrt (u * v) / R with hB
  have hbd : ∀ᵐ r ∂TwoScale.circSq,
      ‖(TwoScale.trans (TwoScale.cpt ε r.1) (μr.sub νr)).logCov
        (TwoScale.trans (TwoScale.cpt ε r.2) (μR.sub νR))‖ ≤ B :=
    ae_of_all _ fun r => by
      rw [Real.norm_eq_abs, TwoScale.logCov_symm _ _ (nondeg_trans _ hNd)]
      exact TwoScale.logCov_trans_bound hμR hνR hμr hνr hR hu hv hGμ hGν hcR hcr _ _
  have h := norm_integral_le_of_norm_le_const hbd
  rw [TwoScale.circSq_real_univ, Real.norm_eq_abs] at h
  have hpi : (0 : ℝ) < 2 * π := by positivity
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹ ^ 2)]
  calc (2 * π)⁻¹ ^ 2 * |∫ r, (TwoScale.trans (TwoScale.cpt ε r.1) (μr.sub νr)).logCov
        (TwoScale.trans (TwoScale.cpt ε r.2) (μR.sub νR)) ∂TwoScale.circSq|
      ≤ (2 * π)⁻¹ ^ 2 * (B * (2 * π) ^ 2) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = B := by
        rw [inv_pow, mul_comm B, ← mul_assoc, inv_mul_cancel₀ (by positivity : (2 * π) ^ 2 ≠ 0),
          one_mul]

/-! ## Pairs of configurations -/

lemma nondeg_of_good {L R u : ℝ} (hR : 0 < R) {c : Config} (h : CfgGood L R u c) :
    (cfgComb c).Nondeg :=
  TwoScale.nondeg_sub _ _ h.1.1 h.2.1.1 (TwoScale.nondeg_of_growth _ hR h.2.2.1)
    (TwoScale.nondeg_of_growth _ hR h.2.2.2.1)

/-- Lemma 3.1 for a coarse configuration `c` and a fine configuration `c'`, in both orders. -/
lemma pair_bound {L R u L' R' u' : ℝ} (hR : 0 < R) (hR' : 0 < R') (hu : 0 ≤ u) (hu' : 0 ≤ u')
    {c c' : Config} (h : CfgGood L R u c) (h' : CfgGood L' R' u' c') (ε : ℝ) :
    |(cfgComb c).circCov ε (cfgComb c')| ≤ 256 * L * √(u * u') / R ∧
    |(cfgComb c').circCov ε (cfgComb c)| ≤ 256 * L * √(u * u') / R := by
  have hNd := nondeg_of_good hR' h'
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨h1', h2', _, _, h5'⟩ := h'
  exact ⟨TwoScale.circCov_twoScale_bound h1 h2 h1' h2' hR hu hu' h3 h4 h5 h5' ε,
    circCov_twoScale_bound_rev h1 h2 h1' h2' hR hu hu' h3 h4 h5 h5' hNd ε⟩

/-- The arithmetic of the pairwise bound: with `Rj ≤ 4^{-d} Ri`, the normalized covariance is at
most `10752 (gi ki^{1/4}) (gj kj^{1/4}) 2^{-d}`. -/
lemma pair_arith {δ Ri Rj gi gj ki kj Y : ℝ} {d : ℕ} (hδ : 0 < δ) (hRi : 0 < Ri)
    (hRij : Rj ≤ (1 / 4) ^ d * Ri) (hgi : 1 ≤ gi) (hgj : 1 ≤ gj)
    (hB : |Y| ≤ 256 * (7 * gi) * √((Ri * (6 * δ * √ki)) * (Rj * (6 * δ * √kj))) / (Ri * 1)) :
    |δ⁻¹ * Y| ≤ 10752 * (gi * √(√ki)) * (gj * √(√kj)) * (1 / 2) ^ d := by
  set a := √(√ki) with ha
  set b := √(√kj) with hb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = √ki := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hb2 : b ^ 2 = √kj := Real.sq_sqrt (Real.sqrt_nonneg _)
  have h14 : ((1 / 2 : ℝ) ^ d) ^ 2 = (1 / 4) ^ d := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hQ0 : 0 ≤ Ri * (1 / 2) ^ d * (6 * δ) * a * b :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hRi.le (pow_nonneg (by norm_num) _))
      (by linarith)) ha0) hb0
  have hQ : √((Ri * (6 * δ * √ki)) * (Rj * (6 * δ * √kj))) ≤
      Ri * (1 / 2) ^ d * (6 * δ) * a * b := by
    rw [← Real.sqrt_sq hQ0]
    apply Real.sqrt_le_sqrt
    have e : (Ri * (1 / 2) ^ d * (6 * δ) * a * b) ^ 2 =
        (Ri ^ 2 * (1 / 4) ^ d) * ((36 * δ ^ 2) * √ki * √kj) := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow, ha2, hb2, h14]; ring
    rw [e]
    have h1 : Ri * Rj ≤ Ri ^ 2 * (1 / 4) ^ d := by
      have := mul_le_mul_of_nonneg_left hRij hRi.le
      nlinarith
    have h2 : 0 ≤ (36 * δ ^ 2) * √ki * √kj := by positivity
    calc (Ri * (6 * δ * √ki)) * (Rj * (6 * δ * √kj)) =
          (Ri * Rj) * ((36 * δ ^ 2) * √ki * √kj) := by ring
      _ ≤ (Ri ^ 2 * (1 / 4) ^ d) * ((36 * δ ^ 2) * √ki * √kj) :=
          mul_le_mul_of_nonneg_right h1 h2
  have hg0 : 0 ≤ 256 * (7 * gi) := by nlinarith
  rw [abs_mul, abs_of_pos (inv_pos.2 hδ)]
  calc δ⁻¹ * |Y| ≤ δ⁻¹ * (256 * (7 * gi) *
        √((Ri * (6 * δ * √ki)) * (Rj * (6 * δ * √kj))) / (Ri * 1)) :=
        mul_le_mul_of_nonneg_left hB (inv_nonneg.2 hδ.le)
    _ ≤ δ⁻¹ * (256 * (7 * gi) * (Ri * (1 / 2) ^ d * (6 * δ) * a * b) / (Ri * 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hδ.le)
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hQ hg0) (by linarith)
    _ = 10752 * gi * a * b * (1 / 2) ^ d := by
        have hδne := hδ.ne'
        have hRine := hRi.ne'
        field_simp
        ring
    _ ≤ 10752 * (gi * a) * (gj * b) * (1 / 2) ^ d := by
        have h1 : b ≤ gj * b := le_mul_of_one_le_left hb0 hgj
        have h2 : 0 ≤ 10752 * gi * a * (1 / 2 : ℝ) ^ d :=
          mul_nonneg (mul_nonneg (by linarith) ha0) (pow_nonneg (by norm_num) _)
        have h3 := mul_le_mul_of_nonneg_left h1 h2
        linarith

/-! ## Geometric summation -/

lemma geom_step (F : ℕ → ℝ) (l : ℕ) :
    ∑ j ∈ Finset.range (l + 1), (1 / 2 : ℝ) ^ (l + 1 - j) * F j =
      1 / 2 * ∑ j ∈ Finset.range l, (1 / 2 : ℝ) ^ (l - j) * F j + 1 / 2 * F l := by
  rw [Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [show l + 1 - j = (l - j) + 1 by omega, pow_succ]; ring
  · rw [show l + 1 - l = 1 by omega, pow_one]

lemma geom_le_one (l : ℕ) : ∑ j ∈ Finset.range l, (1 / 2 : ℝ) ^ (l - j) * 1 ≤ 1 := by
  induction l with
  | zero => simp
  | succ l ih => rw [geom_step]; linarith

/-- **Geometric Schur test.** -/
lemma quad_sum_le (X : ℕ → ℕ → ℝ) (A : ℕ → ℝ) {D : ℝ} (hD : 0 ≤ D) (l : ℕ) (hX : ∀ i j, i ≤ j → j < l →
      |X i j| ≤ D * A i * A j * (1 / 2) ^ (j - i) ∧ |X j i| ≤ D * A i * A j * (1 / 2) ^ (j - i)) :
    ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range l, X i j ≤
      3 * D * ∑ i ∈ Finset.range l, A i ^ 2 := by
  let T : ℕ → ℝ := fun l => ∑ j ∈ Finset.range l, (1 / 2 : ℝ) ^ (l - j) * A j ^ 2
  have hT0 : ∀ l, 0 ≤ T l := fun l =>
    Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg (by norm_num) _) (sq_nonneg _)
  have key : ∀ l', l' ≤ l → ∑ i ∈ Finset.range l', ∑ j ∈ Finset.range l', X i j + 2 * D * T l' ≤
      3 * D * ∑ i ∈ Finset.range l', A i ^ 2 := by
    intro l' hl'
    induction l' with
    | zero => simp [T]
    | succ l' ih =>
      have ih := ih (by omega)
      have hl'l : l' < l := by omega
      have hexp : ∑ i ∈ Finset.range (l' + 1), ∑ j ∈ Finset.range (l' + 1), X i j =
          ∑ i ∈ Finset.range l', ∑ j ∈ Finset.range l', X i j +
            ∑ i ∈ Finset.range l', (X i l' + X l' i) + X l' l' := by
        simp only [Finset.sum_range_succ, Finset.sum_add_distrib]; ring
      have hcross : ∑ i ∈ Finset.range l', (X i l' + X l' i) ≤
          D * T l' + D * A l' ^ 2 * ∑ j ∈ Finset.range l', (1 / 2 : ℝ) ^ (l' - j) * 1 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        obtain ⟨b1, b2⟩ := hX i l' hi'.le hl'l
        have hp : 0 ≤ (1 / 2 : ℝ) ^ (l' - i) := pow_nonneg (by norm_num) _
        have hsq := mul_nonneg (mul_nonneg hD hp) (sq_nonneg (A i - A l'))
        nlinarith [le_abs_self (X i l'), le_abs_self (X l' i)]
      have hdiag : X l' l' ≤ D * A l' ^ 2 := by
        have := (hX l' l' le_rfl hl'l).1
        rw [Nat.sub_self, pow_zero] at this
        nlinarith [le_abs_self (X l' l')]
      have hTs : T (l' + 1) = 1 / 2 * T l' + 1 / 2 * A l' ^ 2 := geom_step (fun j => A j ^ 2) l'
      have hU := geom_le_one l'
      have hA2 : 0 ≤ D * A l' ^ 2 := mul_nonneg hD (sq_nonneg _)
      rw [hexp, hTs, Finset.sum_range_succ]
      have : D * A l' ^ 2 * ∑ j ∈ Finset.range l', (1 / 2 : ℝ) ^ (l' - j) * 1 ≤ D * A l' ^ 2 :=
        by nlinarith
      nlinarith
  have := key l le_rfl
  have := hT0 l
  nlinarith

/-- Iterating the scale hypothesis. -/
lemma scale_le {n : ℕ} (hn : 1 ≤ n) {l : ℕ} {s : ℕ → ℂ × ℂ}
    (hs : ∀ i, i + 1 < l → ‖(s (i + 1)).1‖ ≤ 4 / (16 : ℝ) ^ n * ‖(s i).1‖) :
    ∀ i j, i ≤ j → j < l → ‖(s j).1‖ ≤ (1 / 4) ^ (j - i) * ‖(s i).1‖ := by
  have h4 : 4 / (16 : ℝ) ^ n ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (16 : ℝ) ≤ 16 ^ n := le_self_pow₀ (by norm_num) (by omega)
    linarith
  intro i j hij hjl
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; simp
  | succ j ih =>
    rcases Nat.lt_or_ge j i with h | h
    · have : i = j + 1 := by omega
      subst this; simp
    · have ih' := ih h (by omega)
      calc ‖(s (j + 1)).1‖ ≤ 4 / (16 : ℝ) ^ n * ‖(s j).1‖ := hs j hjl
        _ ≤ 1 / 4 * ((1 / 4) ^ (j - i) * ‖(s i).1‖) :=
            mul_le_mul h4 ih' (norm_nonneg _) (by norm_num)
        _ = (1 / 4) ^ (j + 1 - i) * ‖(s i).1‖ := by
            rw [show j + 1 - i = (j - i) + 1 by omega, pow_succ]; ring

end LQGDimension.RecVar
