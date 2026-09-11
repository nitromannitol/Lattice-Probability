/-
Quantitative probability bounds for continuous processes on finite-dimensional boxes.
-/
import LatticeProb.Prob.ChentsovPiProcess
import LatticeProb.Prob.ChentsovPiLimit

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped ENNReal NNReal

def LatticeProb.boxClamp {k : ℕ} (a b : Fin k → ℝ) (hab : a ≤ b)
    (x : Fin k → ℝ) : Fin k → ℝ := fun i => Set.projIcc (a i) (b i) (hab i) (x i)

theorem LatticeProb.boxClamp_mem {k : ℕ} (a b : Fin k → ℝ) (hab : a ≤ b)
    (x : Fin k → ℝ) : boxClamp a b hab x ∈ Set.Icc a b := by
  unfold boxClamp
  rw [Set.mem_Icc]
  constructor
  · simp only [Pi.le_def]
    intro i
    exact (Set.projIcc (a i) (b i) (hab i) (x i)).property.1
  · simp only [Pi.le_def]
    intro i
    exact (Set.projIcc (a i) (b i) (hab i) (x i)).property.2

theorem LatticeProb.boxClamp_eq {k : ℕ} {a b x : Fin k → ℝ} (hab : a ≤ b)
    (hx : x ∈ Set.Icc a b) : boxClamp a b hab x = x := by
  funext i
  exact congrArg Subtype.val (Set.projIcc_of_mem (hab i) ⟨hx.1 i, hx.2 i⟩)

theorem LatticeProb.dist_boxClamp_le {k : ℕ} (a b : Fin k → ℝ) (hab : a ≤ b)
    (x y : Fin k → ℝ) : dist (boxClamp a b hab x) (boxClamp a b hab y) ≤ dist x y := by
  refine (dist_pi_le_iff dist_nonneg).mpr ?_
  intro i
  change |(Set.projIcc (a i) (b i) (hab i) (x i) : ℝ) - Set.projIcc (a i) (b i) (hab i) (y i)| ≤ dist x y
  exact (Set.abs_projIcc_sub_projIcc (hab i)).trans (dist_le_pi_dist x y i)

theorem LatticeProb.continuous_boxClamp {k : ℕ} (a b : Fin k → ℝ) (hab : a ≤ b) :
    Continuous (boxClamp a b hab) := by
  apply continuous_pi
  intro i
  change Continuous (fun x : Fin k → ℝ => max (a i) (min (b i) (x i)))
  fun_prop

theorem LatticeProb.exists_incr_exponent_pi (k : ℕ) {p q : ℝ} (hp : 0 < p) (hq : (k : ℝ) < q) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ (2 : ℝ) ^ ((k : ℝ) - q) / c ^ p < 1 := by
  set β : ℝ := (2 : ℝ) ^ (((k : ℝ) - q) / p) with hβdef
  have hβpos : 0 < β := Real.rpow_pos_of_pos (by norm_num) _
  have hβlt : β < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
    exact div_neg_of_neg_of_pos (sub_neg.mpr hq) hp
  refine ⟨(β + 1) / 2, by positivity, by linarith, ?_⟩
  have hβb : β < (β + 1) / 2 := by linarith
  have hpow : β ^ p < ((β + 1) / 2) ^ p := Real.rpow_lt_rpow hβpos.le hβb hp
  have hβp : β ^ p = (2 : ℝ) ^ ((k : ℝ) - q) := by
    rw [hβdef, ← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ hp.ne']
  rw [div_lt_one (by positivity), ← hβp]
  exact hpow

theorem LatticeProb.measure_abs_ge_le_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {f : Ω → ℝ} {p r C : ℝ}
    (hp : 0 < p) (hr : 0 < r) (hint : Integrable (fun ω => |f ω| ^ p) P)
    (hbound : ∫ ω, |f ω| ^ p ∂P ≤ C) :
    P {ω | r ≤ |f ω|} ≤ ENNReal.ofReal (C / r ^ p) := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (abs_nonneg (f ω)) p)) hint (r ^ p)
  have hsub : {ω | r ≤ |f ω|} ⊆ {ω | r ^ p ≤ |f ω| ^ p} :=
    fun ω hω => Real.rpow_le_rpow hr.le hω hp.le
  calc
    P {ω | r ≤ |f ω|} ≤ P {ω | r ^ p ≤ |f ω| ^ p} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | r ^ p ≤ |f ω| ^ p}) :=
      (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
    _ ≤ ENNReal.ofReal (C / r ^ p) := by
      apply ENNReal.ofReal_le_ofReal
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hr p)).mpr
      simpa [mul_comm] using hmarkov.trans hbound

theorem LatticeProb.tendsto_dtruncPi_point {k : ℕ} (z : Fin k → ℝ) :
    Tendsto (fun n => dtruncPi n z) atTop (𝓝 z) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have hle : ∀ n, dtruncPi n z i ≤ z i := fun n => dtruncPi_le n z i
  have hlt : ∀ n, z i - dtruncPi n z i < 1 / 2 ^ n := fun n => sub_dtruncPi_lt n z i
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hdiff := squeeze_zero (fun n => sub_nonneg.mpr (hle n))
    (fun n => by simpa only [one_div_pow] using (hlt n).le) hpow
  have h := (tendsto_const_nhds (x := z i)).sub hdiff
  simpa only [sub_sub_cancel, sub_zero] using h

theorem LatticeProb.dyadicIncBoundPi_of_notMem {k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {X : (Fin k → ℝ) → Ω → ℝ} {r : ℕ → ℝ} {ω : Ω} {n₀ : ℕ}
    (h : ∀ n, n₀ ≤ n → ω ∉ badSetPi X r (n + 1) n) :
    DyadicIncBoundPi (fun t => X t ω) r n₀ := by
  intro n hn j hj i
  have hnot := h n hn
  have hmem : j ∈ boxIdx (n + 1) n := by
    rw [mem_boxIdx_iff]
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] using hj
  apply le_of_lt
  apply lt_of_not_ge
  intro hh
  apply hnot
  simp only [badSetPi, Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨i, j, hmem, hh⟩

theorem LatticeProb.card_boxIdx_level_le (k n : ℕ) :
    ((boxIdx (k := k) (n + 1) n).card : ℝ) ≤
      (3 : ℝ) ^ k * (n + 1 : ℝ) ^ k * ((2 : ℝ) ^ k) ^ n := by
  rw [card_boxIdx]
  push_cast
  have htwo : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  calc
    (2 * (((n : ℝ) + 1) * 2 ^ n) + 1) ^ k ≤ (3 * ((n : ℝ) + 1) * 2 ^ n) ^ k := by
      gcongr
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith [hn]
    _ = (3 : ℝ) ^ k * (n + 1 : ℝ) ^ k * ((2 : ℝ) ^ k) ^ n := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm n k]

theorem LatticeProb.summable_polynomial_geometric (k : ℕ) {θ C : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    Summable (fun n : ℕ => C * (n + 1 : ℝ) ^ k * θ ^ n) := by
  have hbase := summable_pow_mul_geometric_of_norm_lt_one k
    (show ‖θ‖ < 1 by simpa [Real.norm_eq_abs, abs_of_pos hθ0] using hθ1)
  have hshift := (summable_nat_add_iff 1).2 hbase
  have hh := (hshift.div_const θ).mul_left C
  apply hh.congr
  intro n
  simp [Nat.cast_add, Nat.cast_one, pow_succ, mul_div_assoc, hθ0.ne', mul_assoc]

theorem LatticeProb.measure_badSetPi_le {k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {X : (Fin k → ℝ) → Ω → ℝ}
    {p q M : ℝ} (hp : 0 < p)
    (hint : ∀ u v, Integrable (fun ω => |X u ω - X v ω| ^ p) P)
    (hbound : ∀ u v, ∫ ω, |X u ω - X v ω| ^ p ∂P ≤ M * dist u v ^ q)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (m n : ℕ) :
    P (badSetPi X r m n) ≤ (k : ℝ≥0∞) * (boxIdx (k := k) m n).card *
      ENNReal.ofReal (M * (1 / 2 ^ n : ℝ) ^ q / (r n) ^ p) := by
  have hedge : ∀ (j : Fin k → ℤ) (i : Fin k),
      P {ω | r n ≤ |X (gridPt n (j + Pi.single i 1)) ω - X (gridPt n j) ω|} ≤
        ENNReal.ofReal (M * (1 / 2 ^ n : ℝ) ^ q / (r n) ^ p) := by
    intro j i
    have hd := congrArg ENNReal.toReal (edist_gridPt_step n j i)
    simp only [edist_dist, ENNReal.toReal_ofReal dist_nonneg,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / 2 ^ n)] at hd
    have hb := measure_abs_ge_le_moment P hp (hr n) (hint (gridPt n (j + Pi.single i 1)) (gridPt n j))
      (hbound (gridPt n (j + Pi.single i 1)) (gridPt n j))
    rw [hd] at hb
    exact hb
  unfold badSetPi
  refine (measure_iUnion_fintype_le P _).trans ?_
  calc
    _ ≤ ∑ i : Fin k, ∑ j ∈ boxIdx m n,
        ENNReal.ofReal (M * (1 / 2 ^ n : ℝ) ^ q / (r n) ^ p) := by
      apply Finset.sum_le_sum
      intro i _
      exact (measure_biUnion_finset_le _ _).trans
        (Finset.sum_le_sum (fun j _ => hedge j i))
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

theorem LatticeProb.exists_level_of_summable (k R : ℕ) {r g : ℕ → ℝ}
    (hr : Summable r) (hg : Summable g) (hg0 : ∀ n, 0 ≤ g n)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ N : ℕ, R ≤ N ∧ 2 * ((k : ℝ) * dtail r N) + (k : ℝ) * r N < η ∧
      (∑' j : ℕ, ENNReal.ofReal (g (j + N))) ≤ ENNReal.ofReal ε := by
  have hfinite : (∑' n, ENNReal.ofReal (g n)) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hg0 hg]
    exact ENNReal.ofReal_ne_top
  have htail := ENNReal.tendsto_sum_nat_add (fun n => ENNReal.ofReal (g n)) hfinite
  have hrzero := hr.tendsto_atTop_zero
  have hd := tendsto_dtail r
  have hc : Tendsto (fun N => 2 * ((k : ℝ) * dtail r N) + (k : ℝ) * r N)
      atTop (𝓝 0) := by
    simpa using ((hd.const_mul (k : ℝ)).const_mul 2).add (hrzero.const_mul (k : ℝ))
  have hdet := hc.eventually (gt_mem_nhds hη)
  have hprob := htail.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε))
  have hevent : ∀ᶠ N : ℕ in atTop, R ≤ N ∧
      2 * ((k : ℝ) * dtail r N) + (k : ℝ) * r N < η ∧
      (∑' j : ℕ, ENNReal.ofReal (g (j + N))) ≤ ENNReal.ofReal ε := by
    filter_upwards [eventually_ge_atTop R, hdet, hprob] with N hR hD hP
    exact ⟨hR, hD, hP.le⟩
  exact hevent.exists

theorem LatticeProb.geometric_grid_factor (k n : ℕ) (p q : ℝ) {c : ℝ} (hc : 0 < c) :
    ((2 : ℝ) ^ k) ^ n * (1 / 2 ^ n : ℝ) ^ q / (c ^ n) ^ p =
      ((2 : ℝ) ^ ((k : ℝ) - q) / c ^ p) ^ n := by
  have hnum : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ q = (2 : ℝ) ^ ((k : ℝ) - q) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, one_div, Real.inv_rpow (by norm_num), div_eq_mul_inv]
  rw [show (1 / 2 ^ n : ℝ) = (1 / 2 : ℝ) ^ n by rw [one_div_pow],
    rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2) q n, rpow_pow_comm hc.le p n,
    ← mul_pow, ← div_pow, hnum]

theorem LatticeProb.dlimPi_eq_of_continuous {k : ℕ} {f : (Fin k → ℝ) → ℝ}
    (hf : Continuous f) (z : Fin k → ℝ) : dlimPi f z = f z := by
  have ht : Tendsto (fun n => f (dtruncPi n z)) atTop (𝓝 (f z)) :=
    (hf.tendsto z).comp (tendsto_dtruncPi_point z)
  exact ht.limsup_eq
