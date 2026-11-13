/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P4ScaleVariance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4HarmonicCov

 
















set_option autoImplicit false
noncomputable section

open Finset MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.QPos.P4

 
def scaleSites (n : ℕ) (z : ℤ × ℤ) (k : ℕ) : Finset (DGFFSite n) :=
  boxSites n z (2 ^ (n - k))

 
def inReg (n : ℕ) (z : ℤ × ℤ) (k : ℕ) (c : DGFFSite n) : Prop :=
  8 * |c.1.1 - z.1| ≤ 6 * 2 ^ (n - k) ∧ 8 * |c.1.2 - z.2| ≤ 6 * 2 ^ (n - k)

 
def GoodScale (n : ℕ) (z : ℤ × ℤ) (k : ℕ) : Prop :=
  k + 4 ≤ n ∧ sqBox z (2 ^ (n - k)) ⊆ interiorSites n

theorem mem_scaleSites_of_inReg {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k)
    {c : DGFFSite n} (hc : inReg n z k c) : c ∈ scaleSites n z k := by
  unfold scaleSites boxSites siteFilter
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [mem_sqBox]
  obtain ⟨h1, h2⟩ := hc
  have hp : (0 : ℤ) < 2 ^ (n - k) := by positivity
  constructor <;> linarith

theorem inReg_mono {n : ℕ} {z : ℤ × ℤ} {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ n) {c : DGFFSite n}
    (hc : inReg n z k c) : inReg n z j c := by
  obtain ⟨h1, h2⟩ := hc
  have : (2 : ℤ) ^ (n - k) ≤ 2 ^ (n - j) := pow_le_pow_right₀ (by norm_num) (by omega)
  constructor <;> linarith

theorem scaleSites_anti {n : ℕ} {z : ℤ × ℤ} {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ n) :
    scaleSites n z k ⊆ scaleSites n z j := by
  intro c hc
  unfold scaleSites boxSites siteFilter at hc ⊢
  rw [Finset.mem_filter] at hc ⊢
  refine ⟨hc.1, ?_⟩
  have : (2 : ℤ) ^ (n - k) ≤ 2 ^ (n - j) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact sqBox_mono this hc.2

 
theorem coarse_increment_variance' (n m : ℕ) (hm : 4 ≤ m) (z : ℤ × ℤ)
    (hQ : sqBox z (2 ^ m) ⊆ interiorSites n)
    (i j : {c : DGFFSite n // c ∈ boxSites n z (2 ^ m)})
    (hi1 : 8 * |i.1.1.1 - z.1| ≤ 6 * 2 ^ m) (hi2 : 8 * |i.1.1.2 - z.2| ≤ 6 * 2 ^ m)
    (hj1 : 8 * |j.1.1.1 - z.1| ≤ 6 * 2 ^ m) (hj2 : 8 * |j.1.1.2 - z.2| ≤ 6 * 2 ^ m)
    (d : ℕ) (hd1 : |i.1.1.1 - j.1.1.1| ≤ d) (hd2 : |i.1.1.2 - j.1.1.2| ≤ d) :
    Var[fun h : EuclideanSpace ℝ (DGFFSite n) =>
        boxHarmonicField n (boxInnerOuterEquiv n (boxSites n z (2 ^ m))) h i -
          boxHarmonicField n (boxInnerOuterEquiv n (boxSites n z (2 ^ m))) h j;
        boxDGFF n] ≤ coarseVarConst * d / (2 ^ m : ℝ) := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 4 := ⟨m - 4, by omega⟩
  exact coarse_increment_variance n a z hQ i j hi1 hi2 hj1 hj2 d hd1 hd2

 
theorem var_hfun_incr_le {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k)
    {x y : DGFFSite n} (hx : inReg n z k x) (hy : inReg n z k y) (d : ℕ)
    (hd1 : |x.1.1 - y.1.1| ≤ d) (hd2 : |x.1.2 - y.1.2| ≤ d) :
    Var[fun h : EuclideanSpace ℝ (DGFFSite n) =>
        hfun n (scaleSites n z k) h x - hfun n (scaleSites n z k) h y; boxDGFF n] ≤
      coarseVarConst * d / (2 ^ (n - k) : ℝ) := by
  have hxS := mem_scaleSites_of_inReg hk hx
  have hyS := mem_scaleSites_of_inReg hk hy
  have key := coarse_increment_variance' n (n - k) (by have := hk.1; omega) z hk.2
    ⟨x, hxS⟩ ⟨y, hyS⟩ hx.1 hx.2 hy.1 hy.2 d hd1 hd2
  have e : (fun h : EuclideanSpace ℝ (DGFFSite n) =>
        hfun n (scaleSites n z k) h x - hfun n (scaleSites n z k) h y) =
      fun h => boxHarmonicField n (boxInnerOuterEquiv n (boxSites n z (2 ^ (n - k)))) h
          ⟨x, hxS⟩ -
        boxHarmonicField n (boxInnerOuterEquiv n (boxSites n z (2 ^ (n - k)))) h
          ⟨y, hyS⟩ := by
    funext h
    rw [hfun_of_mem hxS, hfun_of_mem hyS]
    rfl
  rw [e]
  exact key

 
theorem inReg_dist {n : ℕ} {z : ℤ × ℤ} {k : ℕ} {x y : DGFFSite n} (hx : inReg n z k x)
    (hy : inReg n z k y) :
    |x.1.1 - y.1.1| ≤ ((2 * 2 ^ (n - k) : ℕ) : ℤ) ∧ |x.1.2 - y.1.2| ≤ ((2 * 2 ^ (n - k) : ℕ) : ℤ) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  push_cast
  have hp : (0 : ℤ) < 2 ^ (n - k) := by positivity
  constructor
  · have := abs_sub_le x.1.1 z.1 y.1.1
    have := abs_sub_comm y.1.1 z.1
    nlinarith [abs_nonneg (x.1.1 - z.1), abs_nonneg (y.1.1 - z.1)]
  · have := abs_sub_le x.1.2 z.2 y.1.2
    have := abs_sub_comm y.1.2 z.2
    nlinarith [abs_nonneg (x.1.2 - z.2), abs_nonneg (y.1.2 - z.2)]

 
def incrK (n : ℕ) (z : ℤ × ℤ) (k : ℕ) (x y : DGFFSite n)
    (h : EuclideanSpace ℝ (DGFFSite n)) : ℝ :=
  hfun n (scaleSites n z k) h x - hfun n (scaleSites n z k) h y

theorem incrK_memLp (n : ℕ) (z : ℤ × ℤ) (k : ℕ) (x y : DGFFSite n) :
    MemLp (incrK n z k x y) 2 (boxDGFF n) :=
  (hfun_memLp n _ x).sub (hfun_memLp n _ y)

 
theorem var_incrK_le {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k)
    {x y : DGFFSite n} (hx : inReg n z k x) (hy : inReg n z k y) :
    Var[incrK n z k x y; boxDGFF n] ≤ 2 * coarseVarConst := by
  obtain ⟨d1, d2⟩ := inReg_dist hx hy
  have h := var_hfun_incr_le hk hx hy (2 * 2 ^ (n - k)) d1 d2
  have hp : (0 : ℝ) < 2 ^ (n - k) := by positivity
  have e : coarseVarConst * ((2 * 2 ^ (n - k) : ℕ) : ℝ) / (2 ^ (n - k) : ℝ) =
      2 * coarseVarConst := by push_cast; field_simp
  rw [e] at h
  exact h

 

theorem var_incr_coarse_le {n : ℕ} {z : ℤ × ℤ} {j k : ℕ} (hjk : j ≤ k) (hj : GoodScale n z j)
    (hkn : k ≤ n) {x y : DGFFSite n} (hx : inReg n z k x) (hy : inReg n z k y) :
    Var[incrK n z j x y; boxDGFF n] ≤ 2 * coarseVarConst * (1 / 2) ^ (k - j) := by
  obtain ⟨d1, d2⟩ := inReg_dist hx hy
  have h := var_hfun_incr_le hj (inReg_mono hjk hkn hx) (inReg_mono hjk hkn hy)
    (2 * 2 ^ (n - k)) d1 d2
  have hp : (0 : ℝ) < 2 ^ (n - j) := by positivity
  have hsplit : (2 : ℝ) ^ (n - j) = 2 ^ (n - k) * 2 ^ (k - j) := by
    rw [← pow_add]; congr 1; omega
  have e : coarseVarConst * ((2 * 2 ^ (n - k) : ℕ) : ℝ) / (2 ^ (n - j) : ℝ) =
      2 * coarseVarConst * (1 / 2) ^ (k - j) := by
    rw [hsplit]; push_cast
    rw [one_div_pow]
    field_simp
  rw [e] at h
  exact h

 
theorem cov_incrK_eq {n : ℕ} {z : ℤ × ℤ} {j k : ℕ} (hjk : j ≤ k) (hj : GoodScale n z j)
    (hk : GoodScale n z k) {x y u v : DGFFSite n} (hx : inReg n z j x) (hy : inReg n z j y)
    (hu : inReg n z k u) (hv : inReg n z k v) :
    cov[incrK n z j x y, incrK n z k u v; boxDGFF n] =
      cov[incrK n z j x y, incrK n z j u v; boxDGFF n] := by
  have hSS : scaleSites n z k ⊆ scaleSites n z j := scaleSites_anti hjk (by have := hk.1; omega)
  have hxS := mem_scaleSites_of_inReg hj hx
  have hyS := mem_scaleSites_of_inReg hj hy
  have huS := mem_scaleSites_of_inReg hk hu
  have hvS := mem_scaleSites_of_inReg hk hv
  have e1 : incrK n z k u v = fun h => hfun n (scaleSites n z k) h u -
      hfun n (scaleSites n z k) h v := rfl
  have e2 : incrK n z j u v = fun h => hfun n (scaleSites n z j) h u -
      hfun n (scaleSites n z j) h v := rfl
  rw [e1, e2]
  rw [covariance_fun_sub_right (incrK_memLp n z j x y) (hfun_memLp n _ u) (hfun_memLp n _ v),
    covariance_fun_sub_right (incrK_memLp n z j x y) (hfun_memLp n _ u) (hfun_memLp n _ v)]
  have e3 : incrK n z j x y = fun h => hfun n (scaleSites n z j) h x -
      hfun n (scaleSites n z j) h y := rfl
  rw [e3]
  rw [covariance_fun_sub_left (hfun_memLp n _ x) (hfun_memLp n _ y) (hfun_memLp n _ u),
    covariance_fun_sub_left (hfun_memLp n _ x) (hfun_memLp n _ y) (hfun_memLp n _ v),
    covariance_fun_sub_left (hfun_memLp n _ x) (hfun_memLp n _ y) (hfun_memLp n _ u),
    covariance_fun_sub_left (hfun_memLp n _ x) (hfun_memLp n _ y) (hfun_memLp n _ v)]
  rw [hfun_cross_cov n hSS hxS huS, hfun_cross_cov n hSS hyS huS,
    hfun_cross_cov n hSS hxS hvS, hfun_cross_cov n hSS hyS hvS]

 
theorem sum_pow_le_geom (T : Finset ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ m ∈ T, r ^ m ≤ 1 / (1 - r) := by
  have h := Summable.sum_le_tsum T (fun m _ => pow_nonneg hr0 m)
    (summable_geometric_of_lt_one hr0 hr1)
  rw [tsum_geometric_of_lt_one hr0 hr1] at h
  simpa [one_div] using h

 
theorem sum_pow_dist_le (W : Finset ℕ) (j : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ k ∈ W, r ^ ((k - j) + (j - k)) ≤ 2 / (1 - r) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not W (fun k => j ≤ k)]
  have hA : ∑ k ∈ W.filter (fun k => j ≤ k), r ^ ((k - j) + (j - k)) ≤ 1 / (1 - r) := by
    have e : ∑ k ∈ W.filter (fun k => j ≤ k), r ^ ((k - j) + (j - k)) =
        ∑ m ∈ (W.filter (fun k => j ≤ k)).image (fun k => k - j), r ^ m := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_filter] at hk
        rw [show j - k = 0 by omega, add_zero]
      · intro a ha b hb hab
        rw [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
        simp only at hab
        omega
    rw [e]
    exact sum_pow_le_geom _ hr0 hr1
  have hB : ∑ k ∈ W.filter (fun k => ¬ j ≤ k), r ^ ((k - j) + (j - k)) ≤ 1 / (1 - r) := by
    have e : ∑ k ∈ W.filter (fun k => ¬ j ≤ k), r ^ ((k - j) + (j - k)) =
        ∑ m ∈ (W.filter (fun k => ¬ j ≤ k)).image (fun k => j - k), r ^ m := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_filter] at hk
        rw [show k - j = 0 by omega, zero_add]
      · intro a ha b hb hab
        rw [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
        simp only at hab
        omega
    rw [e]
    exact sum_pow_le_geom _ hr0 hr1
  have : 2 / (1 - r) = 1 / (1 - r) + 1 / (1 - r) := by ring
  rw [this]
  exact add_le_add hA hB

theorem sqrt_half_pow (m : ℕ) : Real.sqrt ((1 / 2 : ℝ) ^ m) = (Real.sqrt (1 / 2)) ^ m := by
  have h : (1 / 2 : ℝ) ^ m = ((Real.sqrt (1 / 2)) ^ m) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
  rw [h, Real.sqrt_sq (by positivity)]

 
theorem cov_incrK_le {n : ℕ} {z : ℤ × ℤ} {j k : ℕ} (hjk : j ≤ k) (hj : GoodScale n z j)
    (hk : GoodScale n z k) {x y u v : DGFFSite n} (hx : inReg n z j x) (hy : inReg n z j y)
    (hu : inReg n z k u) (hv : inReg n z k v) :
    cov[incrK n z j x y, incrK n z k u v; boxDGFF n] ≤
      2 * coarseVarConst * (Real.sqrt (1 / 2)) ^ (k - j) := by
  rw [cov_incrK_eq hjk hj hk hx hy hu hv]
  refine (covariance_le_sqrt (incrK_memLp n z j x y) (incrK_memLp n z j u v)).trans ?_
  have h1 := var_incrK_le hj hx hy
  have h2 := var_incr_coarse_le hjk hj (by have := hk.1; omega) hu hv
  have hv0 : 0 ≤ coarseVarConst := coarseVarConst_pos.le
  calc Real.sqrt (Var[incrK n z j x y; boxDGFF n]) * Real.sqrt (Var[incrK n z j u v; boxDGFF n])
      ≤ Real.sqrt (2 * coarseVarConst) *
          Real.sqrt (2 * coarseVarConst * (1 / 2) ^ (k - j)) := by
        gcongr
    _ = 2 * coarseVarConst * (Real.sqrt (1 / 2)) ^ (k - j) := by
        rw [Real.sqrt_mul (by positivity) ((1 / 2 : ℝ) ^ (k - j)), sqrt_half_pow,
          ← mul_assoc, Real.mul_self_sqrt (by positivity)]

 

theorem var_sum_scales_le (n : ℕ) (z : ℤ × ℤ) (W : Finset ℕ)
    (hW : ∀ k ∈ W, GoodScale n z k) (u v : ℕ → DGFFSite n)
    (hu : ∀ k ∈ W, inReg n z k (u k)) (hv : ∀ k ∈ W, inReg n z k (v k)) :
    Var[fun h => ∑ k ∈ W, incrK n z k (u k) (v k) h; boxDGFF n] ≤
      14 * coarseVarConst * W.card := by
  rw [variance_fun_sum' (fun k _ => incrK_memLp n z k (u k) (v k))]
  set r : ℝ := Real.sqrt (1 / 2)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hterm : ∀ j ∈ W, ∀ k ∈ W,
      cov[incrK n z j (u j) (v j), incrK n z k (u k) (v k); boxDGFF n] ≤
        2 * coarseVarConst * r ^ ((k - j) + (j - k)) := by
    intro j hj k hk
    rcases le_total j k with hjk | hkj
    · rw [show j - k = 0 by omega, add_zero]
      exact cov_incrK_le hjk (hW j hj) (hW k hk) (hu j hj) (hv j hj) (hu k hk) (hv k hk)
    · rw [show k - j = 0 by omega, zero_add, covariance_comm]
      exact cov_incrK_le hkj (hW k hk) (hW j hj) (hu k hk) (hv k hk) (hu j hj) (hv j hj)
  have hv0 : 0 ≤ coarseVarConst := coarseVarConst_pos.le
  calc ∑ j ∈ W, ∑ k ∈ W, cov[incrK n z j (u j) (v j), incrK n z k (u k) (v k); boxDGFF n]
      ≤ ∑ j ∈ W, ∑ k ∈ W, 2 * coarseVarConst * r ^ ((k - j) + (j - k)) :=
        Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => hterm j hj k hk
    _ = ∑ j ∈ W, 2 * coarseVarConst * ∑ k ∈ W, r ^ ((k - j) + (j - k)) := by
        simp_rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ W, 2 * coarseVarConst * (2 / (1 - r)) := by
        gcongr with j hj
        exact sum_pow_dist_le W j hr0 hr1
    _ = W.card * (2 * coarseVarConst * (2 / (1 - r))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 14 * coarseVarConst * W.card := by
        have hr57 : r ≤ 5 / 7 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        have h1r : 0 < 1 - r := by linarith
        have : 2 / (1 - r) ≤ 7 := by
          rw [div_le_iff₀ h1r]; linarith
        have hc : (0 : ℝ) ≤ W.card * (2 * coarseVarConst) := by positivity
        have := mul_le_mul_of_nonneg_left this hc
        nlinarith

end SupercriticalLQGUniqueness.B2.QPos.P4
