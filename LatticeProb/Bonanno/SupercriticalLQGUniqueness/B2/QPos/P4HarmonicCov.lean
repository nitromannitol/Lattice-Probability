/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P4HarmonicCov at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4CoarseVariance

 

















set_option autoImplicit false
noncomputable section

open Finset MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.QPos.P4

 

def hfun (n : ℕ) (S : Finset (DGFFSite n)) (h : EuclideanSpace ℝ (DGFFSite n))
    (c : DGFFSite n) : ℝ :=
  if hc : c ∈ S then boxHarmonicField n (boxInnerOuterEquiv n S) h ⟨c, hc⟩ else h c

 
def resid (n : ℕ) (S : Finset (DGFFSite n)) (h : EuclideanSpace ℝ (DGFFSite n))
    (c : DGFFSite n) : ℝ :=
  if hc : c ∈ S then (boxResidualField n (boxInnerOuterEquiv n S) h).1 ⟨c, hc⟩ else 0

theorem hfun_of_mem {n : ℕ} {S : Finset (DGFFSite n)} {c : DGFFSite n} (hc : c ∈ S)
    (h : EuclideanSpace ℝ (DGFFSite n)) :
    hfun n S h c = boxHarmonicField n (boxInnerOuterEquiv n S) h ⟨c, hc⟩ := dif_pos hc

theorem hfun_of_not_mem {n : ℕ} {S : Finset (DGFFSite n)} {c : DGFFSite n} (hc : c ∉ S)
    (h : EuclideanSpace ℝ (DGFFSite n)) : hfun n S h c = h c := dif_neg hc

theorem hfun_add_resid (n : ℕ) (S : Finset (DGFFSite n)) (h : EuclideanSpace ℝ (DGFFSite n))
    (c : DGFFSite n) : h c = hfun n S h c + resid n S h c := by
  unfold hfun resid
  split_ifs with hc
  · unfold boxHarmonicField
    rw [boxSplitField_apply_left]
    have : (boxInnerOuterEquiv n S).symm (Sum.inl ⟨c, hc⟩) = c := rfl
    rw [this]; ring
  · ring

 
theorem hfun_eq_sum (n : ℕ) (S : Finset (DGFFSite n)) {c : DGFFSite n} (hc : c ∈ S) :
    ∃ α : DGFFSite n → ℝ, (∀ c' ∈ S, α c' = 0) ∧ ∀ h : EuclideanSpace ℝ (DGFFSite n),
      hfun n S h c = ∑ c', α c' * h c' := by
  classical
  set M := (boxSplitPrecision n (boxInnerOuterEquiv n S)).toBlocks₁₁⁻¹ *
      (boxSplitPrecision n (boxInnerOuterEquiv n S)).toBlocks₁₂
  refine ⟨fun c' => if hc' : c' ∉ S then -M ⟨c, hc⟩ ⟨c', hc'⟩ else 0, ?_, fun h => ?_⟩
  · intro c' hc'
    simp [hc']
  rw [hfun_of_mem hc]
  unfold boxHarmonicField
  rw [boxResidualField_apply_left]
  simp only [boxSplitField_apply_right]
  have hsym : ∀ o : {o : DGFFSite n // o ∉ S}, (boxInnerOuterEquiv n S).symm (Sum.inr o) = o.1 :=
    fun o => rfl
  simp only [hsym]
  have hsub : ∑ o : {o : DGFFSite n // o ∉ S}, M ⟨c, hc⟩ o * h o.1 =
      ∑ c' ∈ Finset.univ.filter (fun c' : DGFFSite n => c' ∉ S),
        (if hc' : c' ∉ S then M ⟨c, hc⟩ ⟨c', hc'⟩ else 0) * h c' := by
    rw [Finset.sum_subtype (p := fun c' : DGFFSite n => c' ∉ S)
      (Finset.univ.filter (fun c' : DGFFSite n => c' ∉ S)) (fun x => by simp)
      (fun c' => (if hc' : c' ∉ S then M ⟨c, hc⟩ ⟨c', hc'⟩ else 0) * h c')]
    apply Finset.sum_congr rfl
    intro o _
    rw [dif_pos o.2]
  rw [hsub, Finset.sum_filter]
  rw [show ∑ c' : DGFFSite n, (if hc' : c' ∉ S then -M ⟨c, hc⟩ ⟨c', hc'⟩ else 0) * h c' =
      -∑ c' : DGFFSite n, (if c' ∉ S then (if hc' : c' ∉ S then M ⟨c, hc⟩ ⟨c', hc'⟩ else 0) *
        h c' else 0) by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro c' _
    by_cases hc' : c' ∉ S
    · rw [dif_pos hc', if_pos hc', dif_pos hc']; ring
    · rw [dif_neg hc', if_neg hc']; ring]
  ring

theorem eval_memLp (n : ℕ) (c : DGFFSite n) :
    MemLp (fun h : EuclideanSpace ℝ (DGFFSite n) => h c) 2 (boxDGFF n) :=
  boxDGFF_eval_memLp_two n c

theorem resid_memLp (n : ℕ) (S : Finset (DGFFSite n)) (c : DGFFSite n) :
    MemLp (fun h : EuclideanSpace ℝ (DGFFSite n) => resid n S h c) 2 (boxDGFF n) := by
  unfold resid
  split_ifs with hc
  · have hR := ((boxResidualField_hasGaussianLaw n (boxInnerOuterEquiv n S)).fst.map_fun
      (EuclideanSpace.proj ⟨c, hc⟩)).memLp_two
    exact hR
  · exact memLp_const 0

theorem hfun_memLp (n : ℕ) (S : Finset (DGFFSite n)) (c : DGFFSite n) :
    MemLp (fun h : EuclideanSpace ℝ (DGFFSite n) => hfun n S h c) 2 (boxDGFF n) := by
  have h1 := eval_memLp n c
  have h2 := resid_memLp n S c
  have : (fun h : EuclideanSpace ℝ (DGFFSite n) => hfun n S h c) =
      fun h => h c - resid n S h c := by
    funext h; have := hfun_add_resid n S h c; linarith
  rw [this]
  exact h1.sub h2

theorem lin_memLp (n : ℕ) (α : DGFFSite n → ℝ) :
    MemLp (fun h : EuclideanSpace ℝ (DGFFSite n) => ∑ c', α c' * h c') 2 (boxDGFF n) := by
  have : (fun h : EuclideanSpace ℝ (DGFFSite n) => ∑ c', α c' * h c') =
      ∑ c', fun h : EuclideanSpace ℝ (DGFFSite n) => α c' * h c' := by
    funext h; simp
  rw [this]
  exact memLp_finsetSum' _ fun c' _ => (eval_memLp n c').const_mul (α c')

 

theorem resid_cov_ext_zero (n : ℕ) (S : Finset (DGFFSite n)) {c : DGFFSite n} (hc : c ∈ S)
    (α : DGFFSite n → ℝ) (hα : ∀ c' ∈ S, α c' = 0) :
    cov[fun h : EuclideanSpace ℝ (DGFFSite n) => resid n S h c,
      fun h => ∑ c', α c' * h c'; boxDGFF n] = 0 := by
  rw [covariance_fun_sum_right (fun c' => (eval_memLp n c').const_mul (α c'))
    (resid_memLp n S c)]
  apply Finset.sum_eq_zero
  intro c' _
  rw [covariance_const_mul_right]
  by_cases hc' : c' ∈ S
  · rw [hα c' hc', zero_mul]
  · have h0 := boxResidualField_cross_covariance n (boxInnerOuterEquiv n S) ⟨c, hc⟩ ⟨c', hc'⟩
    have e1 : (fun h : EuclideanSpace ℝ (DGFFSite n) => resid n S h c) =
        fun h => (boxResidualField n (boxInnerOuterEquiv n S) h).1 ⟨c, hc⟩ := by
      funext h; unfold resid; rw [dif_pos hc]
    have e2 : (fun h : EuclideanSpace ℝ (DGFFSite n) => h c') =
        fun h => (boxResidualField n (boxInnerOuterEquiv n S) h).2 ⟨c', hc'⟩ := by
      funext h; rw [boxResidualField_apply_right, boxSplitField_apply_right]; rfl
    rw [e1, e2, h0, mul_zero]

 

theorem hfun_cross_cov (n : ℕ) {S S' : Finset (DGFFSite n)} (hS : S' ⊆ S)
    {x w : DGFFSite n} (hx : x ∈ S) (hw : w ∈ S') :
    cov[fun h : EuclideanSpace ℝ (DGFFSite n) => hfun n S h x,
      fun h => hfun n S' h w; boxDGFF n] =
    cov[fun h : EuclideanSpace ℝ (DGFFSite n) => hfun n S h x,
      fun h => hfun n S h w; boxDGFF n] := by
  obtain ⟨α, hα0, hα⟩ := hfun_eq_sum n S hx
  have hX : (fun h : EuclideanSpace ℝ (DGFFSite n) => hfun n S h x) =
      fun h => ∑ c', α c' * h c' := funext hα
  have hres : ∀ (T : Finset (DGFFSite n)) (y : DGFFSite n),
      (fun h : EuclideanSpace ℝ (DGFFSite n) => hfun n T h y) =
        fun h => h y - resid n T h y := by
    intro T y; funext h; have := hfun_add_resid n T h y; linarith
  rw [hres S' w, hres S w, hX]
  rw [covariance_fun_sub_right (lin_memLp n α) (eval_memLp n w) (resid_memLp n S' w),
    covariance_fun_sub_right (lin_memLp n α) (eval_memLp n w) (resid_memLp n S w)]
  rw [covariance_comm (fun h => ∑ c', α c' * h c') (fun h => resid n S' h w),
    covariance_comm (fun h => ∑ c', α c' * h c') (fun h => resid n S h w)]
  rw [resid_cov_ext_zero n S' hw α (fun c' hc' => hα0 c' (hS hc')),
    resid_cov_ext_zero n S (hS hw) α hα0]

 
theorem covariance_le_sqrt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    cov[X, Y; μ] ≤ Real.sqrt (Var[X; μ]) * Real.sqrt (Var[Y; μ]) := by
  set a := Var[X; μ]
  set b := Var[Y; μ]
  set c := cov[X, Y; μ]
  have hq : ∀ t : ℝ, 0 ≤ a - 2 * t * c + t ^ 2 * b := by
    intro t
    have h := variance_nonneg (fun ω => X ω - t * Y ω) μ
    rw [variance_fun_sub hX (hY.const_mul t), covariance_const_mul_right,
      variance_const_mul] at h
    linarith
  have ha : 0 ≤ a := variance_nonneg X μ
  have hb : 0 ≤ b := variance_nonneg Y μ
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · 
    have hc : c ≤ 0 := by
      by_contra hcpos
      push_neg at hcpos
      have := hq ((a + 1) / (2 * c))
      rw [← hb0] at this
      have : 2 * ((a + 1) / (2 * c)) * c = a + 1 := by field_simp
      nlinarith
    rw [← hb0, Real.sqrt_zero, mul_zero]
    exact hc
  · have h1 := hq (c / b)
    have h2 : c ^ 2 ≤ a * b := by
      have : a - 2 * (c / b) * c + (c / b) ^ 2 * b = a - c ^ 2 / b := by field_simp; ring
      rw [this] at h1
      have := (div_le_iff₀ hbpos).mp (by linarith : c ^ 2 / b ≤ a)
      linarith
    calc c ≤ |c| := le_abs_self c
      _ = Real.sqrt (c ^ 2) := (Real.sqrt_sq_eq_abs c).symm
      _ ≤ Real.sqrt (a * b) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt a * Real.sqrt b := Real.sqrt_mul ha b

end SupercriticalLQGUniqueness.B2.QPos.P4
