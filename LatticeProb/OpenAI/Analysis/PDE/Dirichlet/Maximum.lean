/- Adapted from OpenAI's math repository (https://github.com/openai/math), commit 4eaee875,
   file lean/OAI/Analysis/PDE/Dirichlet/Maximum.lean, Apache License 2.0;
   changes: the module path is LatticeProb.OpenAI.Analysis.PDE.Dirichlet.Maximum in place of OAI.Analysis.PDE.Dirichlet.Maximum; statements and proofs are unchanged. -/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

open Filter Set
open scoped Topology

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

/-- The second derivative test in the form used by the elliptic comparison principle. -/
theorem second_deriv_nonpos_of_localMax {f : ℝ → ℝ} {a : ℝ}
    (hf : ContDiff ℝ 2 f) (hmax : IsLocalMax f a) :
    deriv (deriv f) a ≤ 0 := by
  have htaylor (x : ℝ) : taylorWithinEval f 2 univ a x =
      f a + (x - a) ^ 2 / 2 * deriv (deriv f) a := by
    simp [taylorWithinEval_succ, iteratedDerivWithin_univ, iteratedDeriv_succ,
      hmax.deriv_eq_zero]
    ring_nf
    simp
  have hlim := (taylor_isLittleO_univ (x₀ := a) hf).tendsto_div_nhds_zero
  have hlim' : Tendsto (fun x ↦ (f x - f a) / (x - a) ^ 2)
      (𝓝[≠] a) (𝓝 (deriv (deriv f) a / 2)) := by
    have hadd := (hlim.mono_left (show 𝓝[≠] a ≤ 𝓝 a from nhdsWithin_le_nhds)).add_const
      (deriv (deriv f) a / 2)
    simp only [zero_add] at hadd
    apply hadd.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hne : x - a ≠ 0 := sub_ne_zero.mpr hx
    rw [htaylor]
    field_simp
    ring
  have hle : ∀ᶠ x in 𝓝[≠] a, (f x - f a) / (x - a) ^ 2 ≤ 0 := by
    filter_upwards [hmax.filter_mono nhdsWithin_le_nhds] with x hx
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sq_nonneg _)
  have h := le_of_tendsto hlim' hle
  linarith

/-- At a local maximum the genuine Fréchet Hessian is negative semidefinite. -/
theorem hessian_nonpos_of_localMax
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiff ℝ 2 f) (hmax : IsLocalMax f x) (v : E) :
    (fderiv ℝ (fderiv ℝ f) x v) v ≤ 0 := by
  let g : ℝ → ℝ := fun t ↦ f (x + t • v)
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ ↦ x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hg (t : ℝ) : HasDerivAt g (fderiv ℝ f (x + t • v) v) t :=
    ((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp_hasDerivAt t (hline t)
  have hgd : deriv g = fun t ↦ fderiv ℝ f (x + t • v) v :=
    funext fun t ↦ (hg t).deriv
  have hf' : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hsecond : HasDerivAt (fun t : ℝ ↦ fderiv ℝ f (x + t • v) v)
      ((fderiv ℝ (fderiv ℝ f) x v) v) 0 := by
    have hh := hf'.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 (hline 0)
    simpa [Function.comp_def] using HasDerivAt.clm_apply hh (hasDerivAt_const 0 v)
  have hgcont : ContDiff ℝ 2 g := hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hlinecont : Continuous (fun t : ℝ ↦ x + t • v) := by fun_prop
  have hlinet : Tendsto (fun t : ℝ ↦ x + t • v) (𝓝 0) (𝓝 x) := by
    simpa using hlinecont.tendsto 0
  have hmaxg : IsLocalMax g 0 := by
    change ∀ᶠ t in 𝓝 0, g t ≤ g 0
    simpa [g] using hlinet.eventually hmax
  have h := second_deriv_nonpos_of_localMax hgcont hmaxg
  rw [hgd, hsecond.deriv] at h
  exact h

/-- A nonnegative weighted sum of second directional derivatives. -/
def ellipticValue {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (a : E → ι → ℝ) (v : E → ι → E) (f : E → ℝ) (x : E) : ℝ :=
  ∑ i, a x i * ((fderiv ℝ (fderiv ℝ f) x (v x i)) (v x i))

theorem ellipticValue_nonpos_of_localMax
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] {a : E → ι → ℝ} {v : E → ι → E}
    {f : E → ℝ} {x : E} (ha : ∀ i, 0 ≤ a x i)
    (hf : ContDiff ℝ 2 f) (hmax : IsLocalMax f x) :
    ellipticValue a v f x ≤ 0 := by
  exact Finset.sum_nonpos fun i _ ↦ mul_nonpos_of_nonneg_of_nonpos (ha i)
    (hessian_nonpos_of_localMax hf hmax (v x i))

/-- Strict maximum principle on an arbitrary compact domain. -/
theorem strict_maximum_principle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] {a : E → ι → ℝ} {v : E → ι → E}
    {f : E → ℝ} {K : Set E} {M : ℝ}
    (hK : IsCompact K) (hf : ContDiff ℝ 2 f)
    (ha : ∀ x ∈ interior K, ∀ i, 0 ≤ a x i)
    (hL : ∀ x ∈ interior K, 0 < ellipticValue a v f x)
    (hbd : ∀ x ∈ K, x ∉ interior K → f x ≤ M) :
    ∀ x ∈ K, f x ≤ M := by
  intro x hx
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hf.continuous.continuousOn
  by_cases hyi : y ∈ interior K
  · have hlocal := hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hyi)
    have hnonpos := ellipticValue_nonpos_of_localMax (v := v) (ha y hyi) hf hlocal
    exact False.elim (not_lt_of_ge hnonpos (hL y hyi))
  · exact (hmax hx).trans (hbd y hy hyi)

theorem ellipticValue_add_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (a : E → ι → ℝ) (v : E → ι → E)
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (c : ℝ) (x : E) :
    ellipticValue a v (fun y ↦ f y + c • g y) x =
      ellipticValue a v f x + c * ellipticValue a v g x := by
  have hf₁ := hf.differentiable (by norm_num)
  have hg₁ := hg.differentiable (by norm_num)
  have hf₂ := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hg₂ := (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hD : fderiv ℝ (fun y ↦ f y + c • g y) =
      fun y ↦ fderiv ℝ f y + c • fderiv ℝ g y := by
    funext y
    exact ((hf₁ y).hasFDerivAt.add ((hg₁ y).hasFDerivAt.const_smul c)).fderiv
  have hD₂ : fderiv ℝ (fun y ↦ fderiv ℝ f y + c • fderiv ℝ g y) x =
      fderiv ℝ (fderiv ℝ f) x + c • fderiv ℝ (fderiv ℝ g) x :=
    ((hf₂ x).hasFDerivAt.add ((hg₂ x).hasFDerivAt.const_smul c)).fderiv
  unfold ellipticValue
  rw [hD, hD₂]
  simp only [add_apply, smul_apply,
    smul_eq_mul, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Weak maximum principle when a strict smooth barrier exists. The usual
positive-definite elliptic case uses the squared Euclidean norm as barrier. -/
theorem maximum_principle_of_barrier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] {a : E → ι → ℝ} {v : E → ι → E}
    {f b : E → ℝ} {K : Set E} {M : ℝ}
    (hK : IsCompact K) (hf : ContDiff ℝ 2 f) (hb : ContDiff ℝ 2 b)
    (ha : ∀ x ∈ interior K, ∀ i, 0 ≤ a x i)
    (hL : ∀ x ∈ interior K, 0 ≤ ellipticValue a v f x)
    (hbL : ∀ x ∈ interior K, 0 < ellipticValue a v b x)
    (hbd : ∀ x ∈ K, x ∉ interior K → f x ≤ M) :
    ∀ x ∈ K, f x ≤ M := by
  intro x hx
  obtain ⟨z, hz, hbmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hb.continuous.continuousOn
  have hε (ε : ℝ) (hε : 0 < ε) : f x + ε * b x ≤ M + ε * b z := by
    refine strict_maximum_principle (v := v) hK (hf.add (hb.const_smul ε)) ha ?_ ?_ x hx
    · intro y hy
      rw [ellipticValue_add_smul a v hf hb]
      exact add_pos_of_nonneg_of_pos (hL y hy) (mul_pos hε (hbL y hy))
    · intro y hy hyi
      exact add_le_add (hbd y hy hyi) (mul_le_mul_of_nonneg_left (hbmax hy) hε.le)
  have ht : Tendsto (fun ε : ℝ ↦ f x + ε * b x - (M + ε * b z))
      (𝓝[>] 0) (𝓝 (f x - M)) := by
    have hc : Continuous (fun ε : ℝ ↦ f x + ε * b x - (M + ε * b z)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hle : ∀ᶠ ε : ℝ in 𝓝[>] 0, f x + ε * b x - (M + ε * b z) ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hpos
    exact sub_nonpos.mpr (hε ε hpos)
  have := le_of_tendsto ht hle
  linarith

theorem hessian_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x v : E) :
    (fderiv ℝ (fderiv ℝ (fun y : E ↦ ‖y‖ ^ 2)) x v) v = 2 * ‖v‖ ^ 2 := by
  rw [fderiv_norm_sq, fderiv_const_smul (innerSL ℝ).differentiableAt]
  simp only [ContinuousLinearMap.fderiv, smul_apply]
  change (2 : ℕ) • (inner ℝ v v) = 2 * ‖v‖ ^ 2
  rw [real_inner_self_eq_norm_sq]
  simp [two_smul, two_mul]

theorem ellipticValue_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (a : E → ι → ℝ) (v : E → ι → E) (x : E) :
    ellipticValue a v (fun y : E ↦ ‖y‖ ^ 2) x = 2 * ∑ i, a x i * ‖v x i‖ ^ 2 := by
  simp only [ellipticValue, hessian_norm_sq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The weak elliptic maximum principle. Nonnegative coefficients and positive
trace suffice; no regularity of the coefficients is needed for this statement. -/
theorem maximum_principle
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] {a : E → ι → ℝ} {v : E → ι → E}
    {f : E → ℝ} {K : Set E} {M : ℝ}
    (hK : IsCompact K) (hf : ContDiff ℝ 2 f)
    (ha : ∀ x ∈ interior K, ∀ i, 0 ≤ a x i)
    (htrace : ∀ x ∈ interior K, 0 < ∑ i, a x i * ‖v x i‖ ^ 2)
    (hL : ∀ x ∈ interior K, 0 ≤ ellipticValue a v f x)
    (hbd : ∀ x ∈ K, x ∉ interior K → f x ≤ M) :
    ∀ x ∈ K, f x ≤ M := by
  apply maximum_principle_of_barrier hK hf (contDiff_norm_sq ℝ) ha hL ?_ hbd
  intro x hx
  rw [ellipticValue_norm_sq]
  exact mul_pos (by norm_num) (htrace x hx)

/-- Comparison for the real linearized Dirichlet operator. -/
theorem dirichlet_comparison
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] {a : E → ι → ℝ} {v : E → ι → E}
    {f g : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (ha : ∀ x ∈ interior K, ∀ i, 0 ≤ a x i)
    (htrace : ∀ x ∈ interior K, 0 < ∑ i, a x i * ‖v x i‖ ^ 2)
    (hL : ∀ x ∈ interior K, ellipticValue a v g x ≤ ellipticValue a v f x)
    (hbd : ∀ x ∈ K, x ∉ interior K → f x ≤ g x) :
    ∀ x ∈ K, f x ≤ g x := by
  have hd : ∀ x ∈ K, (fun y ↦ f y + (-1 : ℝ) • g y) x ≤ 0 := by
    apply maximum_principle hK (hf.add (hg.const_smul (-1 : ℝ))) ha htrace ?_ ?_
    · intro x hx
      rw [ellipticValue_add_smul a v hf hg]
      linarith [hL x hx]
    · intro x hx hxi
      simpa only [neg_smul, one_smul, ← sub_eq_add_neg, sub_nonpos] using hbd x hx hxi
  intro x hx
  simpa only [neg_smul, one_smul, ← sub_eq_add_neg, sub_nonpos] using hd x hx

/-- Uniqueness for the linearized Dirichlet boundary-value problem. -/
theorem dirichlet_uniqueness
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] {a : E → ι → ℝ} {v : E → ι → E}
    {f g : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (ha : ∀ x ∈ interior K, ∀ i, 0 ≤ a x i)
    (htrace : ∀ x ∈ interior K, 0 < ∑ i, a x i * ‖v x i‖ ^ 2)
    (hL : ∀ x ∈ interior K, ellipticValue a v f x = ellipticValue a v g x)
    (hbd : ∀ x ∈ K, x ∉ interior K → f x = g x) :
    EqOn f g K := by
  have hfg := dirichlet_comparison hK hf hg ha htrace
    (fun x hx ↦ (hL x hx).ge) (fun x hx hxi ↦ (hbd x hx hxi).le)
  have hgf := dirichlet_comparison hK hg hf ha htrace
    (fun x hx ↦ (hL x hx).le) (fun x hx hxi ↦ (hbd x hx hxi).ge)
  exact fun x hx ↦ le_antisymm (hfg x hx) (hgf x hx)

end OAI.Analysis.PDE.Dirichlet
