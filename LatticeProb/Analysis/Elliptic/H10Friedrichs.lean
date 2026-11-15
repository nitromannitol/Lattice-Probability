import LatticeProb.Analysis.Elliptic.WeakDirichlet
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Bounds on the zero-boundary Sobolev graph

The slab form of the Friedrichs inequality (Gilbarg–Trudinger, (7.44)) extends
to the closure defining `H10`.
-/

namespace LatticeProb.Elliptic.WeakDirichlet

open MeasureTheory

/-- Cauchy–Schwarz on an interval, adapted from
`QuantumZipper.K3.mixedPoincare_cs`. -/
theorem interval_integral_sq_le {f : ℝ → ℝ} (hf : Continuous f) {T : ℝ} (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, f t) ^ 2 ≤ T * ∫ t in (0 : ℝ)..T, f t ^ 2 := by
  set m := ∫ t in (0 : ℝ)..T, f t
  set S := ∫ t in (0 : ℝ)..T, f t ^ 2
  have e : ∀ t, (T * f t - m) ^ 2 = T ^ 2 * f t ^ 2 - (2 * T * m) * f t + m ^ 2 := by
    intro t
    ring
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..T, (T * f t - m) ^ 2 :=
    intervalIntegral.integral_nonneg hT.le (fun t _ => sq_nonneg _)
  have hi1 : IntervalIntegrable (fun t => f t ^ 2) volume 0 T :=
    (hf.pow 2).intervalIntegrable _ _
  have hi2 : IntervalIntegrable f volume 0 T := hf.intervalIntegrable _ _
  simp_rw [e] at h0
  rw [intervalIntegral.integral_add ((hi1.const_mul _).sub (hi2.const_mul _))
      intervalIntegrable_const, intervalIntegral.integral_sub (hi1.const_mul _)
      (hi2.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at h0
  simp only [sub_zero, smul_eq_mul] at h0
  have : 0 ≤ T * (T * S - m ^ 2) := by nlinarith
  nlinarith [(mul_nonneg_iff_of_pos_left hT).1 this]

/-- A function vanishing at the left endpoint is bounded by its derivative. -/
theorem sq_le_interval_integral_deriv_sq {f f' : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf0 : f 0 = 0) (hf' : Continuous f') (hderiv : ∀ t, HasDerivAt f (f' t) t) :
    f T ^ 2 ≤ T * ∫ t in (0 : ℝ)..T, f' t ^ 2 := by
  have hftc : (∫ t in (0 : ℝ)..T, f' t) = f T := by
    simpa [hf0] using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
        (hf'.intervalIntegrable 0 T))
  simpa [hftc] using interval_integral_sq_le hf' hT

/-- The one-dimensional slab estimate on an interval. -/
theorem integral_sq_le_interval_deriv_sq {f f' : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf' : Continuous f') (hderiv : ∀ t, HasDerivAt f (f' t) t)
    (hs : Function.support f ⊆ Set.Ioc 0 T) :
    (∫ t, f t ^ 2) ≤ T ^ 2 * ∫ t in (0 : ℝ)..T, f' t ^ 2 := by
  have hf0 : f 0 = 0 := by
    by_contra h
    have hmem := hs h
    exact (lt_irrefl (0 : ℝ)) hmem.1
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun t => (hderiv t).continuousAt
  have hp : ∀ t ∈ Set.Icc (0 : ℝ) T,
      f t ^ 2 ≤ T * ∫ s in (0 : ℝ)..T, f' s ^ 2 := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      rw [hf0, zero_pow (by decide)]
      exact mul_nonneg hT.le (intervalIntegral.integral_nonneg hT.le (fun s _ => sq_nonneg _))
    · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have h1 := sq_le_interval_integral_deriv_sq htp hf0 hf' hderiv
      have h2 : (∫ s in (0 : ℝ)..t, f' s ^ 2) ≤ ∫ s in (0 : ℝ)..T, f' s ^ 2 :=
        intervalIntegral.integral_mono_interval le_rfl htp.le ht.2
          (Filter.Eventually.of_forall fun _ => sq_nonneg _) (hf'.pow 2 |>.intervalIntegrable 0 T)
      have h3 : 0 ≤ ∫ s in (0 : ℝ)..T, f' s ^ 2 :=
        intervalIntegral.integral_nonneg hT.le fun s _ => sq_nonneg _
      exact h1.trans ((mul_le_mul_of_nonneg_left h2 htp.le).trans
        (mul_le_mul_of_nonneg_right ht.2 h3))
  have hs2 : Function.support (fun t => f t ^ 2) ⊆ Set.Ioc 0 T := by
    intro t ht
    apply hs
    intro hzero
    apply ht
    simp [hzero]
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hs2]
  calc
    (∫ t in (0 : ℝ)..T, f t ^ 2) ≤
        ∫ _t in (0 : ℝ)..T, T * ∫ s in (0 : ℝ)..T, f' s ^ 2 :=
      intervalIntegral.integral_mono_on hT.le (hf.pow 2 |>.intervalIntegrable 0 T)
        intervalIntegrable_const hp
    _ = T ^ 2 * ∫ s in (0 : ℝ)..T, f' s ^ 2 := by
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      ring

/-- A one-dimensional slab estimate centered at the origin. -/
theorem integral_sq_le_of_slab_1d {f f' : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hf' : Continuous f') (hderiv : ∀ t, HasDerivAt f (f' t) t)
    (hs : ∀ t, f t ≠ 0 → |t| < R) (hi : Integrable (fun t => f' t ^ 2)) :
    (∫ t, f t ^ 2) ≤ (2 * R) ^ 2 * ∫ t, f' t ^ 2 := by
  let g : ℝ → ℝ := fun t => f (t - R)
  let g' : ℝ → ℝ := fun t => f' (t - R)
  have hg' : Continuous g' := hf'.comp (continuous_id.sub continuous_const)
  have hgderiv : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    simpa [g, g', Function.comp_def] using (hderiv (t - R)).comp t ((hasDerivAt_id t).sub_const R)
  have hgs : Function.support g ⊆ Set.Ioc 0 (2 * R) := by
    intro t ht
    have h := abs_lt.mp (hs (t - R) ht)
    constructor <;> linarith
  have hfs : Function.support (fun t => f t ^ 2) ⊆ Set.Ioc (-R) R := by
    intro t ht
    have hn : f t ≠ 0 := by
      intro hz
      apply ht
      simp [hz]
    exact ⟨(abs_lt.mp (hs t hn)).1, (abs_lt.mp (hs t hn)).2.le⟩
  have hgs2 : Function.support (fun t => g t ^ 2) ⊆ Set.Ioc 0 (2 * R) := by
    intro t ht
    apply hgs
    intro hz
    apply ht
    simp [hz]
  have h := integral_sq_le_interval_deriv_sq (show 0 < 2 * R by linarith) hg' hgderiv hgs
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hgs2] at h
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hfs]
  have heq : (∫ t in (0 : ℝ)..(2 * R), g t ^ 2) = ∫ t in (-R)..R, f t ^ 2 := by
    change (∫ t in (0 : ℝ)..(2 * R), (fun t => f t ^ 2) (t - R)) = _
    simpa only [zero_sub, show 2 * R - R = R by ring] using
      (intervalIntegral.integral_comp_sub_right (fun t : ℝ => f t ^ 2) R
        (a := 0) (b := 2 * R))
  rw [heq] at h
  have hle : (∫ t in (0 : ℝ)..(2 * R), g' t ^ 2) ≤ ∫ t, f' t ^ 2 := by
    change (∫ t in (0 : ℝ)..(2 * R), (fun t => f' t ^ 2) (t - R)) ≤ _
    have heq' : (∫ t in (0 : ℝ)..(2 * R), f' (t - R) ^ 2) =
        ∫ t in (-R)..R, f' t ^ 2 := by
      simpa only [zero_sub, show 2 * R - R = R by ring] using
        (intervalIntegral.integral_comp_sub_right (fun t : ℝ => f' t ^ 2) R
          (a := 0) (b := 2 * R))
    rw [heq']
    have hRle : -R ≤ R := by linarith
    rw [intervalIntegral.integral_of_le hRle]
    exact setIntegral_le_integral hi (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  exact h.trans (mul_le_mul_of_nonneg_left hle (sq_nonneg _))


/-- Integrating first in a selected coordinate of a finite product. -/
theorem integral_pi_fin_succAbove {n : ℕ} (i : Fin (n + 1))
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Integrable f) :
    (∫ x, f x) = ∫ y : Fin n → ℝ, ∫ t : ℝ, f (i.insertNth t y) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hm : MeasurePreserving e.symm (volume : Measure (ℝ × (Fin n → ℝ))) volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  have hi : Integrable (fun z : ℝ × (Fin n → ℝ) => f (e.symm z)) :=
    (hm.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  calc
    (∫ x, f x) = ∫ z : ℝ × (Fin n → ℝ), f (e.symm z) := (hm.integral_comp' f).symm
    _ = ∫ y : Fin n → ℝ, ∫ t : ℝ, f (i.insertNth t y) := by
      rw [Measure.volume_eq_prod]
      simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
        using (integral_prod_symm (μ := volume) (ν := volume)
          (fun z : ℝ × (Fin n → ℝ) => f (e.symm z)) hi)
/-- Integration in one coordinate preserves integrability in the remaining coordinates. -/
theorem integrable_integral_pi_fin_succAbove {n : ℕ} (i : Fin (n + 1))
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Integrable f) :
    Integrable (fun y : Fin n → ℝ => ∫ t : ℝ, f (i.insertNth t y)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hm : MeasurePreserving e.symm (volume : Measure (ℝ × (Fin n → ℝ))) volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  have hi : Integrable (fun z : ℝ × (Fin n → ℝ) => f (e.symm z)) :=
    (hm.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  have hi' : Integrable (fun z : ℝ × (Fin n → ℝ) => f (e.symm z))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
    rw [← Measure.volume_eq_prod]
    exact hi
  simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using hi'.integral_prod_right

/-- The line-wise slab estimate for smooth compactly supported functions. -/
theorem integral_sq_le_of_slab_line {n : ℕ} (i : Fin (n + 1)) {R : ℝ} (hR : 0 < R)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (hs : ∀ x, f x ≠ 0 → |x i| < R)
    (y : Fin n → ℝ) :
    (∫ t, f (i.insertNth t y) ^ 2) ≤
      (2 * R) ^ 2 * ∫ t, partialDeriv i f (i.insertNth t y) ^ 2 := by
  let x : Fin (n + 1) → ℝ := i.insertNth (0 : ℝ) y
  let line := Function.update x i
  have hline : ∀ t : ℝ, line t = i.insertNth t y := fun t => Fin.update_insertNth (α := fun _ => ℝ) i 0 t y
  have hpc : Continuous (partialDeriv i f) :=
    ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const).continuous
  have hcp : HasCompactSupport (partialDeriv i f) := hc.fderiv_apply ℝ (Pi.single i 1)
  have hcont : Continuous ((partialDeriv i f) ∘ line) :=
    hpc.comp (contDiff_update (𝕜 := ℝ) (⊤ : ℕ∞) x i).continuous
  have hderiv : ∀ t, HasDerivAt (f ∘ line) (((partialDeriv i f) ∘ line) t) t := by
    intro t
    have h := (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_update x i t)
    simpa [partialDeriv, line, Function.comp_def] using h
  have hcomp : HasCompactSupport ((partialDeriv i f) ∘ line) :=
    hcp.comp_isClosedEmbedding (isClosedEmbedding_update x i)
  have hint : Integrable (fun t => (((partialDeriv i f) ∘ line) t) ^ 2) :=
    (hcont.pow 2).integrable_of_hasCompactSupport hcomp.mul_left
  have hslab : ∀ t, (f ∘ line) t ≠ 0 → |t| < R := by
    intro t ht
    have h := hs (line t) ht
    simpa [hline t, Fin.insertNth_apply_same] using h
  have h := integral_sq_le_of_slab_1d hR hcont hderiv hslab hint
  simpa only [Function.comp_def, hline] using h

/-- The slab form of the Friedrichs inequality for a smooth function. -/
theorem integral_sq_le_of_slab {d : ℕ} (i : Fin d) {R : ℝ} (hR : 0 < R)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (hs : ∀ x, f x ≠ 0 → |x i| < R) :
    ∫ x, f x ^ 2 ≤ (2 * R) ^ 2 * ∫ x, partialDeriv i f x ^ 2 := by
  cases d with
  | zero => exact i.elim0
  | succ n =>
    have hfint : Integrable (fun x => f x ^ 2) :=
      (hf.continuous.pow 2).integrable_of_hasCompactSupport hc.mul_left
    have hpcont : Continuous (partialDeriv i f) :=
      ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const).continuous
    have hpcomp : HasCompactSupport (partialDeriv i f) := hc.fderiv_apply ℝ (Pi.single i 1)
    have hpint : Integrable (fun x => partialDeriv i f x ^ 2) :=
      (hpcont.pow 2).integrable_of_hasCompactSupport hpcomp.mul_left
    rw [integral_pi_fin_succAbove i hfint, integral_pi_fin_succAbove i hpint,
      ← integral_const_mul]
    exact integral_mono (integrable_integral_pi_fin_succAbove i hfint)
      ((integrable_integral_pi_fin_succAbove i hpint).const_mul _) fun y =>
        integral_sq_le_of_slab_line i hR hf hc hs y


/-- The squared norm of a test function is its full-space squared integral. -/
theorem TestFunction.norm_toL2_sq {d : ℕ} {U : Set (Fin d → ℝ)} (φ : TestFunction U) :
    ‖φ.toL2‖ ^ 2 = ∫ x, φ.val x ^ 2 := by
  rw [l2_norm_sq]
  calc
    (∫ x in U, (φ.toL2 x) ^ 2) = ∫ x in U, φ.val x ^ 2 := by
      apply integral_congr_ae
      filter_upwards [φ.memLp.coeFn_toLp] with x hx
      change φ.toL2 x = φ.val x at hx
      rw [hx]
    _ = ∫ x, φ.val x ^ 2 := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (φ.supported h)), zero_pow (by decide)]

/-- A squared integral estimate implies the corresponding norm estimate. -/
theorem TestFunction.norm_toL2_le_of_integral_sq_le {d : ℕ} {U : Set (Fin d → ℝ)}
    (φ : TestFunction U) (i : Fin d) {C : ℝ} (hC : 0 ≤ C)
    (h : (∫ x, φ.val x ^ 2) ≤ C ^ 2 * ∫ x, (φ.deriv i).val x ^ 2) :
    ‖φ.toL2‖ ≤ C * ‖(φ.deriv i).toL2‖ := by
  rw [← φ.norm_toL2_sq, ← (φ.deriv i).norm_toL2_sq] at h
  have hn : 0 ≤ C * ‖(φ.deriv i).toL2‖ := mul_nonneg hC (norm_nonneg _)
  nlinarith [sq_nonneg (‖φ.toL2‖ + C * ‖(φ.deriv i).toL2‖)]

/-- A coordinate norm inequality on test graphs extends to the zero-boundary closure. -/
theorem H10.norm_coord_le {d : ℕ} {U : Set (Fin d → ℝ)} (u : H10 U)
    (i : Fin d) (C : ℝ)
    (h : ∀ φ : TestFunction U, ‖φ.toL2‖ ≤ C * ‖(φ.deriv i).toL2‖) :
    ‖u.val 0‖ ≤ C * ‖u.val i.succ‖ := by
  have hc : IsClosed {v : H1Product U | ‖v 0‖ ≤ C * ‖v i.succ‖} :=
    isClosed_le (PiLp.continuous_apply 2 _ 0).norm
      (continuous_const.mul (PiLp.continuous_apply 2 _ i.succ).norm)
  have hs : Set.range (TestFunction.graph (U := U)) ⊆
      {v : H1Product U | ‖v 0‖ ≤ C * ‖v i.succ‖} := by
    rintro _ ⟨φ, rfl⟩
    exact h φ
  exact closure_minimal hs hc u.property

/-- A test-function norm bound makes the zeroth coordinate vanish when the selected
    derivative coordinate vanishes. -/
theorem H10.coord_zero_eq_zero_of_coord_bound {d : ℕ} {U : Set (Fin d → ℝ)} (u : H10 U)
    (i : Fin d) (C : ℝ)
    (h : ∀ φ : TestFunction U, ‖φ.toL2‖ ≤ C * ‖(φ.deriv i).toL2‖)
    (hgrad : u.val i.succ = 0) : u.val 0 = 0 := by
  apply norm_eq_zero.mp
  have hu := u.norm_coord_le i C h
  simp only [hgrad, norm_zero, mul_zero] at hu
  exact le_antisymm hu (norm_nonneg _)

/-- A test function supported in a slab satisfies the Friedrichs bound. -/
theorem TestFunction.norm_toL2_le_slab {d : ℕ} {U : Set (Fin d → ℝ)}
    (φ : TestFunction U) (i : Fin d) {R : ℝ} (hR : 0 < R)
    (hU : U ⊆ {x | |x i| < R}) : ‖φ.toL2‖ ≤ 2 * R * ‖(φ.deriv i).toL2‖ := by
  apply φ.norm_toL2_le_of_integral_sq_le i (by positivity)
  apply integral_sq_le_of_slab i hR φ.smooth φ.compact
  intro x hx
  exact hU (φ.supported (subset_tsupport φ.val hx))

/-- A zero-boundary Sobolev function with zero gradient vanishes in dimension at least one. -/
theorem H10.coord_zero_eq_zero_of_grad_eq_zero {d : ℕ} (hd : 0 < d)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    (u : H10 U) (hgrad : ∀ i : Fin d, u.val i.succ = 0) : u.val 0 = 0 := by
  obtain ⟨R, hR, hbound⟩ := hU.exists_pos_norm_lt
  let i : Fin d := ⟨0, hd⟩
  have hslab : U ⊆ {x | |x i| < R} := by
    intro x hx
    exact (show |x i| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i).trans_lt
      (hbound x hx)
  exact u.coord_zero_eq_zero_of_coord_bound i (2 * R)
    (fun φ => φ.norm_toL2_le_slab i hR hslab) (hgrad i)

end LatticeProb.Elliptic.WeakDirichlet
