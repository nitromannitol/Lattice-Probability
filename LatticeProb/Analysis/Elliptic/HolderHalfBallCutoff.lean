import LatticeProb.Analysis.Elliptic.HolderTrace
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Cutoffs on a half-ball

Smooth cutoffs localize functions on a half-ball while retaining control of their
coordinate Hölder norms.
-/

namespace LatticeProb.Elliptic.HolderExtension

open Set Filter LatticeProb.Euclidean.Lattice
open scoped ContDiff Classical Topology BigOperators ENNReal

noncomputable section

private theorem exists_ball_cutoff {d : ℕ} (p : E d) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    ∃ χ : E d → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x ∈ Metric.ball p r, χ x = 1) ∧
      tsupport χ ⊆ Metric.ball p R := by
  let χ : ContDiffBump p :=
    { rIn := r
      rOut := (r + R) / 2
      rIn_pos := hr
      rIn_lt_rOut := by linarith }
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport, ?_, ?_⟩
  · intro x hx
    exact χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
  · rw [χ.tsupport_eq]
    intro x hx
    exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by
      change (r + R) / 2 < R
      linarith))

private theorem contDiffOn_cutoff_paste {d : ℕ} {S U : Set (E d)}
    (hU : IsOpen U) {χ u : E d → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hsupp : tsupport χ ⊆ U) (hu : ContDiffOn ℝ 2 u (S ∩ U)) :
    ContDiffOn ℝ 2 (U.piecewise (fun x => χ x * u x) 0) S := by
  classical
  intro x hx
  by_cases hxU : x ∈ U
  · have heq : U.piecewise (fun x => χ x * u x) 0 =ᶠ[𝓝 x]
        fun x => χ x * u x := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      simp only [Set.piecewise, hy, ↓reduceIte]
    have hlocal : ContDiffWithinAt ℝ 2 (fun x => χ x * u x) (S ∩ U) x :=
      hχ.contDiffOn.mul hu x ⟨hx, hxU⟩
    have hlocal' : ContDiffWithinAt ℝ 2 (fun x => χ x * u x) S x :=
      (contDiffWithinAt_inter' (nhdsWithin_le_nhds (hU.mem_nhds hxU))).mp hlocal
    exact hlocal'.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) (heq.self_of_nhds)
  · have hnot : x ∉ tsupport χ := fun hx' => hxU (hsupp hx')
    have hneigh : (tsupport χ)ᶜ ∈ 𝓝 x := (isClosed_tsupport χ).isOpen_compl.mem_nhds hnot
    have heq : U.piecewise (fun x => χ x * u x) 0 =ᶠ[𝓝 x] 0 := by
      filter_upwards [hneigh] with y hy
      by_cases hyU : y ∈ U
      · simp only [Set.piecewise, hyU, ↓reduceIte, image_eq_zero_of_notMem_tsupport hy, zero_mul,
          Pi.zero_apply]
      · simp only [Set.piecewise, hyU, ↓reduceIte]
    exact contDiffAt_const.contDiffWithinAt.congr_of_eventuallyEq
      (heq.filter_mono nhdsWithin_le_nhds) heq.self_of_nhds

private theorem holder_increment_of_bounded_lipschitz {d : ℕ} {S : Set (E d)}
    {f : E d → ℝ} {M L σ : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hb : ∀ x ∈ S, |f x| ≤ M)
    (hl : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ L * radius (x - y)) :
    ∀ x ∈ S, ∀ y ∈ S,
      |f x - f y| ≤ (L + 2 * M) * radius (x - y) ^ σ := by
  intro x hx y hy
  have hr := Real.rpow_nonneg (radius_nonneg (x - y)) σ
  by_cases hd : radius (x - y) ≤ 1
  · have hp := Real.self_le_rpow_of_le_one (radius_nonneg (x - y)) hd hσ1
    calc
      |f x - f y| ≤ L * radius (x - y) := hl x hx y hy
      _ ≤ L * radius (x - y) ^ σ := mul_le_mul_of_nonneg_left hp hL
      _ ≤ (L + 2 * M) * radius (x - y) ^ σ := by
        exact mul_le_mul_of_nonneg_right (by linarith) hr
  · have hp : 1 ≤ radius (x - y) ^ σ := Real.one_le_rpow (le_of_not_ge hd) hσ
    have hb' : |f x - f y| ≤ 2 * M := by
      calc
        |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
        _ ≤ 2 * M := by linarith [hb x hx, hb y hy]
    calc
      |f x - f y| ≤ 2 * M := hb'
      _ ≤ (2 * M) * radius (x - y) ^ σ := le_mul_of_one_le_right (by positivity) hp
      _ ≤ (L + 2 * M) * radius (x - y) ^ σ :=
        mul_le_mul_of_nonneg_right (by linarith) hr

private theorem norm_le_radius {d : ℕ} (x : E d) : ‖x‖ ≤ radius x := by
  apply (pi_norm_le_iff_of_nonneg (radius_nonneg x)).2
  intro j
  simpa only [Real.norm_eq_abs] using abs_coord_le_radius x j

private theorem holder_increment_mul {d : ℕ} {S : Set (E d)} {f g : E d → ℝ}
    {A B H K σ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ x ∈ S, |f x| ≤ A) (hg : ∀ x ∈ S, |g x| ≤ B)
    (hfH : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ H * radius (x - y) ^ σ)
    (hgK : ∀ x ∈ S, ∀ y ∈ S, |g x - g y| ≤ K * radius (x - y) ^ σ) :
    ∀ x ∈ S, ∀ y ∈ S,
      |f x * g x - f y * g y| ≤ (A * K + B * H) * radius (x - y) ^ σ := by
  intro x hx y hy
  calc
    |f x * g x - f y * g y| =
        |f x * (g x - g y) + g y * (f x - f y)| := by congr 1; ring
    _ ≤ |f x| * |g x - g y| + |g y| * |f x - f y| := by
      simpa only [abs_mul] using
        abs_add_le (f x * (g x - g y)) (g y * (f x - f y))
    _ ≤ A * (K * radius (x - y) ^ σ) + B * (H * radius (x - y) ^ σ) := by
      exact add_le_add
        (mul_le_mul (hf x hx) (hgK x hx y hy) (abs_nonneg _) hA)
        (mul_le_mul (hg y hy) (hfH x hx y hy) (abs_nonneg _) hB)
    _ = (A * K + B * H) * radius (x - y) ^ σ := by ring

private theorem norm_linear_le_sum {d : ℕ} (L : E d →L[ℝ] ℝ) (x : E d) :
    ‖L x‖ ≤ (∑ j, ‖L (Pi.single j 1)‖) * ‖x‖ := by
  have hx : x = ∑ j : Fin d, (x j) • Pi.single j (1 : ℝ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  calc
    ‖L x‖ = ‖∑ j : Fin d, L ((x j) • Pi.single j (1 : ℝ))‖ := by
      congr 1
      exact (congrArg L hx).trans (map_sum L _ _)
    _ ≤ ∑ j : Fin d, ‖L ((x j) • Pi.single j (1 : ℝ))‖ := by
      let F : Fin d → ℝ := fun j => L ((x j) • Pi.single j 1)
      exact norm_sum_le Finset.univ F
    _ ≤ ∑ j : Fin d, ‖L (Pi.single j (1 : ℝ))‖ * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [map_smul, norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

private theorem lipschitz_of_bounded_partials {d : ℕ} {S : Set (E d)} {f : E d → ℝ}
    (hconv : Convex ℝ S) (hdf : ∀ x ∈ S, DifferentiableAt ℝ f x)
    (hb : ∀ j, supNorm S (partialDeriv j f) < ⊤) :
    ∀ x ∈ S, ∀ y ∈ S,
      |f x - f y| ≤ (∑ j, (supNorm S (partialDeriv j f)).toReal) * radius (x-y) := by
  let B : ℝ := ∑ j, (supNorm S (partialDeriv j f)).toReal
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hbound (x : E d) (hx : x ∈ S) : ‖fderiv ℝ f x‖ ≤ B := by
    apply ContinuousLinearMap.opNorm_le_bound _ hB
    intro v
    refine (norm_linear_le_sum (fderiv ℝ f x) v).trans ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Finset.sum_le_sum
    intro j _
    simpa only [partialDeriv, Real.norm_eq_abs] using abs_le_supNorm_toReal (hb j) hx
  have hlip : LipschitzOnWith ⟨B, hB⟩ f S := by
    apply hconv.lipschitzOnWith_of_nnnorm_fderiv_le hdf
    intro x hx
    exact hbound x hx
  intro x hx y hy
  have h := hlip.dist_le_mul x hx y hy
  change dist (f x) (f y) ≤ B * dist x y at h
  have h' : |f x - f y| ≤ B * ‖x - y‖ := by
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using h
  exact h'.trans (mul_le_mul_of_nonneg_left (norm_le_radius (x-y)) hB)

private theorem partialDeriv_mul_at {d : ℕ} {f g : E d → ℝ} {x : E d}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin d) :
    partialDeriv i (fun x => f x * g x) x =
      f x * partialDeriv i g x + g x * partialDeriv i f x := by
  rw [partialDeriv, fderiv_fun_mul hf hg]
  simp only [add_apply, smul_apply, smul_eq_mul,
    partialDeriv]

private theorem secondPartial_eq_partialDeriv_at {d : ℕ} {f : E d → ℝ}
    {x : E d} (hf : ContDiffAt ℝ 2 f x) (i j : Fin d) :
    secondPartial i j f x = partialDeriv i (partialDeriv j f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  simp only [secondPartial, partialDeriv, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  change ((fderiv ℝ (fderiv ℝ f) x) (Pi.single i 1)) (Pi.single j 1) =
    (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j 1)) x) (Pi.single i 1)
  rw [fderiv_clm_apply hd (differentiableAt_const (Pi.single j 1))]
  simp

private theorem secondPartial_mul_on {d : ℕ} {S : Set (E d)} {f g : E d → ℝ}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 2 f S) (hg : ContDiffOn ℝ 2 g S)
    (i j : Fin d) {x : E d} (hx : x ∈ S) :
    secondPartial i j (fun x => f x * g x) x =
      f x * secondPartial i j g x + partialDeriv i f x * partialDeriv j g x +
      partialDeriv j f x * partialDeriv i g x + secondPartial i j f x * g x := by
  have hf' : ContDiffOn ℝ 1 (partialDeriv j f) S :=
    (hf.fderiv_of_isOpen hS (by norm_num)).clm_apply contDiffOn_const
  have hg' : ContDiffOn ℝ 1 (partialDeriv j g) S :=
    (hg.fderiv_of_isOpen hS (by norm_num)).clm_apply contDiffOn_const
  have hfn := hf.contDiffAt (hS.mem_nhds hx)
  have hgn := hg.contDiffAt (hS.mem_nhds hx)
  have hdf := hfn.differentiableAt (by norm_num)
  have hdg := hgn.differentiableAt (by norm_num)
  have hdf' := (hf'.contDiffAt (hS.mem_nhds hx)).differentiableAt (by norm_num)
  have hdg' := (hg'.contDiffAt (hS.mem_nhds hx)).differentiableAt (by norm_num)
  have heq : partialDeriv j (fun x => f x * g x) =ᶠ[𝓝 x]
      fun x => f x * partialDeriv j g x + g x * partialDeriv j f x := by
    filter_upwards [hS.mem_nhds hx] with y hy
    exact partialDeriv_mul_at
      ((hf.contDiffAt (hS.mem_nhds hy)).differentiableAt (by norm_num))
      ((hg.contDiffAt (hS.mem_nhds hy)).differentiableAt (by norm_num)) j
  rw [secondPartial_eq_partialDeriv_at (hfn.mul hgn)]
  change (fderiv ℝ (partialDeriv j (fun x => f x * g x)) x) (Pi.single i 1) = _
  have hd := ((hdf.hasFDerivAt.mul hdg'.hasFDerivAt).add
    (hdg.hasFDerivAt.mul hdf'.hasFDerivAt)).fderiv
  change fderiv ℝ (fun y => f y * partialDeriv j g y + g y * partialDeriv j f y) x = _ at hd
  rw [heq.fderiv_eq, hd]
  simp only [add_apply, smul_apply, smul_eq_mul]
  change f x * partialDeriv i (partialDeriv j g) x +
    partialDeriv j g x * partialDeriv i f x +
    (g x * partialDeriv i (partialDeriv j f) x +
      partialDeriv j f x * partialDeriv i g x) = _
  rw [← secondPartial_eq_partialDeriv_at hfn i j,
    ← secondPartial_eq_partialDeriv_at hgn i j]
  ring

private theorem radius_separated {d : ℕ} {p x y : E d} {a R : ℝ}
    (hx : x ∈ Metric.closedBall p a) (hy : y ∉ Metric.ball p R) :
    R - a ≤ radius (x - y) := by
  have hx' : dist x p ≤ a := Metric.mem_closedBall.mp hx
  have hy' : R ≤ dist y p := le_of_not_gt (by simpa only [Metric.mem_ball] using hy)
  have htri := dist_triangle y x p
  have hxy : dist y x ≤ radius (x - y) := by
    rw [dist_comm y x, dist_eq_norm]
    exact norm_le_radius (x - y)
  linarith

private theorem holder_increment_of_separation {d : ℕ} {p x y : E d} {a R σ B : ℝ}
    (haR : a < R) (hσ : 0 ≤ σ) (hB : 0 ≤ B)
    (hx : x ∈ Metric.closedBall p a) (hy : y ∉ Metric.ball p R) :
    B ≤ (B / (R - a) ^ σ) * radius (x - y) ^ σ := by
  have hpos : 0 < (R - a) ^ σ := Real.rpow_pos_of_pos (by linarith) _
  have hpow : (R - a) ^ σ ≤ radius (x - y) ^ σ :=
    Real.rpow_le_rpow (by linarith) (radius_separated hx hy) hσ
  calc
    B = (B / (R - a) ^ σ) * (R - a) ^ σ := by field_simp
    _ ≤ (B / (R - a) ^ σ) * radius (x - y) ^ σ :=
      mul_le_mul_of_nonneg_left hpow (div_nonneg hB hpos.le)

private theorem radius_sub_comm {d : ℕ} (x y : E d) : radius (x - y) = radius (y - x) := by
  unfold radius
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  ring

private theorem holder_increment_zero_paste {d : ℕ} {T : Set (E d)} {p : E d}
    {a R σ B C : ℝ} {f : E d → ℝ} (haR : a < R) (hσ : 0 ≤ σ)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ x ∈ T, |f x| ≤ B)
    (hs : ∀ x ∈ T, x ∉ Metric.closedBall p a → f x = 0)
    (hl : ∀ x ∈ T ∩ Metric.ball p R, ∀ y ∈ T ∩ Metric.ball p R,
      |f x - f y| ≤ C * radius (x - y) ^ σ) :
    ∀ x ∈ T, ∀ y ∈ T,
      |f x - f y| ≤ (C + B / (R - a) ^ σ) * radius (x - y) ^ σ := by
  have hpow : 0 < (R - a) ^ σ := Real.rpow_pos_of_pos (by linarith) _
  have hfac : 0 ≤ B / (R - a) ^ σ := div_nonneg hB hpow.le
  have hclose : Metric.closedBall p a ⊆ Metric.ball p R := by
    intro z hz
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt haR)
  have hcross (x : E d) (hx : x ∈ T) (y : E d) (hy : y ∈ T)
      (hyR : y ∉ Metric.ball p R) :
      |f x - f y| ≤ (C + B / (R - a) ^ σ) * radius (x - y) ^ σ := by
    have hyzero : f y = 0 := hs y hy (fun hyclose => hyR (hclose hyclose))
    by_cases hxclose : x ∈ Metric.closedBall p a
    · rw [hyzero, sub_zero]
      calc
        |f x| ≤ B := hb x hx
        _ ≤ (B / (R - a) ^ σ) * radius (x - y) ^ σ :=
          holder_increment_of_separation haR hσ hB hxclose hyR
        _ ≤ (C + B / (R - a) ^ σ) * radius (x - y) ^ σ :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (radius_nonneg _) _)
    · rw [hs x hx hxclose, hyzero, sub_self, abs_zero]
      exact mul_nonneg (add_nonneg hC hfac) (Real.rpow_nonneg (radius_nonneg _) _)
  intro x hx y hy
  by_cases hxR : x ∈ Metric.ball p R
  · by_cases hyR : y ∈ Metric.ball p R
    · calc
        |f x - f y| ≤ C * radius (x - y) ^ σ := hl x ⟨hx, hxR⟩ y ⟨hy, hyR⟩
        _ ≤ (C + B / (R - a) ^ σ) * radius (x - y) ^ σ :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (radius_nonneg _) _)
    · exact hcross x hx y hy hyR
  · simpa only [abs_sub_comm, radius_sub_comm y x] using hcross y hy x hx hxR

private theorem supNorm_le_c2 {d : ℕ} (σ : ℝ) (S : Set (E d)) (u : E d → ℝ) :
    supNorm S u ≤ c2HolderNorm σ S u := by
  unfold c2HolderNorm
  exact le_self_add.trans (le_self_add.trans le_self_add)

private theorem partial_supNorm_le_c2 {d : ℕ} (σ : ℝ) (S : Set (E d))
    (u : E d → ℝ) (i : Fin d) :
    supNorm S (partialDeriv i u) ≤ c2HolderNorm σ S u := by
  unfold c2HolderNorm
  have h : supNorm S (partialDeriv i u) ≤ ∑ j, supNorm S (partialDeriv j u) :=
    Finset.single_le_sum (f := fun j : Fin d => supNorm S (partialDeriv j u))
      (fun _ _ => bot_le) (Finset.mem_univ i)
  exact h.trans (le_add_self.trans (le_self_add.trans le_self_add))

private theorem second_supNorm_le_c2 {d : ℕ} (σ : ℝ) (S : Set (E d))
    (u : E d → ℝ) (i j : Fin d) :
    supNorm S (secondPartial i j u) ≤ c2HolderNorm σ S u := by
  unfold c2HolderNorm
  have h : supNorm S (secondPartial i j u) ≤ ∑ k, ∑ l, supNorm S (secondPartial k l u) :=
    (Finset.single_le_sum (f := fun l : Fin d => supNorm S (secondPartial i l u))
      (fun _ _ => bot_le) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun k : Fin d => ∑ l, supNorm S (secondPartial k l u))
        (fun _ _ => bot_le) (Finset.mem_univ i))
  exact h.trans (le_add_self.trans le_self_add)

private theorem second_holderSeminorm_le_c2 {d : ℕ} (σ : ℝ) (S : Set (E d))
    (u : E d → ℝ) (i j : Fin d) :
    holderSeminorm σ S (secondPartial i j u) ≤ c2HolderNorm σ S u := by
  unfold c2HolderNorm
  have h : holderSeminorm σ S (secondPartial i j u) ≤
      ∑ k, ∑ l, holderSeminorm σ S (secondPartial k l u) :=
    (Finset.single_le_sum (f := fun l : Fin d => holderSeminorm σ S (secondPartial i l u))
      (fun _ _ => bot_le) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun k : Fin d => ∑ l, holderSeminorm σ S (secondPartial k l u))
        (fun _ _ => bot_le) (Finset.mem_univ i))
  exact h.trans le_add_self

private theorem holder_of_bounded_partials {d : ℕ} {S : Set (E d)} {f : E d → ℝ}
    {σ N : ℝ} (hS : Convex ℝ S) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hN : 0 ≤ N)
    (hdf : ∀ x ∈ S, DifferentiableAt ℝ f x)
    (hb : ∀ x ∈ S, |f x| ≤ N)
    (hpart : ∀ j, supNorm S (partialDeriv j f) ≤ ENNReal.ofReal N) :
    ∀ x ∈ S, ∀ y ∈ S,
      |f x - f y| ≤ ((d : ℝ) + 2) * N * radius (x - y) ^ σ := by
  have hfinite (j : Fin d) : supNorm S (partialDeriv j f) < ⊤ :=
    lt_of_le_of_lt (hpart j) ENNReal.ofReal_lt_top
  let L := ∑ j : Fin d, (supNorm S (partialDeriv j f)).toReal
  have hL : 0 ≤ L := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hLN : L ≤ (d : ℝ) * N := by
    calc
      L ≤ ∑ _j : Fin d, N := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [ENNReal.toReal_ofReal hN] using
          (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hpart j))
      _ = (d : ℝ) * N := by simp
  have hh := holder_increment_of_bounded_lipschitz hN hL hσ hσ1 hb
    (lipschitz_of_bounded_partials hS hdf hfinite)
  intro x hx y hy
  refine (hh x hx y hy).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (radius_nonneg _) _)
  nlinarith

private theorem cutoff_paste_eventually_zero {d : ℕ} {U : Set (E d)}
    {χ u : E d → ℝ} {x : E d} (hx : x ∉ tsupport χ) :
    U.piecewise (fun y => χ y * u y) 0 =ᶠ[𝓝 x] 0 := by
  have hneigh : (tsupport χ)ᶜ ∈ 𝓝 x := (isClosed_tsupport χ).isOpen_compl.mem_nhds hx
  filter_upwards [hneigh] with y hy
  by_cases hyU : y ∈ U
  · simp only [Set.piecewise, hyU, ↓reduceIte, image_eq_zero_of_notMem_tsupport hy,
      zero_mul, Pi.zero_apply]
  · simp only [Set.piecewise, hyU, ↓reduceIte]

private theorem cutoff_paste_jets_zero {d : ℕ} {U : Set (E d)}
    {χ u : E d → ℝ} {x : E d} (hx : x ∉ tsupport χ) (i j : Fin d) :
    partialDeriv i (U.piecewise (fun y => χ y * u y) 0) x = 0 ∧
      secondPartial i j (U.piecewise (fun y => χ y * u y) 0) x = 0 := by
  have heq := cutoff_paste_eventually_zero (U := U) (u := u) hx
  constructor
  · unfold partialDeriv
    rw [heq.fderiv_eq]
    simp
  · unfold secondPartial
    rw [(heq.iteratedFDeriv (𝕜 := ℝ) 2).self_of_nhds]
    simp

private theorem smooth_compact_holder_bounds {d : ℕ} {σ : ℝ} {f : E d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ x, |f x| ≤ M) ∧
      ∀ x y, |f x - f y| ≤ M * radius (x - y) ^ σ := by
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuous hf.continuous
  obtain ⟨L, hL⟩ := (hs.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    ((hf.fderiv_right (m := 1) (by exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).continuous)
  have hB0 : 0 ≤ B := (norm_nonneg (f 0)).trans (hB 0)
  have hL0 : 0 ≤ L := (norm_nonneg (fderiv ℝ f 0)).trans (hL 0)
  have hb (x : E d) : |f x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x
  have hl (x y : E d) : |f x - f y| ≤ L * radius (x - y) := by
    have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hf.differentiable (by norm_num) z) (fun z _ => hL z)
      (mem_univ y) (mem_univ x)
    have h' : |f x - f y| ≤ L * ‖x - y‖ := by
      simpa only [Real.norm_eq_abs] using h
    exact h'.trans (mul_le_mul_of_nonneg_left (norm_le_radius (x-y)) hL0)
  have hh := holder_increment_of_bounded_lipschitz (S := Set.univ) hB0 hL0 hσ hσ1
    (fun x _ => hb x) (fun x _ y _ => hl x y)
  refine ⟨L + 3 * B, by positivity, fun x => (hb x).trans (by linarith), ?_⟩
  intro x y
  refine (hh x (mem_univ x) y (mem_univ y)).trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (radius_nonneg _) _)

private theorem smooth_compact_partial {d : ℕ} {f : E d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (i : Fin d) :
    ContDiff ℝ ∞ (partialDeriv i f) ∧ HasCompactSupport (partialDeriv i f) := by
  constructor
  · exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  · exact hs.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)

private theorem smooth_compact_second {d : ℕ} {f : E d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (i j : Fin d) :
    ContDiff ℝ ∞ (secondPartial i j f) ∧ HasCompactSupport (secondPartial i j f) := by
  have heq : secondPartial i j f = partialDeriv i (partialDeriv j f) := by
    funext x
    exact secondPartial_eq_partialDeriv_at
      ((hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt) i j
  rw [heq]
  exact smooth_compact_partial (smooth_compact_partial hf hs j).1
    (smooth_compact_partial hf hs j).2 i

private theorem input_partial_holder {d : ℕ} {S : Set (E d)} {σ : ℝ} {u : E d → ℝ}
    (hS : IsOpen S) (hconv : Convex ℝ S) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hu : ContDiffOn ℝ 2 u S) (hn : c2HolderNorm σ S u < ⊤) (j : Fin d) :
    ∀ x ∈ S, ∀ y ∈ S,
      |partialDeriv j u x - partialDeriv j u y| ≤
        ((d : ℝ) + 2) * (c2HolderNorm σ S u).toReal * radius (x - y) ^ σ := by
  let N := (c2HolderNorm σ S u).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hreal : ENNReal.ofReal N = c2HolderNorm σ S u := ENNReal.ofReal_toReal hn.ne
  have hdu : ContDiffOn ℝ 1 (partialDeriv j u) S :=
    (hu.fderiv_of_isOpen hS (by norm_num)).clm_apply contDiffOn_const
  apply holder_of_bounded_partials hconv hσ hσ1 hN
  · intro x hx
    exact (hdu.contDiffAt (hS.mem_nhds hx)).differentiableAt (by norm_num)
  · intro x hx
    have hle := partial_supNorm_le_c2 σ S u j
    exact (abs_le_supNorm_toReal (lt_of_le_of_lt hle hn) hx).trans
      (ENNReal.toReal_mono hn.ne hle)
  · intro k
    rw [hreal]
    have heq : supNorm S (partialDeriv k (partialDeriv j u)) =
        supNorm S (secondPartial k j u) := by
      unfold supNorm
      apply iSup_congr
      intro x
      apply iSup_congr
      intro hx
      rw [secondPartial_eq_partialDeriv_at (hu.contDiffAt (hS.mem_nhds hx))]
    rw [heq]
    exact second_supNorm_le_c2 σ S u k j

private theorem input_value_holder {d : ℕ} {S : Set (E d)} {σ : ℝ} {u : E d → ℝ}
    (hS : IsOpen S) (hconv : Convex ℝ S) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hu : ContDiffOn ℝ 2 u S) (hn : c2HolderNorm σ S u < ⊤) :
    ∀ x ∈ S, ∀ y ∈ S, |u x - u y| ≤
      ((d : ℝ) + 2) * (c2HolderNorm σ S u).toReal * radius (x - y) ^ σ := by
  let N := (c2HolderNorm σ S u).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hreal : ENNReal.ofReal N = c2HolderNorm σ S u := ENNReal.ofReal_toReal hn.ne
  apply holder_of_bounded_partials hconv hσ hσ1 hN
  · intro x hx
    exact (hu.contDiffAt (hS.mem_nhds hx)).differentiableAt (by norm_num)
  · intro x hx
    have hle := supNorm_le_c2 σ S u
    exact (abs_le_supNorm_toReal (lt_of_le_of_lt hle hn) hx).trans
      (ENNReal.toReal_mono hn.ne hle)
  · intro j
    rw [hreal]
    exact partial_supNorm_le_c2 σ S u j

private theorem input_second_holder {d : ℕ} {S : Set (E d)} {σ : ℝ} {u : E d → ℝ}
    (hn : c2HolderNorm σ S u < ⊤) (i j : Fin d) {x y : E d}
    (hx : x ∈ S) (hy : y ∈ S) :
    |secondPartial i j u x - secondPartial i j u y| ≤
      (c2HolderNorm σ S u).toReal * radius (x - y) ^ σ := by
  have hs := second_supNorm_le_c2 σ S u i j
  have hh := second_holderSeminorm_le_c2 σ S u i j
  have hfinite : c0HolderNorm σ S (secondPartial i j u) < ⊤ := by
    rw [c0HolderNorm, ENNReal.add_lt_top]
    exact ⟨lt_of_le_of_lt hs hn, lt_of_le_of_lt hh hn⟩
  calc
    _ ≤ (holderSeminorm σ S (secondPartial i j u)).toReal * radius (x - y) ^ σ :=
      abs_sub_le_holderSeminorm_toReal hfinite hx hy
    _ ≤ (c2HolderNorm σ S u).toReal * radius (x - y) ^ σ :=
      mul_le_mul_of_nonneg_right (ENNReal.toReal_mono hn.ne hh)
        (Real.rpow_nonneg (radius_nonneg _) _)

private theorem smooth_compact_family_bounds {d : ℕ} {ι : Type*} [Fintype ι]
    {σ : ℝ} (f : ι → E d → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hs : ∀ i, HasCompactSupport (f i)) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ∃ A : ℝ, 0 < A ∧ (∀ i x, |f i x| ≤ A) ∧
      ∀ i x y, |f i x - f i y| ≤ A * radius (x - y) ^ σ := by
  choose B hB0 hB hBH using fun i => smooth_compact_holder_bounds (hf i) (hs i) hσ hσ1
  let A := 1 + ∑ i, B i
  have hA : 0 < A := by
    dsimp [A]
    have hsum : 0 ≤ ∑ i, B i := Finset.sum_nonneg fun i _ => hB0 i
    linarith
  have hBA (i : ι) : B i ≤ A := by
    have h := Finset.single_le_sum (f := B) (fun j _ => hB0 j) (Finset.mem_univ i)
    dsimp [A]
    linarith
  refine ⟨A, hA, fun i x => (hB i x).trans (hBA i), ?_⟩
  intro i x y
  exact (hBH i x y).trans (mul_le_mul_of_nonneg_right (hBA i)
    (Real.rpow_nonneg (radius_nonneg _) _))

private theorem cutoff_jet_bounds {d : ℕ} {σ : ℝ} {χ : E d → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : HasCompactSupport χ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ∃ A : ℝ, 0 < A ∧ (∀ x, |χ x| ≤ A) ∧
      (∀ i x, |partialDeriv i χ x| ≤ A) ∧
      (∀ i j x, |secondPartial i j χ x| ≤ A) ∧
      (∀ x y, |χ x - χ y| ≤ A * radius (x - y) ^ σ) ∧
      (∀ i x y, |partialDeriv i χ x - partialDeriv i χ y| ≤ A * radius (x - y) ^ σ) ∧
      ∀ i j x y, |secondPartial i j χ x - secondPartial i j χ y| ≤
        A * radius (x - y) ^ σ := by
  let F : Option (Fin d ⊕ (Fin d × Fin d)) → E d → ℝ
    | none => χ
    | some (Sum.inl i) => partialDeriv i χ
    | some (Sum.inr (i, j)) => secondPartial i j χ
  have hF (t : Option (Fin d ⊕ (Fin d × Fin d))) :
      ContDiff ℝ ∞ (F t) ∧ HasCompactSupport (F t) := by
    cases t with
    | none => exact ⟨hχ, hs⟩
    | some t =>
      cases t with
      | inl i => exact smooth_compact_partial hχ hs i
      | inr p => exact smooth_compact_second hχ hs p.1 p.2
  obtain ⟨A, hA, hb, hh⟩ := smooth_compact_family_bounds F
    (fun t => (hF t).1) (fun t => (hF t).2) hσ hσ1
  refine ⟨A, hA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hb none
  · intro i
    exact hb (some (Sum.inl i))
  · intro i j
    exact hb (some (Sum.inr (i, j)))
  · exact hh none
  · intro i
    exact hh (some (Sum.inl i))
  · intro i j
    exact hh (some (Sum.inr (i, j)))

private theorem holder_increment_add {d : ℕ} {S : Set (E d)} {f g : E d → ℝ}
    {A B σ : ℝ}
    (hf : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ A * radius (x - y) ^ σ)
    (hg : ∀ x ∈ S, ∀ y ∈ S, |g x - g y| ≤ B * radius (x - y) ^ σ) :
    ∀ x ∈ S, ∀ y ∈ S, |(f x + g x) - (f y + g y)| ≤
      (A + B) * radius (x - y) ^ σ := by
  intro x hx y hy
  calc
    |(f x + g x) - (f y + g y)| = |(f x - f y) + (g x - g y)| := by congr 1; ring
    _ ≤ |f x - f y| + |g x - g y| := abs_add_le _ _
    _ ≤ A * radius (x - y) ^ σ + B * radius (x - y) ^ σ :=
      add_le_add (hf x hx y hy) (hg x hx y hy)
    _ = (A + B) * radius (x - y) ^ σ := by ring

private theorem holder_cutoff_mul_jet {d : ℕ} {S : Set (E d)} {χ f : E d → ℝ}
    {A N σ : ℝ} (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hχ : ∀ x ∈ S, |χ x| ≤ A) (hf : ∀ x ∈ S, |f x| ≤ N)
    (hχH : ∀ x ∈ S, ∀ y ∈ S, |χ x - χ y| ≤ A * radius (x - y) ^ σ)
    (hfH : ∀ x ∈ S, ∀ y ∈ S,
      |f x - f y| ≤ ((d : ℝ) + 2) * N * radius (x - y) ^ σ) :
    ∀ x ∈ S, ∀ y ∈ S,
      |χ x * f x - χ y * f y| ≤ A * ((d : ℝ) + 3) * N * radius (x - y) ^ σ := by
  intro x hx y hy
  have h := holder_increment_mul hA hN hχ hf hχH hfH x hx y hy
  convert h using 1; ring

private theorem supNorm_le_of_abs_bound {d : ℕ} {S : Set (E d)} {f : E d → ℝ}
    {B : ℝ} (hb : ∀ x ∈ S, |f x| ≤ B) : supNorm S f ≤ ENNReal.ofReal B := by
  exact iSup_le fun x => iSup_le fun hx => ENNReal.ofReal_le_ofReal (hb x hx)

private theorem holderSeminorm_le_of_increment {d : ℕ} {S : Set (E d)}
    {f : E d → ℝ} {B σ : ℝ} (hb : ∀ x ∈ S, ∀ y ∈ S,
      |f x - f y| ≤ B * radius (x - y) ^ σ) :
    holderSeminorm σ S f ≤ ENNReal.ofReal B := by
  apply iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy =>
    iSup_le fun hxy => ?_
  apply ENNReal.ofReal_le_ofReal
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (radius_pos (sub_ne_zero.mpr hxy)) _)).2
    (hb x hx y hy)

private theorem input_jet_sup_bounds {d : ℕ} {S : Set (E d)} {σ : ℝ} {u : E d → ℝ}
    (hn : c2HolderNorm σ S u < ⊤) :
    (∀ x ∈ S, |u x| ≤ (c2HolderNorm σ S u).toReal) ∧
    (∀ i x, x ∈ S → |partialDeriv i u x| ≤ (c2HolderNorm σ S u).toReal) ∧
    ∀ i j x, x ∈ S → |secondPartial i j u x| ≤ (c2HolderNorm σ S u).toReal := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hle := supNorm_le_c2 σ S u
    exact (abs_le_supNorm_toReal (lt_of_le_of_lt hle hn) hx).trans
      (ENNReal.toReal_mono hn.ne hle)
  · intro i x hx
    have hle := partial_supNorm_le_c2 σ S u i
    exact (abs_le_supNorm_toReal (lt_of_le_of_lt hle hn) hx).trans
      (ENNReal.toReal_mono hn.ne hle)
  · intro i j x hx
    have hle := second_supNorm_le_c2 σ S u i j
    exact (abs_le_supNorm_toReal (lt_of_le_of_lt hle hn) hx).trans
      (ENNReal.toReal_mono hn.ne hle)

private theorem product_second_holder {d : ℕ} {S : Set (E d)} {σ A : ℝ}
    {χ u : E d → ℝ} (hS : IsOpen S) (hconv : Convex ℝ S)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hA : 0 ≤ A)
    (hχ : ContDiff ℝ 2 χ) (hu : ContDiffOn ℝ 2 u S)
    (hn : c2HolderNorm σ S u < ⊤)
    (hχ0 : ∀ x, |χ x| ≤ A) (hχ1 : ∀ i x, |partialDeriv i χ x| ≤ A)
    (hχ2 : ∀ i j x, |secondPartial i j χ x| ≤ A)
    (hχH0 : ∀ x y, |χ x - χ y| ≤ A * radius (x-y) ^ σ)
    (hχH1 : ∀ i x y, |partialDeriv i χ x - partialDeriv i χ y| ≤ A * radius (x-y) ^ σ)
    (hχH2 : ∀ i j x y, |secondPartial i j χ x - secondPartial i j χ y| ≤
      A * radius (x-y) ^ σ) (i j : Fin d) :
    ∀ x ∈ S, ∀ y ∈ S,
      |secondPartial i j (fun z => χ z * u z) x -
        secondPartial i j (fun z => χ z * u z) y| ≤
        (4 * A * ((d : ℝ) + 3) * (c2HolderNorm σ S u).toReal) * radius (x-y) ^ σ := by
  let N := (c2HolderNorm σ S u).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hle : N ≤ ((d : ℝ) + 2) * N := by
    have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    nlinarith
  have hsup := input_jet_sup_bounds hn
  have huH := input_value_holder hS hconv hσ hσ1 hu hn
  have hiH := input_partial_holder hS hconv hσ hσ1 hu hn i
  have hjH := input_partial_holder hS hconv hσ hσ1 hu hn j
  have hsecondH (x : E d) (hx : x ∈ S) (y : E d) (hy : y ∈ S) :
      |secondPartial i j u x - secondPartial i j u y| ≤
        ((d : ℝ) + 2) * N * radius (x-y) ^ σ :=
    (input_second_holder hn i j hx hy).trans
      (mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg (radius_nonneg _) _))
  have h1 := holder_cutoff_mul_jet hA hN (fun x _ => hχ0 x)
    (fun x hx => hsup.2.2 i j x hx) (fun x _ y _ => hχH0 x y) hsecondH
  have h2 := holder_cutoff_mul_jet hA hN (fun x _ => hχ1 i x)
    (fun x hx => hsup.2.1 j x hx) (fun x _ y _ => hχH1 i x y) hjH
  have h3 := holder_cutoff_mul_jet hA hN (fun x _ => hχ1 j x)
    (fun x hx => hsup.2.1 i x hx) (fun x _ y _ => hχH1 j x y) hiH
  have h4 := holder_cutoff_mul_jet hA hN (fun x _ => hχ2 i j x)
    (fun x hx => hsup.1 x hx) (fun x _ y _ => hχH2 i j x y) huH
  have hsum := holder_increment_add (holder_increment_add (holder_increment_add h1 h2) h3) h4
  intro x hx y hy
  rw [secondPartial_mul_on hS hχ.contDiffOn hu i j hx,
    secondPartial_mul_on hS hχ.contDiffOn hu i j hy]
  have h := hsum x hx y hy
  change _ ≤ (4 * A * ((d : ℝ) + 3) * N) * radius (x-y) ^ σ
  convert h using 1; ring

private theorem product_jet_sup {d : ℕ} {S : Set (E d)} {σ A : ℝ}
    {χ u : E d → ℝ} (hS : IsOpen S) (hA : 0 ≤ A) (hχ : ContDiff ℝ 2 χ)
    (hu : ContDiffOn ℝ 2 u S) (hn : c2HolderNorm σ S u < ⊤)
    (hχ0 : ∀ x, |χ x| ≤ A) (hχ1 : ∀ i x, |partialDeriv i χ x| ≤ A)
    (hχ2 : ∀ i j x, |secondPartial i j χ x| ≤ A) :
    (∀ x ∈ S, |χ x * u x| ≤ A * (c2HolderNorm σ S u).toReal) ∧
    (∀ i x, x ∈ S → |partialDeriv i (fun z => χ z * u z) x| ≤
      2 * A * (c2HolderNorm σ S u).toReal) ∧
    ∀ i j x, x ∈ S → |secondPartial i j (fun z => χ z * u z) x| ≤
      4 * A * (c2HolderNorm σ S u).toReal := by
  let N := (c2HolderNorm σ S u).toReal
  have hsup := input_jet_sup_bounds hn
  have h0 (x : E d) (hx : x ∈ S) : |χ x * u x| ≤ A * N := by
    rw [abs_mul]
    exact mul_le_mul (hχ0 x) (hsup.1 x hx) (abs_nonneg _) hA
  have h1 (i j : Fin d) (x : E d) (hx : x ∈ S) :
      |partialDeriv i χ x * partialDeriv j u x| ≤ A * N := by
    rw [abs_mul]
    exact mul_le_mul (hχ1 i x) (hsup.2.1 j x hx) (abs_nonneg _) hA
  have h2 (i j : Fin d) (x : E d) (hx : x ∈ S) :
      |χ x * secondPartial i j u x| ≤ A * N := by
    rw [abs_mul]
    exact mul_le_mul (hχ0 x) (hsup.2.2 i j x hx) (abs_nonneg _) hA
  have h3 (i j : Fin d) (x : E d) (hx : x ∈ S) :
      |secondPartial i j χ x * u x| ≤ A * N := by
    rw [abs_mul]
    exact mul_le_mul (hχ2 i j x) (hsup.1 x hx) (abs_nonneg _) hA
  refine ⟨h0, ?_, ?_⟩
  · intro i x hx
    rw [partialDeriv_mul_at (hχ.differentiable (by norm_num) x)
      ((hu.contDiffAt (hS.mem_nhds hx)).differentiableAt (by norm_num))]
    have ha : |χ x * partialDeriv i u x| ≤ A * N := by
      rw [abs_mul]
      exact mul_le_mul (hχ0 x) (hsup.2.1 i x hx) (abs_nonneg _) hA
    have hb : |u x * partialDeriv i χ x| ≤ A * N := by
      rw [mul_comm]
      rw [abs_mul]
      exact mul_le_mul (hχ1 i x) (hsup.1 x hx) (abs_nonneg _) hA
    exact (abs_add_le _ _).trans (by linarith)
  · intro i j x hx
    rw [secondPartial_mul_on hS hχ.contDiffOn hu i j hx]
    have ha := h2 i j x hx
    have hb := h1 i j x hx
    have hc := h1 j i x hx
    have hd := h3 i j x hx
    have hab := abs_add_le (χ x * secondPartial i j u x)
      (partialDeriv i χ x * partialDeriv j u x)
    have habc := abs_add_le (χ x * secondPartial i j u x +
      partialDeriv i χ x * partialDeriv j u x) (partialDeriv j χ x * partialDeriv i u x)
    have habcd := abs_add_le (χ x * secondPartial i j u x +
      partialDeriv i χ x * partialDeriv j u x + partialDeriv j χ x * partialDeriv i u x)
      (secondPartial i j χ x * u x)
    linarith

private theorem cutoff_paste_jets_on {d : ℕ} {U : Set (E d)} {χ u : E d → ℝ}
    (hU : IsOpen U) {x : E d} (hx : x ∈ U) (i j : Fin d) :
    U.piecewise (fun y => χ y * u y) 0 x = χ x * u x ∧
    partialDeriv i (U.piecewise (fun y => χ y * u y) 0) x =
      partialDeriv i (fun y => χ y * u y) x ∧
    secondPartial i j (U.piecewise (fun y => χ y * u y) 0) x =
      secondPartial i j (fun y => χ y * u y) x := by
  have heq : U.piecewise (fun y => χ y * u y) 0 =ᶠ[𝓝 x] fun y => χ y * u y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    simp only [Set.piecewise, hy, ↓reduceIte]
  refine ⟨heq.self_of_nhds, ?_, ?_⟩
  · unfold partialDeriv
    rw [heq.fderiv_eq]
  · unfold secondPartial
    rw [(heq.iteratedFDeriv (𝕜 := ℝ) 2).self_of_nhds]

private theorem c2HolderNorm_le_uniform {d : ℕ} {S : Set (E d)} {σ B : ℝ}
    {u : E d → ℝ} (h0 : ∀ x ∈ S, |u x| ≤ B)
    (h1 : ∀ i x, x ∈ S → |partialDeriv i u x| ≤ B)
    (h2 : ∀ i j x, x ∈ S → |secondPartial i j u x| ≤ B)
    (hh : ∀ i j x, x ∈ S → ∀ y ∈ S,
      |secondPartial i j u x - secondPartial i j u y| ≤ B * radius (x-y) ^ σ) :
    c2HolderNorm σ S u ≤ (↑(1 + d + 2 * d * d) : ℝ≥0∞) * ENNReal.ofReal B := by
  have hs0 := supNorm_le_of_abs_bound h0
  have hs1 (i : Fin d) := supNorm_le_of_abs_bound (h1 i)
  have hs2 (i j : Fin d) := supNorm_le_of_abs_bound (h2 i j)
  have hsh (i j : Fin d) := holderSeminorm_le_of_increment (hh i j)
  calc
    c2HolderNorm σ S u ≤ ENNReal.ofReal B + ∑ _i : Fin d, ENNReal.ofReal B +
        ∑ _i : Fin d, ∑ _j : Fin d, ENNReal.ofReal B +
        ∑ _i : Fin d, ∑ _j : Fin d, ENNReal.ofReal B := by
      unfold c2HolderNorm
      have hsum1 : (∑ i, supNorm S (partialDeriv i u)) ≤
          ∑ _i : Fin d, ENNReal.ofReal B :=
        Finset.sum_le_sum fun i _ => hs1 i
      have hsum2 : (∑ i, ∑ j, supNorm S (secondPartial i j u)) ≤
          ∑ _i : Fin d, ∑ _j : Fin d, ENNReal.ofReal B :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hs2 i j
      have hsumh : (∑ i, ∑ j, holderSeminorm σ S (secondPartial i j u)) ≤
          ∑ _i : Fin d, ∑ _j : Fin d, ENNReal.ofReal B :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hsh i j
      exact add_le_add (add_le_add (add_le_add hs0 hsum1) hsum2) hsumh
    _ = (↑(1 + d + 2 * d * d) : ℝ≥0∞) * ENNReal.ofReal B := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      ring

private theorem cutoff_paste_global_bounds {d : ℕ} {T : Set (E d)} {p : E d}
    {a R σ A : ℝ} {χ u : E d → ℝ} (hT : IsOpen T) (hconv : Convex ℝ (T ∩ Metric.ball p R))
    (haR : a < R) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hA : 0 ≤ A)
    (hχ : ContDiff ℝ 2 χ) (hs : tsupport χ ⊆ Metric.closedBall p a)
    (hu : ContDiffOn ℝ 2 u (T ∩ Metric.ball p R))
    (hn : c2HolderNorm σ (T ∩ Metric.ball p R) u < ⊤)
    (hχ0 : ∀ x, |χ x| ≤ A) (hχ1 : ∀ i x, |partialDeriv i χ x| ≤ A)
    (hχ2 : ∀ i j x, |secondPartial i j χ x| ≤ A)
    (hχH0 : ∀ x y, |χ x - χ y| ≤ A * radius (x-y) ^ σ)
    (hχH1 : ∀ i x y, |partialDeriv i χ x - partialDeriv i χ y| ≤ A * radius (x-y) ^ σ)
    (hχH2 : ∀ i j x y, |secondPartial i j χ x - secondPartial i j χ y| ≤
      A * radius (x-y) ^ σ) :
    let w := (Metric.ball p R).piecewise (fun x => χ x * u x) 0
    let N := (c2HolderNorm σ (T ∩ Metric.ball p R) u).toReal
    (∀ x ∈ T, |w x| ≤ A * N) ∧
    (∀ i x, x ∈ T → |partialDeriv i w x| ≤ 2 * A * N) ∧
    (∀ i j x, x ∈ T → |secondPartial i j w x| ≤ 4 * A * N) ∧
    ∀ i j x, x ∈ T → ∀ y ∈ T,
      |secondPartial i j w x - secondPartial i j w y| ≤
        (4 * A * ((d : ℝ) + 3) * N + (4 * A * N) / (R-a) ^ σ) * radius (x-y) ^ σ := by
  let U := Metric.ball p R
  let S := T ∩ U
  let w := U.piecewise (fun x => χ x * u x) 0
  let N := (c2HolderNorm σ S u).toReal
  have hU : IsOpen U := Metric.isOpen_ball
  have hS : IsOpen S := hT.inter hU
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hclose : Metric.closedBall p a ⊆ U := by
    intro x hx
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt haR)
  have hout (x : E d) (hx : x ∉ U) : x ∉ tsupport χ := fun hx' => hx (hclose (hs hx'))
  have hprod := product_jet_sup hS hA hχ hu hn hχ0 hχ1 hχ2
  have hw0 (x : E d) (hx : x ∈ T) : |w x| ≤ A * N := by
    by_cases hxU : x ∈ U
    · simp only [w, Set.piecewise, hxU, ↓reduceIte]
      exact hprod.1 x ⟨hx, hxU⟩
    · simp only [w, Set.piecewise, hxU, ↓reduceIte, Pi.zero_apply, abs_zero]
      exact mul_nonneg hA hN
  have hw1 (i : Fin d) (x : E d) (hx : x ∈ T) : |partialDeriv i w x| ≤ 2 * A * N := by
    by_cases hxU : x ∈ U
    · rw [(cutoff_paste_jets_on hU hxU i i).2.1]
      exact hprod.2.1 i x ⟨hx, hxU⟩
    · rw [(cutoff_paste_jets_zero (u := u) (U := U) (hout x hxU) i i).1]
      simpa only [abs_zero] using (mul_nonneg (mul_nonneg (by norm_num) hA) hN)
  have hw2 (i j : Fin d) (x : E d) (hx : x ∈ T) :
      |secondPartial i j w x| ≤ 4 * A * N := by
    by_cases hxU : x ∈ U
    · rw [(cutoff_paste_jets_on hU hxU i j).2.2]
      exact hprod.2.2 i j x ⟨hx, hxU⟩
    · rw [(cutoff_paste_jets_zero (u := u) (U := U) (hout x hxU) i j).2]
      simpa only [abs_zero] using (mul_nonneg (mul_nonneg (by norm_num) hA) hN)
  refine ⟨hw0, hw1, hw2, ?_⟩
  intro i j
  apply holder_increment_zero_paste haR hσ (by positivity) (by positivity)
  · exact hw2 i j
  · intro x _ hx
    exact (cutoff_paste_jets_zero (u := u) (U := U) (fun h => hx (hs h)) i j).2
  · intro x hx y hy
    rw [(cutoff_paste_jets_on hU hx.2 i j).2.2,
      (cutoff_paste_jets_on hU hy.2 i j).2.2]
    exact product_second_holder hS hconv hσ hσ1 hA hχ hu hn hχ0 hχ1 hχ2
      hχH0 hχH1 hχH2 i j x hx y hy

/-- A function on a half-ball can be localized to the half-space with a controlled Hölder norm. -/
theorem halfBall_cutoff {d : ℕ} (i : Fin d) {σ : ℝ}
    (hσ : 0 < σ) (hσ' : σ < 1) (p : E d) (_hp : p i = 0)
    (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : E d → ℝ,
      ContDiffOn ℝ 2 u (halfSpace i ∩ Metric.ball p R) →
      c2HolderNorm σ (halfSpace i ∩ Metric.ball p R) u < ⊤ →
      ∃ w : E d → ℝ, ContDiffOn ℝ 2 w (halfSpace i) ∧
        Set.EqOn w u (halfSpace i ∩ Metric.ball p r) ∧
        c2HolderNorm σ (halfSpace i) w ≤ ENNReal.ofReal C *
          c2HolderNorm σ (halfSpace i ∩ Metric.ball p R) u := by
  let a := (r + R) / 2
  have hra : r < a := by dsimp [a]; linarith
  have haR : a < R := by dsimp [a]; linarith
  obtain ⟨χ, hχ, hχs, hχone, hχsupport⟩ := exists_ball_cutoff p hr hra
  have hs : tsupport χ ⊆ Metric.closedBall p a :=
    hχsupport.trans Metric.ball_subset_closedBall
  have hsR : tsupport χ ⊆ Metric.ball p R := by
    intro x hx
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp (hs hx)).trans_lt haR)
  obtain ⟨A, hA, hχ0, hχ1, hχ2, hχH0, hχH1, hχH2⟩ :=
    cutoff_jet_bounds hχ hχs hσ.le hσ'.le
  let t := (R - a) ^ σ
  have ht : 0 < t := Real.rpow_pos_of_pos (by linarith) _
  let D := 1 + A + 2 * A + 4 * A + 4 * A * ((d : ℝ) + 3) + 4 * A / t
  have hD : 0 < D := by dsimp [D]; positivity
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hterm : 0 ≤ 4 * A * ((d : ℝ) + 3) := by positivity
  have hdiv : 0 ≤ 4 * A / t := by positivity
  have hDA : A ≤ D := by dsimp [D]; linarith
  have hD1 : 2 * A ≤ D := by dsimp [D]; linarith
  have hD2 : 4 * A ≤ D := by dsimp [D]; linarith
  have hDH : 4 * A * ((d : ℝ) + 3) + 4 * A / t ≤ D := by dsimp [D]; linarith
  let q : ℕ := 1 + d + 2 * d * d
  let C : ℝ := (q : ℝ) * D
  have hq : 0 < (q : ℝ) := by dsimp [q]; positivity
  have hC : 0 < C := mul_pos hq hD
  refine ⟨C, hC, ?_⟩
  intro u hu hn
  let T := halfSpace i
  let S := T ∩ Metric.ball p R
  let w := (Metric.ball p R).piecewise (fun x => χ x * u x) 0
  let N := (c2HolderNorm σ S u).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hT : IsOpen T := isOpen_lt continuous_const (continuous_apply i)
  have hconvT : Convex ℝ T := by
    change Convex ℝ ((LinearMap.proj i : E d →ₗ[ℝ] ℝ) ⁻¹' Set.Ioi 0)
    exact (convex_Ioi (0 : ℝ)).linear_preimage (LinearMap.proj i : E d →ₗ[ℝ] ℝ)
  have hconv : Convex ℝ S := hconvT.inter (convex_ball p R)
  have hχ2' : ContDiff ℝ 2 χ := hχ.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hb := cutoff_paste_global_bounds hT hconv haR hσ.le hσ'.le hA.le hχ2' hs hu hn
    hχ0 hχ1 hχ2 hχH0 hχH1 hχH2
  have hval (x : E d) (hx : x ∈ T) : |w x| ≤ D * N :=
    (hb.1 x hx).trans (mul_le_mul_of_nonneg_right hDA hN)
  have hfirst (j : Fin d) (x : E d) (hx : x ∈ T) : |partialDeriv j w x| ≤ D * N :=
    (hb.2.1 j x hx).trans (mul_le_mul_of_nonneg_right hD1 hN)
  have hsecond (j k : Fin d) (x : E d) (hx : x ∈ T) :
      |secondPartial j k w x| ≤ D * N :=
    (hb.2.2.1 j k x hx).trans (mul_le_mul_of_nonneg_right hD2 hN)
  have hholder (j k : Fin d) (x : E d) (hx : x ∈ T) (y : E d) (hy : y ∈ T) :
      |secondPartial j k w x - secondPartial j k w y| ≤ D * N * radius (x-y) ^ σ := by
    refine (hb.2.2.2 j k x hx y hy).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (radius_nonneg _) _)
    calc
      4 * A * ((d : ℝ) + 3) * N + (4 * A * N) / (R-a) ^ σ =
          (4 * A * ((d : ℝ) + 3) + 4 * A / t) * N := by dsimp [t]; ring
      _ ≤ D * N := mul_le_mul_of_nonneg_right hDH hN
  have hbound := c2HolderNorm_le_uniform hval hfirst hsecond hholder
  have hNreal : ENNReal.ofReal (D * N) = ENNReal.ofReal D * c2HolderNorm σ S u := by
    rw [ENNReal.ofReal_mul hD.le, ENNReal.ofReal_toReal hn.ne]
  have hCreal : ENNReal.ofReal C = (↑q : ℝ≥0∞) * ENNReal.ofReal D := by
    dsimp [C]
    rw [ENNReal.ofReal_mul hq.le]
    simp
  refine ⟨w, contDiffOn_cutoff_paste Metric.isOpen_ball hχ2' hsR hu, ?_, ?_⟩
  · intro x hx
    have hxR : x ∈ Metric.ball p R := Metric.ball_subset_ball hrR.le hx.2
    simp only [w, Set.piecewise, hxR, ↓reduceIte, hχone x hx.2, one_mul]
  · calc
      c2HolderNorm σ T w ≤ (↑q : ℝ≥0∞) * ENNReal.ofReal (D * N) := hbound
      _ = ENNReal.ofReal C * c2HolderNorm σ S u := by rw [hNreal, hCreal]; ring

end
end LatticeProb.Elliptic.HolderExtension
