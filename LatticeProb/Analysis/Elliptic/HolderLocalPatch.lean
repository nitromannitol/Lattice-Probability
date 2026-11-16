import LatticeProb.Analysis.Elliptic.HolderInterpolation
import LatticeProb.Analysis.Elliptic.HolderDefiningGraphProved
import LatticeProb.Analysis.Elliptic.HolderReflectionBound
import LatticeProb.Analysis.Elliptic.HolderHalfBallCutoff
import LatticeProb.Analysis.Elliptic.HolderComposition
import LatticeProb.Analysis.Elliptic.HolderCutoffV2

/-!
# Boundary patches for Hölder extension

Near a boundary point of a bounded `C^{2,σ}` domain, every `C^{2,σ}` function on the domain agrees
with a compactly supported `C^2` function on the whole space whose global `C^{2,σ}` norm is bounded
by a fixed multiple of its norm on the domain.

The boundary is flattened by the shear `x ↦ x` with the graph coordinate `x i` replaced by
`s * (g x - x i)`. The function is pulled back to a half-ball, cut off on the half-space, reflected
across the flat boundary, cut off in the flattened coordinates and pushed forward. The global norm
of the result is controlled by its norm on a ball containing its support.

## Main statement

* `boundary_local_patch`: the local patch at a boundary point.
-/

open Set Metric LatticeProb.Euclidean.Lattice
open scoped ContDiff ENNReal NNReal Topology

namespace LatticeProb.Elliptic.HolderExtension

/-- The shear replacing the coordinate `x i` by `a * g x + b * x i`. -/
private def graphShear {d : ℕ} (i : Fin d) (a b : ℝ) (g : E d → ℝ) (x : E d) : E d :=
  Function.update x i (a * g x + b * x i)

private theorem graphShear_apply_self {d : ℕ} (i : Fin d) (a b : ℝ) (g : E d → ℝ) (x : E d) :
    graphShear i a b g x i = a * g x + b * x i := by
  simp [graphShear]

private theorem graphShear_left_inv {d : ℕ} {i : Fin d} {g : E d → ℝ}
    (hinv : ∀ x t, g (Function.update x i t) = g x) {s : ℝ} (hs : s * s = 1) (x : E d) :
    graphShear i 1 (-s) g (graphShear i s (-s) g x) = x := by
  have h : 1 * g x + -s * (s * g x + -s * x i) = x i := by
    linear_combination (x i - g x) * hs
  simp only [graphShear, hinv, Function.update_idem, Function.update_self, h,
    Function.update_eq_self]

private theorem graphShear_right_inv {d : ℕ} {i : Fin d} {g : E d → ℝ}
    (hinv : ∀ x t, g (Function.update x i t) = g x) {s : ℝ} (hs : s * s = 1) (y : E d) :
    graphShear i s (-s) g (graphShear i 1 (-s) g y) = y := by
  have h : s * g y + -s * (1 * g y + -s * y i) = y i := by
    linear_combination y i * hs
  simp only [graphShear, hinv, Function.update_idem, Function.update_self, h,
    Function.update_eq_self]

private theorem contDiff_graphShear {d : ℕ} (i : Fin d) (a b : ℝ) {g : E d → ℝ}
    (hg : ContDiff ℝ 2 g) : ContDiff ℝ 2 (graphShear i a b g) := by
  refine contDiff_pi.2 fun k => ?_
  by_cases hk : k = i
  · subst hk
    simpa only [graphShear, Function.update_self] using
      (contDiff_const.mul hg).add (contDiff_const.mul (contDiff_apply ℝ ℝ k))
  · simpa only [graphShear, Function.update_of_ne hk] using contDiff_apply ℝ ℝ k

private theorem secondPartial_fun_add {d : ℕ} (j k : Fin d) (f g : E d → ℝ) (x : E d)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    secondPartial j k (fun y => f y + g y) x = secondPartial j k f x +
      secondPartial j k g x := by
  simp only [secondPartial, fun_iteratedFDeriv_add_apply hf hg,
    add_apply]

private theorem secondPartial_const_mul {d : ℕ} (j k : Fin d) (c : ℝ) (f : E d → ℝ)
    (x : E d) (hf : ContDiffAt ℝ 2 f x) :
    secondPartial j k (fun y => c * f y) x = c * secondPartial j k f x := by
  simp only [secondPartial, ← smul_eq_mul, iteratedFDeriv_const_smul_apply' hf,
    smul_apply]

private theorem radius_sub_comm {d : ℕ} (x y : E d) : radius (x - y) = radius (y - x) := by
  simp only [radius, Pi.sub_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- On a bounded set, `x ↦ a * g x + b * x k` has finite `C^{2,σ}` norm when `g` has finite global
`C^{2,σ}` norm. -/
private theorem c2HolderNorm_affine_lt_top {d : ℕ} {σ : ℝ} {g : E d → ℝ} (hg : ContDiff ℝ 2 g)
    (hgn : c2HolderNorm σ univ g < ⊤) (a b : ℝ) (k : Fin d) {S : Set (E d)}
    (hS : Bornology.IsBounded S) :
    c2HolderNorm σ S (fun x => a * g x + b * x k) < ⊤ := by
  obtain ⟨M, hM⟩ := hS.subset_closedBall 0
  set N := (c2HolderNorm σ univ g).toReal
  have hlin : ContDiff ℝ 2 (fun y : E d => y k) := contDiff_apply ℝ ℝ k
  have h0 : ∀ x ∈ S, |a * g x + b * x k| ≤ |a| * N + |b| * M := by
    intro x hx
    have hgx : |g x| ≤ N := abs_le_c2HolderNorm_toReal hgn (mem_univ x)
    have hxk : |x k| ≤ M := by
      have h1 := norm_le_pi_norm x k
      have h2 := mem_closedBall_zero_iff.1 (hM hx)
      rw [Real.norm_eq_abs] at h1
      linarith
    calc |a * g x + b * x k| ≤ |a * g x| + |b * x k| := abs_add_le _ _
      _ = |a| * |g x| + |b| * |x k| := by rw [abs_mul, abs_mul]
      _ ≤ |a| * N + |b| * M := by gcongr
  have h1 : ∀ j x, x ∈ S → |partialDeriv j (fun x => a * g x + b * x k) x| ≤
      |a| * N + |b| * 1 := by
    intro j x _
    have hgx : HasFDerivAt g (fderiv ℝ g x) x :=
      (hg.differentiable (by norm_num) x).hasFDerivAt
    have h := (hgx.const_mul a).fun_add ((hasFDerivAt_apply k x).const_mul b)
    rw [partialDeriv, h.fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    have hgj : |fderiv ℝ g x (Pi.single j 1)| ≤ N :=
      abs_partialDeriv_le_c2HolderNorm_toReal hgn j (mem_univ x)
    have hsj : |(Pi.single j (1 : ℝ) : E d) k| ≤ 1 := by
      rw [Pi.single_apply]
      split_ifs <;> simp
    calc _ ≤ |a * fderiv ℝ g x (Pi.single j 1)| + |b * (Pi.single j (1 : ℝ) : E d) k| :=
          abs_add_le _ _
      _ = |a| * |fderiv ℝ g x (Pi.single j 1)| + |b| * |(Pi.single j (1 : ℝ) : E d) k| := by
          rw [abs_mul, abs_mul]
      _ ≤ |a| * N + |b| * 1 := by gcongr
  have hsd : ∀ j l x, secondPartial j l (fun x => a * g x + b * x k) x =
      a * secondPartial j l g x := by
    intro j l x
    have hA : ContDiffAt ℝ 2 (fun y => a * g y) x := (contDiff_const.mul hg).contDiffAt
    have hB : ContDiffAt ℝ 2 (fun y : E d => b * y k) x := (contDiff_const.mul hlin).contDiffAt
    have h3 := secondPartial_const_mul j l b (fun y : E d => y k) x hlin.contDiffAt
    rw [secondPartial_fun_add j l _ _ x hA hB, secondPartial_const_mul j l a g x hg.contDiffAt,
      h3, secondPartial_coordinate, mul_zero, add_zero]
  have h2 : ∀ j l x, x ∈ S → |secondPartial j l (fun x => a * g x + b * x k) x| ≤ |a| * N := by
    intro j l x _
    rw [hsd, abs_mul]
    gcongr
    exact abs_secondPartial_le_c2HolderNorm_toReal hgn j l (mem_univ x)
  have hH : ∀ j l x, x ∈ S → ∀ y ∈ S,
      |secondPartial j l (fun x => a * g x + b * x k) x -
        secondPartial j l (fun x => a * g x + b * x k) y| ≤ |a| * N * radius (x - y) ^ σ := by
    intro j l x _ y _
    rw [hsd, hsd, ← mul_sub, abs_mul, mul_assoc]
    gcongr
    exact abs_sub_secondPartial_le_c2HolderNorm_toReal hgn j l (mem_univ x) (mem_univ y)
  refine (c2HolderNorm_le_of_bounds h0 h1 h2 hH).trans_lt ?_
  simp only [ENNReal.add_lt_top, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hd : (d : ℝ≥0∞) < ⊤ := ENNReal.natCast_lt_top d
  exact ⟨⟨⟨ENNReal.ofReal_lt_top, ENNReal.mul_lt_top hd ENNReal.ofReal_lt_top⟩,
    ENNReal.mul_lt_top hd (ENNReal.mul_lt_top hd ENNReal.ofReal_lt_top)⟩,
    ENNReal.mul_lt_top hd (ENNReal.mul_lt_top hd ENNReal.ofReal_lt_top)⟩

/-- Each coordinate of a graph shear has finite `C^{2,σ}` norm on a bounded set. -/
private theorem c2HolderNorm_graphShear_lt_top {d : ℕ} {σ : ℝ} (i : Fin d) (a b : ℝ)
    {g : E d → ℝ} (hg : ContDiff ℝ 2 g) (hgn : c2HolderNorm σ univ g < ⊤) {S : Set (E d)}
    (hS : Bornology.IsBounded S) (k : Fin d) :
    c2HolderNorm σ S (fun x => graphShear i a b g x k) < ⊤ := by
  by_cases hk : k = i
  · subst hk
    simpa only [graphShear, Function.update_self] using c2HolderNorm_affine_lt_top hg hgn a b k hS
  · simpa only [graphShear, Function.update_of_ne hk, zero_mul, one_mul, zero_add] using
      c2HolderNorm_affine_lt_top hg hgn 0 1 k hS

/-- A `C^2` map is Lipschitz on every ball. -/
private theorem exists_lipschitzOnWith_ball {d : ℕ} {φ : E d → E d} (hφ : ContDiff ℝ 2 φ)
    (c : E d) (R : ℝ) : ∃ K : ℝ≥0, LipschitzOnWith K φ (ball c R) := by
  have hcont : Continuous (fun x => fderiv ℝ φ x) := hφ.continuous_fderiv (by norm_num)
  obtain ⟨M, hM⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨M.toNNReal, (convex_ball c R).lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => hφ.differentiable (by norm_num) x) (fun x hx => ?_)⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
  exact le_max_of_le_left (hM x (ball_subset_closedBall hx))

/-- The global `C^{2,σ}` norm of a function supported in `closedBall c ρ` is controlled by its
norm on `ball c (2 * ρ)`. -/
private theorem c2HolderNorm_univ_le_of_tsupport_subset {d : ℕ} {σ : ℝ} (hσ : 0 < σ)
    (c : E d) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : E d → ℝ, tsupport f ⊆ closedBall c ρ →
      c2HolderNorm σ univ f ≤ ENNReal.ofReal C * c2HolderNorm σ (ball c (2 * ρ)) f := by
  set K : ℝ := 1 + 1 / ρ ^ σ with hKdef
  have hρσ : 0 < ρ ^ σ := Real.rpow_pos_of_pos hρ σ
  have hK1 : 1 ≤ K := by
    have : 0 ≤ 1 / ρ ^ σ := by positivity
    linarith
  have hK0 : 0 ≤ K := by linarith
  have hs1 : 0 ≤ ∑ _ : Fin d, K := Finset.sum_nonneg fun _ _ => hK0
  have hs2 : 0 ≤ ∑ _ : Fin d, ∑ _ : Fin d, K := Finset.sum_nonneg fun _ _ => hs1
  refine ⟨K + ∑ _ : Fin d, K + ∑ _ : Fin d, ∑ _ : Fin d, K + ∑ _ : Fin d, ∑ _ : Fin d, K,
    by positivity, fun f hf => ?_⟩
  set B := ball c (2 * ρ)
  rcases eq_or_lt_of_le (le_top : c2HolderNorm σ B f ≤ ⊤) with hn | hn
  · rw [hn, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
    exact le_top
  set N := (c2HolderNorm σ B f).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hNK : N ≤ K * N := le_mul_of_one_le_left hN hK1
  have hzero : ∀ x, x ∉ closedBall c ρ → f x = 0 ∧ (∀ j, partialDeriv j f x = 0) ∧
      ∀ j l, secondPartial j l f x = 0 := by
    intro x hx
    have hxs : x ∉ tsupport f := fun h => hx (hf h)
    refine ⟨image_eq_zero_of_notMem_tsupport hxs, fun j => ?_, fun j l => ?_⟩
    · have h : fderiv ℝ f x = 0 := by
        by_contra h
        exact hxs (support_fderiv_subset (𝕜 := ℝ) (f := f) h)
      simp [partialDeriv, h]
    · have h : iteratedFDeriv ℝ 2 f x = 0 := by
        by_contra h
        exact hxs (support_iteratedFDeriv_subset (𝕜 := ℝ) (f := f) 2 h)
      simp [secondPartial, h]
  have hout : ∀ x, x ∉ B → x ∉ closedBall c ρ := fun x hx hx' =>
    hx (closedBall_subset_ball (by linarith) hx')
  have h0 : ∀ x ∈ univ, |f x| ≤ K * N := by
    intro x _
    by_cases hx : x ∈ B
    · exact (abs_le_c2HolderNorm_toReal hn hx).trans hNK
    · rw [(hzero x (hout x hx)).1, abs_zero]
      positivity
  have h1 : ∀ j x, x ∈ univ → |partialDeriv j f x| ≤ K * N := by
    intro j x _
    by_cases hx : x ∈ B
    · exact (abs_partialDeriv_le_c2HolderNorm_toReal hn j hx).trans hNK
    · rw [(hzero x (hout x hx)).2.1 j, abs_zero]
      positivity
  have h2' : ∀ j l x, |secondPartial j l f x| ≤ N := by
    intro j l x
    by_cases hx : x ∈ B
    · exact abs_secondPartial_le_c2HolderNorm_toReal hn j l hx
    · rw [(hzero x (hout x hx)).2.2 j l, abs_zero]
      exact hN
  have h2 : ∀ j l x, x ∈ univ → |secondPartial j l f x| ≤ K * N := fun j l x _ =>
    (h2' j l x).trans hNK
  have hfar : ∀ j l x y, x ∉ B →
      |secondPartial j l f x - secondPartial j l f y| ≤ K * N * radius (x - y) ^ σ := by
    intro j l x y hx
    rw [(hzero x (hout x hx)).2.2 j l, zero_sub, abs_neg]
    by_cases hy : y ∈ closedBall c ρ
    · have hxy : ρ ≤ radius (x - y) := by
        have hxc : 2 * ρ ≤ dist x c := not_lt.1 fun h => hx (mem_ball.2 h)
        have hyc : dist y c ≤ ρ := mem_closedBall.1 hy
        have htri := dist_triangle x y c
        have hxy' : dist x y = ‖x - y‖ := dist_eq_norm x y
        exact (by linarith : ρ ≤ ‖x - y‖).trans (pi_norm_le_radius _)
      have hpow : ρ ^ σ ≤ radius (x - y) ^ σ := Real.rpow_le_rpow hρ.le hxy hσ.le
      calc |secondPartial j l f y| ≤ N := h2' j l y
        _ = N * (1 / ρ ^ σ) * ρ ^ σ := by field_simp
        _ ≤ K * N * radius (x - y) ^ σ := by
          rw [mul_comm K N]
          gcongr
          linarith
    · rw [(hzero y hy).2.2 j l, abs_zero]
      exact mul_nonneg (mul_nonneg hK0 hN) (Real.rpow_nonneg (radius_nonneg _) _)
  have hH : ∀ j l x, x ∈ univ → ∀ y ∈ univ,
      |secondPartial j l f x - secondPartial j l f y| ≤ K * N * radius (x - y) ^ σ := by
    intro j l x _ y _
    by_cases hx : x ∈ B
    · by_cases hy : y ∈ B
      · calc _ ≤ N * radius (x - y) ^ σ := abs_sub_secondPartial_le_c2HolderNorm_toReal hn j l hx hy
          _ ≤ K * N * radius (x - y) ^ σ := by
            gcongr
            exact Real.rpow_nonneg (radius_nonneg _) _
      · rw [abs_sub_comm, radius_sub_comm]
        exact hfar j l y x hy
    · exact hfar j l x y hx
  refine (c2HolderNorm_le_of_bounds h0 h1 h2 hH).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_toReal hn.ne, ENNReal.ofReal_add (by positivity) hs2,
    ENNReal.ofReal_add (by positivity) hs2, ENNReal.ofReal_add hK0 hs1]
  simp only [ENNReal.ofReal_sum_of_nonneg (fun _ _ => hs1),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => hK0), ENNReal.ofReal_mul hK0, add_mul,
    Finset.sum_mul]
  rfl

/-- **Boundary patch.** Near a boundary point `p` of a bounded `C^{2,σ}` domain `U` whose closure
lies in an open set `U'`, there are open sets `V ∋ p` and `W` with `closure V ⊆ W` and
`closure W ⊆ U'`, and a constant `C`, such that every `C^{2,σ}` function `u` on `U` agrees on
`V ∩ U` with a compactly supported `C^2` function supported in `W` whose global `C^{2,σ}` norm is
at most `C` times the norm of `u` on `U`. -/
theorem boundary_local_patch {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (hσ' : σ < 1)
    {U U' : Set (E d)} (hU : IsC2HolderDomain σ U) (hU' : IsOpen U')
    (hsub : closure U ⊆ U') {p : E d} (hp : p ∈ frontier U) :
    ∃ V W : Set (E d), IsOpen V ∧ IsOpen W ∧ p ∈ V ∧ closure V ⊆ W ∧
      closure W ⊆ U' ∧ ∃ C : ℝ, 0 < C ∧ ∀ u : E d → ℝ,
        ContDiffOn ℝ 2 u U → c2HolderNorm σ U u < ⊤ →
        ∃ v : E d → ℝ, ContDiff ℝ 2 v ∧ HasCompactSupport v ∧
          tsupport v ⊆ W ∧ Set.EqOn v u (V ∩ U) ∧
          c2HolderNorm σ Set.univ v ≤ ENNReal.ofReal C * c2HolderNorm σ U u := by
  obtain ⟨i, g, r, hr, hg, hgn, hinv, hgp, hside⟩ :=
    definingFunction_local_graph hσ hσ' hU hp
  obtain ⟨s, hs, hsideU⟩ : ∃ s : ℝ, s * s = 1 ∧
      ∀ x ∈ ball p r, x ∈ U ↔ 0 < s * (g x - x i) := by
    rcases hside with h | h
    · exact ⟨1, by norm_num, fun x hx => by rw [h x hx, one_mul, sub_pos]⟩
    · refine ⟨-1, by norm_num, fun x hx => ?_⟩
      rw [h x hx]
      constructor <;> intro h' <;> linarith
  obtain ⟨ε, hε, hεU'⟩ := Metric.isOpen_iff.1 hU' p (hsub (frontier_subset_closure hp))
  set Φ : E d → E d := graphShear i s (-s) g with hΦdef
  set Ψ : E d → E d := graphShear i 1 (-s) g with hΨdef
  have hΦ : ContDiff ℝ 2 Φ := contDiff_graphShear i s (-s) hg
  have hΨ : ContDiff ℝ 2 Ψ := contDiff_graphShear i 1 (-s) hg
  have hΨΦ : ∀ x, Ψ (Φ x) = x := graphShear_left_inv hinv hs
  have hΦΨ : ∀ y, Φ (Ψ y) = y := graphShear_right_inv hinv hs
  have hΦi : ∀ x, Φ x i = s * (g x - x i) := fun x => by
    rw [hΦdef, graphShear_apply_self]
    ring
  set q : E d := Φ p with hqdef
  have hqi : q i = 0 := by rw [hqdef, hΦi, hgp, sub_self, mul_zero]
  have hΨq : Ψ q = p := hΨΦ p
  set ρW : ℝ := ε / 2 with hρW
  have hρW0 : 0 < ρW := by positivity
  set ρ₁ : ℝ := min r ρW / 2 with hρ₁
  have hmin : 0 < min r ρW := lt_min hr hρW0
  have hρ₁0 : 0 < ρ₁ := by positivity
  have hρ₁r : ρ₁ < r := by
    have := min_le_left r ρW
    linarith
  have hρ₁W : ρ₁ < ρW := by
    have := min_le_right r ρW
    linarith
  obtain ⟨R, hR, hRΨ⟩ : ∃ R > 0, ∀ y, dist y q < R → dist (Ψ y) p < ρ₁ := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hΨ.continuous.continuousAt ρ₁ hρ₁0
    exact ⟨δ, hδ, fun y hy => hΨq ▸ h hy⟩
  obtain ⟨ρV₀, hρV₀, hρVΦ⟩ : ∃ δ > 0, ∀ x, dist x p < δ → dist (Φ x) q < R / 4 := by
    obtain ⟨δ, hδ, h⟩ :=
      Metric.continuousAt_iff.1 hΦ.continuous.continuousAt (R / 4) (by positivity)
    exact ⟨δ, hδ, fun x hx => h hx⟩
  set ρV : ℝ := min ρV₀ (ρW / 2) with hρV
  have hρV0 : 0 < ρV := lt_min hρV₀ (by positivity)
  have hρVW : ρV < ρW := (min_le_right _ _).trans_lt (by linarith)
  have hmemU : ∀ y, dist y q < R → 0 < y i → Ψ y ∈ U := by
    intro y hy hyi
    have hx : Ψ y ∈ ball p r := mem_ball.2 ((hRΨ y hy).trans hρ₁r)
    rw [hsideU _ hx, ← hΦi, hΦΨ]
    exact hyi
  refine ⟨ball p ρV, ball p ρW, isOpen_ball, isOpen_ball, mem_ball_self hρV0,
    closure_ball_subset_closedBall.trans (closedBall_subset_ball hρVW),
    closure_ball_subset_closedBall.trans ((closedBall_subset_ball (by linarith)).trans hεU'),
    ?_⟩
  set S : Set (E d) := halfSpace i ∩ ball q R with hSdef
  have hHopen : IsOpen (halfSpace i) := isOpen_lt continuous_const (continuous_apply i)
  have hHconv : Convex ℝ (halfSpace i) := by
    intro x hx y hy a b ha hb hab
    change 0 < x i at hx
    change 0 < y i at hy
    change 0 < (a • x + b • y) i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx) (mul_nonneg hb hy.le)
    · subst ha'
      rw [zero_add] at hab
      subst hab
      simpa using hy
  have hSopen : IsOpen S := hHopen.inter isOpen_ball
  have hSconv : Convex ℝ S := hHconv.inter (convex_ball q R)
  have hSbdd : Bornology.IsBounded S := isBounded_ball.subset inter_subset_right
  have hmapS : MapsTo Ψ S U := fun y hy => hmemU y (mem_ball.1 hy.2) hy.1
  obtain ⟨A, hA, hAU⟩ := firstDeriv_holder_bound hσ hσ' hU
  obtain ⟨K₁, hK₁⟩ := exists_lipschitzOnWith_ball hΨ q R
  have hΨn : ∀ k, c2HolderNorm σ S (fun y => Ψ y k) < ⊤ := fun k =>
    c2HolderNorm_graphShear_lt_top i 1 (-s) hg hgn hSbdd k
  have hΨfirst : ∀ k j, holderSeminorm σ S (partialDeriv j (fun y => Ψ y k)) < ⊤ :=
    fun k j => (holderSeminorm_partialDeriv_le_c2HolderNorm_of_convex hσ hσ' hSopen hSconv
      (contDiff_pi.1 hΨ k).contDiffOn (hΨn k) j).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hΨn k))
  obtain ⟨C₁, hC₁, hcomp₁⟩ := c2HolderNorm_comp_of_first_holder hσ hσ' S U hSopen hU.1 Ψ
    hΨ.contDiffOn hmapS hΨn hΨfirst K₁ (hK₁.mono inter_subset_right) A hA
  obtain ⟨C₂, hC₂, hcut⟩ :=
    halfBall_cutoff i hσ hσ' q hqi (R / 2) R (by positivity) (by linarith)
  obtain ⟨C₃, hC₃, hrefl⟩ := halfSpace_reflection_bound i hσ hσ'
  let χ : ContDiffBump q := ⟨R / 4, R / 2, by positivity, by linarith⟩
  obtain ⟨C₄, hC₄, hmul⟩ :=
    HolderCutoffV2.c2HolderNorm_mul_cutoff hσ hσ' χ χ.contDiff χ.hasCompactSupport
  obtain ⟨K₂, hK₂⟩ := exists_lipschitzOnWith_ball hΦ p (2 * ρ₁)
  obtain ⟨C₅, hC₅, hcomp₂⟩ := c2HolderNorm_comp hσ hσ' (ball p (2 * ρ₁)) univ isOpen_ball
    isOpen_univ (convex_ball _ _) convex_univ Φ hΦ.contDiffOn (mapsTo_univ _ _)
    (fun k => c2HolderNorm_graphShear_lt_top i s (-s) hg hgn isBounded_ball k) K₂ hK₂
  obtain ⟨C₆, hC₆, hloc⟩ := c2HolderNorm_univ_le_of_tsupport_subset hσ p hρ₁0
  refine ⟨C₆ * C₅ * C₄ * C₃ * C₂ * C₁, by positivity, fun u hu hun => ?_⟩
  obtain ⟨hu₁, hu₁n⟩ := hcomp₁ u hu hun (hAU u hu hun)
  have hu₁f : c2HolderNorm σ S (u ∘ Ψ) < ⊤ :=
    hu₁n.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hun)
  obtain ⟨w, hw, hweq, hwn⟩ := hcut (u ∘ Ψ) hu₁ hu₁f
  have hwf : c2HolderNorm σ (halfSpace i) w < ⊤ :=
    hwn.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu₁f)
  obtain ⟨w', hw', hw'eq, hw'form⟩ := halfSpace_reflection_C2 i hσ hσ' w hw hwf
  have hw'n := hrefl w w' hw hwf hw' hw'eq hw'form
  have hw'f : c2HolderNorm σ univ w' < ⊤ :=
    hw'n.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hwf)
  set h : E d → ℝ := fun y => χ y * w' y with hhdef
  have hh : ContDiff ℝ 2 h := χ.contDiff.mul hw'
  have hhn : c2HolderNorm σ univ h ≤ ENNReal.ofReal C₄ * c2HolderNorm σ univ w' :=
    hmul w' hw' hw'f
  have hhf : c2HolderNorm σ univ h < ⊤ :=
    hhn.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hw'f)
  obtain ⟨-, hvn⟩ := hcomp₂ h hh.contDiffOn hhf
  have hsupp : tsupport (h ∘ Φ) ⊆ ball p ρ₁ := by
    intro x hx
    have hx' := tsupport_comp_subset_preimage h hΦ.continuous hx
    have hχx : Φ x ∈ tsupport χ := tsupport_mul_subset_left hx'
    rw [χ.tsupport_eq] at hχx
    have hlt : dist (Φ x) q < R :=
      (mem_closedBall.1 hχx).trans_lt (by change R / 2 < R; linarith)
    have := hRΨ (Φ x) hlt
    rw [hΨΦ] at this
    exact mem_ball.2 this
  refine ⟨h ∘ Φ, hh.comp hΦ, ?_, hsupp.trans (ball_subset_ball hρ₁W.le), ?_, ?_⟩
  · exact (isCompact_closedBall p ρ₁).of_isClosed_subset (isClosed_tsupport _)
      (hsupp.trans ball_subset_closedBall)
  · rintro x ⟨hxV, hxU⟩
    have hy : dist (Φ x) q < R / 4 :=
      hρVΦ x ((mem_ball.1 hxV).trans_le (min_le_left _ _))
    have hxr : x ∈ ball p r := by
      have := hRΨ (Φ x) (by linarith)
      rw [hΨΦ] at this
      exact mem_ball.2 (this.trans hρ₁r)
    have hyH : Φ x ∈ halfSpace i := by
      change 0 < Φ x i
      rw [hΦi]
      exact (hsideU x hxr).1 hxU
    have hχ1 : χ (Φ x) = 1 :=
      χ.one_of_mem_closedBall (mem_closedBall.2 (le_of_lt (by exact hy)))
    have hwx : w (Φ x) = (u ∘ Ψ) (Φ x) := hweq ⟨hyH, mem_ball.2 (by linarith)⟩
    simp only [Function.comp_apply, hhdef]
    rw [hχ1, one_mul, hw'eq hyH, hwx, Function.comp_apply, hΨΦ]
  · calc c2HolderNorm σ univ (h ∘ Φ)
        ≤ ENNReal.ofReal C₆ * c2HolderNorm σ (ball p (2 * ρ₁)) (h ∘ Φ) :=
          hloc _ (hsupp.trans ball_subset_closedBall)
      _ ≤ ENNReal.ofReal C₆ * (ENNReal.ofReal C₅ * c2HolderNorm σ univ h) := by
          gcongr
      _ ≤ ENNReal.ofReal C₆ * (ENNReal.ofReal C₅ * (ENNReal.ofReal C₄ *
          c2HolderNorm σ univ w')) := by
          gcongr
      _ ≤ ENNReal.ofReal C₆ * (ENNReal.ofReal C₅ * (ENNReal.ofReal C₄ *
          (ENNReal.ofReal C₃ * c2HolderNorm σ (halfSpace i) w))) := by
          gcongr
      _ ≤ ENNReal.ofReal C₆ * (ENNReal.ofReal C₅ * (ENNReal.ofReal C₄ *
          (ENNReal.ofReal C₃ * (ENNReal.ofReal C₂ * c2HolderNorm σ S (u ∘ Ψ))))) := by
          gcongr
      _ ≤ ENNReal.ofReal C₆ * (ENNReal.ofReal C₅ * (ENNReal.ofReal C₄ *
          (ENNReal.ofReal C₃ * (ENNReal.ofReal C₂ * (ENNReal.ofReal C₁ *
            c2HolderNorm σ U u))))) := by
          gcongr
      _ = ENNReal.ofReal (C₆ * C₅ * C₄ * C₃ * C₂ * C₁) * c2HolderNorm σ U u := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul hC₆.le]
          ring

end LatticeProb.Elliptic.HolderExtension
