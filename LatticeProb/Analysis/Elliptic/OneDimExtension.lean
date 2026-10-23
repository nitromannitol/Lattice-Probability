import LatticeProb.Analysis.Elliptic.OneDim

/-!
# Extension from a real interval

Endpoint limits of a uniformly continuous function give a continuous clamped extension.
Twice integrating a continuous extension of the second derivative preserves the original
function when its value and first derivative are fixed at an interior point.
-/

namespace LatticeProb.Elliptic

open Set Filter
open scoped Topology ENNReal NNReal ContDiff

noncomputable section

/-- Uniform continuity on an interval supplies a continuous extension to its closure,
preserving any uniform absolute bound. -/
theorem interval_continuous_extension {α β N : ℝ} {g : ℝ → ℝ}
    (hαβ : α < β) (hg : UniformContinuousOn g (Ioo α β))
    (hN : ∀ t ∈ Ioo α β, |g t| ≤ N) :
    ∃ G : ℝ → ℝ, Continuous G ∧ EqOn G g (Ioo α β) ∧ ∀ t, |G t| ≤ N := by
  have hlim : ∀ x ∈ closure (Ioo α β), ∃ y, Tendsto g (𝓝[Ioo α β] x) (𝓝 y) := by
    intro x hx
    haveI : NeBot (𝓝[Ioo α β] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
    haveI : NeBot (𝓝 x ⊓ 𝓟 (Ioo α β)) :=
      mem_closure_iff_nhdsWithin_neBot.mp hx
    have hc : Cauchy (𝓝[Ioo α β] x) := cauchy_nhds.mono nhdsWithin_le_nhds
    exact cauchy_map_iff_exists_tendsto.mp (hc.map_of_le hg inf_le_right)
  have hcont := continuousOn_extendFrom (Subset.refl (closure (Ioo α β))) hlim
  have heq := extendFrom_extends hg.continuousOn
  have hbound : ∀ x ∈ closure (Ioo α β), |extendFrom (Ioo α β) g x| ≤ N := by
    apply le_on_closure
    · intro x hx
      rw [heq x hx]
      exact hN x hx
    · exact hcont.abs
    · exact continuousOn_const
  let p : ℝ → ℝ := fun t => max α (min β t)
  have hp (t : ℝ) : p t ∈ closure (Ioo α β) := by
    rw [closure_Ioo hαβ.ne]
    exact ⟨le_max_left _ _, max_le hαβ.le (min_le_left _ _)⟩
  refine ⟨fun t => extendFrom (Ioo α β) g (p t), ?_, ?_, fun t => hbound _ (hp t)⟩
  · exact hcont.comp_continuous (by fun_prop) hp
  · intro t ht
    have hpt : p t = t := by
      dsimp [p]
      rw [min_eq_right ht.2.le, max_eq_right ht.1.le]
    change extendFrom (Ioo α β) g (p t) = g t
    rw [hpt]
    exact heq t ht

/-- Real increment estimates with positive exponent imply uniform continuity. -/
theorem uniformContinuousOn_of_holder_bound {σ H : ℝ} {S : Set ℝ} {g : ℝ → ℝ}
    (hσ : 0 < σ) (hH : 0 ≤ H)
    (hg : ∀ x ∈ S, ∀ y ∈ S, |g x - g y| ≤ H * |x - y| ^ σ) :
    UniformContinuousOn g S := by
  have hh : HolderOnWith (NNReal.mk H hH) (NNReal.mk σ hσ.le) g S := by
    intro x hx y hy
    have h := ENNReal.ofReal_le_ofReal (hg x hx y hy)
    simpa only [edist_dist, Real.dist_eq, ENNReal.ofReal_mul hH,
      ← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hσ.le,
      ENNReal.ofReal_eq_coe_nnreal hH, NNReal.coe_mk] using h
  exact hh.uniformContinuousOn hσ

/-- Clamping the endpoint extension preserves the Hölder constant and uniform bound. -/
theorem interval_holder_extension {α β σ H N : ℝ} {g : ℝ → ℝ}
    (hαβ : α < β) (hσ : 0 < σ) (hH : 0 ≤ H)
    (hh : ∀ x ∈ Ioo α β, ∀ y ∈ Ioo α β,
      |g x - g y| ≤ H * |x - y| ^ σ)
    (hN : ∀ t ∈ Ioo α β, |g t| ≤ N) :
    ∃ G : ℝ → ℝ, Continuous G ∧ EqOn G g (Ioo α β) ∧
      (∀ t, |G t| ≤ N) ∧ ∀ x y, |G x - G y| ≤ H * |x - y| ^ σ := by
  obtain ⟨G, hG, hGeq, hGN⟩ := interval_continuous_extension hαβ
    (uniformContinuousOn_of_holder_bound hσ hH hh) hN
  have hclosure : closure (Ioo α β) = Icc α β := closure_Ioo hαβ.ne
  have hleft (y : ℝ) (hy : y ∈ Ioo α β) :
      ∀ x ∈ closure (Ioo α β), |G x - G y| ≤ H * |x - y| ^ σ := by
    apply le_on_closure
    · intro x hx
      rw [hGeq hx, hGeq hy]
      exact hh x hx y hy
    · exact (hG.sub continuous_const).abs.continuousOn
    · exact (continuous_const.mul
        ((continuous_id.sub continuous_const).abs.rpow_const
          (fun _ => Or.inr hσ.le))).continuousOn
  have hboth (x : ℝ) (hx : x ∈ closure (Ioo α β)) :
      ∀ y ∈ closure (Ioo α β), |G x - G y| ≤ H * |x - y| ^ σ := by
    apply le_on_closure
    · intro y hy
      exact hleft y hy x hx
    · exact (continuous_const.sub hG).abs.continuousOn
    · exact (continuous_const.mul
        ((continuous_const.sub continuous_id).abs.rpow_const
          (fun _ => Or.inr hσ.le))).continuousOn
  let p : ℝ → ℝ := fun t => max α (min β t)
  have hp (t : ℝ) : p t ∈ closure (Ioo α β) := by
    rw [hclosure]
    exact ⟨le_max_left _ _, max_le hαβ.le (min_le_left _ _)⟩
  have hpLip : LipschitzWith 1 p := (LipschitzWith.id.const_min β).const_max α
  refine ⟨fun t => G (p t), hG.comp hpLip.continuous, ?_, fun t => hGN _, ?_⟩
  · intro t ht
    have hpt : p t = t := by
      dsimp [p]
      rw [min_eq_right ht.2.le, max_eq_right ht.1.le]
    change G (p t) = g t
    rw [hpt]
    exact hGeq ht
  · intro x y
    apply (hboth (p x) (hp x) (p y) (hp y)).trans
    apply mul_le_mul_of_nonneg_left _ hH
    apply Real.rpow_le_rpow (abs_nonneg _) _ hσ.le
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hpLip.dist_le_mul x y

/-- The primitive based at `c` of a continuous function has that function as derivative. -/
theorem hasDerivAt_interval_primitive {g : ℝ → ℝ} (hg : Continuous g) (c t : ℝ) :
    HasDerivAt (fun x => ∫ s in c..x, g s) (g t) t :=
  intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

/-- Twice integrating a continuous function produces a global `C²` function with the
prescribed second derivative and prescribed value and slope at the base point. -/
theorem exists_contDiff_two_of_continuous {g : ℝ → ℝ} (hg : Continuous g)
    (c a b : ℝ) :
    ∃ W : ℝ → ℝ, ContDiff ℝ 2 W ∧ W c = a ∧ deriv W c = b ∧
      ∀ t, deriv (deriv W) t = g t := by
  let P : ℝ → ℝ := fun t => ∫ s in c..t, g s
  have hP (t : ℝ) : HasDerivAt P (g t) t := hasDerivAt_interval_primitive hg c t
  have hPd : Differentiable ℝ P := fun t => (hP t).differentiableAt
  have hPc : Continuous P := hPd.continuous
  let W : ℝ → ℝ := fun t => a + b * (t - c) + ∫ s in c..t, P s
  have hW (t : ℝ) : HasDerivAt W (b + P t) t := by
    apply (((hasDerivAt_const t a).add
      (((hasDerivAt_id t).sub_const c).const_mul b)).add
      (hasDerivAt_interval_primitive hPc c t)).congr_deriv
    ring
  have hdW : deriv W = fun t => b + P t := funext fun t => (hW t).deriv
  have hddW (t : ℝ) : HasDerivAt (deriv W) (g t) t := by
    rw [hdW]
    exact (hP t).const_add b
  refine ⟨W, ?_, ?_, ?_, fun t => (hddW t).deriv⟩
  · rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
    refine ⟨fun t => (hW t).differentiableAt, by norm_num, ?_⟩
    rw [contDiff_one_iff_deriv]
    refine ⟨fun t => (hddW t).differentiableAt, ?_⟩
    convert hg using 1
    ext t
    exact (hddW t).deriv
  · simp only [W, sub_self, mul_zero, add_zero, intervalIntegral.integral_same]
  · rw [hdW]
    simp only [P, intervalIntegral.integral_same, add_zero]

/-- Two twice differentiable functions on an open interval agree if their second
 derivatives agree and they have the same value and slope at one interior point. -/
theorem eqOn_of_second_deriv_eq {α β c : ℝ} {f g : ℝ → ℝ}
    (hc : c ∈ Ioo α β) (hf : ContDiffOn ℝ 2 f (Ioo α β))
    (hg : ContDiffOn ℝ 2 g (Ioo α β))
    (hsecond : EqOn (deriv (deriv f)) (deriv (deriv g)) (Ioo α β))
    (hvalue : f c = g c) (hslope : deriv f c = deriv g c) : EqOn f g (Ioo α β) := by
  have hf' := hf.deriv_of_isOpen isOpen_Ioo (show 1 + 1 ≤ (2 : ℕ∞ω) from le_rfl)
  have hg' := hg.deriv_of_isOpen isOpen_Ioo (show 1 + 1 ≤ (2 : ℕ∞ω) from le_rfl)
  have hfirst := isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo α β).isPreconnected
    (hf'.differentiableOn (by norm_num)) (hg'.differentiableOn (by norm_num))
    hsecond hc hslope
  exact isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo α β).isPreconnected
    (hf.differentiableOn (by norm_num)) (hg.differentiableOn (by norm_num))
    hfirst hc hvalue

/-- A global bound on the second derivative gives explicit linear and quadratic growth
bounds relative to any base point. -/
theorem bounds_of_second_deriv_bound {W : ℝ → ℝ} {N c : ℝ}
    (hW : ContDiff ℝ 2 W) (hN : 0 ≤ N)
    (hsecond : ∀ t, |deriv (deriv W) t| ≤ N) :
    (∀ t, |deriv W t| ≤ |deriv W c| + N * |t - c|) ∧
      ∀ t, |W t| ≤ |W c| + (|deriv W c| + N * |t - c|) * |t - c| := by
  have hW' : ContDiff ℝ 1 (deriv W) := hW.deriv'
  have hfirst (t : ℝ) : |deriv W t| ≤ |deriv W c| + N * |t - c| := by
    have hh := convex_univ.norm_image_sub_le_of_norm_deriv_le
      (fun x _ => hW'.differentiable (by norm_num) x)
      (fun x _ => by simpa only [Real.norm_eq_abs] using hsecond x)
      (mem_univ c) (mem_univ t)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hh
    calc
      |deriv W t| ≤ |deriv W t - deriv W c| + |deriv W c| := by
        simpa only [sub_add_cancel] using
          abs_add_le (deriv W t - deriv W c) (deriv W c)
      _ ≤ |deriv W c| + N * |t - c| := by linarith
  refine ⟨hfirst, fun t => ?_⟩
  have hh := (convex_uIcc c t).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hW.differentiable (by norm_num) x)
    (fun x hx => show ‖deriv W x‖ ≤ |deriv W c| + N * |t - c| from
      (hfirst x).trans (add_le_add_right
        (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hx) hN) _))
    (left_mem_uIcc : c ∈ uIcc c t) (right_mem_uIcc : t ∈ uIcc c t)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hh
  calc
    |W t| ≤ |W t - W c| + |W c| := by
      simpa only [sub_add_cancel] using abs_add_le (W t - W c) (W c)
    _ ≤ |W c| + (|deriv W c| + N * |t - c|) * |t - c| := by linarith

/-- A uniformly continuous bounded second derivative on an interval admits a global
`C²` extension agreeing on the interval, with an unchanged bound on its second derivative. -/
theorem scalar_C2_extension_of_uniformContinuous {α β N : ℝ} {w : ℝ → ℝ}
    (hαβ : α < β) (hw : ContDiffOn ℝ 2 w (Ioo α β))
    (hu : UniformContinuousOn (deriv (deriv w)) (Ioo α β))
    (hN : ∀ t ∈ Ioo α β, |deriv (deriv w) t| ≤ N) :
    ∃ W : ℝ → ℝ, ContDiff ℝ 2 W ∧ EqOn W w (Ioo α β) ∧
      (∀ t, |deriv (deriv W) t| ≤ N) ∧
      (∀ t, |deriv W t| ≤ |deriv w ((α + β) / 2)| + N * |t - (α + β) / 2|) ∧
      ∀ t, |W t| ≤ |w ((α + β) / 2)| +
        (|deriv w ((α + β) / 2)| + N * |t - (α + β) / 2|) *
          |t - (α + β) / 2| := by
  obtain ⟨G, hG, hGeq, hGN⟩ := interval_continuous_extension hαβ hu hN
  let c := (α + β) / 2
  have hc : c ∈ Ioo α β := by dsimp [c]; constructor <;> linarith
  obtain ⟨W, hW, hWc, hW'c, hW''⟩ :=
    exists_contDiff_two_of_continuous hG c (w c) (deriv w c)
  have heq : EqOn W w (Ioo α β) := eqOn_of_second_deriv_eq hc hW.contDiffOn hw
    (fun t ht => (hW'' t).trans (hGeq ht)) hWc hW'c
  have hbound (t : ℝ) : |deriv (deriv W) t| ≤ N := by rw [hW'' t]; exact hGN t
  have hnonneg : 0 ≤ N := (abs_nonneg _).trans (hN c hc)
  obtain ⟨hfirst, hvalue⟩ := bounds_of_second_deriv_bound (c := c) hW hnonneg hbound
  refine ⟨W, hW, heq, hbound, ?_, ?_⟩
  · simpa only [hW'c] using hfirst
  · simpa only [hWc, hW'c] using hvalue

/-- Finite interior `C^{2,σ}` norm gives a global `C²` extension on the one-coordinate
carrier. Its second derivative preserves the supremum and Hölder bounds; its value and
slope have explicit quadratic and linear growth bounds. -/
theorem one_dim_C2_extension_of_holder {α β σ : ℝ} (hαβ : α < β) (hσ : 0 < σ)
    {u : (Fin 1 → ℝ) → ℝ}
    (hu : ContDiffOn ℝ 2 u {x | α < x 0 ∧ x 0 < β})
    (hnorm : c2HolderNorm σ {x | α < x 0 ∧ x 0 < β} u < ⊤) :
    ∃ v : (Fin 1 → ℝ) → ℝ, ContDiff ℝ 2 v ∧
      EqOn v u {x | α < x 0 ∧ x 0 < β} ∧
      (∀ x, |secondPartial 0 0 v x| ≤
        (supNorm {x | α < x 0 ∧ x 0 < β} (secondPartial 0 0 u)).toReal) ∧
      (∀ x y, |secondPartial 0 0 v x - secondPartial 0 0 v y| ≤
        (holderSeminorm σ {x | α < x 0 ∧ x 0 < β}
          (secondPartial 0 0 u)).toReal *
            LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ) ∧
      (∀ x, |partialDeriv 0 v x| ≤
        |partialDeriv 0 u (fun _ => (α + β) / 2)| +
          (supNorm {x | α < x 0 ∧ x 0 < β} (secondPartial 0 0 u)).toReal *
            |x 0 - (α + β) / 2|) ∧
      ∀ x, |v x| ≤ |u (fun _ => (α + β) / 2)| +
        (|partialDeriv 0 u (fun _ => (α + β) / 2)| +
          (supNorm {x | α < x 0 ∧ x 0 < β} (secondPartial 0 0 u)).toReal *
            |x 0 - (α + β) / 2|) * |x 0 - (α + β) / 2| := by
  let I : Set (Fin 1 → ℝ) := {x | α < x 0 ∧ x 0 < β}
  let w : ℝ → ℝ := fun t => u (fun _ => t)
  let q := secondPartial (0 : Fin 1) 0 u
  have hq : c0HolderNorm σ I q < ⊤ := by
    apply lt_of_le_of_lt (b := c2HolderNorm σ I u) _ hnorm
    simp only [c0HolderNorm, c2HolderNorm, Fin.sum_univ_one, q]
    exact add_le_add (le_add_left le_rfl : supNorm I q ≤
      supNorm I u + supNorm I (partialDeriv 0 u) + supNorm I q) le_rfl
  have hqN : supNorm I q < ⊤ := lt_of_le_of_lt le_self_add hq
  have hw : ContDiffOn ℝ 2 w (Ioo α β) :=
    hu.comp (show ContDiff ℝ 2 (fun t : ℝ => (fun _ : Fin 1 => t)) by
      fun_prop).contDiffOn (fun _ ht => ht)
  have hsecond (t : ℝ) : deriv (deriv w) t = q (fun _ => t) := by
    simpa only [laplacian, Fin.sum_univ_one, q, w] using (laplacian_one_dim u t).symm
  have hholder (s : ℝ) (hs : s ∈ Ioo α β) (t : ℝ) (ht : t ∈ Ioo α β) :
      |deriv (deriv w) s - deriv (deriv w) t| ≤
        (holderSeminorm σ I q).toReal * |s - t| ^ σ := by
    rw [hsecond s, hsecond t]
    simpa only [radius_sub_one_dim] using abs_sub_le_holderSeminorm_toReal hq hs ht
  have hbound (t : ℝ) (ht : t ∈ Ioo α β) :
      |deriv (deriv w) t| ≤ (supNorm I q).toReal := by
    rw [hsecond]
    exact abs_le_supNorm_toReal hqN ht
  obtain ⟨G, hG, hGeq, hGN, hGH⟩ :=
    interval_holder_extension hαβ hσ ENNReal.toReal_nonneg hholder hbound
  let c := (α + β) / 2
  have hcmem : c ∈ Ioo α β := by dsimp [c]; constructor <;> linarith
  obtain ⟨W, hW, hWc, hW'c, hW''⟩ :=
    exists_contDiff_two_of_continuous hG c (w c) (deriv w c)
  have heq : EqOn W w (Ioo α β) := eqOn_of_second_deriv_eq hcmem hW.contDiffOn hw
    (fun t ht => (hW'' t).trans (hGeq ht)) hWc hW'c
  have hWsecond (t : ℝ) : |deriv (deriv W) t| ≤ (supNorm I q).toReal := by
    rw [hW'' t]
    exact hGN t
  obtain ⟨hWfirst, hWvalue⟩ := bounds_of_second_deriv_bound (c := c) hW
    ENNReal.toReal_nonneg hWsecond
  rw [hWc, hW'c] at hWvalue
  rw [hW'c] at hWfirst
  let v : (Fin 1 → ℝ) → ℝ := fun x => W (x 0)
  have hv : ContDiff ℝ 2 v := hW.comp (by fun_prop)
  have hcoord (x : Fin 1 → ℝ) : (fun _ : Fin 1 => x 0) = x := by
    ext i
    fin_cases i
    rfl
  have hvfirst (x : Fin 1 → ℝ) : partialDeriv 0 v x = deriv W (x 0) := by
    have hh := partialDeriv_one_dim (t := x 0) (hv.differentiable (by norm_num) _)
    simpa only [v, hcoord] using hh
  have hvsecond (x : Fin 1 → ℝ) : secondPartial 0 0 v x = deriv (deriv W) (x 0) := by
    have hh := laplacian_one_dim v (x 0)
    simpa only [laplacian, Fin.sum_univ_one, v, hcoord] using hh
  have hc : (fun _ : Fin 1 => (α + β) / 2) ∈ I := by
    constructor <;> dsimp <;> linarith
  have hslope : partialDeriv 0 u (fun _ => (α + β) / 2) =
      deriv w ((α + β) / 2) :=
    partialDeriv_one_dim ((hu.contDiffAt ((isOpen_lt continuous_const
      (continuous_apply 0)).inter (isOpen_lt (continuous_apply 0) continuous_const)
      |>.mem_nhds hc)).differentiableAt (by norm_num))
  refine ⟨v, hv, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (heq hx).trans (congrArg u (hcoord x))
  · intro x
    rw [hvsecond]
    exact hWsecond _
  · intro x y
    rw [hvsecond, hvsecond, hW'', hW'', radius_sub_one_dim]
    exact hGH _ _
  · intro x
    rw [hvfirst, hslope]
    exact hWfirst _
  · intro x
    rw [hslope]
    exact hWvalue _

end

end LatticeProb.Elliptic
