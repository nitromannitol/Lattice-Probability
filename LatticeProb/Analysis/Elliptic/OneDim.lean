import LatticeProb.Analysis.Elliptic.OneDimODE

/-!
# One-dimensional Dirichlet estimates

Restriction to the unique coordinate identifies the coordinate Laplacian with the scalar
second derivative. Scalar interval estimates give sharp supremum bounds and a uniform
Schauder estimate for classical one-dimensional Dirichlet solutions.
-/

namespace LatticeProb.Elliptic

open Set Filter
open scoped Topology ENNReal

noncomputable section

/-- On the one-coordinate carrier the coordinate Laplacian is the scalar second derivative. -/
theorem laplacian_one_dim (u : (Fin 1 → ℝ) → ℝ) (t : ℝ) :
    laplacian u (fun _ => t) = deriv (deriv (fun s : ℝ => u (fun _ => s))) t := by
  let e : (Fin 1 → ℝ) ≃L[ℝ] ℝ := ContinuousLinearEquiv.piUnique ℝ (fun _ => ℝ)
  have h := e.symm.iteratedFDerivWithin_comp_right u uniqueDiffOn_univ
    (x := t) (mem_univ _) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h
  have hscalar : deriv (deriv (u ∘ e.symm)) t =
      iteratedFDeriv ℝ 2 (u ∘ e.symm) t (fun _ => 1) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      (iteratedDeriv_eq_iteratedFDeriv (n := 2) (f := u ∘ e.symm) (x := t))
  rw [h] at hscalar
  have hvec : (fun _ : Fin 2 => e.symm 1) =
      ![Pi.single (0 : Fin 1) (1 : ℝ), Pi.single (0 : Fin 1) (1 : ℝ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at hscalar
  change deriv (deriv (u ∘ e.symm)) t =
    iteratedFDeriv ℝ 2 u (e.symm t) (fun _ => e.symm 1) at hscalar
  rw [hvec] at hscalar
  have he : (⇑e.symm : ℝ → (Fin 1 → ℝ)) = fun s _ => s := by
    ext s i
    fin_cases i
    rfl
  rw [he] at hscalar
  simpa only [laplacian, Fin.sum_univ_one, secondPartial, Function.comp_def]
    using hscalar.symm

/-- The one-dimensional classical Dirichlet solution satisfies the sharp supremum estimate.
Only finiteness of the interior supremum of the datum is needed for this estimate. -/
theorem supNorm_le_one_dim_dirichlet {α β μ a : ℝ}
    {f u : (Fin 1 → ℝ) → ℝ} (hαβ : α < β) (hμ : 0 ≤ μ) (ha : 0 < a)
    (hf : supNorm {x | α < x 0 ∧ x 0 < β} f < ⊤)
    (hu : IsClassicalDirichletSolution {x | α < x 0 ∧ x 0 < β} μ a f u) :
    supNorm {x | α < x 0 ∧ x 0 < β} u ≤
      ENNReal.ofReal ((β - α) ^ 2 / (8 * a)) *
        supNorm {x | α < x 0 ∧ x 0 < β} f := by
  let U : Set (Fin 1 → ℝ) := {x | α < x 0 ∧ x 0 < β}
  let e : (Fin 1 → ℝ) ≃L[ℝ] ℝ := ContinuousLinearEquiv.piUnique ℝ (fun _ => ℝ)
  let v : ℝ → ℝ := fun t => u (fun _ => t)
  have hclosure : closure U = e ⁻¹' Icc α β := by
    change closure (e.toHomeomorph ⁻¹' Ioo α β) = e.toHomeomorph ⁻¹' Icc α β
    rw [← e.toHomeomorph.preimage_closure, closure_Ioo hαβ.ne]
  have hfrontier : frontier U = e ⁻¹' {α, β} := by
    change frontier (e.toHomeomorph ⁻¹' Ioo α β) = e.toHomeomorph ⁻¹' {α, β}
    rw [← e.toHomeomorph.preimage_frontier, frontier_Ioo hαβ]
  have hv : ContinuousOn v (Icc α β) := by
    apply hu.2.1.comp (show Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) by
      fun_prop).continuousOn
    intro t ht
    rw [hclosure]
    exact ht
  have hc : ContDiffOn ℝ 2 v (Ioo α β) :=
    hu.1.comp (show ContDiff ℝ 2 (fun t : ℝ => (fun _ : Fin 1 => t)) by
      fun_prop).contDiffOn (fun _ ht => ht)
  have hleft : v α = 0 := hu.2.2.1 (fun _ => α) (by
    rw [hfrontier]
    exact Or.inl rfl)
  have hright : v β = 0 := hu.2.2.1 (fun _ => β) (by
    rw [hfrontier]
    exact Or.inr rfl)
  have hode (t : ℝ) (ht : t ∈ Ioo α β) :
      |μ * v t - a * deriv (deriv v) t| ≤ (supNorm U f).toReal := by
    rw [← laplacian_one_dim]
    exact (hu.2.2.2 (fun _ => t) ht) ▸ abs_le_supNorm_toReal hf ht
  have hb := abs_le_interval_barrier hαβ hμ ha ENNReal.toReal_nonneg
    hv hc hleft hright hode
  have hpos : 0 ≤ (β - α) ^ 2 / (8 * a) := div_nonneg (sq_nonneg _) (by positivity)
  have hbound : supNorm U u ≤
      ENNReal.ofReal (((β - α) ^ 2 / (8 * a)) * (supNorm U f).toReal) := by
    refine iSup_le fun x => iSup_le fun hx => ENNReal.ofReal_le_ofReal ?_
    have hxcoord : x = fun _ => x 0 := by
      ext i
      fin_cases i
      rfl
    rw [hxcoord]
    exact hb (x 0) (Ioo_subset_Icc_self hx)
  rw [ENNReal.ofReal_mul hpos, ENNReal.ofReal_toReal hf.ne] at hbound
  exact hbound

/-- Finite Hölder data on the closed interval imply the requested sharp supremum estimate. -/
theorem supNorm_le_one_dim_dirichlet_of_holder {α β σ μ a : ℝ}
    {f u : (Fin 1 → ℝ) → ℝ} (hμ : 0 ≤ μ) (ha : 0 < a)
    (hf : c0HolderNorm σ (closure {x | α < x 0 ∧ x 0 < β}) f < ⊤)
    (hu : IsClassicalDirichletSolution {x | α < x 0 ∧ x 0 < β} μ a f u) :
    supNorm {x | α < x 0 ∧ x 0 < β} u ≤
      ENNReal.ofReal ((β - α) ^ 2 / (8 * a)) *
        supNorm {x | α < x 0 ∧ x 0 < β} f := by
  by_cases hαβ : α < β
  · apply supNorm_le_one_dim_dirichlet hαβ hμ ha ?_ hu
    apply lt_of_le_of_lt (b := supNorm (closure {x | α < x 0 ∧ x 0 < β}) f)
    · refine iSup_le fun x => iSup_le fun hx => ?_
      exact le_iSup_of_le x (le_iSup_of_le (subset_closure hx) le_rfl)
    · exact lt_of_le_of_lt le_self_add hf
  · have hempty : {x : Fin 1 → ℝ | α < x 0 ∧ x 0 < β} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      exact fun x hx => hαβ (hx.1.trans hx.2)
    simp [hempty, supNorm]

/-- Restriction to the unique coordinate identifies the first partial with a scalar derivative. -/
theorem partialDeriv_one_dim {u : (Fin 1 → ℝ) → ℝ} {t : ℝ}
    (hu : DifferentiableAt ℝ u (fun _ => t)) :
    partialDeriv 0 u (fun _ => t) = deriv (fun s : ℝ => u (fun _ => s)) t := by
  have hid : HasDerivAt (fun s : ℝ => (fun _ : Fin 1 => s)) (fun _ => 1) t :=
    hasDerivAt_pi.mpr (fun _ => hasDerivAt_id t)
  have h := (HasFDerivAt.comp_hasDerivAt t hu.hasFDerivAt hid).deriv
  have he : (fun _ : Fin 1 => (1 : ℝ)) = Pi.single 0 1 := by
    ext i
    fin_cases i
    rfl
  simpa only [Function.comp_def, he, partialDeriv] using h.symm

/-- The Euclidean distance on the one-coordinate carrier is the absolute coordinate distance. -/
theorem radius_sub_one_dim (x y : Fin 1 → ℝ) :
    LatticeProb.Euclidean.Lattice.radius (x - y) = |x 0 - y 0| := by
  simp only [LatticeProb.Euclidean.Lattice.radius, Fin.sum_univ_one, Pi.sub_apply,
    Real.sqrt_sq_eq_abs]

/-- A real uniform bound controls the extended supremum norm. -/
theorem supNorm_le_of_abs_le {S : Set (Fin 1 → ℝ)} {g : (Fin 1 → ℝ) → ℝ}
    {B : ℝ} (hg : ∀ x ∈ S, |g x| ≤ B) : supNorm S g ≤ ENNReal.ofReal B := by
  exact iSup_le fun x => iSup_le fun hx => ENNReal.ofReal_le_ofReal (hg x hx)

/-- A real increment bound controls the extended Euclidean Hölder seminorm. -/
theorem holderSeminorm_le_of_increment {S : Set (Fin 1 → ℝ)}
    {g : (Fin 1 → ℝ) → ℝ} {σ B : ℝ}
    (hg : ∀ x ∈ S, ∀ y ∈ S, |g x - g y| ≤ B * |x 0 - y 0| ^ σ) :
    holderSeminorm σ S g ≤ ENNReal.ofReal B := by
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy =>
    iSup_le fun hxy => ENNReal.ofReal_le_ofReal ?_
  rw [radius_sub_one_dim]
  have hcoord : x 0 ≠ y 0 := by
    intro he
    apply hxy
    ext i
    fin_cases i
    exact he
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr hcoord)) σ)).mpr
    (hg x hx y hy)

/-- Uniform ellipticity and bounded mass give a uniform one-dimensional Schauder estimate. -/
theorem c2HolderNorm_le_one_dim_dirichlet {α β σ Λ : ℝ} (hαβ : α < β) (hσ : 0 < σ)
    (hσ1 : σ < 1) (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ a : ℝ) (f u : (Fin 1 → ℝ) → ℝ), Λ⁻¹ ≤ a → a ≤ Λ →
      0 ≤ μ → μ ≤ Λ →
      c0HolderNorm σ (closure {x | α < x 0 ∧ x 0 < β}) f < ⊤ →
      IsClassicalDirichletSolution {x | α < x 0 ∧ x 0 < β} μ a f u →
      c2HolderNorm σ {x | α < x 0 ∧ x 0 < β} u ≤
        ENNReal.ofReal C * c0HolderNorm σ (closure {x | α < x 0 ∧ x 0 < β}) f := by
  let L := β - α
  let B := L ^ 2 * Λ
  let K := (Λ * B + 1) * Λ
  let D := L * K
  let H := (Λ * (D * (L + 1)) + 1) * Λ
  have hL : 0 < L := sub_pos.mpr hαβ
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hB : 0 ≤ B := mul_nonneg (sq_nonneg _) hΛpos.le
  have hK : 0 < K := mul_pos (by positivity) hΛpos
  have hD : 0 ≤ D := mul_nonneg hL.le hK.le
  have hH : 0 < H := mul_pos (by positivity) hΛpos
  refine ⟨B + D + K + H, by positivity, ?_⟩
  intro μ a f u ha _ hμ hμΛ hf hu
  have hapos : 0 < a := lt_of_lt_of_le (inv_pos.mpr hΛpos) ha
  have hinv : a⁻¹ ≤ Λ := (inv_le_comm₀ hapos hΛpos).mpr ha
  let U : Set (Fin 1 → ℝ) := {x | α < x 0 ∧ x 0 < β}
  let N := c0HolderNorm σ (closure U) f
  let M := N.toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hsup : (supNorm (closure U) f).toReal ≤ M :=
    ENNReal.toReal_mono hf.ne le_self_add
  have hhold : (holderSeminorm σ (closure U) f).toReal ≤ M :=
    ENNReal.toReal_mono hf.ne le_add_self
  let v : ℝ → ℝ := fun t => u (fun _ => t)
  let e : (Fin 1 → ℝ) ≃L[ℝ] ℝ := ContinuousLinearEquiv.piUnique ℝ (fun _ => ℝ)
  have hclosure : closure U = e ⁻¹' Icc α β := by
    change closure (e.toHomeomorph ⁻¹' Ioo α β) = e.toHomeomorph ⁻¹' Icc α β
    rw [← e.toHomeomorph.preimage_closure, closure_Ioo hαβ.ne]
  have hfrontier : frontier U = e ⁻¹' {α, β} := by
    change frontier (e.toHomeomorph ⁻¹' Ioo α β) = e.toHomeomorph ⁻¹' {α, β}
    rw [← e.toHomeomorph.preimage_frontier, frontier_Ioo hαβ]
  have hv : ContinuousOn v (Icc α β) := by
    apply hu.2.1.comp (show Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) by
      fun_prop).continuousOn
    intro t ht
    rw [hclosure]
    exact ht
  have hc : ContDiffOn ℝ 2 v (Ioo α β) :=
    hu.1.comp (show ContDiff ℝ 2 (fun t : ℝ => (fun _ : Fin 1 => t)) by
      fun_prop).contDiffOn (fun _ ht => ht)
  have hd (t : ℝ) (ht : t ∈ Ioo α β) :=
    (hc.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by norm_num)
  have hcd : ContDiffOn ℝ 1 (deriv v) (Ioo α β) :=
    hc.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hdd (t : ℝ) (ht : t ∈ Ioo α β) :=
    (hcd.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by norm_num)
  have hleft : v α = 0 := hu.2.2.1 (fun _ => α) (by
    rw [hfrontier]
    exact Or.inl rfl)
  have hright : v β = 0 := hu.2.2.1 (fun _ => β) (by
    rw [hfrontier]
    exact Or.inr rfl)
  have hode (t : ℝ) (ht : t ∈ Ioo α β) :
      μ * v t - a * deriv (deriv v) t = f (fun _ => t) := by
    rw [← laplacian_one_dim]
    exact hu.2.2.2 (fun _ => t) ht
  have hfbound (t : ℝ) (ht : t ∈ Ioo α β) : |f (fun _ => t)| ≤ M :=
    (abs_le_supNorm_toReal_of_c0HolderNorm_lt_top hf (subset_closure ht)).trans hsup
  have hbar := abs_le_interval_barrier hαβ hμ hapos hM hv hc hleft hright
    (fun t ht => (hode t ht) ▸ hfbound t ht)
  have hcoeff : (β - α) ^ 2 / (8 * a) ≤ B := by
    calc
      (β - α) ^ 2 / (8 * a) = L ^ 2 * a⁻¹ / 8 := by
        dsimp [L]
        field_simp
      _ ≤ L ^ 2 * Λ / 8 := by gcongr
      _ ≤ B := by dsimp [B]; linarith [mul_nonneg (sq_nonneg L) hΛpos.le]
  have hvbound (t : ℝ) (ht : t ∈ Ioo α β) : |v t| ≤ B * M :=
    (hbar t (Ioo_subset_Icc_self ht)).trans (mul_le_mul_of_nonneg_right hcoeff hM)
  have hsecond (t : ℝ) (ht : t ∈ Ioo α β) : |deriv (deriv v) t| ≤ K * M := by
    apply (abs_second_deriv_le_of_ode (f := fun t => f (fun _ => t)) hμ hapos
      (hvbound t ht) (hfbound t ht) (hode t ht)).trans
    calc
      (μ * (B * M) + M) / a = (μ * B + 1) * a⁻¹ * M := by ring
      _ ≤ (Λ * B + 1) * Λ * M := by gcongr
      _ = K * M := rfl
  have hfirst (t : ℝ) (ht : t ∈ Ioo α β) : |deriv v t| ≤ D * M := by
    have hh := abs_deriv_le_of_dirichlet hαβ (mul_nonneg hK.le hM) hv
      (hleft.trans hright.symm) hdd hsecond t ht
    dsimp [D]
    exact hh.trans_eq (by dsimp [L]; ring)
  have hincrement (x y : ℝ) (hx : x ∈ Ioo α β) (hy : y ∈ Ioo α β) :
      |deriv (deriv v) x - deriv (deriv v) y| ≤ H * M * |x - y| ^ σ := by
    have huinc := abs_sub_le_rpow_of_deriv_bound hαβ hσ hσ1
      (mul_nonneg hD hM) hd hfirst hx hy
    have hfinc := abs_sub_le_holderSeminorm_toReal hf
      (subset_closure (show (fun _ : Fin 1 => x) ∈ U from hx))
      (subset_closure (show (fun _ : Fin 1 => y) ∈ U from hy))
    rw [radius_sub_one_dim] at hfinc
    have hfinc' : |f (fun _ => x) - f (fun _ => y)| ≤ M * |x - y| ^ σ :=
      hfinc.trans (mul_le_mul_of_nonneg_right hhold (Real.rpow_nonneg (abs_nonneg _) _))
    have hh := abs_sub_second_deriv_le_of_ode (f := fun t => f (fun _ => t))
      hμ hapos huinc hfinc'
      (hode x hx) (hode y hy)
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (abs_nonneg _) _)
    calc
      (μ * (D * M * (β - α + 1)) + M) / a =
          (μ * (D * (L + 1)) + 1) * a⁻¹ * M := by dsimp [L]; ring
      _ ≤ (Λ * (D * (L + 1)) + 1) * Λ * M := by gcongr
      _ = H * M := rfl
  have hcoord (x : Fin 1 → ℝ) : x = fun _ => x 0 := by
    ext i
    fin_cases i
    rfl
  have hp (x : Fin 1 → ℝ) (hx : x ∈ U) : partialDeriv 0 u x = deriv v (x 0) := by
    rw [hcoord x]
    apply partialDeriv_one_dim
    rw [← hcoord x]
    have hopen : IsOpen U :=
      (isOpen_lt continuous_const (continuous_apply 0)).inter
        (isOpen_lt (continuous_apply 0) continuous_const)
    exact (hu.1.contDiffAt (hopen.mem_nhds hx)).differentiableAt (by norm_num)
  have hpp (x : Fin 1 → ℝ) : secondPartial 0 0 u x = deriv (deriv v) (x 0) := by
    rw [hcoord x]
    simpa only [laplacian, Fin.sum_univ_one] using laplacian_one_dim u (x 0)
  have h0 : supNorm U u ≤ ENNReal.ofReal (B * M) := supNorm_le_of_abs_le fun x hx => by
    rw [hcoord x]
    exact hvbound (x 0) hx
  have h1 : supNorm U (partialDeriv 0 u) ≤ ENNReal.ofReal (D * M) :=
    supNorm_le_of_abs_le fun x hx => by rw [hp x hx]; exact hfirst (x 0) hx
  have h2 : supNorm U (secondPartial 0 0 u) ≤ ENNReal.ofReal (K * M) :=
    supNorm_le_of_abs_le fun x hx => by rw [hpp x]; exact hsecond (x 0) hx
  have hh : holderSeminorm σ U (secondPartial 0 0 u) ≤ ENNReal.ofReal (H * M) :=
    holderSeminorm_le_of_increment fun x hx y hy => by
      rw [hpp x, hpp y]
      exact hincrement (x 0) (y 0) hx hy
  change c2HolderNorm σ U u ≤ ENNReal.ofReal (B + D + K + H) * N
  simp only [c2HolderNorm, Fin.sum_univ_one]
  calc
    _ ≤ ENNReal.ofReal (B * M) + ENNReal.ofReal (D * M) +
        ENNReal.ofReal (K * M) + ENNReal.ofReal (H * M) :=
      add_le_add (add_le_add (add_le_add h0 h1) h2) hh
    _ = ENNReal.ofReal ((B + D + K + H) * M) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hB hM) (mul_nonneg hD hM),
        ← ENNReal.ofReal_add (by positivity) (mul_nonneg hK.le hM),
        ← ENNReal.ofReal_add (by positivity) (mul_nonneg hH.le hM)]
      congr 1
      ring
    _ = ENNReal.ofReal (B + D + K + H) * N := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hf.ne]

end

end LatticeProb.Elliptic
