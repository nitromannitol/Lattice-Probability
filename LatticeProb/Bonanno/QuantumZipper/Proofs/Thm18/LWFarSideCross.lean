/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.LWFarSideCross at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node LWF-5 (side bound): a planar crossing lemma

`lwfSide_crossing`: a path `σ` in the closed upper half-plane from a negative real `u₁` to a
positive real `u₂`, and a path `τ` in the open upper half-plane from a point `p` closer to `0`
than all of `σ` to a point `q` farther from `0` than all of `σ`, must meet.

This is the topological core of the separation step "a crosscut from `(−∞,0)` to `(0,∞)`
separates `0` from `∞` in `ℍ`" used for LW eq. (2) (G. Lawler, B. Werness, *Multi-point Green's
functions for SLE and an estimate of Beffara*, Ann. Probab. 41 (2013), p. 6) and Beffara,
*The dimension of the SLE curves*, Lemma 6 (p. 13).

**Proof (own elementary argument via winding numbers**; the index of a loop is Burckel,
*Classical Analysis in the Complex Plane* (2021), Def. 4.2 / Cor. 4.3, p. 189, implemented in
`CA.Topo.loopDeg`). If the paths do not meet, the loop `Γ = σ · (conj ∘ σ)⁻¹` avoids every point of
the segment `[0, p]` and of `τ`, so its index about `0`, `p` and `q` agree (homotopy invariance,
`loopDeg_homotopy`). About `q` it is `0` (Rouché, `loopDeg_eq_of_norm_sub_lt`). About `0` it is
`−1`: `log ∘ σ` followed by `conj ∘ log ∘ σ` reversed is a continuous logarithm of `Γ` whose
increment is `conj (log u₁) − log u₁ = −2πi`.
-/

noncomputable section

open Complex Set
open scoped ComplexConjugate

namespace QuantumZipper.Thm18Asm.LWFar

open QuantumZipper.CA.Topo

theorem lwfSide_loopDeg_congr {γ δ : C(unitInterval, ℂ)} (e : γ = δ) (hγ : ∀ t, γ t ≠ 0)
    (hδ : ∀ t, δ t ≠ 0) : loopDeg γ hγ = loopDeg δ hδ := by
  subst e; rfl

/-- The index of a loop about a moving centre that never meets the loop is constant. -/
theorem lwfSide_deg_along {a p q : ℂ} (Γ : Path a a) (c : Path p q)
    (hne : ∀ x s, Γ x ≠ c s) (hp : ∀ x, Γ x - p ≠ 0) (hq : ∀ x, Γ x - q ≠ 0) :
    loopDeg ⟨fun x => Γ x - p, by fun_prop⟩ hp = loopDeg ⟨fun x => Γ x - q, by fun_prop⟩ hq := by
  let Hm : C(unitInterval × unitInterval, ℂ) := ⟨fun y => Γ y.1 - c y.2, by fun_prop⟩
  have h0 : ∀ y, Hm y ≠ 0 := fun y => sub_ne_zero.2 (hne y.1 y.2)
  have hc : ∀ s, Hm (0, s) = Hm (1, s) := fun s => by simp [Hm]
  calc _ = loopDeg (slice Hm 0) (fun _ => h0 _) :=
        lwfSide_loopDeg_congr (by ext x; simp [slice, Hm]) _ _
    _ = loopDeg (slice Hm 1) (fun _ => h0 _) := loopDeg_homotopy Hm h0 hc
    _ = _ := lwfSide_loopDeg_congr (by ext x; simp [slice, Hm]) _ _

/-- **Crossing lemma.** A path in `ℍ̄` from `u₁ < 0` to `u₂ > 0` meets every path in `ℍ` from a
point closer to `0` than the whole first path to a point farther than the whole first path. -/
theorem lwfSide_crossing {u₁ u₂ : ℝ} (hu₁ : u₁ < 0) (hu₂ : 0 < u₂)
    (σ : Path (u₁ : ℂ) (u₂ : ℂ)) (hσ : ∀ t, 0 ≤ (σ t).im)
    {p q : ℂ} (τ : Path p q) (hτ : ∀ t, 0 < (τ t).im)
    (hp : ∀ t, ‖p‖ < ‖σ t‖) (hq : ∀ t, ‖σ t‖ < ‖q‖) :
    ∃ t t', σ t = τ t' := by
  by_contra hno
  push Not at hno
  have hσ0 : ∀ t, σ t ≠ 0 := fun t h => by
    have := hp t; rw [h, norm_zero] at this; exact absurd this (not_lt.2 (norm_nonneg _))
  -- the reversed conjugate of `σ`, and the loop `Γ`
  let σc : Path (u₂ : ℂ) (u₁ : ℂ) :=
    { toFun := fun x => conj (σ (unitInterval.symm x))
      continuous_toFun := Complex.continuous_conj.comp (σ.continuous.comp unitInterval.continuous_symm)
      source' := by simp
      target' := by simp }
  let Γ : Path (u₁ : ℂ) (u₁ : ℂ) := σ.trans σc
  have hΓ : ∀ x, ∃ t, Γ x = σ t ∨ Γ x = conj (σ t) := by
    intro x
    simp only [Γ, Path.trans_apply]
    split_ifs
    · exact ⟨_, Or.inl rfl⟩
    · exact ⟨_, Or.inr rfl⟩
  have hΓn : ∀ x, ∃ t, ‖Γ x‖ = ‖σ t‖ := fun x => by
    obtain ⟨t, h | h⟩ := hΓ x
    · exact ⟨t, by rw [h]⟩
    · exact ⟨t, by rw [h, Complex.norm_conj]⟩
  -- the centres `s p`, `s ∈ [0,1]`
  let c₁ : Path (0 : ℂ) p :=
    { toFun := fun s => ((s : ℝ) : ℂ) * p
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  have hne₁ : ∀ x s, Γ x ≠ c₁ s := by
    intro x s h
    obtain ⟨t, ht⟩ := hΓn x
    have h1 : ‖c₁ s‖ ≤ ‖p‖ := by
      show ‖((s : ℝ) : ℂ) * p‖ ≤ ‖p‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.2.1]
      exact mul_le_of_le_one_left (norm_nonneg _) s.2.2
    have := hp t
    rw [← ht, h] at this
    linarith
  have hne₂ : ∀ x s, Γ x ≠ τ s := by
    intro x s h
    obtain ⟨t, h' | h'⟩ := hΓ x
    · exact hno t s (h' ▸ h)
    · have h1 := hτ s
      rw [← h, h', Complex.conj_im] at h1
      linarith [hσ t]
  have hnz0 : ∀ x, Γ x - 0 ≠ 0 := fun x => sub_ne_zero.2 (fun h => hne₁ x 0 (by simpa using h))
  have hnzp : ∀ x, Γ x - p ≠ 0 := fun x => sub_ne_zero.2 (fun h => hne₁ x 1 (by simpa using h))
  have hnzq : ∀ x, Γ x - q ≠ 0 := fun x => sub_ne_zero.2 (fun h => hne₂ x 1 (by simpa using h))
  have hdeg1 := lwfSide_deg_along Γ c₁ hne₁ hnz0 hnzp
  have hdeg2 := lwfSide_deg_along Γ τ hne₂ hnzp hnzq
  -- index about `q` is `0`
  have hq0 : q ≠ 0 := fun h => by
    have := hq 0; rw [h, norm_zero] at this; exact absurd this (not_lt.2 (norm_nonneg _))
  have hdegq : loopDeg ⟨fun x => Γ x - q, by fun_prop⟩ hnzq = 0 := by
    rw [loopDeg_eq_of_norm_sub_lt _ (ContinuousMap.const unitInterval (-q)) hnzq
      (fun _ => neg_ne_zero.2 hq0) (by simp) rfl ?_]
    · exact loopDeg_const (-q) (neg_ne_zero.2 hq0)
    · intro x
      obtain ⟨t, ht⟩ := hΓn x
      simp only [ContinuousMap.coe_mk, ContinuousMap.const_apply, sub_neg_eq_add, sub_add_cancel,
        norm_neg]
      rw [ht]; exact hq t
  -- index about `0` is `-1`, via an explicit continuous logarithm
  have hlogc : Continuous fun s => log (σ s) := by
    rw [continuous_iff_continuousAt]
    intro s
    by_cases hsl : σ s ∈ slitPlane
    · exact (continuousAt_clog hsl).comp σ.continuous.continuousAt
    · rw [mem_slitPlane_iff] at hsl
      push Not at hsl
      have hre : (σ s).re < 0 := by
        rcases hsl.1.lt_or_eq with h | h
        · exact h
        · exact absurd (Complex.ext (by simpa using h) (by simpa using hsl.2)) (hσ0 s)
      have h1 := continuousWithinAt_log_of_re_neg_of_im_zero hre hsl.2
      have h2 : ContinuousWithinAt (fun s => log (σ s)) univ s :=
        h1.comp σ.continuous.continuousWithinAt (fun x _ => hσ x)
      exact (continuousWithinAt_univ _ _).1 h2
  have hlog₂ : conj (log (u₂ : ℂ)) = log (u₂ : ℂ) := by
    rw [← Complex.ofReal_log hu₂.le, Complex.conj_ofReal]
  let ℓ : Path (log (u₁ : ℂ)) (log (u₂ : ℂ)) :=
    { toFun := fun s => log (σ s)
      continuous_toFun := hlogc
      source' := by simp
      target' := by simp }
  let ℓc : Path (log (u₂ : ℂ)) (conj (log (u₁ : ℂ))) :=
    { toFun := fun x => conj (log (σ (unitInterval.symm x)))
      continuous_toFun := Complex.continuous_conj.comp (hlogc.comp unitInterval.continuous_symm)
      source' := by simp [hlog₂]
      target' := by simp }
  let Λ : Path (log (u₁ : ℂ)) (conj (log (u₁ : ℂ))) := ℓ.trans ℓc
  have hexp : ∀ x, Complex.exp (Λ x) = (⟨fun x => Γ x - 0, by fun_prop⟩ : C(unitInterval, ℂ)) x := by
    intro x
    simp only [Λ, Γ, Path.trans_apply, ContinuousMap.coe_mk, sub_zero]
    split_ifs
    · exact Complex.exp_log (hσ0 _)
    · exact (Complex.exp_conj _).trans (congrArg conj (Complex.exp_log (hσ0 _)))
  have hlift := loopDeg_eq_of_lift ⟨fun x => Γ x - 0, by fun_prop⟩ hnz0 (by simp) Λ.continuous hexp
  rw [hdeg1, hdeg2, hdegq, Path.source, Path.target] at hlift
  have him := congrArg Complex.im hlift
  rw [Int.cast_zero, zero_mul, Complex.sub_im, Complex.conj_im, Complex.log_im,
    arg_ofReal_of_neg hu₁, Complex.zero_im] at him
  linarith [Real.pi_pos]

end QuantumZipper.Thm18Asm.LWFar
