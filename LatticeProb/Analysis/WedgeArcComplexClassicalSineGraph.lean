import LatticeProb.Analysis.WedgeArcClassicalLocalSineGraph

/-! # Complex classical Dirichlet data on an angular arc -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- Complex classical Dirichlet data and their negative second derivatives belong
 to the closed angular sine graph, with the indicated almost-everywhere representatives. -/
theorem wedgeArc_complex_classical_local_mem_sineGraph_closure {θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi)
    {f f' f'' : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-θ / 2) (θ / 2)))
    (hf' : ContinuousOn f' (Icc (-θ / 2) (θ / 2)))
    (hf'' : ContinuousOn f'' (Icc (-θ / 2) (θ / 2)))
    (hfd : ∀ t ∈ Ioo (-θ / 2) (θ / 2), HasDerivAt f (f' t) t)
    (hf'd : ∀ t ∈ Ioo (-θ / 2) (θ / 2), HasDerivAt f' (f'' t) t)
    (ha : f (-θ / 2) = 0) (hb : f (θ / 2) = 0)
    (x y : Lp ℂ 2 (wedgeArcSurfaceMeasure θ))
    (hx : (fun z => x z) =ᵐ[wedgeArcSurfaceMeasure θ]
      fun z => f (Complex.arg z))
    (hy : (fun z => y z) =ᵐ[wedgeArcSurfaceMeasure θ]
      fun z => -f'' (Complex.arg z)) :
    (x, y) ∈ (wedgeArcSinePMap hθ hθ').graph.topologicalClosure := by
  let R : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM
  let I : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM
  have hp (C : ℂ →L[ℝ] ℝ) :
      ((Complex.ofRealCLM.comp C).compLp x,
        (Complex.ofRealCLM.comp C).compLp y) ∈
          (wedgeArcSinePMap hθ hθ').graph.topologicalClosure := by
    apply wedgeArc_classical_local_mem_sineGraph_closure hθ hθ'
      (C.continuous.comp_continuousOn hf) (C.continuous.comp_continuousOn hf'')
      (C.continuous.comp_continuousOn hf')
      (fun t ht => C.hasFDerivAt.comp_hasDerivAt t (hfd t ht))
      (fun t ht => C.hasFDerivAt.comp_hasDerivAt t (hf'd t ht))
      (by simp [ha]) (by simp [hb])
    · filter_upwards [(Complex.ofRealCLM.comp C).coeFn_compLp x, hx] with z hz hzx
      change (Complex.ofRealCLM.comp C).compLp x z = (C (f (Complex.arg z)) : ℂ)
      rw [hz, hzx]
      rfl
    · filter_upwards [(Complex.ofRealCLM.comp C).coeFn_compLp y, hy] with z hz hzy
      change (Complex.ofRealCLM.comp C).compLp y z = ((-C (f'' (Complex.arg z)) : ℝ) : ℂ)
      rw [hz, hzy]
      simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, map_neg,
        Complex.ofReal_neg]
  have hr : (R.compLp x, R.compLp y) ∈
      (wedgeArcSinePMap hθ hθ').graph.topologicalClosure := hp Complex.reCLM
  have hi : (I.compLp x, I.compLp y) ∈
      (wedgeArcSinePMap hθ hθ').graph.topologicalClosure := hp Complex.imCLM
  have hsum := (wedgeArcSinePMap hθ hθ').graph.topologicalClosure.add_mem hr
    ((wedgeArcSinePMap hθ hθ').graph.topologicalClosure.smul_mem Complex.I hi)
  have hdecomp (u : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) :
      R.compLp u + Complex.I • I.compLp u = u := by
    apply Lp.ext
    change (fun z => (R.compLp u + Complex.I • I.compLp u) z) =ᵐ[_] (fun z => u z)
    filter_upwards [Lp.coeFn_add (R.compLp u) (Complex.I • I.compLp u),
      Lp.coeFn_smul Complex.I (I.compLp u), R.coeFn_compLp u, I.coeFn_compLp u] with z hz hs hr' hi'
    rw [hz]
    change R.compLp u z + (Complex.I • I.compLp u) z = u z
    rw [hs, hr']
    change R (u z) + Complex.I * I.compLp u z = u z
    rw [hi']
    change ((u z).re : ℂ) + Complex.I * ((u z).im : ℂ) = u z
    simpa only [mul_comm] using Complex.re_add_im (u z)
  simpa only [Prod.smul_mk, Prod.mk_add_mk, hdecomp] using hsum

end LatticeProb
