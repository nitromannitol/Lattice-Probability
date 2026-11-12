/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.TopoOrdRay at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.TopoOrdChart2

/-!
# TOPO-ORD, step 2d: lifted paths and outward rays in the inner chart plane

With `L₁` a chart of `ℂ ∖ int K₁` and `L₂` one of `ℂ ∖ int K₂` (`K₁ ⊆ int K₂`):
* `chart_path`: a path in `ℂ ∖ int K₁` with an angle lift has a continuous `L₁`-preimage;
* `chart_bdy_pre`: lifted points of `∂K` are chart images of the line `Re ζ = 0`;
* `chart_ray`: the outward ray `r ↦ L₂(ξ + r)` (`Re ξ = 0`) of the outer chart has a continuous
  `L₁`-preimage `R` with `Re R(r) ≥ r − C` and `Im R(r) → Im ξ + d` as `Re R(r) → ∞`, with
  constants `C`, `d` not depending on `ξ`.
These are the "outward rays" of handoff P2-CONFTOPO step 2, built from the Carathéodory maps of
the inverted exteriors (DV-CONF-TO1); the inward rays are the horizontal half-lines `Re ζ < 0`
of the chart plane of `K₁`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter

namespace LQGMetric.CONF.DD

theorem chart_bdy_pre {K : Set ℂ} {z : ℂ} {L : ℂ → ℂ} (hL : IsChart K z L) (hK : IsClosed K)
    {w : ℂ} (hw : z + Complex.exp w ∈ frontier K) : ∃ ζ : ℂ, ζ.re = 0 ∧ L ζ = w := by
  obtain ⟨ζ, hζ, hLζ⟩ := hL.surj w hw.2
  refine ⟨ζ, ?_, hLζ⟩
  by_contra h
  exact hL.out ζ (lt_of_le_of_ne hζ (Ne.symm h)) (by rw [hLζ]; exact hK.frontier_subset hw)

/-- the log-lift of a path with an angle lift -/
def plift (z : ℂ) (P : ℝ → ℂ) (α : ℝ → ℝ) (t : ℝ) : ℂ :=
  (Real.log ‖P t - z‖ : ℂ) + (α t : ℂ) * Complex.I

theorem chart_path {K : Set ℂ} {z : ℂ} {L : ℂ → ℂ} (hL : IsChart K z L) {P : ℝ → ℂ}
    {α : ℝ → ℝ} {a b : ℝ} (hPc : ContinuousOn P (Icc a b)) (hPm : ∀ t ∈ Icc a b, P t ∉ interior K)
    (hz : z ∈ interior K) (hα : IsAngleLift z P a b α) :
    (∀ t ∈ Icc a b, z + Complex.exp (plift z P α t) = P t) ∧
    ∃ Z : ℝ → ℂ, ContinuousOn Z (Icc a b) ∧ ∀ t ∈ Icc a b, 0 ≤ (Z t).re ∧ L (Z t) = plift z P α t := by
  have hne : ∀ t ∈ Icc a b, P t - z ≠ 0 := fun t ht e => hPm t ht (sub_eq_zero.1 e ▸ hz)
  have hexp : ∀ t ∈ Icc a b, z + Complex.exp (plift z P α t) = P t := by
    intro t ht; rw [plift, exp_log_lift (hne t ht) (hα.2 t ht)]; ring
  refine ⟨hexp, ?_⟩
  have hpre : ∀ t, ∃ ζ : ℂ, t ∈ Icc a b → 0 ≤ ζ.re ∧ L ζ = plift z P α t := by
    intro t
    by_cases ht : t ∈ Icc a b
    · obtain ⟨ζ, h1, h2⟩ := hL.surj (plift z P α t) (by rw [hexp t ht]; exact hPm t ht)
      exact ⟨ζ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose Z hZ using hpre
  have hpc : ContinuousOn (plift z P α) (Icc a b) := by
    unfold plift
    refine ContinuousOn.add (Complex.continuous_ofReal.comp_continuousOn
      (ContinuousOn.log (continuous_norm.comp_continuousOn (hPc.sub continuousOn_const))
        fun t ht => norm_ne_zero_iff.2 (hne t ht))) ?_
    exact (Complex.continuous_ofReal.comp_continuousOn hα.1).mul continuousOn_const
  exact ⟨Z, hL.continuousOn_preimage hpc (fun t ht => hZ t ht), fun t ht => hZ t ht⟩

/-- the outward ray of the outer chart, seen in the inner chart plane -/
theorem chart_ray {K₁ K₂ : Set ℂ} {z : ℂ} {L₁ L₂ : ℂ → ℂ} (hL₁ : IsChart K₁ z L₁)
    (hL₂ : IsChart K₂ z L₂) (h12 : K₁ ⊆ interior K₂)
    {C₁ C₂ : ℝ} (hC₁ : ∀ ζ : ℂ, 0 ≤ ζ.re → ‖L₁ ζ - ζ‖ ≤ C₁)
    (hC₂ : ∀ ζ : ℂ, 0 ≤ ζ.re → ‖L₂ ζ - ζ‖ ≤ C₂) {c₁ c₂ : ℂ}
    (hc₁ : ∀ ε > 0, ∃ R, ∀ ζ : ℂ, R ≤ ζ.re → ‖L₁ ζ - ζ - c₁‖ < ε)
    (hc₂ : ∀ ε > 0, ∃ R, ∀ ζ : ℂ, R ≤ ζ.re → ‖L₂ ζ - ζ - c₂‖ < ε)
    {ξ : ℂ} (hξ : ξ.re = 0) :
    ∃ R : ℝ → ℂ, ContinuousOn R (Ici 0) ∧
      (∀ r, 0 ≤ r → 0 ≤ (R r).re ∧ L₁ (R r) = L₂ (ξ + r)) ∧
      (∀ r, 0 ≤ r → r - (C₁ + C₂) ≤ (R r).re) ∧
      ∀ ε > 0, ∃ T, ∀ r, 0 ≤ r → T ≤ (R r).re → |(R r).im - ξ.im - (c₂ - c₁).im| < ε := by
  have hre : ∀ r : ℝ, (ξ + r).re = r := fun r => by simp [hξ]
  have hpre : ∀ r : ℝ, ∃ ζ : ℂ, 0 ≤ r → 0 ≤ ζ.re ∧ L₁ ζ = L₂ (ξ + r) := by
    intro r
    by_cases hr : 0 ≤ r
    · have hni : z + Complex.exp (L₂ (ξ + r)) ∉ interior K₁ := by
        intro hin
        rcases eq_or_lt_of_le hr with h | h
        · have := hL₂.bdy (ξ + r) (by rw [hre, h])
          exact this.2 (h12 (interior_subset hin))
        · exact hL₂.out (ξ + r) (by rw [hre]; exact h) (interior_subset (h12 (interior_subset hin)))
      obtain ⟨ζ, h1, h2⟩ := hL₁.surj _ hni
      exact ⟨ζ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose R hR using hpre
  have hpc : Continuous fun r : ℝ => L₂ (ξ + r) := hL₂.cont.comp (by fun_prop)
  have hRc : ContinuousOn R (Ici 0) := by
    intro r hr
    have hco := hL₁.continuousOn_preimage (p := fun r : ℝ => L₂ (ξ + r)) (q := R) (a := 0)
      (b := r + 1) hpc.continuousOn (fun t ht => hR t ht.1)
    refine (hco r ⟨hr, by linarith⟩).mono_of_mem_nhdsWithin ?_
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  -- distance from the straight ray
  have hdist : ∀ r, 0 ≤ r → ‖R r - (ξ + r)‖ ≤ C₁ + C₂ := by
    intro r hr
    obtain ⟨h0, he⟩ := hR r hr
    have h1 := hC₁ (R r) h0
    have h2 := hC₂ (ξ + r) (by rw [hre]; exact hr)
    calc ‖R r - (ξ + r)‖ = ‖(L₂ (ξ + r) - (ξ + r)) - (L₁ (R r) - R r)‖ := by rw [he]; ring_nf
      _ ≤ ‖L₂ (ξ + r) - (ξ + r)‖ + ‖L₁ (R r) - R r‖ := norm_sub_le _ _
      _ ≤ C₁ + C₂ := by linarith
  have hreb : ∀ r, 0 ≤ r → |(R r).re - r| ≤ C₁ + C₂ := by
    intro r hr
    have := (Complex.abs_re_le_norm _).trans (hdist r hr)
    simpa [hξ] using this
  refine ⟨R, hRc, fun r hr => hR r hr, fun r hr => by linarith [(abs_le.1 (hreb r hr)).1], ?_⟩
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := hc₁ (ε / 2) (by positivity)
  obtain ⟨T₂, hT₂⟩ := hc₂ (ε / 2) (by positivity)
  refine ⟨max T₁ (T₂ + (C₁ + C₂)), fun r hr hT => ?_⟩
  obtain ⟨h0, he⟩ := hR r hr
  have hA := hT₁ (R r) ((le_max_left _ _).trans hT)
  have hrT : T₂ ≤ (ξ + r).re := by
    rw [hre]; linarith [(abs_le.1 (hreb r hr)).2, le_max_right T₁ (T₂ + (C₁ + C₂))]
  have hB := hT₂ (ξ + r) hrT
  have hkey : R r - ξ - r - (c₂ - c₁) =
      (L₂ (ξ + r) - (ξ + r) - c₂) - (L₁ (R r) - R r - c₁) := by rw [he]; ring
  have hn : ‖R r - ξ - r - (c₂ - c₁)‖ < ε := by
    rw [hkey]
    calc _ ≤ ‖L₂ (ξ + r) - (ξ + r) - c₂‖ + ‖L₁ (R r) - R r - c₁‖ := norm_sub_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hB hA
      _ = ε := by ring
  have := (Complex.abs_im_le_norm _).trans_lt hn
  simpa using this

end LQGMetric.CONF.DD
