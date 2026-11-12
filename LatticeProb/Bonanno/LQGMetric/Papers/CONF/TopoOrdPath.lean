/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.TopoOrdPath at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Topo.RectMeet

/-!
# TOPO-ORD, step 3a: path helpers (paths from functions continuous on intervals, segments,
first hitting times)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric.CONF.DD

/-- the path `u ↦ f(s₀ + (s₁ − s₀) u)` -/
def pathOn (f : ℝ → ℂ) {s₀ s₁ : ℝ} (h : s₀ ≤ s₁) (hf : ContinuousOn f (Icc s₀ s₁)) :
    Path (f s₀) (f s₁) where
  toFun u := f (s₀ + (s₁ - s₀) * (u : ℝ))
  continuous_toFun := hf.comp_continuous (by fun_prop) (fun u =>
    ⟨by nlinarith [u.2.1], by nlinarith [u.2.2]⟩)
  source' := by simp
  target' := by simp

theorem pathOn_range (f : ℝ → ℂ) {s₀ s₁ : ℝ} (h : s₀ ≤ s₁) (hf : ContinuousOn f (Icc s₀ s₁)) :
    range (pathOn f h hf) ⊆ f '' Icc s₀ s₁ := by
  rintro _ ⟨u, rfl⟩
  exact ⟨_, ⟨by nlinarith [u.2.1], by nlinarith [u.2.2]⟩, rfl⟩

/-- the segment path -/
def segPath (p q : ℂ) : Path p q :=
  (pathOn (fun s : ℝ => p + (s : ℂ) * (q - p)) zero_le_one (by fun_prop)).cast
    (by simp) (by simp)

theorem segPath_range (p q : ℂ) : range (segPath p q) ⊆
    {x | ∃ s ∈ Icc (0 : ℝ) 1, x.re = p.re + s * (q.re - p.re) ∧ x.im = p.im + s * (q.im - p.im)} := by
  intro x hx
  have : x ∈ range (pathOn (fun s : ℝ => p + (s : ℂ) * (q - p)) zero_le_one (by fun_prop)) := by
    simpa [segPath, Path.cast_coe] using hx
  obtain ⟨s, hs, rfl⟩ := pathOn_range _ _ _ this
  exact ⟨s, hs, by simp, by simp⟩

theorem path_trans_range {p q r : ℂ} (γ₁ : Path p q) (γ₂ : Path q r) :
    range (γ₁.trans γ₂) = range γ₁ ∪ range γ₂ := Path.trans_range γ₁ γ₂

/-- first hitting time of a level -/
theorem first_hit {f : ℝ → ℝ} {R M : ℝ} (hR : 0 ≤ R) (hf : ContinuousOn f (Icc 0 R))
    (h0 : f 0 < M) (hRM : M ≤ f R) :
    ∃ r₀ ∈ Icc 0 R, f r₀ = M ∧ ∀ u ∈ Icc 0 r₀, f u ≤ M := by
  set T := Icc 0 R ∩ f ⁻¹' {M} with hT
  have hTc : IsClosed T := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hTne : T.Nonempty := by
    obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc hR hf ⟨h0.le, hRM⟩
    exact ⟨v, hv, hfv⟩
  have hTb : BddBelow T := ⟨0, fun u hu => hu.1.1⟩
  set t := sInf T with ht
  have htT : t ∈ T := hTc.csInf_mem hTne hTb
  refine ⟨t, htT.1, htT.2, fun u hu => ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc hu.1
    (hf.mono (Icc_subset_Icc le_rfl (hu.2.trans htT.1.2))) ⟨h0.le, hcon.le⟩
  have h1 : t ≤ v := csInf_le hTb ⟨⟨hv.1, hv.2.trans (hu.2.trans htT.1.2)⟩, hfv⟩
  have h2 : v = t := le_antisymm (hv.2.trans hu.2) h1
  have h3 : u = t := le_antisymm hu.2 (h2 ▸ hv.2)
  rw [h3, htT.2] at hcon
  exact lt_irrefl _ hcon

end LQGMetric.CONF.DD
