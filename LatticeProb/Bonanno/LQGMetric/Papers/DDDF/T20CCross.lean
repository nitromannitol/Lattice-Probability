/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20CCross at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CDefs

/-!
# DDDF Theorem 20, Step 4: crossing the annulus around a block (task P2-DDDFT20c)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1131–1132: "if `P` is visited by a geodesic, then
there are at least two short disjoint rectangle crossings among the four surrounding `P`"; the
same fact is used for the circuit of l. 1103–1105. `T20C.annulus_cross`: a path that starts in
the inner box `[x₁,x₂] × [y₁,y₂]` and ends outside the open outer box `(x₀,x₃) × (y₀,y₃)` has
a piece inside the closed outer box that crosses one of the four strips between the inner and the
outer side (first exit time from the outer box, then the last time at the inner level).
Own elementary argument (DDDF leave it implicit).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DDDF
namespace T20C

/-- the last time before `v` at which `f ≤ a`, when `f s ≤ a < f v` -/
lemma last_cross {f : ℝ → ℝ} {s v a : ℝ} (hsv : s ≤ v) (hf : ContinuousOn f (Icc s v))
    (hs : f s ≤ a) (hv : a < f v) :
    ∃ u, s ≤ u ∧ u < v ∧ f u = a ∧ ∀ r ∈ Icc u v, a ≤ f r := by
  set F := {r ∈ Icc s v | f r ≤ a}
  have hFc : IsClosed F := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hFne : F.Nonempty := ⟨s, ⟨le_rfl, hsv⟩, hs⟩
  have hFb : BddAbove F := ⟨v, fun r hr => hr.1.2⟩
  set u := sSup F
  have huF : u ∈ F := hFc.csSup_mem hFne hFb
  have hu1 : s ≤ u := le_csSup hFb ⟨⟨le_rfl, hsv⟩, hs⟩
  have huv : u ≤ v := huF.1.2
  have hgt : ∀ r ∈ Ioc u v, a < f r := by
    intro r hr
    by_contra h
    have : r ∈ F := ⟨⟨hu1.trans hr.1.le, hr.2⟩, not_lt.1 h⟩
    exact absurd (le_csSup hFb this) (not_le.2 hr.1)
  have hlt : u < v := lt_of_le_of_ne huv fun h => by
    have := huF.2; rw [h] at this; linarith
  have hcl : Icc u v ⊆ {r ∈ Icc u v | a ≤ f r} := by
    have hC : IsClosed {r ∈ Icc u v | a ≤ f r} :=
      (hf.mono (Icc_subset_Icc hu1 le_rfl)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have h := (hC.closure_subset_iff).2 fun r (hr : r ∈ Ioc u v) =>
      (⟨Ioc_subset_Icc_self hr, (hgt r hr).le⟩ : r ∈ {r ∈ Icc u v | a ≤ f r})
    rwa [closure_Ioc hlt.ne] at h
  refine ⟨u, hu1, hlt, le_antisymm huF.2 (hcl ⟨le_rfl, huv⟩).2, fun r hr => (hcl hr).2⟩

/-- the first exit time from an open box, and the path stays in the closed box before it -/
lemma first_exit {γ : ℝ → ℂ} {s t : ℝ} (hst : s ≤ t) (hγ : ContinuousOn γ (Icc s t))
    {x₀ x₃ y₀ y₃ : ℝ} (hin : γ s ∈ Ioo x₀ x₃ ×ℂ Ioo y₀ y₃) (hout : γ t ∉ Ioo x₀ x₃ ×ℂ Ioo y₀ y₃) :
    ∃ v, s < v ∧ v ≤ t ∧ γ v ∉ Ioo x₀ x₃ ×ℂ Ioo y₀ y₃ ∧
      ∀ r ∈ Icc s v, γ r ∈ Icc x₀ x₃ ×ℂ Icc y₀ y₃ := by
  have hO : IsOpen (Ioo x₀ x₃ ×ℂ Ioo y₀ y₃) := isOpen_Ioo.reProdIm isOpen_Ioo
  set E := {r ∈ Icc s t | γ r ∉ Ioo x₀ x₃ ×ℂ Ioo y₀ y₃}
  have hEc : IsClosed E := hγ.preimage_isClosed_of_isClosed isClosed_Icc hO.isClosed_compl
  have hEne : E.Nonempty := ⟨t, ⟨hst, le_rfl⟩, hout⟩
  have hEb : BddBelow E := ⟨s, fun r hr => hr.1.1⟩
  set v := sInf E
  have hvE : v ∈ E := hEc.csInf_mem hEne hEb
  have hsv : s < v := lt_of_le_of_ne hvE.1.1 fun h => hvE.2 (h ▸ hin)
  have hbefore : ∀ r ∈ Ico s v, γ r ∈ Ioo x₀ x₃ ×ℂ Ioo y₀ y₃ := by
    intro r hr
    by_contra h
    exact absurd (csInf_le hEb ⟨⟨hr.1, hr.2.le.trans hvE.1.2⟩, h⟩) (not_le.2 hr.2)
  have hC : IsClosed {r ∈ Icc s v | γ r ∈ Icc x₀ x₃ ×ℂ Icc y₀ y₃} :=
    (hγ.mono (Icc_subset_Icc le_rfl hvE.1.2)).preimage_isClosed_of_isClosed isClosed_Icc
      (isClosed_Icc.reProdIm isClosed_Icc)
  have hcl : Icc s v ⊆ {r ∈ Icc s v | γ r ∈ Icc x₀ x₃ ×ℂ Icc y₀ y₃} := by
    have h := (hC.closure_subset_iff).2 fun r (hr : r ∈ Ico s v) => by
      have h := hbefore r hr
      rw [Complex.mem_reProdIm] at h
      exact (⟨Ico_subset_Icc_self hr, (Complex.mem_reProdIm).2
        ⟨Ioo_subset_Icc_self h.1, Ioo_subset_Icc_self h.2⟩⟩ :
          r ∈ {r ∈ Icc s v | γ r ∈ Icc x₀ x₃ ×ℂ Icc y₀ y₃})
    rwa [closure_Ico hsv.ne] at h
  exact ⟨v, hsv, hvE.1.2, hvE.2, fun r hr => (hcl hr).2⟩

/-- **Crossing the annulus** (DDDF l. 1131–1132): a path from the inner box to the outside of
the open outer box crosses one of the four strips of the annulus, from the inner to the outer
side, inside the closed outer box. -/
lemma annulus_cross {γ : ℝ → ℂ} {s t : ℝ} (hst : s ≤ t) (hγ : ContinuousOn γ (Icc s t))
    {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ} (hx₀ : x₀ < x₁) (hx₃ : x₂ < x₃) (hy₀ : y₀ < y₁)
    (hy₃ : y₂ < y₃) (hin : γ s ∈ Icc x₁ x₂ ×ℂ Icc y₁ y₂)
    (hout : γ t ∉ Ioo x₀ x₃ ×ℂ Ioo y₀ y₃) :
    ∃ u v, s ≤ u ∧ u < v ∧ v ≤ t ∧ (∀ r ∈ Icc u v, γ r ∈ Icc x₀ x₃ ×ℂ Icc y₀ y₃) ∧
      (((γ u).im = y₂ ∧ (γ v).im = y₃ ∧ ∀ r ∈ Icc u v, y₂ ≤ (γ r).im) ∨
       ((γ u).im = y₁ ∧ (γ v).im = y₀ ∧ ∀ r ∈ Icc u v, (γ r).im ≤ y₁) ∨
       ((γ u).re = x₂ ∧ (γ v).re = x₃ ∧ ∀ r ∈ Icc u v, x₂ ≤ (γ r).re) ∨
       ((γ u).re = x₁ ∧ (γ v).re = x₀ ∧ ∀ r ∈ Icc u v, (γ r).re ≤ x₁)) := by
  rw [Complex.mem_reProdIm] at hin
  obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := hin
  have hin' : γ s ∈ Ioo x₀ x₃ ×ℂ Ioo y₀ y₃ := by
    rw [Complex.mem_reProdIm]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨v, hsv, hvt, hvout, hbox⟩ := first_exit hst hγ hin' hout
  have hγv : ContinuousOn γ (Icc s v) := hγ.mono (Icc_subset_Icc le_rfl hvt)
  have hre : ContinuousOn (fun r => (γ r).re) (Icc s v) := Complex.continuous_re.comp_continuousOn hγv
  have him : ContinuousOn (fun r => (γ r).im) (Icc s v) := Complex.continuous_im.comp_continuousOn hγv
  have hbv := hbox v ⟨hsv.le, le_rfl⟩
  rw [Complex.mem_reProdIm] at hbv hvout
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hbv
  have hbox' : ∀ u, s ≤ u → ∀ r ∈ Icc u v, γ r ∈ Icc x₀ x₃ ×ℂ Icc y₀ y₃ :=
    fun u hu r hr => hbox r ⟨hu.trans hr.1, hr.2⟩
  by_cases hT : (γ v).im = y₃
  · obtain ⟨u, hsu, huv, hu, hr⟩ := last_cross hsv.le him hi2 (by rw [hT]; exact hy₃)
    exact ⟨u, v, hsu, huv, hvt, hbox' u hsu, Or.inl ⟨hu, hT, hr⟩⟩
  by_cases hB : (γ v).im = y₀
  · obtain ⟨u, hsu, huv, hu, hr⟩ := last_cross (f := fun r => -(γ r).im) (a := -y₁) hsv.le
      him.neg (by linarith) (by rw [hB]; linarith)
    refine ⟨u, v, hsu, huv, hvt, hbox' u hsu, Or.inr (Or.inl ⟨?_, hB, fun r h => ?_⟩)⟩
    · linarith
    · have := hr r h; linarith
  by_cases hR : (γ v).re = x₃
  · obtain ⟨u, hsu, huv, hu, hr⟩ := last_cross hsv.le hre hr2 (by rw [hR]; exact hx₃)
    exact ⟨u, v, hsu, huv, hvt, hbox' u hsu, Or.inr (Or.inr (Or.inl ⟨hu, hR, hr⟩))⟩
  by_cases hL : (γ v).re = x₀
  · obtain ⟨u, hsu, huv, hu, hr⟩ := last_cross (f := fun r => -(γ r).re) (a := -x₁) hsv.le
      hre.neg (by linarith) (by rw [hL]; linarith)
    refine ⟨u, v, hsu, huv, hvt, hbox' u hsu, Or.inr (Or.inr (Or.inr ⟨?_, hL, fun r h => ?_⟩))⟩
    · linarith
    · have := hr r h; linarith
  exact absurd ⟨⟨lt_of_le_of_ne a1 (Ne.symm hL), lt_of_le_of_ne a2 hR⟩,
    ⟨lt_of_le_of_ne b1 (Ne.symm hB), lt_of_le_of_ne b2 hT⟩⟩ hvout

end T20C
end DDDF
end LQGMetric
