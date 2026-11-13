/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.CaraR8a at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CaraR3Defs
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CaraRZ
import LatticeProb.Bonanno.QuantumZipper.Blueprint.ComplexAnalysis

/-!
# EXT-CA node R8 (assembly, part a): `IsCaratheodoryRevExt` from the boundary structure

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3.R, node **R8**. Given the boundary extension
`F` of `revMap W T` (`CaraR.RevExt`, node R3) together with the boundary structure established
by nodes R4–R7 (the two zeros `a < 0 < b` of `F` on `ℝ`, `F` real with the right sign outside
`[a, b]`, `F (a, b) ⊆ K`, injectivity on `[a, 0]` and on `[0, b]`, and every `s ∈ [a, 0]` having
a partner in `[0, b]`), we check the clauses of `Blueprint.IsCaratheodoryRevExt` one by one.

This is pure bookkeeping (own elementary argument, following the blueprint's R8 sketch); the
analytic content (Pommerenke, *Boundary Behaviour of Conformal Maps*, Thm 2.1, Prop 2.5,
Thm 2.6) sits in the hypotheses, which are proved in nodes R3–R7.
-/

noncomputable section

open Set Filter Topology

namespace QuantumZipper

namespace CaraR

private theorem ofReal_mem_Hbar_R8 (x : ℝ) : (x : ℂ) ∈ Hbar := by
  show (0 : ℝ) ≤ (x : ℂ).im
  simp

/-- The vertical boundary limit of `revMap W T` at a real point is the value of a continuous
extension `F` (to `Hbar`) agreeing with `revMap W T` on `H`. -/
theorem revMapBdry_eq_of_extension_R8 {W : ℝ → ℝ} {T : ℝ} {F : ℂ → ℂ}
    (hFeq : EqOn F (revMap W T) H) (hFc : ContinuousOn F Hbar) (x : ℝ) :
    revMapBdry W T x = F x := by
  have htend : Tendsto (fun y : ℝ => revMap W T (x + y * Complex.I)) (𝓝[>] 0) (𝓝 (F x)) := by
    have hpath : Tendsto (fun y : ℝ => (x : ℂ) + y * Complex.I) (𝓝[>] 0)
        (𝓝[Hbar] (x : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Continuous fun y : ℝ => (x : ℂ) + y * Complex.I := by fun_prop
        have h := this.tendsto 0
        simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        show (0 : ℝ) ≤ ((x : ℂ) + y * Complex.I).im
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one]
        linarith [show (0 : ℝ) < y from hy]
    have hc := ((hFc x (ofReal_mem_Hbar_R8 x)).tendsto).comp hpath
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    apply hFeq
    show (0 : ℝ) < ((x : ℂ) + y * Complex.I).im
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one]
    linarith [show (0 : ℝ) < y from hy]
  exact htend.limUnder_eq

/-- **R8 (assembly).** The boundary structure of the extension `F` (nodes R3–R7) yields
`Blueprint.IsCaratheodoryRevExt W T F`. -/
theorem isCaratheodoryRevExt_of_structure {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T)
    {γ : ℝ → ℂ} (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H) (hK : revHull W T = γ '' Ioc 0 1) {F : ℂ → ℂ}
    (hF : RevExt W T γ F) (hγ0 : γ 0 = 0) {a b : ℝ} (ha0 : a < 0) (hb0 : 0 < b)
    (ha : F a = 0) (hb : F b = 0)
    (hleft : ∀ x : ℝ, x < a → (F x).im = 0 ∧ (F x).re < 0)
    (hright : ∀ x : ℝ, b < x → (F x).im = 0 ∧ 0 < (F x).re)
    (hmid : ∀ x ∈ Ioo a b, F x ∈ γ '' Ioc 0 1)
    (hinjL : InjOn (fun x : ℝ => F x) (Icc a 0)) (hinjR : InjOn (fun x : ℝ => F x) (Icc 0 b))
    (hpair : ∀ s ∈ Icc a 0, ∃ y ∈ Icc 0 b, F y = F s) :
    Blueprint.IsCaratheodoryRevExt W T F := by
  have hbdry : ∀ x : ℝ, revMapBdry W T x = F x :=
    revMapBdry_eq_of_extension_R8 hF.eqOn hF.cont
  have hFr : Continuous fun x : ℝ => F x :=
    hF.cont.comp_continuous Complex.continuous_ofReal ofReal_mem_Hbar_R8
  have hbij := bijOn_revMap_revHull hW hT.le
  -- values on `(a, b)` lie in `H`
  have hmidH : ∀ x ∈ Ioo a b, 0 < (F x).im := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := hmid x hx
    rw [← hux]; exact hγH u hu
  -- the real-value clause
  have hreal : ∀ x : ℝ, (F x).im = 0 ↔ (x ≤ a ∨ b ≤ x) := by
    intro x
    constructor
    · intro h
      by_contra hc
      push Not at hc
      have := hmidH x ⟨hc.1, hc.2⟩
      linarith
    · rintro (h | h)
      · rcases h.lt_or_eq with h | h
        · exact (hleft x h).1
        · rw [h, ha]; simp
      · rcases h.lt_or_eq with h | h
        · exact (hright x h).1
        · rw [← h, hb]; simp
  -- the zeros of `F` on `ℝ`
  have hzero : ∀ x : ℝ, F x = 0 → x = a ∨ x = b := by
    intro x hx
    rcases lt_trichotomy x a with h | h | h
    · have := (hleft x h).2; rw [hx] at this; simp at this
    · exact Or.inl h
    rcases lt_trichotomy x b with h' | h' | h'
    · have := hmidH x ⟨h, h'⟩; rw [hx] at this; simp at this
    · exact Or.inr h'
    · have := (hright x h').2; rw [hx] at this; simp at this
  have hzm : zeroMinus W T = a := by
    have : {x : ℝ | x < 0 ∧ revMapBdry W T x = 0} = {a} := by
      ext x
      simp only [mem_ofPred_eq, mem_singleton_iff, hbdry]
      constructor
      · rintro ⟨hx0, hx⟩
        rcases hzero x hx with h | h
        · exact h
        · linarith
      · rintro rfl; exact ⟨ha0, ha⟩
    rw [zeroMinus, this, csSup_singleton]
  have hzp : zeroPlus W T = b := by
    have : {x : ℝ | 0 < x ∧ revMapBdry W T x = 0} = {b} := by
      ext x
      simp only [mem_ofPred_eq, mem_singleton_iff, hbdry]
      constructor
      · rintro ⟨hx0, hx⟩
        rcases hzero x hx with h | h
        · linarith
        · exact h
      · rintro rfl; exact ⟨hb0, hb⟩
    rw [zeroPlus, this, csInf_singleton]
  -- the welding homeomorphism on `[a, 0]`
  have hwdef : ∀ s : ℝ, weldingHom W T s = sInf {y : ℝ | 0 ≤ y ∧ F y = F s} := by
    intro s
    simp only [weldingHom, hbdry]
  have hwmem : ∀ s ∈ Icc a 0, 0 ≤ weldingHom W T s ∧ F (weldingHom W T s) = F s := by
    intro s hs
    rw [hwdef]
    have hcl : IsClosed {y : ℝ | 0 ≤ y ∧ F y = F s} :=
      (isClosed_le continuous_const continuous_id).inter (isClosed_eq hFr continuous_const)
    obtain ⟨y, hy, hys⟩ := hpair s hs
    exact hcl.csInf_mem ⟨y, hy.1, hys⟩ ⟨0, fun _ hz => hz.1⟩
  have hweq : ∀ s ∈ Icc a 0, ∀ y ∈ Icc (0 : ℝ) b, F y = F s → weldingHom W T s = y := by
    intro s hs y hy hys
    obtain ⟨hw0, hws⟩ := hwmem s hs
    have hle : weldingHom W T s ≤ y := by
      rw [hwdef]; exact csInf_le ⟨0, fun _ hz => hz.1⟩ ⟨hy.1, hys⟩
    exact hinjR ⟨hw0, hle.trans hy.2⟩ hy (by simp only; rw [hws, hys])
  have hwa : weldingHom W T a = b :=
    hweq a ⟨le_rfl, ha0.le⟩ b ⟨hb0.le, le_rfl⟩ (by rw [ha, hb])
  -- values on `H` avoid the values on `ℝ`
  have hHR : ∀ z ∈ H, ∀ r : ℝ, F z ≠ F r := by
    intro z hz r hzr
    have hmem : F z ∈ H \ revHull W T := by
      rw [hF.eqOn hz]; exact hbij.mapsTo hz
    rcases hF.bdry r with h | ⟨u, hu, hur⟩
    · have : (0 : ℝ) < (F z).im := hmem.1
      rw [hzr, h] at this; exact lt_irrefl _ this
    · rcases hu.1.lt_or_eq with hu0 | hu0
      · apply hmem.2
        rw [hK, hzr, ← hur]; exact ⟨u, ⟨hu0, hu.2⟩, rfl⟩
      · have : (0 : ℝ) < (F z).im := hmem.1
        rw [hzr, ← hur, ← hu0, hγ0] at this; simp at this
  have hofRe : ∀ z : ℂ, z.im = 0 → ((z.re : ℝ) : ℂ) = z :=
    fun z h => Complex.ext (by simp) (by simp [h])
  -- fibres on `ℝ`
  have hfibR : ∀ x y : ℝ, F x = F y →
      (x : ℂ) = y ∨ Blueprint.WeldingRel a (weldingHom W T) x y := by
    intro x y hxy
    by_cases hp : (F x).im = 0
    · by_cases hp0 : F x = 0
      · have hy0 : F y = 0 := hxy ▸ hp0
        rcases hzero x hp0 with rfl | rfl <;> rcases hzero y hy0 with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr ⟨x, ⟨le_rfl, ha0.le⟩, Or.inl ⟨rfl, by rw [hwa]⟩⟩
        · exact Or.inr ⟨y, ⟨le_rfl, ha0.le⟩, Or.inr ⟨by rw [hwa], rfl⟩⟩
        · exact Or.inl rfl
      · left
        congr 1
        exact hF.inj_real (F x) hp (by rw [hγ0]; exact hp0) x y rfl hxy.symm
    · have hx : x ∈ Ioo a b := by
        by_contra hc
        simp only [mem_Ioo, not_and_or, not_lt] at hc
        exact hp ((hreal x).2 hc)
      have hy : y ∈ Ioo a b := by
        by_contra hc
        simp only [mem_Ioo, not_and_or, not_lt] at hc
        exact hp (hxy ▸ (hreal y).2 hc)
      rcases le_total x 0 with hx0 | hx0 <;> rcases le_total y 0 with hy0 | hy0
      · left; congr 1; exact hinjL ⟨hx.1.le, hx0⟩ ⟨hy.1.le, hy0⟩ hxy
      · right
        refine ⟨x, ⟨hx.1.le, hx0⟩, Or.inl ⟨rfl, ?_⟩⟩
        rw [hweq x ⟨hx.1.le, hx0⟩ y ⟨hy0, hy.2.le⟩ hxy.symm]
      · right
        refine ⟨y, ⟨hy.1.le, hy0⟩, Or.inr ⟨?_, rfl⟩⟩
        rw [hweq y ⟨hy.1.le, hy0⟩ x ⟨hx0, hx.2.le⟩ hxy]
      · left; congr 1; exact hinjR ⟨hx0, hx.2.le⟩ ⟨hy0, hy.2.le⟩ hxy
  refine ⟨hF.eqOn, hF.cont, ?_, ?_, ?_, ?_, ?_⟩
  · -- surjectivity
    intro p hp
    by_cases hpi : p.im = 0
    · obtain ⟨x, hx⟩ := hF.surj p (Or.inl hpi)
      exact ⟨x, ofReal_mem_Hbar_R8 x, hx⟩
    have hpH : p ∈ H := lt_of_le_of_ne (show (0 : ℝ) ≤ p.im from hp) (Ne.symm hpi)
    by_cases hpK : p ∈ revHull W T
    · rw [hK] at hpK
      obtain ⟨x, hx⟩ := hF.surj p (Or.inr (image_mono Ioc_subset_Icc_self hpK))
      exact ⟨x, ofReal_mem_Hbar_R8 x, hx⟩
    · obtain ⟨z, hz, hzp⟩ := hbij.surjOn ⟨hpH, hpK⟩
      exact ⟨z, H_subset_Hbar hz, by rw [hF.eqOn hz, hzp]⟩
  · rw [hzm, ha]
  · rw [hzm, hzp, hwa]
  · intro x; rw [hzm, hzp]; exact hreal x
  · rw [hzm]
    intro x hx y hy
    constructor
    · intro hxy
      rcases (show (0 : ℝ) ≤ x.im from hx).lt_or_eq with hxH | hxR <;>
        rcases (show (0 : ℝ) ≤ y.im from hy).lt_or_eq with hyH | hyR
      · left
        exact hbij.injOn hxH hyH (by rw [← hF.eqOn hxH, ← hF.eqOn hyH]; exact hxy)
      · exact absurd (hxy.trans (congrArg F (hofRe y hyR.symm)).symm) (hHR x hxH y.re)
      · exact absurd (hxy.symm.trans (congrArg F (hofRe x hxR.symm)).symm) (hHR y hyH x.re)
      · have := hfibR x.re y.re (by rw [hofRe x hxR.symm, hofRe y hyR.symm]; exact hxy)
        rwa [hofRe x hxR.symm, hofRe y hyR.symm] at this
    · rintro (rfl | ⟨s, hs, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩)
      · rfl
      · exact (hwmem s hs).2.symm
      · exact (hwmem s hs).2

end CaraR

end QuantumZipper
