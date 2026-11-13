/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.CaraR5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CaraR4
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CaraR5Flow
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CaraRZ
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CoreArc3e

/-!
# EXT-CA node R5: the ends of the swallowed interval are mapped to `0`

Blueprint `blueprint/EXT_CA_BLUEPRINT.md` §3.R, node R5. For a simple reverse hull
`revHull W T = γ(0,1]` with boundary extension `F` (`RevExt`, node R3, taken as the hypothesis
`hR3 : ExtExists` because it is applied to shifted drivers) and swallowed interval
`swallowedSet W T = [a,b]`, we have `a < 0 < b` and `F a = F b = 0`.

Source: Lawler, *Conformally Invariant Processes in the Plane* (2005), §4.1, p. 80 (real flow,
swallowing times: `u^x_τ → 0` at the hitting time). The case split below (hitting time `τ = T`
versus `τ < T`, the latter excluded since then `F b` would be a point of the arc strictly inside
`ℍ`) is the blueprint's own argument.
-/

open Set Filter
open scoped Topology ENNReal

namespace QuantumZipper

namespace CaraR

open RealLine

variable {W : ℝ → ℝ}

/-- Along a filter of real points converging to `c`, a function continuous on `Hbar` converges to
its value at the real point `c`. -/
theorem tendsto_comp_ofReal_of_continuousOn {F : ℂ → ℂ} (hF : ContinuousOn F Hbar)
    {l : Filter ℝ} {g : ℝ → ℝ} {c : ℝ} (hg : Tendsto g l (𝓝 c)) :
    Tendsto (fun x => F (g x)) l (𝓝 (F c)) := by
  have hcH : ((c : ℝ) : ℂ) ∈ Hbar := show 0 ≤ ((c : ℝ) : ℂ).im by simp
  have h1 : Tendsto (fun x => ((g x : ℝ) : ℂ)) l (𝓝[Hbar] (c : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨(Complex.continuous_ofReal.tendsto c).comp hg,
      Eventually.of_forall fun x => show 0 ≤ ((g x : ℝ) : ℂ).im by simp⟩
  exact (hF _ hcH).tendsto.comp h1

/-- A real-valued limit of a function continuous on `Hbar` along real points is real. -/
theorem im_eq_zero_of_eventually {F : ℂ → ℂ} (hF : ContinuousOn F Hbar) {l : Filter ℝ}
    [l.NeBot] {c : ℝ} (hl : l ≤ 𝓝 c) (h : ∀ᶠ x : ℝ in l, (F x).im = 0) : (F c).im = 0 := by
  have hA := tendsto_comp_ofReal_of_continuousOn hF (g := id) (tendsto_id.mono_left hl)
  have hB := (Complex.continuous_im.tendsto _).comp hA
  exact tendsto_nhds_unique hB (tendsto_const_nhds.congr' (h.mono fun x hx => hx.symm))

/-- Surviving to time `T` implies surviving to any earlier time `τ ≤ T`. -/
theorem not_mem_swallowedSet_of_time_le {T τ x : ℝ} (hτT : τ ≤ T) (hx : x ∉ swallowedSet W T) :
    x ∉ swallowedSet W τ := by
  obtain ⟨u, hu⟩ := not_mem_swallowedSet_iff.1 hx
  exact not_mem_swallowedSet_iff.2 ⟨u, isRealRevSol_restrict hu hτT⟩

/-- A swallowed point `c ≠ W 0` has a finite hitting time `τ ∈ (0,T]`. -/
theorem exists_hitTime_of_mem (hW : Continuous W) {T c : ℝ} (hT : 0 ≤ T)
    (hc : c ∈ swallowedSet W T) (hc0 : c ≠ W 0) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ T ∧ realHitTime W c = ENNReal.ofReal τ := by
  have hle : realHitTime W c ≤ ENNReal.ofReal T :=
    not_lt.1 fun h => (ofReal_lt_realHitTime_iff hW hT).1 h hc
  have hτ : realHitTime W c = ENNReal.ofReal (realHitTime W c).toReal :=
    (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)).symm
  refine ⟨_, ?_, ?_, hτ⟩
  · have := realHitTime_pos hW hc0
    rw [hτ] at this
    exact ENNReal.ofReal_pos.1 this
  · rw [hτ] at hle
    exact (ENNReal.ofReal_le_ofReal_iff hT).1 hle

/-- **R5, case `τ < T`.** The extension `F'` of the shifted map `revMap W⁺ (T-τ)` sends `0` into
`ℍ`: `0` lies in the closure of `revHull W τ`, which `revMap W⁺ (T-τ)` maps into the compact
subarc `γ[r,1] ⊆ ℍ` of `revHull W T`, where `revHull W⁺ (T-τ) = γ(0,r]`. -/
theorem shift_ext_zero_mem_H (hW : Continuous W) (hW0 : W 0 = 0) {τ T : ℝ} (hτ : 0 < τ)
    (hτT : τ < T) (hK : IsSimpleCurveHull (revHull W T)) {F' : ℂ → ℂ}
    (hEq' : EqOn F' (revMap (fun r => W (τ + r) - W τ) (T - τ)) H) (hF' : ContinuousOn F' Hbar) :
    F' 0 ∈ H := by
  obtain ⟨γ, hγc, -, -, hγH, hKγ, σ, hσ0, hσT, -, hσm, hσK, -⟩ :=
    WeldingConsistency.exists_arc_data CoreArc.loewnerSubhullsOfArc hW hW0 (hτ.trans hτT) hK
  have hT : 0 < T := hτ.trans hτT
  have hTτ : T - τ ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith⟩
  have hr0 : 0 < σ (T - τ) := by
    have := hσm ⟨le_rfl, hT.le⟩ hTτ (by linarith : (0 : ℝ) < T - τ)
    rwa [hσ0] at this
  have hr1 : σ (T - τ) < 1 := by
    have := hσm hTτ ⟨hT.le, le_rfl⟩ (by linarith : T - τ < T)
    rwa [hσT] at this
  have hshift : revHull (fun r => W (τ + r) - W τ) (T - τ) = γ '' Ioc 0 (σ (T - τ)) :=
    (WeldingConsistency.revHull_shift_eq hW hW0 hτT).trans (hσK _ hTτ)
  have hW' : Continuous fun r => W (τ + r) - W τ :=
    (hW.comp (continuous_const.add continuous_id)).sub continuous_const
  set C := γ '' Icc (σ (T - τ)) 1 with hCdef
  have hCc : IsCompact C :=
    isCompact_Icc.image_of_continuousOn (hγc.mono (Icc_subset_Icc_left hr0.le))
  have hCH : C ⊆ H := by
    rintro _ ⟨u, hu, rfl⟩
    exact hγH u ⟨hr0.trans_le hu.1, hu.2⟩
  have hsub : F' '' revHull W τ ⊆ C := by
    rintro _ ⟨w, hw, rfl⟩
    have hwH : w ∈ H := hw.1
    rw [hEq' hwH]
    have hp := (bijOn_revMap_revHull hW' (by linarith : (0 : ℝ) ≤ T - τ)).mapsTo hwH
    have hpK : revMap (fun r => W (τ + r) - W τ) (T - τ) w ∈ revHull W T := by
      refine ⟨hp.1, ?_⟩
      rintro ⟨z, hz, hzp⟩
      rw [WeldingConsistency.revMap_comp hW hW0 hτ.le hτT.le hz] at hzp
      have hzH := ((bijOn_revMap_revHull hW hτ.le).mapsTo hz).1
      exact hw.2 ⟨z, hz, injOn_revMap _ hW' (by linarith) hzH hwH hzp⟩
    rw [hKγ] at hpK
    obtain ⟨u, hu, hup⟩ := hpK
    refine ⟨u, ⟨not_lt.1 fun hlt => hp.2 ?_, hu.2⟩, hup⟩
    rw [hshift]
    exact ⟨u, ⟨hu.1, hlt.le⟩, hup⟩
  have h0 := zero_mem_closure_revHull hW hW0 hτ
  have hcont : ContinuousWithinAt F' (revHull W τ) 0 :=
    (hF' 0 (show (0 : ℝ) ≤ (0 : ℂ).im by simp)).mono fun w hw =>
      (show (0 : ℝ) < w.im from hw.1).le
  exact hCH (closure_minimal hsub hCc.isClosed (hcont.mem_closure_image h0))

/-- **R5, core.** Let `c` be a real point, approached along a filter `l` of points surviving to
time `T`, with `(F c).im = 0`, and let `τ ∈ (0,T]` be such that `u^x_τ → 0` along `l`. Then
`F c = 0`. For `τ = T` this is R4; for `τ < T`, `F c = F' 0 ∈ ℍ` (`shift_ext_zero_mem_H`) would
contradict `(F c).im = 0`. -/
theorem revExt_end_eq_zero (hR3 : ExtExists) (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hT : 0 < T) (hK : IsSimpleCurveHull (revHull W T)) {γ : ℝ → ℂ} {F : ℂ → ℂ}
    (hF : RevExt W T γ F) {c τ : ℝ} {l : Filter ℝ} [l.NeBot] (hl : l ≤ 𝓝 c) (hτ0 : 0 < τ)
    (hτT : τ ≤ T) (hout : ∀ᶠ x in l, x ∉ swallowedSet W T)
    (hlim : Tendsto (realRevMap W τ) l (𝓝 0)) (hreal : (F c).im = 0) : F c = 0 := by
  have hA := tendsto_comp_ofReal_of_continuousOn hF.cont (g := id) (tendsto_id.mono_left hl)
  rcases hτT.lt_or_eq with hlt | rfl
  · exfalso
    have hW' : Continuous fun r => W (τ + r) - W τ :=
      (hW.comp (continuous_const.add continuous_id)).sub continuous_const
    have hW'0 : (fun r => W (τ + r) - W τ) 0 = 0 := by simp
    obtain ⟨⟨γ', hγ'c, hγ'i, hγ'0, hγ'H, hK'⟩, -⟩ :=
      WeldingConsistency.base_simple CoreArc.loewnerSubhullsOfArc hW hW0 hT hK hτ0 hlt
    obtain ⟨F', hF'⟩ := hR3 _ hW' hW'0 (T - τ) (sub_pos.2 hlt) γ' hγ'c hγ'i hγ'0 hγ'H hK'
    have hcomp : ∀ᶠ x in l, F' (realRevMap W τ x) = F x := hout.mono fun x hx =>
      (eq_comp_of_extension hW hW0 hτ0.le hlt.le hF.eqOn hF.cont hF'.eqOn hF'.cont
        (not_mem_swallowedSet_of_time_le hlt.le hx)).symm
    have hB := tendsto_comp_ofReal_of_continuousOn hF'.cont hlim
    have heq : F' ((0 : ℝ) : ℂ) = F c := tendsto_nhds_unique (hB.congr' hcomp) hA
    rw [Complex.ofReal_zero] at heq
    have hH : 0 < (F' 0).im := shift_ext_zero_mem_H hW hW0 hτ0 hlt hK hF'.eqOn hF'.cont
    rw [heq, hreal] at hH
    exact lt_irrefl _ hH
  · have hB := (Complex.continuous_ofReal.tendsto 0).comp hlim
    have hcomp : ∀ᶠ x in l, ((realRevMap W τ x : ℝ) : ℂ) = F x := hout.mono fun x hx =>
      (eq_realRevMap_of_extension hW hT.le hF.eqOn hF.cont hx).symm
    have := tendsto_nhds_unique hA (hB.congr' hcomp)
    simpa using this

/-- **R5.** For a simple reverse hull with boundary extension `F` and swallowed interval
`[a,b]`: `a < 0 < b` and `F a = F b = 0` (blueprint §3.R node R5; Lawler 2005, §4.1, p. 80). -/
theorem revExt_ends (hR3 : ExtExists) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hT : 0 < T) {γ : ℝ → ℂ} (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hγ0 : (γ 0).im = 0) (hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H) (hK : revHull W T = γ '' Ioc 0 1)
    {F : ℂ → ℂ} (hF : RevExt W T γ F) (htip : F 0 = γ 1) {a b : ℝ}
    (hS : swallowedSet W T = Icc a b) : a < 0 ∧ 0 < b ∧ F a = 0 ∧ F b = 0 := by
  have hK' : IsSimpleCurveHull (revHull W T) := ⟨γ, hγc, hγi, hγ0, hγH, hK⟩
  have h0 : (0 : ℝ) ∈ Icc a b := hS ▸ zero_mem_swallowedSet hW0 hT.le
  obtain ⟨hL, hR, -, -⟩ := revExt_real_outside hW hW0 hT hF hS
  have htipH : ¬ (F ((0 : ℝ) : ℂ)).im = 0 := by
    rw [Complex.ofReal_zero, htip]
    exact (show (0 : ℝ) < (γ 1).im from hγH 1 ⟨one_pos, le_rfl⟩).ne'
  -- the right end
  have hbre : (F b).im = 0 := im_eq_zero_of_eventually hF.cont (l := 𝓝[>] b) nhdsWithin_le_nhds
    (eventually_nhdsWithin_of_forall fun x hx => (hR x hx).1)
  have hb : 0 < b := lt_of_le_of_ne h0.2 fun h => htipH (h ▸ hbre)
  have hbS : b ∈ swallowedSet W T := hS ▸ right_mem_Icc.2 (h0.1.trans h0.2)
  obtain ⟨τ, hτ0, hτT, hτ⟩ := exists_hitTime_of_mem hW hT.le hbS (by rw [hW0]; exact hb.ne')
  have houtR : ∀ x, b < x → x ∉ swallowedSet W T := fun x hx hxS => by
    rw [hS] at hxS; exact absurd hxS.2 (not_le.2 hx)
  have hFb := revExt_end_eq_zero hR3 hW hW0 hT hK' hF (l := 𝓝[>] b) nhdsWithin_le_nhds hτ0 hτT
    (eventually_nhdsWithin_of_forall houtR)
    (tendsto_realRevMap_right_end hW (by rw [hW0]; exact hb) hτ fun x hx =>
      not_mem_swallowedSet_of_time_le hτT (houtR x hx)) hbre
  -- the left end
  have hare : (F a).im = 0 := im_eq_zero_of_eventually hF.cont (l := 𝓝[<] a) nhdsWithin_le_nhds
    (eventually_nhdsWithin_of_forall fun x hx => (hL x hx).1)
  have ha : a < 0 := lt_of_le_of_ne h0.1 fun h => htipH (h ▸ hare)
  have haS : a ∈ swallowedSet W T := hS ▸ left_mem_Icc.2 (h0.1.trans h0.2)
  obtain ⟨σ, hσ0, hσT, hσ⟩ := exists_hitTime_of_mem hW hT.le haS (by rw [hW0]; exact ha.ne)
  have houtL : ∀ x, x < a → x ∉ swallowedSet W T := fun x hx hxS => by
    rw [hS] at hxS; exact absurd hxS.1 (not_le.2 hx)
  have hFa := revExt_end_eq_zero hR3 hW hW0 hT hK' hF (l := 𝓝[<] a) nhdsWithin_le_nhds hσ0 hσT
    (eventually_nhdsWithin_of_forall houtL)
    (tendsto_realRevMap_left_end hW (by rw [hW0]; exact ha) hσ fun x hx =>
      not_mem_swallowedSet_of_time_le hσT (houtL x hx)) hare
  exact ⟨ha, hb, hFa, hFb⟩

end CaraR

end QuantumZipper
