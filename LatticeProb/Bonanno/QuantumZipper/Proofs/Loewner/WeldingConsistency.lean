/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.WeldingConsistency at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CoreArc1
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm14.WeldingData
import LatticeProb.Bonanno.QuantumZipper.Zipper.Welding

/-!
# Welding consistency across times (AUDIT-3 M3)

Deterministic Loewner lemmas for a driver `W` whose reverse hull at time `t` is a simple arc
(AUDIT-3, finding M3; `blueprint/CORE_ARC_PLAN.md`):

* `isSimpleCurveHull_revHull_of_le` (L-sub): the reverse hulls at earlier times are simple arcs;
* `zeroMinus_lt_of_lt`, `continuousOn_zeroMinus`, `tendsto_zeroMinus_zero` (L-0m): `s ↦ 0₋(s)`
  is strictly decreasing and continuous on `(0,t]`, with limit `0` at `0⁺`;
* `weldingHom_eq_of_le` (L-wc): `weldingHom W t = weldingHom W s` on `[0₋(s), 0]` for `s ≤ t`;
* `eqOn_of_revMap_eq_general` (L-arc): equal reverse maps at time `t`, with a simple hull, give
  equal drivers on `[0,t]`;
* `eqOn_of_isWeldingDriver` (M3): two welding drivers of the same field at time `t`, the first
  with removable hulls at time `t` and at all rational times, agree on `[0,t]`.

All results assume `Blueprint.RevMapCaratheodory` and the arc structure of Loewner chains,
`LoewnerSubhullsOfArc`, defined here and proved in `CoreArc*.lean`.
-/

noncomputable section

open Set Filter Topology
open scoped ComplexConjugate

namespace QuantumZipper

namespace WeldingConsistency

open Thm14WeldingData

/-- **Arc structure of Loewner chains** (CORE). If the forward hull at time `T` of a continuous
driver started at `0` is a simple arc `γ(0,1]`, then the hulls at earlier times are the initial
subarcs `γ(0, τ r]`, for a continuous, strictly increasing reparametrization `τ` with `τ 0 = 0`,
`τ T = 1`. Moreover the tip is sent to the driving point: `fwdMap A r (γ w) → 0` as `w ↓ τ r`.
Proved in `Proofs/Loewner/CoreArc*.lean` (not a Blueprint item). -/
def LoewnerSubhullsOfArc : Prop :=
  ∀ A : ℝ → ℝ, Continuous A → A 0 = 0 → ∀ T : ℝ, 0 < T → ∀ γ : ℝ → ℂ,
    ContinuousOn γ (Icc 0 1) → InjOn γ (Icc 0 1) → (γ 0).im = 0 →
    (∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H) → fwdHull A T = γ '' Ioc 0 1 →
    ∃ τ : ℝ → ℝ, τ 0 = 0 ∧ τ T = 1 ∧ ContinuousOn τ (Icc 0 T) ∧ StrictMonoOn τ (Icc 0 T) ∧
      (∀ r ∈ Icc (0 : ℝ) T, fwdHull A r = γ '' Ioc 0 (τ r)) ∧
      ∀ r ∈ Ioo (0 : ℝ) T, Tendsto (fun w => fwdMap A r (γ w)) (𝓝[>] (τ r)) (𝓝 0)

/-! ### Simple curve hulls -/

theorem isSimpleCurveHull_initial {γ : ℝ → ℂ} (hγc : ContinuousOn γ (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1)) (hγ0 : (γ 0).im = 0) (hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) : IsSimpleCurveHull (γ '' Ioc 0 ρ) := by
  have hmaps : MapsTo (fun u : ℝ => ρ * u) (Icc 0 1) (Icc 0 1) := fun u hu =>
    ⟨by nlinarith [hu.1], by nlinarith [hu.1, hu.2]⟩
  refine ⟨fun u => γ (ρ * u), hγc.comp (continuousOn_const.mul continuousOn_id) hmaps, ?_,
    by simpa using hγ0, ?_, ?_⟩
  · intro x hx y hy hxy
    exact mul_left_cancel₀ hρ.ne' (hγi (hmaps hx) (hmaps hy) hxy)
  · intro u hu
    exact hγH _ ⟨mul_pos hρ hu.1, by nlinarith [hu.2]⟩
  · ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v / ρ, ⟨div_pos hv.1 hρ, (div_le_one hρ).2 hv.2⟩, ?_⟩
      simp only
      rw [mul_div_cancel₀ _ hρ.ne']
    · rintro ⟨u, hu, rfl⟩
      exact ⟨ρ * u, ⟨mul_pos hρ hu.1, by nlinarith [hu.2]⟩, rfl⟩

/-! ### Carathéodory extensions -/

section Car

variable {W : ℝ → ℝ} {T : ℝ} {F : ℂ → ℂ}

theorem car_mapsTo (hW : Continuous W) (hT : 0 < T) (hF : Blueprint.IsCaratheodoryRevExt W T F) :
    MapsTo F Hbar Hbar :=
  (WeldingUniqueness.glueData_of_caratheodory hW hT hF).mapsHbar

theorem car_bound (hF : Blueprint.IsCaratheodoryRevExt W T F) {C : ℝ}
    (hC : ∀ z ∈ H, ‖revMap W T z - z‖ ≤ C) (x : ℝ) : ‖F x - x‖ ≤ C := by
  have ht := tendsto_revMap_of_car hF x
  have hc : Tendsto (fun y : ℝ => revMap W T (x + y * Complex.I) - (x + y * Complex.I))
      (𝓝[>] 0) (𝓝 (F x - x)) := by
    refine ht.sub ?_
    have : Continuous fun y : ℝ => (x : ℂ) + y * Complex.I := by fun_prop
    have h := this.tendsto 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hc.norm ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  apply hC
  show (0 : ℝ) < ((x : ℂ) + y * Complex.I).im
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one]
  have : (0 : ℝ) < y := hy
  linarith

/-- The Carathéodory extension of a nonempty simple hull: `0₋ < 0 < 0₊` and the tip `F 0` is
in `ℍ`. -/
theorem car_basic (hW : Continuous W) (hT : 0 < T) (hF : Blueprint.IsCaratheodoryRevExt W T F)
    (hne : (revHull W T).Nonempty) :
    zeroMinus W T < 0 ∧ 0 < zeroPlus W T ∧ F 0 ∈ H := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨x, hx, hxp⟩ := hF.2.2.1 (WeldingUniqueness.wu_H_subset_Hbar hp.1)
  have hxR : x.im = 0 := by
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ x.im from hx) with h | h
    · exact h.symm
    · exfalso
      exact hp.2 ⟨x, h, by rw [← hF.1 h]; exact hxp⟩
  have hxe : x = (x.re : ℂ) := Complex.ext rfl (by simp [hxR])
  have hpim : (F x.re).im ≠ 0 := by
    rw [← hxe, hxp]; exact ne_of_gt hp.1
  have h2 : ¬ (x.re ≤ zeroMinus W T ∨ zeroPlus W T ≤ x.re) := (hF.2.2.2.2.2.1 x.re).not.1 hpim
  push Not at h2
  have ha0 := WeldingUniqueness.zeroMinus_nonpos W T
  have hb0 := zeroPlus_nonneg W T
  have ha : zeroMinus W T < 0 := by
    rcases eq_or_lt_of_le ha0 with h | h
    · exfalso
      have : zeroPlus W T = 0 := by rw [← hF.2.2.2.2.1, h, weldingHom_zero]
      linarith [h2.1, h2.2]
    · exact h
  have hb : 0 < zeroPlus W T := by
    by_contra hb
    have hb' : zeroPlus W T = 0 := le_antisymm (not_lt.1 hb) hb0
    have hxI : x.re ∈ Icc (zeroMinus W T) 0 := ⟨h2.1.le, by linarith [h2.2]⟩
    obtain ⟨hφ0, hφF⟩ := weldingHom_mem_of_car hF hxI
    have hφle := weldingHom_le_zeroPlus_of_car hF hxI
    have hφ : weldingHom W T x.re = 0 := le_antisymm (hb' ▸ hφle) hφ0
    rw [hφ] at hφF
    have hre : (F ((0 : ℝ) : ℂ)).im = 0 := (hF.2.2.2.2.2.1 0).2 (Or.inr hb'.le)
    rw [hφF] at hre
    exact hpim hre
  refine ⟨ha, hb, ?_⟩
  have hne : (F ((0 : ℝ) : ℂ)).im ≠ 0 := by
    intro h
    rcases (hF.2.2.2.2.2.1 0).1 h with h' | h' <;> linarith
  have hge : 0 ≤ (F ((0 : ℝ) : ℂ)).im := car_mapsTo hW hT hF (hbar_ofReal 0)
  have : 0 < (F ((0 : ℝ) : ℂ)).im := lt_of_le_of_ne hge (Ne.symm hne)
  have h' : 0 < (F 0).im := by simpa using this
  exact h'

/-- The only nonpositive real point sent to `0` is `0₋`. -/
theorem car_eq_zeroMinus (hF : Blueprint.IsCaratheodoryRevExt W T F) (ha : zeroMinus W T < 0)
    (hb : 0 < zeroPlus W T) {c : ℝ} (hc : c ≤ 0) (hFc : F c = 0) : c = zeroMinus W T := by
  have h := (hF.2.2.2.2.2.2 _ (hbar_ofReal c) _ (hbar_ofReal (zeroMinus W T))).1
    (by rw [hFc, hF.2.2.2.1])
  rcases h with h | ⟨s', hs', ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · exact Complex.ofReal_injective h
  · exfalso
    have e := Complex.ofReal_injective h2
    have h0 := (weldingHom_mem_of_car hF hs').1
    linarith
  · exfalso
    have e1 := Complex.ofReal_injective h1
    have e2 := Complex.ofReal_injective h2
    rw [← e2, hF.2.2.2.2.1] at e1
    linarith

/-- The tip `F 0` of a nonempty simple hull lies in the hull. -/
theorem car_zero_mem_revHull (hW : Continuous W) (hT : 0 < T)
    (hF : Blueprint.IsCaratheodoryRevExt W T F) (hne : (revHull W T).Nonempty) :
    F 0 ∈ revHull W T := by
  obtain ⟨-, -, hF0⟩ := car_basic hW hT hF hne
  refine ⟨hF0, ?_⟩
  rintro ⟨z, hz, hzF⟩
  have h := (hF.2.2.2.2.2.2 z (WeldingUniqueness.wu_H_subset_Hbar hz) ((0 : ℝ) : ℂ)
    (hbar_ofReal 0)).1 (by rw [hF.1 hz, hzF]; simp)
  have hz' : (0 : ℝ) < z.im := hz
  rcases h with h | ⟨s', -, ⟨h1, -⟩ | ⟨h1, -⟩⟩
  · rw [h] at hz'; simp at hz'
  · rw [h1] at hz'; simp at hz'
  · rw [h1] at hz'; simp at hz'

end Car

/-! ### The chain decomposition `revMap W t = revMap W_s (t-s) ∘ revMap W s` -/

section Chain

variable {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
include hW hW0

/-- The shifted driver `W_s = W(s + ·) - W s` is the time reversal on `[0, t-s]` of the
time reversal of `W` on `[0,t]`. -/
theorem trev_trev_eq {s t : ℝ} :
    ArcDriver.trev (ArcDriver.trev W t) (t - s) = fun r => W (s + r) - W s := by
  funext r
  simp only [ArcDriver.trev]
  rw [show t - (t - s - r) = s + r by ring, show t - (t - s) = s by ring]
  ring

theorem continuous_trev' {t : ℝ} : Continuous (ArcDriver.trev W t) :=
  ArcDriver.continuous_trev hW t

theorem trev_zero' {t : ℝ} : ArcDriver.trev W t 0 = 0 := ArcDriver.trev_zero W t

theorem revHull_eq_fwdHull_trev {t : ℝ} (ht : 0 < t) :
    revHull W t = fwdHull (ArcDriver.trev W t) t :=
  LoewnerAlgebra.revHull_eq_fwdHull_timeRev W hW hW0 ht

theorem revHull_shift_eq {s t : ℝ} (hst : s < t) :
    revHull (fun r => W (s + r) - W s) (t - s) = fwdHull (ArcDriver.trev W t) (t - s) := by
  rw [← trev_trev_eq hW hW0]
  exact ArcDriver.revHull_trev (continuous_trev' hW hW0) (trev_zero' hW hW0) (by linarith)

theorem revMap_comp {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {z : ℂ} (hz : z ∈ H) :
    revMap W t z = revMap (fun r => W (s + r) - W s) (t - s) (revMap W s z) := by
  have := ReverseFlow.revMap_add W hW z hz hs (sub_nonneg.2 hst)
  rwa [show s + (t - s) = t by ring] at this

theorem shift_spec {s t : ℝ} (hst : s < t) {z : ℂ} (hz : z ∈ H) :
    revMap (fun r => W (s + r) - W s) (t - s) z ∈ H \ fwdHull (ArcDriver.trev W t) (t - s) ∧
      fwdMap (ArcDriver.trev W t) (t - s) (revMap (fun r => W (s + r) - W s) (t - s) z) = z := by
  rw [← trev_trev_eq hW hW0]
  exact ArcDriver.revMap_trev_spec (continuous_trev' hW hW0) (trev_zero' hW hW0)
    (by linarith) hz

theorem shift_inv_spec {s t : ℝ} (hst : s < t) {p : ℂ}
    (hp : p ∈ H \ fwdHull (ArcDriver.trev W t) (t - s)) :
    fwdMap (ArcDriver.trev W t) (t - s) p ∈ H ∧
      revMap (fun r => W (s + r) - W s) (t - s) (fwdMap (ArcDriver.trev W t) (t - s) p) = p := by
  rw [← trev_trev_eq hW hW0]
  exact ArcDriver.fwdMap_trev_spec (continuous_trev' hW hW0) (trev_zero' hW hW0)
    (by linarith) hp

end Chain

/-! ### The arc data of a simple reverse hull -/

theorem exists_arc_data (hArc : LoewnerSubhullsOfArc) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 < t) (hK : IsSimpleCurveHull (revHull W t)) :
    ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Icc 0 1) ∧ (γ 0).im = 0 ∧
      (∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H) ∧ revHull W t = γ '' Ioc 0 1 ∧
      ∃ τ : ℝ → ℝ, τ 0 = 0 ∧ τ t = 1 ∧ ContinuousOn τ (Icc 0 t) ∧ StrictMonoOn τ (Icc 0 t) ∧
        (∀ r ∈ Icc (0 : ℝ) t, fwdHull (ArcDriver.trev W t) r = γ '' Ioc 0 (τ r)) ∧
        ∀ r ∈ Ioo (0 : ℝ) t,
          Tendsto (fun w => fwdMap (ArcDriver.trev W t) r (γ w)) (𝓝[>] (τ r)) (𝓝 0) := by
  obtain ⟨γ, hγc, hγi, hγ0, hγH, hKγ⟩ := hK
  refine ⟨γ, hγc, hγi, hγ0, hγH, hKγ, ?_⟩
  exact hArc _ (continuous_trev' hW hW0) (trev_zero' hW hW0) t ht γ hγc hγi hγ0 hγH
    (by rw [← revHull_eq_fwdHull_trev hW hW0 ht, hKγ])

/-! ### L-sub -/

/-- **L-sub.** Earlier reverse hulls of a simple arc are simple arcs. -/
theorem isSimpleCurveHull_revHull_of_le (hArc : LoewnerSubhullsOfArc) {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 < t)
    (hK : IsSimpleCurveHull (revHull W t)) {s : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    IsSimpleCurveHull (revHull W s) := by
  rcases eq_or_lt_of_le hst with rfl | hst
  · exact hK
  obtain ⟨γ, hγc, hγi, hγ0, hγH, hKγ, τ, hτ0, hτt, hτc, hτm, hτK, hτtip⟩ :=
    exists_arc_data hArc hW hW0 ht hK
  set h := t - s with hh
  have hh0 : 0 < h := by rw [hh]; linarith
  have hht : h < t := by rw [hh]; linarith
  have hhI : h ∈ Icc (0 : ℝ) t := ⟨hh0.le, hht.le⟩
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht.le⟩
  have htI : t ∈ Icc (0 : ℝ) t := ⟨ht.le, le_rfl⟩
  have hτpos : 0 < τ h := hτ0 ▸ hτm h0I hhI hh0
  have hτ1 : τ h < 1 := hτt ▸ hτm hhI htI hht
  set ρ := τ h with hρ
  set A := ArcDriver.trev W t with hA
  have hAc : Continuous A := continuous_trev' hW hW0
  have hB : fwdHull A h = γ '' Ioc 0 ρ := hτK h hhI
  -- the arc
  set E : ℝ → ℂ := fun u => fwdMap A h (γ (ρ + u * (1 - ρ))) with hE
  set δ : ℝ → ℂ := fun u => if u = 0 then 0 else E u with hδ
  have hmem : ∀ u ∈ Ioc (0 : ℝ) 1, ρ + u * (1 - ρ) ∈ Ioc ρ 1 := fun u hu =>
    ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
  have hnotB : ∀ v ∈ Ioc ρ 1, γ v ∈ H \ fwdHull A h := by
    intro v hv
    refine ⟨hγH v ⟨by linarith [hv.1], hv.2⟩, ?_⟩
    rw [hB]
    rintro ⟨v', hv', hvv⟩
    have := hγi ⟨by linarith [hv'.1], by linarith [hv'.2]⟩ ⟨by linarith [hv.1], hv.2⟩ hvv
    linarith [hv'.2, hv.1]
  have hopen : IsOpen (H \ fwdHull A h) := FwdHolo.isOpen_compl_fwdHull hAc hh0.le
  have hfc : ContinuousOn (fwdMap A h) (H \ fwdHull A h) :=
    (FwdHolo.differentiableOn_fwdMap hAc hh0.le).continuousOn
  have haff : Continuous fun u : ℝ => ρ + u * (1 - ρ) := by fun_prop
  refine ⟨δ, ?_, ?_, by simp [hδ], ?_, ?_⟩
  · -- continuity
    intro u hu
    rcases eq_or_lt_of_le hu.1 with h0 | hpos
    · subst h0
      refine (continuousWithinAt_Ioi_iff_Ici.1 ?_).mono (fun x hx => hx.1)
      show Tendsto δ (𝓝[>] 0) (𝓝 (δ 0))
      have hδ0 : δ 0 = 0 := by simp [hδ]
      rw [hδ0]
      have hlim : Tendsto (fun u : ℝ => ρ + u * (1 - ρ)) (𝓝[>] 0) (𝓝[>] ρ) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have := haff.tendsto 0
          simpa using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with u hu
          show ρ < ρ + u * (1 - ρ)
          nlinarith [show (0 : ℝ) < u from hu]
      have := (hτtip h ⟨hh0, hht⟩).comp hlim
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu0 : u ≠ 0 := ne_of_gt hu
      simp [hδ, hu0, hE]
    · have hE' : ContinuousWithinAt E (Icc 0 1) u := by
        have hv := hmem u ⟨hpos, hu.2⟩
        have hγv : ContinuousWithinAt (fun u => γ (ρ + u * (1 - ρ))) (Icc 0 1) u := by
          refine ContinuousWithinAt.comp (g := γ) (f := fun u : ℝ => ρ + u * (1 - ρ))
            (hγc (ρ + u * (1 - ρ)) ⟨by linarith [hv.1], hv.2⟩) haff.continuousWithinAt ?_
          intro x hx
          exact ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩
        exact ContinuousAt.comp_continuousWithinAt (g := fwdMap A h)
          (f := fun u => γ (ρ + u * (1 - ρ)))
          ((hfc _ (hnotB _ hv)).continuousAt (hopen.mem_nhds (hnotB _ hv))) hγv
      refine hE'.congr_of_eventuallyEq ?_ (by simp [hδ, hpos.ne', hE])
      filter_upwards [self_mem_nhdsWithin, (lt_mem_nhds hpos).filter_mono nhdsWithin_le_nhds]
        with x _ hx
      simp [hδ, hx.ne', hE]
  · -- injectivity
    intro x hx y hy hxy
    have hE_H : ∀ u ∈ Ioc (0 : ℝ) 1, E u ∈ H := fun u hu =>
      FwdHolo.mapsTo_fwdMap hAc hh0.le (hnotB _ (hmem u hu))
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0 <;> rcases eq_or_lt_of_le hy.1 with hy0 | hy0
    · rw [← hx0, ← hy0]
    · exfalso
      have h1 := hE_H y ⟨hy0, hy.2⟩
      simp only [hδ, ← hx0, ↓reduceIte, hy0.ne', hE] at hxy
      simp only [hE] at h1
      rw [← hxy] at h1
      exact (lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h1))
    · exfalso
      have h1 := hE_H x ⟨hx0, hx.2⟩
      simp only [hδ, ← hy0, ↓reduceIte, hx0.ne', hE] at hxy
      simp only [hE] at h1
      rw [hxy] at h1
      exact (lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h1))
    · simp only [hδ, hx0.ne', hy0.ne', ↓reduceIte, hE] at hxy
      have hvx := hmem x ⟨hx0, hx.2⟩
      have hvy := hmem y ⟨hy0, hy.2⟩
      have h1 := FwdHolo.injOn_fwdMap hAc hh0.le (hnotB _ hvx) (hnotB _ hvy) hxy
      have h2 := hγi ⟨by linarith [hvx.1], hvx.2⟩ ⟨by linarith [hvy.1], hvy.2⟩ h1
      have h3 : (x - y) * (1 - ρ) = 0 := by linarith
      rcases mul_eq_zero.1 h3 with h4 | h4
      · linarith
      · exfalso; linarith
  · intro u hu
    simp only [hδ, hu.1.ne', ↓reduceIte, hE]
    exact FwdHolo.mapsTo_fwdMap hAc hh0.le (hnotB _ (hmem u hu))
  · -- the hull
    ext w
    constructor
    · rintro ⟨hwH, hwn⟩
      obtain ⟨hpB, hpinv⟩ := shift_spec hW hW0 hst hwH
      set p := revMap (fun r => W (s + r) - W s) (t - s) w with hp
      have hpK : p ∈ revHull W t := by
        refine ⟨hpB.1, ?_⟩
        rintro ⟨z, hz, hzp⟩
        rw [revMap_comp hW hW0 hs.le hst.le hz] at hzp
        have hzs : revMap W s z ∈ H := lt_of_lt_of_le hz (im_le_im_revMap W hW z hz hs.le)
        have := injOn_revMap _ (by fun_prop : Continuous fun r => W (s + r) - W s)
          (sub_nonneg.2 hst.le) hzs hwH hzp
        exact hwn ⟨z, hz, this⟩
      rw [hKγ] at hpK
      obtain ⟨v, hv, hvp⟩ := hpK
      have hvρ : ρ < v := by
        by_contra hle
        push Not at hle
        exact hpB.2 (by rw [hB]; exact ⟨v, ⟨hv.1, hle⟩, hvp⟩)
      have h1ρ : 0 < 1 - ρ := by linarith
      refine ⟨(v - ρ) / (1 - ρ), ⟨div_pos (by linarith) h1ρ, (div_le_one h1ρ).2 (by linarith [hv.2])⟩,
        ?_⟩
      have hne : (v - ρ) / (1 - ρ) ≠ 0 := (div_pos (by linarith) h1ρ).ne'
      simp only [hδ, hne, ↓reduceIte, hE]
      rw [show ρ + (v - ρ) / (1 - ρ) * (1 - ρ) = v by field_simp; ring, hvp]
      exact hpinv
    · rintro ⟨u, hu, rfl⟩
      have hv := hmem u hu
      set v := ρ + u * (1 - ρ)
      have hpB := hnotB v hv
      obtain ⟨hzH, hzp⟩ := shift_inv_spec hW hW0 hst hpB
      simp only [hδ, hu.1.ne', ↓reduceIte, hE]
      refine ⟨hzH, ?_⟩
      rintro ⟨y, hy, hyz⟩
      have hγK : γ v ∈ revHull W t := by rw [hKγ]; exact ⟨v, ⟨by linarith [hv.1], hv.2⟩, rfl⟩
      apply hγK.2
      refine ⟨y, hy, ?_⟩
      rw [revMap_comp hW hW0 hs.le hst.le hy, hyz, hzp]

theorem simpleCurveHull_nonempty {K : Set ℂ} (hK : IsSimpleCurveHull K) : K.Nonempty := by
  obtain ⟨γ, -, -, -, -, rfl⟩ := hK
  exact ⟨γ 1, 1, ⟨one_pos, le_rfl⟩, rfl⟩

/-! ### The base hulls and the composition of Carathéodory extensions -/

theorem base_simple (hArc : LoewnerSubhullsOfArc) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 < t) (hK : IsSimpleCurveHull (revHull W t)) {s : ℝ}
    (hs : 0 < s) (hst : s < t) :
    IsSimpleCurveHull (revHull (fun r => W (s + r) - W s) (t - s)) ∧
      (revHull (fun r => W (s + r) - W s) (t - s)).Nonempty := by
  obtain ⟨γ, hγc, hγi, hγ0, hγH, -, τ, hτ0, hτt, -, hτm, hτK, -⟩ :=
    exists_arc_data hArc hW hW0 ht hK
  have hhI : t - s ∈ Icc (0 : ℝ) t := ⟨by linarith, by linarith⟩
  have hτpos : 0 < τ (t - s) := hτ0 ▸ hτm ⟨le_rfl, ht.le⟩ hhI (by linarith)
  have hτ1 : τ (t - s) ≤ 1 := hτt ▸ hτm.monotoneOn hhI ⟨ht.le, le_rfl⟩ (by linarith)
  rw [revHull_shift_eq hW hW0 hst, hτK _ hhI]
  exact ⟨isSimpleCurveHull_initial hγc hγi hγ0 hγH hτpos hτ1,
    ⟨γ (τ (t - s)), τ (t - s), ⟨hτpos, le_rfl⟩, rfl⟩⟩

theorem car_comp {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {s t : ℝ} (hs : 0 < s)
    (hst : s < t) {Ft Fs FG : ℂ → ℂ} (hFt : Blueprint.IsCaratheodoryRevExt W t Ft)
    (hFs : Blueprint.IsCaratheodoryRevExt W s Fs)
    (hFG : Blueprint.IsCaratheodoryRevExt (fun r => W (s + r) - W s) (t - s) FG) :
    ∀ x : ℝ, Ft x = FG (Fs x) := by
  have heq : EqOn Ft (FG ∘ Fs) Hbar := by
    refine Set.EqOn.of_subset_closure (s := H) ?_ hFt.2.1
      (hFG.2.1.comp hFs.2.1 (car_mapsTo hW hs hFs)) WeldingUniqueness.wu_H_subset_Hbar ?_
    · intro z hz
      have hzs : revMap W s z ∈ H := lt_of_lt_of_le hz (im_le_im_revMap W hW z hz hs.le)
      simp only [Function.comp]
      rw [hFt.1 hz, hFs.1 hz, hFG.1 hzs, revMap_comp hW hW0 hs.le hst.le hz]
    · show Hbar ⊆ closure {z : ℂ | 0 < z.im}
      rw [Complex.closure_setOfPred_lt_im]
      exact fun z hz => hz
  intro x
  exact heq (hbar_ofReal x)

/-! ### L-0m and L-wc -/

/-- **L-0m (monotonicity).** `s ↦ 0₋(s)` is strictly decreasing. -/
theorem zeroMinus_lt_of_lt (hCar : Blueprint.RevMapCaratheodory)
    (hArc : LoewnerSubhullsOfArc) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 < t) (hK : IsSimpleCurveHull (revHull W t)) {s : ℝ} (hs : 0 < s) (hst : s < t) :
    zeroMinus W t < zeroMinus W s := by
  have hKs := isSimpleCurveHull_revHull_of_le hArc hW hW0 ht hK hs hst.le
  obtain ⟨Ft, hFt⟩ := hCar W hW hW0 t ht hK
  obtain ⟨Fs, hFs⟩ := hCar W hW hW0 s hs hKs
  obtain ⟨hBs, hBne⟩ := base_simple hArc hW hW0 ht hK hs hst
  have hWs : Continuous fun r => W (s + r) - W s := by fun_prop
  obtain ⟨FG, hFG⟩ := hCar _ hWs (by simp) (t - s) (by linarith) hBs
  obtain ⟨-, -, hFG0⟩ := car_basic hWs (by linarith) hFG hBne
  have hc := car_comp hW hW0 hs hst hFt hFs hFG (zeroMinus W s)
  rw [hFs.2.2.2.1] at hc
  have him : (Ft (zeroMinus W s)).im ≠ 0 := by rw [hc]; exact ne_of_gt hFG0
  have h2 : ¬ (zeroMinus W s ≤ zeroMinus W t ∨ zeroPlus W t ≤ zeroMinus W s) :=
    (hFt.2.2.2.2.2.1 _).not.1 him
  push Not at h2
  exact h2.1

/-- **L-wc.** The welding homeomorphisms are consistent across times. -/
theorem weldingHom_eq_of_le (hCar : Blueprint.RevMapCaratheodory)
    (hArc : LoewnerSubhullsOfArc) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 < t) (hK : IsSimpleCurveHull (revHull W t)) {s : ℝ} (hs : 0 < s) (hst : s ≤ t)
    {x : ℝ} (hx : x ∈ Icc (zeroMinus W s) 0) : weldingHom W t x = weldingHom W s x := by
  rcases eq_or_lt_of_le hst with rfl | hst
  · rfl
  have hKs := isSimpleCurveHull_revHull_of_le hArc hW hW0 ht hK hs hst.le
  obtain ⟨Ft, hFt⟩ := hCar W hW hW0 t ht hK
  obtain ⟨Fs, hFs⟩ := hCar W hW hW0 s hs hKs
  obtain ⟨hBs, -⟩ := base_simple hArc hW hW0 ht hK hs hst
  have hWs : Continuous fun r => W (s + r) - W s := by fun_prop
  obtain ⟨FG, hFG⟩ := hCar _ hWs (by simp) (t - s) (by linarith) hBs
  have hlt := zeroMinus_lt_of_lt hCar hArc hW hW0 ht hK hs hst
  obtain ⟨hy0, hyF⟩ := weldingHom_mem_of_car hFs hx
  have hxt : x ∈ Icc (zeroMinus W t) 0 := ⟨hlt.le.trans hx.1, hx.2⟩
  symm
  refine eq_weldingHom_of_car hFt hxt hy0 ?_
  rw [car_comp hW hW0 hs hst hFt hFs hFG, car_comp hW hW0 hs hst hFt hFs hFG x, hyF]

theorem exists_small {W : ℝ → ℝ} (hW : Continuous W) (p : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : ℝ, 0 < h → h < δ →
      (∀ r ∈ Icc (-h) h, |W (p + r) - W p| ≤ ε) ∧ Real.sqrt h ≤ ε := by
  obtain ⟨δ₁, hδ₁, hc⟩ := Metric.continuous_iff.1 hW p ε hε
  refine ⟨min δ₁ (ε ^ 2), by positivity, fun h hh hδ => ⟨fun r hr => ?_, ?_⟩⟩
  · have hd : dist (p + r) p < δ₁ := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_lt]
      constructor <;> linarith [hr.1, hr.2, min_le_left δ₁ (ε ^ 2)]
    have := hc (p + r) hd
    rw [Real.dist_eq] at this
    exact this.le
  · rw [show ε = Real.sqrt (ε ^ 2) by rw [Real.sqrt_sq hε.le]]
    exact Real.sqrt_le_sqrt (by linarith [min_le_right δ₁ (ε ^ 2)])

/-- **L-0m (limit at `0⁺`).** -/
theorem tendsto_zeroMinus_zero (hCar : Blueprint.RevMapCaratheodory)
    (hArc : LoewnerSubhullsOfArc) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 < t) (hK : IsSimpleCurveHull (revHull W t)) :
    Tendsto (zeroMinus W) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := exists_small hW 0 (ε := ε / 40) (by positivity)
  refine ⟨min δ t, lt_min hδ ht, fun {h} hh hdist => ?_⟩
  have hh0 : 0 < h := hh
  have hlt : h < min δ t := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hh0] at hdist; exact hdist
  obtain ⟨hosc, hsq⟩ := hsmall h hh0 (lt_of_lt_of_le hlt (min_le_left _ _))
  have hKh := isSimpleCurveHull_revHull_of_le hArc hW hW0 ht hK hh0
    (lt_of_lt_of_le hlt (min_le_right _ _)).le
  obtain ⟨F, hF⟩ := hCar W hW hW0 h hh0 hKh
  have hM : ∀ r ∈ Icc (0 : ℝ) h, |W r| ≤ ε / 40 := fun r hr => by
    have := hosc r ⟨by linarith [hr.1], hr.2⟩
    simpa [hW0] using this
  have hb := car_bound hF (fun z hz => CoreArc.norm_revMap_sub_le hW hW0 hh0 hM hz)
    (zeroMinus W h)
  rw [hF.2.2.2.1, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs] at hb
  rw [Real.dist_eq, sub_zero]
  linarith

/-- **L-0m (continuity from the right).** -/
theorem tendsto_zeroMinus_right (hCar : Blueprint.RevMapCaratheodory)
    (hArc : LoewnerSubhullsOfArc) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 < t) (hK : IsSimpleCurveHull (revHull W t)) {s : ℝ} (hs : 0 < s) (hst : s < t) :
    Tendsto (zeroMinus W) (𝓝[>] s) (𝓝 (zeroMinus W s)) := by
  have hKs := isSimpleCurveHull_revHull_of_le hArc hW hW0 ht hK hs hst.le
  obtain ⟨Fs, hFs⟩ := hCar W hW hW0 s hs hKs
  obtain ⟨has, hbs, -⟩ := car_basic hW hs hFs (simpleCurveHull_nonempty hKs)
  have hg : Tendsto (fun t' => Fs (zeroMinus W t')) (𝓝[>] s) (𝓝 0) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := exists_small hW s (ε := ε / 40) (by positivity)
    refine ⟨min δ (t - s), lt_min hδ (by linarith), fun {t'} ht' hdist => ?_⟩
    have ht's : s < t' := ht'
    have hlt : t' - s < min δ (t - s) := by
      rw [Real.dist_eq, abs_of_pos (by linarith)] at hdist; exact hdist
    have ht't : t' < t := by linarith [min_le_right δ (t - s)]
    obtain ⟨hosc, hsq⟩ := hsmall (t' - s) (by linarith) (lt_of_lt_of_le hlt (min_le_left _ _))
    have hKt' := isSimpleCurveHull_revHull_of_le hArc hW hW0 ht hK (by linarith) ht't.le
    obtain ⟨Ft', hFt'⟩ := hCar W hW hW0 t' (by linarith) hKt'
    obtain ⟨hBs, -⟩ := base_simple hArc hW hW0 (by linarith : 0 < t') hKt' hs ht's
    have hWs : Continuous fun r => W (s + r) - W s := by fun_prop
    obtain ⟨FG, hFG⟩ := hCar _ hWs (by simp) (t' - s) (by linarith) hBs
    have hc := car_comp hW hW0 hs ht's hFt' hFs hFG (zeroMinus W t')
    rw [hFt'.2.2.2.1] at hc
    have hlt' := zeroMinus_lt_of_lt hCar hArc hW hW0 (by linarith) hKt' hs ht's
    have hreal : (Fs (zeroMinus W t')).im = 0 := (hFs.2.2.2.2.2.1 _).2 (Or.inl hlt'.le)
    have hye : Fs (zeroMinus W t') = ((Fs (zeroMinus W t')).re : ℂ) :=
      Complex.ext rfl (by simp [hreal])
    have hM : ∀ r ∈ Icc (0 : ℝ) (t' - s), |(fun r => W (s + r) - W s) r| ≤ ε / 40 :=
      fun r hr => hosc r ⟨by linarith [hr.1], hr.2⟩
    have hb := car_bound hFG
      (fun z hz => CoreArc.norm_revMap_sub_le hWs (by simp) (by linarith) hM hz)
      (Fs (zeroMinus W t')).re
    rw [← hye, ← hc, zero_sub, norm_neg] at hb
    rw [dist_zero_right]
    linarith
  refine (isCompact_Icc (a := zeroMinus W t) (b := zeroMinus W s)).tendsto_nhds_of_unique_mapClusterPt
    ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT hst] with t' ht'
    exact ⟨(zeroMinus_lt_of_lt hCar hArc hW hW0 ht hK (by linarith [ht'.1]) ht'.2).le,
      (zeroMinus_lt_of_lt hCar hArc hW hW0 (by linarith [ht'.1])
        (isSimpleCurveHull_revHull_of_le hArc hW hW0 ht hK (by linarith [ht'.1]) ht'.2.le)
        hs ht'.1).le⟩
  · intro c hc hcl
    have hFsc := continuous_car_real hFs
    have h1 : MapClusterPt (Fs c) (𝓝[>] s) ((fun x : ℝ => Fs x) ∘ zeroMinus W) :=
      hcl.continuousAt_comp (f := fun x : ℝ => Fs x) hFsc.continuousAt
    have h3 : ClusterPt (Fs c) (𝓝 0) := ClusterPt.mono h1 hg
    exact car_eq_zeroMinus hFs has hbs (hc.2.trans (WeldingUniqueness.zeroMinus_nonpos W s))
      (eq_of_nhds_neBot h3)

/-- **L-0m (continuity from the left).** -/
theorem tendsto_zeroMinus_left (hCar : Blueprint.RevMapCaratheodory)
    (hArc : LoewnerSubhullsOfArc) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 < t) (hK : IsSimpleCurveHull (revHull W t)) {s : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    Tendsto (zeroMinus W) (𝓝[<] s) (𝓝 (zeroMinus W s)) := by
  have hKs := isSimpleCurveHull_revHull_of_le hArc hW hW0 ht hK hs hst
  obtain ⟨Fs, hFs⟩ := hCar W hW hW0 s hs hKs
  obtain ⟨has, hbs, -⟩ := car_basic hW hs hFs (simpleCurveHull_nonempty hKs)
  have hg : Tendsto (fun s' => Fs (zeroMinus W s')) (𝓝[<] s) (𝓝 0) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := exists_small hW s (ε := ε / 16) (by positivity)
    refine ⟨min δ s, lt_min hδ hs, fun {s'} hs' hdist => ?_⟩
    have hs's : s' < s := hs'
    have hlt : s - s' < min δ s := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith)] at hdist; exact hdist
    have hs'0 : 0 < s' := by linarith [min_le_right δ s]
    obtain ⟨hosc, hsq⟩ := hsmall (s - s') (by linarith) (lt_of_lt_of_le hlt (min_le_left _ _))
    have hKs' := isSimpleCurveHull_revHull_of_le hArc hW hW0 ht hK hs'0 (by linarith)
    obtain ⟨Fs', hFs'⟩ := hCar W hW hW0 s' hs'0 hKs'
    obtain ⟨hBs, hBne⟩ := base_simple hArc hW hW0 hs hKs hs'0 hs's
    have hWs : Continuous fun r => W (s' + r) - W s' := by fun_prop
    obtain ⟨FG, hFG⟩ := hCar _ hWs (by simp) (s - s') (by linarith) hBs
    have hc := car_comp hW hW0 hs'0 hs's hFs hFs' hFG (zeroMinus W s')
    rw [hFs'.2.2.2.1] at hc
    have hmem := car_zero_mem_revHull hWs (by linarith) hFG hBne
    rw [revHull_shift_eq hW hW0 hs's] at hmem
    have hM : ∀ r ∈ Icc (0 : ℝ) (s - s'), |ArcDriver.trev W s r| ≤ ε / 16 := by
      intro r hr
      have := hosc (-r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
      simp only [ArcDriver.trev]
      rwa [show s + -r = s - r by ring] at this
    have hbound : ‖FG 0‖ ≤ 4 * (ε / 16 + Real.sqrt (s - s')) := by
      by_contra hc'
      push Not at hc'
      exact (CoreArc.fwd_far (continuous_trev' hW hW0) (by linarith) hM hmem.1 hc').1 hmem
    rw [hc, dist_zero_right]
    linarith
  refine (isCompact_Icc (a := zeroMinus W s) (b := 0)).tendsto_nhds_of_unique_mapClusterPt ?_ ?_
  · filter_upwards [Ioo_mem_nhdsLT hs] with s' hs'
    exact ⟨(zeroMinus_lt_of_lt hCar hArc hW hW0 hs hKs hs'.1 hs'.2).le,
      WeldingUniqueness.zeroMinus_nonpos W s'⟩
  · intro c hc hcl
    have hFsc := continuous_car_real hFs
    have h1 : MapClusterPt (Fs c) (𝓝[<] s) ((fun x : ℝ => Fs x) ∘ zeroMinus W) :=
      hcl.continuousAt_comp (f := fun x : ℝ => Fs x) hFsc.continuousAt
    have h3 : ClusterPt (Fs c) (𝓝 0) := ClusterPt.mono h1 hg
    exact car_eq_zeroMinus hFs has hbs hc.2 (eq_of_nhds_neBot h3)

/-- **L-0m (continuity).** -/
theorem continuousOn_zeroMinus (hCar : Blueprint.RevMapCaratheodory)
    (hArc : LoewnerSubhullsOfArc) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 < t) (hK : IsSimpleCurveHull (revHull W t)) :
    ContinuousOn (zeroMinus W) (Ioc 0 t) := by
  intro s hs
  have hl : ContinuousWithinAt (zeroMinus W) (Iio s) s :=
    tendsto_zeroMinus_left hCar hArc hW hW0 ht hK hs.1 hs.2
  rcases eq_or_lt_of_le hs.2 with hst | hst
  · exact (continuousWithinAt_Iio_iff_Iic.1 hl).mono fun x hx => hst ▸ hx.2
  · have hr : ContinuousWithinAt (zeroMinus W) (Ioi s) s :=
      tendsto_zeroMinus_right hCar hArc hW hW0 ht hK hs.1 hst
    exact (continuousAt_iff_continuous_left_right.2
      ⟨continuousWithinAt_Iio_iff_Iic.1 hl, continuousWithinAt_Ioi_iff_Ici.1 hr⟩).continuousWithinAt

/-- Intermediate values of `0₋`. -/
theorem exists_zeroMinus_eq (hCar : Blueprint.RevMapCaratheodory)
    (hArc : LoewnerSubhullsOfArc) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 < t) (hK : IsSimpleCurveHull (revHull W t)) {a : ℝ} (ha : zeroMinus W t ≤ a)
    (ha0 : a < 0) : ∃ s ∈ Ioc (0 : ℝ) t, zeroMinus W s = a := by
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), a < zeroMinus W ε ∧ ε ∈ Ioo 0 t :=
    ((tendsto_zeroMinus_zero hCar hArc hW hW0 ht hK).eventually (lt_mem_nhds ha0)).and
      (Ioo_mem_nhdsGT ht)
  obtain ⟨ε, hεa, hε⟩ := hev.exists
  obtain ⟨s, hs, hsa⟩ := intermediate_value_Icc' hε.2.le
    ((continuousOn_zeroMinus hCar hArc hW hW0 ht hK).mono fun x hx => ⟨hε.1.trans_le hx.1, hx.2⟩)
    ⟨ha, hεa.le⟩
  exact ⟨s, ⟨hε.1.trans_le hs.1, hs.2⟩, hsa⟩

/-! ### L-arc for a simple final hull -/

/-- **L-arc.** Equal reverse maps at time `T`, with a simple hull, give equal drivers on
`[0,T]`. -/
theorem eqOn_of_revMap_eq_general (hCar : Blueprint.RevMapCaratheodory)
    (hArc : LoewnerSubhullsOfArc) {W W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W')
    (hW0 : W 0 = 0) (hW'0 : W' 0 = 0) {T : ℝ} (hT : 0 < T)
    (hK : IsSimpleCurveHull (revHull W T)) (h : EqOn (revMap W' T) (revMap W T) H) :
    EqOn W W' (Icc 0 T) := by
  obtain ⟨γ, hγc, hγi, hγ0, hγH, hKγ, τ, hτ0, hτT, hτc, hτm, hτK, -⟩ :=
    exists_arc_data hArc hW hW0 hT hK
  have hrevHull : revHull W' T = revHull W T := by unfold revHull; rw [h.image_eq]
  have hfin' : fwdHull (ArcDriver.trev W' T) T = γ '' Ioc 0 1 := by
    rw [← revHull_eq_fwdHull_trev hW' hW'0 hT, hrevHull, hKγ]
  obtain ⟨τ', hτ'0, hτ'T, -, hτ'm, hτ'K, -⟩ := hArc _ (continuous_trev' hW' hW'0)
    (trev_zero' hW' hW'0) T hT γ hγc hγi hγ0 hγH hfin'
  have hV := continuous_trev' hW hW0 (t := T)
  have hV' := continuous_trev' hW' hW'0 (t := T)
  have hfin : fwdHull (ArcDriver.trev W' T) T = fwdHull (ArcDriver.trev W T) T := by
    rw [← revHull_eq_fwdHull_trev hW' hW'0 hT, ← revHull_eq_fwdHull_trev hW hW0 hT, hrevHull]
  have hrel : ∀ s ∈ Ioc 0 T, ∀ w ∈ H \ fwdHull (ArcDriver.trev W T) s,
      fwdMap (ArcDriver.trev W' T) s w + ArcDriver.trev W' T s =
        fwdMap (ArcDriver.trev W T) s w + ArcDriver.trev W T s := by
    intro s hs
    have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
    have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    have hTI : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
    have hτ'pos : 0 < τ' s := hτ'0 ▸ hτ'm h0I hsI hs.1
    have hτ'1 : τ' s ≤ 1 := hτ'T ▸ hτ'm.monotoneOn hsI hTI hs.2
    obtain ⟨r, hr, hτr⟩ := intermediate_value_Icc hT.le hτc
      (show τ' s ∈ Icc (τ 0) (τ T) by rw [hτ0, hτT]; exact ⟨hτ'pos.le, hτ'1⟩)
    have hr0 : 0 < r := by
      rcases eq_or_lt_of_le hr.1 with h0 | h0
      · rw [← h0, hτ0] at hτr; linarith
      · exact h0
    have hKt : fwdHull (ArcDriver.trev W' T) s = fwdHull (ArcDriver.trev W T) r := by
      rw [hτ'K s hsI, hτK r hr, hτr]
    have hsimple : IsSimpleCurveHull (fwdHull (ArcDriver.trev W T) r) := by
      rw [hτK r hr, hτr]
      exact isSimpleCurveHull_initial hγc hγi hγ0 hγH hτ'pos hτ'1
    obtain ⟨hrs, hmap⟩ := ArcDriver.fwdHull_eq_imp hCar hV hV' (trev_zero' hW hW0)
      (trev_zero' hW' hW'0) hr0 hs.1 hsimple hKt
    subst hrs
    exact hmap
  have hVV := ArcDriver.eqOn_of_fwdMap_rel hV hV' (trev_zero' hW hW0) (trev_zero' hW' hW'0) hT
    hfin hrel
  have hWT : W T = W' T := by
    have := hVV ⟨hT.le, le_rfl⟩
    simp only [ArcDriver.trev, sub_self, hW0, hW'0] at this
    linarith
  intro r hr
  have := hVV ⟨sub_nonneg.2 hr.2, by linarith [hr.1]⟩
  simp only [ArcDriver.trev, sub_sub_cancel] at this
  linarith

/-! ### Weld-driver uniqueness (AUDIT-3 M3) -/

theorem eqOn_of_eqOn_rat_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (h : ∀ q : ℚ, (q : ℝ) ∈ Ioo a b → f q = g q) : f b = g b := by
  have hEq : EqOn f g (Icc a b) := by
    refine Set.EqOn.of_subset_closure (s := Ioo a b ∩ range ((↑) : ℚ → ℝ)) ?_ hf hg
      (inter_subset_left.trans Ioo_subset_Icc_self) ?_
    · rintro _ ⟨hx, q, rfl⟩
      exact h q hx
    · calc Icc a b = closure (Ioo a b) := (closure_Ioo hab.ne).symm
        _ ⊆ closure (Ioo a b ∩ range ((↑) : ℚ → ℝ)) :=
          closure_minimal (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo)
            isClosed_closure
  exact hEq ⟨hab.le, le_rfl⟩

/-- **Weld-driver uniqueness (AUDIT-3 M3).** Two welding drivers of the same field at time
`t > 0` agree on `[0,t]`, provided the hulls of the first one are removable at time `t` and at
all rational times in `(0,t)` (for SLE: `RohdeSchrammHolder` at countably many fixed times, and
`JonesSmirnovRemovable`). -/
theorem eqOn_of_isWeldingDriver (hCar : Blueprint.RevMapCaratheodory)
    (hArc : LoewnerSubhullsOfArc) {γ' : ℝ} {x : FieldSample} {t : ℝ} (ht : 0 < t)
    {W₁ W₂ : ℝ → ℝ} (h₁ : IsWeldingDriver γ' x t W₁) (h₂ : IsWeldingDriver γ' x t W₂)
    (hremt : IsConformallyRemovable (closure (revHull W₁ t) ∪ conj '' closure (revHull W₁ t)))
    (hremq : ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t →
      IsConformallyRemovable (closure (revHull W₁ q) ∪ conj '' closure (revHull W₁ q))) :
    EqOn W₁ W₂ (Icc 0 t) := by
  obtain ⟨hW₁, hW₁0, hK₁', hw₁⟩ := h₁
  obtain ⟨hW₂, hW₂0, hK₂', hw₂⟩ := h₂
  have hK₁ : IsSimpleCurveHull (revHull W₁ t) := hK₁'.resolve_left ht.ne'
  have hK₂ : IsSimpleCurveHull (revHull W₂ t) := hK₂'.resolve_left ht.ne'
  obtain ⟨F₁, hF₁⟩ := hCar W₁ hW₁ hW₁0 t ht hK₁
  obtain ⟨F₂, hF₂⟩ := hCar W₂ hW₂ hW₂0 t ht hK₂
  obtain ⟨ha₁, -, -⟩ := car_basic hW₁ ht hF₁ (simpleCurveHull_nonempty hK₁)
  obtain ⟨ha₂, -, -⟩ := car_basic hW₂ ht hF₂ (simpleCurveHull_nonempty hK₂)
  set a₁ := zeroMinus W₁ t with ha₁def
  set a₂ := zeroMinus W₂ t with ha₂def
  have key : a₁ = a₂ := by
    rcases lt_trichotomy a₂ a₁ with hlt | heq | hgt
    · exfalso
      obtain ⟨s, hs, hsa⟩ := exists_zeroMinus_eq hCar hArc hW₂ hW₂0 ht hK₂ hlt.le ha₁
      have hst : s < t := lt_of_le_of_ne hs.2 fun h => by rw [h] at hsa; linarith
      have hK₂s := isSimpleCurveHull_revHull_of_le hArc hW₂ hW₂0 ht hK₂ hs.1 hs.2
      have hweld : EqOn (weldingHom W₁ t) (weldingHom W₂ s) (Icc (zeroMinus W₁ t) 0) := by
        intro y hy
        rw [hw₁ y hy, ← hw₂ y ⟨hlt.le.trans hy.1, hy.2⟩,
          weldingHom_eq_of_le hCar hArc hW₂ hW₂0 ht hK₂ hs.1 hs.2 (hsa ▸ hy)]
      have := (time_eq_of_welding_eq hCar hW₁ hW₂ hW₁0 hW₂0 ht hs.1 hK₁ hK₂s hsa.symm hweld
        hremt).1
      linarith
    · exact heq.symm
    · exfalso
      obtain ⟨s', hs', hs'a⟩ := exists_zeroMinus_eq hCar hArc hW₁ hW₁0 ht hK₁ hgt.le ha₂
      have hs't : s' < t := lt_of_le_of_ne hs'.2 fun h => by rw [h] at hs'a; linarith
      -- agreement of `0₋` at rational times below `s'`
      have hq : ∀ q : ℚ, (q : ℝ) ∈ Ioo (s' / 2) s' →
          zeroMinus W₁ q = zeroMinus W₂ q := by
        intro q hqI
        have hq0 : 0 < (q : ℝ) := by linarith [hqI.1, hs'.1]
        have hqt : (q : ℝ) < t := hqI.2.trans hs't
        have hK₁q := isSimpleCurveHull_revHull_of_le hArc hW₁ hW₁0 ht hK₁ hq0 hqt.le
        obtain ⟨F₁q, hF₁q⟩ := hCar W₁ hW₁ hW₁0 q hq0 hK₁q
        obtain ⟨haq, -, -⟩ := car_basic hW₁ hq0 hF₁q (simpleCurveHull_nonempty hK₁q)
        have hK₁s' := isSimpleCurveHull_revHull_of_le hArc hW₁ hW₁0 ht hK₁ hs'.1 hs'.2
        have hlt : a₂ < zeroMinus W₁ q := by
          rw [← hs'a]; exact zeroMinus_lt_of_lt hCar hArc hW₁ hW₁0 hs'.1 hK₁s' hq0 hqI.2
        obtain ⟨tq, htq, htqa⟩ := exists_zeroMinus_eq hCar hArc hW₂ hW₂0 ht hK₂ hlt.le haq
        have hK₂q := isSimpleCurveHull_revHull_of_le hArc hW₂ hW₂0 ht hK₂ htq.1 htq.2
        have hweld : EqOn (weldingHom W₁ q) (weldingHom W₂ tq) (Icc (zeroMinus W₁ q) 0) := by
          intro y hy
          have hy₂ : y ∈ Icc a₂ 0 := ⟨hlt.le.trans hy.1, hy.2⟩
          have hy₁ : y ∈ Icc a₁ 0 := ⟨hgt.le.trans hy₂.1, hy.2⟩
          rw [← weldingHom_eq_of_le hCar hArc hW₁ hW₁0 ht hK₁ hq0 hqt.le hy, hw₁ y hy₁,
            ← hw₂ y hy₂, weldingHom_eq_of_le hCar hArc hW₂ hW₂0 ht hK₂ htq.1 htq.2
              (htqa ▸ hy)]
        have := (time_eq_of_welding_eq hCar hW₁ hW₂ hW₁0 hW₂0 hq0 htq.1 hK₁q hK₂q htqa.symm
          hweld (hremq q hq0 hqt)).1
        rw [this] at htqa
        exact htqa.symm
      have hcont₁ := (continuousOn_zeroMinus hCar hArc hW₁ hW₁0 ht hK₁).mono
        (fun y (hy : y ∈ Icc (s' / 2) s') => (⟨by linarith [hy.1, hs'.1], hy.2.trans hs'.2⟩ :
          y ∈ Ioc 0 t))
      have hcont₂ := (continuousOn_zeroMinus hCar hArc hW₂ hW₂0 ht hK₂).mono
        (fun y (hy : y ∈ Icc (s' / 2) s') => (⟨by linarith [hy.1, hs'.1], hy.2.trans hs'.2⟩ :
          y ∈ Ioc 0 t))
      have heq := eqOn_of_eqOn_rat_Ioo (by linarith [hs'.1]) hcont₁ hcont₂ hq
      rw [hs'a] at heq
      have := zeroMinus_lt_of_lt hCar hArc hW₂ hW₂0 ht hK₂ hs'.1 hs't
      rw [← heq] at this
      exact lt_irrefl _ this
  have hweld : EqOn (weldingHom W₁ t) (weldingHom W₂ t) (Icc (zeroMinus W₁ t) 0) := by
    intro y hy
    rw [hw₁ y hy, hw₂ y (key ▸ hy)]
  have hrev := revMap_eq_of_welding_eq hCar hW₁ hW₂ hW₁0 hW₂0 ht ht hK₁ hK₂ key hweld hremt
  exact eqOn_of_revMap_eq_general hCar hArc hW₁ hW₂ hW₁0 hW₂0 ht hK₁ hrev

end WeldingConsistency

end QuantumZipper
