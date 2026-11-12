/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17Core3H at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core3G

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: one stage of Steps 2–4 for the field `h` (R3)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Steps 2–4 (T:1224–1278) with decision D80. For one stage (dyadic domains `𝒲` inside `V`, `𝒲'`
inside `U₁ ⊂ ℂ ∖ V̄`, the bump `φ ≡ 1` on `U₁`), the limit coupling `ρ` of `indep_stage_limit`
for `(h̃, h̃ − φ𝔥)` (`h̃ = h − h_r(z)`) gives, on the law `ν` of `(J h, e^{−ξh_r(z)} D_h)`,

  `⋁_{W ∈ 𝒲} D(·,·;W) ⟂ σ(h̊) ∨ ⋁_{W' ∈ 𝒲'} D(·,·;W') | σ(h̃|_{cl V})`  (`condIndepEv_law_stage`),

all σ-algebras being read on the coordinate space `S × C(ℂ × ℂ, ℝ)` (`S = CoordJ → ℝ`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric
open scoped ENNReal BoundedContinuousFunction

namespace LQGMetric.DFGPS.L217

open Blueprint GM.Bilip InnerProductSpace

/-- `harmFn φ δ T` vanishes off `tsupport φ` -/
theorem harmFn_eq_zero_of_notMem {φ : C(ℂ, ℝ)} {δ : ℝ} (hδ : 0 < δ) (T : DistC) {x : ℂ}
    (hx : x ∉ tsupport φ) : harmFn φ δ hδ T x = 0 := by
  rw [harmFn_apply, image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- **One stage of Steps 2–4 for the field `h`** (T:1224–1278, D80), on the law of
`(J h, e^{−ξh_r(z)} D_h)`. -/
theorem condIndepEv_law_stage (h28 : Lem2_8) (HG : Lem2_1GffApprox.{0}) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) {Dh : Ω → ContMetric} (hDm : Measurable Dh)
    {εn : ℕ → ℝ} (hεp : ∀ n, 0 < εn n) (hε0 : Tendsto εn atTop (𝓝 0))
    (hconv : ∀ φ : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (pairJ ⊤ (h ω), toCMap fun p =>
          (aEpsDF (xiGamma γ) (εn n))⁻¹ * lfppDist (xiGamma γ) (εn n) (h ω) p) ∂P) atTop
        (𝓝 (∫ ω, φ (pairJ ⊤ (h ω), (Dh ω).1) ∂P)))
    {z : ℂ} {r : ℝ} (hr : 0 < r) {V Uc : Opens ℂ}
    {hh' hz : Ω → DistC} (hsum : ∀ ω, normField h z r ω = hh' ω + hz ω)
    (hharm : ∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, HarmonicOnNhd g Uc ∧
      ∀ ψ : TestOn Uc, restrictTo Uc (hh' ω) ψ = ∫ x, g x * ψ x)
    {g : (CoordJ → ℝ) → DistC}
    (hg : Measurable[MeasurableSpace.map (fun ω => pairJ ⊤ (h ω))
      (fieldSigmaClosed (normField h z r) (closure (V : Set ℂ))) ⊓ inferInstance] g)
    (hae : hh' =ᵐ[P] fun ω => g (pairJ ⊤ (h ω)))
    (hind : Indep (MeasurableSpace.comap hz inferInstance)
      (fieldSigmaClosed (normField h z r) (closure (V : Set ℂ))) P)
    {φ : C(ℂ, ℝ)} (hφc : HasCompactSupport φ) {δ : ℝ} (hδ : 0 < δ)
    (hφU : ∀ x, φ x ≠ 0 → closedBall x δ ⊆ (Uc : Set ℂ)) {U₁ : Set ℂ} (hU₁ : IsOpen U₁)
    (hφ1 : ∀ x ∈ U₁, φ x = 1) (𝒲 𝒲' : Finset dyadicDomainsC) (m : ℕ)
    (hWV : ∀ k, ∀ W ∈ 𝒲, ∀ y ∈ closure (W : Set ℂ),
      closedBall y (Real.sqrt (εn (k + m))) ⊆ (V : Set ℂ))
    (hWU : ∀ k, ∀ W ∈ 𝒲', ∀ y ∈ closure (W : Set ℂ),
      closedBall y (Real.sqrt (εn (k + m))) ⊆ U₁) :
    CondIndepEv ((MeasurableSpace.map (fun ω => pairJ ⊤ (h ω))
        (fieldSigmaClosed (normField h z r) (closure (V : Set ℂ))) ⊓ inferInstance).comap
          (Prod.fst : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → CoordJ → ℝ))
      (⨆ W ∈ 𝒲, MeasurableSpace.comap
        (fun q : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) => intFn W q.2) inferInstance)
      ((MeasurableSpace.comap (fun x => normField (pairJInv ⊤) z r x - g x) inferInstance).comap
          (Prod.fst : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → CoordJ → ℝ) ⊔
        ⨆ W ∈ 𝒲', MeasurableSpace.comap
          (fun q : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) => intFn W q.2) inferInstance)
      (P.map fun ω => (pairJ ⊤ (h ω), Real.exp (-xiGamma γ * circleAvg (h ω) r z) • (Dh ω).1)) := by
  set ξ := xiGamma γ
  set X : Ω → CoordJ → ℝ := fun ω => pairJ ⊤ (h ω) with hXdef
  have hX : Measurable X := (measurable_pairJ ⊤).comp hh.1.measurable
  set N : (CoordJ → ℝ) → DistC := normField (pairJInv ⊤) z r with hNdef
  have hNX : ∀ ω, N (X ω) = normField h z r ω := fun ω => normField_pairJInv_pairJ z r ω
  have hNwp : IsWholePlaneGFF N (P.map X) :=
    (isNormalizedAt_recenter (isNormalizedWPGFF_pairJInv hh).1 hr z).1
  have hN : IsGFFPlusBddCont N (P.map X) := isGFFPlusBddCont_normField_pairJInv hh hr z
  have hgm : Measurable g := hg.mono inf_le_right le_rfl
  set Fb : (CoordJ → ℝ) → C(ℂ, ℝ) := fun x => harmFn φ δ hδ (g x) with hFbdef
  have hFb : Measurable Fb := (measurable_harmFn φ δ hδ).comp hgm
  have hFb𝒢 : Measurable[MeasurableSpace.map X
      (fieldSigmaClosed (normField h z r) (closure (V : Set ℂ))) ⊓ inferInstance] Fb :=
    (measurable_harmFn φ δ hδ).comp hg
  have hFbb : ∀ x, ∃ M, ∀ y, |Fb x y| ≤ M := fun x => exists_bound_harmFn hφc δ hδ (g x)
  have hN₂ : IsGFFPlusBddCont (fun x => N x - ofCont (Fb x)) (P.map X) :=
    isGFFPlusBddCont_sub_ofCont hNwp hFb hFbb
  -- the fields on `Ω`
  have hteq : (fun ω => N (X ω)) = normField h z r := funext hNX
  have hhtwp : IsWholePlaneGFF (fun ω => N (X ω)) P := by
    rw [hteq]; exact (isNormalizedAt_recenter hh.1 hr z).1
  have hht : IsGFFPlusBddCont (fun ω => N (X ω)) P := by
    rw [hteq]; exact isGFFPlusBddCont_normField hh hr z
  have hh₂ : IsGFFPlusBddCont (fun ω => N (X ω) - ofCont (Fb (X ω))) P :=
    isGFFPlusBddCont_sub_ofCont hhtwp (hFb.comp hX) fun ω => hFbb _
  -- the zero-boundary part, as a function of `X`
  set hz' : Ω → DistC := fun ω => N (X ω) - g (X ω) with hz'def
  have hz'ae : hz' =ᵐ[P] hz := by
    filter_upwards [hae] with ω hω
    simp only [hz'def, hNX, hsum]
    rw [show g (X ω) = hh' ω from hω.symm]
    exact add_sub_cancel_left _ _
  have hind' : Indep (MeasurableSpace.comap hz' inferInstance)
      (fieldSigmaClosed (fun ω => N (X ω)) (closure (V : Set ℂ))) P := by
    rw [hteq]
    exact indep_of_le_aeClosure hind (L219.comap_le_aeClosure_of_ae_eq (comap_measurable hz)
      hz'ae) (le_aeClosure _)
  have hagree : ∀ᵐ ω ∂P, ∀ ψ : TestC, tsupport (ψ : ℂ → ℝ) ⊆ U₁ →
      (N (X ω) - ofCont (Fb (X ω))) ψ = hz' ω ψ := by
    have H := (exists_harmFun (P := P) (h' := fun ω => N (X ω)) (fun ω => (hNX ω).trans (hsum ω))
      hharm hae hφc hδ hφU hφ1).2
    filter_upwards [H, hz'ae] with ω hω hω'
    intro ψ hψ
    rw [hω ψ hψ, hω']
  have hNgm : Measurable fun x => N x - g x := measurable_distOn_iff.2 fun ψ =>
    ((measurable_distOn_apply ψ).comp hN.1).sub ((measurable_distOn_apply ψ).comp hgm)
  have h𝒢 : (MeasurableSpace.map X (fieldSigmaClosed (normField h z r) (closure (V : Set ℂ))) ⊓
      inferInstance).comap X ≤ fieldSigmaClosed (fun ω => N (X ω)) (closure (V : Set ℂ)) := by
    rw [hteq]
    exact (MeasurableSpace.comap_mono inf_le_left).trans MeasurableSpace.comap_map_le
  have hℋ : (MeasurableSpace.comap (fun x => N x - g x) inferInstance).comap X ≤
      MeasurableSpace.comap hz' inferInstance := by
    rw [MeasurableSpace.comap_comp]; exact le_rfl
  obtain ⟨ψ, hψ, ρ, hconvρ, hmarg, hdy, hindρ⟩ := indep_stage_limit h28 HG hγ hγ2 hht hh₂ hU₁
    hind' hagree (εk := fun k => εn (k + m)) (fun k => hεp _)
    (hε0.comp (tendsto_add_atTop_nat m)) 𝒲 𝒲' hWV hWU hX
    ⟨_, inf_le_right⟩ ⟨_, hNgm.comap_le⟩ h𝒢 hℋ
  set εs : ℕ → ℝ := fun n => εn (ψ n + m)
  have hεs : ∀ n, 0 < εs n := fun n => hεp _
  have hψm : Tendsto (fun n => ψ n + m) atTop atTop :=
    (tendsto_add_atTop_nat m).comp hψ.tendsto_atTop
  have hεs0 : Tendsto εs atTop (𝓝 0) := hε0.comp hψm
  -- the coupling statement on the coordinate space
  have hconv' : ∀ f : (CoordJ → ℝ) × (DyProd × DyProd) →ᵇ ℝ, Tendsto (fun n => ∫ x, f (x,
      (lfppJoint ξ (εs n) (N x), lfppJoint ξ (εs n) (N x - ofCont (Fb x)))) ∂(P.map X)) atTop
        (𝓝 (∫ p, f p ∂(ρ : Measure ((CoordJ → ℝ) × (DyProd × DyProd))))) := fun f => by
    refine (hconvρ f).congr fun n => ?_
    have hm : AEMeasurable (fun x => (x, (lfppJoint ξ (εs n) (N x),
        lfppJoint ξ (εs n) (N x - ofCont (Fb x))))) (P.map X) :=
      aemeasurable_id.prodMk ((aemeasurable_lfppJoint hN (hεs n).ne').prodMk
        (aemeasurable_lfppJoint hN₂ (hεs n).ne'))
    exact (integral_map hX.aemeasurable
      (f.continuous.measurable.comp_aemeasurable hm).aestronglyMeasurable).symm
  have H := condIndepEv_stage h28 hγ hγ2 hN hFb hφc (fun x y hy => harmFn_eq_zero_of_notMem hδ _ hy)
    hN₂ hεs hεs0 hconv' hmarg (hdy.mono fun p hp => hp.1) 𝒲 𝒲' ⟨_, inf_le_right⟩
    ⟨_, hNgm.comap_le⟩ hFb𝒢 hindρ
  -- the law of `(x, D₁)` under `ρ` is that of `(J h, e^{−ξh_r(z)} D_h)`
  have hlaw := map_coupling_fst_eq hh.1 hDm ξ z r (εs := εs) hεs
    (fun φ' hφ' hC => (hconv φ' hφ' hC).comp hψm)
    (Y₂ := fun n ω => lfppJoint ξ (εs n) (N (X ω) - ofCont (Fb (X ω)))) (ρ := ρ)
    (fun f => by simpa only [hNX] using hconvρ f)
  rw [← hlaw]
  exact H

end L217

end LQGMetric.DFGPS
