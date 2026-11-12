/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L35B6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L35B5

/-!
# `CONFHarmBoundU` by scaling to the unit scale (task P2-CONF35b)

Source: Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381,
`confluence-final.tex` C:1169–1172: "the collection `𝒰_r(z;δ)` … is equal to `r𝒰_1(0;δ) + z`";
"for any fixed choice of `U ∈ 𝒰_1(0;δ)`, a.s. `sup_{u ∈ U_{δ/4}} |𝔥^U(u)| < ∞`. By combining this
with the translation and scale invariance of the law of `h`, modulo additive constant, we find
that there exists `A > 0`…".

* `isHarmPart_ae_eq'`: a.s. uniqueness of the harmonic part (the argument of
  `HarmExist.isHarmPart_ae_eq`, Field/HarmExistB.lean by P2-D110c: pair with radial unit bumps at a
  countable dense set, mean value property, continuity; copied verbatim, written before that file
  was committed).
* `preimage_confU`, `mem_innerPart_scale`: `confU r δ z T = r · confU 1 δ 0 T + z`, and the inner
  parts correspond.
* `confHarmBoundU_of`: `CONFHarmBoundU` from `CONFHarmExists` and the unit-scale bound for
  normalized fields `CONFHarmTailN` (one fixed domain `confU 1 δ 0 T`, normalized field
  `h_1(0) = 0`; proved in S3L35B9): with `g := h(r · + z) − h_r(z)` (normalized),
  `𝔥^{U₁}_g(x) = 𝔥^U_h(r x + z) − h_r(z)` a.s. (`isHarmPart_affineComp`,
  `isHarmPart0_addConst_iff`, uniqueness).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace

namespace LQGMetric.CONF

open Blueprint GFFInv

/-- **a.s. uniqueness of the harmonic part** (argument of `HarmExist.isHarmPart_ae_eq`) -/
theorem isHarmPart_ae_eq' {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) {H₁ H₂ : Ω → ℂ → ℝ}
    (h₁ : IsHarmPart P h U H₁) (h₂ : IsHarmPart P h U H₂) : ∀ᵐ ω ∂P, ∀ u ∈ U, H₁ ω u = H₂ ω u := by
  have hne : ((closure U)ᶜ).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hne
    exact NormedSpace.unbounded_univ ℝ ℂ (hne ▸ hUb.closure)
  obtain ⟨ψ, hψ, hψ1⟩ := HarmLoc.exists_unit_test isClosed_closure.isOpen_compl hne
  have hδ : ∀ v ∈ U, ∃ δ : ℝ, 0 < δ ∧ closedBall v δ ⊆ U := fun v hv => by
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU v hv
    exact ⟨ε / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hεU⟩
  choose δ hδpos hδB using hδ
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℂ
  set S' := U ∩ S
  have hS'c : S'.Countable := hSc.mono inter_subset_right
  have hpair : ∀ v (hv : v ∈ S'), ∀ᵐ ω ∂P,
      ∫ x, H₁ ω x * HarmLoc.unitBump (δ v hv.1) (hδpos v hv.1) v x =
        ∫ x, H₂ ω x * HarmLoc.unitBump (δ v hv.1) (hδpos v hv.1) v x := fun v hv => by
    have hs := (HarmLoc.tsupport_unitBump _ (hδpos v hv.1) v).trans (hδB v hv.1)
    filter_upwards [(h₁.2 _ ψ hs hψ hψ1).symm.trans (h₂.2 _ ψ hs hψ hψ1)] with ω hω
    exact sub_left_injective hω
  filter_upwards [(ae_ball_iff hS'c).2 hpair] with ω hω u hu
  have hval : ∀ v ∈ S', H₁ ω v - H₂ ω v = 0 := fun v hv => by
    have k := hω v hv
    rw [HarmLoc.integral_mul_unitBump hU (h₁.1 ω) _ (hδB v hv.1),
      HarmLoc.integral_mul_unitBump hU (h₂.1 ω) _ (hδB v hv.1)] at k
    rw [k, sub_self]
  have hcont : ContinuousAt (fun x => H₁ ω x - H₂ ω x) u :=
    (h₁.1 ω u hu).1.continuousAt.sub (h₂.1 ω u hu).1.continuousAt
  have hcl : u ∈ closure S' := hSd.open_subset_closure_inter hU hu
  have hmem := mem_closure_image hcont hcl
  have himg : (fun x => H₁ ω x - H₂ ω x) '' S' ⊆ {0} := by
    rintro _ ⟨v, hv, rfl⟩; exact hval v hv
  have := closure_mono himg hmem
  rw [closure_singleton, mem_singleton_iff, sub_eq_zero] at this
  exact this

theorem mem_annulus_iff' (w z : ℂ) (a b : ℝ) :
    w ∈ (annulus z a b : Set ℂ) ↔ a < ‖w - z‖ ∧ ‖w - z‖ < b := Iff.rfl

/-- `confU r δ z T = r · confU 1 δ 0 T + z` -/
theorem preimage_confU {r : ℝ} (hr : 0 < r) (δ : ℝ) (z : ℂ) (T : Finset (ℤ × ℤ)) :
    (fun x => r • x + z) ⁻¹' confU r δ z T = confU 1 δ 0 T := by
  ext x
  have hn : ‖r • x + z - z‖ = r * ‖x‖ := by
    rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hre : (r • x + z).re = r * x.re + z.re := by simp
  have him : (r • x + z).im = r * x.im + z.im := by simp
  have hsq : ∀ k, r • x + z ∈ confSq (δ * r) z k ↔ x ∈ confSq (δ * 1) 0 k := by
    intro k
    show (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _)
    rw [hre, him]
    simp only [Complex.zero_re, Complex.zero_im, zero_add, mul_one]
    constructor <;> rintro ⟨a1, a2, a3, a4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  show (r • x + z ∈ (annulus z (3 * r) (4 * r) : Set ℂ) ∧
      r • x + z ∉ ⋃ k ∈ T, confSq (δ * r) z k) ↔
    (x ∈ (annulus 0 (3 * 1) (4 * 1) : Set ℂ) ∧ x ∉ ⋃ k ∈ T, confSq (δ * 1) 0 k)
  rw [mem_annulus_iff', mem_annulus_iff', hn, sub_zero]
  simp only [mem_iUnion, hsq]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3⟩ <;> exact ⟨⟨by nlinarith, by nlinarith⟩, h3⟩

theorem isBounded_confU' (r δ : ℝ) (z : ℂ) (T : Finset (ℤ × ℤ)) :
    Bornology.IsBounded (confU r δ z T) := by
  refine (isBounded_ball (x := z) (r := 4 * r)).subset fun w hw => ?_
  have := hw.1.2
  rw [mem_ball, dist_eq_norm]
  exact this

/-- the affine homeomorphism `x ↦ r x + z` -/
def affHomeo {r : ℝ} (hr : 0 < r) (z : ℂ) : ℂ ≃ₜ ℂ :=
  ⟨⟨fun x => r • x + z, fun y => (y - z) / r, fun x => div_affMap_cancel hr z x,
    fun y => affMap_div_cancel hr z y⟩, by fun_prop, by fun_prop⟩

/-- the inner parts correspond under `x ↦ r x + z` -/
theorem mem_innerPart_scale {r : ℝ} (hr : 0 < r) (z : ℂ) {U : Set ℂ} {ε : ℝ} (hε : 0 < ε)
    {u : ℂ} (hu : u ∈ innerPart U (ε * r)) :
    (u - z) / r ∈ innerPart ((fun x => r • x + z) ⁻¹' U) ε := by
  obtain ⟨huU, hlt⟩ := hu
  set e := affHomeo hr z
  have he : ∀ x, e x = r • x + z := fun x => rfl
  have hfr : frontier ((fun x => r • x + z) ⁻¹' U) = (fun x => r • x + z) ⁻¹' frontier U :=
    (e.preimage_frontier U).symm
  refine ⟨show r • ((u - z) / r) + z ∈ U by rw [affMap_div_cancel hr]; exact huU, ?_⟩
  rw [hfr]
  rcases (frontier U).eq_empty_or_nonempty with h0 | hne
  · rw [h0, Metric.infDist_empty] at hlt
    exact absurd hlt (by nlinarith)
  have hne' : ((fun x => r • x + z) ⁻¹' frontier U).Nonempty := by
    obtain ⟨y, hy⟩ := hne
    exact ⟨(y - z) / r, show r • ((y - z) / r) + z ∈ frontier U by
      rw [affMap_div_cancel hr]; exact hy⟩
  have hlow : infDist u (frontier U) / r ≤ infDist ((u - z) / r)
      ((fun x => r • x + z) ⁻¹' frontier U) := by
    refine (Metric.le_infDist hne').2 fun y hy => ?_
    have h1 : infDist u (frontier U) ≤ dist u (r • y + z) := Metric.infDist_le_dist_of_mem hy
    have h2 : dist u (r • y + z) = r * dist ((u - z) / r) y := by
      rw [dist_eq_norm, dist_eq_norm]
      have : u - (r • y + z) = r • ((u - z) / r - y) := by
        rw [smul_sub, Complex.real_smul, Complex.real_smul,
          mul_div_cancel₀ _ (by exact_mod_cast hr.ne')]
        ring
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    rw [div_le_iff₀ hr]
    linarith
  have : ε < infDist u (frontier U) / r := by rw [lt_div_iff₀ hr]; exact hlt
  linarith

/-- **the harmonic-part bound at the unit scale, for normalized fields** (CONF C:1170–1171: for a
fixed `U ∈ 𝒰_1(0;δ)`, `sup_{U_{δ/4}} |𝔥^U| < ∞` a.s.; uniformity over fields is the uniqueness of
the law of the normalized whole-plane GFF). Proved as `confHarmTailN` (S3L35B9). -/
def CONFHarmTailN : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ T : Finset (ℤ × ℤ), ∀ β : ℝ, 0 < β → ∃ A : ℝ, 0 < A ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWPGFF h P →
        P {ω | ∃ x ∈ innerPart (confU 1 δ 0 T) (δ / 4),
          A < |harmPart P h (confU 1 δ 0 T) ω x|} ≤ ENNReal.ofReal β

/-- **`CONFHarmBoundU` by scaling** (CONF C:1169–1172) -/
theorem confHarmBoundU_of (hEx : CONFHarmExists) (HT : CONFHarmTailN) : CONFHarmBoundU := by
  intro δ hδ hδ1 T β hβ
  obtain ⟨A, hA, HA⟩ := HT δ hδ hδ1 T β hβ
  refine ⟨A, hA, ?_⟩
  intro Ω _ P _ h hh z r hr
  have hUo : IsOpen (confU r δ z T) := GM.p412j_isOpen_confU r δ z T
  have hU₁o : IsOpen (confU 1 δ 0 T) := GM.p412j_isOpen_confU 1 δ 0 T
  have hcm : Measurable fun ω => circleAvg (h ω) r z :=
    (measurable_circleAvg_left r z).comp hh.measurable
  have hg0 : IsWholePlaneGFF (fun ω => affineComp r z (h ω)) P := hh.affineComp hr z
  set g : Ω → DistC := fun ω => addConst (affineComp r z (h ω)) (-circleAvg (h ω) r z) with hg
  have hgN : IsNormalizedWPGFF g P := by
    refine ⟨hg0.addConst hcm.neg, ?_⟩
    filter_upwards [CircleAvg.ae_circleAvg_addConst hg0 0 one_pos,
      CircleAvg.ae_circleAvg_affineComp hh hr z] with ω h1 h2
    simp only [hg]
    rw [h1, h2]; ring
  have hH : IsHarmPart P h (confU r δ z T) (harmPart P h (confU r δ z T)) :=
    isHarmPart0_harmPart0 (hEx P h hh _ hUo (isBounded_confU' r δ z T))
  have hH1 : IsHarmPart P g (confU 1 δ 0 T)
      (fun ω x => harmPart P h (confU r δ z T) ω (r • x + z) + -circleAvg (h ω) r z) := by
    have := isHarmPart_affineComp hr z hUo hH
    rw [preimage_confU hr δ z T] at this
    exact (isHarmPart0_addConst_iff (fun ω => affineComp r z (h ω))
      (fun ω => -circleAvg (h ω) r z) _ _).2 this
  have hHg : IsHarmPart P g (confU 1 δ 0 T) (harmPart P g (confU 1 δ 0 T)) :=
    isHarmPart0_harmPart0 ⟨_, hH1⟩
  have huniq := isHarmPart_ae_eq' hU₁o (isBounded_confU' 1 δ 0 T) hHg hH1
  refine le_trans (measure_mono_ae ?_) (HA P g hgN)
  filter_upwards [huniq] with ω hω
  rintro ⟨u, hu, hlt⟩
  have hu' : u ∈ innerPart (confU r δ z T) (δ / 4 * r) := by
    rwa [show δ / 4 * r = δ * r / 4 by ring]
  have hx := mem_innerPart_scale hr z (by positivity) hu'
  rw [preimage_confU hr δ z T] at hx
  refine ⟨(u - z) / r, hx, ?_⟩
  rw [hω _ hx.1, affMap_div_cancel hr]
  simpa only [sub_eq_add_neg] using hlt

end LQGMetric.CONF
