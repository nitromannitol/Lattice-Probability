/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L214FinalReach at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L214Pull
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L214Beurling
import LatticeProb.Bonanno.LQGMetric.Complex.HarmonicComp
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeBasic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.FieldLawlerSubExcGeo
import Mathlib.Analysis.Complex.OpenMapping

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 2.14, R5-2: the Beurling step inside `U`

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), proof of Lemma 2.14,
confluence-final.tex 862–867: a Brownian motion from `φ(w_I)` exits `φ(H_I)` in `φ(J_I^-)` with
probability `≥ a` (conformal invariance, C:864), but travels distance `R dist(φ(w_I), ∂U)` without
hitting `∂U` with probability `≲ R^{-1/2}` (Beurling, C:865); for `R` large there is a connected
piece of `φ(H_I)` near `φ(w_I)` whose closure reaches `φ(J_I^-)` inside `B_{R dist}(φ(w_I))`.

Analytic form (normalized coordinates `u_I = i`, `H_I = upperHalfDisc`, `w_I = (1 − ℓ) i`):
harmonic measure is the minorant `g` of `l214_minorant` transported by `φ⁻¹`
(`harmonicOnNhd_comp_holo`), and the Beurling step is `l214_beurling_reach`.

Departure (DEVIATIONS, proposed): the Beurling estimate is applied to the connected set
`K = φ(∂𝔻) ∪ ray`, where the ray `{p₀ + t : t ≥ 0}` starts at a point `p₀` of `∂U` of maximal
real part and lies outside `U`. This ensures that `K` leaves `B_ρ(φ(w_I))` (the Beurling
estimate as stated needs it), replacing a case distinction "`∂U ⊆ B_ρ`" plus the maximum
principle. A Brownian motion started in `U` hits `∂U` before the ray, so the probabilistic
statement is the same.
-/

namespace LQGMetric
namespace CONF

open Set Metric Filter Complex
open scoped Topology Real ComplexConjugate

/-- The inverse of a map that is continuous and injective on the closed disc is continuous on
the image (compact-to-Hausdorff). -/
theorem l214_invFun_contOn {Φ : ℂ → ℂ} (hc : ContinuousOn Φ (closedBall 0 1))
    (hinj : InjOn Φ (closedBall 0 1)) :
    ContinuousOn (Function.invFunOn Φ (closedBall 0 1)) (Φ '' closedBall 0 1) := by
  rw [continuousOn_iff_isClosed]
  intro t ht
  refine ⟨Φ '' (closedBall 0 1 ∩ t),
    (((isCompact_closedBall 0 1).inter_right ht).image_of_continuousOn
      (hc.mono inter_subset_left)).isClosed, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, ζ, hζ, rfl⟩
    rw [mem_preimage, hinj.leftInvOn_invFunOn hζ] at hy
    exact ⟨⟨ζ, ⟨hζ, hy⟩, rfl⟩, ζ, hζ, rfl⟩
  · rintro ⟨⟨ζ, ⟨hζ, hζt⟩, rfl⟩, -⟩
    refine ⟨?_, ζ, hζ, rfl⟩
    rw [mem_preimage, hinj.leftInvOn_invFunOn hζ]; exact hζt

/-- Open mapping for a map holomorphic and injective on the disc. -/
theorem l214_isOpen_image {Φ : ℂ → ℂ} (hd : DifferentiableOn ℂ Φ (ball 0 1))
    (hinj : InjOn Φ (closedBall 0 1)) {s : Set ℂ} (hs : s ⊆ ball 0 1) (hso : IsOpen s) :
    IsOpen (Φ '' s) := by
  rcases (hd.analyticOnNhd isOpen_ball).is_constant_or_isOpen (convex_ball (0 : ℂ) 1).isPreconnected
    with ⟨c, hc⟩ | h
  · exfalso
    have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
    have h1 : ((1 / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; norm_num
    have := hinj (ball_subset_closedBall h0) (ball_subset_closedBall h1) (by rw [hc _ h0, hc _ h1])
    have h2 := congrArg Complex.re this
    simp at h2
  · exact h s hs hso

/-- The reflection `z ↦ −z̄` preserves harmonicity (via QZ `fl_harmonicAt_conj` and
`harmonicOnNhd_comp_holo` for `z ↦ −z`). -/
theorem l214_harmonic_refl {g : ℂ → ℝ} (hg : InnerProductSpace.HarmonicOnNhd g (ball 0 1)) :
    InnerProductSpace.HarmonicOnNhd (fun z => g (-conj z)) (ball 0 1) := by
  have hneg : InnerProductSpace.HarmonicOnNhd (g ∘ fun z => -z) (ball 0 1) :=
    harmonicOnNhd_comp_holo isOpen_ball isOpen_ball hg (differentiableOn_neg _)
      (fun z hz => by rw [mem_ball_zero_iff, norm_neg]; exact mem_ball_zero_iff.1 hz)
  intro z hz
  have hz' : conj z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_conj]; exact mem_ball_zero_iff.1 hz
  exact QuantumZipper.FieldLawler.fl_harmonicAt_conj (g := g ∘ fun z => -z) (hneg _ hz')

theorem l214_neg_conj_mem_uhd {z : ℂ} (hz : z ∈ upperHalfDisc) : -conj z ∈ upperHalfDisc := by
  obtain ⟨h1, h2⟩ := hz
  refine ⟨by rwa [norm_neg, Complex.norm_conj], ?_⟩
  simpa using h2

theorem l214_neg_conj_centerM (ℓ : ℝ) : -conj (l214CenterM ℓ) = l214CenterP ℓ := by
  apply Complex.ext
  · rw [neg_re, conj_re, l214CenterM, l214CenterP, exp_ofReal_mul_I_re, exp_ofReal_mul_I_re]
    simp [Real.cos_add, Real.cos_sub]
  · rw [neg_im, conj_im, neg_neg, l214CenterM, l214CenterP, exp_ofReal_mul_I_im,
      exp_ofReal_mul_I_im]
    simp [Real.sin_add, Real.sin_sub]

/-- The mirror minorant for `J⁺` (C:867, "symmetrically"): `g⁺ = g⁻ ∘ (z ↦ −z̄)` has the
properties of `l214_minorant` with centre `c⁺ = l214CenterP ℓ`. -/
theorem l214_minorant_plus {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1 / 10) :
    InnerProductSpace.HarmonicOnNhd (fun z => l214Harm ℓ (-conj z)) (ball (0 : ℂ) 1) ∧
    (∀ z ∈ upperHalfDisc, 0 ≤ l214Harm ℓ (-conj z) ∧ l214Harm ℓ (-conj z) ≤ 1) ∧
    1 / (128 * π) ≤ l214Harm ℓ (-conj (((1 - ℓ : ℝ) : ℂ) * I)) ∧
    ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → 0 ≤ ζ.im → (‖ζ‖ = 1 ∨ ζ.im = 0) → ℓ / 4 ≤ ‖ζ - l214CenterP ℓ‖ →
      Tendsto (fun z => l214Harm ℓ (-conj z)) (𝓝[upperHalfDisc] ζ) (𝓝 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := l214_minorant hℓ hℓ1
  refine ⟨l214_harmonic_refl h1, fun z hz => h2 _ (l214_neg_conj_mem_uhd hz), ?_, ?_⟩
  · have : -conj (((1 - ℓ : ℝ) : ℂ) * I) = ((1 - ℓ : ℝ) : ℂ) * I := by
      simp [map_mul, Complex.conj_ofReal]
    rw [this]; exact h3
  · intro ζ hζ1 hζi hbd hfar
    have hc : Continuous fun z : ℂ => -conj z := continuous_conj.neg
    have hT : Tendsto (fun z : ℂ => -conj z) (𝓝[upperHalfDisc] ζ) (𝓝[upperHalfDisc] (-conj ζ)) :=
      tendsto_nhdsWithin_iff.2 ⟨(hc.tendsto ζ).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun z hz => l214_neg_conj_mem_uhd hz⟩
    refine (h4 (-conj ζ) ?_ ?_ ?_ ?_).comp hT
    · rwa [norm_neg, Complex.norm_conj]
    · simpa using hζi
    · rcases hbd with h | h
      · left; rwa [norm_neg, Complex.norm_conj]
      · right; simp [h]
    · have e : -conj ζ - l214CenterM ℓ = -conj (ζ - l214CenterP ℓ) := by
        rw [← l214_neg_conj_centerM]; simp; ring
      rw [e, norm_neg, Complex.norm_conj]; exact hfar

/-- Points of `Φ(closedBall)` outside `U = Φ(𝔻)` are images of circle points. -/
theorem l214_mem_sphere_image {Φ : ℂ → ℂ} {p : ℂ} (hp : p ∈ Φ '' closedBall 0 1)
    (hpU : p ∉ Φ '' ball 0 1) : p ∈ Φ '' sphere 0 1 := by
  obtain ⟨ζ, hζ, rfl⟩ := hp
  refine ⟨ζ, ?_, rfl⟩
  rcases (mem_closedBall_zero_iff.1 hζ).lt_or_eq with h | h
  · exact absurd ⟨ζ, mem_ball_zero_iff.2 h, rfl⟩ hpU
  · exact mem_sphere_zero_iff_norm.2 h

/-- **CONF Lemma 2.14, R5-2** (C:862–867, normalized coordinates `u_I = i`): for `Φ`
continuous and injective on the closed disc and holomorphic on `𝔻`, `w = (1 − ℓ) i`,
`d = dist(Φ(w), ∂U)`, and `g` a harmonic minorant with the properties of `l214_minorant` for a
cap centre `c` (`c⁻` or, via `l214_minorant_plus`, `c⁺`), there is an open connected
`W ⊆ H = upperHalfDisc` containing `w` with `Φ(W) ⊆ B_{R d}(Φ(w))` whose closure meets the cap
`{|ζ| = 1, |ζ − c| < ℓ/4}`; `R` is universal. -/
theorem l214_reach : ∃ R : ℝ, 1 ≤ R ∧ ∀ (Φ : ℂ → ℂ) (ℓ : ℝ) (c : ℂ) (g : ℂ → ℝ),
    ContinuousOn Φ (closedBall 0 1) → InjOn Φ (closedBall 0 1) →
    DifferentiableOn ℂ Φ (ball 0 1) → 0 < ℓ → ℓ ≤ 1 / 10 → ℓ / 4 ≤ c.im →
    InnerProductSpace.HarmonicOnNhd g (ball 0 1) → (∀ z ∈ upperHalfDisc, 0 ≤ g z ∧ g z ≤ 1) →
    1 / (128 * π) ≤ g (((1 - ℓ : ℝ) : ℂ) * I) →
    (∀ ζ : ℂ, ‖ζ‖ ≤ 1 → 0 ≤ ζ.im → (‖ζ‖ = 1 ∨ ζ.im = 0) → ℓ / 4 ≤ ‖ζ - c‖ →
      Tendsto g (𝓝[upperHalfDisc] ζ) (𝓝 0)) →
    ∃ W : Set ℂ, IsOpen W ∧ IsPreconnected W ∧ W ⊆ upperHalfDisc ∧
      (((1 - ℓ : ℝ) : ℂ) * I) ∈ W ∧
      Φ '' W ⊆ ball (Φ (((1 - ℓ : ℝ) : ℂ) * I))
        (R * infDist (Φ (((1 - ℓ : ℝ) : ℂ) * I)) (Φ '' ball 0 1)ᶜ) ∧
      ∃ a ∈ closure W, ‖a‖ = 1 ∧ ‖a - c‖ < ℓ / 4 := by
  obtain ⟨CB, hCB0, hB⟩ := l214_beurling_reach
  set k : ℝ := 256 * π * CB + 1 with hk
  have hpi := Real.pi_pos
  have hk1 : 1 ≤ k := by have : 0 ≤ 256 * π * CB := by positivity
                         linarith
  refine ⟨k ^ 2, by nlinarith, ?_⟩
  intro Φ ℓ c g hc hinj hd hℓ hℓ1 hcim hgh hgb hgw hgt
  set w : ℂ := ((1 - ℓ : ℝ) : ℂ) * I with hwdef
  set x : ℂ := Φ w with hx
  set U : Set ℂ := Φ '' ball 0 1 with hU
  set B : Set ℂ := closedBall (0 : ℂ) 1 with hBdef
  have hw : w ∈ upperHalfDisc := by
    refine ⟨?_, ?_⟩
    · rw [hwdef, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
        abs_of_pos (by linarith)]; linarith
    · simp [hwdef]; linarith
  have hHB : upperHalfDisc ⊆ ball (0 : ℂ) 1 := upperHalfDisc_subset_ball
  have hHo : IsOpen upperHalfDisc :=
    (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const continuous_im)
  have hUo : IsOpen U := l214_isOpen_image hd hinj subset_rfl isOpen_ball
  set G : Set ℂ := Φ '' upperHalfDisc with hG
  have hGo : IsOpen G := l214_isOpen_image hd hinj hHB hHo
  have hGU : G ⊆ U := image_mono hHB
  have hxG : x ∈ G := ⟨w, hw, rfl⟩
  have hcomp : IsCompact (Φ '' B) := (isCompact_closedBall 0 1).image_of_continuousOn hc
  have hUB : U ⊆ Φ '' B := image_mono ball_subset_closedBall
  have hBne : (Φ '' B).Nonempty := ⟨Φ 0, 0, mem_closedBall_self zero_le_one, rfl⟩
  -- `Uᶜ ≠ ∅` and `d > 0`
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).1 hcomp.isBounded
  have hUc : (Uᶜ).Nonempty := by
    refine ⟨((|r| + 1 : ℝ) : ℂ), fun h => ?_⟩
    have := mem_closedBall_zero_iff.1 (hr (hUB h))
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    have := le_abs_self r
    rw [abs_of_pos (by positivity : (0 : ℝ) < |r| + 1)] at *
    linarith
  set d : ℝ := infDist x Uᶜ with hddef
  have hd0 : 0 < d := (hUo.isClosed_compl.notMem_iff_infDist_pos hUc).1
    (fun h => h (hGU hxG))
  set ρ : ℝ := k ^ 2 * d with hρ
  have hdρ : d ≤ ρ := by
    have : 1 ≤ k ^ 2 := by nlinarith
    nlinarith
  have hρ0 : 0 < ρ := hd0.trans_le hdρ
  -- the inverses
  set Φi := Function.invFunOn Φ (ball (0 : ℂ) 1) with hΦi
  set Φc := Function.invFunOn Φ B with hΦc
  have hinjb : InjOn Φ (ball (0 : ℂ) 1) := hinj.mono ball_subset_closedBall
  have hΦcC : ContinuousOn Φc (Φ '' B) := l214_invFun_contOn hc hinj
  have hΦcΦ : ∀ z ∈ B, Φc (Φ z) = z := fun z hz => hinj.leftInvOn_invFunOn hz
  have hΦiΦ : ∀ z ∈ ball (0 : ℂ) 1, Φi (Φ z) = z := fun z hz => hinjb.leftInvOn_invFunOn hz
  -- `h = g ∘ Φ⁻¹` is harmonic on `G` (C:864)
  have hΦiD : DifferentiableOn ℂ Φi G := by
    rintro _ ⟨z, hz, rfl⟩
    exact (QuantumZipper.CA.Koebe.hasDerivAt_invFunOn_of_injOn isOpen_ball hd hinjb
      (hHB hz)).differentiableAt.differentiableWithinAt
  have hharm : InnerProductSpace.HarmonicOnNhd (g ∘ Φi) G :=
    harmonicOnNhd_comp_holo isOpen_ball hGo hgh hΦiD (by
      rintro _ ⟨z, hz, rfl⟩; rw [hΦiΦ z (hHB hz)]; exact hHB hz)
  have hbnd : ∀ y ∈ G, 0 ≤ (g ∘ Φi) y ∧ (g ∘ Φi) y ≤ 1 := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [Function.comp_apply]; rw [hΦiΦ z (hHB hz)]; exact hgb z hz
  -- the target set `T` (image of the cap)
  set T : Set ℂ := Φ '' {ζ | ‖ζ‖ = 1 ∧ ‖ζ - c‖ < ℓ / 4} with hT
  have hGB : G ⊆ Φ '' B := image_mono (hHB.trans ball_subset_closedBall)
  have hdecay : ∀ x₀ ∈ frontier G ∩ ball x ρ, x₀ ∉ T →
      Tendsto (g ∘ Φi) (𝓝[G] x₀) (𝓝 0) := by
    rintro x₀ ⟨hx₀, -⟩ hx₀T
    have hx₀cl : x₀ ∈ closure G := frontier_subset_closure hx₀
    have hx₀B : x₀ ∈ Φ '' B := hcomp.isClosed.closure_subset_iff.2 hGB hx₀cl
    have hcw : ContinuousWithinAt Φc G x₀ := (hΦcC x₀ hx₀B).mono hGB
    set ζ := Φc x₀ with hζ
    have hΦζ : Φ ζ = x₀ := by
      obtain ⟨z, hz, rfl⟩ := hx₀B; rw [hζ, hΦcΦ z hz]
    have hΦcG : Φc '' G = upperHalfDisc := by
      ext z; constructor
      · rintro ⟨_, ⟨z', hz', rfl⟩, rfl⟩
        rw [hΦcΦ z' (ball_subset_closedBall (hHB hz'))]; exact hz'
      · intro hz; exact ⟨Φ z, ⟨z, hz, rfl⟩, hΦcΦ z (ball_subset_closedBall (hHB hz))⟩
    have hζcl : ζ ∈ closure upperHalfDisc := hΦcG ▸ hcw.mem_closure_image hx₀cl
    have hcls : closure upperHalfDisc ⊆ {z : ℂ | ‖z‖ ≤ 1 ∧ 0 ≤ z.im} :=
      closure_minimal (fun z hz => ⟨hz.1.le, hz.2.le⟩)
        ((isClosed_le continuous_norm continuous_const).inter
          (isClosed_le continuous_const continuous_im))
    obtain ⟨hζ1, hζi⟩ := hcls hζcl
    have hζH : ζ ∉ upperHalfDisc := by
      intro h
      rw [hGo.frontier_eq] at hx₀
      exact hx₀.2 ⟨ζ, h, hΦζ⟩
    have hbd : ‖ζ‖ = 1 ∨ ζ.im = 0 := by
      by_contra hcon
      push Not at hcon
      exact hζH ⟨lt_of_le_of_ne hζ1 hcon.1, lt_of_le_of_ne hζi (Ne.symm hcon.2)⟩
    have hfar : ℓ / 4 ≤ ‖ζ - c‖ := by
      by_contra hlt
      push Not at hlt
      rcases hbd with h | h
      · exact hx₀T ⟨ζ, ⟨h, hlt⟩, hΦζ⟩
      · have := abs_im_le_norm (ζ - c)
        rw [sub_im, h, zero_sub, abs_neg, abs_of_nonneg (by linarith)] at this
        linarith
    have hlim := hgt ζ hζ1 hζi hbd hfar
    have hT2 : Tendsto Φc (𝓝[G] x₀) (𝓝[upperHalfDisc] ζ) :=
      tendsto_nhdsWithin_iff.2 ⟨hcw.tendsto, eventually_nhdsWithin_of_forall fun y hy =>
        hΦcG ▸ mem_image_of_mem Φc hy⟩
    refine (hlim.comp hT2).congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
    obtain ⟨z, hz, rfl⟩ := hy
    simp only [Function.comp_apply]
    rw [hΦcΦ z (ball_subset_closedBall (hHB hz)), hΦiΦ z (hHB hz)]
  -- the connected set `K = Φ(∂𝔻) ∪ ray`
  obtain ⟨p₀, hp₀B, hp₀max⟩ := hcomp.exists_isMaxOn hBne continuous_re.continuousOn
  have hre : ∀ y ∈ Φ '' B, y.re ≤ p₀.re := fun y hy => hp₀max hy
  have hp₀U : p₀ ∉ U := by
    intro hp
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hUo p₀ hp
    have hm : p₀ + ((ε / 2 : ℝ) : ℂ) ∈ U := hεU (by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]; linarith)
    have := hre _ (hUB hm)
    simp at this; linarith
  set ray : Set ℂ := (fun t : ℝ => p₀ + (t : ℂ)) '' Ici 0 with hray
  set K : Set ℂ := Φ '' sphere 0 1 ∪ ray with hK
  have hp₀S : p₀ ∈ Φ '' sphere 0 1 := l214_mem_sphere_image hp₀B hp₀U
  have hp₀ray : p₀ ∈ ray := ⟨0, mem_Ici.2 le_rfl, by simp⟩
  have hSconn : IsConnected (Φ '' sphere (0 : ℂ) 1) :=
    (isConnected_sphere (by simp) 0 zero_le_one).image _ (hc.mono sphere_subset_closedBall)
  have hrayconn : IsConnected ray :=
    (isConnected_Ici).image _ (by fun_prop)
  have hKconn : IsConnected K := IsConnected.union ⟨p₀, hp₀S, hp₀ray⟩ hSconn hrayconn
  have hKG : Disjoint K G := by
    rw [Set.disjoint_left]
    rintro y (⟨ζ, hζ, rfl⟩ | ⟨t, ht, rfl⟩) hyG
    · obtain ⟨z, hz, hzζ⟩ := hyG
      have := hinj (ball_subset_closedBall (hHB hz)) (sphere_subset_closedBall hζ) hzζ
      have h1 := mem_ball_zero_iff.1 (hHB hz)
      rw [this, mem_sphere_zero_iff_norm.1 hζ] at h1
      exact lt_irrefl _ h1
    · rcases (mem_Ici.1 ht).lt_or_eq with htp | rfl
      · have := hre _ (hGB hyG); simp at this; linarith
      · exact hp₀U (by simpa using hGU hyG)
  -- the nearest point of `Uᶜ` lies in `Φ(∂𝔻)`
  obtain ⟨p, hpU, hpd⟩ := hUo.isClosed_compl.exists_infDist_eq_dist hUc x
  have hpB : p ∈ Φ '' B := by
    have hball : ball x d ⊆ U := ball_infDist_compl_subset
    have : p ∈ closure (ball x d) := by
      rw [closure_ball x hd0.ne']; exact mem_closedBall.2 (by rw [dist_comm, ← hpd])
    exact hcomp.isClosed.closure_subset_iff.2 (hball.trans hUB) this
  have hKd : (K ∩ closedBall x d).Nonempty :=
    ⟨p, Or.inl (l214_mem_sphere_image hpB hpU), mem_closedBall.2 (by rw [dist_comm, ← hpd])⟩
  have hKρ : (K \ ball x ρ).Nonempty := by
    refine ⟨p₀ + ((‖x - p₀‖ + ρ : ℝ) : ℂ), Or.inr ⟨_, mem_Ici.2 (by positivity), rfl⟩, ?_⟩
    rw [mem_ball, not_lt, dist_eq_norm]
    have h1 := norm_sub_norm_le (((‖x - p₀‖ + ρ : ℝ) : ℂ)) (x - p₀)
    have e : p₀ + ((‖x - p₀‖ + ρ : ℝ) : ℂ) - x = ((‖x - p₀‖ + ρ : ℝ) : ℂ) - (x - p₀) := by ring
    rw [e]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
    linarith
  -- the Beurling inequality `C_B (d/ρ)^{1/2} < h(x)`
  have hstr : CB * (d / ρ) ^ (1 / 2 : ℝ) < (g ∘ Φi) x := by
    have e1 : d / ρ = (k⁻¹) ^ 2 := by
      rw [hρ, inv_pow, div_mul_eq_div_div_swap, div_self hd0.ne', one_div]
    have e2 : (d / ρ) ^ (1 / 2 : ℝ) = k⁻¹ := by
      rw [← Real.sqrt_eq_rpow, e1, Real.sqrt_sq (by positivity)]
    have hxw : (g ∘ Φi) x = g w := by
      simp only [Function.comp_apply, hx]; rw [hΦiΦ w (hHB hw)]
    rw [e2, hxw]
    refine lt_of_lt_of_le ?_ hgw
    rw [← div_eq_mul_inv, div_lt_div_iff₀ (by linarith) (by positivity)]
    nlinarith
  obtain ⟨y, ⟨hyV, hyT⟩, -⟩ := hB G K T x d ρ (g ∘ Φi) hGo hxG hd0 hdρ hKconn hKG hKd hKρ
    hharm hbnd hdecay hstr
  -- the set `W = Φ⁻¹(V)`
  set V := connectedComponentIn (G ∩ ball x ρ) x with hV
  have hVo : IsOpen V := (hGo.inter isOpen_ball).connectedComponentIn
  have hVG : V ⊆ G ∩ ball x ρ := connectedComponentIn_subset _ _
  have hxV : x ∈ V := mem_connectedComponentIn ⟨hxG, mem_ball_self hρ0⟩
  have hVB : V ⊆ Φ '' B := fun v hv => hGB (hVG hv).1
  set W : Set ℂ := upperHalfDisc ∩ Φ ⁻¹' V with hW
  have hWim : W = Φc '' V := by
    ext z; constructor
    · rintro ⟨hz, hzV⟩
      exact ⟨Φ z, hzV, hΦcΦ z (ball_subset_closedBall (hHB hz))⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨z, hz, rfl⟩ := (hVG hv).1
      rw [hΦcΦ z (ball_subset_closedBall (hHB hz))]
      exact ⟨hz, hv⟩
  refine ⟨W, (hc.mono (hHB.trans ball_subset_closedBall)).isOpen_inter_preimage hHo hVo, ?_,
    inter_subset_left, ⟨hw, hxV⟩, ?_, ?_⟩
  · rw [hWim]
    exact (isPreconnected_connectedComponentIn).image _ (hΦcC.mono hVB)
  · rintro _ ⟨z, ⟨-, hz⟩, rfl⟩; exact (hVG hz).2
  · obtain ⟨a, ⟨ha1, hac⟩, rfl⟩ := hyT
    have haB : a ∈ B := mem_closedBall_zero_iff.2 ha1.le
    refine ⟨a, ?_, ha1, hac⟩
    have hyB : Φ a ∈ Φ '' B := ⟨a, haB, rfl⟩
    have := ((hΦcC _ hyB).mono hVB).mem_closure_image hyV
    rwa [hΦcΦ a haB, ← hWim] at this

end CONF
end LQGMetric
