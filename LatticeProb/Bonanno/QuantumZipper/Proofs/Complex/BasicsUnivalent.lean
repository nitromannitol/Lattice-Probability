/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.BasicsUnivalent at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Univalent maps (EXT-CA node A2)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3.A, node **A2**. If `f` is holomorphic and
injective on an open set `U ⊆ ℂ`, then

* `deriv f z ≠ 0` for `z ∈ U` (`deriv_ne_zero_of_injOn`),
* `f '' V` is open for every open `V ⊆ U` (`isOpen_image_of_injOn`),
* `f` is an open partial homeomorphism `U → f '' U` (`univalentOPH`,
  `univalentHomeomorph : U ≃ₜ f '' U`) whose inverse is holomorphic, with derivative
  `(f' ∘ f⁻¹)⁻¹` (`hasDerivAt_univalentOPH_symm`, `differentiableOn_univalentOPH_symm`).

References: statement = R. B. Burckel, *Classical Analysis in the Complex Plane* (Birkhäuser
2021), Corollary 5.78, p. 363 (`literature/Burckel_ClassicalAnalysisComplexPlane_2021.pdf`,
PDF p. 388). Burckel proves `f' ≠ 0` via isolated zeros of `f'` and removability of isolated
non-differentiability points of the continuous inverse; we follow instead the local
correspondence argument of Ahlfors, *Complex Analysis* (3rd ed. 1979), Ch. 4 §3.3 (the route
fixed by the EXT-CA blueprint), which needs only a local `m`-th root and the inverse function
theorem. The inverse-derivative part follows Burckel's proof (difference quotients, here
`OpenPartialHomeomorph.hasDerivAt_symm`).

Proof of `f' ≠ 0`: if `f - f z₀ = (z - z₀)^m g`, `g z₀ ≠ 0`, `m ≥ 2`, write `g = r^m` with `r`
holomorphic near `z₀` (principal branch of `(g / g z₀)^{1/m}`), so `f - f z₀ = φ^m` with
`φ = (z - z₀) r`, `φ'(z₀) ≠ 0`. By the inverse function theorem `φ` maps every neighbourhood
of `z₀` onto a neighbourhood of `0`; the two points `ε` and `ε ζ` (`ζ` a primitive `m`-th root
of unity) have preimages that `f` identifies, contradicting injectivity.
-/

noncomputable section

open Set Metric Filter Topology Complex

namespace QuantumZipper.CA

variable {f : ℂ → ℂ} {U : Set ℂ}

/-- An injective function on an open set is not locally constant at any point. -/
theorem not_eventually_eq_of_injOn (hU : IsOpen U) (hinj : InjOn f U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ¬ ∀ᶠ z in 𝓝 z₀, f z = f z₀ := by
  intro h
  have h1 : ∀ᶠ z in 𝓝[≠] z₀, (f z = f z₀ ∧ z ∈ U) ∧ z ≠ z₀ :=
    ((h.and (hU.mem_nhds hz₀)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨z, ⟨hfz, hzU⟩, hz⟩ := h1.exists
  exact hz (hinj hzU hz₀ hfz)

/-- **Univalent maps have non-vanishing derivative.** -/
theorem deriv_ne_zero_of_injOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) : deriv f z₀ ≠ 0 := by
  have hA : AnalyticAt ℂ f z₀ := hf.analyticAt (hU.mem_nhds hz₀)
  have hF : AnalyticAt ℂ (fun z => f z - f z₀) z₀ := hA.sub analyticAt_const
  have hne : ¬ ∀ᶠ z in 𝓝 z₀, f z - f z₀ = 0 := by
    intro h
    exact not_eventually_eq_of_injOn hU hinj hz₀ (h.mono fun z hz => sub_eq_zero.1 hz)
  obtain ⟨m, g, hg, hg0, hfg⟩ := hF.exists_eventuallyEq_pow_smul_nonzero_iff.2 hne
  simp only [smul_eq_mul] at hfg
  intro hd
  -- the case `m = 0`
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · have := hfg.self_of_nhds
      simp at this
      exact hg0 this.symm
    · -- `m = 1`: then `deriv f z₀ = g z₀ ≠ 0`
      have h1 : HasDerivAt (fun z => (z - z₀) ^ 1 * g z) (g z₀) z₀ := by
        have := ((hasDerivAt_id z₀).sub_const z₀).mul hg.differentiableAt.hasDerivAt
        simp only [id, sub_self, zero_mul, one_mul, zero_add] at this
        simpa [Pi.mul_def] using this
      have h2 : HasDerivAt (fun z => f z - f z₀) (g z₀) z₀ :=
        h1.congr_of_eventuallyEq hfg
      have h3 : HasDerivAt f (g z₀) z₀ := by
        have := h2.add_const (f z₀)
        simpa using this
      exact hg0 (h3.deriv ▸ hd)
  -- the case `m ≥ 2`
  have hm0 : m ≠ 0 := by omega
  set c : ℂ := g z₀ ^ ((m : ℂ)⁻¹) with hc
  have hcm : c ^ m = g z₀ := cpow_nat_inv_pow _ hm0
  have hc0 : c ≠ 0 := by
    intro h; rw [h, zero_pow hm0] at hcm; exact hg0 hcm.symm
  set r : ℂ → ℂ := fun z => c * (g z / g z₀) ^ ((m : ℂ)⁻¹) with hr
  have hrm : ∀ z, r z ^ m = g z := fun z => by
    simp only [hr, mul_pow, cpow_nat_inv_pow _ hm0, hcm]
    field_simp
  have hrz₀ : r z₀ = c := by simp [hr, div_self hg0]
  -- `r` is holomorphic near `z₀`
  have hslit : ∀ᶠ z in 𝓝 z₀, g z / g z₀ ∈ slitPlane := by
    have hcont : ContinuousAt (fun z => g z / g z₀) z₀ :=
      hg.continuousAt.div_const _
    have : g z₀ / g z₀ ∈ slitPlane := by rw [div_self hg0]; exact one_mem_slitPlane
    exact hcont.eventually_mem (isOpen_slitPlane.mem_nhds this)
  have hgd : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ g z := hg.eventually_analyticAt
  set φ : ℂ → ℂ := fun z => (z - z₀) * r z with hφ
  have hφd : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ φ z := by
    filter_upwards [hslit, hgd] with z hz hgz
    exact (differentiableAt_id.sub_const z₀).mul
      ((differentiableAt_const c).mul ((hgz.differentiableAt.div_const _).cpow_const hz))
  have hφA : AnalyticAt ℂ φ z₀ := by
    obtain ⟨V, hV, hVo, hz₀V⟩ := _root_.eventually_nhds_iff.1 hφd
    exact DifferentiableOn.analyticAt (fun z hz => (hV z hz).differentiableWithinAt)
      (hVo.mem_nhds hz₀V)
  have hφderiv : HasDerivAt φ c z₀ := by
    have hrd : DifferentiableAt ℂ r z₀ := by
      obtain ⟨V, hV, -, hz₀V⟩ := _root_.eventually_nhds_iff.1 (hslit.and hgd)
      exact (differentiableAt_const c).mul
        (((hV z₀ hz₀V).2.differentiableAt.div_const _).cpow_const (hV z₀ hz₀V).1)
    have := ((hasDerivAt_id z₀).sub_const z₀).mul hrd.hasDerivAt
    simp only [id, sub_self, zero_mul, one_mul, zero_add, hrz₀] at this
    rw [add_zero] at this
    exact this
  have hstrict : HasStrictDerivAt φ c z₀ := by
    have := hφA.hasStrictDerivAt
    rwa [hφderiv.deriv] at this
  have hmap : map φ (𝓝 z₀) = 𝓝 0 := by
    have := hstrict.map_nhds_eq hc0
    simpa [hφ] using this
  -- a neighbourhood where everything holds
  have hV : ∀ᶠ z in 𝓝 z₀, z ∈ U ∧ f z - f z₀ = (z - z₀) ^ m * g z :=
    (show ∀ᶠ z in 𝓝 z₀, z ∈ U from hU.mem_nhds hz₀).and hfg
  obtain ⟨V, hVsub, -, -⟩ := _root_.eventually_nhds_iff.1 hV
  have hVn : {z | z ∈ U ∧ f z - f z₀ = (z - z₀) ^ m * g z} ∈ 𝓝 z₀ := hV
  have himg : φ '' {z | z ∈ U ∧ f z - f z₀ = (z - z₀) ^ m * g z} ∈ 𝓝 (0 : ℂ) := by
    rw [← hmap]; exact image_mem_map hVn
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 himg
  have hζ := Complex.isPrimitiveRoot_exp m hm0
  set ζ := exp (2 * Real.pi * I / m)
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have hζn : ‖ζ‖ = 1 := hζ.norm'_eq_one hm0
  set w₁ : ℂ := ((ε / 2 : ℝ) : ℂ)
  have hw₁ : w₁ ∈ ball (0 : ℂ) ε := by
    rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
  have hw₂ : w₁ * ζ ∈ ball (0 : ℂ) ε := by
    rw [mem_ball_zero_iff, norm_mul, hζn, mul_one]; exact mem_ball_zero_iff.1 hw₁
  obtain ⟨z₁, ⟨hz₁U, hz₁f⟩, hφ₁⟩ := hball hw₁
  obtain ⟨z₂, ⟨hz₂U, hz₂f⟩, hφ₂⟩ := hball hw₂
  have hpow : ∀ z, (z - z₀) ^ m * g z = φ z ^ m := fun z => by
    simp only [hφ, mul_pow, hrm]
  have hf12 : f z₁ = f z₂ := by
    have e1 : f z₁ - f z₀ = w₁ ^ m := by rw [hz₁f, hpow, hφ₁]
    have e2 : f z₂ - f z₀ = w₁ ^ m := by rw [hz₂f, hpow, hφ₂, mul_pow, hζ.pow_eq_one, mul_one]
    linear_combination e1 - e2
  have := hinj hz₁U hz₂U hf12
  subst this
  have hw0 : w₁ ≠ 0 := by
    simp only [w₁, ne_eq, ofReal_eq_zero]; linarith
  apply hζ1
  have := hφ₁.symm.trans hφ₂
  exact (mul_eq_left₀ hw0).1 this.symm

/-- **Open mapping for univalent maps**: images of open subsets are open. -/
theorem isOpen_image_of_injOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) {V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ U) : IsOpen (f '' V) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hz, rfl⟩
  have hA : AnalyticAt ℂ f z := hf.analyticAt (hU.mem_nhds (hVU hz))
  rcases hA.eventually_constant_or_nhds_le_map_nhds with h | h
  · exact absurd h (not_eventually_eq_of_injOn hU hinj (hVU hz))
  · exact h (image_mem_map (hV.mem_nhds hz))

theorem isOpen_image_of_injOn' (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) : IsOpen (f '' U) :=
  isOpen_image_of_injOn hU hf hinj hU subset_rfl

/-- A univalent map as an open partial homeomorphism with source `U` and target `f '' U`. -/
def univalentOPH (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) :
    OpenPartialHomeomorph ℂ ℂ :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict (hinj.toPartialEquiv f U) hf.continuousOn
    (by
      intro W hW
      have hW' : IsOpen (Subtype.val '' W) := hU.isOpenMap_subtype_val W hW
      have : (Set.domRestrict U f) '' W = f '' (Subtype.val '' W) := by
        rw [Set.image_image]; rfl
      change IsOpen ((Set.domRestrict U f) '' W)
      rw [this]
      exact isOpen_image_of_injOn hU hf hinj hW' (Subtype.coe_image_subset U W))
    hU

@[simp] theorem univalentOPH_apply (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) (z : ℂ) : univalentOPH hU hf hinj z = f z := rfl

@[simp] theorem univalentOPH_source (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) : (univalentOPH hU hf hinj).source = U := rfl

@[simp] theorem univalentOPH_target (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) : (univalentOPH hU hf hinj).target = f '' U := rfl

/-- A univalent map is a homeomorphism `U ≃ₜ f '' U`. -/
def univalentHomeomorph (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) :
    U ≃ₜ f '' U :=
  (univalentOPH hU hf hinj).toHomeomorphSourceTarget

@[simp] theorem univalentHomeomorph_apply (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) (z : U) : (univalentHomeomorph hU hf hinj z : ℂ) = f z := rfl

/-- The inverse of a univalent map is holomorphic, with derivative `1 / f'(f⁻¹ w)`. -/
theorem hasDerivAt_univalentOPH_symm (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) {w : ℂ} (hw : w ∈ f '' U) :
    HasDerivAt (univalentOPH hU hf hinj).symm
      (deriv f ((univalentOPH hU hf hinj).symm w))⁻¹ w := by
  set e := univalentOPH hU hf hinj
  have hw' : w ∈ e.target := hw
  have hs : e.symm w ∈ U := e.map_target hw'
  exact e.hasDerivAt_symm hw' (deriv_ne_zero_of_injOn hU hf hinj hs)
    ((hf.differentiableAt (hU.mem_nhds hs)).hasDerivAt)

theorem differentiableOn_univalentOPH_symm (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) : DifferentiableOn ℂ (univalentOPH hU hf hinj).symm (f '' U) :=
  fun _ hw => (hasDerivAt_univalentOPH_symm hU hf hinj hw).differentiableAt.differentiableWithinAt

theorem univalentOPH_symm_apply_apply (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) {z : ℂ} (hz : z ∈ U) : (univalentOPH hU hf hinj).symm (f z) = z :=
  (univalentOPH hU hf hinj).left_inv hz

theorem univalentOPH_apply_symm_apply (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) {w : ℂ} (hw : w ∈ f '' U) : f ((univalentOPH hU hf hinj).symm w) = w :=
  (univalentOPH hU hf hinj).right_inv hw

end QuantumZipper.CA
