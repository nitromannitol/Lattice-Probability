/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.Conformal at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualNorm
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# GFF-K3 §3, node C1: conformal invariance of the dual (Dirichlet) norm

Blueprint `blueprint/GFF_K3_BLUEPRINT.md`, §3 node **C1** (TASKS.md R18).  For a conformal map
`φ : D → H` (holomorphic, injective, non-vanishing derivative, `φ '' D = H`) between open sets of
`ℂ` and a finite measure `μ`,

`dualNormSq D (zeroSpace D) μ = dualNormSq H (zeroSpace H) ((μ.restrict D).map φ)`.

Source: Sheffield, *Gaussian free fields for mathematicians* (2007), §2.2 (conformal invariance of
the Dirichlet inner product).  The route is the blueprint's: the map `g ↦ g ∘ φ` sends the test
space `zeroSpace H` onto the test space `zeroSpace D` (with inverse given by the holomorphic
inverse `ψ` of `φ`, `Proofs.Complex.BasicsUnivalent`), the pairings `∫ g d((μ|D).map φ)` agree
with `∫ (g∘φ) d(μ|D)`, and the Dirichlet energies agree because the Jacobian of `φ` is `‖φ'‖²`
(`Pushforward.lintegral_comp_holo`) and `‖∇(g∘φ)‖² = ‖∇g‖²∘φ · ‖φ'‖²` (chain rule).  Concretely a
test function on one side is transported to the other by extending it by `0` off the relevant open
set; the resulting function is automatically `C^∞` (it is `C^∞` on an open set and vanishes off a
compact subset of it) and compactly supported, which is exactly what `zeroSpace` requires.

Deviation: `IsConformalOnto.diffOn` only demands holomorphy *on `D`*; the construction works
because the inverse `ψ` is holomorphic on `H = φ '' D` (`univalentOPH`).  The identities are
stated for the test functions themselves (never for `u ∘ φ` as a global function), since `φ` is
only controlled on `D`.
-/

noncomputable section

open MeasureTheory Filter Set Function
open Classical
open scoped ENNReal

namespace QuantumZipper.K3

variable {φ ψ : ℂ → ℂ} {D H : Set ℂ} {μ ρ : Measure ℂ}

/-! ## The conformal structure -/

/-- A conformal map of `D` onto `H`: holomorphic, injective on `D`, with `φ '' D = H` and
non-vanishing derivative on `D`. -/
structure IsConformalOnto (φ : ℂ → ℂ) (D E : Set ℂ) : Prop where
  isOpen : IsOpen D
  diffOn : DifferentiableOn ℂ φ D
  injOn : Set.InjOn φ D
  image_eq : φ '' D = E
  deriv_ne : ∀ z ∈ D, deriv φ z ≠ 0

namespace IsConformalOnto

/-- The image of a conformal map is open (univalent maps are open). -/
theorem isOpen_target (hφ : IsConformalOnto φ D H) : IsOpen H :=
  hφ.image_eq ▸ CA.isOpen_image_of_injOn' hφ.isOpen hφ.diffOn hφ.injOn

/-- A holomorphic map on an open set is real `C^∞`. -/
theorem contDiffOn (hφ : IsConformalOnto φ D H) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ D :=
  ((hφ.diffOn.contDiffOn hφ.isOpen).restrict_scalars ℝ)

end IsConformalOnto

/-! ## Derivative and norm computations for the chain rule -/

/-- The real Fréchet derivative of a holomorphic map, applied to `1`, is its complex derivative. -/
theorem fderiv_real_apply_one {φ : ℂ → ℂ} {z : ℂ} (h : DifferentiableAt ℂ φ z) :
    fderiv ℝ φ z 1 = deriv φ z := by
  rw [h.fderiv_restrictScalars (𝕜 := ℝ)]
  exact fderiv_apply_one_eq_deriv

/-- The real Fréchet derivative of a holomorphic map is multiplication by the complex derivative. -/
theorem fderiv_real_apply_I {φ : ℂ → ℂ} {z : ℂ} (h : DifferentiableAt ℂ φ z) :
    fderiv ℝ φ z Complex.I = Complex.I * deriv φ z := by
  rw [h.fderiv_restrictScalars (𝕜 := ℝ)]
  have e : Complex.I • (1 : ℂ) = Complex.I := by rw [smul_eq_mul, mul_one]
  calc (fderiv ℂ φ z) Complex.I
      = (fderiv ℂ φ z) (Complex.I • (1 : ℂ)) := by rw [e]
    _ = Complex.I • ((fderiv ℂ φ z) 1) := map_smul _ _ _
    _ = Complex.I * deriv φ z := by rw [fderiv_apply_one_eq_deriv, smul_eq_mul]

/-- Expansion of a real-linear functional on `ℂ` along the basis `1, I`. -/
theorem apply_eq_smul (L : ℂ →L[ℝ] ℝ) (a b : ℝ) :
    L (a • (1 : ℂ) + b • (Complex.I : ℂ)) = a * L 1 + b * L Complex.I := by
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- The Dirichlet integrand of `u` composed with a holomorphic `φ`: the chain rule together with
scaling by `‖φ'‖`, using that a complex scalar multiple of the identity scales a real-linear
functional on `ℂ` by its modulus. -/
theorem norm_sq_apply_mul (L : ℂ →L[ℝ] ℝ) (c : ℂ) :
    (L c) ^ 2 + (L (Complex.I * c)) ^ 2 = (L 1 ^ 2 + L Complex.I ^ 2) * ‖c‖ ^ 2 := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℝ, c = (a : ℂ) + (b : ℂ) * Complex.I :=
    ⟨c.re, c.im, (Complex.re_add_im c).symm⟩
  have hc : ((a : ℂ) + (b : ℂ) * Complex.I) = a • (1 : ℂ) + b • (Complex.I : ℂ) := by
    simp
  have he : Complex.I * (a • (1 : ℂ) + b • (Complex.I : ℂ))
      = (-b) • (1 : ℂ) + a • (Complex.I : ℂ) := by
    simp only [mul_add]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have h1 : L ((a : ℂ) + (b : ℂ) * Complex.I) = a * L 1 + b * L Complex.I := by
    rw [hc, apply_eq_smul L a b]
  have h2 : L (Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I)) = (-b) * L 1 + a * L Complex.I := by
    rw [hc, he, apply_eq_smul L (-b) a]
  have hnorm : ‖((a : ℂ) + (b : ℂ) * Complex.I)‖ ^ 2 = a * a + b * b := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  rw [h1, h2, hnorm]
  ring

/-- `‖∇(u ∘ φ)(z)‖² = ‖u'(φ z)‖² ‖φ'(z)‖²` for holomorphic `φ` and `u : ℂ → ℝ`. -/
theorem norm_fderiv_sq_comp_holo {u : ℂ → ℝ} {φ : ℂ → ℂ} {z : ℂ}
    (hφ : DifferentiableAt ℂ φ z) (hu : DifferentiableAt ℝ u (φ z)) :
    ‖fderiv ℝ (u ∘ φ) z‖ ^ 2 = ‖deriv φ z‖ ^ 2 * ‖fderiv ℝ u (φ z)‖ ^ 2 := by
  have hfd : fderiv ℝ (u ∘ φ) z = (fderiv ℝ u (φ z)).comp (fderiv ℝ φ z) :=
    (hu.hasFDerivAt.comp z (hφ.restrictScalars ℝ).hasFDerivAt).fderiv
  rw [hfd, norm_sq_clm_complex]
  simp only [ContinuousLinearMap.comp_apply]
  rw [fderiv_real_apply_one hφ, fderiv_real_apply_I hφ,
    norm_sq_apply_mul (fderiv ℝ u (φ z)) (deriv φ z),
    ← norm_sq_clm_complex (fderiv ℝ u (φ z))]
  ring

/-! ## Change of variables for the Dirichlet integral -/

/-- The Dirichlet integrand transforms with the Jacobian `‖φ'‖²`: change of variables
(`Pushforward.lintegral_comp_holo`) plus the pointwise chain rule. -/
theorem lintegral_norm_fderiv_sq_comp (hφ : IsConformalOnto φ D H) {u : ℂ → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) :
    ∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ (u ∘ φ) z‖ ^ 2)
      = ∫⁻ w in H, ENNReal.ofReal (‖fderiv ℝ u w‖ ^ 2) := by
  have h := lintegral_comp_holo hφ.isOpen hφ.diffOn hφ.injOn hφ.deriv_ne
    hφ.isOpen.measurableSet (subset_refl D) (fun w => ENNReal.ofReal (‖fderiv ℝ u w‖ ^ 2))
  rw [hφ.image_eq] at h
  rw [h]
  refine setLIntegral_congr_fun hφ.isOpen.measurableSet fun z hz => ?_
  rw [norm_fderiv_sq_comp_holo (hφ.diffOn.differentiableAt (hφ.isOpen.mem_nhds hz))
    (hu.differentiable smooth_ne_zero (φ z)), ENNReal.ofReal_mul (sq_nonneg _)]

/-- **Conformal invariance of the Dirichlet energy.** If `f` (on `D`) and `u` (on `H`) are
globally `C^∞` and agree on `D` as `f = u ∘ φ`, then `(f,f)_∇` on `D` equals `(u,u)_∇` on `H`. -/
theorem dirichletEnergyOn_eq_of_eqOn_comp (hφ : IsConformalOnto φ D H) {f u : ℂ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hfeq : ∀ z ∈ D, f z = u (φ z)) :
    dirichletEnergyOn D f = dirichletEnergyOn H u := by
  have hmeas₁ : AEStronglyMeasurable (fun z => ‖fderiv ℝ f z‖ ^ 2) (volume.restrict D) :=
    ((hf.continuous_fderiv smooth_ne_zero).norm.pow 2).aestronglyMeasurable
  have hmeas₂ : AEStronglyMeasurable (fun w => ‖fderiv ℝ u w‖ ^ 2) (volume.restrict H) :=
    ((hu.continuous_fderiv smooth_ne_zero).norm.pow 2).aestronglyMeasurable
  have h₁ : ∫ z in D, ‖fderiv ℝ f z‖ ^ 2
      = (∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _) hmeas₁
  have h₂ : ∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)
      = ∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ (u ∘ φ) z‖ ^ 2) := by
    refine setLIntegral_congr_fun hφ.isOpen.measurableSet fun z hz => ?_
    have hfd : fderiv ℝ f z = fderiv ℝ (u ∘ φ) z :=
      Filter.EventuallyEq.fderiv_eq (by
        filter_upwards [hφ.isOpen.mem_nhds hz] with w hw
        exact hfeq w hw)
    rw [hfd]
  have h₃ : ∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ (u ∘ φ) z‖ ^ 2)
      = ∫⁻ w in H, ENNReal.ofReal (‖fderiv ℝ u w‖ ^ 2) := lintegral_norm_fderiv_sq_comp hφ hu
  have h₄ : ∫ w in H, ‖fderiv ℝ u w‖ ^ 2
      = (∫⁻ w in H, ENNReal.ofReal (‖fderiv ℝ u w‖ ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _) hmeas₂
  unfold dirichletEnergyOn
  rw [h₁, h₂, h₃, ← h₄]

/-! ## Pairings against the pushforward measure -/

/-- A function whose topological support lies in `D` has the same integral against `μ` and
`μ.restrict D`. -/
theorem integral_eq_setIntegral_of_tsupport_subset {f : ℂ → ℝ} (h : tsupport f ⊆ D) :
    ∫ z, f z ∂μ = ∫ z in D, f z ∂μ :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
    by_contra hne
    exact hz (h (subset_tsupport f hne))).symm

/-- **Change of variables for the pairing.** If `f` is supported in `D` and agrees there with
`u ∘ φ`, then `∫ f dμ = ∫ u d((μ|D).map φ)`. -/
theorem integral_eq_integral_map (hφ : IsConformalOnto φ D H) [IsFiniteMeasure μ]
    {f u : ℂ → ℝ} (hfts : tsupport f ⊆ D) (hu : Continuous u)
    (hfeq : ∀ z ∈ D, f z = u (φ z)) :
    ∫ z, f z ∂μ = ∫ w, u w ∂((μ.restrict D).map φ) := by
  have hae : AEMeasurable φ (μ.restrict D) :=
    ContinuousOn.aemeasurable hφ.diffOn.continuousOn hφ.isOpen.measurableSet
  rw [integral_map hae hu.aestronglyMeasurable, integral_eq_setIntegral_of_tsupport_subset hfts]
  exact integral_congr_ae (by
    filter_upwards [ae_restrict_mem hφ.isOpen.measurableSet] with z hz
    exact hfeq z hz)

/-! ## Transport of the test space -/

/-- A function that is `C^∞` on an open set containing the (compact) support of `f` and vanishes
off that compact set is `C^∞`. -/
theorem contDiff_of_contDiffOn_of_support_subset {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {f : ℂ → ℝ} (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U)
    (hzero : ∀ z ∉ K, f z = 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hf.contDiffAt (hU.mem_nhds hx)
  · have hcompl : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f Kᶜ :=
      ContDiffOn.congr contDiffOn_const fun z hz => hzero z hz
    exact hcompl.contDiffAt (hK.isClosed.isOpen_compl.mem_nhds fun h => hx (hKU h))

/-- `g ↦ g ∘ ψ` extended by `0` off `H`: the transport of a test function from `D` to `H` along
the inverse `ψ : H → D` of the conformal map `φ : D → H`. -/
theorem extByZero_mem_zeroSpace (hφ : IsConformalOnto φ D H) (hψ : IsConformalOnto ψ H D)
    (hφψ : ∀ w ∈ H, φ (ψ w) = w) {f : ℂ → ℝ} (hf : f ∈ zeroSpace D) :
    (fun w => if w ∈ H then f (ψ w) else 0) ∈ zeroSpace H := by
  have hK : IsCompact (φ '' tsupport f) :=
    hf.2.1.image_of_continuousOn (hφ.diffOn.continuousOn.mono hf.2.2)
  have hKsub : φ '' tsupport f ⊆ H := by
    rintro _ ⟨z, hz, rfl⟩
    exact hφ.image_eq ▸ ⟨z, hf.2.2 hz, rfl⟩
  have hsupp : support (fun w => if w ∈ H then f (ψ w) else 0) ⊆ φ '' tsupport f := by
    intro w hw
    have hw' : (fun w => if w ∈ H then f (ψ w) else 0) w ≠ 0 := hw
    have hwH : w ∈ H := by
      by_contra h
      exact hw' (by simp [h])
    have hfw : f (ψ w) ≠ 0 := by simpa [hwH] using hw'
    exact ⟨ψ w, subset_tsupport f hfw, hφψ w hwH⟩
  refine ⟨?_, HasCompactSupport.of_support_subset_isCompact hK hsupp, ?_⟩
  · exact contDiff_of_contDiffOn_of_support_subset hψ.isOpen hK hKsub
      (ContDiffOn.congr ((hf.1.contDiffOn).comp hψ.contDiffOn (Set.mapsTo_univ ψ H))
        fun w hw => by simp [hw])
      fun w hw => by
        by_contra hne
        exact hw (hsupp hne)
  · intro w hw
    exact hKsub (closure_minimal hsupp hK.isClosed hw)

/-- `f ↦ f ∘ φ` extended by `0` off `D`: the transport of a test function from `H` to `D` along
the conformal map `φ : D → H`. -/
theorem precomp_mem_zeroSpace (hφ : IsConformalOnto φ D H) (hψ : IsConformalOnto ψ H D)
    (hψφ : ∀ z ∈ D, ψ (φ z) = z) {g : ℂ → ℝ} (hg : g ∈ zeroSpace H) :
    (fun z => if z ∈ D then g (φ z) else 0) ∈ zeroSpace D := by
  have hK : IsCompact (ψ '' tsupport g) :=
    hg.2.1.image_of_continuousOn (hψ.diffOn.continuousOn.mono hg.2.2)
  have hKsub : ψ '' tsupport g ⊆ D := by
    rintro _ ⟨w, hw, rfl⟩
    exact hψ.image_eq ▸ ⟨w, hg.2.2 hw, rfl⟩
  have hsupp : support (fun z => if z ∈ D then g (φ z) else 0) ⊆ ψ '' tsupport g := by
    intro z hz
    have hz' : (fun z => if z ∈ D then g (φ z) else 0) z ≠ 0 := hz
    have hzD : z ∈ D := by
      by_contra h
      exact hz' (by simp [h])
    have hgz : g (φ z) ≠ 0 := by simpa [hzD] using hz'
    exact ⟨φ z, subset_tsupport g hgz, hψφ z hzD⟩
  refine ⟨?_, HasCompactSupport.of_support_subset_isCompact hK hsupp, ?_⟩
  · exact contDiff_of_contDiffOn_of_support_subset hφ.isOpen hK hKsub
      (ContDiffOn.congr ((hg.1.contDiffOn).comp hφ.contDiffOn (Set.mapsTo_univ φ D))
        fun z hz => by simp [hz])
      fun z hz => by
        by_contra hne
        exact hz (hsupp hne)
  · intro z hz
    exact hKsub (closure_minimal hsupp hK.isClosed hz)

/-- The inverse of a conformal map is conformal. -/
theorem isConformalOnto_symm (hφ : IsConformalOnto φ D H) :
    IsConformalOnto (CA.univalentOPH hφ.isOpen hφ.diffOn hφ.injOn).symm H D where
  isOpen := hφ.isOpen_target
  diffOn := by
    have h := CA.differentiableOn_univalentOPH_symm hφ.isOpen hφ.diffOn hφ.injOn
    rwa [hφ.image_eq] at h
  injOn := by
    intro w₁ hw₁ w₂ hw₂ h
    have h₁ := CA.univalentOPH_apply_symm_apply hφ.isOpen hφ.diffOn hφ.injOn
      (hφ.image_eq ▸ hw₁)
    have h₂ := CA.univalentOPH_apply_symm_apply hφ.isOpen hφ.diffOn hφ.injOn
      (hφ.image_eq ▸ hw₂)
    rw [← h₁, ← h₂, h]
  image_eq := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (CA.univalentOPH hφ.isOpen hφ.diffOn hφ.injOn).map_target (hφ.image_eq ▸ hw)
    · intro hz
      exact ⟨φ z, hφ.image_eq ▸ ⟨z, hz, rfl⟩,
        CA.univalentOPH_symm_apply_apply hφ.isOpen hφ.diffOn hφ.injOn hz⟩
  deriv_ne := by
    intro w hw
    have hw' : w ∈ φ '' D := hφ.image_eq ▸ hw
    have h := CA.hasDerivAt_univalentOPH_symm hφ.isOpen hφ.diffOn hφ.injOn hw'
    rw [h.deriv]
    exact inv_ne_zero (hφ.deriv_ne _ ((CA.univalentOPH hφ.isOpen hφ.diffOn hφ.injOn).map_target hw'))

/-! ## Conformal invariance of the dual norm -/

/-- **Node C1: the dual (Dirichlet) norm is invariant under conformal maps.** -/
theorem dualNormSq_conformal (hφ : IsConformalOnto φ D H) (μ : Measure ℂ) [IsFiniteMeasure μ] :
    dualNormSq D (zeroSpace D) μ = dualNormSq H (zeroSpace H) ((μ.restrict D).map φ) := by
  set ψ : ℂ → ℂ := fun z => (CA.univalentOPH hφ.isOpen hφ.diffOn hφ.injOn).symm z with hψdef
  have hψ : IsConformalOnto ψ H D := isConformalOnto_symm hφ
  have hψφ : ∀ z ∈ D, ψ (φ z) = z := fun z hz =>
    CA.univalentOPH_symm_apply_apply hφ.isOpen hφ.diffOn hφ.injOn hz
  have hφψ : ∀ w ∈ H, φ (ψ w) = w := fun w hw =>
    CA.univalentOPH_apply_symm_apply hφ.isOpen hφ.diffOn hφ.injOn (hφ.image_eq ▸ hw)
  set ν : Measure ℂ := (μ.restrict D).map φ with hνdef
  refine le_antisymm ?_ ?_
  · unfold dualNormSq
    refine iSup₂_le fun f hf => ?_
    set g : ℂ → ℝ := fun w => if w ∈ H then f (ψ w) else 0 with hgdef
    have hgV : g ∈ zeroSpace H := extByZero_mem_zeroSpace hφ hψ hφψ hf.1
    have hE : dirichletEnergyOn H g = dirichletEnergyOn D f :=
      dirichletEnergyOn_eq_of_eqOn_comp hψ hgV.1 hf.1.1 fun w hw => by simp [hgdef, hw]
    have hI : ∫ w, g w ∂ν = ∫ z, f z ∂μ :=
      (integral_eq_integral_map hφ hf.1.2.2 hgV.1.continuous (fun z hz => by
        have hzH : φ z ∈ H := hφ.image_eq ▸ ⟨z, hz, rfl⟩
        simp [hgdef, hzH, hψφ z hz])).symm
    refine le_iSup₂_of_le g ⟨hgV, by rw [hE]; exact hf.2⟩ ?_
    rw [hE, hI]
  · unfold dualNormSq
    refine iSup₂_le fun g hg => ?_
    set f : ℂ → ℝ := fun z => if z ∈ D then g (φ z) else 0 with hfdef
    have hfV : f ∈ zeroSpace D := precomp_mem_zeroSpace hφ hψ hψφ hg.1
    have hE : dirichletEnergyOn D f = dirichletEnergyOn H g :=
      dirichletEnergyOn_eq_of_eqOn_comp hφ hfV.1 hg.1.1 fun z hz => by simp [hfdef, hz]
    have hI : ∫ z, f z ∂μ = ∫ w, g w ∂ν :=
      integral_eq_integral_map hφ hfV.2.2 hg.1.1.continuous (fun z hz => by simp [hfdef, hz])
    refine le_iSup₂_of_le f ⟨hfV, by rw [hE]; exact hg.2⟩ ?_
    rw [hE, hI]

end QuantumZipper.K3
