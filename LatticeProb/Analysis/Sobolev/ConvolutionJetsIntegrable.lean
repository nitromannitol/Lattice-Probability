/-
# Mollified compactness for integrable families

For an integrable real function `f` and a test function `g`, the pairing `∫ f g` is bounded by
`‖f‖_{H^s} ‖g‖_{H^{-s}}` (`sobolevDualityBound_of_integrable_isTestFn`): writing `g = 𝓕 (𝓕⁻ g)`,
the multiplication formula moves the Fourier transform onto `f`, and `‖𝓕⁻ g‖` is the Fourier
modulus of the reflection of `g`, which has the same Sobolev norm.

With this duality the derivatives of `f ⋆ ρ`, for a smooth compactly supported `ρ`, are bounded
uniformly over every integrable family with a common compact support and a common `H^s` bound.
The mollified family then has finite `H^s` nets (`exists_finite_sobolev_net_of_uniform_jets`),
which is `FrechetKolmogorovMollifiedCompact`.
-/
import LatticeProb.Analysis.Sobolev.RellichConvolvedCompact
import LatticeProb.Analysis.Sobolev.FrechetKolmogorovReduce

open MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Pointwise ContDiff Convolution

namespace LatticeProb.Sobolev

variable {d : ℕ}

/-- Reflection invariance of `sobolevNormSq`. -/
theorem sobolevNormSq_comp_neg (s : ℝ) (f : Space d → ℝ) :
    sobolevNormSq d s (fun x => f (-x)) = sobolevNormSq d s f := by
  unfold sobolevNormSq
  let A : Space d ≃ₗᵢ[ℝ] Space d := LinearIsometryEquiv.neg ℝ
  have hF : ∀ ξ, 𝓕 (fun x => ((f (-x) : ℝ) : ℂ)) ξ = 𝓕 (fun x => (f x : ℂ)) (-ξ) := by
    intro ξ
    have h := Real.fourier_comp_linearIsometry A (fun x => (f x : ℂ)) ξ
    simpa [A, Function.comp_def] using h
  simp_rw [hF]
  set G : Space d → ℝ≥0∞ := fun ξ => ENNReal.ofReal
    ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2) with hG
  have h := A.measurePreserving.lintegral_comp_emb A.toHomeomorph.measurableEmbedding G
  refine Eq.trans ?_ h
  refine lintegral_congr fun ξ => ?_
  simp [G, A, norm_neg]

/-- **Duality of an integrable function against a test function.**  For an integrable real `f`
and a test function `g`, `|∫ f g|² ≤ ‖f‖²_{H^s} ‖g‖²_{H^{-s}}`. -/
theorem sobolevDualityBound_of_integrable_isTestFn (s : ℝ) {D : Set (Space d)}
    {f g : Space d → ℝ} (hf : Integrable f) (hg : IsTestFn D g) :
    ENNReal.ofReal (|∫ x, f x * g x| ^ 2) ≤ sobolevNormSq d s f * sobolevNormSq d (-s) g := by
  set F : Space d → ℂ := fun x => (f x : ℂ) with hFdef
  set G : Space d → ℂ := fun x => (g x : ℂ) with hGdef
  have hF1 : Integrable F := hf.ofReal
  have hg1 : Integrable g := hg.integrable
  have hG1 : Integrable G := hg1.ofReal
  have hGc : Continuous G := Complex.continuous_ofReal.comp hg.1.continuous
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hg.2.1.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := Complex.ofRealCLM.contDiff.comp hg.1
  set φ : 𝓢(Space d, ℂ) := hg₁.toSchwartzMap hg₂ with hφ
  have hφG : (φ : Space d → ℂ) = G := funext fun x => by simp [hφ, G]
  have hFG1 : Integrable (𝓕 G) := by
    have h : Integrable (𝓕 (φ : Space d → ℂ)) := (𝓕 φ).integrable (μ := volume)
    rwa [hφG] at h
  have hψ1 : Integrable (𝓕⁻ G) := by
    have h := (𝓕⁻ φ).integrable (μ := volume)
    rwa [SchwartzMap.fourierInv_coe, hφG] at h
  have hinv : 𝓕 (𝓕⁻ G) = G := hGc.fourier_fourierInv_eq hG1 hFG1
  have hflip : ∫ ξ, 𝓕 F ξ • 𝓕⁻ G ξ = ∫ x, F x • 𝓕 (𝓕⁻ G) x := by
    have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
      (L := innerₗ (Space d)) Real.continuous_fourierChar continuous_inner hF1 hψ1
    first | exact h | simpa using! h
  have h1 : ((∫ x, f x * g x : ℝ) : ℂ) = ∫ ξ, 𝓕 F ξ • 𝓕⁻ G ξ := by
    rw [hflip, hinv, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [F, G]
  have hrefl : ∀ ξ, ‖𝓕⁻ G ξ‖ = ‖𝓕 (fun x => ((g (-x) : ℝ) : ℂ)) ξ‖ := by
    intro ξ
    rw [Real.fourierInv_eq_fourier_comp_neg]
  have hg'1 : Integrable (fun x => g (-x)) :=
    (hg.1.continuous.comp continuous_neg).integrable_of_hasCompactSupport
      (by simpa [Function.comp_def] using hg.2.1.comp_homeomorph (Homeomorph.neg (Space d)))
  have hpair := lintegral_fourier_pairing_le s hf hg'1
  rw [sobolevNormSq_comp_neg] at hpair
  have hle : ENNReal.ofReal |∫ x, f x * g x|
      ≤ (sobolevNormSq d s f) ^ ((1 : ℝ) / 2) * (sobolevNormSq d (-s) g) ^ ((1 : ℝ) / 2) := by
    calc ENNReal.ofReal |∫ x, f x * g x| = ‖((∫ x, f x * g x : ℝ) : ℂ)‖ₑ := by
          rw [← ofReal_norm]; simp
      _ = ‖∫ ξ, 𝓕 F ξ • 𝓕⁻ G ξ‖ₑ := by rw [h1]
      _ ≤ ∫⁻ ξ, ‖𝓕 F ξ • 𝓕⁻ G ξ‖ₑ := enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ ξ, ENNReal.ofReal (‖𝓕 F ξ‖ * ‖𝓕 (fun x => ((g (-x) : ℝ) : ℂ)) ξ‖) := by
          refine lintegral_congr fun ξ => ?_
          rw [← ofReal_norm, norm_smul, hrefl]
      _ ≤ _ := hpair
  rw [ENNReal.ofReal_pow (abs_nonneg _)]
  calc _ ≤ ((sobolevNormSq d s f) ^ ((1 : ℝ) / 2)
        * (sobolevNormSq d (-s) g) ^ ((1 : ℝ) / 2)) ^ 2 := pow_le_pow_left' hle 2
    _ = _ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast
          (sobolevNormSq d (-s) g ^ ((1 : ℝ) / 2)), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

/-- **Uniform pairing bound for integrable functions.**  A compact family of test functions with
jointly continuous jets pairs boundedly with every integrable function of bounded `H^s` norm. -/
theorem exists_uniform_integrable_pairing_bound {α : Type*}
    [TopologicalSpace α] [CompactSpace α] (g : α → Space d → ℝ)
    {K : Set (Space d)} (hK : IsCompact K)
    (hsm : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (g p))
    (hsupp : ∀ p, tsupport (g p) ⊆ K)
    (hcont : ∀ n : ℕ,
      Continuous (fun z : α × Space d => iteratedFDeriv ℝ n (g z.1) z.2))
    (s : ℝ) {C : ℝ} (hC0 : 0 ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∀ p (φ : Space d → ℝ),
      Integrable φ → sobolevNormSq d s φ ≤ ENNReal.ofReal C → |∫ x, φ x * g p x| ≤ B := by
  obtain ⟨A, hA, hkernel⟩ :=
    exists_uniform_sobolev_kernel_bound g hK hsm hsupp hcont (-s)
  refine ⟨Real.sqrt (C * A) + 1, by positivity, ?_⟩
  intro p φ hφ hCφ
  have hg : IsTestFn K (g p) :=
    ⟨hsm p, hK.of_isClosed_subset (isClosed_tsupport _) (hsupp p), hsupp p⟩
  have h2 : ENNReal.ofReal (|∫ x, φ x * g p x| ^ 2) ≤ ENNReal.ofReal (C * A) := by
    rw [ENNReal.ofReal_mul hC0]
    exact (sobolevDualityBound_of_integrable_isTestFn s hφ hg).trans
      (mul_le_mul' hCφ (hkernel p))
  have h3 : |∫ x, φ x * g p x| ^ 2 ≤ C * A :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC0 hA)).1 h2
  have h4 : |∫ x, φ x * g p x| ≤ Real.sqrt (C * A) :=
    calc |∫ x, φ x * g p x| = Real.sqrt (|∫ x, φ x * g p x| ^ 2) :=
          (Real.sqrt_sq (abs_nonneg _)).symm
      _ ≤ Real.sqrt (C * A) := Real.sqrt_le_sqrt h3
  linarith

/-- All directional derivatives of the convolution of a locally integrable function with a test
function are differentiated-kernel convolutions. -/
theorem rellichDirectionalKernel_convReal_of_locallyIntegrable {R : Set (Space d)}
    {φ ρ : Space d → ℝ} (hφ : LocallyIntegrable φ volume) (hρ : IsTestFn R ρ)
    (k : ℕ) (v : Fin k → Space d) :
    rellichDirectionalKernel (convReal φ ρ) k v =
      convReal φ (rellichDirectionalKernel ρ k v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    ext x
    rw [rellichDirectionalKernel, ih (Fin.tail v)]
    let κ := rellichDirectionalKernel ρ k (Fin.tail v)
    have hκ := isTestFn_directionalKernel hρ k (Fin.tail v)
    have hd := hκ.2.1.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hφ
      (hκ.1.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)) x
    change fderiv ℝ (convReal φ κ) x (v 0) =
      convReal φ (fun y => fderiv ℝ κ y (v 0)) x
    rw [show fderiv ℝ (convReal φ κ) x =
      (φ ⋆[(ContinuousLinearMap.mul ℝ ℝ).precompR (Space d), volume]
        fderiv ℝ κ) x from hd.fderiv]
    exact convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hφ (hκ.2.1.fderiv ℝ)
      ((hκ.1.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous) x (v 0)

/-- The topological support of a convolution lies in the sum of the two supports. -/
theorem tsupport_convReal_subset_add {K : Set (Space d)} (hK : IsCompact K)
    {φ ρ : Space d → ℝ} (hφ : tsupport φ ⊆ K) (hρ : HasCompactSupport ρ) :
    tsupport (convReal φ ρ) ⊆ tsupport ρ + K := by
  apply closure_minimal
  · exact (support_convolution_subset_swap (ContinuousLinearMap.mul ℝ ℝ)).trans
      (add_subset_add subset_closure (subset_closure.trans hφ))
  · exact (hρ.isCompact.add hK).isClosed

/-- Every derivative of `φ ⋆ ρ` is bounded uniformly over the integrable functions `φ` supported
in a fixed compact set with a fixed `H^s` bound. -/
theorem exists_convReal_derivative_bound_of_integrable {K₀ : Set (Space d)}
    (hK₀ : IsCompact K₀) {ρ : Space d → ℝ}
    (hρsm : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρcs : HasCompactSupport ρ)
    (s : ℝ) {C : ℝ} (hC0 : 0 ≤ C) (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ φ : Space d → ℝ, Integrable φ → tsupport φ ⊆ K₀ →
      sobolevNormSq d s φ ≤ ENNReal.ofReal C → ∀ x,
        ‖iteratedFDeriv ℝ k (convReal φ ρ) x‖ ≤ B := by
  classical
  let K := tsupport ρ + K₀
  have hK : IsCompact K := hρcs.isCompact.add hK₀
  let V := Metric.closedBall (0 : Fin k → Space d) 2
  have hV : IsCompact V := isCompact_closedBall 0 2
  let instK : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let instV : CompactSpace V := isCompact_iff_compactSpace.mp hV
  let P := K × V
  let L := K - tsupport ρ
  have hL : IsCompact L := by
    rw [show L = K - tsupport ρ from rfl, ← Set.sub_image_prod]
    exact (hK.prod hρcs.isCompact).image (continuous_fst.sub continuous_snd)
  have hρ : IsTestFn (tsupport ρ) ρ := ⟨hρsm, hρcs, subset_rfl⟩
  let g (p : P) (t : Space d) :=
    rellichDirectionalKernel ρ k p.2.val (p.1.val - t)
  have htest : ∀ p : P, IsTestFn L (g p) := by
    intro p
    have ht := (isTestFn_directionalKernel hρ k p.2.val).comp_sub_left p.1.val
    refine ⟨ht.1, ht.2.1, ht.2.2.trans ?_⟩
    intro t ht
    exact ⟨p.1.val, p.1.property, p.1.val - t, ht, by abel_nf⟩
  have hjoint : ContDiff ℝ (⊤ : ℕ∞)
      (Function.uncurry (fun p : Space d × (Fin k → Space d) =>
        fun t => rellichDirectionalKernel ρ k p.2 (p.1 - t))) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : (Space d × (Fin k → Space d)) × Space d =>
          (z.1.2, z.1.1 - z.2)) :=
      contDiff_fst.snd.prodMk (contDiff_fst.fst.sub contDiff_snd)
    exact (contDiff_directionalKernel hρsm k).comp hmap
  have hcont : ∀ n : ℕ,
      Continuous (fun z : P × Space d => iteratedFDeriv ℝ n (g z.1) z.2) := by
    intro n
    have hmap : Continuous (fun z : P × Space d => ((z.1.1.val, z.1.2.val), z.2)) :=
      ((continuous_subtype_val.comp continuous_fst.fst).prodMk
        (continuous_subtype_val.comp continuous_fst.snd)).prodMk continuous_snd
    exact (contDiff_uncurry_iteratedFDeriv hjoint n).continuous.comp hmap
  obtain ⟨B, hB, hpair⟩ := exists_uniform_integrable_pairing_bound g hL
    (fun p => (htest p).1) (fun p => (htest p).2.2) hcont s hC0
  refine ⟨B, hB, ?_⟩
  intro φ hφ hφK hφC x
  have hsm := contDiff_convReal hφ.locallyIntegrable hρsm hρcs
  by_cases hx : x ∈ K
  · let q := iteratedFDeriv ℝ k (convReal φ ρ) x
    apply ContinuousMultilinearMap.opNorm_le_bound hB.le
    intro v
    apply q.toMultilinearMap.bound_of_shell_of_continuous q.cont
      (ε := fun _ => 2) (c := fun _ => (2 : ℝ)) (fun _ => by norm_num)
      (fun _ => by norm_num)
    intro w hwlow hwhigh
    have hwV : w ∈ V := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).2
        (fun i => (hwhigh i).le)
    have hp := hpair (⟨x, hx⟩, ⟨w, hwV⟩) φ hφ hφC
    have he : q w = ∫ t, φ t * g (⟨x, hx⟩, ⟨w, hwV⟩) t := by
      rw [← rellichDirectionalKernel_eq_iteratedFDeriv hsm k w x]
      rw [rellichDirectionalKernel_convReal_of_locallyIntegrable hφ.locallyIntegrable hρ k w]
      rfl
    have hprod : (1 : ℝ) ≤ ∏ i, ‖w i‖ := by
      apply Finset.one_le_prod₀
      intro i hi
      simpa using hwlow i
    calc ‖q w‖ = |∫ t, φ t * g (⟨x, hx⟩, ⟨w, hwV⟩) t| := by
          rw [he, Real.norm_eq_abs]
      _ ≤ B := hp
      _ ≤ B * ∏ i, ‖w i‖ := by nlinarith
  · have hz : iteratedFDeriv ℝ k (convReal φ ρ) x = 0 := by
      by_contra hn
      exact hx ((tsupport_convReal_subset_add hK₀ hφK hρcs)
        (support_iteratedFDeriv_subset k hn))
    rw [hz, norm_zero]
    exact hB.le

/-- One constant controls all derivatives of `φ ⋆ ρ` through a given order. -/
theorem exists_convReal_uniform_jets_of_integrable {K₀ : Set (Space d)}
    (hK₀ : IsCompact K₀) {ρ : Space d → ℝ}
    (hρsm : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρcs : HasCompactSupport ρ)
    (s : ℝ) {C : ℝ} (hC0 : 0 ≤ C) (m : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ φ : Space d → ℝ, Integrable φ → tsupport φ ⊆ K₀ →
      sobolevNormSq d s φ ≤ ENNReal.ofReal C → ∀ k ≤ m, ∀ x,
        ‖iteratedFDeriv ℝ k (convReal φ ρ) x‖ ≤ B := by
  classical
  choose B hB hbound using
    fun k => exists_convReal_derivative_bound_of_integrable hK₀ hρsm hρcs s hC0 k
  have ht : (Finset.range (m + 1)).Nonempty := ⟨0, by simp⟩
  let A := (Finset.range (m + 1)).sup' ht B
  have hA : 0 < A := (hB 0).trans_le (Finset.le_sup' B (by simp))
  refine ⟨A, hA, ?_⟩
  intro φ hφ hφK hφC k hk x
  exact (hbound k φ hφ hφK hφC x).trans
    (Finset.le_sup' B (Finset.mem_range.mpr (by omega)))

/-- **Mollified compactness.**  Convolution with a smooth compactly supported `ρ` maps an
integrable family with a common compact support and a common `H^s` bound to a totally bounded
family in `H^s`, with centres the mollified members of the family. -/
theorem frechetKolmogorovMollifiedCompact_holds : FrechetKolmogorovMollifiedCompact := by
  intro d K hK s S ρ hsupp hint hbd hρsm hρcs η hη
  classical
  obtain ⟨C, hC⟩ := hbd
  have hC' : ∀ f ∈ S, sobolevNormSq d s f ≤ ENNReal.ofReal (max C 0) := fun f hf =>
    (hC f hf).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  let U := (fun f => convReal f ρ) '' S
  have hsm : ∀ u ∈ U, ContDiff ℝ (⊤ : ℕ∞) u := by
    rintro _ ⟨f, hf, rfl⟩
    exact contDiff_convReal (hint f hf).locallyIntegrable hρsm hρcs
  have hsuppU : ∀ u ∈ U, tsupport u ⊆ tsupport ρ + K := by
    rintro _ ⟨f, hf, rfl⟩
    exact tsupport_convReal_subset_add hK (hsupp f hf) hρcs
  have hjets : ∀ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ u ∈ U, ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k u x‖ ≤ B := by
    intro m
    obtain ⟨B, hB, hb⟩ :=
      exists_convReal_uniform_jets_of_integrable hK hρsm hρcs s (le_max_right C 0) m
    refine ⟨B, hB.le, ?_⟩
    rintro _ ⟨f, hf, rfl⟩ k hk x
    exact hb f (hint f hf) (hsupp f hf) (hC' f hf) k hk x
  obtain ⟨T, hTU, hTfin, hnet⟩ :=
    exists_finite_sobolev_net_of_uniform_jets (hρcs.isCompact.add hK) U hsm hsuppU hjets s hη
  let instT : Fintype T := hTfin.fintype
  have hpre : ∀ u : T, ∃ f, f ∈ S ∧ convReal f ρ = u.val := fun u => hTU u.property
  choose pick hpickS hpick using hpre
  let e := Fintype.equivFin T
  refine ⟨Fintype.card T, fun i => pick (e.symm i), fun i => hpickS _, ?_⟩
  intro f hf
  obtain ⟨u, hu, hfu⟩ := hnet (convReal f ρ) ⟨f, hf, rfl⟩
  refine ⟨e ⟨u, hu⟩, ?_⟩
  have hc : convReal (pick (e.symm (e ⟨u, hu⟩))) ρ = u := by
    rw [Equiv.symm_apply_apply, hpick]
  dsimp only
  rw [hc]
  exact hfu

end LatticeProb.Sobolev
