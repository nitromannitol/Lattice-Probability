/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovGermVer2C at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer2B

/-!
# The germ step: the core estimate (task P2-MKD2)

`exists_zsSub_approx`: let `w ∈ L²(P)` be orthogonal to the mean-zero pairings `⟨h, ψ⟩` with
`supp ψ ⊆ O`, and let `f ∈ C_c^∞(ℂ)` with `e = ‖(h, f)_∇ − w‖`. With cutoffs `θ ∈ C_c^∞(V)`
(`θ = 1` off a closed `C ⊆ O`), `ζ` (`= 1` on `supp ∇θ`, `supp ζ ⊆ O`) and the weighted mean
`c = ∫ζ²f / ∫ζ²`, the function `k = θ (f − c) ∈ C_c^∞(V)` satisfies
`‖(h, f)_∇ − (h, k)_∇‖² ≤ e² (2 + K² L)`.

Proof (the plan of `handoff/P2-MKD.md`, step (b)):
1. `p = ζ²(f − c)` is a mean-zero test function supported in `O`; so
   `X := ∫ ζ²(f−c)² = ∫ p f = ⟪(h,f)_∇ − w, ⟨h,p⟩⟫ ≤ e ‖⟨h,p⟩‖` and, by the Schur bound,
   `‖⟨h,p⟩‖² = logCov p p ≤ L ∫ p² ≤ L X`; hence `X ≤ e² L` (the "covariance Poincaré" step).
2. `q = f − k = (1−θ)(f − c) + c` and `g = (1−θ)²(f − c) + c` lie in `C_c^∞(ℂ)`, `Δg` is supported
   in `C ⊆ O`, so `⟪w, (h,g)_∇⟫ = 0`; the IMS identity
   `|∇q|² = ∇f·∇g + (f−c)²|∇θ|²` gives `‖(h,q)_∇‖² ≤ e ‖(h,g)_∇‖ + (2π)⁻¹ K² X`, and
   `‖(h,g)_∇‖² ≤ 2‖(h,q)_∇‖² + π⁻¹ K² X`.

This is the cutoff argument behind Sheffield math/0312099 Thm 2.17 / Berestycki–Powell
arXiv:2404.16642 Lemma 1.53 ("the CM function of `w ⊥ S(O)` is constant on `O`"), written so that
no `L²`-limit of functions is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace Laplacian
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovGermVer

open MarkovGauss MarkovZB MarkovGerm MarkovExt MarkovNorm Blueprint QuantumZipper
  QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

lemma hcs_of_vanish {β : Type*} [Zero β] {φ : ℂ → β} {ψ : ℂ → ℝ} (hφ : HasCompactSupport φ) (h0 : ∀ x, φ x = 0 → ψ x = 0) :
    HasCompactSupport ψ :=
  hφ.mono fun x hx h1 => hx (h0 x h1)

lemma integrable_of_cs {φ : ℂ → ℝ} (hc : Continuous φ) (hs : HasCompactSupport φ) :
    Integrable φ := hc.integrable_of_hasCompactSupport hs

lemma integrable_norm_fderiv_sq {φ : ℂ → ℝ} (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) : Integrable fun z => ‖fderiv ℝ φ z‖ ^ 2 :=
  integrable_of_cs (((smooth_le hs 1).continuous_fderiv one_ne_zero).norm.pow 2)
    (hcs_of_vanish (hc.fderiv (𝕜 := ℝ)) fun x hx => by simp [hx])

set_option maxHeartbeats 1000000 in
/-- **The core estimate of the germ step.** -/
theorem exists_zsSub_approx (hh : IsWholePlaneGFF h P) {V : Opens ℂ} {O C : Set ℂ}
    {θ ζ : ℂ → ℝ} {K Lc : ℝ}
    (hθs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ) (hθ01 : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1)
    (hθc : HasCompactSupport θ) (hθV : tsupport θ ⊆ V)
    (hζs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ) (hζ01 : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1)
    (hζc : HasCompactSupport ζ) (hζO : tsupport ζ ⊆ O)
    (hCc : IsClosed C) (hCO : C ⊆ O) (hθC : ∀ x, x ∉ C → θ =ᶠ[𝓝 x] fun _ => 1)
    (hK : ∀ x, ‖fderiv ℝ θ x‖ ≤ K) (hζθ : ∀ x, fderiv ℝ θ x ≠ 0 → ζ x = 1)
    (hLc : 0 ≤ Lc) (hSchur : ∀ p : ℂ → ℝ, Continuous p → (∀ x, ζ x = 0 → p x = 0) →
      logCov p p ≤ Lc * ∫ x, p x ^ 2)
    (w : Lp ℝ 2 P)
    (hw : ∀ ψ : TestC0, tsupport (ψ.1 : ℂ → ℝ) ⊆ O →
      ⟪(memLp_pair hh ψ).toLp (pairProc h ψ), w⟫ = 0)
    (f : zsSub ((⊤ : Opens ℂ) : Set ℂ)) :
    ∃ k : zsSub (V : Set ℂ), ‖cmLin hh ⊤ f - cmLin hh V k‖ ^ 2 ≤
      ‖cmLin hh ⊤ f - w‖ ^ 2 * (2 + K ^ 2 * Lc) := by
  have hfs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f.1 := f.2.1
  have hfc : HasCompactSupport f.1 := f.2.2.1
  have c1 : ∀ {φ : ℂ → ℝ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → Continuous (fderiv ℝ φ) :=
    fun hφ => (smooth_le hφ 1).continuous_fderiv one_ne_zero
  have d1 : ∀ {φ : ℂ → ℝ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → ∀ z,
      DifferentiableAt ℝ φ z := fun hφ z => (smooth_le hφ 1).differentiable one_ne_zero z
  set e := ‖cmLin hh ⊤ f - w‖ with he
  have he0 : 0 ≤ e := norm_nonneg _
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  -- the weighted mean `c`
  have hζ2i : Integrable fun x => ζ x * ζ x :=
    integrable_of_cs (hζs.continuous.mul hζs.continuous) hζc.mul_right
  have hζfi : Integrable fun x => ζ x * ζ x * f.1 x :=
    integrable_of_cs ((hζs.continuous.mul hζs.continuous).mul hfs.continuous) hζc.mul_right.mul_right
  set A := ∫ x, ζ x * ζ x
  set B := ∫ x, ζ x * ζ x * f.1 x
  set c := B / A
  have hBA : B - c * A = 0 := by
    by_cases hA : A = 0
    · have hz := (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (ζ x)) hζ2i).1 hA
      have hB : B = 0 := integral_eq_zero_of_ae (by
        filter_upwards [hz] with x hx
        simp only [Pi.zero_apply] at hx ⊢
        rw [hx, zero_mul])
      rw [hB, hA]; ring
    · simp only [c]; field_simp; ring
  set F : ℂ → ℝ := fun x => f.1 x - c with hF
  have hFs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := hfs.sub contDiff_const
  have hFd : ∀ z, fderiv ℝ F z = fderiv ℝ f.1 z := fun z => fderiv_sub_const c
  ------------------------------------------------------------------ step 1
  set pf : ℂ → ℝ := fun x => ζ x * (ζ x * F x) with hpf
  have hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) pf := hζs.mul (hζs.mul hFs)
  have hpc : HasCompactSupport pf := hζc.mul_right
  have hpi : Integrable pf := integrable_of_cs hps.continuous hpc
  have hp0 : ∫ x, pf x = 0 := by
    have e1 : pf = fun x => ζ x * ζ x * f.1 x - c * (ζ x * ζ x) := funext fun x => by
      simp only [pf, F]; ring
    rw [e1, integral_sub hζfi (hζ2i.const_mul c), integral_const_mul]
    linarith [hBA]
  set p : TestC0 := ⟨tC hps hpc, hp0⟩
  have hpfun : (p.1 : ℂ → ℝ) = pf := rfl
  have hpO : tsupport (p.1 : ℂ → ℝ) ⊆ O := by
    rw [hpfun]; exact (tsupport_mul_subset_left).trans hζO
  set X := ∫ x, (ζ x * F x) ^ 2
  have hXi : Integrable fun x => (ζ x * F x) ^ 2 :=
    integrable_of_cs ((hζs.continuous.mul hFs.continuous).pow 2)
      (hcs_of_vanish hζc fun x hx => by simp [hx])
  have hX0 : 0 ≤ X := integral_nonneg fun x => sq_nonneg _
  have hXp : ⟪cmLin hh ⊤ f - w, (memLp_pair hh p).toLp (pairProc h p)⟫ = X := by
    rw [inner_sub_left, inner_cmLin_pair, real_inner_comm, hw p hpO, sub_zero, hpfun]
    have e1 : (fun x => pf x * f.1 x) = fun x => (ζ x * F x) ^ 2 + c * pf x := funext fun x => by
      simp only [pf, F]; ring
    rw [e1, integral_add hXi (hpi.const_mul c), integral_const_mul, hp0, mul_zero, add_zero]
  have hMp : ‖(memLp_pair hh p).toLp (pairProc h p)‖ ^ 2 ≤ Lc * X := by
    rw [norm_pair_sq hh, hpfun]
    have hL := hSchur pf hps.continuous fun x hx => by simp [pf, hx]
    refine hL.trans (mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
      (ae_of_all _ fun x => sq_nonneg _) hXi (ae_of_all _ fun x => ?_)) hLc)
    have h1 := hζ01 x
    change (ζ x * (ζ x * F x)) ^ 2 ≤ (ζ x * F x) ^ 2
    rw [mul_pow]
    nlinarith [sq_nonneg (ζ x * F x), (pow_le_one₀ h1.1 h1.2 : ζ x ^ 2 ≤ 1)]
  have hXe : X ≤ e ^ 2 * Lc := by
    set M := ‖(memLp_pair hh p).toLp (pairProc h p)‖
    have h1 : X ≤ e * M := hXp ▸ real_inner_le_norm _ _
    have hM0 : 0 ≤ M := norm_nonneg _
    have h2 : X * X ≤ X * (e ^ 2 * Lc) := by
      have h3 : X * X ≤ (e * M) ^ 2 := by nlinarith
      have h4 : (e * M) ^ 2 ≤ e ^ 2 * (Lc * X) := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_left hMp (sq_nonneg e)
      nlinarith
    rcases hX0.lt_or_eq with hpos | h0
    · exact le_of_mul_le_mul_left h2 hpos
    · rw [← h0]; positivity
  ------------------------------------------------------------------ step 2
  set χ : ℂ → ℝ := fun x => 1 - θ x with hχ
  have hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := contDiff_const.sub hθs
  have hχd : ∀ z, ‖fderiv ℝ χ z‖ = ‖fderiv ℝ θ z‖ := fun z => by
    rw [show fderiv ℝ χ z = -fderiv ℝ θ z from fderiv_const_sub 1, norm_neg]
  have hχ1 : ∀ z, |χ z| ≤ 1 := fun z => abs_le.2 ⟨by simp only [χ]; linarith [hθ01 z],
    by simp only [χ]; linarith [hθ01 z]⟩
  have hθ0 : ∀ x, x ∉ tsupport θ → θ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hf0 : ∀ x, x ∉ tsupport f.1 → f.1 x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport hx
  have hkV : (fun x => θ x * F x) ∈ zeroSpace (V : Set ℂ) :=
    ⟨hθs.mul hFs, hθc.mul_right, (tsupport_mul_subset_left).trans hθV⟩
  have hkT : (fun x => θ x * F x) ∈ zeroSpace ((⊤ : Opens ℂ) : Set ℂ) :=
    ⟨hθs.mul hFs, hθc.mul_right, subset_univ _⟩
  set k : zsSub (V : Set ℂ) := ⟨_, hkV⟩
  set kT : zsSub ((⊤ : Opens ℂ) : Set ℂ) := ⟨_, hkT⟩
  have hkk : cmLin hh V k = cmLin hh ⊤ kT := rfl
  refine ⟨k, ?_⟩
  rw [hkk, ← map_sub]
  set q := f - kT
  have hq : q.1 = fun x => χ x * F x + c := funext fun x => by
    change f.1 x - θ x * F x = _; simp only [χ, F]; ring
  have hqd : ∀ z, fderiv ℝ q.1 z = fderiv ℝ (fun x => χ x * F x) z := fun z => by
    rw [hq]; exact fderiv_add_const c
  set gf : ℂ → ℝ := fun x => χ x * (χ x * F x) + c with hgf
  have hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) gf := (hχs.mul (hχs.mul hFs)).add contDiff_const
  have hgc : HasCompactSupport gf := HasCompactSupport.intro (hfc.union hθc) fun x hx => by
    simp only [mem_union, not_or] at hx
    simp only [gf, χ, F, hθ0 x hx.2, hf0 x hx.1]; ring
  set g : zsSub ((⊤ : Opens ℂ) : Set ℂ) := ⟨gf, hgs, hgc, subset_univ _⟩
  have hgd : ∀ z, fderiv ℝ gf z = fderiv ℝ (fun x => χ x * (χ x * F x)) z := fun z =>
    fderiv_add_const c
  have hgw : ⟪cmLin hh ⊤ g, w⟫ = 0 := by
    refine hw (cmTest0 (zsTest g.2)) ?_
    refine (closure_minimal (fun x hx => ?_) hCc).trans hCO
    by_contra hxC
    apply hx
    have hev : gf =ᶠ[𝓝 x] fun _ => c := by
      filter_upwards [hθC x hxC] with y hy
      simp only [gf, χ, hy]; ring
    have hΔ : Δ gf x = 0 := by
      rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds,
        InnerProductSpace.laplacian_const]; rfl
    change -(2 * Real.pi)⁻¹ * Δ gf x = 0
    rw [hΔ, mul_zero]
  set T := ∫ x, F x ^ 2 * ‖fderiv ℝ θ x‖ ^ 2 with hT
  have hTi : Integrable fun x => F x ^ 2 * ‖fderiv ℝ θ x‖ ^ 2 :=
    integrable_of_cs ((hFs.continuous.pow 2).mul ((c1 hθs).norm.pow 2))
      (hcs_of_vanish (hθc.fderiv (𝕜 := ℝ)) fun x hx => by simp [hx])
  have hT0 : 0 ≤ T := integral_nonneg fun x => by positivity
  have hGi : Integrable fun z => gradInner f.1 g.1 z := by
    refine integrable_of_cs ?_ (hcs_of_vanish (hfc.fderiv (𝕜 := ℝ)) fun x hx => by
      simp [gradInner, hx])
    unfold gradInner
    have h1 := c1 hfs
    have h2 := c1 hgs
    fun_prop
  have hTK : T ≤ K ^ 2 * X := by
    rw [← integral_const_mul]
    refine integral_mono hTi (hXi.const_mul _) fun x => ?_
    by_cases h0 : fderiv ℝ θ x = 0
    · simp only [h0, norm_zero]
      have : 0 ≤ K ^ 2 * (ζ x * F x) ^ 2 := by positivity
      simpa using this
    · simp only [hζθ x h0, one_mul]
      have := pow_le_pow_left₀ (norm_nonneg _) (hK x) 2
      nlinarith [sq_nonneg (F x)]
  have hqpt : ∀ z, ‖fderiv ℝ q.1 z‖ ^ 2 =
      gradInner f.1 g.1 z + F z ^ 2 * ‖fderiv ℝ θ z‖ ^ 2 := fun z => by
    rw [hqd, norm_fderiv_mul_sq (d1 hχs z) (d1 hFs z), hχd]
    congr 1
    unfold gradInner
    rw [hFd, show (g.1 : ℂ → ℝ) = gf from rfl, hgd]
  have hQ : ‖cmLin hh ⊤ q‖ ^ 2 = (2 * Real.pi)⁻¹ * ((∫ z, gradInner f.1 g.1 z) + T) := by
    rw [norm_cmLin_sq, gradEnergy]
    simp_rw [hqpt]
    rw [integral_add hGi hTi]
  have hgpt : ∀ z, ‖fderiv ℝ gf z‖ ^ 2 ≤
      2 * ‖fderiv ℝ q.1 z‖ ^ 2 + 2 * (F z ^ 2 * ‖fderiv ℝ θ z‖ ^ 2) := fun z => by
    have hn : ‖fderiv ℝ gf z‖ ≤ ‖fderiv ℝ q.1 z‖ + |F z| * ‖fderiv ℝ θ z‖ := by
      have e : fderiv ℝ (fun x => χ x * (χ x * F x)) z = χ z • fderiv ℝ (fun x => χ x * F x) z +
          (χ z * F z) • fderiv ℝ χ z := fderiv_mul (d1 hχs z) ((d1 hχs z).mul (d1 hFs z))
      rw [hgd, e, hqd]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (hχ1 z)
      · rw [norm_smul, hχd, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) (hχ1 z))
          (norm_nonneg _)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    have h3 : (|F z| * ‖fderiv ℝ θ z‖) ^ 2 = F z ^ 2 * ‖fderiv ℝ θ z‖ ^ 2 := by
      rw [mul_pow, sq_abs]
    nlinarith [sq_nonneg (‖fderiv ℝ q.1 z‖ - |F z| * ‖fderiv ℝ θ z‖)]
  have hNg : ‖cmLin hh ⊤ g‖ ^ 2 ≤ 2 * ‖cmLin hh ⊤ q‖ ^ 2 + Real.pi⁻¹ * T := by
    rw [norm_cmLin_sq, norm_cmLin_sq, gradEnergy, gradEnergy]
    have hqi := integrable_norm_fderiv_sq q.2.1 q.2.2.1
    have hmono : ∫ z, ‖fderiv ℝ gf z‖ ^ 2 ≤
        ∫ z, (2 * ‖fderiv ℝ q.1 z‖ ^ 2 + 2 * (F z ^ 2 * ‖fderiv ℝ θ z‖ ^ 2)) :=
      integral_mono (integrable_norm_fderiv_sq hgs hgc) ((hqi.const_mul 2).add (hTi.const_mul 2))
        hgpt
    rw [integral_add (hqi.const_mul 2) (hTi.const_mul 2), integral_const_mul,
      integral_const_mul] at hmono
    have hpi : 0 < Real.pi := Real.pi_pos
    have := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹)
    calc (2 * Real.pi)⁻¹ * ∫ z, ‖fderiv ℝ gf z‖ ^ 2 ≤ _ := this
      _ = _ := by rw [← hT]; field_simp
  have hQ' : ‖cmLin hh ⊤ q‖ ^ 2 = ⟪cmLin hh ⊤ f - w, cmLin hh ⊤ g⟫ + (2 * Real.pi)⁻¹ * T := by
    have hgw' := hgw
    rw [real_inner_comm] at hgw'
    rw [inner_sub_left, hgw', sub_zero, inner_cmLin_top hh f g, hQ]; ring
  have hfgle : ⟪cmLin hh ⊤ f - w, cmLin hh ⊤ g⟫ ≤ e * ‖cmLin hh ⊤ g‖ := real_inner_le_norm _ _
  have hN0 : 0 ≤ ‖cmLin hh ⊤ g‖ := norm_nonneg _
  have ha : (2 * Real.pi)⁻¹ * T ≤ T / 6 := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ (by norm_num)
      (by linarith [Real.pi_gt_three])) hT0
  have hb : Real.pi⁻¹ * T ≤ T / 3 := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ (by norm_num) Real.pi_gt_three.le) hT0
  have hen : e * ‖cmLin hh ⊤ g‖ ≤ e ^ 2 + ‖cmLin hh ⊤ g‖ ^ 2 / 4 := by
    nlinarith [sq_nonneg (e - ‖cmLin hh ⊤ g‖ / 2)]
  have h1 : ‖cmLin hh ⊤ q‖ ^ 2 ≤ 2 * e ^ 2 + T := by linarith
  calc ‖cmLin hh ⊤ q‖ ^ 2 ≤ 2 * e ^ 2 + T := h1
    _ ≤ 2 * e ^ 2 + K ^ 2 * (e ^ 2 * Lc) := by
        have := mul_le_mul_of_nonneg_left hXe (sq_nonneg K); linarith
    _ = e ^ 2 * (2 + K ^ 2 * Lc) := by ring

end MarkovGermVer
end LQGMetric
