/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P28U1Lvl at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28U1Mom
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28U1Geo
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DiamSum

/-!
# DDDF Prop 28 Part 1 Step 1 for the family: one level of the chaining (task P2-DDDF28U)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1348–1362 (`eq:Decouplage`, `eq:inequa`), used in
Prop 28 Step 1 (l. 1418–1424) for the field `φ_δ = φ_{δ,1}` (l. 1648): at scale `2^{-K}`
(`2^{-K} ≥ δ`), `φ_δ = φ_{0,K} + φ_{δ,2^{-K}}` (independent), so a crossing of
`u 2^{-K} R_{2,1} + c ⊆ [0,1]²` is at most `e^{ξ max |φ_{0,K}|}` times its crossing for
`φ_{δ,2^{-K}}`, and the `ℓ^q` norm `ZqG` of a family `J` of them has mean
`≤ (|J| C)^{1/q} 2^{-K} λ` when `E L_{2,1}(φ_{2^K δ})^q ≤ C λ^q` (`lintegral_ZqG`, scaling
`lintegral_len21V_pow`). As in `S6DiamLvl` the maximum is bounded by the `ℓ^q` norm instead of
DDDF's union bound over the tails.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6P28U

open LFPP T20E Blueprint WhiteNoise S6D SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- the shifted squares lie in `[0,1]²` -/
theorem hmS_sub {K i j : ℕ} (hi : i + 2 ≤ 2 ^ K) (hj : j + 2 ≤ 2 ^ K) (e : Fin 4) :
    T20B.mot K (hmS K i j e).1 (hmS K i j e).2 '' (rectAB 2 1).toSet ⊆ closedUnitSquare := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_rectAB_toSet] at hx
  obtain ⟨⟨x1, x2⟩, ⟨y1, y2⟩⟩ := hx
  have e2 : ∀ a : ℕ, a + 2 ≤ 2 ^ K → ((a : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K ≤ 1 := fun a ha => by
    have h1 : ((a : ℝ) + 2) ≤ 2 ^ K := by exact_mod_cast ha
    rw [inv_pow, mul_inv_le_iff₀ (by positivity)]; linarith
  have hi' := e2 i hi
  have hj' := e2 j hj
  have hp : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ K := by positivity
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  obtain rfl | rfl | rfl | rfl : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by fin_cases e <;> simp
  · obtain ⟨e1, e2⟩ := mot_eH K (i : ℤ) (j : ℤ) x
    simp only [hmS, Matrix.cons_val_zero] at e1 e2 ⊢
    simp only [closedUnitSquare, Set.mem_ofPred_eq]
    rw [e1, e2]; push_cast
    refine ⟨by positivity, by nlinarith, by positivity, by nlinarith⟩
  · obtain ⟨e1, e2⟩ := mot_eH K (i : ℤ) ((j + 1 : ℕ) : ℤ) x
    simp only [hmS, Matrix.cons_val_one, Matrix.cons_val_zero] at e1 e2 ⊢
    simp only [closedUnitSquare, Set.mem_ofPred_eq]
    rw [e1, e2]; push_cast
    refine ⟨by positivity, by nlinarith, by positivity, by nlinarith⟩
  · obtain ⟨e1, e2⟩ := mot_eV K ((i + 1 : ℕ) : ℤ) (j : ℤ) x
    simp only [hmS] at e1 e2 ⊢
    simp only [Matrix.cons_val] at e1 e2 ⊢
    simp only [closedUnitSquare, Set.mem_ofPred_eq]
    rw [e1, e2]; push_cast
    refine ⟨by nlinarith, by nlinarith, by positivity, by nlinarith⟩
  · obtain ⟨e1, e2⟩ := mot_eV K ((i + 2 : ℕ) : ℤ) (j : ℤ) x
    simp only [hmS] at e1 e2 ⊢
    simp only [Matrix.cons_val] at e1 e2 ⊢
    simp only [closedUnitSquare, Set.mem_ofPred_eq]
    rw [e1, e2]; push_cast
    refine ⟨by nlinarith, by nlinarith, by positivity, by nlinarith⟩

/-- the `ℓ^q` norm of the crossing lengths of a finite family of moved `2^{-K} R_{2,1}` -/
def ZqG (ξ : ℝ) (f : ℂ → ℝ) (K q : ℕ) {ι : Type*} (J : Finset ι) (j : ι → Circle × ℂ) :
    ℝ≥0∞ :=
  (∑ r ∈ J, len21 ξ f K (j r) ^ q) ^ ((q : ℝ)⁻¹)

lemma len21_le_ZqG {f : ℂ → ℝ} {K q : ℕ} (hq : q ≠ 0) {ι : Type*} {J : Finset ι}
    {j : ι → Circle × ℂ} {r : ι} (hr : r ∈ J) : len21 ξ f K (j r) ≤ ZqG ξ f K q J j := by
  rw [← ENNReal.pow_rpow_inv_natCast hq (len21 ξ f K (j r))]
  exact ENNReal.rpow_le_rpow (Finset.single_le_sum (f := fun r => len21 ξ f K (j r) ^ q)
    (fun _ _ => zero_le) hr) (by positivity)

lemma measurable_comap_ZqG {Ω' : Type*} (G : Ω' → ℂ → ℝ) (hGc : ∀ ω, Continuous (G ω))
    (K q : ℕ) {ι : Type*} (J : Finset ι) (j : ι → Circle × ℂ) :
    Measurable[MeasurableSpace.comap G inferInstance] (fun ω => ZqG ξ (G ω) K q J j) := by
  letI : MeasurableSpace Ω' := MeasurableSpace.comap G inferInstance
  have hm' : ∀ x, Measurable fun ω => G ω x :=
    fun x => (measurable_pi_apply x).comp (comap_measurable G)
  refine Measurable.pow_const (Finset.measurable_sum _ fun r _ => ?_) _
  exact (measurable_crossLenIn (Y := fun x ω => G ω x)
    ((rectAB 2 1).isCompact_toSet.image (by unfold T20B.mot; fun_prop)) hGc hm').pow_const _

/-- **the mean of the `ℓ^q` norm** (`eq:inequa`, second factor, for `φ_{δ,2^{-K}}`) -/
theorem lintegral_ZqG (hW : IsWhiteNoise P W) {δ : ℝ} {K : ℕ} (hδ : 0 < δ)
    (hδK : δ ≤ (2 : ℝ)⁻¹ ^ K) {q : ℕ} (hq : 2 ≤ q) {C lam : ℝ} (hC0 : 0 ≤ C) (hlam : 0 ≤ lam)
    (hC : ∫⁻ ω, rectLen ξ (fun x => phiVer W P ((2 : ℝ) ^ K * δ) 1 x ω) (rectAB 2 1) ^ q ∂P ≤
      ENNReal.ofReal (C * lam ^ q)) {ι : Type*} (J : Finset ι) (j : ι → Circle × ℂ) :
    ∫⁻ ω, ZqG ξ (fun x => phiVer W P δ ((2 : ℝ)⁻¹ ^ K) x ω) K q J j ∂P ≤
      ENNReal.ofReal ((J.card * C) ^ ((q : ℝ)⁻¹) * ((2 : ℝ)⁻¹ ^ K * lam)) := by
  have hP := hW.isProbabilityMeasure
  have hφ := isPhiVersion_phiVer hW hδ hδK
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : q ≠ 0 := by omega
  have hmeas : ∀ r, Measurable fun ω =>
      len21 ξ (fun x => phiVer W P δ ((2 : ℝ)⁻¹ ^ K) x ω) K (j r) ^ q := fun r =>
    (measurable_crossLenIn ((rectAB 2 1).isCompact_toSet.image (by unfold T20B.mot; fun_prop))
      hφ.cont hφ.meas).pow_const _
  have h1 := lintegral_rpow_inv_le (P := P)
    (Y := fun ω => ∑ r ∈ J, len21 ξ (fun x => phiVer W P δ ((2 : ℝ)⁻¹ ^ K) x ω) K (j r) ^ q)
    (Finset.measurable_sum _ fun r _ => hmeas r).aemeasurable hq1
  simp only [one_div] at h1
  refine h1.trans ?_
  rw [lintegral_finsetSum _ fun r _ => hmeas r]
  have h2 : ∑ r ∈ J, ∫⁻ ω, len21 ξ (fun x => phiVer W P δ ((2 : ℝ)⁻¹ ^ K) x ω) K (j r) ^ q ∂P ≤
      ENNReal.ofReal (J.card * (((2 : ℝ)⁻¹ ^ K) ^ q * (C * lam ^ q))) := by
    calc ∑ r ∈ J, ∫⁻ ω, len21 ξ (fun x => phiVer W P δ ((2 : ℝ)⁻¹ ^ K) x ω) K (j r) ^ q ∂P
        ≤ ∑ _r ∈ J, ENNReal.ofReal (((2 : ℝ)⁻¹ ^ K) ^ q * (C * lam ^ q)) := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [lintegral_len21V_pow hW hδ hδK, ENNReal.ofReal_mul (by positivity)]
          gcongr
      _ = ENNReal.ofReal (J.card * (((2 : ℝ)⁻¹ ^ K) ^ q * (C * lam ^ q))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
  refine (ENNReal.rpow_le_rpow h2 (by positivity)).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  congr 1
  rw [show (J.card : ℝ) * (((2 : ℝ)⁻¹ ^ K) ^ q * (C * lam ^ q)) =
      (J.card * C) * (((2 : ℝ)⁻¹ ^ K) * lam) ^ q by rw [mul_pow]; ring,
    Real.mul_rpow (by positivity) (by positivity), Real.pow_rpow_inv_natCast (by positivity) hq0]

/-- `φ_δ = φ_{0,K} + φ_{δ,2^{-K}}` a.s. for all `x` (`δ ≤ 2^{-K}`) -/
theorem ae_phiVer_split (hW : IsWhiteNoise P W) {δ : ℝ} {K : ℕ} (hδ : 0 < δ)
    (hδK : δ ≤ (2 : ℝ)⁻¹ ^ K) :
    ∀ᵐ ω ∂P, ∀ x, phiVer W P δ 1 x ω = phiMN W P 0 K x ω + phiVer W P δ ((2 : ℝ)⁻¹ ^ K) x ω := by
  have hK1 : (2 : ℝ)⁻¹ ^ K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h1 := isPhiVersion_phiVer hW hδ hδK
  have h2 := isPhiVersion_phiMN (P := P) hW (Nat.zero_le K)
  have h3 := isPhiVersion_phiVer hW hδ (hδK.trans hK1)
  have h2' : ∀ x, (fun ω => phiMN W P 0 K x ω) =ᵐ[P] phi W ((2 : ℝ)⁻¹ ^ K) 1 x := fun x => by
    have := h2.ae_eq x; rwa [pow_zero] at this
  filter_upwards [phi_version_add_ae hW hδ hδK hK1 h1.cont h2.cont h3.cont h1.ae_eq h2'
    h3.ae_eq] with ω hω x
  rw [hω x, add_comm]

/-- **one level of the chaining in mean** (`eq:inequa` for `φ_δ`): independence of `φ_{0,K}` and
`φ_{δ,2^{-K}}`, the maximum bound (2.11) and `lintegral_ZqG` -/
theorem level_mean (hW : IsWhiteNoise P W) {K₂ : ℝ}
    (hK₂ : ∀ (n : ℕ) (Y : ℂ → Ω → ℝ), (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ n)⁻¹ 1 x) →
      (∀ ω, Continuous fun x => Y x ω) →
      Integrable (fun ω => Real.exp (ξ * ⨆ z : ferniqueBox 0 1, |Y z ω|)) P ∧
      ∫ ω, Real.exp (ξ * ⨆ z : ferniqueBox 0 1, |Y z ω|) ∂P ≤ (4 : ℝ) ^ (ξ * n + K₂ * √n))
    {δ : ℝ} {K : ℕ} (hδ : 0 < δ) (hδK : δ ≤ (2 : ℝ)⁻¹ ^ K) {q : ℕ} (hq : 2 ≤ q) {C lam : ℝ}
    (hC0 : 0 ≤ C) (hlam : 0 ≤ lam)
    (hC : ∫⁻ ω, rectLen ξ (fun x => phiVer W P ((2 : ℝ) ^ K * δ) 1 x ω) (rectAB 2 1) ^ q ∂P ≤
      ENNReal.ofReal (C * lam ^ q)) {ι : Type*} (J : Finset ι) (j : ι → Circle × ℂ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (ξ * supAbs (fun z => phiMN W P 0 K z ω))) *
        ZqG ξ (fun x => phiVer W P δ ((2 : ℝ)⁻¹ ^ K) x ω) K q J j ∂P ≤
      ENNReal.ofReal ((4 : ℝ) ^ (ξ * K + K₂ * √(K : ℝ)) *
        ((J.card * C) ^ ((q : ℝ)⁻¹) * ((2 : ℝ)⁻¹ ^ K * lam))) := by
  have hP := hW.isProbabilityMeasure
  have hφF := isPhiVersion_phiMN (P := P) hW (Nat.zero_le K)
  have hφG := isPhiVersion_phiVer hW hδ hδK
  set F : Ω → ℂ → ℝ := fun ω x => phiMN W P 0 K x ω
  set G : Ω → ℂ → ℝ := fun ω x => phiVer W P δ ((2 : ℝ)⁻¹ ^ K) x ω
  have hFm : Measurable F := measurable_pi_iff.2 fun x => hφF.meas x
  have hGm : Measurable G := measurable_pi_iff.2 fun x => hφG.meas x
  have hGF : IndepFun G F P :=
    indepFun_phi_version hW (a := δ) (b := (2 : ℝ)⁻¹ ^ K) (c := (2 : ℝ)⁻¹ ^ 0) hδ hδK
      hφG.meas hφF.meas hφG.ae_eq hφF.ae_eq
  have hind : Indep (MeasurableSpace.comap F inferInstance)
      (MeasurableSpace.comap G inferInstance) P := (IndepFun_iff_Indep F G P).1 hGF.symm
  have hA' : Measurable[MeasurableSpace.comap F inferInstance]
      fun ω => ENNReal.ofReal (Real.exp (ξ * supAbs (F ω))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_comap_supAbs F hφF.cont).const_mul ξ))
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace hFm.comap_le
    hGm.comap_le hind hA' (measurable_comap_ZqG G hφG.cont K q J j),
    ENNReal.ofReal_mul (by positivity)]
  gcongr
  · obtain ⟨hi, hb⟩ := hK₂ K (phiMN W P 0 K)
      (fun x => by have := hφF.ae_eq x; rwa [inv_pow, pow_zero] at this) hφF.cont
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (ξ * supAbs (F ω))) ∂P
        = ENNReal.ofReal (∫ ω, Real.exp (ξ * ⨆ z : ferniqueBox 0 1, |phiMN W P 0 K z ω|) ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ω => (Real.exp_pos _).le)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hb
  · exact lintegral_ZqG hW hδ hδK hq hC0 hlam hC J j

/-- **`eq:Decouplage` for `φ_δ`**: a.s., every crossing of a moved `2^{-K} R_{2,1} ⊆ [0,1]²`
of the family `J` is at most `e^{ξ max |φ_{0,K}|} ZqG(φ_{δ,2^{-K}})` -/
theorem ae_len21_le (hW : IsWhiteNoise P W) (hξ : 0 ≤ ξ) {δ : ℝ} {K : ℕ} (hδ : 0 < δ)
    (hδK : δ ≤ (2 : ℝ)⁻¹ ^ K) {q : ℕ} (hq : q ≠ 0) {ι : Type*} (J : Finset ι)
    (j : ι → Circle × ℂ)
    (hJ : ∀ r ∈ J, T20B.mot K (j r).1 (j r).2 '' (rectAB 2 1).toSet ⊆ closedUnitSquare) :
    ∀ᵐ ω ∂P, ∀ r ∈ J, len21 ξ (fun x => phiVer W P δ 1 x ω) K (j r) ≤
      ENNReal.ofReal (Real.exp (ξ * supAbs (fun z => phiMN W P 0 K z ω))) *
        ZqG ξ (fun x => phiVer W P δ ((2 : ℝ)⁻¹ ^ K) x ω) K q J j := by
  have hφF := isPhiVersion_phiMN (P := P) hW (Nat.zero_le K)
  filter_upwards [ae_phiVer_split hW hδ hδK] with ω hω r hr
  refine (len21_decouple (hω) (fun z hz => abs_le_supAbs (hφF.cont ω) hz) (hJ r hr) hξ).trans ?_
  gcongr
  exact len21_le_ZqG hq hr

end S6P28U
end DDDF
end LQGMetric
