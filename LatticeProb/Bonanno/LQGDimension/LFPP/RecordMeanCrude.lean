/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.RecordMeanCrude at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordMeanCrudeAux3
import LatticeProb.Bonanno.LQGDimension.Gaussian.ChainingBox
import LatticeProb.Bonanno.LQGDimension.Gaussian.SudakovFernique
import Mathlib.Algebra.Order.Group.CompleteLattice

/-!
# Node `M45`: the crude mean bound (4.5)

`recordMeanCrude : Blueprint.Draft.RecordMeanCrude`.  No blueprint hypotheses are needed.

For `n ≥ 1`, `M = 16^n`, `δ ∈ (0,1)` and a nonempty finite family `F` in the normalized local
family,
`gaussianExpectedMax F (δ⁻¹ logCov) (-k) ≤ C_n (k+1)^{1/4} - k`.

## Proof

* **Gaussian reduction** (`gem_le_chain`).  If `δ⁻¹ logCov` is not positive semidefinite on `F`,
  `multivariateGaussian` is the Dirac mass at `0` and the expected maximum is `-k`.  Otherwise it
  is realised by Gram vectors `v`; the drift `-k` comes out, Sudakov–Fernique replaces `v` by the
  increments `v - v i₀`, and chaining on a box (`ChainBox.chainingBox_bound`) applies as soon as
  `logCov(D, D) ≤ K ‖p c - p c'‖` for `D = cfgComb c - cfgComb c'` and parameters `p` of
  sup-diameter `≤ a`: `E max ≤ 20√5 √(δ⁻¹K) √((d+1)a)`.
* **Small family** (`RecordMeanCrudeAux3.small_canon`, `small_diam`): `d = 2(3M+1)+1`,
  `K = Ksm M`, `a = Dsm M · δ √(k+1)`, so the bound is `C_n (k+1)^{1/4}` (the factors `δ⁻¹` and
  `δ` cancel).
* **Large family** (`large_canon`, `large_diam`): `d = 9`, `K = Kl M`, `a = 18`, so the bound
  is `C_n δ^{-1/2} ≤ C_n (k+1)^{1/4}` because `k + 1 > δ⁻²` for `k = ⌊δ⁻²⌋`.

All covariance estimates come from Lemma 3.1 (`TwoScale.logCov_twoScale_bound`) applied to single
segments (`RecordMeanCrudeAux1`).  The constant `C_n = max Cs Cl` is of order `M³`, `M = 16^n`
(growth constant `~ M`, `~ M` parameters, weight-Lipschitz constant `~ M`, box side `~ M²`),
not `C n` as in the paper; only its finiteness for fixed `n` is used (`LFPP_PLAN.md` §4.1).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension

open Blueprint.Draft

namespace RMCrude

/-- A constant drift comes out of the expected maximum. -/
lemma vecEM_const' {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (F : Finset ι) (hF : F.Nonempty)
    (v : ι → E) (c : ℝ) :
    vecExpectedMax F v (fun _ => c) = vecExpectedMax F v 0 + c := by
  have : Nonempty F := hF.to_subtype
  have hpt : ∀ x : E, (⨆ i : F, ⟪v i, x⟫ + c) = (⨆ i : F, ⟪v i, x⟫ + (0 : ι → ℝ) i) + c := by
    intro x
    rw [ciSup_add (Finite.bddAbove_range _)]
    simp
  unfold vecExpectedMax
  calc ∫ x, (⨆ i : F, ⟪v i, x⟫ + c) ∂stdGaussian E
      = ∫ x, ((⨆ i : F, ⟪v i, x⟫ + (0 : ι → ℝ) i) + c) ∂stdGaussian E := by
        congr 1; funext x; exact hpt x
    _ = _ := by
        rw [integral_add (integrable_iSup_inner_add F v 0) (integrable_const c), integral_const,
          probReal_univ, one_smul]

/-- **Gaussian reduction to chaining.** -/
theorem gem_le_chain {F : Finset Config} (hF : F.Nonempty) {δ : ℝ} (hδ : 0 < δ) (k : ℕ)
    {d : ℕ} (p : Config → Fin d → ℝ) {K a : ℝ} (hK : 0 ≤ K)
    (hp : ∀ c ∈ F, ∀ c' ∈ F, ‖p c - p c'‖ ≤ a)
    (hcan : ∀ c ∈ F, ∀ c' ∈ F, SegComb.logCov (SegComb.sub (cfgComb c) (cfgComb c'))
      (SegComb.sub (cfgComb c) (cfgComb c')) ≤ K * ‖p c - p c'‖) :
    gaussianExpectedMax F (fun c c' => δ⁻¹ * (cfgComb c).logCov (cfgComb c'))
      (fun _ => -(k : ℝ)) ≤ 20 * √5 * √(δ⁻¹ * K) * √((d + 1) * a) - k := by
  obtain ⟨i₀, hi₀⟩ := hF
  have ha : 0 ≤ a := (norm_nonneg _).trans (hp i₀ hi₀ i₀ hi₀)
  have hR : 0 ≤ 20 * √5 * √(δ⁻¹ * K) * √((d + 1) * a) := by positivity
  set G : Config → Config → ℝ := fun c c' => δ⁻¹ * (cfgComb c).logCov (cfgComb c') with hG
  by_cases hpsd : PSDOn F G
  · obtain ⟨v, hv, heq⟩ := exists_vecExpectedMax_eq_gaussianExpectedMax F G hpsd
    rw [heq, vecEM_const' F ⟨i₀, hi₀⟩ v]
    have hSF : vecExpectedMax F v 0 ≤ vecExpectedMax F (fun i => v i - v i₀) 0 :=
      sudakovFernique Config (EuclideanSpace ℝ F) (EuclideanSpace ℝ F) F v
        (fun i => v i - v i₀) 0 (fun i _ j _ => by rw [sub_sub_sub_cancel_right])
    have hvv : ∀ c ∈ F, ∀ c' ∈ F, ‖v c - v c'‖ ^ 2 ≤ √(δ⁻¹ * K) ^ 2 * ‖p c - p c'‖ := by
      intro c hc c' hc'
      rw [Real.sq_sqrt (by positivity), ← real_inner_self_eq_norm_sq, inner_sub_left,
        inner_sub_right, inner_sub_right, hv c hc c hc, hv c hc c' hc', hv c' hc' c hc,
        hv c' hc' c' hc']
      have e : G c c - G c c' - (G c' c - G c' c') =
          δ⁻¹ * SegComb.logCov (SegComb.sub (cfgComb c) (cfgComb c'))
            (SegComb.sub (cfgComb c) (cfgComb c')) := by
        rw [hG, TwoScale.logCov_eq_pairing, TwoScale.pairing_sub_sub]
        simp only [← TwoScale.logCov_eq_pairing]
        ring
      rw [e]
      calc δ⁻¹ * SegComb.logCov (SegComb.sub (cfgComb c) (cfgComb c'))
            (SegComb.sub (cfgComb c) (cfgComb c'))
          ≤ δ⁻¹ * (K * ‖p c - p c'‖) :=
            mul_le_mul_of_nonneg_left (hcan c hc c' hc') (inv_nonneg.2 hδ.le)
        _ = δ⁻¹ * K * ‖p c - p c'‖ := by ring
    have hch := ChainBox.chainingBox_bound F p v (Real.sqrt_nonneg _) hp hvv hi₀
    linarith
  · have hdir : gaussianExpectedMax F G (fun _ => -(k : ℝ)) = -(k : ℝ) := by
      have key : ∀ (i1 : DecidableEq F), @multivariateGaussian F _ i1 0
          (Matrix.of fun i j : F => G i j) = Measure.dirac 0 := fun i1 =>
        @multivariateGaussian_of_not_posSemidef F _ i1 0 _ hpsd
      unfold gaussianExpectedMax
      rw [key _, integral_dirac]
      have : Nonempty F := ⟨⟨i₀, hi₀⟩⟩
      simp
    rw [hdir]
    linarith

lemma rpow_quarter_eq (x : ℝ) (hx : 0 ≤ x) : x ^ (1 / 4 : ℝ) = √(√x) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num

end RMCrude

open RMCrude in
/-- **Node `M45`** (`Blueprint.Draft.RecordMeanCrude`, (4.5)). -/
theorem recordMeanCrude : Blueprint.Draft.RecordMeanCrude := by
  intro n hn
  set M : ℕ := 16 ^ n with hMdef
  have hM : 16 ≤ M := by
    calc 16 = 16 ^ 1 := by norm_num
      _ ≤ 16 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set Cs : ℝ := 20 * √5 * √(Ksm M * ((((2 * (3 * M + 1) + 1 : ℕ) : ℝ) + 1) * Dsm M)) with hCs
  set Cl : ℝ := 20 * √5 * √(Kl M * ((((2 * 4 + 1 : ℕ) : ℝ) + 1) * 18)) with hCl
  refine ⟨max Cs Cl, ?_⟩
  intro δ hδ large k hk F hF hFsub
  have hk0 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have hq := rpow_quarter_eq ((k : ℝ) + 1) hk0
  have hq0 : 0 ≤ ((k : ℝ) + 1) ^ (1 / 4 : ℝ) := by positivity
  have hδ0 := hδ.1
  cases large with
  | false =>
    have hsub : ∀ c ∈ F, c ∈ smallFamily M δ k := fun c hc => by
      have := hFsub (Finset.mem_coe.2 hc)
      simpa [localFamily] using this
    have h := gem_le_chain hF hδ0 k (psm M) (K := Ksm M) (a := Dsm M * (δ * √((k : ℝ) + 1)))
      (Ksm_nonneg M) (fun c hc c' hc' => small_diam hM hδ (hsub c hc) (hsub c' hc'))
      (fun c hc c' hc' => small_canon hM hδ (hsub c hc) (hsub c' hc'))
    refine h.trans ?_
    have hD : 0 ≤ Dsm M := by unfold Dsm; positivity
    have hKs := Ksm_nonneg M
    have e : 20 * √5 * √(δ⁻¹ * Ksm M) *
        √((((2 * (3 * M + 1) + 1 : ℕ) : ℝ) + 1) * (Dsm M * (δ * √((k : ℝ) + 1)))) =
        Cs * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) := by
      rw [hq, hCs, mul_assoc (20 * √5), ← Real.sqrt_mul (by positivity)]
      have e2 : δ⁻¹ * Ksm M * ((((2 * (3 * M + 1) + 1 : ℕ) : ℝ) + 1) *
          (Dsm M * (δ * √((k : ℝ) + 1)))) =
          Ksm M * ((((2 * (3 * M + 1) + 1 : ℕ) : ℝ) + 1) * Dsm M) * √((k : ℝ) + 1) := by
        field_simp
      rw [e2, Real.sqrt_mul (by positivity)]
      ring
    rw [e]
    have : Cs * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) ≤ max Cs Cl * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hq0
    linarith
  | true =>
    have hsub : ∀ c ∈ F, c ∈ largeFamily M δ := fun c hc => by
      have := hFsub (Finset.mem_coe.2 hc)
      simpa [localFamily] using this
    have hk' : k = ⌊δ ^ (-2 : ℤ)⌋₊ := hk rfl
    have h := gem_le_chain hF hδ0 k pl (K := Kl M) (a := 18) (Kl_nonneg M)
      (fun c hc c' hc' => large_diam hM hδ (hsub c hc) (hsub c' hc'))
      (fun c hc c' hc' => large_canon hM hδ (hsub c hc) (hsub c' hc'))
    refine h.trans ?_
    have hKl := Kl_nonneg M
    have e : 20 * √5 * √(δ⁻¹ * Kl M) * √((((2 * 4 + 1 : ℕ) : ℝ) + 1) * 18) = Cl * √(δ⁻¹) := by
      rw [hCl, Real.sqrt_mul (inv_nonneg.2 hδ0.le), Real.sqrt_mul hKl]
      ring
    rw [e]
    have hδk : √(δ⁻¹) ≤ ((k : ℝ) + 1) ^ (1 / 4 : ℝ) := by
      rw [hq]
      apply Real.sqrt_le_sqrt
      have h1 : δ ^ (-2 : ℤ) < (k : ℝ) + 1 := by rw [hk']; exact Nat.lt_floor_add_one _
      have h2 : δ ^ (-2 : ℤ) = (δ⁻¹) ^ 2 := by rw [zpow_neg, inv_pow]; norm_num
      rw [h2] at h1
      calc δ⁻¹ = √((δ⁻¹) ^ 2) := (Real.sqrt_sq (inv_nonneg.2 hδ0.le)).symm
        _ ≤ √((k : ℝ) + 1) := Real.sqrt_le_sqrt h1.le
    have hCl0 : 0 ≤ Cl := by rw [hCl]; positivity
    have : Cl * √(δ⁻¹) ≤ max Cs Cl * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) :=
      mul_le_mul (le_max_right _ _) hδk (Real.sqrt_nonneg _) (hCl0.trans (le_max_right _ _))
    linarith

end LQGDimension
