/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Var.Coord at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Var.Subadditive
import LatticeProb.Bonanno.LQGDimension.Section2.Bounds
import Mathlib.Algebra.Order.Chebyshev

/-!
# Comparison with independent scalar copies: Lemma 2.3 at fixed `n`

For `m ≥ 1` and every `n` (HA1 D6, in `[0, ∞]`, with no finiteness assumption):

* `Ag_Rd_le` (upper bound, the template `ACoord` of HA6 D.4):
  `A_n(ℝ^m) ≤ m · A_n(ℝ)`.  Compare `G_d(f)` with `∑ⱼ G₂⁽ʲ⁾(fⱼ)` (independent copies) using
  `‖a‖ ≤ ∑ⱼ |aⱼ|`; the energy is `∑ⱼ E(fⱼ)` (`gEM_le_sum_blocks`).
* `Ag_Rd_ge` (lower bound): `m^{2/3} · A_n(ℝ) ≤ A_n(ℝ^m)`.  For a finite `F* ⊆ V_n(ℝ)` take the
  product family `{x ↦ λ (σ₁(x), …, σ_m(x)) : σ ∈ F*^m}` with `λ = m^{-1/6}`, compare `G_d` from
  below with `m^{-1/4} ∑ⱼ G₂⁽ʲ⁾` using `m^{-1/2} ∑ⱼ |aⱼ| ≤ ‖a‖` (Sudakov–Fernique), and use the
  product equality `vecEM_pi_eq`; the scaling (2.5) with `a = m^{-1/4}`, `b = 1` is done inline
  (`m · m^{-1/3} = m^{2/3}`).
* `A_two_eq`: `A_{n,2} = A_n(ℝ)` (the case `m = 1`).

These are the paper's Lemma 2.3, (2.10); new code (no 2D counterpart), built on the 2D Gaussian
toolkit (`LQGDimension.sudakovFernique`, `LQGDimension.Subadd.vecEM_*`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Var

open LQGDimension (gaussianExpectedMax vecExpectedMax PSDOn)

/-! ## Coordinates of `ℝ^m`-valued profiles -/

/-- The `j`-th coordinate of an `ℝ^m`-valued profile. -/
def coordFn {m : ℕ} (f : ℝ → Rd m) (j : Fin m) : ℝ → ℝ := fun x => f x j

lemma coord_mem {m n : ℕ} {f : ℝ → Rd m} (hf : f ∈ Vg (Rd m) n) (j : Fin m) :
    coordFn f j ∈ Vg ℝ n := by
  obtain ⟨h0, h1, hout, hpiece⟩ := hf
  refine ⟨by simp [coordFn, h0], by simp [coordFn, h1], fun x hx => by simp [coordFn, hout x hx],
    fun k hk => ?_⟩
  obtain ⟨α, β, h⟩ := hpiece k hk
  exact ⟨α j, β j, fun x hx => by simp [coordFn, h x hx]⟩

lemma pi_mem_Vg {m n : ℕ} {g : Fin m → ℝ → ℝ} (hg : ∀ j, g j ∈ Vg ℝ n) :
    (fun x => (WithLp.toLp 2 (fun j => g j x) : Rd m)) ∈ Vg (Rd m) n := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext j; simp [(hg j).1]
  · ext j; simp [(hg j).2.1]
  · intro x hx; ext j; simp [(hg j).2.2.1 x hx]
  · intro k hk
    choose α β h using fun j => (hg j).2.2.2 k hk
    refine ⟨WithLp.toLp 2 α, WithLp.toLp 2 β, fun x hx => ?_⟩
    ext j
    simp [h j x hx]

/-- The energy of an `ℝ^m`-valued profile is the sum of the energies of its coordinates
(HA1 D3.4). -/
lemma energy_eq_sum_coord {m n : ℕ} {f : ℝ → Rd m} (hf : f ∈ Vg (Rd m) n) :
    energy f = ∑ j, energy (coordFn f j) := by
  rw [Vg_energy hf]
  simp_rw [Vg_energy (coord_mem hf _)]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  rfl

lemma norm_le_sum_abs {m : ℕ} (v : Rd m) : ‖v‖ ≤ ∑ j, |v j| := by
  have h1 : ‖v‖ ^ 2 ≤ (∑ j, |v j|) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs]
    exact Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => abs_nonneg _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Finset.sum_nonneg fun j _ => abs_nonneg _)
    two_ne_zero).1 h1

lemma sum_abs_le_sqrt_mul_norm {m : ℕ} (v : Rd m) : ∑ j, |v j| ≤ Real.sqrt m * ‖v‖ := by
  have h1 : (∑ j, |v j|) ^ 2 ≤ (m : ℝ) * ‖v‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m))) (f := fun j => |v j|)
    rw [Finset.card_univ, Fintype.card_fin] at this
    rw [EuclideanSpace.norm_sq_eq]
    simpa only [Real.norm_eq_abs, sq_abs] using this
  have h2 : 0 ≤ ∑ j, |v j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  calc ∑ j, |v j| = Real.sqrt ((∑ j, |v j|) ^ 2) := (Real.sqrt_sq h2).symm
    _ ≤ Real.sqrt ((m : ℝ) * ‖v‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt m * ‖v‖ := by
      rw [Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq (norm_nonneg _)]

/-- The canonical distance (2.2) for a Gram family indexed by an arbitrary type. -/
lemma gram_dist_sq {ι E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (T : ι → H) (φ : ι → ℝ → E) {i j : ι}
    (hi : Continuous (φ i)) (hj : Continuous (φ j)) (hii : ⟪T i, T i⟫ = gCov (φ i) (φ i))
    (hjj : ⟪T j, T j⟫ = gCov (φ j) (φ j)) (hij : ⟪T i, T j⟫ = gCov (φ i) (φ j)) :
    ‖T i - T j‖ ^ 2 = 2 * Real.pi * ∫ x in (0 : ℝ)..1, ‖φ i x - φ j x‖ := by
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hii, hjj,
    hij]
  have := gCov_dist_formula hi hj
  linarith

/-! ## Upper bound `A_n(ℝ^m) ≤ m A_n(ℝ)` -/

/-- One finite family: `𝕄_F(gCov, -E) ≤ m B` if `B` bounds the scalar problem at level `n`. -/
theorem gEM_coord_upper {m n : ℕ} (F : Finset (Vg (Rd m) n)) (B : ℝ)
    (hB : ∀ G : Finset (Vg ℝ n), gaussianExpectedMax G (fun f g => gCov (f : ℝ → ℝ) g)
      (fun f => -energy (f : ℝ → ℝ)) ≤ B) :
    gaussianExpectedMax F (fun f g => gCov (f : ℝ → Rd m) g) (fun f => -energy (f : ℝ → Rd m)) ≤
      m * B := by
  classical
  let P : Fin m → Vg (Rd m) n → ℝ → ℝ := fun j f => coordFn (f : ℝ → Rd m) j
  have hP : ∀ j f, P j f ∈ Vg ℝ ((fun _ : Fin m => n) j) := fun j f => coord_mem f.2 j
  have hb : ∀ f ∈ F, -energy (f : ℝ → Rd m) = ∑ j, (1 : ℝ) * -energy (P j f) := by
    intro f _
    rw [energy_eq_sum_coord f.2]
    simp only [one_mul, Finset.sum_neg_distrib, P]
  have hdist : ∀ f ∈ F, ∀ g ∈ F, gCov (f : ℝ → Rd m) f + gCov (g : ℝ → Rd m) g -
      2 * gCov (f : ℝ → Rd m) g ≤
      ∑ j, (1 : ℝ) ^ 2 * (2 * Real.pi * ∫ x in (0 : ℝ)..1, ‖P j f x - P j g x‖) := by
    intro f _ g _
    have hfc := Vg_continuous f.2
    have hgc := Vg_continuous g.2
    rw [gCov_dist_formula hfc hgc]
    simp only [one_pow, one_mul]
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hint : ∀ j ∈ (Finset.univ : Finset (Fin m)),
        IntervalIntegrable (fun x => ‖P j f x - P j g x‖) volume 0 1 := fun j _ =>
      ((Vg_continuous (hP j f)).sub (Vg_continuous (hP j g))).norm.intervalIntegrable 0 1
    rw [← intervalIntegral.integral_finsetSum hint]
    refine intervalIntegral.integral_mono_on zero_le_one
      ((hfc.sub hgc).norm.intervalIntegrable 0 1)
      (IntervalIntegrable.sum Finset.univ hint |>.congr (by
        intro x _; simp only [Finset.sum_apply])) fun x _ => ?_
    refine (norm_le_sum_abs _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [P, coordFn, PiLp.sub_apply, Real.norm_eq_abs]
  have key := gEM_le_sum_blocks F (fun f g => gCov (f : ℝ → Rd m) g) (gCov_psdOn_Vg n F)
    (fun f => -energy (f : ℝ → Rd m)) (fun _ : Fin m => n) P hP (fun _ => 1)
    (fun _ => zero_le_one) hb hdist (fun _ => B) (fun _ G => hB G)
  refine key.trans (le_of_eq ?_)
  simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Lemma 2.3, upper bound** (template `ACoord`): `A_n(ℝ^m) ≤ m · A_n(ℝ)` in `[0, ∞]`. -/
theorem Ag_Rd_le {m : ℕ} (hm : 1 ≤ m) (n : ℕ) : Ag (Rd m) n ≤ (m : EReal) * Ag ℝ n := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hcast : (m : EReal) = ((m : ℝ) : EReal) := rfl
  by_cases htop : Ag ℝ n = ⊤
  · rw [htop, hcast, EReal.coe_mul_top_of_pos hm0]
    exact le_top
  · rw [← Ag_eq_coe_toReal htop, hcast, ← EReal.coe_mul]
    refine Ag_le_of_forall fun F => EReal.coe_le_coe_iff.2 ?_
    exact gEM_coord_upper F _ (gEM_le_toReal htop)

/-! ## Lower bound `m^{2/3} A_n(ℝ) ≤ A_n(ℝ^m)` -/

/-- The constants of the lower comparison: `λ = m^{-1/6}`, `s = m^{-1/3}`. -/
lemma coord_consts {m : ℕ} (hm : 1 ≤ m) : ∃ lam s : ℝ, 0 < lam ∧ 0 < s ∧ lam ^ 2 = s ∧
    s ^ 2 * Real.sqrt m = lam ∧ (m : ℝ) * s = (m : ℝ) ^ (2 / 3 : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨(m : ℝ) ^ (-1 / 6 : ℝ), (m : ℝ) ^ (-1 / 3 : ℝ), Real.rpow_pos_of_pos hm0 _,
    Real.rpow_pos_of_pos hm0 _, ?_, ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
    norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le, Real.sqrt_eq_rpow, ← Real.rpow_add hm0]
    norm_num
  · rw [show (m : ℝ) * (m : ℝ) ^ (-1 / 3 : ℝ) = (m : ℝ) ^ (1 : ℝ) * (m : ℝ) ^ (-1 / 3 : ℝ) by
      rw [Real.rpow_one], ← Real.rpow_add hm0]
    norm_num

/-- One finite scalar family `F*`: `m^{2/3} 𝕄_{F*}(gCov, -E) ≤ A_n(ℝ^m)`. -/
theorem gEM_coord_lower {m n : ℕ} (hm : 1 ≤ m) (Fs : Finset (Vg ℝ n)) :
    (((m : ℝ) ^ (2 / 3 : ℝ) * gaussianExpectedMax Fs (fun f g => gCov (f : ℝ → ℝ) g)
      (fun f => -energy (f : ℝ → ℝ)) : ℝ) : EReal) ≤ Ag (Rd m) n := by
  classical
  rcases Fs.eq_empty_or_nonempty with rfl | hne
  · rw [gEM_empty, mul_zero, EReal.coe_zero]
    exact Ag_nonneg n
  obtain ⟨lam, s, hlam, hs, hls, hsl, hms⟩ := coord_consts hm
  -- the product family, dilated by `λ`
  let enc : (Fin m → Vg ℝ n) → Vg (Rd m) n := fun σ =>
    ⟨fun x => WithLp.toLp 2 (fun j => (lam • (σ j : ℝ → ℝ)) x),
      pi_mem_Vg (g := fun j => lam • (σ j : ℝ → ℝ)) (fun j => smul_mem_Vg (σ j).2 lam)⟩
  set P : Finset (Fin m → Vg ℝ n) := Fintype.piFinset fun _ : Fin m => Fs with hPdef
  have hσmem : ∀ σ ∈ P, ∀ j, σ j ∈ Fs := fun σ hσ j => Fintype.mem_piFinset.1 hσ j
  have hle := le_Ag (P.image enc)
  rw [gEM_image P enc _ _ (gCov_psdOn_Vg n _)] at hle
  refine le_trans (EReal.coe_le_coe_iff.2 ?_) hle
  -- Gram representations
  obtain ⟨V, hV⟩ := LQGDimension.exists_gram_of_psdOn P
    (fun σ τ => gCov ((enc σ : Vg (Rd m) n) : ℝ → Rd m) (enc τ))
    (gCov_psdOn P (fun σ => ((enc σ : Vg (Rd m) n) : ℝ → Rd m))
      (fun σ _ => Vg_intervalIntegrable (enc σ).2 0 1))
  obtain ⟨T, hT⟩ := LQGDimension.exists_gram_of_psdOn Fs (fun f g => gCov (f : ℝ → ℝ) g)
    (gCov_psdOn_Vg n Fs)
  have hFsT : gaussianExpectedMax Fs (fun f g => gCov (f : ℝ → ℝ) g)
      (fun f => -energy (f : ℝ → ℝ)) = vecExpectedMax Fs T (fun f => -energy (f : ℝ → ℝ)) := by
    rw [← LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax]
    exact LQGDimension.gaussianExpectedMax_congr Fs _ (fun f hf g hg => (hT f hf g hg).symm)
  have hPV : gaussianExpectedMax P (fun σ τ => gCov ((enc σ : Vg (Rd m) n) : ℝ → Rd m) (enc τ))
      (fun σ => -energy ((enc σ : Vg (Rd m) n) : ℝ → Rd m)) =
      vecExpectedMax P V (fun σ => -energy ((enc σ : Vg (Rd m) n) : ℝ → Rd m)) := by
    rw [← LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax]
    exact LQGDimension.gaussianExpectedMax_congr P _ (fun σ hσ τ hτ => (hV σ hσ τ hτ).symm)
  -- the comparison family: `m^{-1/4} √λ = s` times independent scalar copies
  let W : (Fin m → Vg ℝ n) → PiLp 2 (fun _ : Fin m => EuclideanSpace ℝ Fs) :=
    fun σ => WithLp.toLp 2 (fun j => s • T (σ j))
  -- Sudakov–Fernique, from `m^{-1/2} ∑ⱼ |aⱼ| ≤ ‖a‖`
  have hSF : vecExpectedMax P W (fun σ => -energy ((enc σ : Vg (Rd m) n) : ℝ → Rd m)) ≤
      vecExpectedMax P V (fun σ => -energy ((enc σ : Vg (Rd m) n) : ℝ → Rd m)) := by
    refine LQGDimension.sudakovFernique _ _ _ P W V _ fun σ hσ τ hτ => ?_
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    have hW : ‖W σ - W τ‖ ^ 2 = ∑ j, s ^ 2 *
        (2 * Real.pi * ∫ x in (0 : ℝ)..1, ‖(σ j : ℝ → ℝ) x - (τ j : ℝ → ℝ) x‖) := by
      rw [← WithLp.toLp_sub, PiLp.norm_sq_eq_of_L2]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.sub_apply]
      rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        gram_dist_sq T (fun f : Vg ℝ n => (f : ℝ → ℝ)) (Vg_continuous (σ j).2)
          (Vg_continuous (τ j).2)
          (hT _ (hσmem σ hσ j) _ (hσmem σ hσ j)) (hT _ (hσmem τ hτ j) _ (hσmem τ hτ j))
          (hT _ (hσmem σ hσ j) _ (hσmem τ hτ j))]
    have hVd : ‖V σ - V τ‖ ^ 2 = 2 * Real.pi * ∫ x in (0 : ℝ)..1,
        ‖((enc σ : Vg (Rd m) n) : ℝ → Rd m) x - ((enc τ : Vg (Rd m) n) : ℝ → Rd m) x‖ :=
      gram_dist_sq V (fun σ => ((enc σ : Vg (Rd m) n) : ℝ → Rd m)) (Vg_continuous (enc σ).2)
        (Vg_continuous (enc τ).2) (hV σ hσ σ hσ) (hV τ hτ τ hτ) (hV σ hσ τ hτ)
    rw [hW, hVd]
    have hpt : ∀ x : ℝ, s ^ 2 * ∑ j, ‖(σ j : ℝ → ℝ) x - (τ j : ℝ → ℝ) x‖ ≤
        ‖((enc σ : Vg (Rd m) n) : ℝ → Rd m) x - ((enc τ : Vg (Rd m) n) : ℝ → Rd m) x‖ := by
      intro x
      have e : ((enc σ : Vg (Rd m) n) : ℝ → Rd m) x - ((enc τ : Vg (Rd m) n) : ℝ → Rd m) x =
          lam • (WithLp.toLp 2 (fun j => (σ j : ℝ → ℝ) x - (τ j : ℝ → ℝ) x) : Rd m) := by
        ext j
        simp [enc, mul_sub]
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hlam, ← hsl]
      have h1 := sum_abs_le_sqrt_mul_norm
        (WithLp.toLp 2 (fun j => (σ j : ℝ → ℝ) x - (τ j : ℝ → ℝ) x) : Rd m)
      simp only at h1
      simp only [Real.norm_eq_abs]
      calc s ^ 2 * ∑ j, |(σ j : ℝ → ℝ) x - (τ j : ℝ → ℝ) x|
          ≤ s ^ 2 * (Real.sqrt m * ‖(WithLp.toLp 2 (fun j => (σ j : ℝ → ℝ) x - (τ j : ℝ → ℝ) x) :
            Rd m)‖) := mul_le_mul_of_nonneg_left h1 (sq_nonneg s)
        _ = s ^ 2 * Real.sqrt m * ‖(WithLp.toLp 2 (fun j => (σ j : ℝ → ℝ) x -
            (τ j : ℝ → ℝ) x) : Rd m)‖ := by ring
    have hint : ∀ j ∈ (Finset.univ : Finset (Fin m)), IntervalIntegrable
        (fun x => ‖(σ j : ℝ → ℝ) x - (τ j : ℝ → ℝ) x‖) volume 0 1 := fun j _ =>
      ((Vg_continuous (σ j).2).sub (Vg_continuous (τ j).2)).norm.intervalIntegrable 0 1
    have hsum_int : ∑ j, s ^ 2 * (2 * Real.pi * ∫ x in (0 : ℝ)..1,
        ‖(σ j : ℝ → ℝ) x - (τ j : ℝ → ℝ) x‖) = 2 * Real.pi * ∫ x in (0 : ℝ)..1,
          s ^ 2 * ∑ j, ‖(σ j : ℝ → ℝ) x - (τ j : ℝ → ℝ) x‖ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum hint,
        Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsum_int]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ (fun x _ => hpt x)
    · exact (continuous_const.mul (continuous_finsetSum _ fun j _ =>
        ((Vg_continuous (σ j).2).sub (Vg_continuous (τ j).2)).norm)).intervalIntegrable 0 1
    · exact ((Vg_continuous (enc σ).2).sub (Vg_continuous (enc τ).2)).norm.intervalIntegrable 0 1
  -- the drift splits: `E(λ σ) = ∑ⱼ λ² E(σⱼ) = ∑ⱼ s E(σⱼ)`
  have hdrift : ∀ σ ∈ P, -energy ((enc σ : Vg (Rd m) n) : ℝ → Rd m) =
      ∑ j, s * -energy ((σ j : ℝ → ℝ)) := by
    intro σ _
    rw [energy_eq_sum_coord (enc σ).2]
    have hc : ∀ j, coordFn ((enc σ : Vg (Rd m) n) : ℝ → Rd m) j = lam • (σ j : ℝ → ℝ) := by
      intro j; funext x; simp [coordFn, enc]
    simp_rw [hc, energy_smul (σ _).2 lam, hls]
    simp only [mul_neg, Finset.sum_neg_distrib]
  -- the product equality
  have hprod := vecEM_pi_eq (m := m) Fs hne (fun a => s • T a)
    (fun a => s * -energy (a : ℝ → ℝ))
  rw [LQGDimension.Subadd.vecEM_smul Fs T (fun a => -energy (a : ℝ → ℝ)) hs.le] at hprod
  calc (m : ℝ) ^ (2 / 3 : ℝ) * gaussianExpectedMax Fs (fun f g => gCov (f : ℝ → ℝ) g)
        (fun f => -energy (f : ℝ → ℝ))
      = (m : ℝ) * (s * vecExpectedMax Fs T (fun f => -energy (f : ℝ → ℝ))) := by
        rw [hFsT, ← hms]; ring
    _ = vecExpectedMax P W (fun σ => ∑ j, s * -energy ((σ j : ℝ → ℝ))) := hprod.symm
    _ = vecExpectedMax P W (fun σ => -energy ((enc σ : Vg (Rd m) n) : ℝ → Rd m)) :=
        vecEM_congr_drift P W (fun σ hσ => (hdrift σ hσ).symm)
    _ ≤ vecExpectedMax P V (fun σ => -energy ((enc σ : Vg (Rd m) n) : ℝ → Rd m)) := hSF
    _ = _ := hPV.symm

/-- **Lemma 2.3, lower bound**: `m^{2/3} · A_n(ℝ) ≤ A_n(ℝ^m)` in `[0, ∞]`. -/
theorem Ag_Rd_ge {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    (((m : ℝ) ^ (2 / 3 : ℝ) : ℝ) : EReal) * Ag ℝ n ≤ Ag (Rd m) n := by
  have hc : (0 : ℝ) < (m : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hm) _
  have h : Ag ℝ n = ⨆ F : Finset (Vg ℝ n),
      ((gaussianExpectedMax F (fun f g => gCov (f : ℝ → ℝ) g)
        (fun f => -energy (f : ℝ → ℝ)) : ℝ) : EReal) := rfl
  rw [h, LQGDimension.Bounds.EReal_coe_mul_iSup hc]
  refine iSup_le fun Fs => ?_
  rw [← EReal.coe_mul]
  exact gEM_coord_lower hm Fs

/-- `A_{n,2} = A_n(ℝ)` (Lemma 2.3 with `m = 1`; HA1 D11 (iv)). -/
theorem A_two_eq (n : ℕ) : A n 2 = Ag ℝ n := by
  show Ag (Rd 1) n = Ag ℝ n
  apply le_antisymm
  · have := Ag_Rd_le (m := 1) le_rfl n
    simpa using this
  · have := Ag_Rd_ge (m := 1) le_rfl n
    simpa using this

end HigherDimLFPP.Var
