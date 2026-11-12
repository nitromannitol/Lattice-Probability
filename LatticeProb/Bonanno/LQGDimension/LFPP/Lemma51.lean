/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.Lemma51 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.Lemma51Aux4
import LatticeProb.Bonanno.LQGDimension.LFPP.Lemma33
import LatticeProb.Bonanno.LQGDimension.Assembly.AStarProved

/-!
# Lemma 5.1 (node `L51`, `Blueprint.Draft.Lemma51`)

`E min_{f ∈ Fn} C_f(μ) ≤ 1 - δ²(a_n - C n^{7/8}) + θ δ²` for all small `ξ` (`δ = ξ^{2/3}`),
uniformly over finitely supported probabilities `μ` on the tube `T_δ` and over Gram realisations
`u` of the root band `bandCov(4ρ/M, ρ)`, `ρ = δ n^{3/4}`, on the block points.

## Decomposition (all files in `LQGDimension/LFPP/`)

Notation: `M = 16ⁿ`, `K = C₀√n` (sup bound, tube radius `2δK`), `R = n^{3/4}` (`b = ρ = δR`,
`a = 4δR/M`), `E₀ = C₀ n`, `q = n^{1/8}`.

(i) **Potential convergence (5.5)** — `Lemma51Aux2`: `pot_eq` (substitution `y = x + δu`),
    `abs_pot_sub_le` (error `η(δ) = ∫ min(Lδ, lk B u) du`, uniform in `x ∈ ℝ`, `|Y| ≤ Y₀`),
    `tendsto_eta`.
(ii) **Band truncation** — `Lemma51Aux1` (band form `bandForm a b`, bilinear, PSD,
    Cauchy–Schwarz, `bandForm = bandCov` on points, `logCov_split` into `(0,a] ∪ (a,b] ∪ (b,∞)`,
    `bandForm_le_logCov`) and `Lemma51Aux2` (`abs_gaussPair_pt_gdiff_le`: small scales cost
    `≤ 2√π t`; `abs_gaussPair_vdip_le`: large scales, mixed second difference of the Gaussian
    kernel with horizontal decay).
(iii) **Gram-level lower bound (5.4)** — `Lemma51Aux3` (block points are `O(δ²)`-close to
    `x + iδ(f(x)+ζ)`; `cross_hpt` = (5.6) per dipole; `cross_pert`: `O(δ²)` perturbations cost
    `o(δ)` by Cauchy–Schwarz; Riemann sums; total variation `≤ √(2E)`) and `Lemma51Aux4`
    (`norm_vecV_sub_sq`, `cross_total`, `gram_lower`).
(iv) **SF comparison and entropy** — `SfLowerProp` below (to be discharged by
    `Lemma51Aux5.sf_lower`).
(v) **Taylor remainder / linearization** — `TaylorProp` below (to be discharged by
    `Lemma51Aux6.integral_iInf_blockCost_le`).
(vi) **Assembly** — this file: `lemma51_of`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension.L51

open Blueprint.Draft

/-! ## The two remaining sub-lemmas, as propositions -/

/-- **(iv)** Sudakov–Fernique comparison with independent `N_f` of variance `β/2`, and the
entropy term `E max N_f ≤ √(β log |Fn|)`. -/
def SfLowerProp : Prop :=
  ∀ {n : ℕ} {Fn : Finset (ℝ → ℝ)}, (∀ f ∈ Fn, f ∈ V n) → Fn.Nonempty →
    ∀ {E₀ α β : ℝ}, 0 ≤ α → α ≤ 1 → 0 ≤ β → (∀ f ∈ Fn, energy f ≤ E₀) →
    ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (y : (ℝ → ℝ) → E),
      (∀ f ∈ Fn, ∀ g ∈ Fn,
        (1 - α) * (2 * π * ∫ x in (0:ℝ)..1, |f x - g x|) - β ≤ ‖y f - y g‖ ^ 2) →
      √(1 - α) * gaussianExpectedMax Fn zCov (fun f => -energy f) - (1 - √(1 - α)) * E₀ -
          √(β * Real.log Fn.card) ≤
        vecExpectedMax Fn (fun f => -y f) (fun f => -energy f)

/-- **(v)** Linearization of `C_f(μ)`: Taylor expansion of `exp`, edge lengths
`Σ r_i ≤ 1 + δ² E(f)`, removal of the common centered part `ξ ⟨X, ν⁰_μ⟩`. -/
def TaylorProp : Prop :=
  ∀ {n : ℕ} {Fn : Finset (ℝ → ℝ)}, (∀ f ∈ Fn, f ∈ V n) → (0 : ℝ → ℝ) ∈ Fn →
    ∀ {E₀ : ℝ}, (∀ f ∈ Fn, energy f ≤ E₀) → ∀ {ξ δ : ℝ}, 0 < ξ → ξ ≤ 1 → 0 < δ →
    ∀ {S : Finset ℂ} {w : ℂ → ℝ}, (∀ z ∈ S, 0 ≤ w z) → ∑ z ∈ S, w z = 1 →
    ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (u : ℂ → E) {v : ℝ},
      (∀ f ∈ Fn, ∀ i < 16 ^ n, ∀ z ∈ S, ‖u (edgeSim (16 ^ n) δ f i z)‖ ^ 2 = v) →
      ∫ x, (⨅ f : Fn, blockCost ξ (16 ^ n) δ f S w (fun z => ⟪u z, x⟫)) ∂stdGaussian E ≤
        1 - δ ^ 2 * vecExpectedMax Fn
            (fun f => -((ξ / δ ^ 2) • (vecV n δ S w u f - vecV n δ S w u 0)))
            (fun f => -energy f) +
          Fn.card * (2 * ξ * Real.exp (v / 2) * δ ^ 2 * E₀ +
            4 * ξ ^ 2 * Real.exp (2 * v) * (1 + δ ^ 2 * E₀))

/-! ## Auxiliary facts -/

lemma tube_mono {δ K K' : ℝ} (hδ : 0 ≤ δ) (hK : K ≤ K') : tube δ K ⊆ tube δ K' := by
  rintro z ⟨s, hs, hz⟩
  exact ⟨s, hs, hz.trans (by nlinarith)⟩

lemma zCov_four {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    zCov f f - zCov f g - zCov g f + zCov g g = 2 * π * ∫ x in (0:ℝ)..1, |f x - g x| := by
  unfold zCov
  have i1 : IntervalIntegrable (fun x => |f x| + |f x| - |f x - f x|) volume 0 1 :=
    (by fun_prop : Continuous fun x => |f x| + |f x| - |f x - f x|).intervalIntegrable 0 1
  have i2 : IntervalIntegrable (fun x => |f x| + |g x| - |f x - g x|) volume 0 1 :=
    (by fun_prop : Continuous fun x => |f x| + |g x| - |f x - g x|).intervalIntegrable 0 1
  have i3 : IntervalIntegrable (fun x => |g x| + |f x| - |g x - f x|) volume 0 1 :=
    (by fun_prop : Continuous fun x => |g x| + |f x| - |g x - f x|).intervalIntegrable 0 1
  have i4 : IntervalIntegrable (fun x => |g x| + |g x| - |g x - g x|) volume 0 1 :=
    (by fun_prop : Continuous fun x => |g x| + |g x| - |g x - g x|).intervalIntegrable 0 1
  rw [← mul_sub, ← mul_sub, ← mul_add, ← intervalIntegral.integral_sub i1 i2,
    ← intervalIntegral.integral_sub (i1.sub i2) i3,
    ← intervalIntegral.integral_add ((i1.sub i2).sub i3) i4, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  congr 1; funext x
  rw [abs_sub_comm (g x) (f x)]
  simp only [sub_self, abs_zero]
  ring

/-- The graph covariance limit for `μ_{δ,f} - μ_{δ,g}`. -/
lemma tendsto_gdiff (hL32g : GraphCovLimit) {n : ℕ} {f g : ℝ → ℝ} (hf : f ∈ V n)
    (hg : g ∈ V n) :
    Tendsto (fun δ => δ⁻¹ * (gdiff (16 ^ n) δ f g).logCov (gdiff (16 ^ n) δ f g)) (𝓝[>] 0)
      (𝓝 (2 * π * ∫ x in (0:ℝ)..1, |f x - g x|)) := by
  have hff := hL32g n f f hf hf
  have hfg := hL32g n f g hf hg
  have hgf := hL32g n g f hg hf
  have hgg := hL32g n g g hg hg
  have hlim := ((hff.sub hfg).sub hgf).add hgg
  rw [zCov_four (Subadd.V_continuous hf) (Subadd.V_continuous hg)] at hlim
  refine hlim.congr fun δ => ?_
  simp only [gdiff, GraphCov.logCov_sub_sub]
  ring

lemma bandCov_self {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (p : ℂ) :
    bandCov a b p p = Real.log (b / a) := by
  unfold bandCov
  simp only [sub_self, norm_zero]
  rw [← integral_inv_of_pos ha (ha.trans_le hab)]
  congr 1; funext t
  norm_num

/-- `ξ ↦ ξ^{2/3}` maps `𝓝[>] 0` to `𝓝[>] 0`. -/
lemma tendsto_rpow_two_thirds :
    Tendsto (fun ξ : ℝ => ξ ^ (2 / 3 : ℝ)) (𝓝[>] 0) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have h := (Real.continuousAt_rpow_const 0 (2 / 3 : ℝ) (Or.inr (by norm_num))).tendsto
    rw [Real.zero_rpow (by norm_num)] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ξ hξ
    exact Real.rpow_pos_of_pos hξ _

lemma rpow_two_thirds_cube {ξ : ℝ} (hξ : 0 ≤ ξ) : (ξ ^ (2 / 3 : ℝ)) ^ 3 = ξ ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hξ]
  norm_num

/-- `gaussianExpectedMax Fn zCov (-E) ≤ a n` and `a n ≤ n a₁`. -/
lemma gem_le_a {n : ℕ} (hn : 1 ≤ n) {Fn : Finset (ℝ → ℝ)} (hFnV : ∀ f ∈ Fn, f ∈ V n) :
    gaussianExpectedMax Fn zCov (fun f => -energy f) ≤ a n ∧ a n ≤ n * a 1 ∧ 0 ≤ a 1 := by
  classical
  have h1 := aOneFinite
  have h2 := aSubadditiveE
  have ha1nb : aE 1 ≠ ⊥ := ne_bot_of_le_ne_bot EReal.zero_ne_bot (Bounds.aE_nonneg 1)
  have ha1 : aE 1 = ((aE 1).toReal : EReal) := (EReal.coe_toReal h1 ha1nb).symm
  obtain ⟨an, han, hanle⟩ := Bounds.aE_finite_le h2 ha1 n hn
  have e : a n = an := by rw [a, han, EReal.toReal_coe]
  have hGa : ∀ G : Finset (V n),
      gaussianExpectedMax G (fun f g => zCov f g) (fun f => -energy f) ≤ a n := by
    intro G
    have hG : ((gaussianExpectedMax G (fun f g => zCov f g) (fun f => -energy f) : ℝ) : EReal)
        ≤ aE n :=
      le_iSup (fun G : Finset (V n) => ((gaussianExpectedMax G (fun f g => zCov f g)
        (fun f => -energy f) : ℝ) : EReal)) G
    rw [han] at hG
    rw [e]
    exact EReal.coe_le_coe_iff.1 hG
  refine ⟨?_, by rw [e]; exact hanle, EReal.toReal_nonneg (Bounds.aE_nonneg 1)⟩
  obtain ⟨U, hU⟩ := exists_gram_of_psdOn Fn zCov
    (zCovPSD Fn fun f hf => mem_V_intervalIntegrable (hFnV f hf))
  have hφ : ∀ f ∈ Fn, ((L33.toV n f : V n) : ℝ → ℝ) = f := fun f hf => L33.toV_coe (hFnV f hf)
  have hUφ : ∀ i ∈ Fn, ∀ j ∈ Fn, ⟪U (L33.toV n i), U (L33.toV n j)⟫ =
      zCov (L33.toV n i) (L33.toV n j) := by
    intro i hi j hj
    rw [hφ i hi, hφ j hj]; exact hU i hi j hj
  have e1 := L33.vecEM_toV n Fn (L33.toV n) U hUφ (fun f => -energy f)
  have e2 : gaussianExpectedMax Fn zCov (fun f => -energy f) =
      vecExpectedMax Fn U (fun f => -energy f) := by
    rw [← gaussianExpectedMax_gram_eq_vecExpectedMax]
    exact gaussianExpectedMax_congr Fn _ fun i hi j hj => (hU i hi j hj).symm
  have e3 : vecExpectedMax Fn U (fun f => -energy f) =
      vecExpectedMax Fn (fun i => U (L33.toV n i)) (fun i => -energy (L33.toV n i)) :=
    L33.vecEM_congr Fn (fun i hi => by rw [hφ i hi]) (fun i hi => by rw [hφ i hi])
  rw [e2, e3, e1]
  exact hGa _

/-- The final numerical inequality, in terms of `q = n^{1/8}`. -/
lemma final_ineq {q c c₁ c₂ a₁ an G β L Mr : ℝ} (hq : 1 ≤ q) (hc : 0 ≤ c) (hc₂ : 0 ≤ c₂)
    (ha₁ : 0 ≤ a₁) (hMr : 0 < Mr) (hc₁ : c₁ / q ^ 2 ≤ 1) (hc₁0 : 0 ≤ c₁)
    (hGlow : an - 1 ≤ G) (hGup : G ≤ q ^ 8 * a₁) (_hβ : 0 ≤ β) (hβle : β ≤ c₂ * q ^ 6 / Mr)
    (hL : 0 ≤ L) (hLle : L ≤ c * Mr * (q ^ 8 * Real.log 16)) :
    an - (1 + c₁ * (a₁ + c) + √(c₂ * c * Real.log 16)) * q ^ 7 ≤
      √(1 - c₁ / q ^ 2) * G - (1 - √(1 - c₁ / q ^ 2)) * (c * q ^ 8) - √(β * L) := by
  set α := c₁ / q ^ 2 with hα
  have hq0 : 0 < q := by linarith
  have hα0 : 0 ≤ α := by positivity
  set s := √(1 - α) with hs
  have hs1 : s ≤ 1 := by rw [hs, Real.sqrt_le_one]; linarith
  have hs0 : 1 - α ≤ s := by
    rw [hs]; apply Real.le_sqrt_of_sq_le; nlinarith
  have h1s : 0 ≤ 1 - s := by linarith
  have h1sα : 1 - s ≤ α := by linarith
  have hαq : α * q ^ 8 = c₁ * q ^ 6 := by
    rw [hα]; field_simp
  -- `s G ≥ G - (1 - s) q⁸ a₁`
  have hsG : G - (1 - s) * (q ^ 8 * a₁) ≤ s * G := by
    have := mul_le_mul_of_nonneg_left hGup h1s
    nlinarith
  have hA : (1 - s) * (q ^ 8 * a₁) ≤ c₁ * q ^ 6 * a₁ := by
    have := mul_le_mul_of_nonneg_right h1sα (by positivity : 0 ≤ q ^ 8 * a₁)
    calc (1 - s) * (q ^ 8 * a₁) ≤ α * (q ^ 8 * a₁) := this
      _ = c₁ * q ^ 6 * a₁ := by rw [← mul_assoc, hαq]
  have hB : (1 - s) * (c * q ^ 8) ≤ c₁ * q ^ 6 * c := by
    have := mul_le_mul_of_nonneg_right h1sα (by positivity : 0 ≤ c * q ^ 8)
    calc (1 - s) * (c * q ^ 8) ≤ α * (c * q ^ 8) := this
      _ = c * (α * q ^ 8) := by ring
      _ = c₁ * q ^ 6 * c := by rw [hαq]; ring
  -- the entropy term
  have hβL : β * L ≤ c₂ * c * Real.log 16 * (q ^ 7) ^ 2 := by
    calc β * L ≤ (c₂ * q ^ 6 / Mr) * (c * Mr * (q ^ 8 * Real.log 16)) :=
          mul_le_mul hβle hLle hL (by positivity)
      _ = c₂ * c * Real.log 16 * (q ^ 7) ^ 2 := by field_simp
  have hC : √(β * L) ≤ √(c₂ * c * Real.log 16) * q ^ 7 := by
    calc √(β * L) ≤ √(c₂ * c * Real.log 16 * (q ^ 7) ^ 2) := Real.sqrt_le_sqrt hβL
      _ = √(c₂ * c * Real.log 16) * q ^ 7 := by
        rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hq67 : q ^ 6 ≤ q ^ 7 := pow_le_pow_right₀ hq (by norm_num)
  have hq07 : 1 ≤ q ^ 7 := one_le_pow₀ hq
  have hD : c₁ * (a₁ + c) * q ^ 6 ≤ c₁ * (a₁ + c) * q ^ 7 :=
    mul_le_mul_of_nonneg_left hq67 (by positivity)
  have hsq0 : 0 ≤ √(c₂ * c * Real.log 16) := Real.sqrt_nonneg _
  nlinarith

/-- The conclusion of `gram_lower` ((5.4)) for one pair `f, g` at one `δ`. -/
def Gram54 (n : ℕ) (K R E₀ θ₀ : ℝ) (f g : ℝ → ℝ) (δ : ℝ) : Prop :=
  ∀ (S : Finset ℂ) (w : ℂ → ℝ), ↑S ⊆ tube δ K → (∀ z ∈ S, 0 ≤ w z) →
    ∑ z ∈ S, w z = 1 → ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : ℂ → E),
    (∀ h h' : ℝ → ℝ, (h = f ∨ h = g) → (h' = f ∨ h' = g) → ∀ k ∈ bIdx n S,
      ∀ l ∈ bIdx n S, ⟪u (bP n δ h k), u (bP n δ h' l)⟫ =
        bandCov (4 * (δ * R) / (16 : ℝ) ^ n) (δ * R) (bP n δ h k) (bP n δ h' l)) →
    (1 - 2 * (2 / √π * K / R) - θ₀) * (2 * π * ∫ x in (0:ℝ)..1, |f x - g x|) -
        2 * ((4 * π * √(2 * E₀) + 4 * π * K + 16 * √π * R) / (16 : ℝ) ^ n) ≤
      ‖vecV n δ S w u f - vecV n δ S w u g‖ ^ 2 / δ

/-- **Lemma 5.1**, from the graph covariance limit and the sub-lemmas (iv) and (v). -/
theorem lemma51_of (hL32g : GraphCovLimit) (hb1 : SfLowerProp) (hb2 : TaylorProp) :
    Blueprint.Draft.Lemma51 := by
  intro C₀
  set c : ℝ := max C₀ 0 with hc_def
  have hc0 : 0 ≤ c := le_max_right _ _
  have hC₀c : C₀ ≤ c := le_max_left _ _
  set c₁ : ℝ := 4 * c / √π + 1 with hc₁_def
  set c₂ : ℝ := 2 * (4 * π * √(2 * c) + 4 * π * c + 16 * √π) with hc₂_def
  set a₁ : ℝ := a 1 with ha₁_def
  have hsqπ : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  refine ⟨1 + c₁ * (a₁ + c) + √(c₂ * c * Real.log 16), ⌈c₁ ^ 4⌉₊ + 1, ?_⟩
  intro n hn Fn hFnV h0 hE hK hlog hG θ hθ
  have hn1 : 1 ≤ n := by omega
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hne : Fn.Nonempty := ⟨0, h0⟩
  -- `q = n^{1/8}`
  set q : ℝ := (n : ℝ) ^ (1 / 8 : ℝ) with hq_def
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by linarith) _
  have hqpow : ∀ k : ℕ, q ^ k = (n : ℝ) ^ ((k : ℝ) / 8) := by
    intro k
    rw [hq_def, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1; ring
  have hq8 : q ^ 8 = (n : ℝ) := by rw [hqpow]; norm_num
  have hq6 : q ^ 6 = (n : ℝ) ^ (3 / 4 : ℝ) := by rw [hqpow]; norm_num
  have hq7 : q ^ 7 = (n : ℝ) ^ (7 / 8 : ℝ) := by rw [hqpow]; norm_num
  have hq4 : q ^ 4 = √(n : ℝ) := by rw [hqpow, Real.sqrt_eq_rpow]; norm_num
  have hq1 : 1 ≤ q := Real.one_le_rpow hnr (by norm_num)
  have hc₁q : c₁ ≤ q ^ 2 := by
    have h1 : c₁ ^ 4 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈c₁ ^ 4⌉₊ ≤ n))
    have h2 : c₁ ^ 4 ≤ (q ^ 2) ^ 4 := by rw [← pow_mul, hq8]; exact h1
    exact (pow_le_pow_iff_left₀ hc₁0 (by positivity) (by norm_num)).1 h2
  -- the parameters of (5.4)
  set K : ℝ := c * √(n : ℝ) with hK_def
  set R : ℝ := (n : ℝ) ^ (3 / 4 : ℝ) with hR_def
  set E₀ : ℝ := c * n with hE₀_def
  set θ₀ : ℝ := 1 / q ^ 2 with hθ₀_def
  have hK0 : 0 ≤ K := by positivity
  have hR0 : 0 < R := Real.rpow_pos_of_pos (by linarith) _
  have hθ₀0 : 0 < θ₀ := by positivity
  have hKq : K = c * q ^ 4 := by rw [hK_def, hq4]
  have hRq : R = q ^ 6 := by rw [hR_def, hq6]
  have hE₀q : E₀ = c * q ^ 8 := by rw [hE₀_def, hq8]
  have hκeq : 2 / √π * K / R = 2 * c / √π / q ^ 2 := by
    rw [hKq, hRq]; field_simp
  have hκ : 2 / √π * K / R ≤ 1 := by
    rw [hκeq]
    refine (div_le_div_of_nonneg_right ?_ (by positivity)).trans ((div_le_one (by positivity)).2 hc₁q)
    rw [hc₁_def]
    have : 2 * c / √π ≤ 4 * c / √π := div_le_div_of_nonneg_right (by linarith) hsqπ.le
    linarith
  set α : ℝ := 2 * (2 / √π * K / R) + θ₀ with hα_def
  have hαeq : α = c₁ / q ^ 2 := by
    rw [hα_def, hκeq, hθ₀_def, hc₁_def]; field_simp; ring
  have hα0 : 0 ≤ α := by rw [hαeq]; positivity
  have hα1 : α ≤ 1 := by rw [hαeq]; exact (div_le_one (by positivity)).2 hc₁q
  set Mr : ℝ := (16 : ℝ) ^ n with hMr_def
  have hMr0 : 0 < Mr := by positivity
  have hM16 : (16 : ℝ) ≤ Mr := by
    calc (16 : ℝ) = 16 ^ 1 := by norm_num
      _ ≤ 16 ^ n := pow_le_pow_right₀ (by norm_num) hn1
  set β : ℝ := 2 * ((4 * π * √(2 * E₀) + 4 * π * K + 16 * √π * R) / Mr) with hβ_def
  have hβ0 : 0 ≤ β := by positivity
  have hβle : β ≤ c₂ * q ^ 6 / Mr := by
    have hsE : √(2 * E₀) = √(2 * c) * q ^ 4 := by
      rw [hE₀q, show 2 * (c * q ^ 8) = 2 * c * (q ^ 4) ^ 2 by ring,
        Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (by positivity)]
    have hq46 : q ^ 4 ≤ q ^ 6 := pow_le_pow_right₀ hq1 (by norm_num)
    rw [hβ_def, hsE, hKq, hRq, hc₂_def]
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hMr0]
    have h1 := mul_le_mul_of_nonneg_left hq46 (by positivity : (0:ℝ) ≤ 4 * π * √(2 * c))
    have h2 := mul_le_mul_of_nonneg_left hq46 (by positivity : (0:ℝ) ≤ 4 * π * c)
    linarith
  have hfK' : ∀ f ∈ Fn, ∀ x, |f x| ≤ K := fun f hf x =>
    (hK f hf x).trans (mul_le_mul_of_nonneg_right hC₀c (Real.sqrt_nonneg _))
  have hE' : ∀ f ∈ Fn, energy f ≤ E₀ := fun f hf =>
    (hE f hf).trans (mul_le_mul_of_nonneg_right hC₀c (by positivity))
  -- (5.4) for all pairs, eventually in `δ`, then in `ξ`
  have h54 : ∀ᶠ δ in 𝓝[>] (0:ℝ), ∀ f ∈ Fn, ∀ g ∈ Fn, Gram54 n K R E₀ θ₀ f g δ := by
    refine (eventually_all_finset Fn).2 fun f hf => (eventually_all_finset Fn).2 fun g hg => ?_
    exact gram_lower hn1 hK0 hR0 hθ₀0 hκ (hFnV f hf) (hFnV g hg) (hfK' f hf) (hfK' g hg)
      (hE' f hf) (hE' g hg) (tendsto_gdiff hL32g (hFnV f hf) (hFnV g hg))
  have h54ξ := tendsto_rpow_two_thirds.eventually h54
  -- the Taylor remainder is `o(δ²)`
  set v : ℝ := Real.log (Mr / 4) with hv_def
  set Φ : ℝ → ℝ := fun ξ => (Fn.card : ℝ) * (2 * ξ * Real.exp (v / 2) * E₀ +
    4 * ξ ^ (2 / 3 : ℝ) * Real.exp (2 * v) * (1 + (ξ ^ (2 / 3 : ℝ)) ^ 2 * E₀)) with hΦ_def
  have hΦt : Tendsto Φ (𝓝[>] 0) (𝓝 0) := by
    have t1 : Tendsto (fun ξ : ℝ => ξ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have t2 : Tendsto (fun ξ : ℝ => ξ ^ (2 / 3 : ℝ)) (𝓝[>] 0) (𝓝 0) :=
      (tendsto_nhdsWithin_iff.1 tendsto_rpow_two_thirds).1
    have t := ((((t1.const_mul 2).mul_const (Real.exp (v / 2))).mul_const E₀).add
      (((t2.const_mul 4).mul_const (Real.exp (2 * v))).mul
        (((t2.pow 2).mul_const E₀).const_add 1))).const_mul (Fn.card : ℝ)
    simp only [mul_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at t
    exact t
  have hΦev : ∀ᶠ ξ in 𝓝[>] (0:ℝ), Φ ξ < θ := hΦt.eventually (gt_mem_nhds hθ)
  have hle1 : ∀ᶠ ξ in 𝓝[>] (0:ℝ), ξ ≤ 1 :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT one_pos) fun ξ hξ => hξ.2.le
  -- the pure inequality `a n - C n^{7/8} ≤ s G - (1 - s) E₀ - √(β log |Fn|)`
  obtain ⟨hGa, hana, ha₁0⟩ := gem_le_a hn1 hFnV
  have hcard : (1 : ℝ) ≤ Fn.card := by exact_mod_cast hne.card_pos
  have hL0 : 0 ≤ Real.log Fn.card := Real.log_nonneg hcard
  have hLle : Real.log Fn.card ≤ c * Mr * (q ^ 8 * Real.log 16) := by
    have hlogM : Real.log ((16 : ℝ) ^ n) = q ^ 8 * Real.log 16 := by
      rw [Real.log_pow, hq8]
    have hMlog : 0 ≤ Mr * Real.log Mr := by
      rw [hMr_def, hlogM]; positivity
    calc Real.log Fn.card ≤ C₀ * Mr * Real.log Mr := hlog
      _ ≤ c * Mr * Real.log Mr := by
        rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hC₀c hMlog
      _ = c * Mr * (q ^ 8 * Real.log 16) := by rw [hMr_def, hlogM]
  have hfin := final_ineq (a₁ := a₁) (an := a n) (G := gaussianExpectedMax Fn zCov
      (fun f => -energy f)) (L := Real.log Fn.card) hq1 hc0 hc₂0 ha₁0 hMr0
    (by rw [← hαeq]; exact hα1) hc₁0 hG (hGa.trans (by rw [hq8]; exact hana)) hβ0 hβle hL0 hLle
  rw [← hαeq, ← hE₀q, hq7] at hfin
  -- main estimate
  filter_upwards [h54ξ, self_mem_nhdsWithin, hle1, hΦev] with ξ hGL hξ hξ1 hΦξ
  intro S w hS hw hw1 d u hGram
  have hξ0 : (0:ℝ) < ξ := hξ
  set δ : ℝ := ξ ^ (2 / 3 : ℝ) with hδ_def
  have hδ : 0 < δ := Real.rpow_pos_of_pos hξ0 _
  have hξδ : ξ ^ 2 = δ ^ 3 := (rpow_two_thirds_cube hξ0.le).symm
  have hb : 0 < δ * R := mul_pos hδ hR0
  have ha : 0 < 4 * (δ * R) / Mr := by positivity
  have hab : 4 * (δ * R) / Mr ≤ δ * R := by
    rw [div_le_iff₀ hMr0]
    have := mul_le_mul_of_nonneg_left (by linarith : (4:ℝ) ≤ Mr) hb.le
    linarith
  -- the Gram hypothesis on the block points
  have hGram' : ∀ p ∈ blockPts (16 ^ n) δ Fn S, ∀ p' ∈ blockPts (16 ^ n) δ Fn S,
      ⟪u p, u p'⟫ = bandCov (4 * (δ * R) / Mr) (δ * R) p p' := hGram
  have hv : ∀ f ∈ Fn, ∀ i < 16 ^ n, ∀ z ∈ S, ‖u (edgeSim (16 ^ n) δ f i z)‖ ^ 2 = v := by
    intro f hf i hi z hz
    have hp : edgeSim (16 ^ n) δ f i z ∈ blockPts (16 ^ n) δ Fn S := ⟨f, hf, i, hi, z, hz, rfl⟩
    rw [← real_inner_self_eq_norm_sq, hGram' _ hp _ hp, bandCov_self ha hab, hv_def]
    congr 1; field_simp
  have hT := hb2 hFnV h0 hE' hξ0 hξ1 hδ hw hw1 u hv
  -- (5.4) at this `δ`, for the Gram vectors `y_f = (ξ/δ²)(V_f - V_0)`
  have hy : ∀ f ∈ Fn, ∀ g ∈ Fn,
      (1 - α) * (2 * π * ∫ x in (0:ℝ)..1, |f x - g x|) - β ≤
        ‖(ξ / δ ^ 2) • (vecV n δ S w u f - vecV n δ S w u 0) -
          (ξ / δ ^ 2) • (vecV n δ S w u g - vecV n δ S w u 0)‖ ^ 2 := by
    intro f hf g hg
    have hGfg : ∀ h h' : ℝ → ℝ, (h = f ∨ h = g) → (h' = f ∨ h' = g) → ∀ k ∈ bIdx n S,
        ∀ l ∈ bIdx n S, ⟪u (bP n δ h k), u (bP n δ h' l)⟫ =
          bandCov (4 * (δ * R) / (16 : ℝ) ^ n) (δ * R) (bP n δ h k) (bP n δ h' l) := by
      intro h h' hh hh' k hk l hl
      have hhF : h ∈ Fn := by rcases hh with rfl | rfl <;> assumption
      have hhF' : h' ∈ Fn := by rcases hh' with rfl | rfl <;> assumption
      obtain ⟨hk1, hk2⟩ := Finset.mem_product.1 hk
      obtain ⟨hl1, hl2⟩ := Finset.mem_product.1 hl
      exact hGram' _ ⟨h, hhF, k.1, Finset.mem_range.1 hk1, k.2, hk2, rfl⟩ _
        ⟨h', hhF', l.1, Finset.mem_range.1 hl1, l.2, hl2, rfl⟩
    have h1 := hGL f hf g hg S w (hS.trans (tube_mono hδ.le
      (mul_le_mul_of_nonneg_right hC₀c (Real.sqrt_nonneg _)))) hw hw1
      (EuclideanSpace ℝ (Fin d)) u hGfg
    have e1 : (ξ / δ ^ 2) • (vecV n δ S w u f - vecV n δ S w u 0) -
        (ξ / δ ^ 2) • (vecV n δ S w u g - vecV n δ S w u 0) =
        (ξ / δ ^ 2) • (vecV n δ S w u f - vecV n δ S w u g) := by
      rw [← smul_sub, sub_sub_sub_cancel_right]
    have e2 : ‖(ξ / δ ^ 2) • (vecV n δ S w u f - vecV n δ S w u g)‖ ^ 2 =
        ‖vecV n δ S w u f - vecV n δ S w u g‖ ^ 2 / δ := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, div_pow, hξδ]
      field_simp
    rw [e1, e2, hα_def]
    linarith
  have hSF : √(1 - α) * gaussianExpectedMax Fn zCov (fun f => -energy f) -
      (1 - √(1 - α)) * E₀ - √(β * Real.log Fn.card) ≤
      vecExpectedMax Fn (fun f => -((ξ / δ ^ 2) • (vecV n δ S w u f - vecV n δ S w u 0)))
        (fun f => -energy f) :=
    hb1 hFnV hne hα0 hα1 hβ0 hE' (fun f => (ξ / δ ^ 2) • (vecV n δ S w u f - vecV n δ S w u 0))
      hy
  -- the remainder
  have hRem : (Fn.card : ℝ) * (2 * ξ * Real.exp (v / 2) * δ ^ 2 * E₀ +
      4 * ξ ^ 2 * Real.exp (2 * v) * (1 + δ ^ 2 * E₀)) = δ ^ 2 * Φ ξ := by
    rw [hΦ_def, hξδ]; simp only; rw [← hδ_def]; ring
  rw [hRem] at hT
  have hΦδ : δ ^ 2 * Φ ξ ≤ δ ^ 2 * θ := mul_le_mul_of_nonneg_left hΦξ.le (by positivity)
  have hmain := mul_le_mul_of_nonneg_left (hfin.trans hSF) (by positivity : (0:ℝ) ≤ δ ^ 2)
  linarith

/-- **Lemma 5.1**, with the (proved) graph covariance limit plugged in. -/
theorem lemma51_of_parts (hb1 : SfLowerProp) (hb2 : TaylorProp) : Blueprint.Draft.Lemma51 :=
  lemma51_of graphCovLimit hb1 hb2

end LQGDimension.L51
