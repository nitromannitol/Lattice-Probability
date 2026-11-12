/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5D117C2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117A
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117B
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117C
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W12
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32UClip
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L6Log
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Space

/-!
# D117 packet P-SIM (d): `DZZSimCoupleU` (P2-DZZSIM)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) lem-scaling-coupling (l. 611–624) composed with
Lemma 3.8 (l. 1218–1233) in the walled form of Remark 5.2 (l. 2281–2284), as used at
l. 2318–2322 and 2538–2548. Proof (DZZ's): on a product space with two independent white noises
`W, W'`, take `W₂ = coupledNoise θ W W'` (`dzz_lemma29_simU`, uniform in `b`); the exponents of
the chaos of `h̃[W]` along `2^{-n}` and of `h̃[W₂]` along `|a| 2^{-n}` at `θ v` differ by at most
`γ (|h̃ − η|[W] + |η[W] − η[W₂] ∘ θ| + |η − h̃|[W₂] ∘ θ) + γ²/2 (B + log |a|⁻¹)`
(DZZ L2.7, L2.9 `dzz_lemma29_simU`, (eq-var-compare) `tildeVar_two_point_le`), so
`lgd_sim_sandwich` gives the sandwich outside an event of probability `≤ C e^{−λ²/C}`.

DZZ use two facts at the scales `|a| 2^{-n}` that the library has only for `|a| = 2^{-m}`:
* `DZZWickChaosAlong c`: `M^W` is the chaos limit (eq-def-M-eta) of `h̃` along `c 2^{-n}` (DZZ
  l. 1209–1213 define it as a limit as `δ → 0`; the library proves it along `2^{-n}`,
  `ae_isChaosLimit_wickQArea`);
* `DZZLemma27Along c`: DZZ Lemma 2.7 (l. 548–576) along `c 2^{-j}` (library: `dzz_lemma27_uncond`).
`dzzSimCoupleU_of_along` proves `DZZSimCoupleU` from these two at `c = ‖a‖`; both hold for
`c = 2^{-m}` (`dzzWickChaosAlong_pow`, `dzzLemma27Along_pow`), which gives
`dzzSimCoupleU_dyadic` unconditionally.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise WNPush SupTail

lemma IsChaosLimit.shift {γ : ℝ} {ζ V : ℝ → ℂ → ℝ} {s : ℕ → ℝ} {μ : Measure ℂ}
    (h : IsChaosLimit γ ζ V s μ) (m : ℕ) : IsChaosLimit γ ζ V (fun n => s (n + m)) μ :=
  fun c q hq => (h c q hq).comp (tendsto_add_atTop_nat m)

lemma dzzVXi_sub_ferniqueBox {ξ : ℝ} : dzzVXi ξ ⊆ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) := by
  intro z hz
  obtain ⟨h1, h2, h3, h4⟩ := dzzVXi_sub_dzzVIn le_rfl hz
  exact ⟨⟨h1, by simp only; linarith⟩, ⟨h3, by simp only; linarith⟩⟩

lemma ferniqueBox_xi_sub_unit {ξ : ℝ} (hξ : 0 ≤ ξ) :
    ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) ⊆ ferniqueBox 0 1 := by
  rintro z ⟨⟨h1, h2⟩, h3, h4⟩
  simp only at h1 h2 h3 h4
  exact ⟨⟨by simp only [Complex.zero_re]; linarith, by simp only [Complex.zero_re]; linarith⟩,
    ⟨by simp only [Complex.zero_im]; linarith, by simp only [Complex.zero_im]; linarith⟩⟩

/-- **(eq-def-M-eta) along the scales `c 2^{-n}`** (DZZ l. 1209–1213): `M^W` is the chaos limit
of continuous versions of `h̃_{c 2^{-n}}`. -/
def DZZWickChaosAlong (c : ℝ) : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {W : WNSpace → Ω' → ℝ},
    IsWhiteNoise P' W → ∀ {γ : ℝ}, 0 < γ → γ < 2 →
    ∃ Z : ℝ → ℂ → Ω' → ℝ, (∀ (n : ℕ) (ω : Ω'), Continuous fun x => Z (c * (1 / 2 : ℝ) ^ n) x ω) ∧
      (∀ (n : ℕ) (x : ℂ), Z (c * (1 / 2 : ℝ) ^ n) x =ᵐ[P'] tildeHInf W (c * (1 / 2 : ℝ) ^ n) x) ∧
      ∀ᵐ ω ∂P', IsChaosLimit γ (fun s z => Z s z ω) tildeVar (fun n => c * (1 / 2 : ℝ) ^ n)
        (wickQArea γ W ω)

/-- **DZZ Lemma 2.7 along the scales `c 2^{-j}`** (`lem-tilde-h-eta`, l. 548–576). -/
def DZZLemma27Along (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ},
    IsWhiteNoise P W → ∀ Z : ℕ → ℂ → Ω → ℝ, (∀ j ω, Continuous fun x => Z j x ω) →
    (∀ j x, Z j x =ᵐ[P] fun ω => tildeHInf W (c * (1 / 2 : ℝ) ^ j) x ω -
      etaInf W (c * (1 / 2 : ℝ) ^ j) x ω) →
    ∀ lam : ℝ, 0 ≤ lam →
      P.real {ω | ∃ v ∈ ferniqueBox 0 1, ∃ j : ℕ, lam ≤ |Z j v ω|} ≤ C * Real.exp (-lam ^ 2 / C)

lemma dzzWickChaosAlong_pow (m : ℕ) : DZZWickChaosAlong ((1 / 2 : ℝ) ^ m) := by
  intro Ω' _ P' W hW γ hγ hγ2
  have e : ∀ n : ℕ, (1 / 2 : ℝ) ^ m * (1 / 2) ^ n = (1 / 2) ^ (n + m) := fun n => by
    rw [← pow_add, add_comm]
  refine ⟨wickZeta hW, fun n ω => ?_, fun n x => ?_, ?_⟩
  · rw [e]; exact (wickZeta_spec hW).1 (n + m) ω
  · rw [e]; exact (wickZeta_spec hW).2 (n + m) x
  · filter_upwards [ae_isChaosLimit_wickQArea hW hγ hγ2] with ω h
    have hs : (fun n : ℕ => (1 / 2 : ℝ) ^ m * (1 / 2) ^ n) = fun n => (1 / 2) ^ (n + m) :=
      funext e
    rw [hs]
    exact h.shift m

/-- **`DZZSimCoupleU` from DZZ's chaos limit and Lemma 2.7 at the scales `‖a‖ 2^{-n}`** (DZZ
lem-scaling-coupling, l. 611–624, with Lemma 3.8 walled, Remark 5.2): for `0 < ‖a‖ ≤ 1` and a
closed `K ⊆ 𝕍^ξ`, the similarity coupling of the walled LGDs holds with a constant uniform in
the translation `b`. -/
theorem dzzSimCoupleU_of_along {γ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hξ : 0 < ξ)
    (hξ2 : ξ < 1 / 2) {K : Set ℂ} (hK : IsClosed K) (hKξ : K ⊆ dzzVXi ξ) {a : ℂ} (ha0 : a ≠ 0)
    (ha1 : ‖a‖ ≤ 1) (hch : DZZWickChaosAlong ‖a‖) (h27a : DZZLemma27Along ‖a‖) :
    DZZSimCoupleU γ ξ K a := by
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha0
  obtain ⟨C29, hC29, h29⟩ := dzz_lemma29_simU.{0} hξ hξ2 ha0 ha1
  obtain ⟨C27, hC27, h27⟩ := dzz_lemma27_uncond.{0}
  obtain ⟨C27b, hC27b, h27b⟩ := h27a
  obtain ⟨Bv, hBv, hvar⟩ := tildeVar_two_point_le hξ (by linarith)
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hla : 0 ≤ Real.log ‖a‖⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hna, ha1⟩)
  set V0 := Bv + Real.log ‖a‖⁻¹ with hV0
  have hV00 : 0 ≤ V0 := by positivity
  set lam0 := γ ^ 2 / 2 * V0 with hlam0
  have hlam00 : 0 ≤ lam0 := by positivity
  set M := max (max C27 C27b) C29 with hM
  have hM0 : 0 < M := lt_max_of_lt_right hC29
  set C := max (9 * γ ^ 2 * M) (3 * M) + lam0 ^ 2 + 3 with hC
  have hC0 : 0 < C := by positivity
  refine ⟨C, hC0, fun b hθK => ?_⟩
  set θ := simMap a b
  have hKbox : K ⊆ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) := hKξ.trans dzzVXi_sub_ferniqueBox
  have hθbox : θ '' K ⊆ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) := hθK.trans dzzVXi_sub_ferniqueBox
  have hKV : K ⊆ dzzV := hKξ.trans (dzzVXi_sub_dzzV ξ)
  have hθKV : θ '' K ⊆ dzzV := hθK.trans (dzzVXi_sub_dzzV ξ)
  have hunit := ferniqueBox_xi_sub_unit hξ.le
  set P' : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := LQGDimension.ExistAsm.stdP.prod
    LQGDimension.ExistAsm.stdP
  have hW := DDDF.isWhiteNoise_fst hW₀
  have hW' := DDDF.isWhiteNoise_snd hW₀
  have hind := DDDF.indepFun_fst_snd_noise hW₀
  obtain ⟨hW₂, htail⟩ := h29 b hKbox hθbox hW hW' hind
  set W : WNSpace → (ℕ → ℝ) × (ℕ → ℝ) → ℝ := fun f ω => W₀ f ω.1
  set W₂ := coupledNoise (confHyp_simMap ha0 b) W (fun f ω => W₀ f ω.2)
  refine ⟨(ℕ → ℝ) × (ℕ → ℝ), inferInstance, P', W, W₂, hW, hW₂, fun lam hlam => ?_⟩
  have hP := hW.isProbabilityMeasure
  by_cases hl : lam < lam0
  · -- small `λ`: the bound is `≥ 1`
    refine measureReal_le_one.trans ?_
    have hsq : lam ^ 2 / C ≤ 1 := by
      rw [div_le_one hC0]
      have : lam ^ 2 ≤ lam0 ^ 2 := pow_le_pow_left₀ hlam hl.le 2
      have : 0 ≤ max (9 * γ ^ 2 * M) (3 * M) := le_max_of_le_right (by positivity)
      linarith
    have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
    have h1 : Real.exp (-1) ≤ Real.exp (-lam ^ 2 / C) := by
      rw [Real.exp_le_exp, neg_div]; linarith
    have h2 : 1 ≤ 3 * Real.exp (-1) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos 1)]; linarith
    have h3 : (3 : ℝ) ≤ C := by
      have : 0 ≤ max (9 * γ ^ 2 * M) (3 * M) := le_max_of_le_right (by positivity)
      nlinarith [sq_nonneg lam0]
    nlinarith [Real.exp_pos (-1), Real.exp_pos (-lam ^ 2 / C)]
  push Not at hl
  -- continuous versions of `η`
  have hp : ∀ j : ℕ, (0 : ℝ) < (1 / 2) ^ j := fun j => by positivity
  choose Y1 hY1c hY1m hY1 using fun j : ℕ => exists_continuous_etaInf hW (hp j)
  choose Y2 hY2c hY2m hY2 using fun j : ℕ => exists_continuous_etaInf hW₂ (mul_pos hna (hp j))
  obtain ⟨Zc, hZcc, hZce, hZch⟩ := hch hW₂ hγ hγ2
  set t := lam / (3 * γ) with ht
  have ht0 : 0 ≤ t := by positivity
  -- the three Gaussian events
  set Z1 : ℕ → ℂ → (ℕ → ℝ) × (ℕ → ℝ) → ℝ := fun j x ω =>
    wickZeta hW ((1 / 2 : ℝ) ^ j) x ω - Y1 j x ω
  set Z3 : ℕ → ℂ → (ℕ → ℝ) × (ℕ → ℝ) → ℝ := fun j x ω =>
    Zc (‖a‖ * (1 / 2 : ℝ) ^ j) x ω - Y2 j x ω
  have hP1 := h27 hW Z1 (fun j ω => ((wickZeta_spec hW).1 j ω).sub (hY1c j ω))
    (fun j x => by
      filter_upwards [(wickZeta_spec hW).2 j x, hY1 j x] with ω h1 h2
      simp only [Z1, h1, h2]) t ht0
  have hP3 := h27b hW₂ Z3 (fun j ω => (hZcc j ω).sub (hY2c j ω))
    (fun j x => by
      filter_upwards [hZce j x, hY2 j x] with ω h1 h2
      simp only [Z3, h1, h2]) t ht0
  have hP2 := htail Y1 Y2 hY1c hY2c hY1 hY2 t ht0
  set E1 := {ω | ∃ v ∈ ferniqueBox 0 1, ∃ j : ℕ, t ≤ |Z1 j v ω|}
  set E2 := {ω | ∃ v ∈ K, ∃ j : ℕ, t ≤ |Y1 j v ω - Y2 j (θ v) ω|}
  set E3 := {ω | ∃ v ∈ ferniqueBox 0 1, ∃ j : ℕ, t ≤ |Z3 j v ω|}
  -- the bad event is contained in `E1 ∪ E2 ∪ E3` up to a null set
  have hsub : {ω | ¬ ∀ x ∈ K, ∀ y ∈ K, ∀ δ : ℝ, 0 < δ →
      lgdDZZ (dzzWall (θ '' K) (dzzMuIn γ W₂ ω)) (‖a‖ * δ * Real.exp lam) (θ x) (θ y) ≤
        lgdDZZ (dzzWall K (dzzMuIn γ W ω)) δ x y ∧
      lgdDZZ (dzzWall K (dzzMuIn γ W ω)) δ x y ≤
        lgdDZZ (dzzWall (θ '' K) (dzzMuIn γ W₂ ω)) (‖a‖ * δ * Real.exp (-lam)) (θ x) (θ y)}
      ≤ᵐ[P'] E1 ∪ E2 ∪ E3 := by
    filter_upwards [ae_isChaosLimit_wickQArea hW hγ hγ2, hZch] with ω h1 h2 hbad
    by_contra hnot
    simp only [mem_union, not_or, E1, E2, E3, mem_ofPred_eq, not_exists, not_and, not_le]
      at hnot
    obtain ⟨⟨n1, n2⟩, n3⟩ := hnot
    refine hbad fun x _ y _ δ _ => ?_
    have hc : ∀ n : ℕ, ∀ z ∈ K,
        |(γ * wickZeta hW ((1 / 2 : ℝ) ^ n) z ω - γ ^ 2 / 2 * tildeVar ((1 / 2 : ℝ) ^ n) z) -
          (γ * Zc (‖a‖ * (1 / 2 : ℝ) ^ n) (θ z) ω -
            γ ^ 2 / 2 * tildeVar (‖a‖ * (1 / 2 : ℝ) ^ n) (θ z))| ≤ 2 * lam := by
      intro n z hz
      have hθz : θ z ∈ θ '' K := mem_image_of_mem θ hz
      have e1 := n1 z (hunit (hKbox hz)) n
      have e2 := n2 z hz n
      have e3 := n3 (θ z) (hunit (hθbox hθz)) n
      have ev := hvar n ‖a‖ hna ha1 z (θ z) (hKbox hz) (hθbox hθz)
      simp only [Z1, Z3] at e1 e3
      have hsplit : wickZeta hW ((1 / 2 : ℝ) ^ n) z ω -
          Zc (‖a‖ * (1 / 2 : ℝ) ^ n) (θ z) ω =
          (wickZeta hW ((1 / 2 : ℝ) ^ n) z ω - Y1 n z ω) +
            (Y1 n z ω - Y2 n (θ z) ω) -
            (Zc (‖a‖ * (1 / 2 : ℝ) ^ n) (θ z) ω - Y2 n (θ z) ω) := by ring
      have hf : |wickZeta hW ((1 / 2 : ℝ) ^ n) z ω -
          Zc (‖a‖ * (1 / 2 : ℝ) ^ n) (θ z) ω| ≤ 3 * t := by
        rw [hsplit]
        refine (abs_sub _ _).trans ?_
        have := abs_add_le (wickZeta hW ((1 / 2 : ℝ) ^ n) z ω - Y1 n z ω)
          (Y1 n z ω - Y2 n (θ z) ω)
        linarith
      have hid : (γ * wickZeta hW ((1 / 2 : ℝ) ^ n) z ω -
            γ ^ 2 / 2 * tildeVar ((1 / 2 : ℝ) ^ n) z) -
          (γ * Zc (‖a‖ * (1 / 2 : ℝ) ^ n) (θ z) ω -
            γ ^ 2 / 2 * tildeVar (‖a‖ * (1 / 2 : ℝ) ^ n) (θ z)) =
          γ * (wickZeta hW ((1 / 2 : ℝ) ^ n) z ω -
            Zc (‖a‖ * (1 / 2 : ℝ) ^ n) (θ z) ω) -
          γ ^ 2 / 2 * (tildeVar ((1 / 2 : ℝ) ^ n) z -
            tildeVar (‖a‖ * (1 / 2 : ℝ) ^ n) (θ z)) := by ring
      rw [hid]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos hγ, abs_of_nonneg (by positivity : (0 : ℝ) ≤ γ ^ 2 / 2)]
      have h3t : γ * (3 * t) = lam := by rw [ht]; field_simp
      have := mul_le_mul_of_nonneg_left hf hγ.le
      have := mul_le_mul_of_nonneg_left ev (by positivity : (0 : ℝ) ≤ γ ^ 2 / 2)
      linarith
    have hs := lgd_sim_sandwich h1 h2 ha0 b hK hKV hθKV hc δ x y
    rw [show 2 * lam / 2 = lam by ring, show -(2 * lam) / 2 = -lam by ring] at hs
    exact hs
  -- the union bound
  have hexp : ∀ c : ℝ, 0 < c → c ≤ M →
      c * Real.exp (-t ^ 2 / c) ≤ M * Real.exp (-lam ^ 2 / C) := by
    intro c hc hcM
    refine mul_le_mul hcM (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hM0.le
    have hC9 : 9 * γ ^ 2 * c ≤ C := by
      have := le_max_left (9 * γ ^ 2 * M) (3 * M)
      nlinarith [sq_nonneg γ, sq_nonneg lam0]
    rw [ht, div_pow, neg_div, neg_div, neg_le_neg_iff, div_div,
      div_le_div_iff₀ hC0 (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hC9 (sq_nonneg lam)]
  have f1 := hexp C27 hC27 ((le_max_left _ _).trans (le_max_left _ _))
  have f1' := hexp C27b hC27b ((le_max_right _ _).trans (le_max_left _ _))
  have f2 := hexp C29 hC29 (le_max_right _ _)
  have h3M : 3 * M ≤ C := by
    have := le_max_right (9 * γ ^ 2 * M) (3 * M)
    nlinarith [sq_nonneg lam0]
  calc _ ≤ P'.real (E1 ∪ E2 ∪ E3) :=
        ENNReal.toReal_mono (measure_ne_top P' _) (measure_mono_ae hsub)
    _ ≤ P'.real E1 + P'.real E2 + P'.real E3 :=
        (measureReal_union_le _ _).trans (by linarith [measureReal_union_le (μ := P') E1 E2])
    _ ≤ 3 * M * Real.exp (-lam ^ 2 / C) := by linarith
    _ ≤ C * Real.exp (-lam ^ 2 / C) :=
        mul_le_mul_of_nonneg_right h3M (Real.exp_pos _).le

end DZZ
end LQGMetric
