/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53X4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53K2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53X2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53X3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53V1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3Eta9B
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117G3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D125C

/-!
# P-131S (4): the scaling coupling for DZZ's η-chaos on the small side, all `‖a‖ ≤ 1`
(P2-DZZ53X, `fineChaos_sim_couple`)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) (eq-scaling-invariance-approximate), l. 2474, and its
proof l. 2531–2548 (through `ĥ`), with the mass comparison l. 2501–2503; decision D131 §3 and
the amendment §9 (the small side is the mass map `fineMass W₂ γ m` = DZZ's `M̃_{γ,2^{-m},η}`).

Proof: `dzzSimCoupleScale_of` (S5D125C) and `dzz_lemma29_simScale` (S5D125B), copied and
modified (near-miss reuse). Coupling `W₂ = coupledNoise θ W₁ W'`; with `c = 2^{-m}/‖a‖ ∈ (0,1]`:
* exact scaling of the `ĥ` band (`phi_coupledNoise_simMap`, `phi_add_ae`):
  `ĥ^1_{2^{-(n+m)}}[W₂](θz) − ĥ^1_{2^{-m}}[W₂](θz) = ĥ^1_{c2^{-n}}[W₁](z) − ĥ^1_c[W₁](z)`;
* the small-side field is the band `η^{2^{-m}}_{2^{-(n+m)}}[W₂] = η_{2^{-(n+m)}} − η_{2^{-m}}`
  (`ae_etaCV_split`, S3Eta9B, inside the integrals; `ae_tendsto_fineMass_exp`, S5L53K2);
* `η − ĥ` for `W₂` at dyadic scales (`dzz_lemma28_uncond`), `ĥ − η` and `h̃ − η` for `W₁` along
  `c 2^{-n}` with constants uniform in `c` (`dzz_lemma28_unif`, `dzzLemma27Along_unif`, S5L53X2),
  the coarse band `ĥ^1_c[W₁]` on `𝕍^ξ` (`hat_sup_tail_grid`, S5L53X3);
* variances: `Var h̃_{c2^{-n}} ≤ log (c2^{-n})^{-1} + 4 + b₁` (`etaVar_le`,
  `tildeVar_sub_etaVar_le`) and `Var η^{2^{-m}}_{2^{-(n+m)}} ≥ n log 2 − B` (`etaVarBand_ge`,
  P-131V), difference `≤ log(‖a‖2^m) + B'`: the factor `(‖a‖ 2^m)^{γ²/4}` of the threshold;
* the LGD comparison `lgdRat_sim_upper` (S5L53K2).

Correction of the DEC-131 §3 statement (see the report): the tail is
`C (‖a‖2^m)² e^{−λ²/(C(log(‖a‖2^m)+1))}`, not `C e^{−λ²/(C(log₂‖a‖⁻¹+2))}`: the coarse band
`ĥ^1_c[W₁]` (variance `log c⁻¹ = log(‖a‖2^m)`, unbounded in `m` for fixed `‖a‖`) has to be
controlled on all of `K`, which costs the number `≍ c^{-2}` of resolution boxes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise WNPush SupTail

set_option maxHeartbeats 1000000 in
/-- **The scaling coupling for the η-chaos on the small side** (DZZ (eq-scaling-invariance-
approximate) l. 2474 with l. 2501–2503 and 2531–2548; DEC-131 §3, §9): for `‖a‖ ≤ 1`, `θ = simMap a b`
with `θK ⊆ 𝕍^ξ` and `2^{-m} ≤ ‖a‖`, outside an event of probability
`≤ C (‖a‖2^m)² e^{−λ²/(C(log(‖a‖2^m)+1))}` (`C = C(γ, ξ)`),
`D^{θK}_{‖a‖ δ e^λ (‖a‖2^m)^{γ²/4}}(θx, θy)[M̃_{γ,2^{-m},η}[W₂]] ≤ D^K_δ(x, y)[μIn[W₁]]`. -/
theorem fineChaos_sim_couple {γ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hξ : 0 < ξ) (hξ2 : ξ < 1 / 2)
    {K : Set ℂ} (hK : IsClosed K) (hKξ : K ⊆ dzzVXi ξ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℂ), 0 < ‖a‖ → ‖a‖ ≤ 1 → ∀ b : ℂ, simMap a b '' K ⊆ dzzVXi ξ →
      ∀ m : ℕ, (2 : ℝ)⁻¹ ^ m ≤ ‖a‖ →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (W₁ W₂ : WNSpace → Ω' → ℝ),
        IsWhiteNoise P' W₁ ∧ IsWhiteNoise P' W₂ ∧ ∀ lam : ℝ, 0 ≤ lam →
        P'.real {ω | ¬ ∀ x ∈ K, ∀ y ∈ K, ∀ δ : ℝ, 0 < δ →
          lgdRat (wallMass (simMap a b '' K) (fineMass W₂ γ m ω))
              (‖a‖ * δ * Real.exp lam * (‖a‖ * 2 ^ m) ^ (γ ^ 2 / 4))
              {simMap a b x} {simMap a b y} ≤
            lgdDZZ (dzzWall K (dzzMuIn γ W₁ ω)) δ x y} ≤
          C * (‖a‖ * 2 ^ m) ^ 2 * Real.exp (-lam ^ 2 / (C * (Real.log (‖a‖ * 2 ^ m) + 1))) := by
  obtain ⟨C28, hC28, h28⟩ := dzz_lemma28_uncond.{0} hξ hξ2
  obtain ⟨C8u, hC8u, h8u⟩ := dzz_lemma28_unif hξ hξ2
  obtain ⟨C7u, hC7u, h7u⟩ := dzzLemma27Along_unif
  obtain ⟨Bv, hBv, hvar⟩ := etaVarBand_ge hξ hξ2
  obtain ⟨b₁, hb₁, htv⟩ := tildeVar_sub_etaVar_le
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise
  set CD := 32 * Real.exp (8 * ferniqueCF ^ 2) with hCD
  have hCD0 : 0 < CD := by positivity
  set M := max (max C28 C8u) (max C7u CD) with hM
  have hM0 : 0 < M := lt_max_of_lt_left (lt_max_of_lt_left hC28)
  set Bv' := 4 + b₁ + Bv with hBv'
  set lam0 := γ ^ 2 / 2 * Bv' with hlam0
  have hlam00 : 0 ≤ lam0 := by positivity
  set C := 25 * γ ^ 2 * (M + 4) + 4 * M + lam0 ^ 2 + 3 with hC
  have hC0 : 0 < C := by positivity
  refine ⟨C, hC0, fun a hna ha1 b hθK m hma => ?_⟩
  have ha0 : a ≠ 0 := norm_pos_iff.1 hna
  set θ := simMap a b with hθ
  set s' : ℝ := (2 : ℝ)⁻¹ ^ m with hs'
  have hs'0 : 0 < s' := by positivity
  set c : ℝ := s' / ‖a‖ with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by rw [hc, div_le_one hna]; exact hma
  set R : ℝ := ‖a‖ * 2 ^ m with hR
  have hR1 : 1 ≤ R := by
    have e : (2 : ℝ)⁻¹ ^ m * 2 ^ m = 1 := by rw [← mul_pow]; norm_num
    calc (1 : ℝ) = (2 : ℝ)⁻¹ ^ m * 2 ^ m := e.symm
      _ ≤ ‖a‖ * 2 ^ m := mul_le_mul_of_nonneg_right hma (by positivity)
  have hR0 : 0 < R := by linarith
  have hcR : c⁻¹ = R := by
    rw [hc, inv_div, hs', hR, inv_pow, div_inv_eq_mul]
  set Lc := Real.log R with hLc
  have hLc0 : 0 ≤ Lc := Real.log_nonneg hR1
  have eh : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  have hac : ‖a‖ * c = (1 / 2 : ℝ) ^ m := by
    rw [hc, mul_div_cancel₀ _ hna.ne', hs', eh]
  have hacn : ∀ n : ℕ, ‖a‖ * (c * (1 / 2 : ℝ) ^ n) = (1 / 2 : ℝ) ^ (n + m) := fun n => by
    rw [← mul_assoc, hac, ← pow_add, add_comm]
  have hp : ∀ j : ℕ, (0 : ℝ) < (1 / 2) ^ j := fun j => by positivity
  have hcn : ∀ n : ℕ, 0 < c * (1 / 2 : ℝ) ^ n := fun n => by positivity
  have hcn1 : ∀ n : ℕ, c * (1 / 2 : ℝ) ^ n ≤ c := fun n =>
    mul_le_of_le_one_right hc0.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hKbox : K ⊆ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) := hKξ.trans dzzVXi_sub_ferniqueBox
  have hθbox : θ '' K ⊆ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) := hθK.trans dzzVXi_sub_ferniqueBox
  have hKV : K ⊆ dzzV := hKξ.trans (dzzVXi_sub_dzzV ξ)
  have hunit := ferniqueBox_xi_sub_unit hξ.le
  -- the coupling
  set P' : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := LQGDimension.ExistAsm.stdP.prod
    LQGDimension.ExistAsm.stdP
  have hW₁ := DDDF.isWhiteNoise_fst hW₀
  have hW' := DDDF.isWhiteNoise_snd hW₀
  have hind := DDDF.indepFun_fst_snd_noise hW₀
  set W₁ : WNSpace → (ℕ → ℝ) × (ℕ → ℝ) → ℝ := fun f ω => W₀ f ω.1
  set W₂ := coupledNoise (confHyp_simMap ha0 b) W₁ (fun f ω => W₀ f ω.2)
  have hW₂ : IsWhiteNoise P' W₂ := isWhiteNoise_coupledNoise_simMap ha0 b hW₁ hW' hind
  refine ⟨(ℕ → ℝ) × (ℕ → ℝ), inferInstance, P', W₁, W₂, hW₁, hW₂, fun lam hlam => ?_⟩
  have hP := hW₁.isProbabilityMeasure
  have hLc1 : 1 ≤ Lc + 1 := by linarith
  by_cases hl : lam < lam0
  · -- small `λ`: the bound is `≥ 1`
    refine measureReal_le_one.trans ?_
    have hsq : lam ^ 2 / (C * (Lc + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : lam ^ 2 ≤ lam0 ^ 2 := pow_le_pow_left₀ hlam hl.le 2
      have : C ≤ C * (Lc + 1) := le_mul_of_one_le_right hC0.le hLc1
      have : 0 ≤ 25 * γ ^ 2 * (M + 4) + 4 * M := by positivity
      linarith
    have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
    have h1 : Real.exp (-1) ≤ Real.exp (-lam ^ 2 / (C * (Lc + 1))) := by
      rw [Real.exp_le_exp, neg_div]; linarith
    have h2 : 1 ≤ 3 * Real.exp (-1) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos 1)]; linarith
    have h3 : (3 : ℝ) ≤ C := by
      have : 0 ≤ 25 * γ ^ 2 * (M + 4) + 4 * M := by positivity
      nlinarith [sq_nonneg lam0]
    have h4 : C ≤ C * R ^ 2 := le_mul_of_one_le_right hC0.le (one_le_pow₀ hR1)
    nlinarith [Real.exp_pos (-1), Real.exp_pos (-lam ^ 2 / (C * (Lc + 1)))]
  push Not at hl
  set t := lam / (5 * γ) with ht
  have ht0 : 0 ≤ t := by positivity
  -- continuous versions
  choose Φ₂ hΦ₂c hΦ₂ using fun k : ℕ => exists_continuous_phi hW₂ (hp k) 1
  choose H₁ hH₁c hH₁ using fun n : ℕ => exists_continuous_phi hW₁ (hcn n) 1
  obtain ⟨Hc, hHcc, hHc⟩ := exists_continuous_phi hW₁ hc0 1
  choose Y₁ hY₁c hY₁m hY₁ using fun n : ℕ => exists_continuous_etaInf hW₁ (hcn n)
  obtain ⟨Zc, hZcc, hZce, hZch⟩ := dzzWickChaosAlong_of hc0 hc1 hW₁ hγ hγ2
  set E2 : ℕ → ℂ → (ℕ → ℝ) × (ℕ → ℝ) → ℝ := fun k => etaCV hW₂ k
  have hE2c : ∀ k ω, Continuous fun x => E2 k x ω := fun k => (etaCV_spec hW₂ k).1
  have hE2 : ∀ k x, E2 k x =ᵐ[P'] etaInf W₂ ((1 / 2 : ℝ) ^ k) x := fun k x => by
    have := (etaCV_spec hW₂ k).2.2 x; rwa [eh] at this
  -- the exact scaling of the `ĥ` band
  have hpt : ∀ n z, ∀ᵐ ω ∂P', Φ₂ (n + m) (θ z) ω - Φ₂ m (θ z) ω = H₁ n z ω - Hc z ω := by
    intro n z
    have c1 := phi_coupledNoise_simMap ha0 b hW' (W := W₁) (hcn n) c z
    rw [hacn n, hac] at c1
    have c2 := phi_add_ae hW₂ (hp (n + m)) (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (Nat.le_add_left m n)) (pow_le_one₀ (by norm_num) (by norm_num) : (1 / 2 : ℝ) ^ m ≤ 1) (θ z)
    have c3 := phi_add_ae hW₁ (hcn n) (hcn1 n) hc1 z
    filter_upwards [c1, c2, c3, hΦ₂ (n + m) (θ z), hΦ₂ m (θ z), hH₁ n z, hHc z] with
      ω h1 h2 h3 h4 h5 h6 h7
    rw [h4, h5, h6, h7, h2, h3, ← h1]
    ring
  have hall : ∀ᵐ ω ∂P', ∀ n : ℕ, ∀ z : ℂ,
      Φ₂ (n + m) (θ z) ω - Φ₂ m (θ z) ω = H₁ n z ω - Hc z ω := by
    have hq : ∀ᵐ ω ∂P', ∀ n : ℕ, ∀ q : ℚ × ℚ,
        Φ₂ (n + m) (θ (ratPt q)) ω - Φ₂ m (θ (ratPt q)) ω = H₁ n (ratPt q) ω - Hc (ratPt q) ω := by
      rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro q; exact hpt n (ratPt q)
    filter_upwards [hq] with ω hω n
    have hθc : Continuous θ := continuous_simMap a b
    have hS : Continuous fun x => Φ₂ (n + m) (θ x) ω - Φ₂ m (θ x) ω :=
      ((hΦ₂c (n + m) ω).comp hθc).sub ((hΦ₂c m ω).comp hθc)
    have := denseRange_ratPt'.equalizer hS ((hH₁c n ω).sub (hHcc ω)) (funext fun q => hω n q)
    exact fun x => congrFun this x
  -- the four Gaussian events
  set D2 : ℕ → ℂ → (ℕ → ℝ) × (ℕ → ℝ) → ℝ := fun k x ω => Φ₂ k x ω - E2 k x ω
  set D1 : ℕ → ℂ → (ℕ → ℝ) × (ℕ → ℝ) → ℝ := fun n x ω => H₁ n x ω - Y₁ n x ω
  set Z3 : ℕ → ℂ → (ℕ → ℝ) × (ℕ → ℝ) → ℝ := fun n x ω => Zc (c * (1 / 2 : ℝ) ^ n) x ω - Y₁ n x ω
  set EA := {ω | ∃ v ∈ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ), ∃ j : ℕ, t ≤ |D2 j v ω|}
  set EB := {ω | ∃ v ∈ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ), ∃ j : ℕ, t ≤ |D1 j v ω|}
  set EC := {ω | ∃ v ∈ ferniqueBox 0 1, ∃ j : ℕ, t ≤ |Z3 j v ω|}
  set ED := {ω | ∃ v ∈ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ), t ≤ |Hc v ω|}
  have hPA : P'.real EA ≤ C28 * Real.exp (-t ^ 2 / C28) :=
    h28 hW₂ D2 (fun j ω => (hΦ₂c j ω).sub (hE2c j ω)) (fun j x => by
      filter_upwards [hΦ₂ j x, hE2 j x] with ω h1 h2
      simp only [D2, h1, h2]) t ht0
  have hPB : P'.real EB ≤ C8u * Real.exp (-t ^ 2 / C8u) :=
    h8u c hc0 hc1 hW₁ D1 (fun j ω => (hH₁c j ω).sub (hY₁c j ω)) (fun j x => by
      filter_upwards [hH₁ j x, hY₁ j x] with ω h1 h2
      simp only [D1, h1, h2]) t ht0
  have hPC : P'.real EC ≤ C7u * Real.exp (-t ^ 2 / C7u) :=
    h7u c hc0 hc1 hW₁ Z3 (fun j ω => (hZcc j ω).sub (hY₁c j ω)) (fun j x => by
      filter_upwards [hZce j x, hY₁ j x] with ω h1 h2
      simp only [Z3, h1, h2]) t ht0
  have hPD : P'.real ED ≤ 16 * (c⁻¹) ^ 2 * (2 * Real.exp (8 * ferniqueCF ^ 2)) *
      Real.exp (-t ^ 2 / (4 * (Real.log c⁻¹ + 1))) :=
    hat_sup_tail_grid hW₁ hc0 hc1 (by linarith) (by linarith) hHcc hHc t ht0
  rw [hcR, ← hLc] at hPD
  -- the bad event is contained in `EA ∪ EB ∪ EC ∪ ED` up to a null set
  have hsub : {ω | ¬ ∀ x ∈ K, ∀ y ∈ K, ∀ δ : ℝ, 0 < δ →
      lgdRat (wallMass (θ '' K) (fineMass W₂ γ m ω))
          (‖a‖ * δ * Real.exp lam * (‖a‖ * 2 ^ m) ^ (γ ^ 2 / 4)) {θ x} {θ y} ≤
        lgdDZZ (dzzWall K (dzzMuIn γ W₁ ω)) δ x y} ≤ᵐ[P'] EA ∪ EB ∪ EC ∪ ED := by
    filter_upwards [hZch, hall, ae_etaCV_split hW₂, ae_tendsto_fineMass_exp hW₂ γ m] with
      ω h1 hω hsplit hfine hbad
    by_contra hnot
    simp only [mem_union, not_or, EA, EB, EC, ED, mem_ofPred_eq, not_exists, not_and, not_le]
      at hnot
    obtain ⟨⟨⟨n1, n2⟩, n3⟩, n4⟩ := hnot
    refine hbad fun x _ y _ δ _ => ?_
    set F₂ : ℕ → ℂ → ℝ := fun n w => γ * (etaCV hW₂ (n + m) w ω - etaCV hW₂ m w ω) -
      γ ^ 2 / 2 * etaBVar ((2 : ℝ)⁻¹ ^ m) (n + m) w with hF₂
    have h₂ : ∀ (x : ℚ × ℚ) (q : ℚ), 0 < q → ball (ratPt x) q ⊆ θ '' K →
        Tendsto (fun n => ∫⁻ z in ball (ratPt x) q, ENNReal.ofReal (Real.exp (F₂ n z))) atTop
          (𝓝 (fineMass W₂ γ m ω x q)) := by
      intro x q _ _
      refine ((hfine x q).comp (tendsto_add_atTop_nat m)).congr fun n => ?_
      simp only [Function.comp_apply]
      refine lintegral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [hsplit m (n + m) (Nat.le_add_left m n)] with z hz
      simp only [hF₂, hz, add_sub_cancel_right]
    have hpt : ∀ n : ℕ, ∀ z ∈ K, F₂ n (θ z) ≤ (2 * lam + γ ^ 2 / 2 * Lc) +
        (γ * Zc (c * (1 / 2 : ℝ) ^ n) z ω - γ ^ 2 / 2 * tildeVar (c * (1 / 2 : ℝ) ^ n) z) := by
      intro n z hz
      have hθz : θ z ∈ θ '' K := mem_image_of_mem θ hz
      have hzb := hKbox hz
      have hθb := hθbox hθz
      have e1 := n1 (θ z) hθb (n + m)
      have e1' := n1 (θ z) hθb m
      have e2 := n2 z hzb n
      have e3 := n3 z (hunit hzb) n
      have e4 := n4 z hzb
      have hid := hω n z
      simp only [D2, D1, Z3, E2] at e1 e1' e2 e3
      have hdiff : etaCV hW₂ (n + m) (θ z) ω - etaCV hW₂ m (θ z) ω -
          Zc (c * (1 / 2 : ℝ) ^ n) z ω ≤ 5 * t := by
        have a1 := (abs_lt.1 e1).1
        have a2 := (abs_lt.1 e1').2
        have a3 := (abs_lt.1 e2).2
        have a4 := (abs_lt.1 e3).1
        have a5 := (abs_lt.1 e4).1
        linarith
      have hv1 := htv (c * (1 / 2 : ℝ) ^ n) (hcn n) z
      have hv2 := etaVar_le (hcn n) ((hcn1 n).trans hc1) z
      have hv3 : Real.log ((2 : ℝ)⁻¹ ^ m / (2 : ℝ)⁻¹ ^ (n + m)) - Bv ≤
          etaBVar ((2 : ℝ)⁻¹ ^ m) (n + m) (θ z) :=
        hvar (θ z) (hθK hθz) ((2 : ℝ)⁻¹ ^ (n + m)) ((2 : ℝ)⁻¹ ^ m) (by positivity)
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left m n))
          (pow_le_one₀ (by norm_num) (by norm_num))
      have hlog : Real.log (c * (1 / 2 : ℝ) ^ n)⁻¹ =
          Lc + Real.log ((2 : ℝ)⁻¹ ^ m / (2 : ℝ)⁻¹ ^ (n + m)) := by
        have e : (c * (1 / 2 : ℝ) ^ n)⁻¹ = R * ((2 : ℝ)⁻¹ ^ m / (2 : ℝ)⁻¹ ^ (n + m)) := by
          rw [← hcR, hc, hs', pow_add, eh]
          field_simp
        rw [e, Real.log_mul hR0.ne' (by positivity)]
      have hvv : tildeVar (c * (1 / 2 : ℝ) ^ n) z - etaBVar ((2 : ℝ)⁻¹ ^ m) (n + m) (θ z) ≤
          Lc + Bv' := by
        rw [hBv']; linarith [hv1.2]
      have g1 := mul_le_mul_of_nonneg_left hdiff hγ.le
      have g2 := mul_le_mul_of_nonneg_left hvv (by positivity : (0 : ℝ) ≤ γ ^ 2 / 2)
      have h5t : γ * (5 * t) = lam := by rw [ht]; field_simp
      have hl0 : γ ^ 2 / 2 * Bv' ≤ lam := hl
      simp only [hF₂]
      nlinarith
    have hs := lgdRat_sim_upper h1 ha0 b hK hKV h₂ hpt δ x y
    have hth : ‖a‖ * δ * Real.exp lam * (‖a‖ * 2 ^ m) ^ (γ ^ 2 / 4) =
        ‖a‖ * δ * Real.exp ((2 * lam + γ ^ 2 / 2 * Lc) / 2) := by
      rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < ‖a‖ * 2 ^ m), mul_assoc (‖a‖ * δ),
        ← Real.exp_add, hLc, hR]
      congr 2; ring
    rw [hth]
    exact hs
  -- the union bound
  have hexp : ∀ c' d : ℝ, 0 < c' → c' ≤ M * R ^ 2 → 0 < d → d ≤ (M + 4) * (Lc + 1) →
      c' * Real.exp (-t ^ 2 / d) ≤ M * R ^ 2 * Real.exp (-lam ^ 2 / (C * (Lc + 1))) := by
    intro c' d hc' hc'M hd hdM
    refine mul_le_mul hc'M (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (by positivity)
    have hd25 : (5 * γ) ^ 2 * d ≤ C * (Lc + 1) := by
      have h1 := mul_le_mul_of_nonneg_left hdM (by positivity : (0 : ℝ) ≤ 25 * γ ^ 2)
      have h2 : 25 * γ ^ 2 * (M + 4) ≤ C := by
        have : 0 ≤ 4 * M + lam0 ^ 2 + 3 := by positivity
        rw [hC]; linarith
      have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ Lc + 1)
      have e : (5 * γ) ^ 2 * d = 25 * γ ^ 2 * d := by ring
      have e' : 25 * γ ^ 2 * ((M + 4) * (Lc + 1)) = 25 * γ ^ 2 * (M + 4) * (Lc + 1) := by ring
      linarith
    rw [ht, div_pow, neg_div, neg_div, neg_le_neg_iff, div_div]
    exact div_le_div_of_nonneg_left (sq_nonneg lam) (by positivity) hd25
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR1
  have hMR : M ≤ M * R ^ 2 := le_mul_of_one_le_right hM0.le hR2
  have hML : M ≤ (M + 4) * (Lc + 1) := by nlinarith
  have m1 : C28 ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have m2 : C8u ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have m3 : C7u ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have m4 : CD ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have f1 := hexp C28 C28 hC28 (m1.trans hMR) hC28 (m1.trans hML)
  have f2 := hexp C8u C8u hC8u (m2.trans hMR) hC8u (m2.trans hML)
  have f3 := hexp C7u C7u hC7u (m3.trans hMR) hC7u (m3.trans hML)
  have hc4e : 16 * R ^ 2 * (2 * Real.exp (8 * ferniqueCF ^ 2)) = CD * R ^ 2 := by
    rw [hCD]; ring
  have hc4 : 16 * R ^ 2 * (2 * Real.exp (8 * ferniqueCF ^ 2)) ≤ M * R ^ 2 := by
    rw [hc4e]; exact mul_le_mul_of_nonneg_right m4 (by positivity)
  have f4 := hexp (16 * R ^ 2 * (2 * Real.exp (8 * ferniqueCF ^ 2))) (4 * (Lc + 1))
    (by positivity) hc4 (by positivity)
    (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have h4M : 4 * M ≤ C := by
    have : 0 ≤ 25 * γ ^ 2 * (M + 4) + lam0 ^ 2 + 3 := by positivity
    rw [hC]; linarith
  have hU : P'.real (EA ∪ EB ∪ EC ∪ ED) ≤
      P'.real EA + P'.real EB + P'.real EC + P'.real ED := by
    have u1 := measureReal_union_le (μ := P') (EA ∪ EB ∪ EC) ED
    have u2 := measureReal_union_le (μ := P') (EA ∪ EB) EC
    have u3 := measureReal_union_le (μ := P') EA EB
    linarith
  calc _ ≤ P'.real (EA ∪ EB ∪ EC ∪ ED) :=
        ENNReal.toReal_mono (measure_ne_top P' _) (measure_mono_ae hsub)
    _ ≤ 4 * M * R ^ 2 * Real.exp (-lam ^ 2 / (C * (Lc + 1))) := by linarith
    _ ≤ C * R ^ 2 * Real.exp (-lam ^ 2 / (C * (Lc + 1))) := by
        gcongr

end DZZ
end LQGMetric
