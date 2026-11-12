/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20CGather at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CSplit

/-!
# DDDF Theorem 20, Step 4: gathering (5.66) and (5.67) (task P2-DDDFT20c)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1103–1155; see `T20CSplit.lean` for the plan.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

open T20C in
/-- **DDDF (5.65)+(5.66)** (`tightness.tex` l. 1103–1123), per visited block, with
`(1+η)`-near-geodesics. Open. -/
def T20Step4Num (ξ : ℝ) (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ d₁ : ℕ, ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n → ∃ s : ℝ,
    (∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s) ∧
    ∃ (J : Finset (Circle × ℂ)) (hJ : J.Nonempty), ((J.card : ℝ) ≤ C₁ * 4 ^ K) ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ γ : ℕ → Ω → ℝ → ℂ, T20.IsNearGeodSel ξ Q W P η γ →
      ∀ Y : ℂ → Ω → ℝ, (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ K)⁻¹ 1 x) →
        (∀ ω, ContDiff ℝ 1 fun x => Y x ω) →
        ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K, z ∈ visSet γ n K b s →
          ∃ P' ∈ T20.coarseBlocks K (γ n z.1),
            |((b.1 - P'.1 : ℤ) : ℝ)| ≤ C₁ * ((K : ℝ) + 1) ∧
            |((b.2 - P'.2 : ℤ) : ℝ)| ≤ C₁ * ((K : ℝ) + 1) ∧
            incr ξ Q W P K n b z ≤ η + C₁ * ((K : ℝ) + 1) ^ d₁ * Real.exp (C₁ * Xbig Q W P z.1) *
              Real.exp (C₁ * (K : ℝ) ^ Q.ε₀ * Obig K Y z.1) *
              Real.exp (ξ * psiMN Q W P 0 K (T20.dyCenter K P') z.1) *
              maxLong ξ W P K n J hJ z.1 / lenPsi ξ Q W P n z.1

open T20C in
/-- **DDDF (5.67)** (`tightness.tex` l. 1131–1146), with `(1+η)`-near-geodesics. Open. -/
def T20Step4Den (ξ : ℝ) (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n →
    ∃ (J' : Finset (Circle × ℂ)) (hJ' : J'.Nonempty), ((J'.card : ℝ) ≤ C₁ * 4 ^ K) ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ γ : ℕ → Ω → ℝ → ℂ, T20.IsNearGeodSel ξ Q W P η γ →
      ∀ Y : ℂ → Ω → ℝ, (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ K)⁻¹ 1 x) →
        (∀ ω, ContDiff ℝ 1 fun x => Y x ω) →
        ∀ᵐ ω ∂P, Real.exp (-(C₁ * Xbig Q W P ω)) * Real.exp (-(C₁ * (K : ℝ) ^ Q.ε₀ * Obig K Y ω)) *
          minShort ξ W P K n J' hJ' ω *
          ∑ P' ∈ T20.coarseBlocks K (γ n ω), Real.exp (ξ * psiMN Q W P 0 K (T20.dyCenter K P') ω) ≤
          C₁ * lenPsi ξ Q W P n ω

namespace T20C

lemma maxLong_nonneg (ξ : ℝ) (K n : ℕ) (J : Finset (Circle × ℂ)) (hJ : J.Nonempty) (ω : Ω) :
    0 ≤ maxLong ξ W P K n J hJ ω := by
  set g : Circle × ℂ → ℝ := fun j => T20B.mrectLen ξ (fun x => phiMN W P K n x ω) K j.1 j.2 3 1
  exact (ENNReal.toReal_nonneg).trans (Finset.le_sup' g hJ.choose_spec)

omit [MeasurableSpace Ω] in
lemma Obig_nonneg (K : ℕ) (Y : ℂ → Ω → ℝ) (ω : Ω) : 0 ≤ Obig K Y ω := by
  obtain ⟨c₁, hc₁⟩ := offs_nonempty
  exact (mul_nonneg (by positivity) (Real.iSup_nonneg fun _ => norm_nonneg _)).trans
    (Finset.le_sup' (fun c => ((2 : ℝ) ^ K)⁻¹ *
      ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y (x + c) ω) z‖) hc₁)

/-- the real algebra of the gathering step (DDDF l. 1150–1155) -/
lemma gather_real {ι : Type*} (V : Finset ι) {η A C₂ M H m S1 S2 Nn sq : ℝ} {inc T : ι → ℝ}
    (hA : 0 ≤ A) (hC₂ : 0 < C₂) (hM : 0 ≤ M) (hH : 0 < H) (hm : 0 < m)
    (hS1 : 0 < S1) (hinc : ∀ i ∈ V, 0 ≤ inc i ∧ inc i ≤ η + A * T i * M * C₂ / (H * m * S1))
    (hT : ∀ i, 0 ≤ T i) (hV : (V.card : ℝ) ≤ Nn) (hsq : ∑ i ∈ V, T i ^ 2 ≤ sq * S2) :
    ∑ i ∈ V, inc i ^ 2 ≤ 2 * η ^ 2 * Nn +
      2 * sq * (A * C₂ / H) ^ 2 * (M / m) ^ 2 * (S2 / S1 ^ 2) := by
  set Z : ℝ := A * M * C₂ / (H * m * S1) with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have hb : ∀ i ∈ V, inc i ^ 2 ≤ 2 * η ^ 2 + 2 * Z ^ 2 * T i ^ 2 := by
    intro i hi
    obtain ⟨h0, h1⟩ := hinc i hi
    have e : A * T i * M * C₂ / (H * m * S1) = Z * T i := by rw [hZ]; ring
    rw [e] at h1
    have hZT : 0 ≤ Z * T i := mul_nonneg hZ0 (hT i)
    nlinarith [sq_nonneg (η - Z * T i)]
  calc ∑ i ∈ V, inc i ^ 2 ≤ ∑ i ∈ V, (2 * η ^ 2 + 2 * Z ^ 2 * T i ^ 2) := Finset.sum_le_sum hb
    _ = 2 * η ^ 2 * V.card + 2 * Z ^ 2 * ∑ i ∈ V, T i ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]; ring
    _ ≤ 2 * η ^ 2 * Nn + 2 * Z ^ 2 * (sq * S2) := by
        gcongr
    _ = _ := by rw [hZ]; field_simp

lemma AH_eq (C₁ C₂ k X e O : ℝ) (d₁ : ℕ) :
    C₁ * (k + 1) ^ d₁ * Real.exp (C₁ * X) * Real.exp (C₁ * e * O) * C₂ /
      (Real.exp (-(C₂ * X)) * Real.exp (-(C₂ * e * O))) =
    C₁ * C₂ * (k + 1) ^ d₁ * Real.exp ((C₁ + C₂) * X) * Real.exp ((C₁ + C₂) * (e * O)) := by
  rw [div_eq_iff (by positivity)]
  have e1 : Real.exp ((C₁ + C₂) * X) * Real.exp (-(C₂ * X)) = Real.exp (C₁ * X) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp ((C₁ + C₂) * (e * O)) * Real.exp (-(C₂ * e * O)) =
      Real.exp (C₁ * e * O) := by
    rw [← Real.exp_add]; ring_nf
  rw [← e1, ← e2]; ring

/-- the constants of the gathering step -/
lemma final_gather {C₁ C₂ k X O e η F W0 : ℝ} (d₁ : ℕ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hk : 0 ≤ k) (hX : 0 ≤ X) (hO : 0 ≤ O) (he : 0 ≤ e) (hF : 0 ≤ F) (hW0 : 0 ≤ W0) (m₀ : ℕ)
    (hm₀ : (m₀ : ℝ) < C₁ * (k + 1) + 1) :
    2 * η ^ 2 * (16 * F) + 2 * ((2 * m₀ + 1 : ℕ) : ℝ) ^ 2 *
      (C₁ * C₂ * (k + 1) ^ d₁ * Real.exp ((C₁ + C₂) * X) * Real.exp ((C₁ + C₂) * (e * O))) ^ 2 *
      W0 ≤
    (32 + 2 * (C₁ + C₂) + C₁ + C₂ + 2 * (2 * C₁ + 3) ^ 2 * (C₁ * C₂) ^ 2) * F * η ^ 2 +
      (32 + 2 * (C₁ + C₂) + C₁ + C₂ + 2 * (2 * C₁ + 3) ^ 2 * (C₁ * C₂) ^ 2) * (k + 1) ^ (2 * d₁ + 2) *
      Real.exp ((32 + 2 * (C₁ + C₂) + C₁ + C₂ + 2 * (2 * C₁ + 3) ^ 2 * (C₁ * C₂) ^ 2) * X) *
      Real.exp ((32 + 2 * (C₁ + C₂) + C₁ + C₂ + 2 * (2 * C₁ + 3) ^ 2 * (C₁ * C₂) ^ 2) * e * O) *
      W0 := by
  set C₀ := 32 + 2 * (C₁ + C₂) + C₁ + C₂ + 2 * (2 * C₁ + 3) ^ 2 * (C₁ * C₂) ^ 2 with hC₀
  have hlast : 0 ≤ 2 * (2 * C₁ + 3) ^ 2 * (C₁ * C₂) ^ 2 := by positivity
  have hk1 : 1 ≤ k + 1 := by linarith
  set q : ℝ := ((2 * m₀ + 1 : ℕ) : ℝ)
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  have hq : q ≤ (2 * C₁ + 3) * (k + 1) := by
    simp only [q]; push_cast; nlinarith
  have hq2 : q ^ 2 ≤ (2 * C₁ + 3) ^ 2 * (k + 1) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hq0 hq 2
  have hE1 : Real.exp ((C₁ + C₂) * X) ^ 2 ≤ Real.exp (C₀ * X) := by
    rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.2 (by push_cast; nlinarith)
  have hE2 : Real.exp ((C₁ + C₂) * (e * O)) ^ 2 ≤ Real.exp (C₀ * e * O) := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have heO : 0 ≤ e * O := mul_nonneg he hO
    push_cast; nlinarith
  have h1 : 2 * η ^ 2 * (16 * F) ≤ C₀ * F * η ^ 2 := by
    have : 32 ≤ C₀ := by rw [hC₀]; linarith
    nlinarith [mul_nonneg hF (sq_nonneg η)]
  have h2 : 2 * q ^ 2 * (C₁ * C₂ * (k + 1) ^ d₁ * Real.exp ((C₁ + C₂) * X) *
      Real.exp ((C₁ + C₂) * (e * O))) ^ 2 * W0 ≤
      C₀ * (k + 1) ^ (2 * d₁ + 2) * Real.exp (C₀ * X) * Real.exp (C₀ * e * O) * W0 := by
    refine mul_le_mul_of_nonneg_right ?_ hW0
    have hc : 2 * (2 * C₁ + 3) ^ 2 * (C₁ * C₂) ^ 2 ≤ C₀ := by rw [hC₀]; linarith
    have hpk : 0 ≤ (k + 1) ^ (2 * d₁ + 2) := by positivity
    calc 2 * q ^ 2 * (C₁ * C₂ * (k + 1) ^ d₁ * Real.exp ((C₁ + C₂) * X) *
          Real.exp ((C₁ + C₂) * (e * O))) ^ 2
        = 2 * q ^ 2 * (C₁ * C₂) ^ 2 * ((k + 1) ^ d₁) ^ 2 * Real.exp ((C₁ + C₂) * X) ^ 2 *
          Real.exp ((C₁ + C₂) * (e * O)) ^ 2 := by ring
      _ ≤ 2 * ((2 * C₁ + 3) ^ 2 * (k + 1) ^ 2) * (C₁ * C₂) ^ 2 * ((k + 1) ^ d₁) ^ 2 *
          Real.exp (C₀ * X) * Real.exp (C₀ * e * O) := by gcongr
      _ = (2 * (2 * C₁ + 3) ^ 2 * (C₁ * C₂) ^ 2) * (k + 1) ^ (2 * d₁ + 2) *
          Real.exp (C₀ * X) * Real.exp (C₀ * e * O) := by ring
      _ ≤ C₀ * (k + 1) ^ (2 * d₁ + 2) * Real.exp (C₀ * X) * Real.exp (C₀ * e * O) := by gcongr
  linarith

end T20C

open T20C in
/-- **DDDF l. 1150–1155**: (5.66) and (5.67) give the pathwise bound `T20Step4Pathwise`. -/
theorem t20Step4Pathwise_of_num_den (hW : IsWhiteNoise P W) (Q : PsiParams) {ξ : ℝ}
    (hN : T20Step4Num ξ Q W P) (hD : T20Step4Den ξ Q W P) : T20Step4Pathwise ξ Q W P := by
  classical
  have := hW.isProbabilityMeasure
  obtain ⟨C₁, hC₁, d₁, K₁, hN⟩ := hN
  obtain ⟨C₂, hC₂, K₂, hD⟩ := hD
  set C₀ : ℝ := 32 + 2 * (C₁ + C₂) + C₁ + C₂ + 2 * (2 * C₁ + 3) ^ 2 * (C₁ * C₂) ^ 2 with hC₀
  refine ⟨C₀, by positivity, 2 * d₁ + 2, max K₁ K₂, fun K hK n hn => ?_⟩
  have hKn : K ≤ n := hn
  obtain ⟨s, hσ, J, hJ, hJc, hNK⟩ := hN K (le_of_max_le_left hK) n hn
  obtain ⟨J', hJ', hJ'c, hDK⟩ := hD K (le_of_max_le_right hK) n hn
  have h4K : (0 : ℝ) < 4 ^ K := by positivity
  have hlast : 0 ≤ 2 * (2 * C₁ + 3) ^ 2 * (C₁ * C₂) ^ 2 := by positivity
  have hcard : ((J.card : ℝ) + J'.card) ≤ C₀ * 4 ^ K := by
    have : (C₁ + C₂) * 4 ^ K ≤ C₀ * 4 ^ K :=
      mul_le_mul_of_nonneg_right (by rw [hC₀]; linarith) h4K.le
    linarith
  refine ⟨s, hσ, J, J', hJ, hJ', hcard, fun η hη hη1 γ hγ Y hY hYc => ?_⟩
  have hm : ∀ᵐ ω ∂P, 0 < minShort ξ W P K n J' hJ' ω := by
    have h := (Filter.eventually_all_finset J').2 fun j _ =>
      T20B.ae_mrectLen_pos (ξ := ξ) hW hKn j.1 j.2 (a := 1) (b := 3) one_pos (by norm_num)
    filter_upwards [h] with ω hω
    exact (Finset.lt_inf'_iff _).2 hω
  have hmp := measurePreserving_fst (μ := P) (ν := P)
  filter_upwards [hNK η hη hη1 γ hγ Y hY hYc,
    hmp.quasiMeasurePreserving.ae (hDK η hη hη1 γ hγ Y hY hYc),
    hmp.quasiMeasurePreserving.ae hm] with z hNz hDz hmz
  set V := (T20B.nearIdx K).filter (fun b => z ∈ visSet γ n K b s) with hV
  have hL : ∑ b ∈ T20B.nearIdx K, (visSet γ n K b s).indicator
      (fun z => ENNReal.ofReal (incr ξ Q W P K n b z ^ 2)) z =
      ENNReal.ofReal (∑ b ∈ V, incr ξ Q W P K n b z ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun b _ => sq_nonneg _), hV, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : z ∈ visSet γ n K b s
    · rw [indicator_of_mem h, if_pos h]
    · rw [indicator_of_notMem h, if_neg h]
  rw [hL]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
  set X := Xbig Q W P z.1 with hXd
  set O := Obig K Y z.1 with hOd
  set M := maxLong ξ W P K n J hJ z.1 with hMd
  set m := minShort ξ W P K n J' hJ' z.1 with hmd
  set L := lenPsi ξ Q W P n z.1 with hLd
  set R := T20.condTRatio ξ K (fun x => psiMN Q W P 0 K x z.1) (γ n z.1) with hRd
  set S := lsRatio ξ W P K n J J' hJ hJ' z.1 with hSd
  have hR0 : 0 ≤ R := condTRatio_nonneg _ _ _ _
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hO0 : 0 ≤ O := Obig_nonneg K Y z.1
  have hmain0 : 0 ≤ C₀ * ((K : ℝ) + 1) ^ (2 * d₁ + 2) * Real.exp (C₀ * X) *
      Real.exp (C₀ * (K : ℝ) ^ Q.ε₀ * O) * S ^ 2 * R := mul_nonneg (by positivity) hR0
  rcases V.eq_empty_or_nonempty with hVe | ⟨b₀, hb₀⟩
  · rw [hVe, Finset.sum_empty]; positivity
  have hspec : ∀ b ∈ V, ∃ P' ∈ T20.coarseBlocks K (γ n z.1),
      |((b.1 - P'.1 : ℤ) : ℝ)| ≤ C₁ * ((K : ℝ) + 1) ∧
      |((b.2 - P'.2 : ℤ) : ℝ)| ≤ C₁ * ((K : ℝ) + 1) ∧
      incr ξ Q W P K n b z ≤ η + C₁ * ((K : ℝ) + 1) ^ d₁ * Real.exp (C₁ * X) *
        Real.exp (C₁ * (K : ℝ) ^ Q.ε₀ * O) *
        Real.exp (ξ * psiMN Q W P 0 K (T20.dyCenter K P') z.1) * M / L :=
    fun b hb => hNz b (Finset.mem_filter.1 hb).1 (Finset.mem_filter.1 hb).2
  set g : ℤ × ℤ → ℤ × ℤ := fun b => if h : b ∈ V then Classical.choose (hspec b h) else 0
  have hg : ∀ b ∈ V, g b ∈ T20.coarseBlocks K (γ n z.1) ∧
      |((b.1 - (g b).1 : ℤ) : ℝ)| ≤ C₁ * ((K : ℝ) + 1) ∧
      |((b.2 - (g b).2 : ℤ) : ℝ)| ≤ C₁ * ((K : ℝ) + 1) ∧
      incr ξ Q W P K n b z ≤ η + C₁ * ((K : ℝ) + 1) ^ d₁ * Real.exp (C₁ * X) *
        Real.exp (C₁ * (K : ℝ) ^ Q.ε₀ * O) *
        Real.exp (ξ * psiMN Q W P 0 K (T20.dyCenter K (g b)) z.1) * M / L := by
    intro b hb
    have := Classical.choose_spec (hspec b hb)
    simp only [g, dif_pos hb]
    exact this
  set S1 := ∑ P' ∈ T20.coarseBlocks K (γ n z.1), Real.exp (ξ * psiMN Q W P 0 K (T20.dyCenter K P') z.1)
  set S2 := ∑ P' ∈ T20.coarseBlocks K (γ n z.1),
    Real.exp (2 * ξ * psiMN Q W P 0 K (T20.dyCenter K P') z.1)
  set A := C₁ * ((K : ℝ) + 1) ^ d₁ * Real.exp (C₁ * X) * Real.exp (C₁ * (K : ℝ) ^ Q.ε₀ * O)
  set H := Real.exp (-(C₂ * X)) * Real.exp (-(C₂ * (K : ℝ) ^ Q.ε₀ * O))
  have hS1 : 0 < S1 := Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨g b₀, (hg b₀ hb₀).1⟩
  have hH : 0 < H := by positivity
  have hM0 : 0 ≤ M := maxLong_nonneg ξ K n J hJ z.1
  have hden : H * m * S1 ≤ C₂ * L := hDz
  have hpos : 0 < H * m * S1 := by positivity
  have hL0 : 0 < L := by nlinarith
  set T : ℤ × ℤ → ℝ := fun b => Real.exp (ξ * psiMN Q W P 0 K (T20.dyCenter K (g b)) z.1)
  have hinc : ∀ b ∈ V, 0 ≤ incr ξ Q W P K n b z ∧
      incr ξ Q W P K n b z ≤ η + A * T b * M * C₂ / (H * m * S1) := by
    intro b hb
    refine ⟨le_max_right _ _, (hg b hb).2.2.2.trans ?_⟩
    have hnum : 0 ≤ A * T b * M := by positivity
    rw [add_le_add_iff_left, div_le_div_iff₀ hL0 hpos]
    nlinarith [mul_le_mul_of_nonneg_left hden hnum]
  set m₀ : ℕ := ⌈C₁ * ((K : ℝ) + 1)⌉₊
  have hsq : ∑ b ∈ V, T b ^ 2 ≤ ((2 * m₀ + 1 : ℕ) : ℝ) ^ 2 * S2 := by
    have e : ∀ b, T b ^ 2 = Real.exp (2 * ξ * psiMN Q W P 0 K (T20.dyCenter K (g b)) z.1) :=
      fun b => by rw [sq, ← Real.exp_add]; ring_nf
    simp_rw [e]
    exact sum_fiber_le g (fun b hb => (hg b hb).1) m₀
      (fun b hb => ⟨(hg b hb).2.1.trans (Nat.le_ceil _), (hg b hb).2.2.1.trans (Nat.le_ceil _)⟩)
      (fun j => Real.exp (2 * ξ * psiMN Q W P 0 K (T20.dyCenter K j) z.1))
      fun j => (Real.exp_pos _).le
  have hVc : (V.card : ℝ) ≤ 16 * 4 ^ K :=
    (Nat.cast_le.2 (Finset.card_le_card (Finset.filter_subset _ _))).trans (card_nearIdx_le K)
  have hG := gather_real V (inc := fun b => incr ξ Q W P K n b z) (T := T) (A := A) (C₂ := C₂)
    (M := M) (H := H) (m := m) (S1 := S1) (S2 := S2) (η := η) (by positivity) hC₂ hM0 hH hmz hS1
    hinc (fun b => (Real.exp_pos _).le) hVc hsq
  -- the constants
  have hAH : A * C₂ / H = C₁ * C₂ * ((K : ℝ) + 1) ^ d₁ * Real.exp ((C₁ + C₂) * X) *
      Real.exp ((C₁ + C₂) * ((K : ℝ) ^ Q.ε₀ * O)) := AH_eq C₁ C₂ K X ((K : ℝ) ^ Q.ε₀) O d₁
  have hSe : S = M / m := rfl
  have hRe : R = S2 / S1 ^ 2 := rfl
  have hS2 : 0 ≤ S2 := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have hKe : (0 : ℝ) ≤ (K : ℝ) ^ Q.ε₀ := Real.rpow_nonneg (Nat.cast_nonneg K) _
  have hK0 : (0 : ℝ) ≤ C₁ * ((K : ℝ) + 1) :=
    mul_nonneg hC₁.le (add_nonneg (Nat.cast_nonneg K) zero_le_one)
  have hfin := final_gather (η := η) (X := X) (O := O) (e := (K : ℝ) ^ Q.ε₀) (F := 4 ^ K)
    (W0 := (M / m) ^ 2 * (S2 / S1 ^ 2)) d₁ hC₁ hC₂ (Nat.cast_nonneg K) hX0 hO0 hKe h4K.le
    (mul_nonneg (sq_nonneg _) (div_nonneg hS2 (sq_nonneg _))) m₀ (Nat.ceil_lt_add_one hK0)
  rw [hSe, hRe]
  refine hG.trans (le_of_eq_of_le ?_ (hfin.trans (le_of_eq ?_)))
  · rw [hAH]; ring
  · rw [hC₀]; ring

/-- **DDDF Step 4, visited blocks**, from (5.66), (5.67) and Condition (T). -/
theorem dddf_t20_step4_visited_of_num_den (hW : IsWhiteNoise P W) (Q : PsiParams)
    (hε : Q.ε₀ < 1 / 2) {ξ : ℝ} (hξ : 0 < ξ) (hT : ConditionT ξ Q W P)
    (hN : T20Step4Num ξ Q W P) (hD : T20Step4Den ξ Q W P) : T20Step4Visited ξ Q W P :=
  dddf_t20_step4_visited_of_pathwise hW Q hε hξ hT (t20Step4Pathwise_of_num_den hW Q hN hD)

/-- **DDDF Theorem 20** (`thm:AssTthm`, `tightness.tex` l. 1070–1213) from Condition (T) and the
two pathwise estimates (5.66), (5.67) of Step 4: `Λ_∞(φ,p) < ∞`, `sup_n Var log L^{(n)}(ψ) < ∞`,
and tightness of `log L^{(n)}_{1,1} − log λ_n`. -/
theorem dddf_thm20_of_num_den (hW : IsWhiteNoise P W) (Q : PsiParams) (hQ : PsiSmall Q)
    (hε : Q.ε₀ < 1 / 2) {ξ : ℝ} (hξ : 0 < ξ) (hT : ConditionT ξ Q W P)
    (hN : T20Step4Num ξ Q W P) (hD : T20Step4Den ξ Q W P) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      (∃ B : ℝ, ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B) ∧
      (∃ B : ℝ, ∀ n, Var[L24.logLenPsi ξ Q W P n; P] ≤ B) ∧
      ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ n : ℕ,
        P {ω | M < |Real.log (lenN ξ W P 1 1 n ω) - Real.log (lambdaN ξ W P n)|} ≤
          ENNReal.ofReal ε :=
  dddf_thm20_of_step4Visited hW Q hQ hξ (dddf_t20_step4_visited_of_num_den hW Q hε hξ hT hN hD)

end DDDF
end LQGMetric
