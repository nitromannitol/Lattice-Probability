/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20BStep4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BRec
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.D5T

/-!
# DDDF Theorem 20, Step 4: blocks not visited by the near-geodesic (task P2-DDDFT20b)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1093–1095: "For `P ∈ 𝒫_K`, if `L^P_n(ψ) > L_n(ψ)`,
the block `P` is visited by the geodesic `π_n(ψ)`" — more precisely the resampled field
`ψ_{0,n} − ψ_{K,n,P} + ψ̃_{K,n,P}` coincides with `ψ_{0,n}` outside the range of dependence of
`ψ_{K,n,P}` ("thanks to the truncation, the fields have finite correlation length", l. 358).
With `(1+η)`-near-geodesics (D-DDDF-5) the statement becomes: if the near-geodesic avoids the
`2s`-neighbourhood of the block (`s ≥ σ_t` on the time range), then
`(log L^P − log L)_+ ≤ log(1+η)` (`dddf_t20_step4_far`).

* `T20B.blockKernel_eq_zero_far`, `T20B.blkVer_eq_zero_far`: a.s. the continuous block field
  vanishes on the whole far set `farSet B s = {x : ∀ y ∈ B, 2s ≤ |x − y|}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

namespace T20B

/-- the points at distance `≥ 2s` from `B` -/
def farSet (B : Set ℂ) (s : ℝ) : Set ℂ := {x | ∀ y ∈ B, 2 * s ≤ ‖x - y‖}

lemma blockKernel_eq_zero_far (Q : PsiParams) {a b s : ℝ} (ha : 0 < a)
    (hσ : ∀ t ∈ Icc (a ^ 2) (b ^ 2), Q.sigma t ≤ s) {B : Set ℂ} {x : ℂ} (hx : x ∈ farSet B s)
    (p : ℝ × ℂ) : Q.blockKernel a b B x p = 0 := by
  unfold PsiParams.blockKernel
  by_cases hB : p.2 ∈ B
  · by_cases ht : p ∈ Icc (a ^ 2) (b ^ 2) ×ˢ (univ : Set ℂ)
    · have ht0 : 0 < p.1 := lt_of_lt_of_le (by positivity) (mem_prod.mp ht).1.1
      rw [Q.psiKernel_eq_zero_of_far a b x ht0 ((mul_le_mul_of_nonneg_left
        (hσ _ (mem_prod.mp ht).1) (by norm_num)).trans (hx _ hB)), zero_mul]
    · simp [PsiParams.psiKernel, phiKernel, indicator_of_notMem ht]
  · simp [indicator, hB]

/-- a.s. the continuous block field vanishes on the far set (finite range) -/
theorem blkVer_eq_zero_far (hW : IsWhiteNoise P W) (Q : PsiParams) {a b s : ℝ} (ha : 0 < a)
    (hab : a ≤ b) {B : Set ℂ} (hB : MeasurableSet B)
    (hσ : ∀ t ∈ Icc (a ^ 2) (b ^ 2), Q.sigma t ≤ s) :
    ∀ᵐ ω ∂P, ∀ x ∈ farSet B s, blkVer Q W P a b B x ω = 0 := by
  have hS := blkVer_spec hW Q ha hab hB
  have hW0 : (fun ω => W 0 ω) =ᵐ[P] 0 := by
    have h := hW.ae_eq_zero_of_norm_eq_zero (ι := Unit) (fun _ => 0) (fun _ => 1) (by simp)
    filter_upwards [h] with ω hω
    simpa using hω
  have hpt : ∀ x ∈ farSet B s, (fun ω => blkVer Q W P a b B x ω) =ᵐ[P] 0 := by
    intro x hx
    have hL : Q.blockKernelL2 a b B x = 0 := by
      refine Lp.ext ?_
      filter_upwards [Q.coeFn_blockKernelL2 a b ha hB x,
        Lp.coeFn_zero ℝ 2 (volume : Measure (ℝ × ℂ))] with p h1 h2
      rw [h1, h2, blockKernel_eq_zero_far Q ha hσ hx p]; rfl
    filter_upwards [hS.2.2 x, hW0] with ω h1 h2
    rw [h1]
    simp only [psiBlock, hL, Pi.zero_apply]
    rw [show W 0 ω = 0 from h2, mul_zero]
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (farSet B s)
  have := hDc.to_subtype
  have hD : ∀ᵐ ω ∂P, ∀ d : D, blkVer Q W P a b B (d : farSet B s) ω = 0 :=
    ae_all_iff.2 fun d => hpt _ (d : farSet B s).2
  filter_upwards [hD] with ω hω x hx
  have h := Continuous.ext_on hDd (((hS.1 ω).comp continuous_subtype_val))
    (continuous_const (y := (0 : ℝ))) fun y hy => hω ⟨y, hy⟩
  exact congrFun h ⟨x, hx⟩

lemma lfppLen_congr_path {ξ : ℝ} {f g : ℂ → ℝ} {γ : ℝ → ℂ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, f (γ t) = g (γ t)) : lfppLen ξ f γ = lfppLen ξ g γ := by
  unfold lfppLen
  exact setLIntegral_congr_fun measurableSet_Icc fun t ht => by rw [h t ht]

end T20B

open T20B in
/-- **DDDF Step 4, unvisited blocks** (`tightness.tex` l. 1093–1095, with `(1+η)`-near-geodesics):
a.s. on `Ω × Ω`, if the near-geodesic `γ_n(ω)` stays at distance `≥ 2s` from the block `b`
(`s ≥ σ_t` for `t ∈ [2^{-2n}, 2^{-2K}]`), then resampling `ψ_{K,n,b}` raises `log L^{(n)}_{1,1}`
by at most `log(1+η)`. -/
theorem dddf_t20_step4_far (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ) {K n : ℕ}
    (hKn : K ≤ n) {s : ℝ}
    (hσ : ∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s)
    (b : ℤ × ℤ) {η : ℝ} (hη : 0 ≤ η) {γ : ℕ → Ω → ℝ → ℂ}
    (hγ : T20.IsNearGeodSel ξ Q W P η γ) :
    ∀ᵐ z ∂(P.prod P), (∀ t ∈ Icc (0 : ℝ) 1, γ n z.1 t ∈ farSet (hoBlock K b) s) →
      max (L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1 - blkKn Q W P K n b x z.1 +
          blkKn Q W P K n b x z.2) - L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1)) 0 ≤
        Real.log (1 + η) := by
  have := hW.isProbabilityMeasure
  have h0n := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  have hB := blkKn_spec hW Q hKn b
  have hfar := blkVer_eq_zero_far (P := P) hW Q (s := s) (by positivity)
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hKn) (measurableSet_hoBlock K b) hσ
  have h1 := (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving.ae hfar
  have h2 := (measurePreserving_snd (μ := P) (ν := P)).quasiMeasurePreserving.ae hfar
  filter_upwards [h1, h2] with z hz1 hz2 hav
  set f : ℂ → ℝ := fun x => psiMN Q W P 0 n x z.1
  set g : ℂ → ℝ := fun x => psiMN Q W P 0 n x z.1 - blkKn Q W P K n b x z.1 +
    blkKn Q W P K n b x z.2
  have hfc : Continuous f := h0n.cont z.1
  have hgc : Continuous g := ((h0n.cont z.1).sub (hB.1 z.1)).add (hB.1 z.2)
  have hpath : ∀ t ∈ Icc (0 : ℝ) 1, g (γ n z.1 t) = f (γ n z.1 t) := fun t ht => by
    have e1 : blkKn Q W P K n b (γ n z.1 t) z.1 = 0 := hz1 _ (hav t ht)
    have e2 : blkKn Q W P K n b (γ n z.1 t) z.2 = 0 := hz2 _ (hav t ht)
    simp only [g, f, e1, e2]; ring
  have hle : rectLen ξ g (rectAB 1 1) ≤
      ENNReal.ofReal (1 + η) * rectLen ξ f (rectAB 1 1) := by
    calc rectLen ξ g (rectAB 1 1) ≤ lfppLen ξ g (γ n z.1) := crossLenIn_le_lfppLen (hγ.adm n z.1)
      _ = lfppLen ξ f (γ n z.1) := lfppLen_congr_path hpath
      _ ≤ _ := hγ.near n z.1
  have hw : (0 : ℝ) ≤ (rectAB 1 1).w := by simp [rectAB]
  have hh : (0 : ℝ) ≤ (rectAB 1 1).h := by simp [rectAB]
  have hcw : (0 : ℝ) < (rectAB 1 1).crossWidth := by simp [rectAB, MarkedRect.crossWidth]
  have hfin := rectLen_ne_top (ξ := ξ) _ hw hh hfc
  have hgin := rectLen_ne_top (ξ := ξ) _ hw hh hgc
  have hLf : 0 < (rectLen ξ f (rectAB 1 1)).toReal :=
    ENNReal.toReal_pos (rectLen_pos _ hcw hfc).ne' hfin
  have hLg : 0 < (rectLen ξ g (rectAB 1 1)).toReal :=
    ENNReal.toReal_pos (rectLen_pos _ hcw hgc).ne' hgin
  have hle' : (rectLen ξ g (rectAB 1 1)).toReal ≤ (1 + η) * (rectLen ξ f (rectAB 1 1)).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
  have hlog0 : 0 ≤ Real.log (1 + η) := Real.log_nonneg (by linarith)
  refine max_le ?_ hlog0
  simp only [L23.logLen]
  rw [sub_le_iff_le_add, ← Real.log_mul (by linarith) hLf.ne']
  exact Real.log_le_log hLg (by linarith)

open T20B in
/-- **DDDF Step 4, visited blocks** (`tightness.tex` l. 1093–1177): the open part of Step 4.
For `p` small there are `C₂ > 0`, `K₀` such that for `K ≥ K₀`, `n ≥ K` there is a range bound
`s ≥ σ_t` on `[4^{-n}, 4^{-K}]` (DDDF: `s = C K^{ε₀} 2^{-K}`, l. 1097) such that for all small
`η > 0` some `(1+η)`-near-geodesic selection `γ` satisfies
`Σ_{b} E[(log L(ψ^b_{0,n}) − log L(ψ_{0,n}))_+² ; γ_n comes within 2s of b] ≤ e^{-C₂K} Λ_{n−K}(ψ,p/2)²`. -/
def T20Step4Visited (ξ : ℝ) (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ K₀ : ℕ,
    ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n → ∃ s : ℝ,
      (∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s) ∧
      ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∃ γ : ℕ → Ω → ℝ → ℂ,
        T20.IsNearGeodSel ξ Q W P η γ ∧
        ∑ b ∈ nearIdx K, ∫⁻ z, {z : Ω × Ω | ∃ t ∈ Icc (0 : ℝ) 1,
            γ n z.1 t ∉ farSet (hoBlock K b) s}.indicator (fun z => ENNReal.ofReal
          (max (L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1 - blkKn Q W P K n b x z.1 +
            blkKn Q W P K n b x z.2) - L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1)) 0 ^ 2)) z
          ∂(P.prod P) ≤
          ENNReal.ofReal (Real.exp (-(C₂ * K)) *
            LambdaNPsi ξ Q W P (n - K) (ENNReal.ofReal (p / 2)) ^ 2)

namespace T20B

lemma integral_le_toReal_lintegral {μ : Measure (Ω × Ω)} {f : Ω × Ω → ℝ} (hf : ∀ z, 0 ≤ f z) :
    ∫ z, f z ∂μ ≤ (∫⁻ z, ENNReal.ofReal (f z) ∂μ).toReal := by
  by_cases h : AEStronglyMeasurable f μ
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf) h]
  · rw [integral_non_aestronglyMeasurable h]; exact ENNReal.toReal_nonneg

end T20B

open T20B in
/-- **Step 4 reduced to the visited blocks**: blocks whose dependence range the near-geodesic
avoids contribute at most `log(1+η)²` each (`dddf_t20_step4_far`); there are `|nearIdx K|` of
them, and `η → 0`. -/
theorem dddf_t20_step4_of_visited (hW : IsWhiteNoise P W) (Q : PsiParams) {ξ : ℝ}
    (hV : T20Step4Visited ξ Q W P) : T20Step4 ξ Q W P := by
  have := hW.isProbabilityMeasure
  obtain ⟨p₀, hp₀, h⟩ := hV
  refine ⟨p₀, hp₀, fun p hp hpp => ?_⟩
  obtain ⟨C₂, hC₂, K₀, hK⟩ := h p hp hpp
  refine ⟨C₂, hC₂, K₀, fun K hK0 n hn => ?_⟩
  obtain ⟨s, hσ, η₀, hη₀, hη⟩ := hK K hK0 n hn
  set N : ℝ := ((nearIdx K).card : ℝ)
  set B : ℝ := Real.exp (-(C₂ * K)) * LambdaNPsi ξ Q W P (n - K) (ENNReal.ofReal (p / 2)) ^ 2
  have hB0 : 0 ≤ B := by positivity
  set f : ℤ × ℤ → Ω × Ω → ℝ := fun b z => max (L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1 -
    blkKn Q W P K n b x z.1 + blkKn Q W P K n b x z.2) -
      L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1)) 0 ^ 2
  have hf0 : ∀ b z, 0 ≤ f b z := fun b z => sq_nonneg _
  -- for every admissible `η`
  have key : ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∑ b ∈ nearIdx K, ∫ z, f b z ∂(P.prod P) ≤ B + N * Real.log (1 + η) ^ 2 := by
    intro η hη0 hηη
    obtain ⟨γ, hγ, hsum⟩ := hη η hη0 hηη
    have hl0 : 0 ≤ Real.log (1 + η) := Real.log_nonneg (by linarith)
    have hb : ∀ b ∈ nearIdx K, ∫⁻ z, ENNReal.ofReal (f b z) ∂(P.prod P) ≤
        ∫⁻ z, {z : Ω × Ω | ∃ t ∈ Icc (0 : ℝ) 1, γ n z.1 t ∉ farSet (hoBlock K b) s}.indicator
          (fun z => ENNReal.ofReal (f b z)) z ∂(P.prod P) +
          ENNReal.ofReal (Real.log (1 + η) ^ 2) := by
      intro b _
      have hc : ENNReal.ofReal (Real.log (1 + η) ^ 2) =
          ∫⁻ _z, ENNReal.ofReal (Real.log (1 + η) ^ 2) ∂(P.prod P) := by
        rw [lintegral_const, measure_univ, mul_one]
      rw [hc, ← lintegral_add_right _ measurable_const]
      refine lintegral_mono_ae ?_
      filter_upwards [dddf_t20_step4_far hW Q ξ hn hσ b hη0.le hγ] with z hz
      by_cases hv : z ∈ {z : Ω × Ω | ∃ t ∈ Icc (0 : ℝ) 1, γ n z.1 t ∉ farSet (hoBlock K b) s}
      · rw [indicator_of_mem hv]; exact le_self_add
      · rw [indicator_of_notMem hv, zero_add]
        simp only [mem_ofPred_eq, not_exists, not_and, not_not] at hv
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := hz hv
        have h2 : 0 ≤ max (L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1 -
          blkKn Q W P K n b x z.1 + blkKn Q W P K n b x z.2) -
            L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1)) 0 := le_max_right _ _
        exact pow_le_pow_left₀ h2 h1 2
    have hfin : ∑ b ∈ nearIdx K, ∫⁻ z, ENNReal.ofReal (f b z) ∂(P.prod P) ≤
        ENNReal.ofReal B + ENNReal.ofReal (N * Real.log (1 + η) ^ 2) := by
      calc _ ≤ ∑ b ∈ nearIdx K, (∫⁻ z, {z : Ω × Ω | ∃ t ∈ Icc (0 : ℝ) 1,
              γ n z.1 t ∉ farSet (hoBlock K b) s}.indicator
              (fun z => ENNReal.ofReal (f b z)) z ∂(P.prod P) +
              ENNReal.ofReal (Real.log (1 + η) ^ 2)) := Finset.sum_le_sum hb
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
          congr 1
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        _ ≤ _ := add_le_add_left hsum _
    have hne : ENNReal.ofReal B + ENNReal.ofReal (N * Real.log (1 + η) ^ 2) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
    calc ∑ b ∈ nearIdx K, ∫ z, f b z ∂(P.prod P)
        ≤ ∑ b ∈ nearIdx K, (∫⁻ z, ENNReal.ofReal (f b z) ∂(P.prod P)).toReal :=
          Finset.sum_le_sum fun b _ => integral_le_toReal_lintegral (hf0 b)
      _ = (∑ b ∈ nearIdx K, ∫⁻ z, ENNReal.ofReal (f b z) ∂(P.prod P)).toReal := by
          rw [ENNReal.toReal_sum fun b _ => ne_top_of_le_ne_top hne
            ((Finset.single_le_sum (f := fun b => ∫⁻ z, ENNReal.ofReal (f b z) ∂(P.prod P))
              (fun _ _ => bot_le) ‹_›).trans hfin)]
      _ ≤ (ENNReal.ofReal B + ENNReal.ofReal (N * Real.log (1 + η) ^ 2)).toReal :=
          ENNReal.toReal_mono hne hfin
      _ = B + N * Real.log (1 + η) ^ 2 := by
          rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
            ENNReal.toReal_ofReal hB0, ENNReal.toReal_ofReal (by positivity)]
  -- `η → 0`
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set η : ℝ := min η₀ (min 1 (ε / (N + 1)))
  have hη0 : 0 < η := lt_min hη₀ (lt_min one_pos (by positivity))
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hηε : η ≤ ε / (N + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hl : Real.log (1 + η) ≤ η := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + η by linarith); linarith
  have hl0 : 0 ≤ Real.log (1 + η) := Real.log_nonneg (by linarith)
  have hsq : Real.log (1 + η) ^ 2 ≤ η := by nlinarith
  have hNe : N * η < ε := by
    have h1 : N * η ≤ N * (ε / (N + 1)) := mul_le_mul_of_nonneg_left hηε hN
    have h2 : N * (ε / (N + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
    linarith
  calc _ ≤ B + N * Real.log (1 + η) ^ 2 := key η hη0 (min_le_left _ _)
    _ < B + ε := by nlinarith [mul_le_mul_of_nonneg_left hsq hN]

end DDDF
end LQGMetric
