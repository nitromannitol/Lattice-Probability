/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20EMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20EGeo
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DSigma
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DNum
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DDen

/-!
# DDDF Theorem 20, Step 4: the circuit gluing `T20CircuitGlue` (task P2-DDDFT20e)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1097–1123 ((5.65)–(5.66)): for a block `b` visited by
the near-geodesic (within `2s` of it, `s ≥ σ_t` on `[4^{-n}, 4^{-K}]`), the resampled length is at
most `(1+η) L_n(ψ) + Σ_{j ∈ R} L^{(n)}(R_j, ψ)` for the `O(K^{ε₀})` long rectangles of the
clipped circuit (D-DDDF-22) around the box of `m = ⌈2 s 2^K⌉` blocks around `b`.

* `dddf_t20_circuit_glue`: `T20CircuitGlue` for `ε₀ ≤ 1` (the index distance `≤ C(K+1)` between
  `b` and the visited block `P'` requires `K^{ε₀} ≤ C(K+1)`; DDDF Theorem 20 has `ε₀ < 1/2`).
  `s = r₀(1+2ε₀)^{ε₀}(1 + K log 4)^{ε₀} 2^{-K}` (`T20D.sigma_le_range`), the resampled block
  field vanishes off the `2s`-neighbourhood (`T20B.blkVer_eq_zero_far`), and the pathwise bound is
  `T20E.glue_rect`.
* `dddf_thm20_glued`: DDDF Theorem 20 (`dddf_thm20_of_glue`) from Condition (T) and `ε₀ < 1/2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise SupTail LFPP T20E

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DDDF (5.65)–(5.66): the circuit gluing** (`tightness.tex` l. 1097–1123, D-DDDF-22). -/
theorem dddf_t20_circuit_glue (hW : IsWhiteNoise P W) (Q : PsiParams) (hε : Q.ε₀ ≤ 1)
    {ξ : ℝ} : T20CircuitGlue ξ Q W P := by
  classical
  have := hW.isProbabilityMeasure
  have hε0 := Q.ε₀_pos
  set A : ℝ := Q.r₀ * (1 + 2 * Q.ε₀) ^ Q.ε₀ * 4 ^ Q.ε₀ with hA
  have hA0 : 0 < A := by have := Q.r₀_pos; positivity
  obtain ⟨K₁, hK₁⟩ := exists_lin_le_two_pow (4 * A) 9
  set C₁ : ℝ := 40 * A + 100
  have hC₁ : 0 < C₁ := by positivity
  refine ⟨C₁, hC₁, 1, max K₁ 2, fun K hK n hKn => ?_⟩
  have hK2 : 2 ≤ K := le_of_max_le_right hK
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  set h : ℝ := (2 : ℝ)⁻¹ ^ K
  have hp : 0 < h := by positivity
  have e1 : (2 : ℝ) ^ K * h = 1 := by simp only [h]; rw [← mul_pow]; norm_num
  set S : ℝ := Q.r₀ * (1 + 2 * Q.ε₀) ^ Q.ε₀ * (1 + K * Real.log 4) ^ Q.ε₀
  set s : ℝ := S * h
  -- `S ≤ A K^{ε₀} ≤ A K`
  have hlog : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
  have hKe1 : (1 : ℝ) ≤ (K : ℝ) ^ Q.ε₀ := Real.one_le_rpow hKr hε0.le
  have hKeK : (K : ℝ) ^ Q.ε₀ ≤ K := Real.rpow_le_self_of_one_le hKr hε
  have hS : S ≤ A * (K : ℝ) ^ Q.ε₀ := by
    have h1 : (1 + K * Real.log 4) ^ Q.ε₀ ≤ (4 * K) ^ Q.ε₀ :=
      Real.rpow_le_rpow (by positivity) (by
        have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ K); linarith) hε0.le
    rw [Real.mul_rpow (by norm_num) (by positivity)] at h1
    have := Q.r₀_pos
    simp only [S, hA]
    have h2 : 0 ≤ Q.r₀ * (1 + 2 * Q.ε₀) ^ Q.ε₀ := by positivity
    calc Q.r₀ * (1 + 2 * Q.ε₀) ^ Q.ε₀ * (1 + K * Real.log 4) ^ Q.ε₀
        ≤ Q.r₀ * (1 + 2 * Q.ε₀) ^ Q.ε₀ * (4 ^ Q.ε₀ * (K : ℝ) ^ Q.ε₀) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = _ := by ring
  have hS0 : 0 ≤ S := by have := Q.r₀_pos; positivity
  set m : ℕ := ⌈2 * S⌉₊
  have hm1 : 2 * S ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) < 2 * S + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmK : (m : ℝ) ≤ 2 * A * (K : ℝ) ^ Q.ε₀ + 1 := by linarith
  have hAKe : 0 ≤ A * (K : ℝ) ^ Q.ε₀ := by positivity
  have hAK : 0 ≤ A * (K : ℝ) := by positivity
  have hmK' : (m : ℝ) ≤ 2 * A * K + 1 := by
    have := mul_le_mul_of_nonneg_left hKeK (by positivity : (0 : ℝ) ≤ 2 * A); linarith
  have h2K : (2 * m + 7 : ℝ) ≤ 2 ^ K := by
    have := hK₁ K (le_of_max_le_left hK); linarith
  have hsm : 2 * s * 2 ^ K ≤ m := by
    simp only [s]; rw [mul_assoc, mul_assoc, mul_comm h, e1, mul_one]; exact hm1
  refine ⟨s, fun t ht => ?_, fun η hη hη1 γ hγ => ?_⟩
  · exact T20D.sigma_le_range Q K (lt_of_lt_of_le (by positivity) ht.1) ht.2
  -- the resampled block fields vanish off the `2s`-neighbourhood, for all blocks
  have hσ : ∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s := fun t ht =>
    T20D.sigma_le_range Q K (lt_of_lt_of_le (by positivity) ht.1) ht.2
  have hzero : ∀ᵐ ω ∂P, ∀ b ∈ T20B.nearIdx K, ∀ x ∈ T20B.farSet (T20B.hoBlock K b) s,
      T20B.blkKn Q W P K n b x ω = 0 := by
    rw [eventually_all_finset]
    intro b _
    exact T20B.blkVer_eq_zero_far hW Q (by positivity)
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hKn) (T20B.measurableSet_hoBlock K b) hσ
  have h1 := (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving.ae hzero
  have h2 := (measurePreserving_snd (μ := P) (ν := P)).quasiMeasurePreserving.ae hzero
  filter_upwards [h1, h2] with z hz1 hz2 b hb hvis
  obtain ⟨t, ht, hnf⟩ := hvis
  simp only [T20B.farSet, mem_setOf_eq, not_forall, not_le] at hnf
  obtain ⟨y, hy, hxy⟩ := hnf
  set x := γ n z.1 t
  obtain ⟨_, _, _, _, _, hγU⟩ := hγ.adm n z.1
  have hxsq := mem_sq.1 (hγU t ht)
  -- the floors
  have hp2 : (0 : ℝ) < 2 ^ K := by positivity
  have hre : |x.re * 2 ^ K - y.re * 2 ^ K| < m := by
    rw [← sub_mul, abs_mul, abs_of_pos hp2]
    have := Complex.abs_re_le_norm (x - y)
    rw [Complex.sub_re] at this
    have := mul_lt_mul_of_pos_right (this.trans_lt hxy) hp2
    linarith
  have him : |x.im * 2 ^ K - y.im * 2 ^ K| < m := by
    rw [← sub_mul, abs_mul, abs_of_pos hp2]
    have := Complex.abs_im_le_norm (x - y)
    rw [Complex.sub_im] at this
    have := mul_lt_mul_of_pos_right (this.trans_lt hxy) hp2
    linarith
  have q1 : 0 ≤ x.re * 2 ^ K := mul_nonneg hxsq.1.1 hp2.le
  have q2 : x.re * 2 ^ K ≤ 2 ^ K := by
    have := mul_le_mul_of_nonneg_right hxsq.1.2 hp2.le; linarith
  have q3 : 0 ≤ x.im * 2 ^ K := mul_nonneg hxsq.2.1 hp2.le
  have q4 : x.im * 2 ^ K ≤ 2 ^ K := by
    have := mul_le_mul_of_nonneg_right hxsq.2.2 hp2.le; linarith
  obtain ⟨fa1, fa2, fa3, fa4⟩ := floor_facts (N := 2 ^ K) q1 q2 hy.1 hre
  obtain ⟨fb1, fb2, fb3, fb4⟩ := floor_facts (N := 2 ^ K) q3 q4 hy.2 him
  have h2K' : (2 * m + 7 : ℤ) ≤ 2 ^ K := by exact_mod_cast h2K
  have hbx : BoxOK K (b.1 - m) (b.1 + 1 + m) := ⟨by omega, by omega,
    by have : ((b.1 - m : ℤ) : ℝ) < ((2 ^ K : ℤ) : ℝ) := by push_cast; linarith
       exact_mod_cast this.le, by omega⟩
  have hby : BoxOK K (b.2 - m) (b.2 + 1 + m) := ⟨by omega, by omega,
    by have : ((b.2 - m : ℤ) : ℝ) < ((2 ^ K : ℤ) : ℝ) := by push_cast; linarith
       exact_mod_cast this.le, by omega⟩
  set P' : ℤ × ℤ := (⌊x.re * 2 ^ K⌋, ⌊x.im * 2 ^ K⌋)
  obtain ⟨g1, g2, g3, g4⟩ := floor_block K hxsq.1.1 hxsq.1.2
  obtain ⟨g5, g6, g7, g8⟩ := floor_block K hxsq.2.1 hxsq.2.2
  have hP' : P' ∈ T20.coarseBlocks K (γ n z.1) := by
    simp only [T20.coarseBlocks, Finset.mem_filter, T20.blkIdx, Finset.mem_product,
      Finset.mem_Icc]
    refine ⟨⟨⟨g1, g2⟩, g5, g6⟩, t, ht, ?_⟩
    simp only [T20.dyBlock, Complex.mem_reProdIm, mem_Icc]
    exact ⟨⟨g3, g4⟩, g7, g8⟩
  have hC1e : C₁ * ((K : ℝ) + 1) = 40 * (A * K) + 40 * A + 100 * K + 100 := by
    simp only [C₁]; ring
  have hmC : (m : ℝ) ≤ C₁ * ((K : ℝ) + 1) := by rw [hC1e]; linarith
  refine ⟨P', hP', ?_, ?_, circR K (b.1 - m) (b.1 + 1 + m) (b.2 - m) (b.2 + 1 + m),
    circR_sub_longFam hbx hby, ?_, ?_, ?_⟩
  · refine le_trans ?_ hmC
    rw [abs_le]; constructor <;> push_cast <;>
    · have := fa3; have := fa4
      have c1 : ((b.1 - m : ℤ) : ℝ) ≤ (P'.1 : ℝ) := Int.cast_le.2 fa3
      have c2 : (P'.1 : ℝ) ≤ ((b.1 + m : ℤ) : ℝ) := Int.cast_le.2 fa4
      push_cast at c1 c2; linarith
  · refine le_trans ?_ hmC
    rw [abs_le]; constructor <;> push_cast <;>
    · have c1 : ((b.2 - m : ℤ) : ℝ) ≤ (P'.2 : ℝ) := Int.cast_le.2 fb3
      have c2 : (P'.2 : ℝ) ≤ ((b.2 + m : ℤ) : ℝ) := Int.cast_le.2 fb4
      push_cast at c1 c2; linarith
  · have hc := card_circR_le hbx hby
    have hc' : ((circR K (b.1 - m) (b.1 + 1 + m) (b.2 - m) (b.2 + 1 + m)).card : ℝ) ≤
        16 * m + 64 := by
      have : ((circR K (b.1 - m) (b.1 + 1 + m) (b.2 - m) (b.2 + 1 + m)).card : ℤ) ≤
          16 * m + 64 := by omega
      exact_mod_cast this
    rw [pow_one, hC1e]; linarith
  · intro j hj x' hx'
    obtain ⟨⟨hsq', hbox'⟩, -⟩ := circR_props hbx hby hj hx'
    refine ⟨?_, ?_⟩
    · obtain ⟨⟨a5, a6⟩, ⟨a7, a8⟩⟩ := hsq'
      have e2 : (2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ K = 1 := e1
      push_cast at a5 a6 a7 a8
      simp only [zero_mul] at a5 a7
      simp only [T20D.bigBox, Complex.mem_reProdIm, mem_Icc]
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · have hn := elem_near (P' := P') fa3 fa4 fb3 fb4 hbox'
      have : (4 * m + 8 : ℝ) ≤ C₁ * (K : ℝ) ^ Q.ε₀ := by
        have e3 : C₁ * (K : ℝ) ^ Q.ε₀ = 40 * (A * (K : ℝ) ^ Q.ε₀) + 100 * (K : ℝ) ^ Q.ε₀ := by
          simp only [C₁]; ring
        have e4 : 2 * A * (K : ℝ) ^ Q.ε₀ = 2 * (A * (K : ℝ) ^ Q.ε₀) := by ring
        rw [e3]; rw [e4] at hmK; linarith
      calc _ ≤ _ := hn
        _ ≤ C₁ * (K : ℝ) ^ Q.ε₀ * h := mul_le_mul_of_nonneg_right this hp.le
  · -- the pathwise bound
    set f : ℂ → ℝ := fun x => psiMN Q W P 0 n x z.1
    have hf : Continuous f := (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)).cont z.1
    have hfg : ∀ x ∈ T20B.farSet (T20B.hoBlock K b) s,
        (fun x => psiMN Q W P 0 n x z.1 - T20B.blkKn Q W P K n b x z.1 +
          T20B.blkKn Q W P K n b x z.2) x = f x := fun x hx => by
      simp only [f, hz1 b hb x hx, hz2 b hb x hx, sub_zero, add_zero]
    have hfin : rectLen ξ f (rectAB 1 1) ≠ ⊤ :=
      rectLen_ne_top _ (by norm_num [rectAB]) (by norm_num [rectAB]) hf
    have hnear := hγ.near n z.1
    have hγf : lfppLen ξ f (γ n z.1) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hnear
    have hglue := glue_rect (ξ := ξ) hf hfg hbx hby (fun x' _ hx' => outBox_far hsm hx')
      (hγ.adm n z.1) hγf
    have hL : (lfppLen ξ f (γ n z.1)).toReal ≤ (1 + η) * T20C.lenPsi ξ Q W P n z.1 := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hnear
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
    linarith

end DDDF
end LQGMetric
