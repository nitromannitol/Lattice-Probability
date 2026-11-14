/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3Pathwise at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Mul
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Sub
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Glue3

 











set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP
open LQGMetric.DDDF.T20C LQGMetric.DDDF.T20D

open Classical in
 

def laneB3ShortFamily (k : ℕ) : Finset (Circle × ℂ) :=
  (T20.blkIdx k).biUnion (shortJ k)

theorem laneB3ShortFamily_nonempty (k : ℕ) : (laneB3ShortFamily k).Nonempty := by
  classical
  unfold laneB3ShortFamily
  refine Finset.biUnion_nonempty.2 ⟨(0, 0), ?_, ?_⟩
  · simp [T20.blkIdx]
  · simp [shortJ]

theorem laneB3ShortFamily_card_le (k : ℕ) :
    ((laneB3ShortFamily k).card : ℝ) ≤ 36 * 4 ^ k := by
  classical
  unfold laneB3ShortFamily
  calc (((T20.blkIdx k).biUnion (shortJ k)).card : ℝ) ≤
        ∑ b ∈ T20.blkIdx k, ((shortJ k b).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ T20.blkIdx k, (4 : ℝ) :=
        Finset.sum_le_sum fun b _ => by exact_mod_cast card_shortJ_le k b
    _ = 4 * (T20.blkIdx k).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 4 * (9 * 4 ^ k) := by gcongr; exact card_blkIdx_le k
    _ = 36 * 4 ^ k := by ring

 



theorem laneB3_lower_pathwise {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {ξ : ℝ} (hξ : 0 < ξ)
    {k n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n) (Y : ℂ → Ω → ℝ)
    (hY : ∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ k)⁻¹ 1 x)
    (hYc : ∀ ω, ContDiff ℝ 1 fun x => Y x ω) :
    ∀ᵐ ω ∂P, Real.exp (-((164 + 6 * ξ) * Obig k Y ω)) *
        ((2 : ℝ) ^ k * minShort ξ W P k (n + k) (laneB3ShortFamily k)
          (laneB3ShortFamily_nonempty k) ω) * lenN ξ W P 1 1 k ω ≤
      (164 + 6 * ξ) * lenN ξ W P 1 1 (n + k) ω := by
  classical
  set J' : Finset (Circle × ℂ) := laneB3ShortFamily k with hJ'def
  have hJ' : J'.Nonempty := laneB3ShortFamily_nonempty k
  have hk2 : 2 ≤ k := hk
  have hkn : k ≤ n + k := by omega
  have hφK := isPhiVersion_phiMN hW (Nat.zero_le k)
  have hφN := isPhiVersion_phiMN hW (Nat.zero_le (n + k))
  have hYeq : ∀ᵐ ω ∂P, ∀ x, Y x ω = phiMN W P 0 k x ω := by
    refine T20C.ae_forall_eq_of_cont (fun ω => (hYc ω).continuous) hφK.cont fun x => ?_
    have e : phi W ((2 : ℝ)⁻¹ ^ k) ((2 : ℝ)⁻¹ ^ 0) x = phi W ((2 : ℝ) ^ k)⁻¹ 1 x := by
      rw [inv_pow, pow_zero]
    exact (hY x).trans (by rw [← e]; exact (hφK.ae_eq x).symm)
  filter_upwards [ae_phiMN_add hW hkn, hYeq] with ω hadd hYω
  set O := Obig k Y ω
  set m := minShort ξ W P k (n + k) J' hJ' ω
  have hO0 : 0 ≤ O := Obig_nonneg k Y ω
  have hm0 : 0 ≤ m := Finset.le_inf' _ _ fun j _ => ENNReal.toReal_nonneg
  set f₀ : ℂ → ℝ := fun x => phiMN W P 0 (n + k) x ω
  set g : ℂ → ℝ := fun x => phiMN W P 0 k x ω
  
  have hfin : rectLen ξ f₀ (rectAB 1 1) ≠ ⊤ :=
    rectLen_ne_top _ (by norm_num [rectAB]) (by norm_num [rectAB]) (hφN.cont ω)
  have hpos : 0 < rectLen ξ f₀ (rectAB 1 1) :=
    rectLen_pos _ (by norm_num [rectAB, MarkedRect.crossWidth]) (hφN.cont ω)
  have hlt : rectLen ξ f₀ (rectAB 1 1) < 2 * rectLen ξ f₀ (rectAB 1 1) := by
    calc rectLen ξ f₀ (rectAB 1 1) = 1 * rectLen ξ f₀ (rectAB 1 1) := (one_mul _).symm
      _ < 2 * rectLen ξ f₀ (rectAB 1 1) :=
          ENNReal.mul_lt_mul_left hpos.ne' hfin (by norm_num)
  obtain ⟨γ, hγadm, hγlen⟩ := exists_admPath_lt hlt
  
  have hosc : ∀ b ∈ T20.coarseBlocks k γ, ∀ x ∈ hatBox k b,
      |g x - g (T20.dyCenter k b)| ≤ 3 * O := by
    intro b hb x hx
    have := osc_hatBox_le hk2 (hYc ω) (Finset.mem_filter.1 hb).1 hx
    simp only [g]; rw [← hYω, ← hYω]; exact this
  set E : ℤ × ℤ → ℝ := fun b => Real.exp (ξ * g (T20.dyCenter k b)) * Real.exp (-(ξ * (3 * O)))
  
  have hpiece : ∀ b ∈ T20.coarseBlocks k γ, ∃ a c, Icc a c ⊆ Icc (0 : ℝ) 1 ∧
      (∀ r ∈ Icc a c, γ r ∈ hatBox k b) ∧ ENNReal.ofReal (E b * m) ≤
        ∫⁻ r in Icc a c, lenDens ξ f₀ γ r := by
    intro b hb
    have hbI : b ∈ T20.blkIdx k := (Finset.mem_filter.1 hb).1
    refine piece_lower hk2 hγadm hb (by positivity) (fun x _ hxb => ?_) fun j hj =>
      Finset.inf'_le _ (by
        rw [hJ'def]; unfold laneB3ShortFamily; exact Finset.mem_biUnion.2 ⟨b, hbI, hj⟩)
    have h3 := abs_le.1 (hosc b hb x hxb)
    have h4 := hadd x
    simp only [E]
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : g (T20.dyCenter k b) - 3 * O + phiMN W P k (n + k) x ω ≤ f₀ x := by
      simp only [f₀, g] at h3 ⊢; linarith [h3.1]
    nlinarith
  have hsum := sum_pieces_le (K := k) (γ := γ) (T20.coarseBlocks k γ)
    (lenDens ξ f₀ γ) (fun b => ENNReal.ofReal (E b * m)) hpiece
  rw [← lfppLen_eq] at hsum
  have hbound : ∑ b ∈ T20.coarseBlocks k γ, ENNReal.ofReal (E b * m) ≤
      ENNReal.ofReal 32 * rectLen ξ f₀ (rectAB 1 1) := by
    refine hsum.trans ?_
    rw [show (32 : ℝ) = 16 * 2 by norm_num, ENNReal.ofReal_mul (by norm_num), mul_assoc]
    gcongr
    · norm_num
    · rw [ENNReal.ofReal_ofNat]; exact hγlen.le
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hbound
  rw [ENNReal.toReal_sum (fun b _ => ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)] at hreal
  have hreal' : ∑ b ∈ T20.coarseBlocks k γ, E b * m ≤ 32 * lenN ξ W P 1 1 (n + k) ω := by
    refine le_trans (le_of_eq ?_) hreal
    exact Finset.sum_congr rfl fun b _ => (ENNReal.toReal_ofReal (by positivity)).symm
  
  set w : ℤ × ℤ → ℝ := fun b => Real.exp (ξ * g (T20.dyCenter k b)) * Real.exp (ξ * (3 * O))
  have hw : ∀ b ∈ T20.coarseBlocks k γ, ∀ x ∈ hatBox k b, Real.exp (ξ * g x) ≤ w b := by
    intro b hb x hx
    have h3 := abs_le.1 (hosc b hb x hx)
    simp only [w]; rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [h3.2]
  have hcoarse := S6.rectLen_le_coarse hγadm hw
  have hLk : lenN ξ W P 1 1 k ω ≤ 4 * (2 : ℝ)⁻¹ ^ k * ∑ b ∈ T20.coarseBlocks k γ, w b := by
    have h0 : 0 ≤ 4 * (2 : ℝ)⁻¹ ^ k * ∑ b ∈ T20.coarseBlocks k γ, w b := by positivity
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcoarse
    rwa [ENNReal.toReal_ofReal h0] at this
  
  set S₀ := ∑ b ∈ T20.coarseBlocks k γ, Real.exp (ξ * g (T20.dyCenter k b))
  have hS0 : 0 ≤ S₀ := Finset.sum_nonneg fun b _ => (Real.exp_pos _).le
  have hw' : ∑ b ∈ T20.coarseBlocks k γ, w b = Real.exp (ξ * (3 * O)) * S₀ := by
    simp only [w, S₀, Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
  have hE' : ∑ b ∈ T20.coarseBlocks k γ, E b * m = Real.exp (-(ξ * (3 * O))) * m * S₀ := by
    simp only [E, S₀, Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
  rw [hw'] at hLk
  rw [hE'] at hreal'
  have hL0 : 0 ≤ lenN ξ W P 1 1 k ω := ENNReal.toReal_nonneg
  have h2k : (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ k = 1 := by rw [← mul_pow]; norm_num
  have hexp : Real.exp (-((164 + 6 * ξ) * O)) ≤
      Real.exp (-(ξ * (3 * O))) * Real.exp (-(ξ * (3 * O))) := by
    rw [← Real.exp_add]; refine Real.exp_le_exp.2 ?_; nlinarith
  have hee : Real.exp (-(ξ * (3 * O))) * Real.exp (ξ * (3 * O)) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hA : 0 ≤ (2 : ℝ) ^ k * m := by positivity
  calc Real.exp (-((164 + 6 * ξ) * O)) * ((2 : ℝ) ^ k * m) * lenN ξ W P 1 1 k ω
      ≤ Real.exp (-(ξ * (3 * O))) * Real.exp (-(ξ * (3 * O))) * ((2 : ℝ) ^ k * m) *
          (4 * (2 : ℝ)⁻¹ ^ k * (Real.exp (ξ * (3 * O)) * S₀)) := by
        gcongr
    _ = 4 * ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ k) *
          (Real.exp (-(ξ * (3 * O))) * Real.exp (ξ * (3 * O))) *
          (Real.exp (-(ξ * (3 * O))) * m * S₀) := by ring
    _ = 4 * (Real.exp (-(ξ * (3 * O))) * m * S₀) := by rw [h2k, hee]; ring
    _ ≤ 4 * (32 * lenN ξ W P 1 1 (n + k) ω) := by gcongr
    _ ≤ (164 + 6 * ξ) * lenN ξ W P 1 1 (n + k) ω := by
        have : 0 ≤ lenN ξ W P 1 1 (n + k) ω := ENNReal.toReal_nonneg
        nlinarith


 




theorem laneB3_upper_pathwise {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ k : ℕ, 2 ≤ k → ∃ circ : ℤ × ℤ → Finset (Circle × ℂ),
      (∀ b, ((circ b).card : ℝ) ≤ C₁) ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ, 1 ≤ n →
        ∃ V : ℤ × ℤ → Ω → ℝ, (∀ b ∈ T20.blkIdx k, ∀ ω, 0 ≤ V b ω) ∧
          ∀ Y : ℂ → Ω → ℝ, (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ k)⁻¹ 1 x) →
            (∀ ω, ContDiff ℝ 1 fun x => Y x ω) →
            ∀ᵐ ω ∂P, lenN ξ W P 1 1 (n + k) ω ≤
                ∑ b ∈ T20.blkIdx k, V b ω * ∑ j ∈ circ b,
                  T20B.mrectLen ξ (fun x => phiMN W P k (n + k) x ω) k j.1 j.2 3 1 ∧
              ∑ b ∈ T20.blkIdx k, V b ω ≤
                C₁ * (2 : ℝ) ^ k * Real.exp (C₁ * Obig k Y ω) * lenN ξ W P 1 1 k ω := by
  classical
  obtain ⟨Cg, hCg, hglue⟩ := s6_step1_glue ξ
  refine ⟨max Cg ((Cg + 1) * (32 + 10 * ξ)), lt_max_of_lt_left hCg, fun k hk => ?_⟩
  obtain ⟨circ, hcard, hgl⟩ := hglue k hk
  refine ⟨circ, fun b => (hcard b).trans (le_max_left _ _), ?_⟩
  intro Ω _ P W hW n hn
  set F : Ω → ℂ → ℝ := fun ω x => phiMN W P 0 k x ω with hFdef
  have hφK := isPhiVersion_phiMN hW (Nat.zero_le k)
  have hφG := isPhiVersion_phiMN hW (show k ≤ n + k by omega)
  have hφN := isPhiVersion_phiMN hW (Nat.zero_le (n + k))
  have hFc : ∀ ω, Continuous (F ω) := fun ω => hφK.cont ω
  obtain ⟨Q, hQa, Jsel, hJm, hJl⟩ := S6U.exists_sel ξ F hFc
  set w : ℤ × ℤ → Ω → ℝ := fun b ω => Real.exp (ξ * ⨆ x : S6U.glueBox k b, F ω x) with hwdef
  set V : ℤ × ℤ → Ω → ℝ := fun b ω =>
    Cg * if b ∈ T20.coarseBlocks k (Q (Jsel ω)) then w b ω else 0 with hVdef
  refine ⟨V, fun b _ ω => ?_, fun Y hY hYc => ?_⟩
  · simp only [V]; refine mul_nonneg hCg.le ?_; split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have hYeq : ∀ᵐ ω ∂P, ∀ x, Y x ω = phiMN W P 0 k x ω := by
    refine T20C.ae_forall_eq_of_cont (fun ω => (hYc ω).continuous) hφK.cont fun x => ?_
    have e : phi W ((2 : ℝ)⁻¹ ^ k) ((2 : ℝ)⁻¹ ^ 0) x = phi W ((2 : ℝ) ^ k)⁻¹ 1 x := by
      rw [inv_pow, pow_zero]
    exact (hY x).trans (by rw [← e]; exact (hφK.ae_eq x).symm)
  filter_upwards [ae_phiMN_add hW (show k ≤ n + k by omega), hYeq] with ω hadd hYω
  set γ := Q (Jsel ω)
  have hγ := hQa (Jsel ω)
  set S := T20.coarseBlocks k γ
  have hSI : S ⊆ T20.blkIdx k := Finset.filter_subset _ _
  have hred : ∀ X : ℤ × ℤ → ℝ,
      ∑ b ∈ T20.blkIdx k, V b ω * X b = Cg * ∑ b ∈ S, w b ω * X b := by
    intro X
    simp only [V, mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    rw [← Finset.sum_subset hSI (fun b _ hb => by
      rw [if_neg (show b ∉ T20.coarseBlocks k (Q (Jsel ω)) from hb), zero_mul])]
    exact Finset.sum_congr rfl fun b hb => by
      rw [if_pos (show b ∈ T20.coarseBlocks k (Q (Jsel ω)) from hb)]
  have hO0 : 0 ≤ Obig k Y ω := Obig_nonneg k Y ω
  set O := Obig k Y ω
  refine ⟨?_, ?_⟩
  · 
    rw [hred]
    have hf : (fun x => phiMN W P 0 (n + k) x ω) = fun x => F ω x + phiMN W P k (n + k) x ω :=
      funext hadd
    show (rectLen ξ (fun x => phiMN W P 0 (n + k) x ω) (rectAB 1 1)).toReal ≤ _
    rw [hf]
    exact hgl (F ω) _ (hFc ω) (hφG.cont ω) γ hγ (fun b => w b ω) fun b _ x hx =>
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (S6U.le_sup_of_mem (hFc ω) (S6U.isCompact_glueBox k b) hx) hξ.le)
  · 
    have hred1 : ∑ b ∈ T20.blkIdx k, V b ω = Cg * ∑ b ∈ S, w b ω := by
      have := hred (fun _ => 1); simpa using this
    rw [hred1]
    have hk2 : 2 ≤ k := hk
    
    have hosc : ∀ b ∈ S, ∀ x ∈ hatBox k b, |F ω x - F ω (T20.dyCenter k b)| ≤ 3 * O := by
      intro b hb x hx
      have := osc_hatBox_le hk2 (hYc ω) (Finset.mem_filter.1 hb).1 hx
      simp only [F]; rw [← hYω, ← hYω]; exact this
    have hwle : ∀ b ∈ S,
        w b ω ≤ Real.exp (ξ * F ω (T20.dyCenter k b)) * Real.exp (ξ * (7 * O)) := by
      intro b hb
      have hbI : b ∈ T20.blkIdx k := (Finset.mem_filter.1 hb).1
      simp only [w]; rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have : ⨆ x : S6U.glueBox k b, F ω x ≤ F ω (T20.dyCenter k b) + 7 * O := by
        refine S6U.sup_le_of_forall (S6U.nonempty_glueBox k b) fun x hx => ?_
        obtain ⟨hxB, hxd⟩ := S6U.glueBox_near hk2 hbI hx
        have hcB : T20.dyCenter k b ∈ bigBox :=
          (S6U.glueBox_near hk2 hbI (x := T20.dyCenter k b) (by
            have hp := h_pos k
            simp only [S6U.glueBox, T20.dyCenter, Complex.mem_reProdIm, mem_Icc]
            refine ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩)).1
        have h1 := osc_bigBox_le k (hYc ω) hxB hcB
        rw [hYω, hYω] at h1
        have h2k : (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ k = 1 := by rw [← mul_pow]; norm_num
        have h3 : (2 : ℝ) ^ k * O * ‖x - T20.dyCenter k b‖ ≤ 7 * O := by
          calc (2 : ℝ) ^ k * O * ‖x - T20.dyCenter k b‖
              ≤ (2 : ℝ) ^ k * O * (7 * (2 : ℝ)⁻¹ ^ k) :=
                mul_le_mul_of_nonneg_left hxd (by positivity)
            _ = 7 * O * ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ k) := by ring
            _ = 7 * O := by rw [h2k, mul_one]
        have := (abs_le.1 (h1.trans h3)).2
        simp only [F]; linarith
      nlinarith
    set E : ℤ × ℤ → ℝ := fun b => Real.exp (ξ * F ω (T20.dyCenter k b)) *
      Real.exp (-(ξ * (3 * O)))
    
    have hpiece : ∀ b ∈ S, ∃ a c, Icc a c ⊆ Icc (0 : ℝ) 1 ∧
        (∀ r ∈ Icc a c, γ r ∈ hatBox k b) ∧ ENNReal.ofReal (E b * (2 : ℝ)⁻¹ ^ k) ≤
          ∫⁻ r in Icc a c, lenDens ξ (F ω) γ r := by
      intro b hb
      refine piece_lower (f := fun _ => 0) hk2 hγ hb (by positivity) (fun x _ hxb => ?_)
        fun j _ => S6U.mrectLen_zero_ge ξ k j.1 j.2
      have h3 := abs_le.1 (hosc b hb x hxb)
      simp only [E, mul_zero, Real.exp_zero, mul_one]
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith [h3.1]
    have hsum := sum_pieces_le (K := k) (γ := γ) S (lenDens ξ (F ω) γ)
      (fun b => ENNReal.ofReal (E b * (2 : ℝ)⁻¹ ^ k)) hpiece
    rw [← lfppLen_eq] at hsum
    have hfin : rectLen ξ (F ω) (rectAB 1 1) ≠ ⊤ :=
      rectLen_ne_top _ (by norm_num [rectAB]) (by norm_num [rectAB]) (hFc ω)
    have hbound : ∑ b ∈ S, ENNReal.ofReal (E b * (2 : ℝ)⁻¹ ^ k) ≤
        ENNReal.ofReal 32 * rectLen ξ (F ω) (rectAB 1 1) := by
      refine hsum.trans ?_
      rw [show (32 : ℝ) = 16 * 2 by norm_num, ENNReal.ofReal_mul (by norm_num), mul_assoc]
      gcongr
      · norm_num
      · rw [ENNReal.ofReal_ofNat]
        have := (hJl ω).le
        rwa [one_add_one_eq_two] at this
    have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hbound
    rw [ENNReal.toReal_sum (fun b _ => ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)] at hreal
    have hreal' : ∑ b ∈ S, E b * (2 : ℝ)⁻¹ ^ k ≤ 32 * lenN ξ W P 1 1 k ω := by
      refine le_trans (le_of_eq ?_) hreal
      exact Finset.sum_congr rfl fun b _ => (ENNReal.toReal_ofReal (by positivity)).symm
    have hee : Real.exp (ξ * (7 * O)) = Real.exp (10 * ξ * O) * Real.exp (-(ξ * (3 * O))) := by
      rw [← Real.exp_add]; ring_nf
    have h2k : (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ k = 1 := by rw [← mul_pow]; norm_num
    have hL0 : 0 ≤ lenN ξ W P 1 1 k ω := ENNReal.toReal_nonneg
    have hkey : ∑ b ∈ S, w b ω ≤ Real.exp (10 * ξ * O) * (2 : ℝ) ^ k * (32 * lenN ξ W P 1 1 k ω) :=
      calc ∑ b ∈ S, w b ω ≤ ∑ b ∈ S, Real.exp (ξ * F ω (T20.dyCenter k b)) *
          Real.exp (ξ * (7 * O)) := Finset.sum_le_sum hwle
      _ = Real.exp (10 * ξ * O) * (2 : ℝ) ^ k * ∑ b ∈ S, E b * (2 : ℝ)⁻¹ ^ k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          simp only [E]; rw [hee]
          calc Real.exp (ξ * F ω (T20.dyCenter k b)) *
                (Real.exp (10 * ξ * O) * Real.exp (-(ξ * (3 * O))))
              = Real.exp (10 * ξ * O) * ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ k) *
                  (Real.exp (ξ * F ω (T20.dyCenter k b)) * Real.exp (-(ξ * (3 * O)))) := by
                rw [h2k]; ring
            _ = _ := by ring
      _ ≤ Real.exp (10 * ξ * O) * (2 : ℝ) ^ k * (32 * lenN ξ W P 1 1 k ω) := by gcongr
    set C' := max Cg ((Cg + 1) * (32 + 10 * ξ))
    have h1 : Real.exp (10 * ξ * O) ≤ Real.exp (C' * O) := by
      refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ hO0)
      refine le_trans ?_ (le_max_right _ _)
      nlinarith
    have h2 : Cg * 32 ≤ C' := le_trans (by nlinarith) (le_max_right _ _)
    have hp : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
    calc Cg * ∑ b ∈ S, w b ω ≤ Cg * (Real.exp (10 * ξ * O) * (2 : ℝ) ^ k *
          (32 * lenN ξ W P 1 1 k ω)) := mul_le_mul_of_nonneg_left hkey hCg.le
      _ = (Cg * 32) * (2 : ℝ) ^ k * Real.exp (10 * ξ * O) * lenN ξ W P 1 1 k ω := by ring
      _ ≤ C' * (2 : ℝ) ^ k * Real.exp (C' * O) * lenN ξ W P 1 1 k ω := by gcongr

end SupercriticalLQGUniqueness.B2.DG20Conc
