/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P26Sub at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Up
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DDen
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DNum

/-!
# DDDF Prop 26, Step 1: the circuit bound from the deterministic gluing (task P2-DDDF6b)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 1285–1306. `S6Step1Circ` (S6P26Up.lean) is reduced to the deterministic statement
`S6Step1Glue` (DDDF l. 1289–1294: "`Γ_{k,n}` contains a left-right crossing of `[0,1]²` whose
length is bounded above by `Σ_{P ∈ π_k^k} L^{(k,n+k)}(S^{(k,n+k)}(P)) e^{ξ max_{\hat P} φ_{0,k}}`").
Proved here:

* the geodesic `π_k` is a measurable near-geodesic selection (`exists_nearGeodesic`, factor 2)
  for the `σ(φ_{0,k})`-measurable structure, so `V_P := 1_{P ∈ π_k^k} e^{ξ max_{\hat P} φ_{0,k}}` is
  `φ_{0,k}`-measurable (DDDF l. 1288);
* DDDF l. 1296–1306: every visited block `P` contains a piece of `π_k` crossing a short rectangle of
  `\hat P` (`T20D.piece_lower` with the zero field: Euclidean length `≥ 2^{-k}`,
  `mrectLen_zero_ge`), of `φ_{0,k}`-length `≥ 2^{-k} e^{ξφ_{0,k}(P) − 3ξ Obig}`, and the boxes
  `\hat P` overlap at most 16 times (`T20D.sum_pieces_le`; DDDF: 9), whence
  `Σ_P V_P ≤ 32 · 2^k e^{6ξ Obig} L^{(k)}_{1,1}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise LFPP T20C T20D

namespace S6U

/-- the `7 × 7` box of blocks around the block `b` (it contains the circuit of the block nearest
to `b` whose circuit lies in `[0,1]²`) -/
def glueBox (k : ℕ) (b : ℤ × ℤ) : Set ℂ :=
  Icc (((b.1 : ℝ) - 3) * (2 : ℝ)⁻¹ ^ k) (((b.1 : ℝ) + 4) * (2 : ℝ)⁻¹ ^ k) ×ℂ
    Icc (((b.2 : ℝ) - 3) * (2 : ℝ)⁻¹ ^ k) (((b.2 : ℝ) + 4) * (2 : ℝ)⁻¹ ^ k)

end S6U

/-- **DDDF Prop 26, Step 1, the gluing** (l. 1289–1294), deterministic: for `k ≥ 2` there are
circuits `circ b` of `≤ C₁` long rectangles `u 2^{-k} R_{3,1} + c` near each block such that for
continuous `f, g`, every left–right crossing `γ` of `[0,1]²` and weights `w` with
`e^{ξ f} ≤ w(P)` on the `7 × 7` box `glueBox k P` for `P ∈ π^k(γ)`,
`L_{1,1}(f + g) ≤ C₁ Σ_{P ∈ π^k(γ)} w(P) Σ_{R ∈ circ P} L^{(k)}(R, g)`. Proved:
`s6_step1_glue` (S6P26Glue3.lean). -/
def S6Step1Glue (ξ : ℝ) : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ k : ℕ, 2 ≤ k → ∃ circ : ℤ × ℤ → Finset (Circle × ℂ),
    (∀ b, ((circ b).card : ℝ) ≤ C₁) ∧
    ∀ (f g : ℂ → ℝ), Continuous f → Continuous g → ∀ γ : ℝ → ℂ,
      AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁ (rectAB 1 1).side₂ γ →
      ∀ w : ℤ × ℤ → ℝ, (∀ b ∈ T20.coarseBlocks k γ, ∀ x ∈ S6U.glueBox k b,
        Real.exp (ξ * f x) ≤ w b) →
        (rectLen ξ (fun x => f x + g x) (rectAB 1 1)).toReal ≤
          C₁ * ∑ b ∈ T20.coarseBlocks k γ, w b * ∑ j ∈ circ b, T20B.mrectLen ξ g k j.1 j.2 3 1

namespace S6U

/-- the Euclidean crossing length of `u 2^{-k} R_{1,3} + c` is at least `2^{-k}` -/
lemma mrectLen_zero_ge (ξ : ℝ) (k : ℕ) (u : Circle) (c : ℂ) :
    (2 : ℝ)⁻¹ ^ k ≤ T20B.mrectLen ξ (fun _ => 0) k u c 1 3 := by
  have hr : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  have htop := crossLenIn_mot_ne_top (ξ := ξ) k u c (a := 1) (b := 3) zero_le_one (by norm_num)
    (f := fun _ => (0 : ℝ)) continuous_const
  unfold T20B.mrectLen
  refine (ENNReal.ofReal_le_iff_le_toReal htop).1 ?_
  rw [T20B.mot_image, T20B.mot_image, T20B.mot_image, crossLenIn_image_motion,
    crossLenIn_image_mul _ _ _ _ _ hr]
  have h1 : ENNReal.ofReal 1 ≤ rectLen ξ (fun _ => (0 : ℝ)) (rectAB 1 3) := by
    have := rectLen_ge (ξ := ξ) (f := fun _ => (0 : ℝ)) (rectAB 1 3) (M := 0)
      (fun x _ => by simp)
    simpa [MarkedRect.crossWidth, rectAB] using this
  calc ENNReal.ofReal ((2 : ℝ)⁻¹ ^ k) = ENNReal.ofReal ((2 : ℝ)⁻¹ ^ k) * ENNReal.ofReal 1 := by
        rw [ENNReal.ofReal_one, mul_one]
    _ ≤ _ := by gcongr; exact h1

/-- a near-geodesic of `F` chosen `σ(F)`-measurably -/
lemma exists_sel {Ω' : Type*} (ξ : ℝ) (F : Ω' → ℂ → ℝ) (hFc : ∀ ω, Continuous (F ω)) :
    ∃ Q : ℕ → ℝ → ℂ, (∀ j, AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁ (rectAB 1 1).side₂ (Q j))
      ∧ ∃ J : Ω' → ℕ, Measurable[MeasurableSpace.comap F inferInstance] J ∧
        ∀ ω, lfppLen ξ (F ω) (Q (J ω)) < (1 + 1) * rectLen ξ (F ω) (rectAB 1 1) := by
  letI : MeasurableSpace Ω' := MeasurableSpace.comap F inferInstance
  have hm : ∀ x, Measurable fun ω => F ω x :=
    fun x => (measurable_pi_apply x).comp (comap_measurable F)
  obtain ⟨Q, hQa, -, -, -, h2⟩ := exists_nearGeodesic (ξ := ξ) (rectAB 1 1) zero_le_one
    zero_le_one (Y := fun x ω => F ω x) hFc hm one_pos
  obtain ⟨J, hJ, hJl⟩ := h2 (by norm_num [MarkedRect.crossWidth, rectAB])
  exact ⟨Q, hQa, J, hJ, hJl⟩

lemma isCompact_glueBox (k : ℕ) (b : ℤ × ℤ) : IsCompact (glueBox k b) :=
  (isCompact_Icc.reProdIm isCompact_Icc)

lemma nonempty_glueBox (k : ℕ) (b : ℤ × ℤ) : (glueBox k b).Nonempty := by
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  refine ⟨⟨((b.1 : ℝ) - 3) * (2 : ℝ)⁻¹ ^ k, ((b.2 : ℝ) - 3) * (2 : ℝ)⁻¹ ^ k⟩, ?_⟩
  simp only [glueBox, Complex.mem_reProdIm, mem_Icc]
  exact ⟨⟨le_rfl, by nlinarith⟩, le_rfl, by nlinarith⟩

/-- `glueBox k b ⊆ [-2,3]²` and its points are within `7 · 2^{-k}` of the centre of `b` -/
lemma glueBox_near {k : ℕ} (hk : 2 ≤ k) {b : ℤ × ℤ} (hb : b ∈ T20.blkIdx k) {x : ℂ}
    (hx : x ∈ glueBox k b) : x ∈ bigBox ∧ ‖x - T20.dyCenter k b‖ ≤ 7 * (2 : ℝ)⁻¹ ^ k := by
  have hp := h_pos k
  have hq := h_le_quarter hk
  have e1 : (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ k = 1 := by rw [inv_pow, mul_inv_cancel₀ (by positivity)]
  simp only [T20.blkIdx, Finset.mem_product, Finset.mem_Icc] at hb
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hb
  have b1 : (-1 : ℝ) ≤ b.1 := by exact_mod_cast a1
  have b2 : (b.1 : ℝ) ≤ 2 ^ k := by exact_mod_cast a2
  have b3 : (-1 : ℝ) ≤ b.2 := by exact_mod_cast a3
  have b4 : (b.2 : ℝ) ≤ 2 ^ k := by exact_mod_cast a4
  simp only [glueBox, Complex.mem_reProdIm, mem_Icc] at hx
  obtain ⟨⟨x1, x2⟩, x3, x4⟩ := hx
  refine ⟨?_, ?_⟩
  · simp only [bigBox, Complex.mem_reProdIm, mem_Icc]
    refine ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im, T20.dyCenter]
    have h1 : |x.re - ((b.1 : ℝ) + 1 / 2) * (2 : ℝ)⁻¹ ^ k| ≤ 7 / 2 * (2 : ℝ)⁻¹ ^ k :=
      abs_le.2 ⟨by nlinarith, by nlinarith⟩
    have h2 : |x.im - ((b.2 : ℝ) + 1 / 2) * (2 : ℝ)⁻¹ ^ k| ≤ 7 / 2 * (2 : ℝ)⁻¹ ^ k :=
      abs_le.2 ⟨by nlinarith, by nlinarith⟩
    linarith

/-- `max_B F` is `σ(F)`-measurable for a compact nonempty `B` -/
lemma measurable_comap_sup {Ω' : Type*} (F : Ω' → ℂ → ℝ) (hFc : ∀ ω, Continuous (F ω))
    {B : Set ℂ} (hB : IsCompact B) (hne : B.Nonempty) :
    Measurable[MeasurableSpace.comap F inferInstance] fun ω => ⨆ x : B, F ω x := by
  letI : MeasurableSpace Ω' := MeasurableSpace.comap F inferInstance
  haveI : CompactSpace B := isCompact_iff_compactSpace.1 hB
  haveI : Nonempty B := hne.to_subtype
  exact measurable_iSup_of_continuous (X := fun (x : B) ω => F ω x)
    (fun ω => (hFc ω).comp continuous_subtype_val)
    (fun x => (measurable_pi_apply (x : ℂ)).comp (comap_measurable F))

lemma le_sup_of_mem {F : ℂ → ℝ} (hF : Continuous F) {B : Set ℂ} (hB : IsCompact B) {x : ℂ}
    (hx : x ∈ B) : F x ≤ ⨆ y : B, F y := by
  haveI : CompactSpace B := isCompact_iff_compactSpace.1 hB
  have hb : BddAbove (range fun y : B => F y) :=
    (isCompact_range (hF.comp continuous_subtype_val)).bddAbove
  exact le_ciSup (f := fun y : B => F y) hb ⟨x, hx⟩

lemma sup_le_of_forall {F : ℂ → ℝ} {B : Set ℂ} (hne : B.Nonempty) {M : ℝ}
    (h : ∀ x ∈ B, F x ≤ M) : ⨆ y : B, F y ≤ M := by
  haveI : Nonempty B := hne.to_subtype
  exact ciSup_le fun y => h y y.2

end S6U

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DDDF Prop 26, Step 1, pathwise part** (l. 1285–1306) from the gluing `S6Step1Glue`. -/
theorem s6Step1Circ_of_glue (hW : IsWhiteNoise P W) {ξ : ℝ} (hξ : 0 < ξ)
    (hG : S6Step1Glue ξ) : S6Step1Circ ξ W P := by
  classical
  obtain ⟨Cg, hCg, hglue⟩ := hG
  refine ⟨max Cg ((Cg + 1) * (32 + 10 * ξ)), lt_max_of_lt_left hCg, fun k n hk hn => ?_⟩
  obtain ⟨circ, hcard, hgl⟩ := hglue k hk
  set F : Ω → ℂ → ℝ := fun ω x => phiMN W P 0 k x ω with hFdef
  have hφK := isPhiVersion_phiMN hW (Nat.zero_le k)
  have hφG := isPhiVersion_phiMN hW (show k ≤ n + k by omega)
  have hφN := isPhiVersion_phiMN hW (Nat.zero_le (n + k))
  have hFc : ∀ ω, Continuous (F ω) := fun ω => hφK.cont ω
  obtain ⟨Q, hQa, Jsel, hJm, hJl⟩ := S6U.exists_sel ξ F hFc
  set w : ℤ × ℤ → Ω → ℝ := fun b ω => Real.exp (ξ * ⨆ x : S6U.glueBox k b, F ω x) with hwdef
  set V : ℤ × ℤ → Ω → ℝ := fun b ω =>
    Cg * if b ∈ T20.coarseBlocks k (Q (Jsel ω)) then w b ω else 0 with hVdef
  refine ⟨T20.blkIdx k, circ, V, fun b _ => (hcard b).trans (le_max_left _ _), fun b _ => ?_,
    fun b _ ω => ?_, fun Y hY hYc => ?_⟩
  · have hw : Measurable[MeasurableSpace.comap F inferInstance] (w b) :=
      ((S6U.measurable_comap_sup F hFc (S6U.isCompact_glueBox k b)
        (S6U.nonempty_glueBox k b)).const_mul ξ).exp
    have hs : MeasurableSet[MeasurableSpace.comap F inferInstance]
        {ω | b ∈ T20.coarseBlocks k (Q (Jsel ω))} :=
      hJm (MeasurableSet.of_discrete (s := {j | b ∈ T20.coarseBlocks k (Q j)}))
    exact (Measurable.ite hs hw measurable_const).const_mul Cg
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
  · -- (i): the gluing
    rw [hred]
    have hf : (fun x => phiMN W P 0 (n + k) x ω) = fun x => F ω x + phiMN W P k (n + k) x ω :=
      funext hadd
    show (rectLen ξ (fun x => phiMN W P 0 (n + k) x ω) (rectAB 1 1)).toReal ≤ _
    rw [hf]
    exact hgl (F ω) _ (hFc ω) (hφG.cont ω) γ hγ (fun b => w b ω) fun b _ x hx =>
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (S6U.le_sup_of_mem (hFc ω) (S6U.isCompact_glueBox k b) hx) hξ.le)
  · -- (ii): DDDF l. 1296–1306
    have hred1 : ∑ b ∈ T20.blkIdx k, V b ω = Cg * ∑ b ∈ S, w b ω := by
      have := hred (fun _ => 1); simpa using this
    rw [hred1]
    have hk2 : 2 ≤ k := hk
    -- `w(P) ≤ e^{ξ F(c_P) + 3ξ O}` on visited blocks
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
    -- pieces of `γ`, Euclidean length `≥ 2^{-k}`
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

end DDDF
end LQGMetric
