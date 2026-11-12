/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412U1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodL416b
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodL422F
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodS46
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412bStab

/-!
# GM Lemmas 4.22, 4.16 and the stability step with a uniform threshold (P2-M2J2i, part 1)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.22 (l. 2527–2565),
Lemma 4.16 (l. 2216–2222, 2572–2579), L4.15 Step 3 (l. 2155–2199). `GMP4_12At` needs `ε₀`
uniform in `E, rr`, the space and `𝕣` (P412jGoodU, handoff P2-M2J2h §4). The proofs of
`gm_L4_22` (ManyGoodL422F), `gm_L4_16` (ManyGoodL416E), `p412b_stab_of_ext` (P412bStab) choose
`ε₁` from the numbers `a, β, χ, χ', λ, ℓ, ξ` only; the primed copies `…U` below are the same
proofs with `∃ ε₁` stated before the regularity parameters `R` (with the numeric fields fixed,
`RegNum`), the space, the field and `𝕣`.

* `RegNum R ξ c p χ χ' μ ν lam ℓ U V`: all fields of `R` except `E, rr` are the given ones;
* `regC2N`: `regC2const` in terms of the numbers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- the fields of `R` other than the events `E` and the radii `rr` -/
def RegNum (R : RegPar) (ξ : ℝ) (c : ℝ → ℝ) (p : CONFParams) (χ χ' μ ν : ℝ) (lam : Fin 5 → ℝ)
    (ℓ : ℝ) (U V : Set ℂ) : Prop :=
  R.ξ = ξ ∧ R.c = c ∧ R.p = p ∧ R.χ = χ ∧ R.χ' = χ' ∧ R.μ = μ ∧ R.ν = ν ∧ R.lam = lam ∧
    R.ℓ = ℓ ∧ R.U = U ∧ R.V = V

theorem regNum_self (R : RegPar) : RegNum R R.ξ R.c R.p R.χ R.χ' R.μ R.ν R.lam R.ℓ R.U R.V :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `regC2const` in terms of the numbers `ℓ, ξ` -/
def regC2N (ℓ ξ a : ℝ) : ℝ := (ℓ / a + 1) * Real.exp (ξ / a)

theorem regC2N_eq (R : RegPar) (a : ℝ) : regC2N R.ℓ R.ξ a = regC2const R a := rfl

variable {ξN : ℝ} {cN : ℝ → ℝ} {pN : CONFParams} {χN χ'N μN νN : ℝ} {lamN : Fin 5 → ℝ} {ℓN : ℝ}
  {UN VN : Set ℂ}

theorem gm_L4_22U
    {a β : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ ℓN) (hχ : 0 < χN) (hχ' : 0 < χ'N)
    (hβ : 0 < β) (hβχ : β < χN) (hlam : 1 < lamN 3) (hUV : UN ⊆ VN)
    (hξ : 0 ≤ ξN) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ R : RegPar, RegNum R ξN cN pN χN χ'N μN νN lamN ℓN UN VN →
    ∀ {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC}
    {H : ℝ → ℂ → Ω → ℝ} {𝕣 : ℝ}, 0 < 𝕣 → 0 < R.c 𝕣 → ∀ ε ∈ Ioo (0 : ℝ) ε₁, ∀ ω ∈ regEvent D P h H R 𝕣 a,
    ∀ 𝕫 ∈ rScale 𝕣 R.U, H 𝕣 0 ω = circleAvg (h ω) 𝕣 0 → H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫 →
    (D (h ω)).IsLength → (∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) →
    (∀ y, ∃ Q : ℝ → ℂ, IsGeodesicL (D (h ω)) Q ((D (h ω)).1 (𝕫, y)) 𝕫 y) →
    ∀ k ≤ p4K R a ε β, ∀ z : ℂ,
      R.lam 3 * (ε * 𝕣) ≤ infDist z (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) →
      infDist z (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) ≤ 2 * R.lam 3 * (ε * 𝕣) →
      filledBall (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω) ⊆ ball 𝕫 (3 * (R.ℓ * 𝕣)) ∧
      s4T D h 𝕫 R.ℓ 𝕣 ε β k ω + ⌈16 * Real.pi * R.lam 3⌉₊ *
          ((ε / 4) ^ R.χ * scaleFac R.ξ R.c (h ω) 𝕣 0) < s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω ∧
      2 * R.lam 3 * (ε * 𝕣) < ‖𝕫 - z‖ ∧
      ∀ u ∈ sphere z (2 * R.lam 3 * (ε * 𝕣)),
        (D (h ω)).internal (filledBall (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω) \
            closedBall z (ε * 𝕣)) 𝕫 u ≤
          ENNReal.ofReal (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω + ⌈16 * Real.pi * R.lam 3⌉₊ *
            ((ε / 4) ^ R.χ * scaleFac R.ξ R.c (h ω) 𝕣 0)) := by
  set lam := lamN 3 with hlamdef
  set N := ⌈16 * Real.pi * lam⌉₊ with hNdef
  have hℓ : 0 < ℓN := lt_of_lt_of_le ha0 haℓ
  have hc2 : 0 < regC2N ℓN ξN a := by unfold regC2N; positivity
  have ha2 : 0 < (a / 2) ^ χ'N := by positivity
  have hgapev := gm_small_gap hβ hβχ (show 0 < ((N : ℝ) + 1) / (a / 2) ^ χ'N by positivity)
  have hβev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ β ≤ a / regC2N ℓN ξN a := by
    have := (Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto
    rw [Real.zero_rpow hβ.ne'] at this
    exact (this.mono_left nhdsWithin_le_nhds).eventually (Iic_mem_nhds (by positivity))
  have hlin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 (min (min 1 (a / (2 * lam)))
      (ℓN / (4 * lam + 1))) :=
    Ioo_mem_nhdsGT (lt_min (lt_min one_pos (by positivity)) (by positivity))
  obtain ⟨ε₁, hε₁, hε₁'⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 ((hgapev.and hβev).and hlin)
  refine ⟨ε₁, hε₁, ?_⟩
  intro R hRN Ω _ D P h H 𝕣 h𝕣 hc
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hRN
  try simp only [regC2N_eq] at *
  try rw [← hlamdef]
  try rw [← hNdef]
  intro ε hε ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd hgeod k hk z hz1 hz2
  obtain ⟨⟨hgap0, hεβ⟩, hεlin⟩ := hε₁' hε
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 := lt_of_lt_of_le hεlin.2 ((min_le_left _ _).trans (min_le_left _ _))
  have hεa : ε < a / (2 * lam) := lt_of_lt_of_le hεlin.2 ((min_le_left _ _).trans (min_le_right _ _))
  have hεℓ : ε < R.ℓ / (4 * lam + 1) := lt_of_lt_of_le hεlin.2 (min_le_right _ _)
  have hlam0 : 0 < lam := by linarith
  have hεa' : 2 * lam * ε < a := by rw [lt_div_iff₀ (by positivity)] at hεa; linarith
  have hεℓ' : (4 * lam + 1) * ε < R.ℓ := by rw [lt_div_iff₀ (by positivity)] at hεℓ; linarith
  obtain ⟨_, h2, h3, _, _, _, _⟩ := gm_regEvent_mem.1 hω
  set S := scaleFac R.ξ R.c (h ω) 𝕣 0 with hSdef
  have hS : 0 < S := mul_pos hc (Real.exp_pos _)
  set e := ε * 𝕣 with hedef
  have he : 0 < e := mul_pos hε0 h𝕣
  have h𝕫V : 𝕫 ∈ rScale 𝕣 R.V := image_mono hUV h𝕫
  have hreg : ∀ x : ℂ, dist x 𝕫 < 4 * (R.ℓ * 𝕣) → x ∈ regRegion R 𝕣 := fun x hx =>
    Metric.mem_thickening_iff.2 ⟨𝕫, h𝕫V, hx⟩
  have h𝕫R : 𝕫 ∈ regRegion R 𝕣 := hreg 𝕫 (by rw [dist_self]; positivity)
  -- the unit `τ = τ_{ℓ𝕣}(𝕫) ≥ (a/2)^{χ'} S`
  set τ := tauR D h 𝕫 (R.ℓ * 𝕣) ω with hτdef
  have hτ : (a / 2) ^ R.χ' * S ≤ τ := by
    have har : 0 < a * 𝕣 := mul_pos ha0 h𝕣
    have hal : a * 𝕣 ≤ R.ℓ * 𝕣 := mul_le_mul_of_nonneg_right haℓ h𝕣.le
    refine gm_tauR_ge_of_sphere hL (by positivity : 0 < a * 𝕣 / 2) (by linarith) fun w hw => ?_
    have hw' : ‖𝕫 - w‖ = a * 𝕣 / 2 := by rw [← dist_eq_norm, dist_comm]; exact mem_sphere.1 hw
    have := gm_regC3_lower h3 h𝕣 hS h𝕫R (hreg w (by rw [mem_sphere.1 hw]; linarith))
      (by rw [hw']; linarith)
    rwa [hw', show a * 𝕣 / 2 / 𝕣 = a / 2 by field_simp] at this
  have hτ0 : 0 < τ := lt_of_lt_of_le (mul_pos ha2 hS) hτ
  -- times
  set t := s4T D h 𝕫 R.ℓ 𝕣 ε β k ω with htdef
  set s' := s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω with hs'def
  have hεβ0 : 0 ≤ ε ^ β := (Real.rpow_pos_of_pos hε0 _).le
  have hτt : τ ≤ t := by
    have := gm_s4S_le_s4T (D := D) (h := h) (𝕫 := 𝕫) (ℓ := R.ℓ) (𝕣 := 𝕣) (β := β) hε0 k ω
    have h1 : τ ≤ s4S D h 𝕫 R.ℓ 𝕣 ε β k ω := by
      simp only [s4S, s4Unit]; rw [← hτdef, mul_add, mul_one]
      have := mul_nonneg hτ0.le (mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hεβ0)
      linarith
    linarith
  have ht0 : 0 < t := lt_of_lt_of_le hτ0 hτt
  have hts' : t ≤ s' := gm_s4T_le_s4S_succ hε0 hε1.le hβ.le k ω
  have hs'2 : s' ≤ tauR D h 𝕫 (2 * (R.ℓ * 𝕣)) ω := by
    refine gm_S4_3 hω hc hξ h𝕣 hℓ ha0 ha1 hχ.le hUV h𝕫 hH0 hH𝕫 ?_
    have hx1 : 1 ≤ a / regC2const R a * ε ^ (-β) := by
      rw [Real.rpow_neg hε0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hε0 _)]
      linarith
    have hk1 : ((k + 1 : ℕ) : ℝ) ≤ a / regC2const R a * ε ^ (-β) := by
      have h1 : k + 1 ≤ ⌊a / regC2const R a * ε ^ (-β)⌋₊ := by
        have := Nat.one_le_floor_iff _ |>.2 hx1
        unfold p4K at hk; omega
      exact (Nat.cast_le.2 h1).trans (Nat.floor_le (by positivity))
    calc ((k + 1 : ℕ) : ℝ) * ε ^ β ≤ a / regC2const R a * ε ^ (-β) * ε ^ β :=
          mul_le_mul_of_nonneg_right hk1 hεβ0
      _ = a / regC2const R a := by
          rw [Real.rpow_neg hε0.le, mul_assoc, inv_mul_cancel₀ (Real.rpow_pos_of_pos hε0 _).ne',
            mul_one]
  have h2𝕫 := h2 𝕫 h𝕫R
  have hs'3 : s' < tauR D h 𝕫 (3 * (R.ℓ * 𝕣)) ω := by
    have hpos : 0 < a * max (R.c 𝕣 * Real.exp (R.ξ * H 𝕣 𝕫 ω))
        (R.c (R.ℓ * 𝕣) * Real.exp (R.ξ * H (R.ℓ * 𝕣) 𝕫 ω)) :=
      mul_pos ha0 (lt_of_lt_of_le (mul_pos hc (Real.exp_pos _)) (le_max_left _ _))
    have := h2𝕫.2.trans (min_le_right _ _)
    linarith
  -- `K = 𝓑^•_t ⊆ B_{3ℓ𝕣}(𝕫)` and `B_{a𝕣}(𝕫) ⊆ K`
  have hKball : filledBall (D (h ω)) 𝕫 t ⊆ ball 𝕫 (3 * (R.ℓ * 𝕣)) :=
    gm_filledBall_subset_ball_of_lt_tauR ht0 (lt_of_le_of_lt hts' hs'3)
  have hballK : ball 𝕫 (a * 𝕣) ⊆ filledBall (D (h ω)) 𝕫 t :=
    h2𝕫.1.trans (gm_filledBall_mono _ _ hτt)
  have hfar : 2 * lam * e < ‖𝕫 - z‖ := by
    by_contra hle
    push_neg at hle
    have hlt : 2 * lam * e < a * 𝕣 := by
      rw [hedef, ← mul_assoc]; exact mul_lt_mul_of_pos_right hεa' h𝕣
    have hzK : z ∈ filledBall (D (h ω)) 𝕫 t := hballK (by
      rw [mem_ball, dist_eq_norm, norm_sub_rev]; linarith)
    rw [infDist_zero_of_mem hzK] at hz1
    exact absurd hz1 (not_le.2 (by positivity))
  -- `z` is close to `K`
  have hKne : (filledBall (D (h ω)) 𝕫 t).Nonempty := ⟨𝕫, hballK (mem_ball_self (by positivity))⟩
  have hKc : IsCompact (filledBall (D (h ω)) 𝕫 t) :=
    Metric.isCompact_of_isClosed_isBounded (gm_filledBall_isClosed _ _ _)
      (isBounded_ball.subset hKball)
  obtain ⟨y, hyK, hyz'⟩ := hKc.exists_infDist_eq_dist hKne z
  have hyz : dist z y ≤ 2 * lam * e := hyz' ▸ hz2
  have hy𝕫 : dist y 𝕫 < 3 * (R.ℓ * 𝕣) := hKball hyK
  -- Hölder upper bound on the circle
  have hHol : ∀ u ∈ sphere z (2 * lam * e), ∀ v : ℂ, u ≠ v → ‖u - v‖ ≤ e / 2 →
      (D (h ω)).internal (ball u (2 * ‖u - v‖)) u v ≤
        ENNReal.ofReal ((‖u - v‖ / 𝕣) ^ R.χ * S) := by
    intro u' hu' v huv hd
    have hu'z : dist u' z = 2 * lam * e := mem_sphere.1 hu'
    have hkey : (4 * lam + 1) * e < R.ℓ * 𝕣 := by
      rw [hedef]; have := mul_lt_mul_of_pos_right hεℓ' h𝕣; linarith
    have hu'𝕫 : dist u' 𝕫 < 4 * (R.ℓ * 𝕣) - e / 2 := by
      have := dist_triangle4 u' z y 𝕫
      linarith
    refine gm_regC3_upper h3 h𝕣 hS (hreg u' (by linarith [he])) (hreg v ?_) ?_ huv
    · have := dist_triangle v u' 𝕫
      rw [dist_eq_norm v u', norm_sub_rev] at this
      linarith
    · have hεl : ε < lam * ε := lt_mul_of_one_lt_left hε0 hlam
      have : e / 2 ≤ a * 𝕣 := by
        rw [hedef]
        have : ε * 𝕣 ≤ a * 𝕣 := mul_le_mul_of_nonneg_right (by linarith) h𝕣.le
        linarith
      linarith
  -- the gap (4.40)
  have hgap : t + ⌈8 * Real.pi * (2 * lam * e) / e⌉₊ * ((e / 4 / 𝕣) ^ R.χ * S) +
      (e / 2 / 𝕣) ^ R.χ * S < s' := by
    have hN : ⌈8 * Real.pi * (2 * lam * e) / e⌉₊ = N := by
      rw [hNdef]; congr 1; field_simp; ring
    rw [hN, show e / 4 / 𝕣 = ε / 4 by rw [hedef]; field_simp,
      show e / 2 / 𝕣 = ε / 2 by rw [hedef]; field_simp]
    have h4 : (ε / 4) ^ R.χ ≤ ε ^ R.χ :=
      Real.rpow_le_rpow (by positivity) (by linarith) hχ.le
    have h2' : (ε / 2) ^ R.χ ≤ ε ^ R.χ :=
      Real.rpow_le_rpow (by positivity) (by linarith) hχ.le
    have hs't : s' - t = τ * (ε ^ β - ε ^ (2 * β)) := by
      simp only [hs'def, htdef, s4T, s4S, s4Unit]; rw [← hτdef]; push_cast; ring
    have hgap0' : ((N : ℝ) + 1) * ε ^ R.χ < (a / 2) ^ R.χ' * (ε ^ β - ε ^ (2 * β)) := by
      have := hgap0
      rw [div_mul_eq_mul_div, div_lt_iff₀ ha2] at this
      linarith
    have hdiff0 : 0 ≤ ε ^ β - ε ^ (2 * β) := by
      have : ε ^ (2 * β) ≤ ε ^ β :=
        Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
      linarith
    have : ((N : ℝ) + 1) * ε ^ R.χ * S < τ * (ε ^ β - ε ^ (2 * β)) := by
      calc ((N : ℝ) + 1) * ε ^ R.χ * S < (a / 2) ^ R.χ' * (ε ^ β - ε ^ (2 * β)) * S :=
            mul_lt_mul_of_pos_right hgap0' hS
        _ = (a / 2) ^ R.χ' * S * (ε ^ β - ε ^ (2 * β)) := by ring
        _ ≤ τ * (ε ^ β - ε ^ (2 * β)) := mul_le_mul_of_nonneg_right hτ hdiff0
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have k1 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hN0 hS.le)
    have k2 := mul_le_mul_of_nonneg_right h2' hS.le
    linarith
  have hN : ⌈8 * Real.pi * (2 * lam * e) / e⌉₊ = N := by
    rw [hNdef]; congr 1; field_simp; ring
  have he4 : e / 4 / 𝕣 = ε / 4 := by rw [hedef]; field_simp
  refine ⟨gm_filledBall_subset_ball_of_lt_tauR (lt_of_lt_of_le ht0 hts') hs'3, ?_, hfar, ?_⟩
  · have := hgap
    rw [hN, he4] at this
    have : 0 ≤ (e / 2 / 𝕣) ^ R.χ * S := by positivity
    linarith
  · intro u hu
    have hmain := gm_L4_22_det (D (h ω)) hlam he h𝕣 hχ hS.le ht0 hL (hbd t) hgeod hz1
      ⟨y, hyK, hyz⟩ hfar hHol hgap u hu
    rw [hN, he4] at hmain
    exact hmain


theorem gm_L4_16U
    {a β : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ ℓN) (hχ : 0 < χN) (hχ' : 0 < χ'N)
    (hβ : 0 < β) (hβχ : β < χN) (hlam : 1 < lamN 3) (hUV : UN ⊆ VN)
    (hξ : 0 ≤ ξN) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ R : RegPar, RegNum R ξN cN pN χN χ'N μN νN lamN ℓN UN VN →
    ∀ {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC}
    {H : ℝ → ℂ → Ω → ℝ} {𝕣 : ℝ}, 0 < 𝕣 → 0 < R.c 𝕣 → ∀ ε ∈ Ioo (0 : ℝ) ε₁, ∀ ω ∈ regEvent D P h H R 𝕣 a,
    ∀ 𝕫 ∈ rScale 𝕣 R.U, H 𝕣 0 ω = circleAvg (h ω) 𝕣 0 → H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫 →
    (D (h ω)).IsLength → (∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) →
    (∀ y, ∃ Q : ℝ → ℂ, IsGeodesicL (D (h ω)) Q ((D (h ω)).1 (𝕫, y)) 𝕫 y) →
    ∀ k ≤ p4K R a ε β, ∀ (z : ℂ) (r : ℝ) (Rads : Set ℝ),
      (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) (R.lam 0) (R.lam 3)
        ε R.ν 𝕣 Rads → r ∈ Ioc 0 (ε * 𝕣) →
      ∀ (x : ℂ) (Q : ℝ → ℂ) (T : ℝ), IsAvoidGeod (D (h ω)) 𝕫 z r x Q T →
        (D (h ω)).len Q 0 T ≠ ⊤ →
      ∀ s₁ ∈ Icc 0 T, ∀ s₂ ∈ Icc 0 T,
        ENNReal.ofReal (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) ≤ (D (h ω)).len Q 0 s₁ →
        ENNReal.ofReal (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) ≤ (D (h ω)).len Q 0 s₂ →
        ‖Q s₁ - Q s₂‖ ≤ 2 * (𝕣 * (⌈16 * Real.pi * R.lam 3⌉₊ * (ε / 4) ^ R.χ) ^ (1 / R.χ')) +
          8 * R.lam 3 * (ε * 𝕣) := by
  obtain ⟨ε₁, hε₁, H22⟩ := gm_L4_22U (ξN := ξN) (cN := cN) (pN := pN)
    (χN := χN) (χ'N := χ'N) (μN := μN) (νN := νN) (lamN := lamN) (ℓN := ℓN) (UN := UN) (VN := VN)
    ha0 ha1 haℓ hχ
    hχ' hβ hβχ hlam hUV  hξ
  set N := ⌈16 * Real.pi * lamN 3⌉₊ with hNdef
  -- smallness: `N (ε/4)^χ < a^{χ'}`
  have hsm : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (N : ℝ) * (ε / 4) ^ χN < a ^ χ'N := by
    have hcont : ContinuousAt (fun ε : ℝ => (N : ℝ) * (ε / 4) ^ χN) 0 :=
      continuousAt_const.mul ((Real.continuousAt_rpow_const _ _ (Or.inr hχ.le)).comp
        (continuousAt_id.div_const 4))
    have h0 : (N : ℝ) * ((0 : ℝ) / 4) ^ χN = 0 := by
      simp [Real.zero_rpow hχ.ne']
    have := hcont.tendsto
    rw [h0] at this
    exact (this.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (by positivity))
  have hev := hsm.and (Ioo_mem_nhdsGT hε₁ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 ε₁)
  obtain ⟨ε₂, hε₂, hε₂'⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
  refine ⟨ε₂, hε₂, ?_⟩
  intro R hRN Ω _ D P h H 𝕣 h𝕣 hc
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hRN
  replace H22 := H22 R (regNum_self R) (D := D) (P := P) (h := h) (H := H) h𝕣 hc
  try simp only [regC2N_eq] at *
  try rw [← hNdef]
  intro ε hε ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd hgeod k hk z r Rads hzr hr x Q T hQ hfin
  obtain ⟨hsmallε, hεε₁⟩ := hε₂' hε
  have hε0 : 0 < ε := hε.1
  set K := filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) with hKdef
  obtain ⟨_, hzK, _, hzd⟩ := hzr
  have hKne : K.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, frontier_empty, infDist_empty] at hzd
    have hl0 : 0 < R.lam 3 := by linarith
    have : 0 < R.lam 3 * ε * 𝕣 := by positivity
    linarith [hzd.1]
  rw [gm_infDist_frontier_eq (gm_filledBall_isClosed _ _ _) hKne hzK] at hzd
  have hz1 : R.lam 3 * (ε * 𝕣) ≤ infDist z K := by rw [← mul_assoc]; exact hzd.1
  have hz2 : infDist z K ≤ 2 * R.lam 3 * (ε * 𝕣) := by
    have := hzd.2; rw [show 2 * R.lam 3 * ε * 𝕣 = 2 * R.lam 3 * (ε * 𝕣) by ring] at this
    exact this
  obtain ⟨hsub, hgap, hfar, hcirc⟩ :=
    H22 ε hεε₁ ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd hgeod k hk z hz1 hz2
  obtain ⟨_, _, h3, _, _, _, _⟩ := gm_regEvent_mem.1 hω
  set S := scaleFac R.ξ R.c (h ω) 𝕣 0 with hSdef
  have hS : 0 < S := mul_pos hc (Real.exp_pos _)
  have he : 0 < ε * 𝕣 := mul_pos hε0 h𝕣
  have hρe : ε * 𝕣 < 2 * R.lam 3 * (ε * 𝕣) := by nlinarith
  have ht0 : 0 ≤ s4T D h 𝕫 R.ℓ 𝕣 ε β k ω := by
    have h1 := gm_s4S_le_s4T (D := D) (h := h) (𝕫 := 𝕫) (ℓ := R.ℓ) (𝕣 := 𝕣) (β := β) hε0 k ω
    have h2 : 0 ≤ s4S D h 𝕫 R.ℓ 𝕣 ε β k ω :=
      mul_nonneg (gm_s4Unit_nonneg ω) (by positivity)
    linarith
  -- Hölder lower bound on `𝓑_{s_{k+1}}`
  have h𝕫V : 𝕫 ∈ rScale 𝕣 R.V := image_mono hUV h𝕫
  have hreg : ∀ y ∈ ballM (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω), y ∈ regRegion R 𝕣 := by
    intro y hy
    have hy' : dist y 𝕫 < 3 * (R.ℓ * 𝕣) := hsub (Or.inl (subset_closure hy))
    refine Metric.mem_thickening_iff.2 ⟨𝕫, h𝕫V, ?_⟩
    have : 0 < R.ℓ * 𝕣 := mul_pos (lt_of_lt_of_le ha0 haℓ) h𝕣
    linarith
  have hHolLow : ∀ u ∈ ballM (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω),
      ∀ v ∈ ballM (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω), ‖u - v‖ ≤ a * 𝕣 →
      (‖u - v‖ / 𝕣) ^ R.χ' * S ≤ (D (h ω)).1 (u, v) := fun u hu v hv huv =>
    gm_regC3_lower h3 h𝕣 hS (hreg u hu) (hreg v hv) huv
  have hB0 : 0 ≤ (N : ℝ) * ((ε / 4) ^ R.χ * S) := by positivity
  have hsmall : (N : ℝ) * ((ε / 4) ^ R.χ * S) < (a * 𝕣 / 𝕣) ^ R.χ' * S := by
    rw [show a * 𝕣 / 𝕣 = a by field_simp, ← mul_assoc]
    exact mul_lt_mul_of_pos_right hsmallε hS
  have hmain := gm_L4_16_of_439 (D (h ω)) he hρe h𝕣 hS ht0 hB0 hgap hfar hcirc hr.1 hr.2 hQ
    hfin hχ' (mul_pos ha0 h𝕣) hHolLow hsmall
  intro s₁ hs₁ s₂ hs₂ ht₁ ht₂
  have := hmain s₁ hs₁ s₂ hs₂ ht₁ ht₂
  rw [show (N : ℝ) * ((ε / 4) ^ R.χ * S) / S = N * (ε / 4) ^ R.χ by field_simp] at this
  linarith


theorem p412b_stab_of_extU
    {a β : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ ℓN) (hχ : 0 < χN) (hχ' : 0 < χ'N)
    (hβ : 0 < β) (hβχ : β < χN) (hlam : 1 < lamN 3) (hUV : UN ⊆ VN)
    (hξ : 0 ≤ ξN) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ R : RegPar, RegNum R ξN cN pN χN χ'N μN νN lamN ℓN UN VN →
    ∀ {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC}
    {H : ℝ → ℂ → Ω → ℝ} {𝕣 : ℝ}, 0 < 𝕣 → 0 < R.c 𝕣 → ∀ ε ∈ Ioo (0 : ℝ) ε₁, ∀ ω ∈ regEvent D P h H R 𝕣 a,
    ∀ 𝕫 ∈ rScale 𝕣 R.U, H 𝕣 0 ω = circleAvg (h ω) 𝕣 0 → H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫 →
    (D (h ω)).IsLength → (∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) →
    (∀ y, ∃ Q : ℝ → ℂ, IsGeodesicL (D (h ω)) Q ((D (h ω)).1 (𝕫, y)) 𝕫 y) →
    ∀ k ≤ p4K R a ε β, ∀ (z : ℂ) (r : ℝ) (Rads : Set ℝ),
      (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) (R.lam 0) (R.lam 3)
        ε R.ν 𝕣 Rads → r ∈ Ioc 0 (ε * 𝕣) →
      (∀ (x : ℂ) (Q : ℝ → ℂ) (T : ℝ), IsAvoidGeod (D (h ω)) 𝕫 z r x Q T →
        (D (h ω)).len Q 0 T ≠ ⊤) →
      ∀ x₀ ∈ confPts (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω),
      ∀ p ∈ closedBall z r, ∀ ρ : ℝ,
      (∀ v ∈ frontier (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) \
          arcOf (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) x₀,
        ENNReal.ofReal ρ ≤ dU (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω))ᶜ p v) →
      2 * (𝕣 * (⌈16 * Real.pi * R.lam 3⌉₊ * (ε / 4) ^ R.χ) ^ (1 / R.χ')) +
          8 * R.lam 3 * (ε * 𝕣) + 2 * r < ρ →
      stabCond (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) z r := by
  obtain ⟨ε₁, hε₁, H16⟩ := gm_L4_16U (ξN := ξN) (cN := cN) (pN := pN)
    (χN := χN) (χ'N := χ'N) (μN := μN) (νN := νN) (lamN := lamN) (ℓN := ℓN) (UN := UN) (VN := VN)
    ha0 ha1 haℓ hχ
    hχ' hβ hβχ hlam hUV  hξ
  refine ⟨ε₁, hε₁, ?_⟩
  intro R hRN Ω _ D P h H 𝕣 h𝕣 hc
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hRN
  replace H16 := H16 R (regNum_self R) (D := D) (P := P) (h := h) (H := H) h𝕣 hc
  try simp only [regC2N_eq] at *
  refine fun ε hε ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd hgeod k hk z r Rads hcand hr hfin x₀ hx₀
    p hp ρ hext hρ => ⟨x₀, hx₀, fun x Q T hQ => ?_⟩
  have hε0 : 0 < ε := hε.1
  have hr' : r < R.lam 3 * ε * 𝕣 := by
    have : ε * 𝕣 < R.lam 3 * ε * 𝕣 := by
      have := mul_pos hε0 h𝕣; nlinarith
    linarith [hr.2]
  have hdisj := p412b_disj_of_cand (gm_filledBall_isClosed _ _ _) hcand hr.1.le hr'
  exact p412_hit_mem_of_dU hQ (hfin x Q T hQ) hgeod (hbd _) hdisj hp
    (H16 ε hε ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd hgeod k hk z r Rads hcand hr x Q T hQ (hfin x Q T hQ))
    hext hρ

end LQGMetric.GM
