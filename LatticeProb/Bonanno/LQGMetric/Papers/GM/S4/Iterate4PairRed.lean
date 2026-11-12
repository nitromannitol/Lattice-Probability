/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate4PairRed at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4Pair

/-!
# GM Theorem 4.2 for one pair: general `λ₃` and general `ε` (DEC-89, packet D)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, l. 1611 ("we assume `λ₃ = 1`;
the proof when `λ₃ ≠ 1` is identical, just with extra factors of `λ₃` in various subscripts").
Decision `decisions/DEC-89.md` (D89b, own argument DV-D89b): `T4_2Pair` from `T4_2PairOne` by
* the scaling of the radius variable `r' = r/λ₃` (`gm_geoIterateHyp_scale` with `s = λ₃⁻¹`, base
  scale `𝕣/s`, `U' = sU`, `ℓ' = min(ℓs, 1/2)`), which makes `λ'₃ = 1`;
* a reparametrization of the scale variable `ε'' ↦ θε''` with `θ = ε/ε' ∈ (1/2, 1]`, `ε' ∈ [ε, 2ε)`
  dyadic (`gm_geoIterateHyp_reparam`, at the price `ν ↦ 2ν` and a smaller `ε₀`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the radii of (1) under the scaling `r' = r/s` -/
theorem gm_T42Radii_scale {lam : Fin 5 → ℝ} {μ ν R ε₀ : ℝ} {Rad : Set ℝ}
    {rr : ℝ → ℝ → ℕ → ℝ} {s : ℝ} (hs : 0 < s) (H : T42Radii lam μ ν R ε₀ Rad rr) :
    T42Radii (fun i => s * lam i) μ ν (R / s) ε₀ {r | s * r ∈ Rad}
      (fun _ ε k => rr R ε k / s) := by
  intro ε hε
  obtain ⟨h1, h2⟩ := H ε hε
  refine ⟨fun k hk => ⟨⟨?_, ?_⟩, ?_⟩, fun k hk => ?_⟩
  · rw [mul_div_assoc', div_le_div_iff_of_pos_right hs]; exact (h1 k hk).1.1
  · rw [mul_div_assoc', div_le_div_iff_of_pos_right hs]; exact (h1 k hk).1.2
  · show s * (rr R ε k / s) ∈ Rad
    rw [mul_div_cancel₀ _ hs.ne']; exact (h1 k hk).2
  · have := h2 k hk
    have e1 : s * lam 3 / (s * lam 0) = lam 3 / lam 0 := mul_div_mul_left _ _ hs.ne'
    have e2 : rr R ε k / s / (rr R ε (k + 1) / s) = rr R ε k / rr R ε (k + 1) :=
      div_div_div_cancel_right₀ hs.ne' _ _
    simp only [e1, e2]; exact this

/-- the number of radii of (1) decreases with `ε` -/
theorem gm_floor_count_mono {μ ε θ : ℝ} (hμ : 0 ≤ μ) (hε : 0 < ε) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ⌊μ * Real.logb 8 ε⁻¹⌋₊ ≤ ⌊μ * Real.logb 8 (θ * ε)⁻¹⌋₊ :=
  Nat.floor_mono (mul_le_mul_of_nonneg_left (Real.logb_le_logb_of_le (by norm_num)
    (inv_pos.2 hε) (inv_anti₀ (mul_pos hθ hε) (mul_le_of_le_one_left hε.le hθ1))) hμ)

/-- **reparametrization of the scale variable** (D89b): the hypotheses of T4.2 with `ν`, `ε₀`
give those with `2ν`, `ε₀' ≤ min(ε₀, 2^{-(1+ν)/ν})`, radii `r_k(θε)` for `θ ∈ (1/2, 1]` -/
theorem gm_geoIterateHyp_reparam {D : DistC → ContMetric}
    {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)} {μ ν : ℝ} {lam : Fin 5 → ℝ} {𝕡 R ε₀ Λ : ℝ}
    {Rad : Set ℝ} {E : ℝ → ℂ → Set DistC} {Ef : ℝ → ℂ → ℂ → ℂ → Set DistC}
    {rr : ℝ → ℝ → ℕ → ℝ} (H : GeoIterateHyp D sel μ ν lam 𝕡 R ε₀ Λ Rad E Ef)
    (hrr : T42Radii lam μ ν R ε₀ Rad rr) (hμ : 0 ≤ μ) (hν : 0 < ν) (hR : 0 < R) {θ ε₀' : ℝ}
    (hθ : θ ∈ Ioc (1 / 2 : ℝ) 1) (hε₀' : ε₀' ≤ ε₀) (hc : ε₀' ≤ (2 : ℝ)⁻¹ ^ ((1 + ν) / ν)) :
    GeoIterateHyp D sel μ (2 * ν) lam 𝕡 R ε₀' Λ (Rad ∩ Iic (ε₀' * R)) E Ef ∧
      T42Radii lam μ (2 * ν) R ε₀' (Rad ∩ Iic (ε₀' * R)) (fun R' ε k => rr R' (θ * ε) k) := by
  obtain ⟨hRad, hΛ, hE, hEf, -, hP⟩ := H
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have key : T42Radii lam μ (2 * ν) R ε₀' (Rad ∩ Iic (ε₀' * R))
      (fun R' ε k => rr R' (θ * ε) k) := by
    intro ε hε
    have hθε : θ * ε ∈ Ioc (0 : ℝ) ε₀ :=
      ⟨mul_pos hθ0 hε.1, (mul_le_of_le_one_left hε.1.le hθ.2).trans (hε.2.trans hε₀')⟩
    obtain ⟨h1', h2'⟩ := hrr (θ * ε) hθε
    have hcnt := gm_floor_count_mono hμ hε.1 hθ0 hθ.2
    refine ⟨fun k hk => ?_, fun k hk => h2' k (lt_of_lt_of_le hk hcnt)⟩
    obtain ⟨⟨hl, hu⟩, hmem⟩ := h1' k (lt_of_lt_of_le hk hcnt)
    have hup : rr R (θ * ε) k ≤ ε * R :=
      hu.trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hε.1.le hθ.2) hR.le)
    refine ⟨⟨le_trans (mul_le_mul_of_nonneg_right ?_ hR.le) hl, hup⟩, hmem,
      hup.trans (mul_le_mul_of_nonneg_right hε.2 hR.le)⟩
    have h1 : ε ^ ν ≤ θ ^ (1 + ν) := by
      calc ε ^ ν ≤ ((2 : ℝ)⁻¹ ^ ((1 + ν) / ν)) ^ ν :=
            Real.rpow_le_rpow hε.1.le (hε.2.trans hc) hν.le
        _ = (2 : ℝ)⁻¹ ^ (1 + ν) := by
            rw [← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ hν.ne']
        _ ≤ θ ^ (1 + ν) :=
            Real.rpow_le_rpow (by norm_num) (by linarith [hθ.1]) (by linarith)
    rw [Real.mul_rpow hθ0.le hε.1.le, show 1 + 2 * ν = ν + (1 + ν) by ring,
      Real.rpow_add hε.1]
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hε.1.le _)
  refine ⟨⟨fun r hr => ⟨(hRad hr.1).1, hr.2⟩, hΛ, hE, hEf,
    fun ε hε => ⟨fun k => rr R (θ * ε) k, (key ε hε).1, (key ε hε).2⟩,
    fun {Ω} _ P _ h hh => ?_⟩, key⟩
  obtain ⟨hg, h2, h2f, h3, h4⟩ := hP P h hh
  exact ⟨hg, fun z r hr => h2 z r hr.1, fun z r hr => h2f z r hr.1, fun z r hr => h3 z r hr.1,
    fun z r hr => h4 z r hr.1⟩

/-- **packet D** (D89b, own argument DV-D89b): `T4_2Pair` from `T4_2PairOne` -/
theorem gm_T4_2Pair_of_one (H : T4_2PairOne) : T4_2Pair := by
  intro γ D c hγ hγ2 hD sel hsel
  obtain ⟨νs₁, hνs₁, H1⟩ := H hγ hγ2 hD sel hsel
  refine ⟨νs₁ / 2, ⟨by linarith [hνs₁.1], by linarith [hνs₁.2]⟩,
    fun {μ ν} hμ hμν hν lam h0 h01 h12 h23 h34 => ?_⟩
  have hl2 : 0 < lam 2 := by linarith
  have hν0 : 0 < ν := hμ.trans hμν
  set s : ℝ := (lam 2)⁻¹ with hsdef
  have hs : 0 < s := inv_pos.2 hl2
  obtain ⟨𝕡, h𝕡, H2⟩ := H1 (ν := 2 * ν) hμ (by linarith) (by linarith) (fun i => s * lam i)
    (mul_pos hs h0) (mul_lt_mul_of_pos_left h01 hs) (mul_le_mul_of_nonneg_left h12 hs.le)
    (le_of_eq (inv_mul_cancel₀ hl2.ne')) ((one_lt_inv_mul₀ hl2).2 h23)
    (mul_lt_mul_of_pos_left h34 hs)
  refine ⟨𝕡, h𝕡, fun ℓ U hℓ hU hUb ε₀ Λ η M hε₀ hη hM => ?_⟩
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  set U' : Set ℂ := (fun x : ℂ => (s : ℂ) * x) '' U with hU'def
  have hU' : IsOpen U' := (Homeomorph.mulLeft₀ (s : ℂ) hsC).isOpenMap U hU
  have hU'b : Bornology.IsBounded U' := by
    obtain ⟨C, hC⟩ := hUb.exists_norm_le
    refine isBounded_iff_forall_norm_le.2 ⟨s * C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
    exact mul_le_mul_of_nonneg_left (hC x hx) hs.le
  set ℓ' : ℝ := min (ℓ * s) (1 / 2) with hℓ'def
  have hℓ' : ℓ' ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_min (mul_pos hℓ.1 hs) (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩
  set ε₀' : ℝ := min ε₀ ((2 : ℝ)⁻¹ ^ ((1 + ν) / ν)) with hε₀'def
  have hε₀' : 0 < ε₀' := lt_min hε₀ (Real.rpow_pos_of_pos (by norm_num) _)
  obtain ⟨C, ε₁, hC, hε₁, H3⟩ := H2 ℓ' U' hℓ' hU' hU'b ε₀' Λ η M hε₀' hη hM
  refine ⟨C * 2 ^ M, min (ε₁ / 2) 1, by positivity, lt_min (by positivity) one_pos, ?_⟩
  intro R Rad E Ef rr hR hGeo hrr Ω _ P _ h hh ε hε
  have hεpos := hε.1
  have hε1 : ε ≤ 1 := (hε.2.trans_le (min_le_right _ _)).le
  have hεε₁ : 2 * ε < ε₁ := by
    have := hε.2.trans_le (min_le_left _ _); linarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one hεpos hε1
    (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
  set ε' : ℝ := (2 : ℝ)⁻¹ ^ n with hε'def
  have hε'pos : 0 < ε' := pow_pos (by norm_num) n
  have hε'2 : ε' < 2 * ε := by
    have : (2 : ℝ)⁻¹ ^ (n + 1) = ε' / 2 := by rw [pow_succ]; ring
    rw [this] at hn1; linarith
  set θ : ℝ := ε / ε' with hθdef
  have hθ : θ ∈ Ioc (1 / 2 : ℝ) 1 := by
    refine ⟨?_, (div_le_one hε'pos).2 hn2⟩
    rw [hθdef, lt_div_iff₀ hε'pos]; linarith
  have hθε' : θ * ε' = ε := div_mul_cancel₀ _ hε'pos.ne'
  have hRs : 0 < R / s := div_pos hR hs
  obtain ⟨hGeo2, hrr2⟩ := gm_geoIterateHyp_reparam (gm_geoIterateHyp_scale hs hGeo)
    (gm_T42Radii_scale hs hrr) hμ.le hν0 hRs hθ (min_le_left _ _) (min_le_right _ _)
  obtain ⟨Reg, hReg, Hp⟩ := H3 (R / s) _ _ _ _ hRs hGeo2 hrr2 P h hh n (hε'2.trans hεε₁)
  refine ⟨Reg, hReg, fun 𝕫 𝕨 h𝕫 h𝕨 h𝕫𝕨 => ?_⟩
  have hU1 : ∀ x : ℂ, x ∈ (fun y => (R : ℂ) * y) '' U →
      x ∈ (fun y => ((R / s : ℝ) : ℂ) * y) '' U' := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨(s : ℂ) * y, ⟨y, hy, rfl⟩, ?_⟩
    simp only
    push_cast
    field_simp
  have hadm : ℓ' * (R / s) ≤ ‖𝕫 - 𝕨‖ := by
    refine le_trans ?_ h𝕫𝕨
    have : ℓ' * (R / s) ≤ ℓ * s * (R / s) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hRs.le
    refine this.trans (le_of_eq ?_)
    field_simp
  have Hb := Hp 𝕫 𝕨 (hU1 𝕫 h𝕫) (hU1 𝕨 h𝕨) hadm
  have hcnt := gm_floor_count_mono hμ.le hε'pos (by linarith [hθ.1] : (0 : ℝ) < θ) hθ.2
  rw [hθε'] at hcnt
  have hsub : Reg ∩ {ω | ¬ t42Wit sel h Ef lam rr μ R ε 𝕫 𝕨 ω} ⊆
      Reg ∩ {ω | ¬ t42Wit sel h (fun r z a b => Ef (s * r) z a b) (fun i => s * lam i)
        (fun R' ε k => rr R (θ * ε) k / s) μ (R / s) ε' 𝕫 𝕨 ω} := by
    refine inter_subset_inter_right _ fun ω hω hw => hω ?_
    obtain ⟨z, k, hk, hhit, hEf, hza, hzb⟩ := hw
    simp only [hθε'] at hhit hEf hza hzb
    have e : ∀ i : Fin 5, s * lam i * (rr R ε k / s) = lam i * rr R ε k := fun i => by
      field_simp
    rw [e] at hhit hza hzb
    rw [mul_div_cancel₀ _ hs.ne'] at hEf
    exact ⟨z, k, lt_of_lt_of_le hk hcnt, hhit, hEf, hza, hzb⟩
  calc P.real (Reg ∩ {ω | ¬ t42Wit sel h Ef lam rr μ R ε 𝕫 𝕨 ω})
      ≤ P.real (Reg ∩ {ω | ¬ t42Wit sel h (fun r z a b => Ef (s * r) z a b) (fun i => s * lam i)
        (fun R' ε k => rr R (θ * ε) k / s) μ (R / s) ε' 𝕫 𝕨 ω}) := measureReal_mono hsub
    _ ≤ C * ε' ^ M := Hb
    _ ≤ C * (2 * ε) ^ M :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hε'pos.le hε'2.le hM.le) hC
    _ = C * 2 ^ M * ε ^ M := by
        rw [Real.mul_rpow (by norm_num) hεpos.le]; ring

end LQGMetric.GM
