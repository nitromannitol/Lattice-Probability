/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L14 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L13

/-!
# DG Lemma 3.14 (rectangle distances at all scales `2^{-m} ≤ ε^β`) (P2-DG105i)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.14
(`lem-rectangle-dist-multi`, DG:1328–1343). DG's proof (DG:1338–1342): Lemma 3.5 gives
`max |ĥ_{2^{-m}}| ≤ (2+ζ) log 2^m` with exponentially high probability in `m`; combined with
Lemma 3.13 (`dg_lemma313_core`), a union bound over `m ≥ log₂ ε^{-β}` and "possibly shrinking `ζ`"
(here: Lemma 3.13 at `ζ/(1+γ)`).

The rectangles are the abstract family of `dg_lemma313_core`. Deviation: as in Lemma 3.13,
`ε ∈ (0,ε₀)` with `ε₀ ≤ 1` (DG's "polynomially high probability as `ε → 0`").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the bound of Lemma 3.13 at `ζ/(1+γ)` is at most that of Lemma 3.14 when
`min ĥ_{2^{-m}} ≤ (2 + ζ/(1+γ)) m log 2` (DG:1338–1342) -/
lemma l314_tgt_le {γ d ζ ε x : ℝ} {m : ℕ} (hγ : 0 < γ) (hd : 1 ≤ d) (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hx : x ≤ (2 + ζ / (1 + γ)) * m * Real.log 2) :
    l313Tgt γ d (ζ / (1 + γ)) ε m x ≤ max ((m : ℝ) ^ 3)
      (ε ^ (-(1 / (d - ζ))) * (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - 2 * γ - ζ) * m / d))) := by
  unfold l313Tgt
  refine max_le_max le_rfl ?_
  have hζ' : ζ / (1 + γ) ≤ ζ := div_le_self hζ.le (by linarith)
  have h1 : ε ^ (-(1 / (d - ζ / (1 + γ)))) ≤ ε ^ (-(1 / (d - ζ))) := by
    refine Real.rpow_le_rpow_of_exponent_ge hε hε1 ?_
    have : 1 / (d - ζ / (1 + γ)) ≤ 1 / (d - ζ) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  have h2 : (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - ζ / (1 + γ)) * m / d)) * Real.exp (γ / d * x) ≤
      (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - 2 * γ - ζ) * m / d)) := by
    rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos (by norm_num), ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hd0 : 0 < d := by linarith
    have hγd : 0 ≤ γ / d := by positivity
    have := mul_le_mul_of_nonneg_left hx hγd
    have e : ζ / (1 + γ) * (1 + γ) = ζ := by field_simp
    have e2 : Real.log 2 * -((2 + γ ^ 2 / 2 - ζ / (1 + γ)) * m / d) +
        γ / d * ((2 + ζ / (1 + γ)) * m * Real.log 2) =
        Real.log 2 * -((2 + γ ^ 2 / 2 - 2 * γ - ζ / (1 + γ) * (1 + γ)) * m / d) := by
      field_simp; ring
    rw [e] at e2
    linarith
  calc ε ^ (-(1 / (d - ζ / (1 + γ)))) * (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - ζ / (1 + γ)) * m / d)) *
        Real.exp (γ / d * x)
      = ε ^ (-(1 / (d - ζ / (1 + γ)))) * ((2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - ζ / (1 + γ)) * m / d)) *
        Real.exp (γ / d * x)) := by ring
    _ ≤ ε ^ (-(1 / (d - ζ))) * (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - 2 * γ - ζ) * m / d)) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)

/-- **DG Lemma 3.14** (DG:1328–1343), for the abstract rectangle family of `dg_lemma313_core`:
with polynomially high probability as `ε → 0`, for every `m` with `2^{-m} ≤ ε^β` and every
`u ∈ Λ m`, `D m u ε ≤ max{m³, ε^{-1/(d−ζ)} 2^{-(2+γ²/2−2γ−ζ)m/d}}` -/
theorem dg_lemma314_core (hW : IsWhiteNoise P W) {γ d : ℝ} (hγ : 0 < γ) (hd : 1 ≤ d)
    {ι : Type*} {Λ : ℕ → Finset ι} {Cn : ℝ} (hΛ : ∀ m, ((Λ m).card : ℝ) ≤ Cn * 4 ^ m)
    {Rp : ℕ → ι → Set ℂ} {U : Set ℂ} (hU : Bornology.IsBounded U)
    (hRU : ∀ m, ∀ u ∈ Λ m, Rp m u ⊆ U) (hRne : ∀ m, ∀ u ∈ Λ m, (Rp m u).Nonempty)
    {Cd : ℝ} (hCd : 1 ≤ Cd)
    (hRd : ∀ m, ∀ u ∈ Λ m, ∀ z ∈ Rp m u, ∀ w ∈ Rp m u, ‖z - w‖ ≤ Cd * (2 : ℝ)⁻¹ ^ m)
    {D : ℕ → ι → ℝ → Ω → ℝ≥0∞} (hL : L313Hyp P W γ d Λ Rp D) {ζ β : ℝ} (hζ : 0 < ζ)
    (hζ1 : ζ < 1) (hβ : 0 < β) :
    ∃ p C ε₀ : ℝ, 0 < p ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      P {ω | ∃ m : ℕ, (2 : ℝ)⁻¹ ^ m ≤ ε ^ β ∧ ∃ u ∈ Λ m, ¬ D m u ε ω ≤ ENNReal.ofReal
        (max ((m : ℝ) ^ 3) (ε ^ (-(1 / (d - ζ))) *
          (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - 2 * γ - ζ) * m / d))))} ≤ ENNReal.ofReal (C * ε ^ p) := by
  have := hW.isProbabilityMeasure
  set ζ' := ζ / (1 + γ) with hζ'
  have hζ'0 : 0 < ζ' := by positivity
  have hζ'1 : ζ' < 1 := (div_le_self hζ.le (by linarith)).trans_lt hζ1
  obtain ⟨lam, C₁, hlam, h313⟩ :=
    dg_lemma313_core hW hγ hd hΛ hU hRU hRne hCd hRd hL hζ'0 hζ'1
  obtain ⟨K, δ₅, hδ₅, h35⟩ := dg_lemma35 hW hU hζ'0
  obtain ⟨N₅, hN₅⟩ := exists_pow_lt_of_lt_one hδ₅ (by norm_num : (2 : ℝ)⁻¹ < 1)
  set L := Real.log 2 with hL_def
  have hL0 : 0 < L := Real.log_pos (by norm_num)
  set lm : ℝ := min lam (ζ' * L) with hlm
  have hlm0 : 0 < lm := lt_min hlam (by positivity)
  set r : ℝ := Real.exp (-(lm / 2)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by linarith)
  set c : ℝ := |C₁| + |K| with hc
  refine ⟨β * (lm / (2 * L)), c * (1 - r)⁻¹, ((2 : ℝ)⁻¹ ^ N₅) ^ β⁻¹, by positivity,
    by positivity, fun ε hε hεlt => ?_⟩
  have hεβ : ε ^ β < (2 : ℝ)⁻¹ ^ N₅ := by
    have := Real.rpow_lt_rpow hε.le hεlt hβ
    rwa [Real.rpow_inv_rpow (by positivity) hβ.ne'] at this
  have hε1 : ε ≤ 1 := by
    refine hεlt.le.trans (Real.rpow_le_one (by positivity) ?_ (by positivity))
    exact pow_le_one₀ (by norm_num) (by norm_num)
  -- per scale
  set G : ℕ → Set Ω := fun m => {ω | ∃ u ∈ Λ m, ¬ D m u ε ω ≤ ENNReal.ofReal (l313Tgt γ d ζ' ε m
        (sInf ((fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ m) 1 z ω) '' Rp m u)))}
  set E : ℕ → Set Ω := fun m => {ω | ∃ z ∈ U, (2 + ζ') * Real.log ((2 : ℝ)⁻¹ ^ m)⁻¹ <
    |DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ m) 1 z ω|}
  set F : ℕ → Set Ω := fun m => if (2 : ℝ)⁻¹ ^ m ≤ ε ^ β then G m ∪ E m else ∅
  have hsub : {ω | ∃ m : ℕ, (2 : ℝ)⁻¹ ^ m ≤ ε ^ β ∧ ∃ u ∈ Λ m, ¬ D m u ε ω ≤ ENNReal.ofReal
        (max ((m : ℝ) ^ 3) (ε ^ (-(1 / (d - ζ))) *
          (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - 2 * γ - ζ) * m / d))))} ⊆ ⋃ m, F m := by
    rintro ω ⟨m, hm, u, hu, hbad⟩
    refine mem_iUnion.2 ⟨m, ?_⟩
    simp only [F, if_pos hm]
    by_contra hcon
    simp only [mem_union, not_or, G, E, mem_ofPred_eq, not_exists, not_and, not_not,
      not_lt] at hcon
    obtain ⟨hG, hE⟩ := hcon
    apply hbad
    refine (hG u hu).trans (ENNReal.ofReal_le_ofReal (l314_tgt_le hγ hd hζ hζ1 hε hε1 ?_))
    have hlog : Real.log ((2 : ℝ)⁻¹ ^ m)⁻¹ = m * L := by rw [inv_pow, inv_inv, Real.log_pow]
    obtain ⟨-, h2⟩ := l313_sup_inf (hRne m u hu)
      (f := fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ m) 1 z ω)
      (g := fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ m) 1 z ω)
      (a := (2 + ζ') * (m * L)) (b := 2 * ((2 + ζ') * (m * L)))
      (fun w hw => by have := hE w (hRU m u hu hw); rwa [hlog] at this)
      (fun z hz w hw => by
        have h1 := hE z (hRU m u hu hz); have h2 := hE w (hRU m u hu hw)
        rw [hlog] at h1 h2
        calc _ ≤ |DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ m) 1 z ω| +
              |DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ m) 1 w ω| := abs_sub _ _
          _ ≤ _ := by linarith)
    have := (le_abs_self _).trans h2
    linarith
  have hF : ∀ m, P (F m) ≤ ENNReal.ofReal (c * ε ^ (β * (lm / (2 * L))) * r ^ m) := by
    intro m
    by_cases hm : (2 : ℝ)⁻¹ ^ m ≤ ε ^ β
    · simp only [F, if_pos hm]
      have hmN : N₅ < m := by
        by_contra h; rw [not_lt] at h
        have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num) h
        linarith
      have hδ : (2 : ℝ)⁻¹ ^ m < δ₅ :=
        lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmN.le) hN₅
      have hlogm : Real.log ((2 : ℝ)⁻¹ ^ m) = -(m * L) := by
        rw [Real.log_pow, Real.log_inv]; ring
      -- `e^{-lm m} ≤ ε^{β lm/(2L)} r^m`
      have hkey : Real.exp (-(lm * m)) ≤ ε ^ (β * (lm / (2 * L))) * r ^ m := by
        have h1 : Real.exp (-(lm / 2 * m)) ≤ ε ^ (β * (lm / (2 * L))) := by
          rw [Real.rpow_mul hε.le]
          have h := Real.rpow_le_rpow (by positivity) hm (by positivity : 0 ≤ lm / (2 * L))
          refine le_trans (le_of_eq ?_) h
          rw [Real.rpow_def_of_pos (by positivity), hlogm]
          congr 1; field_simp
        have h2 : r ^ m = Real.exp (-(lm / 2 * m)) := by
          rw [hr, ← Real.exp_nat_mul]; ring_nf
        rw [h2, show -(lm * m) = -(lm / 2 * m) + -(lm / 2 * m) by ring, Real.exp_add]
        exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      refine (measure_union_le _ _).trans ?_
      have hG := h313 m ε hε hε1
      have hE := h35 _ ⟨by positivity, hδ⟩
      refine (add_le_add hG hE).trans ?_
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have b1 : C₁ * Real.exp (-(lam * m)) ≤ |C₁| * Real.exp (-(lm * m)) := by
        refine (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le).trans ?_
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg _)
        have := mul_le_mul_of_nonneg_right (min_le_left lam (ζ' * L)) hm0
        linarith
      have b2 : K * ((2 : ℝ)⁻¹ ^ m) ^ ζ' ≤ |K| * Real.exp (-(lm * m)) := by
        refine (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [Real.rpow_def_of_pos (by positivity), hlogm]
        refine Real.exp_le_exp.2 ?_
        have := mul_le_mul_of_nonneg_right (min_le_right lam (ζ' * L)) hm0
        linarith
      refine (add_le_add (ENNReal.ofReal_le_ofReal b1) (ENNReal.ofReal_le_ofReal b2)).trans ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc |C₁| * Real.exp (-(lm * m)) + |K| * Real.exp (-(lm * m))
          = c * Real.exp (-(lm * m)) := by rw [hc]; ring
        _ ≤ c * (ε ^ (β * (lm / (2 * L))) * r ^ m) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = _ := by ring
    · simp only [F, if_neg hm, measure_empty]; exact zero_le
  refine (measure_mono hsub).trans ((measure_iUnion_le _).trans
    ((ENNReal.tsum_le_tsum hF).trans (le_of_eq ?_)))
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left _), tsum_mul_left,
    tsum_geometric_of_lt_one hr0 hr1]
  congr 1; ring

end DG
end LQGMetric
