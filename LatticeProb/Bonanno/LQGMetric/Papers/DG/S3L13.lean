/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L13 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L13A
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L4Mid

/-!
# DG Lemma 3.13 (rectangle distances, uniformly over dyadic rectangles) (P2-DG105i)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.13
(`lem-rectangle-dist`, DG:1282–1312). DG's proof:
1. (eqn-use-mid-scale-compare) (DG:1296–1299) by Lemmas 3.5 and 3.6 (`dg_lemma35`, `dg_lemma36`
   with `δ = 2^{-m}`, `A = 2^{n_m}`): exponentially likely in `m`;
2. by (3.7) and the independence of `ĥ_{2^{-m-n_m}}` and the rescaled field, the conditional law
   of the distance across `R` is dominated by that of the distance across `ℛ_{2^{n_m}}` at `T_R ε`
   (DG:1300–1305), and Lemma 3.11 bounds it (DG:1310);
3. on the event of 1., `T_R ≥ …` (eqn-rectangle-dist-T) (DG:1303–1309; `l313_thr_le_tgt`);
4. a union bound over `O(2^{2m})` rectangles (DG:1310).

Step 2 (Lemma 3.11 transported to the rectangle `R` at scale `2^{-m-n_m}`, with DG's random
factor `T_R`) is the hypothesis `L313Hyp` (D105 item 1: Lemma 3.11 is stated for `δℛ_n + b`).
The rectangles are an abstract family `Rp m u` (`u ∈ Λ m`, `#Λ m ≤ C 4^m`, diameter `≤ C 2^{-m}`)
with distances `D m u ε ω`, so horizontal and vertical rectangles are two instances.

Deviations: `n_m = 2^{⌊log₂ m⌋ + J + 1} ≍ m` (DG: `≍ m^{3/2}`; DG's own remark DG:1294 allows
any `n_m` with `a₁ n_m ≥ (log 4 + 1) m`, here with `J` depending on `a₁`); `ε ∈ (0, 1]` (DG:
`ε > 0`; for `ε > 1` the factor `ε^{-1/(d−ζ)}` is not monotone in `ζ`, and only `ε → 0` is used).
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

/-- **DG Lemma 3.11 at the rectangles of Lemma 3.13** (DG:1300–1310): for each `ζ₁`, the
distance `D m u ε` across the rectangle `R` with stretched rectangle `Rp m u` exceeds
`2^{2k} max{A, e^{√(2^k)} (T ε)^{-1/(d−ζ₁)}}`, `T = 2^{(2+γ²/2)(m+k)} e^{−γ max_{Rp} ĥ_{2^{-m-k}}}`,
with probability `≤ a₀ e^{−a₁ 2^k}` -/
def L313Hyp (P : Measure Ω) (W : WNSpace → Ω → ℝ) (γ d : ℝ) {ι : Type*} (Λ : ℕ → Finset ι)
    (Rp : ℕ → ι → Set ℂ) (D : ℕ → ι → ℝ → Ω → ℝ≥0∞) : Prop :=
  ∀ ζ₁ : ℝ, 0 < ζ₁ → ζ₁ < 1 → ∃ a₀ a₁ A : ℝ, 0 < a₁ ∧ ∀ m : ℕ, ∀ u ∈ Λ m, ∀ k : ℕ, ∀ ε : ℝ,
    0 < ε → P {ω | ¬ D m u ε ω ≤ ENNReal.ofReal (l313Thr A γ d ζ₁ ε m k
      (sSup ((fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ (m + k)) 1 z ω) '' Rp m u)))} ≤
      ENNReal.ofReal (a₀ * Real.exp (-(a₁ * 2 ^ k)))

/-- `2^J m ≤ 2^{⌊log₂ m⌋ + J + 1} ≤ 2^{J+1} m` -/
lemma l313_n_bounds (J m : ℕ) (hm : 1 ≤ m) :
    (2 : ℝ) ^ J * m ≤ 2 ^ (Nat.log 2 m + (J + 1)) ∧
      (2 : ℝ) ^ (Nat.log 2 m + (J + 1)) ≤ 2 ^ (J + 1) * m := by
  have h1 : m < 2 ^ (Nat.log 2 m).succ := Nat.lt_pow_succ_log_self (by norm_num) m
  have h2 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
  have h1' : (m : ℝ) ≤ 2 ^ (Nat.log 2 m + 1) := by exact_mod_cast h1.le
  have h2' : (2 : ℝ) ^ Nat.log 2 m ≤ m := by exact_mod_cast h2
  constructor
  · calc (2 : ℝ) ^ J * m ≤ 2 ^ J * 2 ^ (Nat.log 2 m + 1) :=
          mul_le_mul_of_nonneg_left h1' (by positivity)
      _ = _ := by rw [← pow_add]; ring_nf
  · calc (2 : ℝ) ^ (Nat.log 2 m + (J + 1)) = 2 ^ (J + 1) * 2 ^ Nat.log 2 m := by
          rw [← pow_add]; ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left h2' (by positivity)

lemma l313_div_pow (a b : ℕ) : (2 : ℝ)⁻¹ ^ a / 2 ^ b = (2 : ℝ)⁻¹ ^ (a + b) := by
  rw [pow_add, inv_pow (2 : ℝ) b, div_eq_mul_inv]

/-- the event (eqn-use-mid-scale-compare) gives DG's two bounds on `R'` (DG:1303–1306) -/
lemma l313_sup_inf {R : Set ℂ} (hne : R.Nonempty) {f g : ℂ → ℝ} {a b : ℝ}
    (hf : ∀ w ∈ R, |f w| ≤ a) (hfg : ∀ z ∈ R, ∀ w ∈ R, |g z - f w| ≤ b) :
    sSup (g '' R) ≤ sInf (f '' R) + b ∧ |sInf (f '' R)| ≤ a := by
  obtain ⟨w₀, hw₀⟩ := id hne
  have hbdd : BddBelow (f '' R) := ⟨-a, by
    rintro _ ⟨w, hw, rfl⟩; linarith [neg_abs_le (f w), hf w hw]⟩
  refine ⟨csSup_le (hne.image g) ?_, abs_le.2 ⟨le_csInf (hne.image f) ?_, ?_⟩⟩
  · rintro _ ⟨z, hz, rfl⟩
    have : g z - b ≤ sInf (f '' R) := le_csInf (hne.image f) (by
      rintro _ ⟨w, hw, rfl⟩; linarith [le_abs_self (g z - f w), hfg z hz w hw])
    linarith
  · rintro _ ⟨w, hw, rfl⟩; linarith [neg_abs_le (f w), hf w hw]
  · exact (csInf_le hbdd ⟨w₀, hw₀, rfl⟩).trans ((le_abs_self _).trans (hf w₀ hw₀))

/-- **DG Lemma 3.13** (DG:1282–1312), for an abstract family of dyadic rectangles: with
probability `1 − O(e^{−λ m})`, uniformly in `ε ∈ (0,1]`, for every `u ∈ Λ m`,
`D m u ε ≤ max{m³, ε^{-1/(d−ζ)} 2^{-(2+γ²/2−ζ)m/d} e^{(γ/d) min_{Rp m u} ĥ_{2^{-m}}}}` -/
theorem dg_lemma313_core (hW : IsWhiteNoise P W) {γ d : ℝ} (hγ : 0 < γ) (hd : 1 ≤ d)
    {ι : Type*} {Λ : ℕ → Finset ι} {Cn : ℝ} (hΛ : ∀ m, ((Λ m).card : ℝ) ≤ Cn * 4 ^ m)
    {Rp : ℕ → ι → Set ℂ} {U : Set ℂ} (hU : Bornology.IsBounded U)
    (hRU : ∀ m, ∀ u ∈ Λ m, Rp m u ⊆ U) (hRne : ∀ m, ∀ u ∈ Λ m, (Rp m u).Nonempty)
    {Cd : ℝ} (hCd : 1 ≤ Cd)
    (hRd : ∀ m, ∀ u ∈ Λ m, ∀ z ∈ Rp m u, ∀ w ∈ Rp m u, ‖z - w‖ ≤ Cd * (2 : ℝ)⁻¹ ^ m)
    {D : ℕ → ι → ℝ → Ω → ℝ≥0∞} (hL : L313Hyp P W γ d Λ Rp D) {ζ : ℝ} (hζ : 0 < ζ)
    (hζ1 : ζ < 1) :
    ∃ lam C : ℝ, 0 < lam ∧ ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      P {ω | ∃ u ∈ Λ m, ¬ D m u ε ω ≤ ENNReal.ofReal (l313Tgt γ d ζ ε m
        (sInf ((fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ m) 1 z ω) '' Rp m u)))} ≤
        ENNReal.ofReal (C * Real.exp (-(lam * m))) := by
  have := hW.isProbabilityMeasure
  have hd0 : 0 < d := by linarith
  obtain ⟨t, ht0, htζ, ht12, hkey⟩ := l313_exists_param (γ := γ) hd0 hζ
  have ht1 : t < 1 := by linarith
  obtain ⟨a₀, a₁, A, ha₁, hLt⟩ := hL t ht0 ht1
  obtain ⟨K₅, δ₅, hδ₅, h35⟩ := dg_lemma35 hW hU ht0
  obtain ⟨K₆, δ₆, hδ₆, h36⟩ := dg_lemma36 hW hU ht0 ht1 hCd (p := 1) one_pos
  set L := Real.log 2 with hL_def
  have hL0 : 0 < L := Real.log_pos (by norm_num)
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (2 * (Real.log 4 + 1) / a₁) (by norm_num : (1:ℝ) < 2)
  set c' : ℝ := 2 ^ (J + 1) with hc'
  have hc'0 : 0 < c' := by positivity
  set σ : ℝ := ζ * L / (2 * d) with hσ
  have hσ0 : 0 < σ := by positivity
  -- the threshold `m₀`
  obtain ⟨N₅, hN₅⟩ := exists_pow_lt_of_lt_one hδ₅ (by norm_num : (2 : ℝ)⁻¹ < 1)
  obtain ⟨N₆, hN₆⟩ := exists_pow_lt_of_lt_one hδ₆ (by norm_num : (2 : ℝ)⁻¹ < 1)
  obtain ⟨Na, hNa⟩ := exists_nat_ge (c' ^ 2 * A)
  obtain ⟨Ns, hNs⟩ := exists_nat_ge (25 * c' / σ ^ 2)
  obtain ⟨Nl, hNl⟩ := exists_nat_ge (1 / L)
  obtain ⟨Ne, hNe⟩ := exists_nat_gt (64 * c' / L ^ 2)
  set m₀ : ℕ := max (max (max N₅ N₆) (max Na Ns)) (max (max Nl Ne) 1) with hm₀
  set lam : ℝ := min (t * L) 1 with hlam
  have hlam0 : 0 < lam := lt_min (by positivity) one_pos
  refine ⟨lam, Real.exp (lam * m₀) + |K₅| + |K₆| + |Cn| * |a₀|, hlam0, fun m ε hε hε1 => ?_⟩
  rcases lt_or_ge m m₀ with hmm | hmm
  · -- small `m`: the bound is `≥ 1`
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : 1 ≤ Real.exp (lam * m₀) * Real.exp (-(lam * m)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by
        have : (m : ℝ) ≤ m₀ := by exact_mod_cast hmm.le
        have := mul_le_mul_of_nonneg_left this hlam0.le
        linarith)
    have h2 : 0 ≤ (|K₅| + |K₆| + |Cn| * |a₀|) * Real.exp (-(lam * m)) := by positivity
    have e : (Real.exp (lam * m₀) + |K₅| + |K₆| + |Cn| * |a₀|) * Real.exp (-(lam * m)) =
        Real.exp (lam * m₀) * Real.exp (-(lam * m)) +
          (|K₅| + |K₆| + |Cn| * |a₀|) * Real.exp (-(lam * m)) := by ring
    linarith
  -- large `m`
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) ((le_max_right _ _).trans hmm)
  have hmN : N₅ ≤ m ∧ N₆ ≤ m ∧ Na ≤ m ∧ Ns ≤ m ∧ Nl ≤ m ∧ Ne ≤ m := by
    simp only [hm₀, max_le_iff] at hmm; omega
  obtain ⟨hm5, hm6, hma, hms, hml, hme⟩ := hmN
  set k : ℕ := Nat.log 2 m + (J + 1) with hk
  obtain ⟨hnlo, hnhi⟩ := l313_n_bounds J m hm1
  set δ : ℝ := (2 : ℝ)⁻¹ ^ m with hδ
  have hδ0 : 0 < δ := by positivity
  have hlogδ : Real.log δ⁻¹ = m * L := by rw [hδ, inv_pow, inv_inv, Real.log_pow]
  have hδk : δ / (2 : ℝ) ^ k = (2 : ℝ)⁻¹ ^ (m + k) := l313_div_pow m k
  have hδ5 : δ < δ₅ := lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hm5) hN₅
  have hδ6 : δ < δ₆ := lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hm6) hN₆
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  -- the range of `A = 2^k` in Lemma 3.6
  have hA1 : (1 : ℝ) < 2 ^ k := one_lt_pow₀ (by norm_num) (by omega)
  have hA2 : (2 : ℝ) ^ k < Real.exp (Real.log δ⁻¹ ^ (1 - t)) := by
    rw [hlogδ]
    refine hnhi.trans_lt (l313_lt_exp hc'0 hL0 ht12 ?_ ?_)
    · have : (1 / L) ≤ m := hNl.trans (by exact_mod_cast hml)
      rw [div_le_iff₀ hL0] at this; linarith
    · have : 64 * c' / L ^ 2 < m := hNe.trans_le (by exact_mod_cast hme)
      rw [div_lt_iff₀ (by positivity)] at this; linarith
  -- the deterministic inputs of `l313_thr_le_tgt`
  have hnA : ((2 : ℝ) ^ k) ^ 2 * A ≤ (m : ℝ) ^ 3 := by
    rcases le_or_gt A 0 with hA | hA
    · have : ((2 : ℝ) ^ k) ^ 2 * A ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hA
      linarith [pow_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) 3]
    · have h1 : ((2 : ℝ) ^ k) ^ 2 ≤ (c' * m) ^ 2 := pow_le_pow_left₀ (by positivity) hnhi 2
      have h2 : c' ^ 2 * A ≤ m := hNa.trans (by exact_mod_cast hma)
      calc ((2 : ℝ) ^ k) ^ 2 * A ≤ (c' * m) ^ 2 * A := mul_le_mul_of_nonneg_right h1 hA.le
        _ = (m : ℝ) ^ 2 * (c' ^ 2 * A) := by ring
        _ ≤ (m : ℝ) ^ 2 * m := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring
  have hn5 : 5 * √((2 : ℝ) ^ k) ≤ σ * m := by
    have h1 : 25 * c' / σ ^ 2 ≤ m := hNs.trans (by exact_mod_cast hms)
    rw [div_le_iff₀ (by positivity)] at h1
    have h2 : 25 * ((2 : ℝ) ^ k) ≤ (σ * m) ^ 2 := by
      calc 25 * ((2 : ℝ) ^ k) ≤ 25 * (c' * m) := by linarith
        _ = 25 * c' * m := by ring
        _ ≤ m * σ ^ 2 * m := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (σ * m) ^ 2 := by ring
    have h3 : 5 * √((2 : ℝ) ^ k) = √(25 * (2 : ℝ) ^ k) := by
      rw [Real.sqrt_mul (by norm_num), show (25 : ℝ) = 5 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [h3]
    calc √(25 * (2 : ℝ) ^ k) ≤ √((σ * m) ^ 2) := Real.sqrt_le_sqrt h2
      _ = σ * m := Real.sqrt_sq (by positivity)
  -- events
  set E5 : Set Ω := {ω | ∃ z ∈ U, (2 + t) * Real.log δ⁻¹ < |DDDF.phiVer W P δ 1 z ω|}
  set E6 : Set Ω := {ω | ∃ z ∈ U, ∃ w ∈ U, ‖z - w‖ ≤ Cd * δ ∧
    t * Real.log δ⁻¹ < |DDDF.phiVer W P (δ / 2 ^ k) 1 z ω - DDDF.phiVer W P δ 1 w ω|}
  set B : ι → Set Ω := fun u => {ω | ¬ D m u ε ω ≤ ENNReal.ofReal (l313Thr A γ d t ε m k
      (sSup ((fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ (m + k)) 1 z ω) '' Rp m u)))}
  have hsub : {ω | ∃ u ∈ Λ m, ¬ D m u ε ω ≤ ENNReal.ofReal (l313Tgt γ d ζ ε m
        (sInf ((fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ m) 1 z ω) '' Rp m u)))} ⊆
      E5 ∪ E6 ∪ ⋃ u ∈ Λ m, B u := by
    rintro ω ⟨u, hu, hbad⟩
    by_contra hcon
    simp only [mem_union, mem_iUnion, not_or, not_exists] at hcon
    obtain ⟨⟨h5, h6⟩, hB⟩ := hcon
    have hBu := hB u hu
    simp only [B, mem_ofPred_eq, not_not] at hBu
    apply hbad
    refine hBu.trans (ENNReal.ofReal_le_ofReal ?_)
    simp only [E5, mem_ofPred_eq, not_exists, not_and, not_lt] at h5
    simp only [E6, mem_ofPred_eq, not_exists, not_and, not_lt] at h6
    rw [hlogδ] at h5 h6
    obtain ⟨hM, hm0⟩ := l313_sup_inf (hRne m u hu)
      (f := fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ m) 1 z ω)
      (g := fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ (m + k)) 1 z ω)
      (fun w hw => h5 w (hRU m u hu hw))
      (fun z hz w hw => by
        have := h6 z (hRU m u hu hz) w (hRU m u hu hw) (hRd m u hu z hz w hw)
        rwa [hδk] at this)
    refine l313_thr_le_tgt hγ hd0 ht0.le htζ.le (by linarith) hkey hε hε1 hnA hn5 ?_ ?_
    · convert hM using 2; ring
    · convert hm0 using 1; ring
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add (measure_union_le _ _) (measure_biUnion_finset_le _ _)).trans ?_
  have hP5 : P E5 ≤ ENNReal.ofReal (|K₅| * Real.exp (-(lam * m))) := by
    refine (h35 δ ⟨hδ0, hδ5⟩).trans (ENNReal.ofReal_le_ofReal ?_)
    have : δ ^ t ≤ Real.exp (-(lam * m)) := by
      have hlδ : Real.log δ = -(m * L) := by
        have := hlogδ; rw [Real.log_inv] at this; linarith
      rw [Real.rpow_def_of_pos hδ0, hlδ]
      refine Real.exp_le_exp.2 ?_
      have h : lam * m ≤ t * L * m :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg m)
      linarith
    calc K₅ * δ ^ t ≤ |K₅| * δ ^ t :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left this (abs_nonneg _)
  have hP6 : P E6 ≤ ENNReal.ofReal (|K₆| * Real.exp (-(lam * m))) := by
    refine (h36 δ ⟨hδ0, hδ6⟩ (2 ^ k) hA1 hA2).trans (ENNReal.ofReal_le_ofReal ?_)
    have : δ ^ (1 : ℝ) ≤ Real.exp (-(lam * m)) := by
      have hlδ : Real.log δ = -(m * L) := by
        have := hlogδ; rw [Real.log_inv] at this; linarith
      rw [Real.rpow_one, ← Real.exp_log hδ0, hlδ]
      refine Real.exp_le_exp.2 ?_
      have htL : t * L ≤ L := mul_le_of_le_one_left hL0.le (by linarith)
      have h : lam * m ≤ L * m :=
        mul_le_mul_of_nonneg_right ((min_le_left _ _).trans htL) (Nat.cast_nonneg m)
      linarith
    calc K₆ * δ ^ (1 : ℝ) ≤ |K₆| * δ ^ (1 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left this (abs_nonneg _)
  have hPB : ∑ u ∈ Λ m, P (B u) ≤ ENNReal.ofReal (|Cn| * |a₀| * Real.exp (-(lam * m))) := by
    have hb : ∀ u ∈ Λ m, P (B u) ≤ ENNReal.ofReal (|a₀| * Real.exp (-(a₁ * 2 ^ k))) :=
      fun u hu => (hLt m u hu k ε hε).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h4 : (4 : ℝ) ^ m * Real.exp (-(a₁ * 2 ^ k)) ≤ Real.exp (-(lam * m)) := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4), ← Real.exp_nat_mul, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hJ' : 2 * (Real.log 4 + 1) ≤ a₁ * 2 ^ J := by
        rw [div_lt_iff₀ ha₁] at hJ; linarith
      have e0 : a₁ * (2 ^ J * m) ≤ a₁ * 2 ^ k := mul_le_mul_of_nonneg_left hnlo ha₁.le
      have hl4 : 0 ≤ Real.log 4 * m := mul_nonneg (Real.log_pos (by norm_num)).le (Nat.cast_nonneg m)
      have e1 : 2 * (Real.log 4 + 1) * m ≤ a₁ * 2 ^ J * m :=
        mul_le_mul_of_nonneg_right hJ' (Nat.cast_nonneg m)
      have e2 : lam * m ≤ 1 * m := mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg m)
      linarith
    calc ((Λ m).card : ℝ) * (|a₀| * Real.exp (-(a₁ * 2 ^ k)))
        ≤ |Cn| * 4 ^ m * (|a₀| * Real.exp (-(a₁ * 2 ^ k))) :=
          mul_le_mul_of_nonneg_right ((hΛ m).trans (mul_le_mul_of_nonneg_right (le_abs_self _)
            (by positivity))) (by positivity)
      _ = |Cn| * |a₀| * ((4 : ℝ) ^ m * Real.exp (-(a₁ * 2 ^ k))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
  calc P E5 + P E6 + ∑ u ∈ Λ m, P (B u)
      ≤ ENNReal.ofReal (|K₅| * Real.exp (-(lam * m))) +
          ENNReal.ofReal (|K₆| * Real.exp (-(lam * m))) +
          ENNReal.ofReal (|Cn| * |a₀| * Real.exp (-(lam * m))) := add_le_add (add_le_add hP5 hP6) hPB
    _ = ENNReal.ofReal ((|K₅| + |K₆| + |Cn| * |a₀|) * Real.exp (-(lam * m))) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have : 0 ≤ Real.exp (lam * m₀) * Real.exp (-(lam * m)) := by positivity
      have e : (Real.exp (lam * m₀) + |K₅| + |K₆| + |Cn| * |a₀|) * Real.exp (-(lam * m)) =
          Real.exp (lam * m₀) * Real.exp (-(lam * m)) +
            (|K₅| + |K₆| + |Cn| * |a₀|) * Real.exp (-(lam * m)) := by ring
      linarith)

end DG
end LQGMetric
