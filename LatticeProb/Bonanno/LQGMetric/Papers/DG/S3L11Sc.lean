/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11Sc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11Lev
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L13R
import Mathlib.MeasureTheory.Function.Floor

/-!
# DG Lemma 3.11 transported by (3.7): `DGLem311Scaled` from single-square inputs (P2-DG105g)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.11 (DG:1189–1278) in the
form in which it enters the proof of Lemma 3.13 (DG:1300–1310): for the rectangle `sℛ_n + b`,
`s = 2^{-j}`, the bound `n² max{A, e^{√n} T^{−1/(d−ζ)}}` with DG's random factor
`T = ε s^{−(2+γ²/2)} e^{−γ max ĥ_s}` (`l311T`), outside probability `a₀ e^{−a₁ n}`.

The proof follows DG: the rectangle is tiled by the grid of side `s/32` (`sℛ_n + b =
(s/32)ℛ_{32n} + b`, so that the expanded squares `S(1)` (side `3s/32`) are carried by the scaling
(3.7) at scale `s` onto `[13/32,19/32]²`, whose side midpoints lie in DZZ's `𝕍̄` of `dg_lemma312`); the level `κ = min(⌊log T⌋, ⌊log ε_*⌋)` of the coarse
factor is independent of the fine events (DG:1302–1305, "independent from `ĥ_{2^{-m-n_m}}`"),
`dg_lemma311_level` (Peierls + conditioning) gives the crossing at the threshold
`C e^{−κ/(d−ζ)}`, and the cap at `⌊log ε_*⌋` is DG's monotonicity in `ε` (DG:1260, "`A =
2ε_*^{−1/(d−ζ)}`"). The single-square inputs (`L311LevelInput`, at deterministic levels
`t = e^k ≤ ε_*`) are: the fine events and their σ-algebra, the independence of `T` from it, the
probability bound (DG (eqn-perc-prob), from L3.12 by translation invariance), the far
independence (DG:1267) and the pathwise implication (DG (3.7) + L3.2, DG:1305).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- DG's random factor `T_R ε = ε s^{−(2+γ²/2)} e^{−γ max_{R'} ĥ_s}` of `sℛ_n + b`, `s = 2^{-j}`
(DG:1305), verbatim as in `DGLem311Scaled` -/
def l311T (P : Measure Ω) (W : WNSpace → Ω → ℝ) (γ ε : ℝ) (j n : ℕ) (b : ℂ) (ω : Ω) : ℝ :=
  ε * (((2 : ℝ)⁻¹ ^ j) ^ (2 + γ ^ 2 / 2))⁻¹ *
    Real.exp (-(γ * sSup ((fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ j) 1 z ω) ''
      l313Str ((2 : ℝ)⁻¹ ^ j) b n)))

lemma l311T_pos {P : Measure Ω} {W : WNSpace → Ω → ℝ} {γ ε : ℝ} (hε : 0 < ε) (j n : ℕ) (b : ℂ)
    (ω : Ω) : 0 < l311T P W γ ε j n b ω := by
  unfold l311T; positivity

/-- the level of the coarse factor, capped at `k₀` -/
def l311Lev (k₀ : ℤ) (t : ℝ) : ℤ := min ⌊Real.log t⌋ k₀

lemma measurable_l311Lev (k₀ : ℤ) : Measurable (l311Lev k₀) :=
  (Measurable.of_discrete (f := fun i : ℤ => min i k₀)).comp
    (Int.measurable_floor.comp Real.measurable_log)

lemma l311Lev_le (k₀ : ℤ) (t : ℝ) : l311Lev k₀ t ≤ k₀ := min_le_right _ _

lemma exp_l311Lev_le (k₀ : ℤ) {t : ℝ} (ht : 0 < t) : Real.exp (l311Lev k₀ t) ≤ t := by
  have h1 : ((l311Lev k₀ t : ℤ) : ℝ) ≤ Real.log t :=
    (Int.cast_le.2 (min_le_left _ _)).trans (Int.floor_le _)
  calc Real.exp (l311Lev k₀ t) ≤ Real.exp (Real.log t) := Real.exp_le_exp.2 h1
    _ = t := Real.exp_log ht

/-- the threshold at the level of `t` is `≤ max{C e^{−βk₀}, e^β C t^{−β}}` -/
lemma l311Lev_thr {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C) (k₀ : ℤ) {t : ℝ} (ht : 0 < t) :
    C * Real.exp (-(β * l311Lev k₀ t)) ≤
      max (C * Real.exp (-(β * k₀))) (Real.exp β * C * t ^ (-β)) := by
  unfold l311Lev
  rcases le_total ⌊Real.log t⌋ k₀ with h | h
  · rw [min_eq_left h]
    refine le_max_of_le_right ?_
    have h2 := Int.lt_floor_add_one (Real.log t)
    have h3 : -(β * ⌊Real.log t⌋) ≤ β + Real.log t * (-β) := by nlinarith
    rw [Real.rpow_def_of_pos ht, mul_comm (Real.exp β) C, mul_assoc, ← Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h3) hC
  · rw [min_eq_right h]; exact le_max_left _ _

/-- `sℛ_n + b = (s/32)ℛ_{32n} + b` -/
lemma rect_quarter (s : ℝ) (b : ℂ) (n : ℕ) :
    rectStretch (s / 32) b (32 * n) = l313Str s b n ∧
      rectLeft (s / 32) b (32 * n) = l313Left s b n ∧
      rectRight (s / 32) b (32 * n) = l313Right s b n := by
  have e : s / 32 * ((32 * n : ℕ) : ℝ) = s * n := by push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · unfold rectStretch l313Str; rw [mul_assoc 3, e]
  · unfold rectLeft l313Left; rw [e]
  · unfold rectRight l313Right; rw [mul_assoc 2, e]

/-- `(T e^{−λr})^{−β} = T^{−β} e^{λβ r}` -/
lemma rpow_mul_exp_neg {T : ℝ} (hT : 0 < T) (l β r : ℝ) :
    (T * Real.exp (-(l * r))) ^ (-β) = T ^ (-β) * Real.exp (l * β * r) := by
  rw [Real.mul_rpow hT.le (Real.exp_pos _).le, ← Real.exp_mul]
  congr 2; ring

/-- the final probability bookkeeping: `P ≤ 1` for `n < n₀`, and
`c₀ 2^{−4n} + a₂ e^{−a₃ n} ≤ (c₀ + a₂) e^{−a₁ n}` with `a₁ = min(log 2, a₃)` -/
lemma l311_final {p : ℝ≥0∞} (hp1 : p ≤ 1) {c₀ a₂ a₃ : ℝ} (hc₀ : 0 ≤ c₀) (ha₂ : 0 ≤ a₂)
    (ha₃ : 0 ≤ a₃) (n₀ n : ℕ) (hp : n₀ ≤ n → p ≤ ENNReal.ofReal (c₀ * (2 : ℝ)⁻¹ ^ (32 * n)) +
      ENNReal.ofReal (a₂ * Real.exp (-(a₃ * n)))) :
    p ≤ ENNReal.ofReal (max (c₀ + a₂) (Real.exp (min (Real.log 2) a₃ * n₀)) *
      Real.exp (-(min (Real.log 2) a₃ * n))) := by
  set a₁ := min (Real.log 2) a₃
  have ha₁ : 0 ≤ a₁ := le_min (Real.log_nonneg (by norm_num)) ha₃
  rcases lt_or_ge n n₀ with hn | hn
  · refine hp1.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hn' : (n : ℝ) ≤ n₀ := by exact_mod_cast hn.le
    calc (1 : ℝ) ≤ Real.exp (a₁ * n₀) * Real.exp (-(a₁ * n)) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by nlinarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · refine (hp hn).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (2 : ℝ)⁻¹ ^ (32 * n) ≤ Real.exp (-(a₁ * n)) := by
      have e : (2 : ℝ)⁻¹ ^ n = Real.exp (-(Real.log 2 * n)) := by
        rw [Real.exp_neg, mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num), inv_pow]
      calc (2 : ℝ)⁻¹ ^ (32 * n) ≤ (2 : ℝ)⁻¹ ^ n :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = Real.exp (-(Real.log 2 * n)) := e
        _ ≤ _ := Real.exp_le_exp.2 (by
            have := min_le_left (Real.log 2) a₃
            nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
    have h2 : Real.exp (-(a₃ * n)) ≤ Real.exp (-(a₁ * n)) := Real.exp_le_exp.2 (by
      have := min_le_right (Real.log 2) a₃
      nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
    calc c₀ * (2 : ℝ)⁻¹ ^ (32 * n) + a₂ * Real.exp (-(a₃ * n))
        ≤ c₀ * Real.exp (-(a₁ * n)) + a₂ * Real.exp (-(a₁ * n)) := by gcongr
      _ = (c₀ + a₂) * Real.exp (-(a₁ * n)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-- **the single-square inputs of DG Lemma 3.11 at scale `2^{-j}`** (DG:1240–1267 with
DG:1222–1225 and DG:1300–1305): for every rectangle `sℛ_n + b ⊆ Q` and `ε > 0`, the factor
`T` is measurable, and there are fine events `E k x` (level `k`, grid square `x` of side `s/32`)
generating a σ-algebra independent of `T`, each of probability `≥ 1 − 32^{−100}` and with the
product bound at distance `> 9` for the levels `e^k ≤ ε_*`, and an exceptional event `Z` of
probability `≤ a₂ e^{−a₃ n}` (DG's comparison `max |ĥ − ĥ^tr| > c√n`, DG:1226–1227), such that
a.s. off `Z`, on `{e^k ≤ T e^{−(d−ζ₁)√n/2}}`, `E k x` implies that the square `x` is good with
threshold `C e^{−k/(d−ζ₁)}`. -/
def L311LevelInput (P : Measure Ω) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (γ d : ℝ)
    (Q : Set ℂ) : Prop :=
  ∀ ζ₁ : ℝ, 0 < ζ₁ → ζ₁ < 1 → ∃ C εs a₂ a₃ : ℝ, 0 < C ∧ 0 < εs ∧ 0 ≤ a₂ ∧ 0 < a₃ ∧
    ∀ (j n : ℕ) (b : ℂ), l313Str ((2 : ℝ)⁻¹ ^ j) b n ⊆ Q → ∀ ε : ℝ, 0 < ε →
    Measurable (l311T P W γ ε j n b) ∧
    ∃ (Fg : Set (Set Ω)) (E : ℤ → ℤ × ℤ → Set Ω) (Z : Set Ω),
      P Z ≤ ENNReal.ofReal (a₂ * Real.exp (-(a₃ * n))) ∧ (∀ k x, E k x ∈ Fg) ∧
      (∀ B : Set ℝ, MeasurableSet B → ∀ A : Set Ω,
        MeasurableSet[MeasurableSpace.generateFrom Fg] A →
        P (l311T P W γ ε j n b ⁻¹' B ∩ A) = P (l311T P W γ ε j n b ⁻¹' B) * P A) ∧
      (∀ k : ℤ, Real.exp k ≤ εs → ∀ x,
        percInGrid (2 * ((32 * n : ℕ) : ℤ)) (((32 * n : ℕ) : ℤ) - 2) x →
        P (E k x)ᶜ ≤ (32⁻¹ : ℝ≥0∞) ^ 100) ∧
      (∀ k : ℤ, Real.exp k ≤ εs → ∀ F : Finset (ℤ × ℤ),
        (∀ x ∈ F, percInGrid (2 * ((32 * n : ℕ) : ℤ)) (((32 * n : ℕ) : ℤ) - 2) x) →
        (∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar 9 x y) →
        P (⋂ x ∈ F, (E k x)ᶜ) ≤ ∏ x ∈ F, P (E k x)ᶜ) ∧
      (∀ᵐ ω ∂P, ω ∉ Z → ∀ (k : ℤ) (x : ℤ × ℤ),
        Real.exp k ≤ l311T P W γ ε j n b ω * Real.exp (-((d - ζ₁) / 2 * √(n : ℝ))) →
        ω ∈ E k x →
        goodSq (μ ω) ε ((2 : ℝ)⁻¹ ^ j / 32) b (C * Real.exp (-(k / (d - ζ₁)))) x)

/-- **DG Lemma 3.11 at scale `2^{-j}`, transported by (3.7)** (`DGLem311Scaled`, the input of
DG Lemmas 3.13/3.14, Papers/DG/S3L13R) from the single-square inputs. -/
theorem dgLem311Scaled_of_input {P : Measure Ω} [IsProbabilityMeasure P]
    {W : WNSpace → Ω → ℝ} {μ : Ω → Measure ℂ} {γ d : ℝ} {Q : Set ℂ} (hd : 1 ≤ d)
    (h : L311LevelInput P W μ γ d Q) : DGLem311Scaled P W μ γ d Q := by
  intro ζ₁ h0 h1
  obtain ⟨C, εs, a₂, a₃, hC, hεs, ha₂, ha₃, hh⟩ := h ζ₁ h0 h1
  set β : ℝ := 1 / (d - ζ₁) with hβdef
  have hdz : 0 < d - ζ₁ := by linarith
  have hβ : 0 < β := by rw [hβdef]; exact one_div_pos.2 hdz
  set k₀ : ℤ := ⌊Real.log εs⌋
  set n₀ : ℕ := ⌈(2 * Real.log (2048 * C * Real.exp β)) ^ 2⌉₊
  refine ⟨max (32 + a₂) (Real.exp (min (Real.log 2) a₃ * n₀)), min (Real.log 2) a₃,
    2048 * (C * Real.exp (-(β * k₀))), lt_min (Real.log_pos (by norm_num)) ha₃,
    fun j n b hQ ε hε => ?_⟩
  refine l311_final prob_le_one (by norm_num) ha₂ ha₃.le n₀ n fun hn => ?_
  obtain ⟨hT, Fg, E, Z, hZ, hEm, hindT, hgood, hind, hpath⟩ := hh j n b hQ ε hε
  set T := l311T P W γ ε j n b with hTdef
  set c : ℝ := Real.exp (-((d - ζ₁) / 2 * √(n : ℝ)))
  have hTpos : ∀ ω, 0 < T ω * c := fun ω => mul_pos (l311T_pos hε j n b ω) (Real.exp_pos _)
  set κ : Ω → ℤ := fun ω => l311Lev k₀ (T ω * c)
  have hk₀ : Real.exp k₀ ≤ εs := by
    calc Real.exp k₀ ≤ Real.exp (Real.log εs) := Real.exp_le_exp.2 (Int.floor_le _)
      _ = εs := Real.exp_log hεs
  have hmin : ∀ k : ℤ, Real.exp (min k k₀ : ℤ) ≤ εs := fun k =>
    (Real.exp_le_exp.2 (Int.cast_le.2 (min_le_right k k₀))).trans hk₀
  have hs4 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ j / 32 := by positivity
  have hmeas : Measurable fun t : ℝ => l311Lev k₀ (t * c) :=
    (measurable_l311Lev k₀).comp (measurable_id.mul_const c)
  have hP := dg_lemma311_level P μ (ε := ε) hs4 b (32 * n) κ (hmeas.comp hT)
    (fun k => C * Real.exp (-(k / (d - ζ₁)))) Fg
    (fun k x => E (min k k₀) x) (fun k x => hEm _ x)
    (fun k A hA => by
      have e : {ω | κ ω = k} = T ⁻¹' ((fun t : ℝ => l311Lev k₀ (t * c)) ⁻¹' {k}) := rfl
      rw [e]
      exact hindT _ (hmeas (measurableSet_singleton k)) A hA) Z
    (by
      filter_upwards [hpath] with ω hp hZω k x hk hx
      have hkk : min k k₀ = k := min_eq_left (hk ▸ l311Lev_le k₀ (T ω * c))
      have := hp hZω (min k k₀) x (by rw [hkk, ← hk]; exact exp_l311Lev_le k₀ (hTpos ω)) hx
      rwa [hkk] at this)
    (fun k x hx => hgood _ (hmin k) x hx) (fun k F hF hfar => hind _ (hmin k) F hF hfar)
  obtain ⟨r1, r2, r3⟩ := rect_quarter ((2 : ℝ)⁻¹ ^ j) b n
  rw [r1, r2, r3] at hP
  refine (measure_mono ?_).trans (hP.trans (add_le_add_right hZ _))
  intro ω hω hle
  refine hω ?_
  -- the threshold: `2 (32n)² C e^{−κ/(d−ζ)} ≤ n² max{A, e^{√n} T^{−1/(d−ζ)}}`
  refine (show (l313Set (μ ω) ε (l313Str ((2 : ℝ)⁻¹ ^ j) b n) (l313Left ((2 : ℝ)⁻¹ ^ j) b n)
    (l313Right ((2 : ℝ)⁻¹ ^ j) b n) : ℝ≥0∞) = (dgLGDSet (μ ω) ε (l313Str ((2 : ℝ)⁻¹ ^ j) b n)
    (l313Left ((2 : ℝ)⁻¹ ^ j) b n) (l313Right ((2 : ℝ)⁻¹ ^ j) b n) : ℝ≥0∞) from rfl).trans_le
    (hle.trans ?_)
  rw [show (2 * ((32 * n : ℕ) : ℝ≥0∞) ^ 2) * ENNReal.ofReal (C * Real.exp (-((κ ω : ℝ) /
      (d - ζ₁)))) = ENNReal.ofReal ((n : ℝ) ^ 2 * (2048 * (C * Real.exp (-((κ ω : ℝ) /
      (d - ζ₁)))))) by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1; push_cast; ring]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hthr := l311Lev_thr hβ.le hC.le k₀ (hTpos ω)
  have e3 : -((κ ω : ℝ) / (d - ζ₁)) = -(β * (l311Lev k₀ (T ω * c) : ℝ)) := by
    simp only [κ, hβdef]; ring
  rw [e3]
  have e4 : (T ω * c) ^ (-β) = T ω ^ (-β) * Real.exp (√(n : ℝ) / 2) := by
    rw [rpow_mul_exp_neg (l311T_pos hε j n b ω)]
    congr 2; rw [hβdef]; field_simp
  have hsq : 2048 * C * Real.exp β * Real.exp (√(n : ℝ) / 2) ≤ Real.exp √(n : ℝ) := by
    have hpos : 0 < 2048 * C * Real.exp β := by positivity
    rw [← Real.exp_log hpos, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h5 : (2 * Real.log (2048 * C * Real.exp β)) ^ 2 ≤ n := by
      have := Nat.le_ceil ((2 * Real.log (2048 * C * Real.exp β)) ^ 2)
      exact this.trans (by exact_mod_cast hn)
    have h6 : 2 * Real.log (2048 * C * Real.exp β) ≤ √(n : ℝ) :=
      calc 2 * Real.log (2048 * C * Real.exp β) ≤ |2 * Real.log (2048 * C * Real.exp β)| :=
            le_abs_self _
        _ = √((2 * Real.log (2048 * C * Real.exp β)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ √(n : ℝ) := Real.sqrt_le_sqrt h5
    linarith
  have hTβ : 0 ≤ T ω ^ (-β) := Real.rpow_nonneg (l311T_pos hε j n b ω).le _
  calc 2048 * (C * Real.exp (-(β * (l311Lev k₀ (T ω * c) : ℝ))))
      ≤ 2048 * max (C * Real.exp (-(β * k₀))) (Real.exp β * C * (T ω * c) ^ (-β)) := by gcongr
    _ = max (2048 * (C * Real.exp (-(β * k₀))))
          (2048 * C * Real.exp β * Real.exp (√(n : ℝ) / 2) * T ω ^ (-β)) := by
        rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2048), e4]; ring_nf
    _ ≤ max (2048 * (C * Real.exp (-(β * k₀)))) (Real.exp √(n : ℝ) * T ω ^ (-β)) := by
        gcongr
    _ = _ := by rw [hβdef]; rfl

end DG
end LQGMetric
