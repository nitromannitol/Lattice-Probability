/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L19Sc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L19Lev
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L21R
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11Sc
import Mathlib.MeasureTheory.Function.Floor

/-!
# DG Lemma 3.19 transported by (3.7): `DGLem319Scaled` from single-square inputs (P2-DG105g)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.19 (DG:1614–1660) in the
form in which it enters the proof of Lemma 3.21 (DG:1699–1706): for the annulus `s𝒜_n + b`,
`s = 2^{-j}`, `D^ε(∂_in, ∂_out) ≥ e^{−√n} T^{−1/(d+ζ)}` on `{T ≤ ε_*}`, with DG's random factor
`T = ε s^{−(2+γ²/2)} e^{−γ min ĥ_s}` (`l319X`), outside probability `a₀ e^{−a₁ n}`.

As in S3L11Sc: the annulus is tiled by the grid of side `s/32` (`s𝒜_n + b = (s/32)𝒜_{32n} + b`);
the level `κ = min(⌈log T⌉, k₀ + 1)` (`k₀ = ⌊log ε_*⌋`) of the coarse factor is independent of
the fine events; on `{T ≤ e^{k₀}}` it is `⌈log T⌉` and the threshold `C e^{−κ/(d+ζ)}` dominates
`e^{−√n} T^{−1/(d+ζ)}` for `n ≥ n₀`; the level `k₀ + 1` (where `T > e^{k₀}`) carries the trivial
threshold `0`. Then `dg_lemma319_level` (Peierls for enclosures + conditioning).
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

/-- DG's random factor `T_S ε = ε s^{−(2+γ²/2)} e^{−γ min ĥ_s}` of `s𝒜_n + b` (DG:1702),
verbatim as in `DGLem319Scaled` -/
def l319X (P : Measure Ω) (W : WNSpace → Ω → ℝ) (γ ε : ℝ) (j n : ℕ) (b : ℂ) (ω : Ω) : ℝ :=
  ε * ((((2 : ℝ)⁻¹ ^ j) ^ (2 + γ ^ 2 / 2))⁻¹ * Real.exp (-(γ * sInf
    ((fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ j) 1 z ω) '' l321Out ((2 : ℝ)⁻¹ ^ j) b n))))

lemma l319X_pos {P : Measure Ω} {W : WNSpace → Ω → ℝ} {γ ε : ℝ} (hε : 0 < ε) (j n : ℕ) (b : ℂ)
    (ω : Ω) : 0 < l319X P W γ ε j n b ω := by
  unfold l319X; positivity

/-- the level `min(⌈log t⌉, k₀ + 1)` -/
def l319Lev (k₀ : ℤ) (t : ℝ) : ℤ := min ⌈Real.log t⌉ (k₀ + 1)

lemma measurable_l319Lev (k₀ : ℤ) : Measurable (l319Lev k₀) :=
  (Measurable.of_discrete (f := fun i : ℤ => min i (k₀ + 1))).comp
    (Int.measurable_ceil.comp Real.measurable_log)

lemma le_exp_ceil_log {t : ℝ} (ht : 0 < t) : t ≤ Real.exp ⌈Real.log t⌉ := by
  calc t = Real.exp (Real.log t) := (Real.exp_log ht).symm
    _ ≤ Real.exp ⌈Real.log t⌉ := Real.exp_le_exp.2 (Int.le_ceil _)

lemma exp_ceil_log_thr {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C) {t : ℝ} (ht : 0 < t) :
    Real.exp (-β) * C * t ^ (-β) ≤ C * Real.exp (-(β * ⌈Real.log t⌉)) := by
  have h2 := Int.ceil_lt_add_one (Real.log t)
  have h3 : -β + Real.log t * (-β) ≤ -(β * ⌈Real.log t⌉) := by nlinarith
  rw [Real.rpow_def_of_pos ht, mul_comm (Real.exp (-β)) C, mul_assoc, ← Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h3) hC

/-- `s𝒜_n + b = (s/32)𝒜_{32n} + b` -/
lemma ann_quarter (s : ℝ) (b : ℂ) (n : ℕ) :
    annIn (s / 32) b (32 * n) = l321In s b n ∧ annOut (s / 32) b (32 * n) = l321Out s b n := by
  have e : s / 32 * ((32 * n : ℕ) : ℝ) = s * n := by push_cast; ring
  refine ⟨?_, ?_⟩
  · unfold annIn l321In; rw [e]
  · unfold annOut l321Out; rw [e]

/-- every set-to-set LGD is `≥ 1` (a path is covered by at least one ball) -/
lemma one_le_dgLGDSet (μ : Measure ℂ) (ε : ℝ) (U A B : Set ℂ) :
    (1 : ℝ≥0∞) ≤ (dgLGDSet μ ε U A B : ℝ≥0∞) := by
  have h : (1 : ℕ∞) ≤ dgLGDSet μ ε U A B := by
    refine le_iInf₂ fun z _ => le_iInf₂ fun w _ => ?_
    unfold dgLGD
    refine le_iInf₂ fun N hN => ?_
    obtain ⟨x, ρ, P, -, hc⟩ := hN
    have : N ≠ 0 := by
      rintro rfl
      obtain ⟨i, -⟩ := hc 0
      exact i.elim0
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  simpa using ENat.toENNReal_le.2 h

/-- **the single-square inputs of DG Lemma 3.19 at scale `2^{-j}`** (DG:1641–1656 with
DG:1633–1636 and DG:1699–1706): for every annulus `s𝒜_n + b ⊆ Q` and `ε > 0`, the factor `T`
is measurable, and there are fine events `E k z` (level `k`, grid square `z` of side `s/32`,
sites of the annulus `c₀ + 2 ≤ ‖z‖_∞ ≤ 32n − 2 + c₀`, `c₀ = 16n`) generating a σ-algebra
independent of `T`, with probability `≥ 1 − 32^{−100}` and the product bound at distance `> 9`
for the levels `e^k ≤ ε_*`, and an exceptional event `Z` of probability `≤ a₂ e^{−a₃ n}`
(DG's comparison `max |ĥ − ĥ^tr| > c√n`, DG:1637–1638), such that a.s. off `Z`, on
`{T e^{(d+ζ₁)√n/2} ≤ e^k}`, `E k z` implies `D^ε(S_z, ∂S_z(1/2)) ≥ C e^{−k/(d+ζ₁)}`. -/
def L319LevelInput (P : Measure Ω) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (γ d : ℝ)
    (Q : Set ℂ) : Prop :=
  ∀ ζ₁ : ℝ, 0 < ζ₁ → ζ₁ < 1 → ∃ C εs a₂ a₃ : ℝ, 0 < C ∧ 0 < εs ∧ 0 ≤ a₂ ∧ 0 < a₃ ∧
    ∀ (j n : ℕ) (b : ℂ), l321Out ((2 : ℝ)⁻¹ ^ j) b n ⊆ Q → ∀ ε : ℝ, 0 < ε →
    Measurable (l319X P W γ ε j n b) ∧
    ∃ (Fg : Set (Set Ω)) (E : ℤ → ℤ × ℤ → Set Ω) (Z : Set Ω),
      P Z ≤ ENNReal.ofReal (a₂ * Real.exp (-(a₃ * n))) ∧ (∀ k z, E k z ∈ Fg) ∧
      (∀ B : Set ℝ, MeasurableSet B → ∀ A : Set Ω,
        MeasurableSet[MeasurableSpace.generateFrom Fg] A →
        P (l319X P W γ ε j n b ⁻¹' B ∩ A) = P (l319X P W γ ε j n b ⁻¹' B) * P A) ∧
      (∀ k : ℤ, Real.exp k ≤ εs → ∀ z,
        (∃ d, z ∈ annRect ((32 * n / 2 + 2 : ℕ) : ℤ) ((32 * n - 2 + 32 * n / 2 : ℕ) : ℤ) d) →
        P (E k z)ᶜ ≤ (32⁻¹ : ℝ≥0∞) ^ 100) ∧
      (∀ k : ℤ, Real.exp k ≤ εs → ∀ F : Finset (ℤ × ℤ),
        (∀ z ∈ F, ∃ d, z ∈ annRect ((32 * n / 2 + 2 : ℕ) : ℤ) ((32 * n - 2 + 32 * n / 2 : ℕ) : ℤ) d) →
        (∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar 9 x y) →
        P (⋂ x ∈ F, (E k x)ᶜ) ≤ ∏ x ∈ F, P (E k x)ᶜ) ∧
      (∀ᵐ ω ∂P, ω ∉ Z → ∀ (k : ℤ) (z : ℤ × ℤ),
        l319X P W γ ε j n b ω * Real.exp ((d + ζ₁) / 2 * √(n : ℝ)) ≤ Real.exp k →
        ω ∈ E k z →
        goodAnn (μ ω) ε ((2 : ℝ)⁻¹ ^ j / 32) b (32 * n / 2 : ℕ)
          (C * Real.exp (-(k / (d + ζ₁)))) z)

/-- **DG Lemma 3.19 at scale `2^{-j}`, transported by (3.7)** (`DGLem319Scaled`, the input of
DG Lemma 3.21, Papers/DG/S3L21R) from the single-square inputs. -/
theorem dgLem319Scaled_of_input {P : Measure Ω} [IsProbabilityMeasure P]
    {W : WNSpace → Ω → ℝ} {μ : Ω → Measure ℂ} {γ d : ℝ} {Q : Set ℂ} (hd : 1 ≤ d)
    (h : L319LevelInput P W μ γ d Q) : DGLem319Scaled P W μ γ d Q := by
  intro ζ₁ h0 h1
  obtain ⟨C, εs, a₂, a₃, hC, hεs, ha₂, ha₃, hh⟩ := h ζ₁ h0 h1
  set β : ℝ := 1 / (d + ζ₁) with hβdef
  have hdz : 0 < d + ζ₁ := by linarith
  have hβ : 0 < β := by rw [hβdef]; exact one_div_pos.2 hdz
  set k₀ : ℤ := ⌊Real.log εs⌋
  set n₀ : ℕ := ⌈(2 * Real.log (Real.exp (-β) * C)) ^ 2⌉₊ + ⌈(2 * (β * k₀)) ^ 2⌉₊
  have hk₀ : Real.exp k₀ ≤ εs := by
    calc Real.exp k₀ ≤ Real.exp (Real.log εs) := Real.exp_le_exp.2 (Int.floor_le _)
      _ = εs := Real.exp_log hεs
  refine ⟨max (768 + a₂) (Real.exp (min (Real.log 2) a₃ * n₀)), min (Real.log 2) a₃, 1,
    lt_min (Real.log_pos (by norm_num)) ha₃, one_pos, fun j n b hQ ε hε => ?_⟩
  refine l311_final prob_le_one (by norm_num) ha₂ ha₃.le n₀ n fun hn => ?_
  obtain ⟨hT, Fg, E, Z, hZ, hEm, hindT, hgood, hind, hpath⟩ := hh j n b hQ ε hε
  set T := l319X P W γ ε j n b with hTdef
  set c : ℝ := Real.exp ((d + ζ₁) / 2 * √(n : ℝ))
  have hT0 : ∀ ω, 0 < T ω := l319X_pos hε j n b
  have hTpos : ∀ ω, 0 < T ω * c := fun ω => mul_pos (hT0 ω) (Real.exp_pos _)
  set κ : Ω → ℤ := fun ω => l319Lev k₀ (T ω * c)
  have hmin : ∀ k : ℤ, Real.exp (min k k₀ : ℤ) ≤ εs := fun k =>
    (Real.exp_le_exp.2 (Int.cast_le.2 (min_le_right k k₀))).trans hk₀
  have hs4 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ j / 32 := by positivity
  have hmeas : Measurable fun t : ℝ => l319Lev k₀ (t * c) :=
    (measurable_l319Lev k₀).comp (measurable_id.mul_const c)
  set Mf : ℤ → ℝ := fun k => if k ≤ k₀ then C * Real.exp (-(k / (d + ζ₁))) else 1
  have hP := dg_lemma319_level P μ (ε := ε) hs4 b (32 * n) κ (hmeas.comp hT) Mf Fg
    (fun k z => E (min k k₀) z) (fun k z => hEm _ z)
    (fun k A hA => by
      have e : {ω | κ ω = k} = T ⁻¹' ((fun t : ℝ => l319Lev k₀ (t * c)) ⁻¹' {k}) := rfl
      rw [e]
      exact hindT _ (hmeas (measurableSet_singleton k)) A hA) Z
    (by
      filter_upwards [hpath] with ω hp hZω k z hk hz
      by_cases hkk : k ≤ k₀
      · have hm : min k k₀ = k := min_eq_left hkk
        have hceil : l319Lev k₀ (T ω * c) = ⌈Real.log (T ω * c)⌉ := by
          have : min ⌈Real.log (T ω * c)⌉ (k₀ + 1) = k := hk
          rcases min_choice ⌈Real.log (T ω * c)⌉ (k₀ + 1) with e | e
          · exact e
          · omega
        have hTk : T ω * c ≤ Real.exp k := by
          rw [← hk]; show T ω * c ≤ Real.exp (l319Lev k₀ (T ω * c) : ℤ)
          rw [hceil]; exact le_exp_ceil_log (hTpos ω)
        have := hp hZω k z hTk (by rwa [hm] at hz)
        simpa only [Mf, if_pos hkk] using this
      · simp only [Mf, if_neg hkk, goodAnn, ENNReal.ofReal_one]
        exact one_le_dgLGDSet _ _ _ _ _)
    (fun k z hz => hgood _ (hmin k) z hz) (fun k F hF hfar => hind _ (hmin k) F hF hfar)
  obtain ⟨r1, r2⟩ := ann_quarter ((2 : ℝ)⁻¹ ^ j) b n
  rw [r1, r2] at hP
  have e4 : Real.exp (-(Real.log 2 * ((32 * n : ℕ) : ℝ))) = (2 : ℝ)⁻¹ ^ (32 * n) := by
    rw [Real.exp_neg, mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num), inv_pow]
  rw [e4] at hP
  refine (measure_mono ?_).trans (hP.trans (add_le_add_right hZ _))
  rintro ω ⟨-, hlt⟩
  refine (show (l313Set (μ ω) ε univ (l321In ((2 : ℝ)⁻¹ ^ j) b n)
    (frontier (l321Out ((2 : ℝ)⁻¹ ^ j) b n)) : ℝ≥0∞) = (dgLGDSet (μ ω) ε univ
    (l321In ((2 : ℝ)⁻¹ ^ j) b n) (frontier (l321Out ((2 : ℝ)⁻¹ ^ j) b n)) : ℝ≥0∞)
    from rfl).symm.trans_lt hlt |>.trans_le ?_
  refine ENNReal.ofReal_le_ofReal ?_
  -- `T^{−β} = (Tc)^{−β} e^{√n/2}`
  have eT : T ω ^ (-β) = (T ω * c) ^ (-β) * Real.exp (√(n : ℝ) / 2) := by
    rw [Real.mul_rpow (hT0 ω).le (Real.exp_pos _).le, ← Real.exp_mul, mul_assoc,
      ← Real.exp_add]
    have : (d + ζ₁) / 2 * √(n : ℝ) * -β + √(n : ℝ) / 2 = 0 := by
      rw [hβdef]; field_simp; ring
    rw [this, Real.exp_zero, mul_one]
  have hsqrt : ∀ x : ℝ, x ^ 2 ≤ n → x ≤ √(n : ℝ) := fun x hx =>
    (le_abs_self x).trans ((Real.sqrt_sq_eq_abs x).symm.le.trans (Real.sqrt_le_sqrt hx))
  have hn1 : (2 * Real.log (Real.exp (-β) * C)) ^ 2 ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_trans (Nat.le_add_right _ _) hn))
  have hn2 : (2 * (β * k₀)) ^ 2 ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_trans (Nat.le_add_left _ _) hn))
  have hTβ : 0 ≤ (T ω * c) ^ (-β) := Real.rpow_nonneg (hTpos ω).le _
  change Real.exp (-√(n : ℝ)) * T ω ^ (-β) ≤ Mf (κ ω)
  rw [eT]
  by_cases hk : κ ω ≤ k₀
  · simp only [Mf, if_pos hk]
    have hceil : κ ω = ⌈Real.log (T ω * c)⌉ := by
      have : min ⌈Real.log (T ω * c)⌉ (k₀ + 1) = κ ω := rfl
      rcases min_choice ⌈Real.log (T ω * c)⌉ (k₀ + 1) with e | e
      · rw [← this, e]
      · omega
    have hthr := exp_ceil_log_thr hβ.le hC.le (hTpos ω)
    have e3 : -((κ ω : ℝ) / (d + ζ₁)) = -(β * (⌈Real.log (T ω * c)⌉ : ℝ)) := by
      rw [hceil, hβdef]; ring
    rw [e3]
    have hsq : Real.exp (-√(n : ℝ)) * Real.exp (√(n : ℝ) / 2) ≤ Real.exp (-β) * C := by
      have hpos : 0 < Real.exp (-β) * C := by positivity
      rw [← Real.exp_log hpos, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have := hsqrt _ hn1
      have h7 := neg_abs_le (2 * Real.log (Real.exp (-β) * C))
      have h8 : |2 * Real.log (Real.exp (-β) * C)| ≤ √(n : ℝ) := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hn1
      linarith
    calc Real.exp (-√(n : ℝ)) * ((T ω * c) ^ (-β) * Real.exp (√(n : ℝ) / 2))
        = Real.exp (-√(n : ℝ)) * Real.exp (√(n : ℝ) / 2) * (T ω * c) ^ (-β) := by ring
      _ ≤ Real.exp (-β) * C * (T ω * c) ^ (-β) := by gcongr
      _ ≤ _ := hthr
  · simp only [Mf, if_neg hk]
    have hbig : Real.exp k₀ ≤ T ω * c := by
      have h1 : k₀ + 1 ≤ ⌈Real.log (T ω * c)⌉ := by
        have : min ⌈Real.log (T ω * c)⌉ (k₀ + 1) = κ ω := rfl
        rcases min_choice ⌈Real.log (T ω * c)⌉ (k₀ + 1) with e | e <;> omega
      have h2 : (k₀ : ℝ) < Real.log (T ω * c) := by
        have := Int.lt_ceil.1 (show k₀ < ⌈Real.log (T ω * c)⌉ by omega)
        exact this
      calc Real.exp k₀ ≤ Real.exp (Real.log (T ω * c)) := Real.exp_le_exp.2 h2.le
        _ = T ω * c := Real.exp_log (hTpos ω)
    have hr : (T ω * c) ^ (-β) ≤ Real.exp (-(β * k₀)) := by
      calc (T ω * c) ^ (-β) ≤ (Real.exp k₀) ^ (-β) :=
            Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hbig (by linarith)
        _ = Real.exp (-(β * k₀)) := by rw [← Real.exp_mul]; ring_nf
    have h9 : -(β * k₀) ≤ √(n : ℝ) / 2 := by
      have h8 : |2 * (β * k₀)| ≤ √(n : ℝ) := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hn2
      have := neg_abs_le (2 * (β * k₀))
      linarith
    calc Real.exp (-√(n : ℝ)) * ((T ω * c) ^ (-β) * Real.exp (√(n : ℝ) / 2))
        ≤ Real.exp (-√(n : ℝ)) * (Real.exp (-(β * k₀)) * Real.exp (√(n : ℝ) / 2)) := by
          gcongr
      _ = Real.exp (-√(n : ℝ) + -(β * k₀) + √(n : ℝ) / 2) := by
          rw [Real.exp_add, Real.exp_add]; ring
      _ ≤ Real.exp 0 := Real.exp_le_exp.2 (by linarith)
      _ = 1 := Real.exp_zero

end DG
end LQGMetric
