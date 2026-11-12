/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P28U1Geo at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DiamDet

/-!
# DDDF Prop 28 Part 1 Step 1: the chaining restricted to levels `≥ k` (task P2-DDDF28U)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1414–1418: "We use the chaining argument
`eq:Chaining` at scale `k`", i.e. for `x, x'` at distance `≲ 2^{-k}` only the levels `i ≥ k` of
the chaining (DF arXiv:1809.02607 l. 1013–1021, (6.1)) are used. Here: two points whose
coordinates differ by less than `h = 2^{-K}` lie in a common square `[ih, (i+2)h] × [jh, (j+2)h]`
of `[0,1]²` (not dyadic: its corner is on the grid `h ℤ²`), whose four halves (crossings of
`2^{-K} R_{2,1}`, motions `hmS K i j`) meet the systems of the dyadic squares of level `K`
containing the points (`SqSys.meet_child`); below level `K` the chaining is that of
`diam_chain_det`. The final link (from a point to the system of level `m`) is left abstract:
`hE` bounds `d(z, w)` for `|z − w| ≤ 2·2^{-m}` (it is used with the small-pair estimate of
Step 2, DDDF l. 1438–1446, in place of DDDF's straight segment `2^{-n} e^{ξ sup φ}`).

`chain_restr`: `d(x, y) ≤ 2E + 8 B' + 24 Σ_{K ≤ k ≤ m} B k`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6P28U

open LFPP T20E Blueprint S6D

/-- the motions of the four halves of the square `[ih, (i+2)h] × [jh, (j+2)h]`, `h = 2^{-K}` -/
def hmS (K i j : ℕ) : Fin 4 → Circle × ℂ :=
  ![eH K (i : ℤ) (j : ℤ), eH K (i : ℤ) ((j + 1 : ℕ) : ℤ), eV K ((i + 1 : ℕ) : ℤ) (j : ℤ),
    eV K ((i + 2 : ℕ) : ℤ) (j : ℤ)]

theorem sqSys_of_admS {K i j : ℕ} {γ : Fin 4 → ℝ → ℂ}
    (h : ∀ e, Adm21 K (hmS K i j e) (γ e)) :
    SqSys (i * (2 : ℝ)⁻¹ ^ K) (j * (2 : ℝ)⁻¹ ^ K) ((2 : ℝ)⁻¹ ^ K) γ := by
  have h0 := adm_eH (h 0)
  have h1 := adm_eH (h 1)
  have h2 := adm_eV (h 2)
  have h3 := adm_eV (h 3)
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Int.cast_add, Int.cast_ofNat,
    Int.cast_one, Int.cast_natCast] at h0 h1 h2 h3
  refine ⟨fun e => ?_, h0.2.1, h0.2.2, ?_, h1.2.2, ?_, h2.2.2, ?_, h3.2.2⟩
  · obtain rfl | rfl | rfl | rfl : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by fin_cases e <;> simp
    exacts [h0.1, h1.1, h2.1, h3.1]
  · intro t ht
    obtain ⟨a, b⟩ := h1.2.1 t ht
    exact ⟨a, ⟨by linarith [b.1], by linarith [b.2]⟩⟩
  · intro t ht
    obtain ⟨a, b⟩ := h2.2.1 t ht
    exact ⟨⟨by linarith [a.1], by linarith [a.2]⟩, b⟩
  · intro t ht
    obtain ⟨a, b⟩ := h3.2.1 t ht
    exact ⟨⟨by linarith [a.1], by linarith [a.2]⟩, b⟩

/-- the column of level `k` of `t` (computed from level `m`) brackets `t` -/
lemma colIdx_div_bracket {m k : ℕ} (hk : k ≤ m) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ((colIdx m t / 2 ^ (m - k) : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ k ≤ t ∧
      t ≤ (((colIdx m t / 2 ^ (m - k) : ℕ) : ℝ) + 1) * (2 : ℝ)⁻¹ ^ k := by
  obtain ⟨h1, h2⟩ := abs_sub_colIdx (n := m) ht
  set c := colIdx m t
  set I := c / 2 ^ (m - k)
  have hpos : 0 < 2 ^ (m - k) := by positivity
  have hlo : I * 2 ^ (m - k) ≤ c := Nat.div_mul_le_self _ _
  have hhi : c + 1 ≤ (I + 1) * 2 ^ (m - k) := by
    have := Nat.lt_div_mul_add (a := c) hpos
    simp only [I]; nlinarith
  have hmk : (2 : ℝ)⁻¹ ^ k = (2 : ℝ) ^ (m - k) * (2 : ℝ)⁻¹ ^ m := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [Nat.add_sub_cancel_left, pow_add, ← mul_assoc, mul_comm ((2 : ℝ) ^ d), mul_assoc,
      ← mul_pow, mul_inv_cancel₀ (two_ne_zero), one_pow, mul_one]
  have hp : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ m := by positivity
  have hlo' : (I : ℝ) * (2 : ℝ) ^ (m - k) ≤ c := by exact_mod_cast hlo
  have hhi' : (c : ℝ) + 1 ≤ ((I : ℝ) + 1) * (2 : ℝ) ^ (m - k) := by exact_mod_cast hhi
  rw [hmk]
  constructor
  · calc (I : ℝ) * ((2 : ℝ) ^ (m - k) * (2 : ℝ)⁻¹ ^ m) = (I * (2 : ℝ) ^ (m - k)) * (2 : ℝ)⁻¹ ^ m := by
          ring
      _ ≤ c * (2 : ℝ)⁻¹ ^ m := mul_le_mul_of_nonneg_right hlo' hp
      _ ≤ t := h1
  · calc t ≤ ((c : ℝ) + 1) * (2 : ℝ)⁻¹ ^ m := h2
      _ ≤ (((I : ℝ) + 1) * (2 : ℝ) ^ (m - k)) * (2 : ℝ)⁻¹ ^ m := mul_le_mul_of_nonneg_right hhi' hp
      _ = _ := by ring

/-- two close coordinates have neighbouring columns -/
lemma colIdx_div_near {m k : ℕ} (hk : k ≤ m) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hst : |s - t| < (2 : ℝ)⁻¹ ^ k) :
    colIdx m s / 2 ^ (m - k) ≤ colIdx m t / 2 ^ (m - k) + 1 := by
  obtain ⟨a1, -⟩ := colIdx_div_bracket hk hs
  obtain ⟨-, b2⟩ := colIdx_div_bracket hk ht
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  have h := (abs_lt.1 hst).2
  have : ((colIdx m s / 2 ^ (m - k) : ℕ) : ℝ) < ((colIdx m t / 2 ^ (m - k) : ℕ) : ℝ) + 2 := by
    by_contra hc
    push Not at hc
    nlinarith
  have : (colIdx m s / 2 ^ (m - k) : ℕ) < colIdx m t / 2 ^ (m - k) + 2 := by exact_mod_cast this
  omega

/-- **the chaining at scale `K`** (DDDF l. 1414–1418): two points of `[0,1]²` whose coordinates
differ by less than `2^{-K}` are at distance `≤ 2E + 8B' + 24 Σ_{K ≤ k ≤ m} B k`. -/
theorem chain_restr {ξ : ℝ} {f : ℂ → ℝ} (hf : Continuous f) {K m : ℕ} (hK1 : 1 ≤ K)
    (hKm : K ≤ m) (B : ℕ → ℝ≥0∞)
    (hB : ∀ k, K ≤ k → k ≤ m → ∀ i < 2 ^ k, ∀ j < 2 ^ k, ∀ e,
      len21 ξ f (k + 1) (hm k i j e) ≤ B k)
    (B' : ℝ≥0∞) (hB' : ∀ i j : ℕ, i + 2 ≤ 2 ^ K → j + 2 ≤ 2 ^ K → ∀ e,
      len21 ξ f K (hmS K i j e) ≤ B')
    {E : ℝ≥0∞} (hE : ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare,
      ‖w - z‖ ≤ 2 * (2 : ℝ)⁻¹ ^ m → lfppDOn ξ f closedUnitSquare z w ≤ E)
    {x y : ℂ} (hx : x ∈ closedUnitSquare) (hy : y ∈ closedUnitSquare)
    (hre : |x.re - y.re| < (2 : ℝ)⁻¹ ^ K) (him : |x.im - y.im| < (2 : ℝ)⁻¹ ^ K) :
    lfppDOn ξ f closedUnitSquare x y ≤
      2 * E + 8 * B' + 24 * ∑ t ∈ Finset.range (m - K + 1), B (K + t) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set η : ℝ := (ε : ℝ) / (32 * (m + 1)) with hηdef
  have hη : 0 < η := by positivity
  set η' : ℝ≥0∞ := ENNReal.ofReal η
  have hfin : ∀ (k i j : ℕ) (e : Fin 4), len21 ξ f (k + 1) (hm k i j e) ≠ ⊤ := fun k i j e =>
    T20D.crossLenIn_mot_ne_top (k + 1) _ _ (by norm_num) (by norm_num) hf
  have hfinS : ∀ (i j : ℕ) (e : Fin 4), len21 ξ f K (hmS K i j e) ≠ ⊤ := fun i j e =>
    T20D.crossLenIn_mot_ne_top K _ _ (by norm_num) (by norm_num) hf
  choose γ hγA hγL using fun (k i j : ℕ) (e : Fin 4) => exists_near (hfin k i j e) hη
  choose γS hγSA hγSL using fun (i j : ℕ) (e : Fin 4) => exists_near (hfinS i j e) hη
  have hSys : ∀ k i j : ℕ, SqSys (2 * i * (2 : ℝ)⁻¹ ^ (k + 1)) (2 * j * (2 : ℝ)⁻¹ ^ (k + 1))
      ((2 : ℝ)⁻¹ ^ (k + 1)) (γ k i j) := fun k i j => sqSys_of_adm (hγA k i j)
  have hSysS : ∀ i j : ℕ, SqSys (i * (2 : ℝ)⁻¹ ^ K) (j * (2 : ℝ)⁻¹ ^ K) ((2 : ℝ)⁻¹ ^ K)
      (γS i j) := fun i j => sqSys_of_admS (hγSA i j)
  have hh : ∀ k : ℕ, (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ k := fun k => by positivity
  set cen : ℕ → ℕ → ℕ → ℂ := fun k i j => (hSys k i j).center (hh (k + 1)) with hcen
  have hu : ∀ k : ℕ, (2 : ℝ)⁻¹ ^ (k + 1) = (2 : ℝ)⁻¹ ^ k * 2⁻¹ := fun k => pow_succ _ _
  have hin : ∀ k i j : ℕ, i < 2 ^ k → j < 2 ^ k → ∀ e, ∀ t ∈ Icc (0 : ℝ) 1,
      γ k i j e t ∈ closedUnitSquare := by
    intro k i j hi hj e t ht
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := (hSys k i j).inSq (hh (k + 1)) e ht
    have hi' := idx_le hi
    have hj' := idx_le hj
    have hp : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ k := by positivity
    rw [hu] at a1 a2 b1 b2
    refine ⟨le_trans (by positivity) a1, ?_, le_trans (by positivity) b1, ?_⟩
    · nlinarith
    · nlinarith
  have hinS : ∀ i j : ℕ, i + 2 ≤ 2 ^ K → j + 2 ≤ 2 ^ K → ∀ e, ∀ t ∈ Icc (0 : ℝ) 1,
      γS i j e t ∈ closedUnitSquare := by
    intro i j hi hj e t ht
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := (hSysS i j).inSq (hh K) e ht
    have hp : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ K := by positivity
    have e2 : ∀ a : ℕ, a + 2 ≤ 2 ^ K → ((a : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K ≤ 1 := fun a ha => by
      have h1 : ((a : ℝ) + 2) ≤ 2 ^ K := by exact_mod_cast ha
      rw [inv_pow, mul_inv_le_iff₀ (by positivity)]; linarith
    have := e2 i hi
    have := e2 j hj
    refine ⟨le_trans (by positivity) a1, by nlinarith, le_trans (by positivity) b1, by nlinarith⟩
  have hlen : ∀ k, K ≤ k → k ≤ m → ∀ i < 2 ^ k, ∀ j < 2 ^ k, ∀ e,
      lfppLen ξ f (γ k i j e) ≤ B k + η' := fun k hk1 hk2 i hi j hj e =>
    (hγL k i j e).trans (by gcongr; exact hB k hk1 hk2 i hi j hj e)
  -- the chaining from `z` up to its square of level `K`
  have hpt : ∀ z ∈ closedUnitSquare, lfppDOn ξ f closedUnitSquare z
      (cen K (colIdx m z.re / 2 ^ (m - K)) (colIdx m z.im / 2 ^ (m - K))) ≤
      E + 2 * ∑ t ∈ Finset.range (m - K + 1), 4 * (B (K + t) + η') := by
    intro z hz
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
    set I : ℕ → ℕ := fun k => colIdx m z.re / 2 ^ (m - k)
    set J : ℕ → ℕ := fun k => colIdx m z.im / 2 ^ (m - k)
    have hc := chain_center (d := lfppDOn ξ f closedUnitSquare) lfppDOn_triangle lfppDOn_comm
      (m - K) (fun t => ⋃ e, γ (K + t) (I (K + t)) (J (K + t)) e '' Icc 0 1)
      (fun t => cen (K + t) (I (K + t)) (J (K + t)))
      (fun t => 4 * (B (K + t) + η')) ?_ ?_ z E ?_
    · simpa only [add_zero] using hc
    · intro t ht u hu'
      have hk : K + t ≤ m := by omega
      obtain ⟨e, s, hs, rfl⟩ : ∃ e, ∃ s ∈ Icc (0 : ℝ) 1, γ (K + t) (I (K + t)) (J (K + t)) e s = u := by
        simpa only [mem_iUnion, mem_image] using hu'
      refine ((hSys (K + t) (I (K + t)) (J (K + t))).dist_center (hh _)
        (hin (K + t) _ _ (colIdx_div_lt hk _) (colIdx_div_lt hk _)) e hs).trans ?_
      calc ∑ e', lfppLen ξ f (γ (K + t) (I (K + t)) (J (K + t)) e') ≤
            ∑ _e' : Fin 4, (B (K + t) + η') :=
            Finset.sum_le_sum fun e' _ =>
              hlen (K + t) (by omega) hk _ (colIdx_div_lt hk _) _ (colIdx_div_lt hk _) e'
        _ = 4 * (B (K + t) + η') := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num
    · intro t ht
      have hk : K + t < m := by omega
      have hIk : I (K + t + 1) / 2 = I (K + t) := colIdx_div_succ m (K + t) hk z.re
      have hJk : J (K + t + 1) / 2 = J (K + t) := colIdx_div_succ m (K + t) hk z.im
      have e1 : K + (t + 1) = K + t + 1 := by omega
      rw [e1]
      have hS' := hSys (K + t + 1) (I (K + t + 1)) (J (K + t + 1))
      rw [show (2 : ℝ)⁻¹ ^ (K + t + 1 + 1) = (2 : ℝ)⁻¹ ^ (K + t + 1) / 2 by
        rw [pow_succ]; ring] at hS'
      have hcast : ∀ a b : ℕ, a / 2 = b →
          (2 * (a : ℝ) * ((2 : ℝ)⁻¹ ^ (K + t + 1) / 2) = 2 * b * (2 : ℝ)⁻¹ ^ (K + t + 1) ∨
            2 * (a : ℝ) * ((2 : ℝ)⁻¹ ^ (K + t + 1) / 2) =
              2 * b * (2 : ℝ)⁻¹ ^ (K + t + 1) + (2 : ℝ)⁻¹ ^ (K + t + 1)) := by
        intro a b hab
        rcases Nat.even_or_odd a with ⟨r, hr⟩ | ⟨r, hr⟩
        · left
          have : b = r := by omega
          subst this; rw [hr]; push_cast; ring
        · right
          have : b = r := by omega
          subst this; rw [hr]; push_cast; ring
      obtain ⟨e, s, hs, t', ht', est⟩ := (hSys (K + t) (I (K + t)) (J (K + t))).meet_child
        (hh _) hS' (hcast _ _ hIk) (hcast _ _ hJk)
      refine ⟨γ (K + t + 1) (I (K + t + 1)) (J (K + t + 1)) 0 s, ?_, ?_⟩
      · rw [est]; exact mem_iUnion.2 ⟨e, t', ht', rfl⟩
      · exact mem_iUnion.2 ⟨0, s, hs, rfl⟩
    · -- the link from `z` to the system of level `m`
      have em : K + (m - K) = m := by omega
      show ∃ p ∈ ⋃ e, γ (K + (m - K)) (I (K + (m - K))) (J (K + (m - K))) e '' Icc 0 1,
        lfppDOn ξ f closedUnitSquare z p ≤ E
      rw [em]
      have hIn : I m = colIdx m z.re := by simp [I]
      have hJn : J m = colIdx m z.im := by simp [J]
      set p := γ m (I m) (J m) 0 0
      refine ⟨p, mem_iUnion.2 ⟨0, 0, ⟨le_rfl, zero_le_one⟩, rfl⟩, ?_⟩
      have hS := hSys m (I m) (J m)
      have hp0 : p.re = 2 * (I m : ℝ) * (2 : ℝ)⁻¹ ^ (m + 1) := hS.h0e.1
      have hp1 := (hS.h0 0 ⟨le_rfl, zero_le_one⟩).2
      have hpin : p ∈ closedUnitSquare := hin m _ _ (colIdx_div_lt le_rfl _)
        (colIdx_div_lt le_rfl _) 0 0 ⟨le_rfl, zero_le_one⟩
      obtain ⟨hr1, hr2⟩ := abs_sub_colIdx (n := m) (t := z.re) ⟨hz1, hz2⟩
      obtain ⟨hi1, hi2⟩ := abs_sub_colIdx (n := m) (t := z.im) ⟨hz3, hz4⟩
      rw [← hIn] at hr1 hr2
      rw [← hJn] at hi1 hi2
      rw [hu] at hp0 hp1
      have hq : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
      have hnorm : ‖p - z‖ ≤ 2 * (2 : ℝ)⁻¹ ^ m := by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        rw [Complex.sub_re, Complex.sub_im]
        have h1 : |p.re - z.re| ≤ (2 : ℝ)⁻¹ ^ m := by
          rw [abs_le]; constructor <;> nlinarith
        have h2 : |p.im - z.im| ≤ (2 : ℝ)⁻¹ ^ m := by
          rw [abs_le]; constructor <;> nlinarith [hp1.1, hp1.2]
        linarith
      exact hE z ⟨hz1, hz2, hz3, hz4⟩ p hpin hnorm
  -- the common square of side `2^{1-K}`
  set Ix := colIdx m x.re / 2 ^ (m - K)
  set Iy := colIdx m y.re / 2 ^ (m - K)
  set Jx := colIdx m x.im / 2 ^ (m - K)
  set Jy := colIdx m y.im / 2 ^ (m - K)
  have h2K : 2 ≤ 2 ^ K := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK1
  have hIx := colIdx_div_lt hKm x.re
  have hIy := colIdx_div_lt hKm y.re
  have hJx := colIdx_div_lt hKm x.im
  have hJy := colIdx_div_lt hKm y.im
  have nIxy := colIdx_div_near (m := m) hKm ⟨hx.1, hx.2.1⟩ ⟨hy.1, hy.2.1⟩ hre
  have nIyx := colIdx_div_near (m := m) hKm ⟨hy.1, hy.2.1⟩ ⟨hx.1, hx.2.1⟩
    (by rwa [abs_sub_comm])
  have nJxy := colIdx_div_near (m := m) hKm ⟨hx.2.2.1, hx.2.2.2⟩ ⟨hy.2.2.1, hy.2.2.2⟩ him
  have nJyx := colIdx_div_near (m := m) hKm ⟨hy.2.2.1, hy.2.2.2⟩ ⟨hx.2.2.1, hx.2.2.2⟩
    (by rwa [abs_sub_comm])
  set i := min (min Ix Iy) (2 ^ K - 2)
  set j := min (min Jx Jy) (2 ^ K - 2)
  have hi2 : i + 2 ≤ 2 ^ K := by omega
  have hj2 : j + 2 ≤ 2 ^ K := by omega
  have hSS := hSysS i j
  set cS := hSS.center (hh K)
  have hlenS : ∀ e, lfppLen ξ f (γS i j e) ≤ B' + η' := fun e =>
    (hγSL i j e).trans (by gcongr; exact hB' i j hi2 hj2 e)
  have hrS : ∀ u ∈ ⋃ e, γS i j e '' Icc 0 1, lfppDOn ξ f closedUnitSquare cS u ≤ 4 * (B' + η') := by
    intro u hu'
    obtain ⟨e, s, hs, rfl⟩ : ∃ e, ∃ s ∈ Icc (0 : ℝ) 1, γS i j e s = u := by
      simpa only [mem_iUnion, mem_image] using hu'
    refine (hSS.dist_center (hh K) (hinS i j hi2 hj2) e hs).trans ?_
    calc ∑ e', lfppLen ξ f (γS i j e') ≤ ∑ _e' : Fin 4, (B' + η') :=
          Finset.sum_le_sum fun e' _ => hlenS e'
      _ = 4 * (B' + η') := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num
  -- the link from the level-`K` square of `z` to the common square
  have hlink : ∀ I J : ℕ, I < 2 ^ K → J < 2 ^ K → (I = i ∨ I = i + 1) → (J = j ∨ J = j + 1) →
      lfppDOn ξ f closedUnitSquare (cen K I J) cS ≤ 4 * (B K + η') + 4 * (B' + η') := by
    intro I J hI hJ hIi hJj
    have hS' := hSys K I J
    rw [show (2 : ℝ)⁻¹ ^ (K + 1) = (2 : ℝ)⁻¹ ^ K / 2 by rw [pow_succ]; ring] at hS'
    have hcast : ∀ a b : ℕ, (a = b ∨ a = b + 1) →
        (2 * (a : ℝ) * ((2 : ℝ)⁻¹ ^ K / 2) = b * (2 : ℝ)⁻¹ ^ K ∨
          2 * (a : ℝ) * ((2 : ℝ)⁻¹ ^ K / 2) = b * (2 : ℝ)⁻¹ ^ K + (2 : ℝ)⁻¹ ^ K) := by
      rintro a b (rfl | rfl)
      · left; ring
      · right; push_cast; ring
    obtain ⟨e, s, hs, t, ht, est⟩ := hSS.meet_child (hh K) hS' (hcast _ _ hIi) (hcast _ _ hJj)
    calc lfppDOn ξ f closedUnitSquare (cen K I J) cS
        ≤ lfppDOn ξ f closedUnitSquare (cen K I J) (γ K I J 0 s) +
            lfppDOn ξ f closedUnitSquare (γ K I J 0 s) cS := lfppDOn_triangle _ _ _
      _ ≤ 4 * (B K + η') + 4 * (B' + η') := by
          gcongr
          · refine ((hSys K I J).dist_center (hh _) (hin K I J hI hJ) 0 hs).trans ?_
            calc ∑ e', lfppLen ξ f (γ K I J e') ≤ ∑ _e' : Fin 4, (B K + η') :=
                  Finset.sum_le_sum fun e' _ => hlen K le_rfl hKm I hI J hJ e'
              _ = 4 * (B K + η') := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                  norm_num
          · rw [lfppDOn_comm, est]; exact hrS _ (mem_iUnion.2 ⟨e, t, ht, rfl⟩)
  have hBK : B K + η' ≤ ∑ t ∈ Finset.range (m - K + 1), (B (K + t) + η') := by
    have := Finset.single_le_sum (f := fun t => B (K + t) + η') (fun _ _ => zero_le)
      (Finset.mem_range.2 (Nat.succ_pos (m - K)))
    simpa only [add_zero] using this
  set R := ∑ t ∈ Finset.range (m - K + 1), (B (K + t) + η')
  have hone : ∀ z ∈ closedUnitSquare, ∀ I J : ℕ,
      I = colIdx m z.re / 2 ^ (m - K) → J = colIdx m z.im / 2 ^ (m - K) →
      (I = i ∨ I = i + 1) → (J = j ∨ J = j + 1) →
      lfppDOn ξ f closedUnitSquare z cS ≤ E + 12 * R + 4 * (B' + η') := by
    intro z hz I J hI hJ hIi hJj
    have h1 := hpt z hz
    rw [← hI, ← hJ] at h1
    have h2 := hlink I J (hI ▸ colIdx_div_lt hKm _) (hJ ▸ colIdx_div_lt hKm _) hIi hJj
    have hR : ∑ t ∈ Finset.range (m - K + 1), 4 * (B (K + t) + η') = 4 * R := by
      rw [Finset.mul_sum]
    calc lfppDOn ξ f closedUnitSquare z cS
        ≤ lfppDOn ξ f closedUnitSquare z (cen K I J) + lfppDOn ξ f closedUnitSquare (cen K I J) cS :=
          lfppDOn_triangle _ _ _
      _ ≤ (E + 2 * (4 * R)) + (4 * R + 4 * (B' + η')) :=
          add_le_add (h1.trans_eq (by rw [hR]))
            (h2.trans (add_le_add_left (show 4 * (B K + η') ≤ 4 * R from mul_le_mul_of_nonneg_left hBK zero_le) _))
      _ = E + 12 * R + 4 * (B' + η') := by ring
  have hx' := hone x hx Ix Jx rfl rfl (by omega) (by omega)
  have hy' := hone y hy Iy Jy rfl rfl (by omega) (by omega)
  have hsum : 2 * (E + 12 * R + 4 * (B' + η')) =
      2 * E + 8 * B' + 24 * ∑ t ∈ Finset.range (m - K + 1), B (K + t) +
        ENNReal.ofReal ((24 * (m - K + 1 : ℕ) + 8) * η) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by norm_num)]
    simp only [R, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]
    rw [show ENNReal.ofReal 24 = 24 by norm_num, show ENNReal.ofReal 8 = 8 by norm_num]
    ring
  have hηε : ENNReal.ofReal ((24 * (m - K + 1 : ℕ) + 8) * η) ≤ ε := by
    rw [hηdef]
    have hmK : ((m - K + 1 : ℕ) : ℝ) ≤ m := by
      have : m - K + 1 ≤ m := by omega
      exact_mod_cast this
    have h1 : (24 * ((m - K + 1 : ℕ) : ℝ) + 8) * ((ε : ℝ) / (32 * (m + 1))) ≤ (ε : ℝ) := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      have : (0 : ℝ) ≤ ε := ε.2
      nlinarith
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal h1
  calc lfppDOn ξ f closedUnitSquare x y
      ≤ lfppDOn ξ f closedUnitSquare x cS + lfppDOn ξ f closedUnitSquare cS y :=
        lfppDOn_triangle _ _ _
    _ ≤ (E + 12 * R + 4 * (B' + η')) + (E + 12 * R + 4 * (B' + η')) := by
        gcongr
        rw [lfppDOn_comm]; exact hy'
    _ = _ := by rw [← two_mul, hsum]
    _ ≤ _ := by gcongr

end S6P28U
end DDDF
end LQGMetric
