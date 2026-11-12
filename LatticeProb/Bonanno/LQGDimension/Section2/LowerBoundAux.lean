/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Section2.LowerBoundAux at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Section2
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Independence.Integration
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Auxiliary lemmas for Lemma 2.2 (`a_n ≥ 3 · 2^{-13/3} n`)

Deterministic part of the proof of Lemma 2.2:

* the tents `ψ_I` on the 16-adic intervals `I = [k 16^{-j}, (k+1) 16^{-j}]`, `j < n`,
  and the functions `f_σ = b Σ_I σ_I ψ_I ∈ V n`;
* the energy `E(f_σ) = n b² / 2` (orthogonality of the tent derivatives);
* the `L¹` lower bound `∫₀¹ |f_σ - f_τ| ≥ b Σ_{I ∈ D} ∫ T_I`, where `D` is the set of intervals
  at which the signs first differ along the ancestry.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped Classical

namespace LQGDimension.LowerBound22

/-! ## Tent functions -/

/-- The tent `ψ(t) = min(t, 1 - t)` on `[0,1]`, zero outside. -/
def tent (t : ℝ) : ℝ := max 0 (min t (1 - t))

lemma tent_nonneg (t : ℝ) : 0 ≤ tent t := le_max_left _ _

lemma tent_of_nonpos {t : ℝ} (h : t ≤ 0) : tent t = 0 := by
  unfold tent; exact max_eq_left ((min_le_left _ _).trans h)

lemma tent_of_one_le {t : ℝ} (h : 1 ≤ t) : tent t = 0 := by
  unfold tent; exact max_eq_left ((min_le_right _ _).trans (by linarith))

lemma tent_of_le_half {t : ℝ} (h0 : 0 ≤ t) (h : t ≤ 1 / 2) : tent t = t := by
  unfold tent; rw [min_eq_left (by linarith), max_eq_right h0]

lemma tent_of_half_le {t : ℝ} (h0 : 1 / 2 ≤ t) (h : t ≤ 1) : tent t = 1 - t := by
  unfold tent; rw [min_eq_right (by linarith), max_eq_right (by linarith)]

lemma continuous_tent : Continuous tent := by unfold tent; fun_prop

lemma pos_lt_one_of_tent_ne_zero {t : ℝ} (h : tent t ≠ 0) : 0 < t ∧ t < 1 := by
  refine ⟨?_, ?_⟩
  · by_contra hc; exact h (tent_of_nonpos (not_lt.mp hc))
  · by_contra hc; exact h (tent_of_one_le (not_lt.mp hc))

/-! ## 16-adic intervals -/

/-- The 16-adic intervals at levels `j < n`, encoded as pairs `(j, k)` with `k < 16^j`; the
interval is `[k 16^{-j}, (k+1) 16^{-j}]`. -/
def ivs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range n).sigma fun j => Finset.range (16 ^ j)).map
    (Equiv.sigmaEquivProd ℕ ℕ).toEmbedding

lemma mem_ivs {n : ℕ} {p : ℕ × ℕ} : p ∈ ivs n ↔ p.1 < n ∧ p.2 < 16 ^ p.1 := by
  obtain ⟨j, k⟩ := p
  simp [ivs]

lemma sum_ivs {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ × ℕ → M) :
    ∑ p ∈ ivs n, f p = ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range (16 ^ j), f (j, k) := by
  rw [ivs, Finset.sum_map, Finset.sum_sigma]
  rfl

/-- The length `16^{-j}` of an interval at level `j`. -/
def sc (j : ℕ) : ℝ := ((16 : ℝ) ^ j)⁻¹

lemma sc_pos (j : ℕ) : 0 < sc j := by unfold sc; positivity

lemma sc_mul_pow (j : ℕ) : sc j * (16 : ℝ) ^ j = 1 := by
  unfold sc; exact inv_mul_cancel₀ (by positivity)

/-- The tent `ψ_I` on the interval `I = (j, k)`. -/
def psi (p : ℕ × ℕ) (x : ℝ) : ℝ := sc p.1 * tent ((16 : ℝ) ^ p.1 * x - p.2)

lemma psi_nonneg (p : ℕ × ℕ) (x : ℝ) : 0 ≤ psi p x :=
  mul_nonneg (sc_pos _).le (tent_nonneg _)

lemma continuous_psi (p : ℕ × ℕ) : Continuous (psi p) := by
  unfold psi; exact continuous_const.mul (continuous_tent.comp (by fun_prop))

lemma psi_of_nonpos (p : ℕ × ℕ) {x : ℝ} (hx : x ≤ 0) : psi p x = 0 := by
  unfold psi
  have h1 : (16 : ℝ) ^ p.1 * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hx
  have h2 : (0 : ℝ) ≤ p.2 := Nat.cast_nonneg _
  rw [tent_of_nonpos (by linarith), mul_zero]

lemma cast_succ_le_pow {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ ivs n) : (p.2 : ℝ) + 1 ≤ (16 : ℝ) ^ p.1 := by
  have := Nat.succ_le_of_lt (mem_ivs.mp hp).2
  exact_mod_cast this

lemma psi_of_one_le {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ ivs n) {x : ℝ} (hx : 1 ≤ x) : psi p x = 0 := by
  unfold psi
  have h1 := cast_succ_le_pow hp
  have h2 : (16 : ℝ) ^ p.1 ≤ (16 : ℝ) ^ p.1 * x := le_mul_of_one_le_right (by positivity) hx
  rw [tent_of_one_le (by linarith), mul_zero]

/-- Each tent is affine on every interval of the mesh `16^{-n}`. -/
lemma psi_affine {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ ivs n) (m : ℕ) :
    ∃ α β : ℝ, ∀ x ∈ Icc ((m : ℝ) / 16 ^ n) (((m : ℝ) + 1) / 16 ^ n), psi p x = α * x + β := by
  obtain ⟨j, k⟩ := p
  obtain ⟨hj, hk⟩ := mem_ivs.mp hp
  simp only at hj hk
  set M : ℕ := 8 * 16 ^ (n - j - 1) with hM
  have hMpos : (0 : ℝ) < 2 * (M : ℝ) := by rw [hM]; positivity
  have hNM : (16 : ℝ) ^ n = (16 : ℝ) ^ j * (2 * (M : ℝ)) := by
    have e : n = j + 1 + (n - j - 1) := by omega
    rw [hM]; push_cast
    rw [show (16 : ℝ) ^ n = (16 : ℝ) ^ (j + 1 + (n - j - 1)) by rw [← e]]
    rw [pow_add, pow_succ]; ring
  have hcases : m + 1 ≤ k * (2 * M) ∨ (k * (2 * M) ≤ m ∧ m + 1 ≤ k * (2 * M) + M) ∨
      (k * (2 * M) + M ≤ m ∧ m + 1 ≤ k * (2 * M) + 2 * M) ∨ k * (2 * M) + 2 * M ≤ m := by
    omega
  have hx12 : ∀ x ∈ Icc ((m : ℝ) / 16 ^ n) (((m : ℝ) + 1) / 16 ^ n),
      (m : ℝ) ≤ ((16 : ℝ) ^ j * x) * (2 * M) ∧ ((16 : ℝ) ^ j * x) * (2 * M) ≤ (m : ℝ) + 1 := by
    intro x hx
    have h16 : (0 : ℝ) < 16 ^ n := by positivity
    have hx1 := (div_le_iff₀ h16).mp hx.1
    have hx2 := (le_div_iff₀ h16).mp hx.2
    have e : ((16 : ℝ) ^ j * x) * (2 * M) = x * 16 ^ n := by rw [hNM]; ring
    rw [e]; exact ⟨hx1, hx2⟩
  have hsc := sc_mul_pow j
  rcases hcases with h | h | h | h
  · refine ⟨0, 0, fun x hx => ?_⟩
    obtain ⟨h1, h2⟩ := hx12 x hx
    have h' : ((m : ℝ) + 1) ≤ (k : ℝ) * (2 * M) := by exact_mod_cast h
    have : (16 : ℝ) ^ j * x ≤ k := le_of_mul_le_mul_right (by linarith) hMpos
    simp only [psi]
    rw [tent_of_nonpos (by linarith)]; ring
  · refine ⟨1, -(k : ℝ) * sc j, fun x hx => ?_⟩
    obtain ⟨h1, h2⟩ := hx12 x hx
    have ha : (k : ℝ) * (2 * M) ≤ m := by exact_mod_cast h.1
    have hb : (m : ℝ) + 1 ≤ (k : ℝ) * (2 * M) + M := by exact_mod_cast h.2
    have c1 : (k : ℝ) ≤ (16 : ℝ) ^ j * x := le_of_mul_le_mul_right (by linarith) hMpos
    have c2 : (16 : ℝ) ^ j * x ≤ (k : ℝ) + 1 / 2 :=
      le_of_mul_le_mul_right (by nlinarith) hMpos
    simp only [psi]
    rw [tent_of_le_half (by linarith) (by linarith)]
    linear_combination x * hsc
  · refine ⟨-1, ((k : ℝ) + 1) * sc j, fun x hx => ?_⟩
    obtain ⟨h1, h2⟩ := hx12 x hx
    have ha : (k : ℝ) * (2 * M) + M ≤ m := by exact_mod_cast h.1
    have hb : (m : ℝ) + 1 ≤ (k : ℝ) * (2 * M) + 2 * M := by exact_mod_cast h.2
    have c1 : (k : ℝ) + 1 / 2 ≤ (16 : ℝ) ^ j * x :=
      le_of_mul_le_mul_right (by nlinarith) hMpos
    have c2 : (16 : ℝ) ^ j * x ≤ (k : ℝ) + 1 := le_of_mul_le_mul_right (by nlinarith) hMpos
    simp only [psi]
    rw [tent_of_half_le (by linarith) (by linarith)]
    linear_combination -x * hsc
  · refine ⟨0, 0, fun x hx => ?_⟩
    obtain ⟨h1, h2⟩ := hx12 x hx
    have h' : (k : ℝ) * (2 * M) + 2 * M ≤ m := by exact_mod_cast h
    have : (k : ℝ) + 1 ≤ (16 : ℝ) ^ j * x := le_of_mul_le_mul_right (by nlinarith) hMpos
    simp only [psi]
    rw [tent_of_one_le (by linarith)]; ring

/-! ## Sign assignments and the functions `f_σ` -/

/-- Sign assignments on the intervals of levels `< n`. -/
abbrev SA (n : ℕ) : Type := ↥(ivs n) → Bool

/-- A sign assignment, extended by `false` outside `ivs n`. -/
def sv {n : ℕ} (σ : SA n) (p : ℕ × ℕ) : Bool := if h : p ∈ ivs n then σ ⟨p, h⟩ else false

/-- The sign `±1` of a boolean. -/
def sgn (s : Bool) : ℝ := if s then 1 else -1

lemma sgn_mul_self (s : Bool) : sgn s * sgn s = 1 := by cases s <;> norm_num [sgn]

lemma abs_sgn (s : Bool) : |sgn s| = 1 := by cases s <;> norm_num [sgn]

lemma sgn_mul_sub_of_ne {s t : Bool} (h : s ≠ t) : sgn s * (sgn s - sgn t) = 2 := by
  cases s <;> cases t <;> simp_all [sgn] <;> norm_num

lemma neg_two_le_sgn_mul_sub (s t u : Bool) : -2 ≤ sgn s * (sgn t - sgn u) := by
  cases s <;> cases t <;> cases u <;> norm_num [sgn]

/-- `f_σ = b Σ_I σ_I ψ_I`. -/
def fS (b : ℝ) {n : ℕ} (σ : SA n) (x : ℝ) : ℝ := b * ∑ p ∈ ivs n, sgn (sv σ p) * psi p x

lemma continuous_fS (b : ℝ) {n : ℕ} (σ : SA n) : Continuous (fS b σ) := by
  unfold fS
  exact continuous_const.mul
    (continuous_finsetSum _ fun p _ => continuous_const.mul (continuous_psi p))

lemma fS_mem_V (b : ℝ) {n : ℕ} (σ : SA n) : fS b σ ∈ V n := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold fS
    rw [Finset.sum_eq_zero, mul_zero]
    intro p _; rw [psi_of_nonpos p le_rfl, mul_zero]
  · unfold fS
    rw [Finset.sum_eq_zero, mul_zero]
    intro p hp; rw [psi_of_one_le hp le_rfl, mul_zero]
  · intro x hx
    rw [Set.mem_Icc, not_and_or] at hx
    unfold fS
    rw [Finset.sum_eq_zero, mul_zero]
    intro p hp
    rcases hx with h | h
    · rw [psi_of_nonpos p (not_le.mp h).le, mul_zero]
    · rw [psi_of_one_le hp (not_le.mp h).le, mul_zero]
  · intro m _
    choose α β hαβ using fun p : ivs n => psi_affine p.2 m
    refine ⟨b * ∑ p : ivs n, sgn (sv σ p) * α p, b * ∑ p : ivs n, sgn (sv σ p) * β p, ?_⟩
    intro x hx
    unfold fS
    rw [← Finset.sum_coe_sort (ivs n)]
    have : ∀ p : ivs n, sgn (sv σ ↑p) * psi (↑p) x =
        sgn (sv σ p) * α p * x + sgn (sv σ p) * β p := fun p => by rw [hαβ p x hx]; ring
    rw [Finset.sum_congr rfl fun p _ => this p, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring

/-! ## Derivatives of the tents -/

/-- The derivative of the tent away from `0, 1/2, 1`. -/
def dtent (t : ℝ) : ℝ :=
  if t ∈ Ioo (0 : ℝ) (1 / 2) then 1 else if t ∈ Ioo (1 / 2 : ℝ) 1 then -1 else 0

/-- `t ↦ max 0 (min t 1)`; its derivative is `dtent t ^ 2` away from `0, 1/2, 1`. -/
def clampF (t : ℝ) : ℝ := max 0 (min t 1)

lemma continuous_clampF : Continuous clampF := by unfold clampF; fun_prop

lemma measurable_dtent : Measurable dtent := by
  unfold dtent
  exact Measurable.ite measurableSet_Ioo measurable_const
    (Measurable.ite measurableSet_Ioo measurable_const measurable_const)

lemma abs_dtent_le (t : ℝ) : |dtent t| ≤ 1 := by
  unfold dtent; split_ifs <;> norm_num

lemma pos_lt_one_of_dtent_ne_zero {t : ℝ} (h : dtent t ≠ 0) : 0 < t ∧ t < 1 := by
  unfold dtent at h
  split_ifs at h with h1 h2
  · exact ⟨h1.1, by linarith [h1.2]⟩
  · exact ⟨by linarith [h2.1], h2.2⟩
  · exact absurd rfl h

lemma hasDerivAt_tent_clamp {t : ℝ} (h0 : t ≠ 0) (h1 : t ≠ 1 / 2) (h2 : t ≠ 1) :
    HasDerivAt tent (dtent t) t ∧ HasDerivAt clampF (dtent t ^ 2) t := by
  rcases lt_or_gt_of_ne h0 with ha | ha
  · have hd : dtent t = 0 := by
      simp only [dtent, mem_Ioo]
      rw [ite_eq_right (fun h => by linarith [h.1]), ite_eq_right (fun h => by linarith [h.1])]
    rw [hd]
    constructor
    · refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds ha] with s hs
      exact tent_of_nonpos (le_of_lt hs)
    · rw [show (0 : ℝ) ^ 2 = 0 by norm_num]
      refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds ha] with s hs
      simp only [clampF]; exact max_eq_left ((min_le_left _ _).trans (le_of_lt hs))
  rcases lt_or_gt_of_ne h1 with hb | hb
  · have hd : dtent t = 1 := by simp only [dtent, mem_Ioo]; rw [ite_eq_left ⟨ha, hb⟩]
    rw [hd]
    constructor
    · refine (hasDerivAt_id' t).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds ha hb] with s hs
      exact tent_of_le_half hs.1.le hs.2.le
    · rw [one_pow]
      refine (hasDerivAt_id' t).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds ha (show t < 1 by linarith)] with s hs
      simp only [clampF]; rw [min_eq_left hs.2.le, max_eq_right hs.1.le]
  rcases lt_or_gt_of_ne h2 with hc | hc
  · have hd : dtent t = -1 := by
      simp only [dtent, mem_Ioo]
      rw [ite_eq_right (fun h => by linarith [h.2]), ite_eq_left ⟨hb, hc⟩]
    rw [hd]
    constructor
    · refine ((hasDerivAt_id' t).const_sub 1).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hb hc] with s hs
      exact tent_of_half_le hs.1.le hs.2.le
    · rw [show (-1 : ℝ) ^ 2 = 1 by norm_num]
      refine (hasDerivAt_id' t).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < t by linarith) hc] with s hs
      simp only [clampF]; rw [min_eq_left hs.2.le, max_eq_right hs.1.le]
  · have hd : dtent t = 0 := by
      simp only [dtent, mem_Ioo]
      rw [ite_eq_right (fun h => by linarith [h.2]), ite_eq_right (fun h => by linarith [h.2])]
    rw [hd]
    constructor
    · refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hc] with s hs
      exact tent_of_one_le (le_of_lt hs)
    · rw [show (0 : ℝ) ^ 2 = 0 by norm_num]
      refine (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hc] with s hs
      simp only [clampF]; rw [min_eq_right (le_of_lt hs)]; norm_num

/-- The derivative of `ψ_I` (away from the countable set `exc`). -/
def dpsi (p : ℕ × ℕ) (x : ℝ) : ℝ := dtent ((16 : ℝ) ^ p.1 * x - p.2)

/-- An antiderivative of `dpsi p ^ 2`. -/
def cpsi (p : ℕ × ℕ) (x : ℝ) : ℝ := sc p.1 * clampF ((16 : ℝ) ^ p.1 * x - p.2)

lemma continuous_cpsi (p : ℕ × ℕ) : Continuous (cpsi p) := by
  unfold cpsi; exact continuous_const.mul (continuous_clampF.comp (by fun_prop))

lemma measurable_dpsi (p : ℕ × ℕ) : Measurable (dpsi p) :=
  measurable_dtent.comp (by fun_prop)

lemma abs_dpsi_le (p : ℕ × ℕ) (x : ℝ) : |dpsi p x| ≤ 1 := abs_dtent_le _

/-- The countable set of points `m / (2 · 16^j)`, off which all tents are differentiable. -/
def exc : Set ℝ := Set.range fun q : ℤ × ℕ => (q.1 : ℝ) / (2 * 16 ^ q.2)

lemma exc_countable : exc.Countable := Set.countable_range _

lemma ne_of_notMem_exc {x : ℝ} (hx : x ∉ exc) (j k : ℕ) (m : ℤ) :
    2 * ((16 : ℝ) ^ j * x - k) ≠ m := by
  intro h
  apply hx
  refine ⟨(m + 2 * k, j), ?_⟩
  show (((m + 2 * k : ℤ)) : ℝ) / (2 * 16 ^ j) = x
  rw [div_eq_iff (by positivity)]
  push_cast
  linarith

lemma hasDerivAt_psi_cpsi {x : ℝ} (hx : x ∉ exc) (p : ℕ × ℕ) :
    HasDerivAt (psi p) (dpsi p x) x ∧ HasDerivAt (cpsi p) (dpsi p x ^ 2) x := by
  have h0 : (16 : ℝ) ^ p.1 * x - p.2 ≠ 0 := fun h =>
    ne_of_notMem_exc hx p.1 p.2 0 (by rw [h]; simp)
  have h1 : (16 : ℝ) ^ p.1 * x - p.2 ≠ 1 / 2 := fun h =>
    ne_of_notMem_exc hx p.1 p.2 1 (by rw [h]; norm_num)
  have h2 : (16 : ℝ) ^ p.1 * x - p.2 ≠ 1 := fun h =>
    ne_of_notMem_exc hx p.1 p.2 2 (by rw [h]; norm_num)
  obtain ⟨hT, hC⟩ := hasDerivAt_tent_clamp h0 h1 h2
  have hin : HasDerivAt (fun y => (16 : ℝ) ^ p.1 * y - p.2) ((16 : ℝ) ^ p.1) x := by
    simpa using ((hasDerivAt_id' x).const_mul ((16 : ℝ) ^ p.1)).sub_const (p.2 : ℝ)
  have hsc := sc_mul_pow p.1
  constructor
  · have := (hT.comp x hin).const_mul (sc p.1)
    refine this.congr_deriv ?_
    simp only [dpsi]
    linear_combination dtent ((16 : ℝ) ^ p.1 * x - p.2) * hsc
  · have := (hC.comp x hin).const_mul (sc p.1)
    refine this.congr_deriv ?_
    simp only [dpsi]
    linear_combination dtent ((16 : ℝ) ^ p.1 * x - p.2) ^ 2 * hsc

lemma intervalIntegrable_of_bdd {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (h : ∀ x, |f x| ≤ C)
    (a b : ℝ) : IntervalIntegrable f volume a b := by
  refine (intervalIntegrable_const (c := C)).mono_fun' hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using h x)

lemma intervalIntegrable_dpsi_mul (p q : ℕ × ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => dpsi p x * dpsi q x) volume a b := by
  refine intervalIntegrable_of_bdd ((measurable_dpsi p).mul (measurable_dpsi q)) (C := 1)
    (fun x => ?_) a b
  show |dpsi p x * dpsi q x| ≤ 1
  rw [abs_mul]
  exact (mul_le_mul (abs_dpsi_le p x) (abs_dpsi_le q x) (abs_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

lemma intervalIntegrable_sum' {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {a b : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun x => ∑ i ∈ s, f i x) volume a b := by
  have e : (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, f i := by
    funext x; simp [Finset.sum_apply]
  rw [e]
  exact IntervalIntegrable.sum s h

lemma integral_dpsi {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ ivs n) : ∫ x in (0 : ℝ)..1, dpsi p x = 0 := by
  rw [integral_eq_of_hasDerivAt_off_countable_of_le (psi p) (dpsi p) zero_le_one exc_countable
    (continuous_psi p).continuousOn (fun x hx => (hasDerivAt_psi_cpsi hx.2 p).1)
    (intervalIntegrable_of_bdd (measurable_dpsi p) (abs_dpsi_le p) 0 1)]
  rw [psi_of_one_le hp le_rfl, psi_of_nonpos p le_rfl, sub_zero]

lemma integral_dpsi_sq {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ ivs n) :
    ∫ x in (0 : ℝ)..1, dpsi p x ^ 2 = sc p.1 := by
  have hii : IntervalIntegrable (fun x => dpsi p x ^ 2) volume 0 1 := by
    simpa [sq] using intervalIntegrable_dpsi_mul p p 0 1
  rw [integral_eq_of_hasDerivAt_off_countable_of_le (cpsi p) (fun x => dpsi p x ^ 2) zero_le_one
    exc_countable (continuous_cpsi p).continuousOn (fun x hx => (hasDerivAt_psi_cpsi hx.2 p).2)
    hii]
  have h1 := cast_succ_le_pow hp
  have h2 : (0 : ℝ) ≤ p.2 := Nat.cast_nonneg _
  have e1 : clampF ((16 : ℝ) ^ p.1 * 1 - p.2) = 1 := by
    unfold clampF; rw [min_eq_right (by linarith), max_eq_right zero_le_one]
  have e0 : clampF ((16 : ℝ) ^ p.1 * 0 - p.2) = 0 := by
    unfold clampF; rw [mul_zero, min_eq_left (by linarith), max_eq_left (by linarith)]
  simp only [cpsi, e1, e0]; ring

lemma dpsi_ne_zero {p : ℕ × ℕ} {x : ℝ} (h : dpsi p x ≠ 0) :
    (p.2 : ℝ) < (16 : ℝ) ^ p.1 * x ∧ (16 : ℝ) ^ p.1 * x < p.2 + 1 := by
  have := pos_lt_one_of_dtent_ne_zero h
  constructor <;> linarith [this.1, this.2]

lemma nat_eq_of_mem_Ioo {u : ℝ} {k k' : ℕ} (h : (k : ℝ) < u ∧ u < k + 1)
    (h' : (k' : ℝ) < u ∧ u < k' + 1) : k = k' := by
  have a : (k : ℝ) < k' + 1 := by linarith [h.1, h'.2]
  have b : (k' : ℝ) < k + 1 := by linarith [h'.1, h.2]
  have a' : k < k' + 1 := by exact_mod_cast a
  have b' : k' < k + 1 := by exact_mod_cast b
  omega

lemma iff_nat_of_mem_Ioo {u : ℝ} {k A B : ℕ} (hu : (k : ℝ) < u ∧ u < k + 1) :
    ((A : ℝ) < u ∧ u < B) ↔ (A ≤ k ∧ k + 1 ≤ B) := by
  constructor
  · rintro ⟨h1, h2⟩
    have a : (A : ℝ) < k + 1 := by linarith [hu.2]
    have b : (k : ℝ) < B := by linarith [hu.1]
    have a' : A < k + 1 := by exact_mod_cast a
    have b' : k < B := by exact_mod_cast b
    omega
  · rintro ⟨h1, h2⟩
    have a : (A : ℝ) ≤ k := by exact_mod_cast h1
    have b : (k : ℝ) + 1 ≤ B := by exact_mod_cast h2
    constructor <;> linarith [hu.1, hu.2]

lemma dpsi_mul_dpsi_same_level {p q : ℕ × ℕ} (h1 : p.1 = q.1) (h2 : p.2 ≠ q.2) (x : ℝ) :
    dpsi p x * dpsi q x = 0 := by
  by_contra h
  obtain ⟨hp, hq⟩ := mul_ne_zero_iff.mp h
  have a := dpsi_ne_zero hp
  have b := dpsi_ne_zero hq
  rw [h1] at a
  exact h2 (nat_eq_of_mem_Ioo a b)

/-- A coarser tent derivative is constant on each finer open interval. -/
lemma dpsi_const_of_lt {p q : ℕ × ℕ} (hpq : p.1 < q.1) {x y : ℝ}
    (hx : (q.2 : ℝ) < (16 : ℝ) ^ q.1 * x ∧ (16 : ℝ) ^ q.1 * x < q.2 + 1)
    (hy : (q.2 : ℝ) < (16 : ℝ) ^ q.1 * y ∧ (16 : ℝ) ^ q.1 * y < q.2 + 1) :
    dpsi p x = dpsi p y := by
  obtain ⟨j, k⟩ := p
  obtain ⟨j', k'⟩ := q
  simp only at hpq hx hy ⊢
  set M : ℕ := 8 * 16 ^ (j' - j - 1) with hM
  have hMpos : (0 : ℝ) < M := by rw [hM]; positivity
  have hNM : (16 : ℝ) ^ j' = (16 : ℝ) ^ j * (2 * (M : ℝ)) := by
    have e : j' = j + 1 + (j' - j - 1) := by omega
    rw [hM]; push_cast
    rw [show (16 : ℝ) ^ j' = (16 : ℝ) ^ (j + 1 + (j' - j - 1)) by rw [← e]]
    rw [pow_add, pow_succ]; ring
  have key : ∀ z : ℝ, ((k' : ℝ) < (16 : ℝ) ^ j' * z ∧ (16 : ℝ) ^ j' * z < k' + 1) →
      dpsi (j, k) z = if (k * (2 * M) ≤ k' ∧ k' + 1 ≤ k * (2 * M) + M) then 1
        else if (k * (2 * M) + M ≤ k' ∧ k' + 1 ≤ k * (2 * M) + 2 * M) then -1 else 0 := by
    intro z hz
    have e : (16 : ℝ) ^ j' * z = ((16 : ℝ) ^ j * z) * (2 * M) := by rw [hNM]; ring
    rw [e] at hz
    have c1 := iff_nat_of_mem_Ioo (A := k * (2 * M)) (B := k * (2 * M) + M) hz
    have c2 := iff_nat_of_mem_Ioo (A := k * (2 * M) + M) (B := k * (2 * M) + 2 * M) hz
    push_cast at c1 c2
    have d1 : ((16 : ℝ) ^ j * z - k ∈ Ioo (0 : ℝ) (1 / 2)) ↔
        ((k : ℝ) * (2 * M) < 16 ^ j * z * (2 * M) ∧ 16 ^ j * z * (2 * M) < k * (2 * M) + M) := by
      rw [mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩; constructor <;> nlinarith
      · rintro ⟨h1, h2⟩; constructor <;> nlinarith
    have d2 : ((16 : ℝ) ^ j * z - k ∈ Ioo (1 / 2 : ℝ) 1) ↔
        ((k : ℝ) * (2 * M) + M < 16 ^ j * z * (2 * M) ∧
          16 ^ j * z * (2 * M) < k * (2 * M) + 2 * M) := by
      rw [mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩; constructor <;> nlinarith
      · rintro ⟨h1, h2⟩; constructor <;> nlinarith
    simp only [dpsi, dtent]
    simp only [d1.trans c1, d2.trans c2]
  rw [key x hx, key y hy]

lemma dpsi_mul_dpsi_of_lt {p q : ℕ × ℕ} (hpq : p.1 < q.1) (x : ℝ) :
    dpsi p x * dpsi q x = dpsi p (((q.2 : ℝ) + 1 / 2) / 16 ^ q.1) * dpsi q x := by
  by_cases hq : dpsi q x = 0
  · rw [hq, mul_zero, mul_zero]
  · congr 1
    apply dpsi_const_of_lt hpq (dpsi_ne_zero hq)
    have : (16 : ℝ) ^ q.1 * (((q.2 : ℝ) + 1 / 2) / 16 ^ q.1) = q.2 + 1 / 2 := by
      field_simp
    rw [this]; constructor <;> linarith

lemma integral_dpsi_mul {n : ℕ} {p q : ℕ × ℕ} (hp : p ∈ ivs n) (hq : q ∈ ivs n) :
    ∫ x in (0 : ℝ)..1, dpsi p x * dpsi q x = if p = q then sc p.1 else 0 := by
  split_ifs with hpq
  · subst hpq; simp_rw [← sq]; exact integral_dpsi_sq hp
  · rcases lt_trichotomy p.1 q.1 with h | h | h
    · simp_rw [dpsi_mul_dpsi_of_lt h]
      rw [intervalIntegral.integral_const_mul, integral_dpsi hq, mul_zero]
    · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h h2)
      simp_rw [dpsi_mul_dpsi_same_level h h2]; simp
    · simp_rw [mul_comm (dpsi p _) (dpsi q _), dpsi_mul_dpsi_of_lt h]
      rw [intervalIntegral.integral_const_mul, integral_dpsi hp, mul_zero]

/-! ## The energy of `f_σ` -/

lemma hasDerivAt_fS (b : ℝ) {n : ℕ} (σ : SA n) {x : ℝ} (hx : x ∉ exc) :
    HasDerivAt (fS b σ) (b * ∑ p ∈ ivs n, sgn (sv σ p) * dpsi p x) x := by
  have : HasDerivAt (fun y => ∑ p ∈ ivs n, sgn (sv σ p) * psi p y)
      (∑ p ∈ ivs n, sgn (sv σ p) * dpsi p x) x :=
    HasDerivAt.fun_sum (fun p _ => ((hasDerivAt_psi_cpsi hx p).1).const_mul _)
  exact this.const_mul b

lemma sum_sc (n : ℕ) : ∑ p ∈ ivs n, sc p.1 = n := by
  rw [sum_ivs]
  have h : ∀ j, ((16 : ℝ) ^ j) * sc j = 1 := fun j => by rw [mul_comm]; exact sc_mul_pow j
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  simp only [h, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- `E(f_σ) = n b² / 2`. -/
lemma energy_fS (b : ℝ) {n : ℕ} (σ : SA n) : energy (fS b σ) = n * b ^ 2 / 2 := by
  unfold energy
  have h1 : ∫ x in (0 : ℝ)..1, deriv (fS b σ) x ^ 2 =
      ∫ x in (0 : ℝ)..1, (b * ∑ p ∈ ivs n, sgn (sv σ p) * dpsi p x) ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [exc_countable.ae_notMem volume] with x hx _
    rw [(hasDerivAt_fS b σ hx).deriv]
  rw [h1]
  have h2 : ∀ x, (b * ∑ p ∈ ivs n, sgn (sv σ p) * dpsi p x) ^ 2 =
      ∑ p ∈ ivs n, ∑ q ∈ ivs n,
        b ^ 2 * (sgn (sv σ p) * sgn (sv σ q)) * (dpsi p x * dpsi q x) := by
    intro x
    rw [mul_pow, sq (∑ p ∈ ivs n, _), Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  simp_rw [h2]
  rw [intervalIntegral.integral_finsetSum]
  · have h3 : ∀ p ∈ ivs n, ∫ x in (0 : ℝ)..1, ∑ q ∈ ivs n,
        b ^ 2 * (sgn (sv σ p) * sgn (sv σ q)) * (dpsi p x * dpsi q x) = b ^ 2 * sc p.1 := by
      intro p hp
      rw [intervalIntegral.integral_finsetSum]
      · simp_rw [intervalIntegral.integral_const_mul]
        rw [Finset.sum_congr rfl fun q hq => by rw [integral_dpsi_mul hp hq]]
        simp_rw [mul_ite, mul_zero]
        rw [Finset.sum_ite_eq, ite_eq_left hp, sgn_mul_self, mul_one]
      · intro q _
        exact (intervalIntegrable_dpsi_mul p q 0 1).const_mul _
    rw [Finset.sum_congr rfl h3, ← Finset.mul_sum, sum_sc]
    ring
  · intro p _
    exact intervalIntegrable_sum' _ fun q _ => (intervalIntegrable_dpsi_mul p q 0 1).const_mul _

/-! ## Levels and ancestry -/

/-- The index of the level-`j` interval containing `x`. -/
def lev (j : ℕ) (x : ℝ) : ℕ := ⌊(16 : ℝ) ^ j * x⌋₊

lemma div_pow_div (k a b : ℕ) : k / 16 ^ a / 16 ^ b = k / 16 ^ (a + b) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add]

lemma lev_eq_div {i j : ℕ} (h : i ≤ j) (x : ℝ) : lev i x = lev j x / 16 ^ (j - i) := by
  unfold lev
  have hp : (16 : ℝ) ^ j = 16 ^ i * 16 ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' h]
  have e : (16 : ℝ) ^ i * x = (16 : ℝ) ^ j * x / ((16 ^ (j - i) : ℕ) : ℝ) := by
    push_cast
    rw [hp]; field_simp
  rw [e, Nat.floor_div_natCast]

lemma lev_of_psi_ne_zero {p : ℕ × ℕ} {x : ℝ} (h : psi p x ≠ 0) : lev p.1 x = p.2 := by
  have h' : tent ((16 : ℝ) ^ p.1 * x - p.2) ≠ 0 := fun h0 => h (by simp [psi, h0])
  have := pos_lt_one_of_tent_ne_zero h'
  have h2 : (0 : ℝ) ≤ p.2 := Nat.cast_nonneg _
  unfold lev
  rw [Nat.floor_eq_iff (by linarith [this.1])]
  constructor <;> linarith [this.1, this.2]

/-- The intervals at which the signs of `σ` and `τ` first differ along the ancestry. -/
def dset {n : ℕ} (σ τ : SA n) : Finset (ℕ × ℕ) :=
  (ivs n).filter fun p => sv σ p ≠ sv τ p ∧
    ∀ i < p.1, sv σ (i, p.2 / 16 ^ (p.1 - i)) = sv τ (i, p.2 / 16 ^ (p.1 - i))

/-- `q` lies strictly below `p` in the 16-adic tree. -/
def sdesc (p q : ℕ × ℕ) : Prop := p.1 < q.1 ∧ q.2 / 16 ^ (q.1 - p.1) = p.2

instance (p q : ℕ × ℕ) : Decidable (sdesc p q) := by unfold sdesc; infer_instance

lemma not_sdesc_self (p : ℕ × ℕ) : ¬ sdesc p p := fun h => lt_irrefl _ h.1

/-- Coefficients of `T_p = 2 ψ_p - 2 Σ_{q strictly below p} ψ_q`. -/
def tc (p q : ℕ × ℕ) : ℝ := if q = p then 2 else if sdesc p q then -2 else 0

/-- The test function `T_p = 2 ψ_p - 2 Σ_{q strictly below p} ψ_q`. -/
def Tf (n : ℕ) (p : ℕ × ℕ) (x : ℝ) : ℝ := ∑ q ∈ ivs n, tc p q * psi q x

lemma continuous_Tf (n : ℕ) (p : ℕ × ℕ) : Continuous (Tf n p) := by
  unfold Tf; exact continuous_finsetSum _ fun q _ => continuous_const.mul (continuous_psi q)

lemma sum_tc {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ ivs n) (r : ℕ × ℕ → ℝ) :
    ∑ q ∈ ivs n, tc p q * r q = 2 * r p - 2 * ∑ q ∈ (ivs n).filter (sdesc p), r q := by
  have h : ∀ q, tc p q * r q = (if q = p then 2 * r q else 0) + (if sdesc p q then -2 * r q else 0) := by
    intro q
    unfold tc
    by_cases h1 : q = p
    · subst h1; simp [not_sdesc_self]
    · by_cases h2 : sdesc p q <;> simp [h1, h2]
  rw [Finset.sum_congr rfl fun q _ => h q, Finset.sum_add_distrib, Finset.sum_ite_eq',
    ite_eq_left hp, ← Finset.sum_filter, ← Finset.mul_sum]
  ring

lemma sgn_mul_sub_psi_ge {n : ℕ} {σ τ : SA n} {p : ℕ × ℕ} (hp : p ∈ dset σ τ) {x : ℝ}
    (hx : lev p.1 x = p.2) (q : ℕ × ℕ) :
    tc p q * psi q x ≤ sgn (sv σ p) * (sgn (sv σ q) - sgn (sv τ q)) * psi q x := by
  obtain ⟨_, hne, hanc⟩ := Finset.mem_filter.mp hp
  have hψ := psi_nonneg q x
  unfold tc
  by_cases h1 : q = p
  · subst h1; rw [ite_eq_left rfl, sgn_mul_sub_of_ne hne]
  rw [ite_eq_right h1]
  by_cases h2 : sdesc p q
  · rw [ite_eq_left h2]
    have := neg_two_le_sgn_mul_sub (sv σ p) (sv σ q) (sv τ q)
    nlinarith
  rw [ite_eq_right h2, zero_mul]
  by_cases hψ0 : psi q x = 0
  · rw [hψ0, mul_zero]
  have hq := lev_of_psi_ne_zero hψ0
  rcases lt_trichotomy q.1 p.1 with h | h | h
  · have e : q.2 = p.2 / 16 ^ (p.1 - q.1) := by rw [← hq, lev_eq_div h.le x, hx]
    have := hanc q.1 h
    rw [← e] at this
    simp only [Prod.mk.eta] at this
    rw [this, sub_self, mul_zero, zero_mul]
  · exact absurd (Prod.ext h (by rw [← hq, h, hx])) h1
  · exact absurd ⟨h, by rw [← hq, ← lev_eq_div h.le x, hx]⟩ h2

lemma Tf_le {n : ℕ} {σ τ : SA n} {p : ℕ × ℕ} (hp : p ∈ dset σ τ) {x : ℝ}
    (hx : lev p.1 x = p.2) {b : ℝ} (hb : 0 ≤ b) :
    b * Tf n p x ≤ sgn (sv σ p) * (fS b σ x - fS b τ x) := by
  have e : sgn (sv σ p) * (fS b σ x - fS b τ x) =
      b * ∑ q ∈ ivs n, sgn (sv σ p) * (sgn (sv σ q) - sgn (sv τ q)) * psi q x := by
    simp only [fS]
    rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [e]
  unfold Tf
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => sgn_mul_sub_psi_ge hp hx q) hb

lemma lev_of_Tf_ne_zero {n : ℕ} {p : ℕ × ℕ} {x : ℝ} (h : Tf n p x ≠ 0) : lev p.1 x = p.2 := by
  obtain ⟨q, _, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have htc : tc p q ≠ 0 := left_ne_zero_of_mul hq
  have hl := lev_of_psi_ne_zero (right_ne_zero_of_mul hq)
  unfold tc at htc
  by_cases h1 : q = p
  · rw [← h1]; exact hl
  rw [ite_eq_right h1] at htc
  by_cases h2 : sdesc p q
  · rw [lev_eq_div h2.1.le x, hl]; exact h2.2
  · rw [ite_eq_right h2] at htc; exact absurd rfl htc

lemma dset_unique {n : ℕ} {σ τ : SA n} {p p' : ℕ × ℕ} (hp : p ∈ dset σ τ)
    (hp' : p' ∈ dset σ τ) {x : ℝ} (hx : lev p.1 x = p.2) (hx' : lev p'.1 x = p'.2) : p = p' := by
  wlog hle : p.1 ≤ p'.1 generalizing p p'
  · exact (this hp' hp hx' hx (not_le.mp hle).le).symm
  obtain ⟨_, hne, _⟩ := Finset.mem_filter.mp hp
  obtain ⟨_, _, hanc'⟩ := Finset.mem_filter.mp hp'
  have e : p.2 = p'.2 / 16 ^ (p'.1 - p.1) := by rw [← hx, ← hx', lev_eq_div hle x]
  rcases lt_or_eq_of_le hle with h | h
  · exfalso
    apply hne
    have := hanc' p.1 h
    rw [← e] at this
    simpa only [Prod.mk.eta] using this
  · exact Prod.ext h (by rw [e, h, Nat.sub_self, pow_zero, Nat.div_one])

/-- Pointwise: `b Σ_{p ∈ D} T_p ≤ |f_σ - f_τ|`. -/
lemma sum_Tf_le {n : ℕ} (σ τ : SA n) {b : ℝ} (hb : 0 ≤ b) (x : ℝ) :
    b * ∑ p ∈ dset σ τ, Tf n p x ≤ |fS b σ x - fS b τ x| := by
  by_cases h : ∃ p ∈ dset σ τ, Tf n p x ≠ 0
  · obtain ⟨p, hp, hT⟩ := h
    have hx := lev_of_Tf_ne_zero hT
    rw [Finset.sum_eq_single_of_mem p hp]
    · calc b * Tf n p x ≤ sgn (sv σ p) * (fS b σ x - fS b τ x) := Tf_le hp hx hb
        _ ≤ |sgn (sv σ p) * (fS b σ x - fS b τ x)| := le_abs_self _
        _ = |fS b σ x - fS b τ x| := by rw [abs_mul, abs_sgn, one_mul]
    · intro p' hp' hne
      by_contra hT'
      exact hne (dset_unique hp' hp (lev_of_Tf_ne_zero hT') hx)
  · push Not at h
    rw [Finset.sum_eq_zero h, mul_zero]
    exact abs_nonneg _

/-! ## Integrals of the tents -/

lemma integral_tent : ∫ t in (0 : ℝ)..1, tent t = 1 / 4 := by
  have h1 : ∫ t in (0 : ℝ)..(1 / 2), tent t = ∫ t in (0 : ℝ)..(1 / 2), t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    exact tent_of_le_half ht.1 ht.2
  have h2 : ∫ t in (1 / 2 : ℝ)..1, tent t = ∫ t in (1 / 2 : ℝ)..1, (1 - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    exact tent_of_half_le ht.1 ht.2
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2)
    (continuous_tent.intervalIntegrable _ _) (continuous_tent.intervalIntegrable _ _), h1, h2,
    intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (continuous_id'.intervalIntegrable _ _)]
  simp only [integral_id, intervalIntegral.integral_const, smul_eq_mul]
  norm_num

lemma integral_tent_of_le {a c : ℝ} (ha : a ≤ 0) (hc : 1 ≤ c) : ∫ t in a..c, tent t = 1 / 4 := by
  have hi : ∀ u v : ℝ, IntervalIntegrable tent volume u v :=
    fun u v => continuous_tent.intervalIntegrable u v
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi a 0) (hi 0 c),
    ← intervalIntegral.integral_add_adjacent_intervals (hi 0 1) (hi 1 c), integral_tent]
  have e1 : ∫ t in a..0, tent t = ∫ t in a..0, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht; rw [uIcc_of_le ha] at ht; exact tent_of_nonpos ht.2
  have e2 : ∫ t in (1 : ℝ)..c, tent t = ∫ t in (1 : ℝ)..c, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht; rw [uIcc_of_le hc] at ht; exact tent_of_one_le ht.1
  rw [e1, e2, intervalIntegral.integral_zero, intervalIntegral.integral_zero]
  ring

lemma integral_psi {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ ivs n) :
    ∫ x in (0 : ℝ)..1, psi p x = sc p.1 ^ 2 / 4 := by
  unfold psi
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_sub tent (by positivity : (16 : ℝ) ^ p.1 ≠ 0) (p.2 : ℝ)]
  have h1 := cast_succ_le_pow hp
  have h2 : (0 : ℝ) ≤ p.2 := Nat.cast_nonneg _
  rw [integral_tent_of_le (by linarith) (by linarith)]
  simp only [smul_eq_mul, sc]
  ring

lemma integral_Tf {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ ivs n) :
    ∫ x in (0 : ℝ)..1, Tf n p x =
      sc p.1 ^ 2 / 2 - (∑ q ∈ (ivs n).filter (sdesc p), sc q.1 ^ 2) / 2 := by
  unfold Tf
  rw [intervalIntegral.integral_finsetSum (f := fun q x => tc p q * psi q x)
    (fun q _ => (continuous_const.mul (continuous_psi q)).intervalIntegrable 0 1)]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [Finset.sum_congr rfl (g := fun q => tc p q * (sc q.1 ^ 2 / 4))
    fun q hq => by rw [integral_psi hq], sum_tc hp (fun q => sc q.1 ^ 2 / 4), ← Finset.sum_div]
  ring

/-- `∫₀¹ |f_σ - f_τ| ≥ b Σ_{p ∈ D} (|p|² - Σ_{q below p} |q|²) / 2`. -/
lemma integral_abs_fS_sub_ge {n : ℕ} (σ τ : SA n) {b : ℝ} (hb : 0 ≤ b) :
    b * ∑ p ∈ dset σ τ, (sc p.1 ^ 2 / 2 - (∑ q ∈ (ivs n).filter (sdesc p), sc q.1 ^ 2) / 2) ≤
      ∫ x in (0 : ℝ)..1, |fS b σ x - fS b τ x| := by
  have hint : ∫ x in (0 : ℝ)..1, b * ∑ p ∈ dset σ τ, Tf n p x =
      b * ∑ p ∈ dset σ τ,
        (sc p.1 ^ 2 / 2 - (∑ q ∈ (ivs n).filter (sdesc p), sc q.1 ^ 2) / 2) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
      (fun p _ => (continuous_Tf n p).intervalIntegrable 0 1)]
    congr 1
    exact Finset.sum_congr rfl fun p hp => integral_Tf (Finset.mem_filter.mp hp).1
  rw [← hint]
  apply intervalIntegral.integral_mono_on zero_le_one
  · exact (continuous_const.mul
      (continuous_finsetSum _ fun p _ => continuous_Tf n p)).intervalIntegrable 0 1
  · exact ((continuous_fS b σ).sub (continuous_fS b τ)).abs.intervalIntegrable 0 1
  · intro x _; exact sum_Tf_le σ τ hb x

/-! ## Counting descendants -/

lemma card_sdesc_le (p : ℕ × ℕ) (j N : ℕ) :
    ((Finset.range N).filter fun k => sdesc p (j, k)).card ≤ 16 ^ (j - p.1) := by
  have hm : 0 < 16 ^ (j - p.1) := by positivity
  calc _ ≤ (Finset.Ico (p.2 * 16 ^ (j - p.1)) ((p.2 + 1) * 16 ^ (j - p.1))).card := by
        apply Finset.card_le_card
        intro k hk
        rw [Finset.mem_filter] at hk
        have h2 : k / 16 ^ (j - p.1) = p.2 := hk.2.2
        simp only [Finset.mem_Ico]
        constructor
        · exact (Nat.le_div_iff_mul_le hm).mp h2.ge
        · exact (Nat.div_lt_iff_lt_mul hm).mp (by rw [h2]; exact Nat.lt_succ_self _)
    _ = 16 ^ (j - p.1) := by rw [Nat.card_Ico, add_mul, one_mul, Nat.add_sub_cancel_left]

lemma sum_sdesc_le {n : ℕ} (p : ℕ × ℕ) :
    ∑ q ∈ (ivs n).filter (sdesc p), sc q.1 ^ 2 ≤ sc p.1 ^ 2 / 15 := by
  rw [Finset.sum_filter, sum_ivs]
  have inner : ∀ j ∈ Finset.range n,
      (∑ k ∈ Finset.range (16 ^ j), if sdesc p (j, k) then sc (j, k).1 ^ 2 else 0) ≤
        if p.1 < j then sc p.1 * (1 / 16 : ℝ) ^ j else 0 := by
    intro j _
    split_ifs with hj
    · dsimp only
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hc : (((Finset.range (16 ^ j)).filter fun k => sdesc p (j, k)).card : ℝ) ≤
          (16 : ℝ) ^ (j - p.1) := by exact_mod_cast card_sdesc_le p j (16 ^ j)
      have hp16 : (16 : ℝ) ^ j = 16 ^ p.1 * 16 ^ (j - p.1) := by
        rw [← pow_add, Nat.add_sub_cancel' hj.le]
      have e : (16 : ℝ) ^ (j - p.1) * sc j ^ 2 = sc p.1 * (1 / 16 : ℝ) ^ j := by
        simp only [sc, one_div, inv_pow]
        rw [hp16]; field_simp
      rw [← e]
      exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    · apply le_of_eq
      apply Finset.sum_eq_zero
      intro k _
      exact ite_eq_right (fun h => hj h.1)
  refine (Finset.sum_le_sum inner).trans ?_
  rw [← Finset.sum_filter]
  have hfil : (Finset.range n).filter (fun j => p.1 < j) = Finset.Ico (p.1 + 1) n := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hfil, ← Finset.mul_sum]
  have hg := geom_sum_Ico_le_of_lt_one (x := (1 / 16 : ℝ)) (m := p.1 + 1) (n := n)
    (by norm_num) (by norm_num)
  calc sc p.1 * ∑ i ∈ Finset.Ico (p.1 + 1) n, (1 / 16 : ℝ) ^ i
      ≤ sc p.1 * ((1 / 16 : ℝ) ^ (p.1 + 1) / (1 - 1 / 16)) :=
        mul_le_mul_of_nonneg_left hg (sc_pos _).le
    _ = sc p.1 ^ 2 / 15 := by
        simp only [sc, one_div, inv_pow, pow_succ]
        field_simp
        ring

/-! ## Ancestral sign words and the comparison of canonical distances -/

lemma toNat_eq_iff (a b : Bool) : a.toNat = b.toNat ↔ a = b := by
  cases a <;> cases b <;> simp

/-- The word of signs of `σ` along the ancestry of `(j, k)` (including `(j, k)`), in binary. -/
def ancW {n : ℕ} (σ : SA n) : ℕ → ℕ → ℕ
  | 0, k => (sv σ (0, k)).toNat
  | j + 1, k => 2 * ancW σ j (k / 16) + (sv σ (j + 1, k)).toNat

lemma ancW_lt {n : ℕ} (σ : SA n) : ∀ j k, ancW σ j k < 2 ^ (j + 1)
  | 0, k => by
    have := Bool.toNat_le (sv σ (0, k))
    simp only [ancW, zero_add, pow_one]; omega
  | j + 1, k => by
    have ih := ancW_lt σ j (k / 16)
    have h2 := Bool.toNat_le (sv σ (j + 1, k))
    simp only [ancW, pow_succ 2 (j + 1)]
    generalize 2 ^ (j + 1) = N at *
    omega

lemma div16_div (k : ℕ) {i j : ℕ} (h : i ≤ j) : k / 16 / 16 ^ (j - i) = k / 16 ^ (j + 1 - i) := by
  rw [Nat.div_div_eq_div_mul, ← pow_succ', show j + 1 - i = j - i + 1 by omega]

lemma ancW_eq_iff {n : ℕ} (σ τ : SA n) : ∀ j k, ancW σ j k = ancW τ j k ↔
    ∀ i ≤ j, sv σ (i, k / 16 ^ (j - i)) = sv τ (i, k / 16 ^ (j - i))
  | 0, k => by
    simp only [ancW, toNat_eq_iff]
    constructor
    · intro h i hi
      obtain rfl := Nat.le_zero.mp hi
      simpa using h
    · intro h
      simpa using h 0 le_rfl
  | j + 1, k => by
    have ih := ancW_eq_iff σ τ j (k / 16)
    have hb1 := Bool.toNat_le (sv σ (j + 1, k))
    have hb2 := Bool.toNat_le (sv τ (j + 1, k))
    simp only [ancW]
    constructor
    · intro h
      have h1 : ancW σ j (k / 16) = ancW τ j (k / 16) := by omega
      have h2 : (sv σ (j + 1, k)).toNat = (sv τ (j + 1, k)).toNat := by omega
      intro i hi
      rcases Nat.lt_or_eq_of_le hi with hi | hi
      · have := ih.mp h1 i (by omega)
        rwa [div16_div k (by omega : i ≤ j)] at this
      · subst hi
        simpa using (toNat_eq_iff _ _).mp h2
    · intro h
      have h1 := ih.mpr (fun i hi => by
        have := h i (by omega)
        rwa [div16_div k hi])
      have h2 := h (j + 1) le_rfl
      simp only [Nat.sub_self, pow_zero, Nat.div_one] at h2
      rw [h1, h2]

lemma eq_of_ancW_eq {n : ℕ} {σ τ : SA n}
    (h : ∀ q ∈ ivs n, ancW σ q.1 q.2 = ancW τ q.1 q.2) : σ = τ := by
  funext q
  have := (ancW_eq_iff σ τ q.1.1 q.1.2).mp (h q.1 q.2) q.1.1 le_rfl
  simp only [Nat.sub_self, pow_zero, Nat.div_one, Prod.mk.eta] at this
  simpa [sv, q.2] using this

lemma exists_dset_of_ancW_ne {n : ℕ} {σ τ : SA n} {q : ℕ × ℕ} (hq : q ∈ ivs n)
    (h : ancW σ q.1 q.2 ≠ ancW τ q.1 q.2) : ∃ p ∈ dset σ τ, q = p ∨ sdesc p q := by
  have hP : ∃ i, i ≤ q.1 ∧ sv σ (i, q.2 / 16 ^ (q.1 - i)) ≠ sv τ (i, q.2 / 16 ^ (q.1 - i)) := by
    by_contra hc
    apply h
    rw [ancW_eq_iff]
    intro i hi
    by_contra hne
    exact hc ⟨i, hi, hne⟩
  have hi := Nat.find_spec hP
  have hmin := fun i' (h' : i' < Nat.find hP) => Nat.find_min hP h'
  obtain ⟨hq1, hq2⟩ := mem_ivs.mp hq
  refine ⟨(Nat.find hP, q.2 / 16 ^ (q.1 - Nat.find hP)), ?_, ?_⟩
  · rw [dset, Finset.mem_filter, mem_ivs]
    refine ⟨⟨by simp only; omega, ?_⟩, hi.2, ?_⟩
    · simp only
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_cancel' hi.1]
      exact hq2
    · intro i' hi'
      simp only at hi' ⊢
      have := hmin i' hi'
      rw [not_and, not_not] at this
      rw [div_pow_div, show q.1 - Nat.find hP + (Nat.find hP - i') = q.1 - i' by omega]
      exact this (by omega)
  · rcases Nat.lt_or_eq_of_le hi.1 with hlt | heq
    · exact Or.inr ⟨hlt, rfl⟩
    · refine Or.inl (Prod.ext heq.symm ?_)
      simp [heq]

lemma sum_ancW_ne_le {n : ℕ} (σ τ : SA n) :
    ∑ q ∈ ivs n, (if ancW σ q.1 q.2 = ancW τ q.1 q.2 then 0 else sc q.1 ^ 2) ≤
      ∑ p ∈ dset σ τ, (sc p.1 ^ 2 + ∑ q ∈ (ivs n).filter (sdesc p), sc q.1 ^ 2) := by
  have hnn : ∀ q p : ℕ × ℕ, 0 ≤ (if q = p ∨ sdesc p q then sc q.1 ^ 2 else 0) := by
    intro q p; split_ifs <;> positivity
  calc ∑ q ∈ ivs n, (if ancW σ q.1 q.2 = ancW τ q.1 q.2 then 0 else sc q.1 ^ 2)
      ≤ ∑ q ∈ ivs n, ∑ p ∈ dset σ τ, (if q = p ∨ sdesc p q then sc q.1 ^ 2 else 0) := by
        apply Finset.sum_le_sum
        intro q hq
        split_ifs with h
        · exact Finset.sum_nonneg fun p _ => hnn q p
        · obtain ⟨p, hp, hpq⟩ := exists_dset_of_ancW_ne hq h
          calc sc q.1 ^ 2 = (if q = p ∨ sdesc p q then sc q.1 ^ 2 else 0) :=
                (ite_eq_left hpq).symm
            _ ≤ _ := Finset.single_le_sum
                (f := fun p => if q = p ∨ sdesc p q then sc q.1 ^ 2 else 0)
                (fun p _ => hnn q p) hp
    _ = ∑ p ∈ dset σ τ, ∑ q ∈ ivs n, (if q = p ∨ sdesc p q then sc q.1 ^ 2 else 0) :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun p hp => ?_
        have hpI := (Finset.mem_filter.mp hp).1
        have h : ∀ q, (if q = p ∨ sdesc p q then sc q.1 ^ 2 else 0) =
            (if q = p then sc q.1 ^ 2 else 0) + (if sdesc p q then sc q.1 ^ 2 else 0) := by
          intro q
          by_cases h1 : q = p
          · subst h1; simp [not_sdesc_self]
          · simp [h1]
        rw [Finset.sum_congr rfl fun q _ => h q, Finset.sum_add_distrib, Finset.sum_ite_eq',
          ite_eq_left hpI, ← Finset.sum_filter]

/-- The squared canonical distance of the tree family is dominated by that of `Z`:
`(π b / 4) Σ_{q below D} |q|² ≤ 2π ∫₀¹ |f_σ - f_τ|`. -/
lemma tree_dist_le {n : ℕ} (σ τ : SA n) {b : ℝ} (hb : 0 ≤ b) :
    π * b / 4 * ∑ q ∈ ivs n, (if ancW σ q.1 q.2 = ancW τ q.1 q.2 then 0 else sc q.1 ^ 2) ≤
      2 * π * ∫ x in (0 : ℝ)..1, |fS b σ x - fS b τ x| := by
  have h1 := sum_ancW_ne_le σ τ
  have h2 := integral_abs_fS_sub_ge σ τ hb
  set X := ∑ p ∈ dset σ τ, sc p.1 ^ 2 with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun p _ => sq_nonneg _
  have hA : ∑ p ∈ dset σ τ, (sc p.1 ^ 2 + ∑ q ∈ (ivs n).filter (sdesc p), sc q.1 ^ 2) ≤
      16 / 15 * X := by
    rw [hX, Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ => by linarith [sum_sdesc_le (n := n) p]
  have hB : 7 / 15 * X ≤ ∑ p ∈ dset σ τ,
      (sc p.1 ^ 2 / 2 - (∑ q ∈ (ivs n).filter (sdesc p), sc q.1 ^ 2) / 2) := by
    rw [hX, Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ => by linarith [sum_sdesc_le (n := n) p]
  have hπ := Real.pi_pos
  have hbX : 0 ≤ π * b * X := by positivity
  calc π * b / 4 * ∑ q ∈ ivs n, (if ancW σ q.1 q.2 = ancW τ q.1 q.2 then 0 else sc q.1 ^ 2)
      ≤ π * b / 4 * (16 / 15 * X) := mul_le_mul_of_nonneg_left (h1.trans hA) (by positivity)
    _ ≤ 2 * π * (b * (7 / 15 * X)) := by
        have e1 : π * b / 4 * (16 / 15 * X) = 4 / 15 * (π * b * X) := by ring
        have e2 : 2 * π * (b * (7 / 15 * X)) = 14 / 15 * (π * b * X) := by ring
        rw [e1, e2]; linarith
    _ ≤ 2 * π * (b * ∑ p ∈ dset σ τ,
          (sc p.1 ^ 2 / 2 - (∑ q ∈ (ivs n).filter (sdesc p), sc q.1 ^ 2) / 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hb) (by positivity)
    _ ≤ 2 * π * ∫ x in (0 : ℝ)..1, |fS b σ x - fS b τ x| :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

end LQGDimension.LowerBound22
