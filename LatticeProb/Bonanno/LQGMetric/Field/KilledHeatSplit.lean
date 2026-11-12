/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatSplit at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatDens

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
(task P2-KILLED, decision D-KHK1)

Let `β` be a planar Brownian bridge of length `T = t + s`. Then
* `γ¹ = bridgeOf t β` (`γ¹_a = β_a − (a/t)β_t`) is a planar bridge of length `t`;
* `γ² = bridgeTail (t + s) s β` (`γ²_r = β_{t+r} − ((s−r)/s)β_t`) is a planar bridge of length `s`;
* `β_t`, `γ¹`, `γ²` are independent, and `β_t` has independent `N(0, ts/T)` coordinates.

This is the Markov property of the Brownian bridge (e.g. Revuz–Yor, *Continuous Martingales and
Brownian Motion*, Ch. I §3, Exercise 3.16; the Gaussian computation is elementary). It gives the
pointwise Chapman–Kolmogorov equation for the bridge formula (`KilledHeatCK.lean`), which DZZ use
at l. 437–441 (eq-cov-tildeh).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LQGMetric
namespace KilledHeat

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

lemma bridgeCov_same (T : ℝ≥0) (b : Bool) (x y : ℝ≥0) :
    bridgeCov T (b, x) (b, y) = ((min x y : ℝ≥0) : ℝ) - x * y / T := by
  simp [bridgeCov]

lemma bridgeCov_diff (T : ℝ≥0) {b b' : Bool} (hb : b ≠ b') (x y : ℝ≥0) :
    bridgeCov T (b, x) (b', y) = 0 := by
  simp [bridgeCov, hb]

/-- Linear combinations of two coordinates of a Gaussian planar process are jointly Gaussian. -/
lemma isGaussianProcess_comb {X : ℝ≥0 → Ω → ℂ} {P : Measure Ω}
    (hX : IsGaussianProcess (coordProc X) P) {I : Type*}
    (F : I → (Bool × ℝ≥0) × (Bool × ℝ≥0) × ℝ) (Y : I → Ω → ℝ)
    (hY : ∀ i ω, Y i ω = coordProc X (F i).1 ω - (F i).2.2 * coordProc X (F i).2.1 ω) :
    IsGaussianProcess Y P := by
  classical
  refine hX.of_isGaussianProcess fun i ↦ ?_
  refine ⟨{(F i).1, (F i).2.1}, (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : ({(F i).1, (F i).2.1} : Finset (Bool × ℝ≥0)) ↦ ℝ) ⟨(F i).1, by simp⟩) -
    (F i).2.2 • (ContinuousLinearMap.proj ⟨(F i).2.1, by simp⟩), fun ω ↦ ?_⟩
  rw [hY]
  simp

section Cov

variable {T : ℝ≥0} {β : ℝ≥0 → Ω → ℂ} {P : Measure Ω}

lemma cov_comb (hβ : IsPlanarBridge T β P) {p1 p2 q1 q2 : Bool × ℝ≥0} (hp1 : p1.2 ≤ T)
    (hp2 : p2.2 ≤ T) (hq1 : q1.2 ≤ T) (hq2 : q2.2 ≤ T) (c d : ℝ) :
    cov[fun ω ↦ coordProc β p1 ω - c * coordProc β p2 ω,
      fun ω ↦ coordProc β q1 ω - d * coordProc β q2 ω; P] =
      bridgeCov T p1 q1 - d * bridgeCov T p1 q2 - c * bridgeCov T p2 q1 +
        c * d * bridgeCov T p2 q2 := by
  have := hβ.gauss.isProbabilityMeasure
  have hL2 : ∀ p, MemLp (coordProc β p) 2 P := fun p ↦ (hβ.gauss.hasGaussianLaw_eval p).memLp_two
  have hb : MemLp (fun ω ↦ coordProc β q1 ω - d * coordProc β q2 ω) 2 P :=
    (hL2 q1).sub ((hL2 _).const_mul _)
  rw [covariance_fun_sub_left (hL2 p1) ((hL2 _).const_mul _) hb,
    covariance_fun_sub_right (hL2 p1) (hL2 q1) ((hL2 _).const_mul _),
    covariance_fun_sub_right ((hL2 _).const_mul _) (hL2 q1) ((hL2 _).const_mul _),
    covariance_const_mul_right, covariance_const_mul_left, covariance_const_mul_left,
    covariance_const_mul_right, hβ.cov _ _ hp1 hq1, hβ.cov _ _ hp1 hq2, hβ.cov _ _ hp2 hq1,
    hβ.cov _ _ hp2 hq2]
  ring

/-- Restricting a bridge of length `T` to `[0, t]` and re-bridging gives a bridge of length `t`. -/
theorem IsPlanarBridge.bridgeOf (hβ : IsPlanarBridge T β P) {t : ℝ≥0} (htT : t ≤ T)
    (ht : t ≠ 0) : IsPlanarBridge t (KilledHeat.bridgeOf t β) P := by
  have := hβ.gauss.isProbabilityMeasure
  have hL2 : ∀ p, MemLp (coordProc β p) 2 P := fun p ↦ (hβ.gauss.hasGaussianLaw_eval p).memLp_two
  refine ⟨?_, ?_, fun p ↦ ?_, fun p q hp hq ↦ ?_⟩
  · filter_upwards [hβ.cont] with ω hω
    unfold KilledHeat.bridgeOf
    fun_prop
  · exact isGaussianProcess_comb hβ.gauss (fun p ↦ (p, (p.1, t), (p.2 : ℝ) / t)) _
      fun p ω ↦ by rw [coordProc_bridgeOf]
  · rw [coordProc_bridgeOf, integral_sub ((hL2 p).integrable (by norm_num))
      (((hL2 _).integrable (by norm_num)).const_mul _), integral_const_mul, hβ.mean, hβ.mean]
    simp
  · rw [coordProc_bridgeOf, coordProc_bridgeOf, cov_comb hβ (hp.trans htT) htT (hq.trans htT) htT]
    rcases p with ⟨b, a⟩
    rcases q with ⟨b', a'⟩
    simp only at hp hq ⊢
    by_cases hb : b = b'
    · subst hb
      rw [bridgeCov_same, bridgeCov_same, bridgeCov_same, bridgeCov_same, bridgeCov_same,
        min_eq_left hp, min_eq_right hq, min_self]
      have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
      have hT' : (T : ℝ) ≠ 0 := by
        have : (0 : ℝ) < t := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm ht')
        exact ne_of_gt (lt_of_lt_of_le this (by exact_mod_cast htT))
      field_simp
      ring
    · rw [bridgeCov_diff T hb, bridgeCov_diff T hb, bridgeCov_diff T hb, bridgeCov_diff T hb,
        bridgeCov_diff t hb]
      ring

end Cov

/-- The tail bridge `γ²_r = β_{T−(s−r)} − ((s−r)/s) β_{T−s}` (`= β_{t+r} − ((s−r)/s)β_t` when
`T = t + s`, `r ≤ s`). -/
def bridgeTail (T s : ℝ≥0) (β : ℝ≥0 → Ω → ℂ) : ℝ≥0 → Ω → ℂ :=
  reverse s (KilledHeat.bridgeOf s (reverse T β))

lemma bridgeTail_apply (T s : ℝ≥0) (β : ℝ≥0 → Ω → ℂ) (r : ℝ≥0) (ω : Ω) :
    bridgeTail T s β r ω = β (T - (s - r)) ω - ((((s - r : ℝ≥0) : ℝ) / s : ℝ) : ℂ) * β (T - s) ω := by
  rfl

lemma coordProc_bridgeTail (T s : ℝ≥0) (β : ℝ≥0 → Ω → ℂ) (p : Bool × ℝ≥0) :
    coordProc (bridgeTail T s β) p = fun ω ↦ coordProc β (p.1, T - (s - p.2)) ω -
      (((s - p.2 : ℝ≥0) : ℝ) / s) * coordProc β (p.1, T - s) ω := by
  ext ω
  rcases p with ⟨b, r⟩
  cases b <;> simp [coordProc, bridgeTail_apply]

theorem IsPlanarBridge.bridgeTail {T s : ℝ≥0} {β : ℝ≥0 → Ω → ℂ} {P : Measure Ω}
    (hβ : IsPlanarBridge T β P) (hsT : s ≤ T) (hs : s ≠ 0) :
    IsPlanarBridge s (KilledHeat.bridgeTail T s β) P :=
  (hβ.reverse.bridgeOf hsT hs).reverse

lemma add_tsub_tsub_eq (t s r : ℝ≥0) (hr : r ≤ s) : t + s - (s - r) = t + r := by
  apply NNReal.eq
  rw [NNReal.coe_sub (tsub_le_self.trans le_add_self), NNReal.coe_sub hr]
  push_cast
  ring

section Indep

variable {t s : ℝ≥0} {β : ℝ≥0 → Ω → ℂ} {P : Measure Ω}

lemma coordProc_eq_sub_zero (β : ℝ≥0 → Ω → ℂ) (p : Bool × ℝ≥0) :
    coordProc β p = fun ω ↦ coordProc β p ω - 0 * coordProc β p ω := by
  funext ω
  ring

lemma cov_mid_head (hβ : IsPlanarBridge (t + s) β P) (ht : t ≠ 0) (b b' : Bool) {a : ℝ≥0}
    (ha : a ≤ t) :
    cov[coordProc β (b, t), coordProc (bridgeOf t β) (b', a); P] = 0 := by
  have htT : t ≤ t + s := le_self_add
  rw [coordProc_eq_sub_zero β (b, t), coordProc_bridgeOf,
    cov_comb hβ htT htT (ha.trans htT) htT]
  by_cases hb : b = b'
  · subst hb
    simp only [bridgeCov_same, min_eq_right ha, min_self]
    have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    field_simp
    ring
  · simp [bridgeCov_diff _ hb]

lemma cov_mid_tail (hβ : IsPlanarBridge (t + s) β P) (hs : s ≠ 0) (b b' : Bool) {r : ℝ≥0}
    (hr : r ≤ s) :
    cov[coordProc β (b, t), coordProc (bridgeTail (t + s) s β) (b', r); P] = 0 := by
  have htT : t ≤ t + s := le_self_add
  have h1 : t + s - (s - r) = t + r := add_tsub_tsub_eq t s r hr
  have h2 : t + s - s = t := add_tsub_cancel_right t s
  have hrT : t + r ≤ t + s := add_le_add_right hr t
  rw [coordProc_eq_sub_zero β (b, t), coordProc_bridgeTail]
  simp only [h1, h2]
  rw [cov_comb hβ htT htT hrT htT]
  by_cases hb : b = b'
  · subst hb
    simp only [bridgeCov_same, min_eq_left (le_self_add : t ≤ t + r), min_self,
      NNReal.coe_sub hr, NNReal.coe_add]
    have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs
    have hT : (t : ℝ) + s ≠ 0 := by positivity
    field_simp
    ring
  · simp [bridgeCov_diff _ hb]

lemma cov_head_tail (hβ : IsPlanarBridge (t + s) β P) (ht : t ≠ 0) (hs : s ≠ 0) (b b' : Bool)
    {a r : ℝ≥0} (ha : a ≤ t) (hr : r ≤ s) :
    cov[coordProc (bridgeOf t β) (b, a), coordProc (bridgeTail (t + s) s β) (b', r); P] = 0 := by
  have htT : t ≤ t + s := le_self_add
  have h1 : t + s - (s - r) = t + r := add_tsub_tsub_eq t s r hr
  have h2 : t + s - s = t := add_tsub_cancel_right t s
  have hrT : t + r ≤ t + s := add_le_add_right hr t
  rw [coordProc_bridgeOf, coordProc_bridgeTail]
  simp only [h1, h2]
  rw [cov_comb hβ (ha.trans htT) htT hrT htT]
  by_cases hb : b = b'
  · subst hb
    simp only [bridgeCov_same, min_eq_left (ha.trans (le_self_add : t ≤ t + r)), min_eq_left ha,
      min_eq_left (le_self_add : t ≤ t + r), min_self, NNReal.coe_sub hr, NNReal.coe_add]
    have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs
    have hT : (t : ℝ) + s ≠ 0 := by positivity
    field_simp
    ring
  · simp [bridgeCov_diff _ hb]

end Indep

end KilledHeat
end LQGMetric
