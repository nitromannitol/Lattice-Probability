/-
The exponential Efron-Stein inequality for a product measure, by coordinate
telescoping.

A function that moves by at most `ℓ_i |ξ_i - y|` when its `i`-th coordinate is
replaced moves by at most `∑_i ℓ_i |ξ_i - η_i|` when all of them are: replace the
coordinates one at a time and add the increments.  That global bound is what
makes every exponential of such a function integrable against a product measure
whose one-site law has an exponential moment.
-/
import Mathlib
import LatticeProb.Prob.SubGaussian

open MeasureTheory

namespace LatticeProb

variable {N : ℕ}

/-- The configuration agreeing with `η` on the coordinates below `k` and with
`ξ` from `k` on. -/
def hybrid (ξ η : Fin N → ℝ) (k : ℕ) : Fin N → ℝ :=
  fun i => if (i : ℕ) < k then η i else ξ i

theorem hybrid_zero (ξ η : Fin N → ℝ) : hybrid ξ η 0 = ξ := by
  funext i; simp [hybrid]

theorem hybrid_full (ξ η : Fin N → ℝ) : hybrid ξ η N = η := by
  funext i; simp [hybrid, i.isLt]

theorem hybrid_apply_self (ξ η : Fin N → ℝ) (k : ℕ) (hk : k < N) :
    hybrid ξ η k ⟨k, hk⟩ = ξ ⟨k, hk⟩ := by
  simp [hybrid]

theorem hybrid_succ (ξ η : Fin N → ℝ) (k : ℕ) (hk : k < N) :
    hybrid ξ η (k + 1) = Function.update (hybrid ξ η k) ⟨k, hk⟩ (η ⟨k, hk⟩) := by
  funext i
  by_cases h : i = (⟨k, hk⟩ : Fin N)
  · subst h
    simp [hybrid, Function.update_self]
  · rw [Function.update_of_ne h]
    have hne : (i : ℕ) ≠ k := fun hc => h (Fin.ext hc)
    unfold hybrid
    by_cases h2 : (i : ℕ) < k
    · rw [if_pos (by omega), if_pos h2]
    · rw [if_neg (by omega), if_neg h2]

/-- The coordinate Lipschitz bounds add up. -/
theorem abs_sub_le_sum_lip (F : (Fin N → ℝ) → ℝ) (ℓ : Fin N → ℝ)
    (hLip : ∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
      |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|)
    (ξ η : Fin N → ℝ) : |F ξ - F η| ≤ ∑ i, ℓ i * |ξ i - η i| := by
  classical
  set g : ℕ → ℝ := fun j => if h : j < N then ℓ ⟨j, h⟩ * |ξ ⟨j, h⟩ - η ⟨j, h⟩| else 0 with hg
  have key : ∀ k, k ≤ N →
      |F ξ - F (hybrid ξ η k)| ≤ ∑ j ∈ Finset.range k, g j := by
    intro k
    induction k with
    | zero => intro _; simp [hybrid_zero]
    | succ m ih =>
        intro hm
        have hmN : m < N := by omega
        have hstep : |F (hybrid ξ η m) - F (hybrid ξ η (m + 1))|
            ≤ g m := by
          rw [hybrid_succ ξ η m hmN]
          refine le_trans (hLip (hybrid ξ η m) ⟨m, hmN⟩ (η ⟨m, hmN⟩)) ?_
          rw [hybrid_apply_self ξ η m hmN, hg]
          simp only [dif_pos hmN]
          exact le_rfl
        have htri : |F ξ - F (hybrid ξ η (m + 1))|
            ≤ |F ξ - F (hybrid ξ η m)| + |F (hybrid ξ η m) - F (hybrid ξ η (m + 1))| := by
          have := abs_sub_le (F ξ) (F (hybrid ξ η m)) (F (hybrid ξ η (m + 1)))
          linarith
        rw [Finset.sum_range_succ]
        have := ih (by omega)
        linarith
  have hfin := key N le_rfl
  rw [hybrid_full] at hfin
  refine le_trans hfin (le_of_eq ?_)
  rw [← Fin.sum_univ_eq_sum_range g N]
  exact Finset.sum_congr rfl fun i _ => by simp [hg]


/-! ### Sub-Gaussian on a range, with the range set by a gap -/

/-- A centred variable with an exponential moment of order `θ` is sub-Gaussian on
the range `θ - δ`, with a constant deteriorating as `δ` shrinks. -/
theorem subGaussianOn_of_exp_moment_gap {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (W : Ω → ℝ) (hWm : Measurable W) (θ K δ : ℝ)
    (hδ : 0 < δ) (hδθ : δ ≤ θ)
    (hexp : Integrable (fun ω => Real.exp (θ * |W ω|)) μ)
    (hK : ∫ ω, Real.exp (θ * |W ω|) ∂μ ≤ K)
    (hint : Integrable W μ) (hmean : ∫ ω, W ω ∂μ = 0) :
    SubGaussianOn W (4 * K / δ ^ 2) (θ - δ) μ := by
  have hθ : 0 < θ := lt_of_lt_of_le hδ hδθ
  intro s hs
  have hsθ : |s| ≤ θ := le_trans hs (by linarith)
  have hdom : ∀ ω, Real.exp (s * W ω) ≤ Real.exp (θ * |W ω|) := by
    intro ω
    refine Real.exp_le_exp.mpr ?_
    calc s * W ω ≤ |s * W ω| := le_abs_self _
      _ = |s| * |W ω| := abs_mul s (W ω)
      _ ≤ θ * |W ω| := mul_le_mul_of_nonneg_right hsθ (abs_nonneg _)
  have hintL : Integrable (fun ω => Real.exp (s * W ω)) μ := by
    refine hexp.mono' ((Real.measurable_exp.comp (hWm.const_mul s))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hdom ω
  refine ⟨hintL, ?_⟩
  have hpt : ∀ ω, Real.exp (s * W ω)
      ≤ 1 + s * W ω + s ^ 2 * (4 / δ ^ 2) * Real.exp (θ * |W ω|) := by
    intro ω
    have hbase := exp_le_one_add_add_sq (s * W ω)
    have hsq : W ω ^ 2 ≤ 4 / δ ^ 2 * Real.exp (δ * |W ω|) := by
      have := sq_le_exp_mul δ hδ |W ω| (abs_nonneg _)
      rwa [sq_abs] at this
    have habs : |s * W ω| ≤ (θ - δ) * |W ω| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)
    have hexpmono : Real.exp |s * W ω| ≤ Real.exp ((θ - δ) * |W ω|) :=
      Real.exp_le_exp.mpr habs
    have hjoin : Real.exp (δ * |W ω|) * Real.exp ((θ - δ) * |W ω|)
        = Real.exp (θ * |W ω|) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hprod : W ω ^ 2 * Real.exp |s * W ω|
        ≤ 4 / δ ^ 2 * (Real.exp (δ * |W ω|) * Real.exp ((θ - δ) * |W ω|)) := by
      calc W ω ^ 2 * Real.exp |s * W ω|
          ≤ (4 / δ ^ 2 * Real.exp (δ * |W ω|)) * Real.exp ((θ - δ) * |W ω|) :=
            mul_le_mul hsq hexpmono (Real.exp_pos _).le (by positivity)
        _ = 4 / δ ^ 2 * (Real.exp (δ * |W ω|) * Real.exp ((θ - δ) * |W ω|)) := by ring
    rw [hjoin] at hprod
    have hs2 : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
    have hfin := mul_le_mul_of_nonneg_left hprod hs2
    calc Real.exp (s * W ω) ≤ 1 + s * W ω + (s * W ω) ^ 2 * Real.exp |s * W ω| := hbase
      _ ≤ 1 + s * W ω + s ^ 2 * (4 / δ ^ 2) * Real.exp (θ * |W ω|) := by
          have h1 : (s * W ω) ^ 2 * Real.exp |s * W ω|
              = s ^ 2 * (W ω ^ 2 * Real.exp |s * W ω|) := by ring
          rw [h1]
          nlinarith [hfin]
  have hA : Integrable (fun ω => 1 + s * W ω) μ := (integrable_const 1).add (hint.const_mul s)
  have hB : Integrable (fun ω => s ^ 2 * (4 / δ ^ 2) * Real.exp (θ * |W ω|)) μ :=
    hexp.const_mul _
  have hRHS : ∫ ω, (1 + s * W ω + s ^ 2 * (4 / δ ^ 2) * Real.exp (θ * |W ω|)) ∂μ
      = 1 + s ^ 2 * (4 / δ ^ 2) * ∫ ω, Real.exp (θ * |W ω|) ∂μ := by
    rw [integral_add hA hB, integral_add (integrable_const 1) (hint.const_mul s),
      integral_const_mul, hmean, integral_const, integral_const_mul]
    simp
  have hle : ∫ ω, Real.exp (s * W ω) ∂μ
      ≤ ∫ ω, (1 + s * W ω + s ^ 2 * (4 / δ ^ 2) * Real.exp (θ * |W ω|)) ∂μ :=
    integral_mono hintL (hA.add hB) hpt
  rw [hRHS] at hle
  have hc : (0 : ℝ) ≤ s ^ 2 * (4 / δ ^ 2) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hK hc
  have heq : s ^ 2 * (4 / δ ^ 2) * K = 4 * K / δ ^ 2 * s ^ 2 := by ring
  have hkey : ∫ ω, Real.exp (s * W ω) ∂μ ≤ 1 + 4 * K / δ ^ 2 * s ^ 2 := by
    rw [← heq]
    linarith [hle, hmul]
  refine le_trans hkey ?_
  have := Real.add_one_le_exp (4 * K / δ ^ 2 * s ^ 2)
  linarith


/-! ### The one-variable step: a centred Lipschitz function of one coordinate -/

theorem le_exp_self (x : ℝ) : x ≤ Real.exp x := by
  have := Real.add_one_le_exp x
  linarith

theorem one_le_integral_exp_abs (ν : Measure ℝ) [IsProbabilityMeasure ν] (θ₀ : ℝ)
    (hθ₀ : 0 ≤ θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    1 ≤ ∫ z, Real.exp (θ₀ * |z|) ∂ν := by
  have h := integral_mono (integrable_const (1 : ℝ)) hexp
    (fun z => Real.one_le_exp (mul_nonneg hθ₀ (abs_nonneg z)))
  simpa using h

/-- The first absolute moment is controlled by the exponential moment. -/
theorem integral_abs_le (ν : Measure ℝ) [IsProbabilityMeasure ν] (θ₀ K : ℝ)
    (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hK : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K)
    (habs : Integrable (fun z => |z|) ν) : θ₀ * ∫ z, |z| ∂ν ≤ K := by
  have h1 : ∫ z, θ₀ * |z| ∂ν ≤ ∫ z, Real.exp (θ₀ * |z|) ∂ν :=
    integral_mono (habs.const_mul θ₀) hexp fun z => le_exp_self _
  rw [integral_const_mul] at h1
  linarith

/-- A Lipschitz function of one coordinate, centred, is sub-Gaussian on the range
the gap allows, with a constant depending only on the exponential moment and the
gap. -/
theorem subGaussianOn_centred_lip (ν : Measure ℝ) [IsProbabilityMeasure ν] (θ₀ K : ℝ)
    (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hK : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K)
    (G : ℝ → ℝ) (hGm : Measurable G) (L : ℝ) (hL : 0 < L)
    (hGlip : ∀ y z, |G y - G z| ≤ L * |y - z|) (δ : ℝ) (hδ : 0 < δ) (hδθ : δ ≤ θ₀) :
    SubGaussianOn (fun y => G y - ∫ z, G z ∂ν)
      (4 * (Real.exp K * K) / δ ^ 2 * L ^ 2) ((θ₀ - δ) / L) ν := by
  have hK1 : 1 ≤ K := le_trans (one_le_integral_exp_abs ν θ₀ hθ₀.le hexp) hK
  have hid : Integrable id ν := integrable_id_of_exp_moment ν θ₀ hθ₀ hexp
  have habs : Integrable (fun z => |z|) ν := hid.abs
  set m : ℝ := ∫ z, |z| ∂ν with hmdef
  have hm0 : 0 ≤ m := integral_nonneg fun z => abs_nonneg z
  have hθm : θ₀ * m ≤ K := integral_abs_le ν θ₀ K hexp hK habs
  have hGint : Integrable G ν := by
    refine Integrable.mono' ((habs.const_mul L).add (integrable_const |G 0|))
      hGm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    have h := hGlip y 0
    rw [sub_zero] at h
    have hsplit : |G y| ≤ |G y - G 0| + |G 0| := by
      have h2 := abs_add_le (G y - G 0) (G 0)
      simpa using h2
    linarith
  set W : ℝ → ℝ := fun y => G y - ∫ z, G z ∂ν with hWdef
  have hWm : Measurable W := hGm.sub_const _
  have hintW : Integrable W ν := hGint.sub (integrable_const _)
  have hmeanW : ∫ y, W y ∂ν = 0 := by
    rw [hWdef]
    rw [integral_sub hGint (integrable_const _), integral_const]
    simp
  have hWbound : ∀ y, |W y| ≤ L * (|y| + m) := by
    intro y
    have hrep : W y = ∫ z, (G y - G z) ∂ν := by
      rw [integral_sub (integrable_const _) hGint, integral_const]
      simp [hWdef]
    have hint1 : Integrable (fun z => G y - G z) ν := (integrable_const _).sub hGint
    have hint2 : Integrable (fun z => L * (|y| + |z|)) ν :=
      ((integrable_const |y|).add habs).const_mul L
    calc |W y| = |∫ z, (G y - G z) ∂ν| := by rw [hrep]
      _ ≤ ∫ z, |G y - G z| ∂ν := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (μ := ν) (f := fun z => G y - G z)
      _ ≤ ∫ z, L * (|y| + |z|) ∂ν := by
          refine integral_mono hint1.abs hint2 fun z => ?_
          refine le_trans (hGlip y z) ?_
          exact mul_le_mul_of_nonneg_left (abs_sub y z) hL.le
      _ = L * (|y| + m) := by
          rw [integral_const_mul, integral_add (integrable_const _) habs, integral_const]
          simp [hmdef]
  have hexpdom : ∀ y, Real.exp (θ₀ / L * |W y|)
      ≤ Real.exp (θ₀ * m) * Real.exp (θ₀ * |y|) := by
    intro y
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 : θ₀ / L * |W y| ≤ θ₀ / L * (L * (|y| + m)) :=
      mul_le_mul_of_nonneg_left (hWbound y) (by positivity)
    have h2 : θ₀ / L * (L * (|y| + m)) = θ₀ * m + θ₀ * |y| := by
      field_simp
      ring
    linarith [h1, h2.le, h2.ge]
  have hexpW : Integrable (fun y => Real.exp (θ₀ / L * |W y|)) ν := by
    refine Integrable.mono' (hexp.const_mul (Real.exp (θ₀ * m)))
      ((Real.measurable_exp.comp (hWm.abs.const_mul _))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hexpdom y
  have hKW : ∫ y, Real.exp (θ₀ / L * |W y|) ∂ν ≤ Real.exp K * K := by
    have h1 : ∫ y, Real.exp (θ₀ / L * |W y|) ∂ν
        ≤ ∫ y, Real.exp (θ₀ * m) * Real.exp (θ₀ * |y|) ∂ν :=
      integral_mono hexpW (hexp.const_mul _) hexpdom
    rw [integral_const_mul] at h1
    have h2 : Real.exp (θ₀ * m) ≤ Real.exp K := Real.exp_le_exp.mpr hθm
    have h3 : (0 : ℝ) ≤ ∫ z, Real.exp (θ₀ * |z|) ∂ν :=
      integral_nonneg fun z => (Real.exp_pos _).le
    nlinarith [h1, h2, h3, hK, (Real.exp_pos (θ₀ * m)).le]
  have hcast1 : 4 * (Real.exp K * K) / (δ / L) ^ 2
      = 4 * (Real.exp K * K) / δ ^ 2 * L ^ 2 := by
    field_simp
  have hcast2 : θ₀ / L - δ / L = (θ₀ - δ) / L := by ring
  rw [← hcast1, ← hcast2]
  exact subGaussianOn_of_exp_moment_gap ν W hWm (θ₀ / L) (Real.exp K * K) (δ / L)
    (by positivity) (by gcongr) hexpW hKW hintW hmeanW


/-! ### Integrability of the exponential, and the head-tail split -/

theorem integrable_exp_lip (ν : Measure ℝ) [IsProbabilityMeasure ν] (θ₀ : ℝ)
    (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (F : (Fin N → ℝ) → ℝ) (hFm : Measurable F) (ℓ : Fin N → ℝ)
    (hLip : ∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
      |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|)
    (lam : ℝ) (hlam : ∀ i, |lam| * ℓ i ≤ θ₀) (c : ℝ) :
    Integrable (fun ξ => Real.exp (lam * (F ξ - c)))
      (Measure.pi fun _ : Fin N => ν) := by
  have hfac : ∀ i : Fin N, Integrable (fun z : ℝ => Real.exp (|lam| * ℓ i * |z|)) ν := by
    intro i
    refine hexp.mono' ((Real.measurable_exp.comp
      ((measurable_id.abs).const_mul _))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hlam i) (abs_nonneg z))
  have hprod : Integrable (fun ξ : Fin N → ℝ => ∏ i, Real.exp (|lam| * ℓ i * |ξ i|))
      (Measure.pi fun _ : Fin N => ν) := Integrable.fintype_prod hfac
  refine Integrable.mono' (hprod.const_mul (Real.exp (|lam| * (|F 0| + |c|))))
    ((Real.measurable_exp.comp ((hFm.sub_const c).const_mul lam))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hglob : |F ξ - F 0| ≤ ∑ i, ℓ i * |ξ i| := by
    refine le_trans (abs_sub_le_sum_lip F ℓ hLip ξ 0) (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => by simp
  have hbnd : lam * (F ξ - c) ≤ |lam| * (|F 0| + |c|) + ∑ i, |lam| * ℓ i * |ξ i| := by
    have h1 : lam * (F ξ - c) ≤ |lam| * |F ξ - c| := by
      calc lam * (F ξ - c) ≤ |lam * (F ξ - c)| := le_abs_self _
        _ = |lam| * |F ξ - c| := abs_mul _ _
    have h2 : |F ξ - c| ≤ |F ξ - F 0| + (|F 0| + |c|) := by
      have h3 := abs_add_le (F ξ - F 0) (F 0 - c)
      have h4 := abs_sub (F 0) c
      have h5 : F ξ - c = (F ξ - F 0) + (F 0 - c) := by ring
      rw [h5]
      have h6 : |F 0 - c| ≤ |F 0| + |c| := abs_sub _ _
      linarith
    have hmid : |F ξ - F 0| + (|F 0| + |c|) ≤ (∑ i, ℓ i * |ξ i|) + (|F 0| + |c|) := by
      linarith [hglob]
    have h7 : |lam| * |F ξ - c| ≤ |lam| * ((∑ i, ℓ i * |ξ i|) + (|F 0| + |c|)) :=
      mul_le_mul_of_nonneg_left (le_trans h2 hmid) (abs_nonneg lam)
    have h9 : |lam| * ((∑ i, ℓ i * |ξ i|) + (|F 0| + |c|))
        = |lam| * (|F 0| + |c|) + ∑ i, |lam| * ℓ i * |ξ i| := by
      rw [mul_add, Finset.mul_sum]
      have hs : ∑ i, |lam| * (ℓ i * |ξ i|) = ∑ i, |lam| * ℓ i * |ξ i| :=
        Finset.sum_congr rfl fun i _ => by ring
      rw [hs]
      ring
    linarith [h1, h7, h9.le, h9.ge]
  calc Real.exp (lam * (F ξ - c))
      ≤ Real.exp (|lam| * (|F 0| + |c|) + ∑ i, |lam| * ℓ i * |ξ i|) :=
        Real.exp_le_exp.mpr hbnd
    _ = Real.exp (|lam| * (|F 0| + |c|)) * ∏ i, Real.exp (|lam| * ℓ i * |ξ i|) := by
        rw [Real.exp_add, Real.exp_sum]
    _ = Real.exp (|lam| * (|F 0| + |c|)) * ∏ i, Real.exp (|lam| * ℓ i * |ξ i|) := rfl

theorem measurable_cons_pair :
    Measurable fun p : ℝ × (Fin N → ℝ) => (Fin.cons p.1 p.2 : Fin (N + 1) → ℝ) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.cases ?_ ?_ i
  · simp only [Fin.cons_zero]
    exact measurable_fst
  · intro j
    simp only [Fin.cons_succ]
    exact (measurable_pi_apply j).comp measurable_snd

theorem measurable_cons (y : ℝ) :
    Measurable fun η : Fin N → ℝ => (Fin.cons y η : Fin (N + 1) → ℝ) :=
  measurable_cons_pair.comp (measurable_const.prodMk measurable_id)

theorem cons_update_zero (y z : ℝ) (η : Fin N → ℝ) :
    Function.update (Fin.cons y η : Fin (N + 1) → ℝ) 0 z = Fin.cons z η := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp
  · intro k
    simp

theorem cons_update_succ (y : ℝ) (η : Fin N → ℝ) (j : Fin N) (z : ℝ) :
    (Fin.cons y (Function.update η j z) : Fin (N + 1) → ℝ)
      = Function.update (Fin.cons y η) j.succ z := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [Function.update_of_ne (Fin.succ_ne_zero j).symm]
  · intro k
    by_cases h : k = j
    · subst h; simp
    · have hs : k.succ ≠ j.succ := fun hc => h (Fin.succ_injective _ hc)
      rw [Fin.cons_succ, Function.update_of_ne h, Function.update_of_ne hs, Fin.cons_succ]

theorem cons_comp (ξ : Fin (N + 1) → ℝ) :
    (Fin.cons (ξ 0) fun j => ξ (Fin.succAbove 0 j) : Fin (N + 1) → ℝ) = ξ := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp
  · intro j
    simp

theorem integrable_prod_cons (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (H : (Fin (N + 1) → ℝ) → ℝ) (hH : Integrable H (Measure.pi fun _ : Fin (N + 1) => ν)) :
    Integrable (fun p : ℝ × (Fin N → ℝ) => H (Fin.cons p.1 p.2))
      (ν.prod (Measure.pi fun _ : Fin N => ν)) := by
  classical
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) 0 with hedef
  have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (N + 1) => ν)
      (ν.prod (Measure.pi fun _ : Fin N => ν)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => ν) 0
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  rw [← hmp.integrable_comp_emb hemb]
  refine hH.congr (Filter.Eventually.of_forall fun ξ => ?_)
  show H ξ = H (Fin.cons (ξ 0) fun j => ξ (Fin.succAbove 0 j))
  rw [cons_comp]

/-- The head-tail split of an integral against a product of `N + 1` copies. -/
theorem integral_pi_succ (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (F : (Fin (N + 1) → ℝ) → ℝ) (hF : Integrable F (Measure.pi fun _ : Fin (N + 1) => ν)) :
    ∫ ξ, F ξ ∂(Measure.pi fun _ : Fin (N + 1) => ν)
      = ∫ y, (∫ η, F (Fin.cons y η) ∂(Measure.pi fun _ : Fin N => ν)) ∂ν := by
  classical
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) 0 with hedef
  have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (N + 1) => ν)
      (ν.prod (Measure.pi fun _ : Fin N => ν)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => ν) 0
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  have hGint := integrable_prod_cons ν F hF
  have h1 : ∫ ξ, F ξ ∂(Measure.pi fun _ : Fin (N + 1) => ν)
      = ∫ p, F (Fin.cons p.1 p.2) ∂(ν.prod (Measure.pi fun _ : Fin N => ν)) := by
    rw [← hmp.integral_comp hemb (fun p => F (Fin.cons p.1 p.2))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show F ξ = F (Fin.cons (ξ 0) fun j => ξ (Fin.succAbove 0 j))
    rw [cons_comp]
  rw [h1, integral_prod _ hGint]

theorem integrable_integral_cons (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (H : (Fin (N + 1) → ℝ) → ℝ) (hH : Integrable H (Measure.pi fun _ : Fin (N + 1) => ν)) :
    Integrable (fun y => ∫ η, H (Fin.cons y η) ∂(Measure.pi fun _ : Fin N => ν)) ν :=
  (integrable_prod_cons ν H hH).integral_prod_left

/-! ### Integrability of a Lipschitz function itself -/

theorem integrable_eval_abs (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (habs : Integrable (fun z => |z|) ν) (i : Fin N) :
    Integrable (fun ξ : Fin N → ℝ => |ξ i|) (Measure.pi fun _ : Fin N => ν) := by
  classical
  have h : Integrable (fun ξ : Fin N → ℝ => ∏ j, (if j = i then |ξ j| else 1))
      (Measure.pi fun _ : Fin N => ν) := by
    refine Integrable.fintype_prod (f := fun j z => if j = i then |z| else 1) fun j => ?_
    by_cases hj : j = i
    · simpa [hj] using habs
    · simp only [if_neg hj]
      exact integrable_const (1 : ℝ)
  refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
  show (∏ j, if j = i then |ξ j| else 1) = |ξ i|
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj])
    (fun hi => absurd (Finset.mem_univ i) hi)]
  simp

theorem integrable_of_lip (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (habs : Integrable (fun z => |z|) ν) (F : (Fin N → ℝ) → ℝ) (hFm : Measurable F)
    (ℓ : Fin N → ℝ)
    (hLip : ∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
      |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) :
    Integrable F (Measure.pi fun _ : Fin N => ν) := by
  refine Integrable.mono'
    ((integrable_finsetSum Finset.univ
        fun i _ => (integrable_eval_abs ν habs i).const_mul (ℓ i)).add
      (integrable_const |F 0|))
    hFm.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  have hglob : |F ξ - F 0| ≤ ∑ i, ℓ i * |ξ i| := by
    refine le_trans (abs_sub_le_sum_lip F ℓ hLip ξ 0) (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => by simp
  have hsplit : |F ξ| ≤ |F ξ - F 0| + |F 0| := by
    have h2 := abs_add_le (F ξ - F 0) (F 0)
    simpa using h2
  linarith


/-! ### The exponential concentration inequality -/

/-- Part (d) of `lem:weighted-exp-conc`, by induction on the coordinates: the
first coordinate is split off, the inner integral is bounded uniformly by the
inductive hypothesis, and what remains is a centred Lipschitz function of one
coordinate. -/
theorem exp_conc_pi (ν : Measure ℝ) [IsProbabilityMeasure ν] (θ₀ K δ : ℝ)
    (hθ₀ : 0 < θ₀) (hδ : 0 < δ) (hδθ : δ ≤ θ₀)
    (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hK : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K) (lam : ℝ) :
    ∀ (M : ℕ) (F : (Fin M → ℝ) → ℝ), Measurable F → ∀ ℓ : Fin M → ℝ, (∀ i, 0 ≤ ℓ i) →
      (∀ (ξ : Fin M → ℝ) (i : Fin M) (y : ℝ),
        |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) →
      (∀ i, |lam| * ℓ i ≤ θ₀ - δ) →
        ∫ ξ, Real.exp (lam * (F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin M => ν)))
            ∂(Measure.pi fun _ : Fin M => ν)
          ≤ Real.exp (4 * (Real.exp K * K) / δ ^ 2 * lam ^ 2 * ∑ i, ℓ i ^ 2) := by
  have habs : Integrable (fun z => |z|) ν := (integrable_id_of_exp_moment ν θ₀ hθ₀ hexp).abs
  set C : ℝ := 4 * (Real.exp K * K) / δ ^ 2 with hC
  intro M
  induction M with
  | zero =>
      intro F hFm ℓ hℓ hLip hgap
      have hconst : ∀ η : Fin 0 → ℝ, F η = F (fun _ => 0) := fun η => by
        congr 1
        exact Subsingleton.elim η _
      have hI : ∫ η, F η ∂(Measure.pi fun _ : Fin 0 => ν) = F (fun _ => 0) := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hconst)]
        simp
      rw [hI]
      have hzero : ∀ ξ : Fin 0 → ℝ, Real.exp (lam * (F ξ - F (fun _ => 0))) = 1 := by
        intro ξ
        rw [hconst ξ]
        simp
      rw [integral_congr_ae (Filter.Eventually.of_forall hzero)]
      simp
  | succ N ih =>
      intro F hFm ℓ hℓ hLip hgap
      have hgap' : ∀ i : Fin (N + 1), |lam| * ℓ i ≤ θ₀ := fun i =>
        le_trans (hgap i) (by linarith)
      have hFint : Integrable F (Measure.pi fun _ : Fin (N + 1) => ν) :=
        integrable_of_lip ν habs F hFm ℓ hLip
      set μ0 : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => ν with hμ0
      set G : ℝ → ℝ := fun y => ∫ η, F (Fin.cons y η) ∂μ0 with hGdef
      have hGm : Measurable G := by
        have hfm : Measurable fun p : ℝ × (Fin N → ℝ) => F (Fin.cons p.1 p.2) :=
          hFm.comp measurable_cons_pair
        exact (hfm.stronglyMeasurable.integral_prod_right').measurable
      set EF : ℝ := ∫ ξ, F ξ ∂(Measure.pi fun _ : Fin (N + 1) => ν) with hEFdef
      have hEF : EF = ∫ y, G y ∂ν := integral_pi_succ ν F hFint
      have hconsLip : ∀ y : ℝ, ∀ (η : Fin N → ℝ) (j : Fin N) (z : ℝ),
          |F (Fin.cons y η) - F (Fin.cons y (Function.update η j z))|
            ≤ ℓ j.succ * |η j - z| := by
        intro y η j z
        rw [cons_update_succ]
        have h := hLip (Fin.cons y η) j.succ z
        simpa using h
      have hconsm : ∀ y : ℝ, Measurable fun η : Fin N → ℝ => F (Fin.cons y η) :=
        fun y => hFm.comp (measurable_cons y)
      have hinner : ∀ y : ℝ,
          ∫ η, Real.exp (lam * (F (Fin.cons y η) - G y)) ∂μ0
            ≤ Real.exp (C * lam ^ 2 * ∑ j : Fin N, ℓ j.succ ^ 2) :=
        fun y => ih (fun η => F (Fin.cons y η)) (hconsm y) (fun j => ℓ j.succ)
          (fun j => hℓ _) (hconsLip y) (fun j => hgap _)
      have hGlip : ∀ y z : ℝ, |G y - G z| ≤ ℓ 0 * |y - z| := by
        intro y z
        have hy : Integrable (fun η => F (Fin.cons y η)) μ0 :=
          integrable_of_lip ν habs _ (hconsm y) (fun j => ℓ j.succ) (hconsLip y)
        have hz : Integrable (fun η => F (Fin.cons z η)) μ0 :=
          integrable_of_lip ν habs _ (hconsm z) (fun j => ℓ j.succ) (hconsLip z)
        have hrep : G y - G z = ∫ η, (F (Fin.cons y η) - F (Fin.cons z η)) ∂μ0 := by
          rw [integral_sub hy hz]
        rw [hrep]
        calc |∫ η, (F (Fin.cons y η) - F (Fin.cons z η)) ∂μ0|
            ≤ ∫ η, |F (Fin.cons y η) - F (Fin.cons z η)| ∂μ0 := by
              simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
                (μ := μ0) (f := fun η => F (Fin.cons y η) - F (Fin.cons z η))
          _ ≤ ∫ _η : Fin N → ℝ, ℓ 0 * |y - z| ∂μ0 := by
              refine integral_mono (hy.sub hz).abs (integrable_const _) fun η => ?_
              have h := hLip (Fin.cons y η) 0 z
              rw [cons_update_zero] at h
              simpa using h
          _ = ℓ 0 * |y - z| := by simp
      have hexpint1 : Integrable (fun ξ => Real.exp (lam * (F ξ - EF)))
          (Measure.pi fun _ : Fin (N + 1) => ν) :=
        integrable_exp_lip ν θ₀ hexp F hFm ℓ hLip lam hgap' EF
      have hsplit : ∫ ξ, Real.exp (lam * (F ξ - EF)) ∂(Measure.pi fun _ : Fin (N + 1) => ν)
          = ∫ y, (∫ η, Real.exp (lam * (F (Fin.cons y η) - EF)) ∂μ0) ∂ν :=
        integral_pi_succ ν _ hexpint1
      have hfactor : ∀ y : ℝ, ∫ η, Real.exp (lam * (F (Fin.cons y η) - EF)) ∂μ0
          = Real.exp (lam * (G y - EF)) *
            ∫ η, Real.exp (lam * (F (Fin.cons y η) - G y)) ∂μ0 := by
        intro y
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
        show Real.exp (lam * (F (Fin.cons y η) - EF))
          = Real.exp (lam * (G y - EF)) * Real.exp (lam * (F (Fin.cons y η) - G y))
        rw [← Real.exp_add]
        congr 1
        ring
      have hbig : ∀ y : ℝ, ∫ η, Real.exp (lam * (F (Fin.cons y η) - EF)) ∂μ0
          ≤ Real.exp (lam * (G y - EF)) *
            Real.exp (C * lam ^ 2 * ∑ j : Fin N, ℓ j.succ ^ 2) := by
        intro y
        rw [hfactor y]
        exact mul_le_mul_of_nonneg_left (hinner y) (Real.exp_pos _).le
      have hLint : Integrable
          (fun y => ∫ η, Real.exp (lam * (F (Fin.cons y η) - EF)) ∂μ0) ν :=
        integrable_integral_cons ν _ hexpint1
      have hfac0 : Integrable (fun y : ℝ => Real.exp (|lam| * ℓ 0 * |y|)) ν := by
        refine hexp.mono' ((Real.measurable_exp.comp
          ((measurable_id.abs).const_mul _))).aestronglyMeasurable
          (Filter.Eventually.of_forall fun z => ?_)
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hgap' 0) (abs_nonneg z))
      have hGexpint : Integrable (fun y => Real.exp (lam * (G y - EF))) ν := by
        refine Integrable.mono' (hfac0.const_mul (Real.exp (|lam| * (|G 0| + |EF|))))
          ((Real.measurable_exp.comp ((hGm.sub_const EF).const_mul lam))).aestronglyMeasurable
          (Filter.Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have h1 : lam * (G y - EF) ≤ |lam| * |G y - EF| := by
          calc lam * (G y - EF) ≤ |lam * (G y - EF)| := le_abs_self _
            _ = |lam| * |G y - EF| := abs_mul _ _
        have h2 : |G y - EF| ≤ ℓ 0 * |y| + (|G 0| + |EF|) := by
          have hg := hGlip y 0
          rw [sub_zero] at hg
          have h3 := abs_add_le (G y - G 0) (G 0 - EF)
          have h4 : |G 0 - EF| ≤ |G 0| + |EF| := abs_sub _ _
          have h5 : G y - EF = (G y - G 0) + (G 0 - EF) := by ring
          rw [h5]
          linarith
        have h6 : |lam| * |G y - EF| ≤ |lam| * (ℓ 0 * |y| + (|G 0| + |EF|)) :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg lam)
        have h7 : |lam| * (ℓ 0 * |y| + (|G 0| + |EF|))
            = |lam| * (|G 0| + |EF|) + |lam| * ℓ 0 * |y| := by ring
        linarith [h1, h6, h7.le, h7.ge]
      have houter : ∫ y, Real.exp (lam * (G y - EF)) ∂ν
          ≤ Real.exp (C * lam ^ 2 * ℓ 0 ^ 2) := by
        rcases eq_or_lt_of_le (hℓ 0) with h0 | h0
        · have hGconst : ∀ y z : ℝ, G y = G z := by
            intro y z
            have h := hGlip y z
            rw [← h0, zero_mul] at h
            have habs0 : |G y - G z| = 0 := le_antisymm h (abs_nonneg _)
            have := abs_eq_zero.mp habs0
            linarith
          have hEF0 : EF = G 0 := by
            rw [hEF, integral_congr_ae (Filter.Eventually.of_forall fun y => hGconst y 0)]
            simp
          have hone : ∀ y : ℝ, Real.exp (lam * (G y - EF)) = 1 := by
            intro y
            rw [hEF0, hGconst y 0]
            simp
          rw [integral_congr_ae (Filter.Eventually.of_forall hone), ← h0]
          simp
        · have hSG := subGaussianOn_centred_lip ν θ₀ K hθ₀ hexp hK G hGm (ℓ 0) h0 hGlip δ hδ hδθ
          have hlamle : |lam| ≤ (θ₀ - δ) / ℓ 0 := by
            rw [le_div_iff₀ h0]
            exact hgap 0
          rw [hEF]
          exact le_trans (hSG lam hlamle).2 (le_of_eq (congrArg Real.exp (by rw [hC]; ring)))
      rw [hsplit]
      calc ∫ y, (∫ η, Real.exp (lam * (F (Fin.cons y η) - EF)) ∂μ0) ∂ν
          ≤ ∫ y, Real.exp (lam * (G y - EF)) *
              Real.exp (C * lam ^ 2 * ∑ j : Fin N, ℓ j.succ ^ 2) ∂ν :=
            integral_mono hLint (hGexpint.mul_const _) hbig
        _ = (∫ y, Real.exp (lam * (G y - EF)) ∂ν) *
              Real.exp (C * lam ^ 2 * ∑ j : Fin N, ℓ j.succ ^ 2) := integral_mul_const _ _
        _ ≤ Real.exp (C * lam ^ 2 * ℓ 0 ^ 2) *
              Real.exp (C * lam ^ 2 * ∑ j : Fin N, ℓ j.succ ^ 2) :=
            mul_le_mul_of_nonneg_right houter (Real.exp_pos _).le
        _ = Real.exp (C * lam ^ 2 * ∑ i : Fin (N + 1), ℓ i ^ 2) := by
            rw [← Real.exp_add, Fin.sum_univ_succ]
            congr 1
            ring

end LatticeProb
