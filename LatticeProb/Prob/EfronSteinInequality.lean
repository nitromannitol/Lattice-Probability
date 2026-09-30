/-
The exponential Efron-Stein inequality itself, and the second-moment integrability
lemmas it needs, completing `LatticeProb.Prob.EfronStein`.

`LatticeProb.Prob.EfronStein` proves the coordinate-telescoping bound and the
exponential concentration inequality `exp_conc_pi`, but stops short of the
Efron-Stein inequality proper: the variance of a coordinate-Lipschitz function
of independent coordinates is at most the total resampling energy, under only a
second-moment hypothesis on the one-site law (no exponential moment needed).
This file adds that theorem, `efron_stein`, together with the integrability
lemmas its proof by induction on the coordinates requires.

Moved from Divisible-Sandpile-Percolation, `Sandpile/Support/EfronStein.lean`.
-/
import Mathlib
import LatticeProb.Prob.EfronStein

open MeasureTheory

namespace LatticeProb

variable {N : ℕ}

/-! ### Integrability under a coordinate Lipschitz bound and a second moment -/

/-- A real random variable with a finite second moment has a finite first
absolute moment. -/
theorem integrable_abs_of_sq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) : Integrable (fun z => |z|) ν := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hsq)
    (measurable_id.abs).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  simp only [Real.norm_eq_abs, abs_abs, Pi.add_apply]
  nlinarith [sq_nonneg (|z| - 1), abs_nonneg z, sq_abs z]

/-- Composing an integrable function of one real variable with a single
coordinate of a product configuration is integrable against the product
measure. -/
theorem integrable_eval_comp (ν : Measure ℝ) [IsProbabilityMeasure ν] (f : ℝ → ℝ)
    (hf : Integrable f ν) (i : Fin N) :
    Integrable (fun ξ : Fin N → ℝ => f (ξ i)) (Measure.pi fun _ : Fin N => ν) := by
  classical
  have h : Integrable (fun ξ : Fin N → ℝ => ∏ j, (if j = i then f (ξ j) else 1))
      (Measure.pi fun _ : Fin N => ν) := by
    refine Integrable.fintype_prod (f := fun j z => if j = i then f z else 1) fun j => ?_
    by_cases hj : j = i
    · simpa [hj] using hf
    · simp only [if_neg hj]
      exact integrable_const (1 : ℝ)
  refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
  show (∏ j, if j = i then f (ξ j) else 1) = f (ξ i)
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj])
    (fun hi => absurd (Finset.mem_univ i) hi)]
  simp

/-- One coordinate of a product configuration has an integrable square when
the one-site law does. -/
theorem integrable_eval_sq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) (i : Fin N) :
    Integrable (fun ξ : Fin N → ℝ => ξ i ^ 2) (Measure.pi fun _ : Fin N => ν) :=
  integrable_eval_comp ν (fun z => z ^ 2) hsq i

/-- One coordinate of a product configuration is itself integrable when the
one-site law has a second moment. -/
theorem integrable_eval_id (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) (i : Fin N) :
    Integrable (fun ξ : Fin N → ℝ => ξ i) (Measure.pi fun _ : Fin N => ν) := by
  have h := integrable_eval_comp ν (fun z => z) (by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hsq)
      measurable_id.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    nlinarith [sq_nonneg (|z| - 1), abs_nonneg z, sq_abs z, le_abs_self z]) i
  exact h

/-- A coordinate-Lipschitz function is square integrable when the one-site law
has a second moment. -/
theorem integrable_sq_of_lip (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν)
    (G : (Fin N → ℝ) → ℝ) (hGm : Measurable G) (c : Fin N → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hLip : ∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
      |G ξ - G (Function.update ξ i y)| ≤ c i * |ξ i - y|) (a : ℝ) :
    Integrable (fun ξ => (G ξ - a) ^ 2) (Measure.pi fun _ : Fin N => ν) := by
  have hdom : Integrable (fun ξ : Fin N → ℝ =>
      2 * (G 0 - a) ^ 2 + 2 * (N : ℝ) * ∑ i, c i ^ 2 * ξ i ^ 2)
      (Measure.pi fun _ : Fin N => ν) :=
    (integrable_const _).add
      ((integrable_finsetSum Finset.univ
        fun i _ => (integrable_eval_sq ν hsq i).const_mul (c i ^ 2)).const_mul _)
  refine Integrable.mono' hdom ((hGm.sub_const a).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hglob : |G ξ - G 0| ≤ ∑ i, c i * |ξ i| := by
    refine le_trans (abs_sub_le_sum_lip G c hLip ξ 0) (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => by simp
  have hcs : (∑ i, c i * |ξ i|) ^ 2 ≤ (N : ℝ) * ∑ i, c i ^ 2 * ξ i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N)))
      (f := fun i => c i * |ξ i|)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    refine le_trans h (le_of_eq ?_)
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [mul_pow, sq_abs]
  have hsum0 : 0 ≤ ∑ i, c i * |ξ i| :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (abs_nonneg _)
  have h1 : |G ξ - a| ≤ |G ξ - G 0| + |G 0 - a| := by
    have h2 := abs_add_le (G ξ - G 0) (G 0 - a)
    have h3 : G ξ - a = (G ξ - G 0) + (G 0 - a) := by ring
    rw [h3]
    exact h2
  have h4 : |G ξ - a| ≤ (∑ i, c i * |ξ i|) + |G 0 - a| := by linarith
  have h5 : (G ξ - a) ^ 2 = |G ξ - a| ^ 2 := (sq_abs _).symm
  rw [h5]
  have h6 : |G ξ - a| ^ 2 ≤ ((∑ i, c i * |ξ i|) + |G 0 - a|) ^ 2 := by
    refine pow_le_pow_left₀ (abs_nonneg _) h4 2
  refine le_trans h6 ?_
  have h7 : ((∑ i, c i * |ξ i|) + |G 0 - a|) ^ 2
      ≤ 2 * (∑ i, c i * |ξ i|) ^ 2 + 2 * |G 0 - a| ^ 2 := by
    nlinarith [sq_nonneg ((∑ i, c i * |ξ i|) - |G 0 - a|)]
  have h8 : |G 0 - a| ^ 2 = (G 0 - a) ^ 2 := sq_abs _
  have h9 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith [h7, hcs, h8]

/-- A coordinate-Lipschitz function is integrable when the one-site law has a
second moment. -/
theorem integrable_of_lip_sq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν)
    (G : (Fin N → ℝ) → ℝ) (hGm : Measurable G) (c : Fin N → ℝ)
    (hLip : ∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
      |G ξ - G (Function.update ξ i y)| ≤ c i * |ξ i - y|) :
    Integrable G (Measure.pi fun _ : Fin N => ν) :=
  integrable_of_lip ν (integrable_abs_of_sq ν hsq) G hGm c hLip

/-- The resampling energy in one coordinate is integrable. -/
theorem integrable_resample (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν)
    (G : (Fin N → ℝ) → ℝ) (hGm : Measurable G) (c : Fin N → ℝ) (_hc : ∀ i, 0 ≤ c i)
    (hLip : ∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
      |G ξ - G (Function.update ξ i y)| ≤ c i * |ξ i - y|) (i : Fin N) :
    Integrable (fun ξ => ∫ y, (G ξ - G (Function.update ξ i y)) ^ 2 ∂ν)
      (Measure.pi fun _ : Fin N => ν) := by
  have hid : Integrable (fun z => z) ν := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hsq)
      measurable_id.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    nlinarith [sq_nonneg (|z| - 1), abs_nonneg z, sq_abs z, le_abs_self z]
  have hpair : Measurable fun p : (Fin N → ℝ) × ℝ =>
      (G p.1 - G (Function.update p.1 i p.2)) ^ 2 :=
    (((hGm.comp measurable_fst).sub (hGm.comp (measurable_update_pair i))).pow_const 2)
  have hm : Measurable fun ξ : Fin N → ℝ =>
      ∫ y, (G ξ - G (Function.update ξ i y)) ^ 2 ∂ν :=
    (hpair.stronglyMeasurable.integral_prod_right').measurable
  set m₁ : ℝ := ∫ z, z ∂ν with hm₁
  set m₂ : ℝ := ∫ z, z ^ 2 ∂ν with hm₂
  have hdom : Integrable (fun ξ : Fin N → ℝ =>
      c i ^ 2 * (ξ i ^ 2 - 2 * ξ i * m₁ + m₂)) (Measure.pi fun _ : Fin N => ν) := by
    refine Integrable.const_mul ?_ _
    refine ((integrable_eval_sq ν hsq i).sub ?_).add (integrable_const _)
    have := (integrable_eval_id ν hsq i).const_mul (2 * m₁)
    exact this.congr (Filter.Eventually.of_forall fun ξ => by ring)
  refine Integrable.mono' hdom hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  have hnn : 0 ≤ ∫ y, (G ξ - G (Function.update ξ i y)) ^ 2 ∂ν :=
    integral_nonneg fun y => sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have hbnd : ∀ y : ℝ, (G ξ - G (Function.update ξ i y)) ^ 2
      ≤ c i ^ 2 * (ξ i ^ 2 - 2 * ξ i * y + y ^ 2) := by
    intro y
    have h := hLip ξ i y
    have h1 : (G ξ - G (Function.update ξ i y)) ^ 2 ≤ (c i * |ξ i - y|) ^ 2 := by
      rw [← sq_abs (G ξ - G (Function.update ξ i y))]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have h2 : (c i * |ξ i - y|) ^ 2 = c i ^ 2 * (ξ i - y) ^ 2 := by
      rw [mul_pow, sq_abs]
    have h3 : (ξ i - y) ^ 2 = ξ i ^ 2 - 2 * ξ i * y + y ^ 2 := by ring
    rw [h2, h3] at h1
    exact h1
  have hint2 : Integrable (fun y : ℝ => c i ^ 2 * (ξ i ^ 2 - 2 * ξ i * y + y ^ 2)) ν := by
    refine Integrable.const_mul ?_ _
    refine ((integrable_const _).sub ?_).add hsq
    have := hid.const_mul (2 * ξ i)
    exact this.congr (Filter.Eventually.of_forall fun y => by ring)
  have hym : Measurable fun y : ℝ => (G ξ - G (Function.update ξ i y)) ^ 2 := by
    have h1 : Measurable fun y : ℝ => Function.update ξ i y :=
      (measurable_update_pair i).comp (measurable_const.prodMk measurable_id)
    exact (measurable_const.sub (hGm.comp h1)).pow_const 2
  have hintL : Integrable (fun y : ℝ => (G ξ - G (Function.update ξ i y)) ^ 2) ν :=
    Integrable.mono' hint2 hym.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hbnd y)
  have hle := integral_mono hintL hint2 hbnd
  have hquad : ∫ y, (ξ i ^ 2 - 2 * ξ i * y + y ^ 2) ∂ν = ξ i ^ 2 - 2 * ξ i * m₁ + m₂ := by
    have hA : Integrable (fun y : ℝ => ξ i ^ 2 - 2 * ξ i * y) ν :=
      (integrable_const _).sub (hid.const_mul (2 * ξ i))
    rw [integral_add hA hsq,
      integral_sub (integrable_const _) (hid.const_mul (2 * ξ i)), integral_const,
      integral_const_mul]
    simp only [smul_eq_mul, probReal_univ, one_mul]
    rw [← hm₁, ← hm₂]
  refine le_trans hle (le_of_eq ?_)
  rw [integral_const_mul, hquad]

/-! ### One-variable Lipschitz integrability, and one Fubini swap -/

/-- A Lipschitz function of a real variable is integrable when the underlying
law has a second moment. -/
theorem integrable_lip_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) (g : ℝ → ℝ) (hgm : Measurable g) (L : ℝ)
    (_hL : 0 ≤ L) (hglip : ∀ y z, |g y - g z| ≤ L * |y - z|) :
    Integrable g ν := by
  refine Integrable.mono' ((hsq.const_mul (L ^ 2)).add (integrable_const (2 + |g 0| ^ 2)))
    hgm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  have h1 : |g y| ≤ |g 0| + L * |y| := by
    have h := hglip y 0
    rw [sub_zero] at h
    have h2 := abs_add_le (g y - g 0) (g 0)
    have h3 : g y = (g y - g 0) + g 0 := by ring
    calc |g y| = |(g y - g 0) + g 0| := by rw [← h3]
      _ ≤ |g y - g 0| + |g 0| := h2
      _ ≤ L * |y| + |g 0| := by linarith
      _ = |g 0| + L * |y| := by ring
  have hb1 : |g 0| ≤ 1 + |g 0| ^ 2 := by nlinarith [sq_nonneg (|g 0| - 1), abs_nonneg (g 0)]
  have hsqy : (L * |y|) ^ 2 = L ^ 2 * y ^ 2 := by rw [mul_pow, sq_abs]
  have hb2 : L * |y| ≤ 1 + L ^ 2 * y ^ 2 := by
    nlinarith [sq_nonneg (L * |y| - 1), hsqy]
  linarith [h1, hb1, hb2]

/-- The centred square of a Lipschitz function of a real variable is
integrable when the underlying law has a second moment. -/
theorem integrable_sq_lip_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) (g : ℝ → ℝ) (hgm : Measurable g) (L : ℝ)
    (_hL : 0 ≤ L) (hglip : ∀ y z, |g y - g z| ≤ L * |y - z|) (a : ℝ) :
    Integrable (fun y => (g y - a) ^ 2) ν := by
  refine Integrable.mono'
    ((hsq.const_mul (2 * L ^ 2)).add (integrable_const (2 * (g 0 - a) ^ 2)))
    ((hgm.sub_const a).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_of_nonneg (sq_nonneg _)]
  have h1 : |g y - a| ≤ L * |y| + |g 0 - a| := by
    have h := hglip y 0
    rw [sub_zero] at h
    have h2 := abs_add_le (g y - g 0) (g 0 - a)
    have h3 : g y - a = (g y - g 0) + (g 0 - a) := by ring
    calc |g y - a| = |(g y - g 0) + (g 0 - a)| := by rw [← h3]
      _ ≤ |g y - g 0| + |g 0 - a| := h2
      _ ≤ L * |y| + |g 0 - a| := by linarith
  have h4 : (g y - a) ^ 2 = |g y - a| ^ 2 := (sq_abs _).symm
  rw [h4]
  have h5 : |g y - a| ^ 2 ≤ (L * |y| + |g 0 - a|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h6 : (L * |y| + |g 0 - a|) ^ 2 ≤ 2 * (L * |y|) ^ 2 + 2 * |g 0 - a| ^ 2 := by
    nlinarith [sq_nonneg (L * |y| - |g 0 - a|)]
  have h7 : (L * |y|) ^ 2 = L ^ 2 * y ^ 2 := by rw [mul_pow, sq_abs]
  have h8 : |g 0 - a| ^ 2 = (g 0 - a) ^ 2 := sq_abs _
  linarith [h5, h6, h7.le, h7.ge, h8.le, h8.ge]

/-- A function of the first coordinate alone of a product space is integrable
against the product measure when it is integrable against the first factor. -/
theorem integrable_comp_fst' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (κ : Measure β) [IsProbabilityMeasure κ]
    {H : α → ℝ} (hH : Integrable H μ) :
    Integrable (fun p : α × β => H p.1) (μ.prod κ) := by
  have hmapfst : (μ.prod κ).map Prod.fst = μ := Measure.fst_prod
  have hasm : AEStronglyMeasurable H ((μ.prod κ).map Prod.fst) := by
    rw [hmapfst]; exact hH.aestronglyMeasurable
  show Integrable (H ∘ Prod.fst) _
  refine (integrable_map_measure hasm measurable_fst.aemeasurable).mp ?_
  rw [hmapfst]
  exact hH

/-- Fubini for a jointly measurable function dominated by an integrable function
of the first variable. -/
theorem integral_swap_bounded {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (κ : Measure β) [IsProbabilityMeasure κ]
    (f : α → β → ℝ) (hf : Measurable (Function.uncurry f)) (b : α → ℝ)
    (hb : Integrable b μ) (hbound : ∀ x y, |f x y| ≤ b x) :
    ∫ x, (∫ y, f x y ∂κ) ∂μ = ∫ y, (∫ x, f x y ∂μ) ∂κ := by
  refine integral_integral_swap ?_
  refine Integrable.mono' (integrable_comp_fst' μ κ hb) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  exact hbound p.1 p.2

/-! ### The Efron-Stein inequality

The variance of a coordinate-Lipschitz function of independent coordinates is at
most the total resampling energy.  The constant here is `1` rather than the
optimal `1/2`, because the head term is bounded by Jensen twice rather than by
the exact variance identity; every use in the paper carries a free constant. -/

/-- The Efron-Stein inequality: for a function of `M` independent real
coordinates that is `c i`-Lipschitz in coordinate `i`, the variance is bounded
by the total resampling energy `∑ i, E[(G ξ - G (ξ with i resampled))²]`, under
only a second-moment hypothesis on the one-site law. -/
theorem efron_stein (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) :
    ∀ (M : ℕ) (G : (Fin M → ℝ) → ℝ), Measurable G → ∀ c : Fin M → ℝ, (∀ i, 0 ≤ c i) →
      (∀ (ξ : Fin M → ℝ) (i : Fin M) (y : ℝ),
        |G ξ - G (Function.update ξ i y)| ≤ c i * |ξ i - y|) →
        ∫ ξ, (G ξ - ∫ η, G η ∂(Measure.pi fun _ : Fin M => ν)) ^ 2
            ∂(Measure.pi fun _ : Fin M => ν)
          ≤ ∑ i, ∫ ξ, (∫ y, (G ξ - G (Function.update ξ i y)) ^ 2 ∂ν)
              ∂(Measure.pi fun _ : Fin M => ν) := by
  intro M
  induction M with
  | zero =>
      intro G hGm c hc hLip
      have hconst : ∀ η : Fin 0 → ℝ, G η = G (fun _ => 0) := fun η => by
        congr 1
        exact Subsingleton.elim η _
      have hI : ∫ η, G η ∂(Measure.pi fun _ : Fin 0 => ν) = G (fun _ => 0) := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hconst)]
        simp
      rw [hI]
      have hz : ∀ ξ : Fin 0 → ℝ, (G ξ - G (fun _ => 0)) ^ 2 = 0 := by
        intro ξ
        rw [hconst ξ]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hz)]
      simp
  | succ N ih =>
      intro G hGm c hc hLip
      have hGint : Integrable G (Measure.pi fun _ : Fin (N + 1) => ν) :=
        integrable_of_lip_sq ν hsq G hGm c hLip
      have hconsm : ∀ y : ℝ, Measurable fun η : Fin N → ℝ => G (Fin.cons y η) :=
        fun y => hGm.comp (measurable_cons y)
      have hconsLip : ∀ y : ℝ, ∀ (η : Fin N → ℝ) (j : Fin N) (z : ℝ),
          |G (Fin.cons y η) - G (Fin.cons y (Function.update η j z))|
            ≤ c j.succ * |η j - z| := by
        intro y η j z
        rw [cons_update_succ]
        have h := hLip (Fin.cons y η) j.succ z
        simpa using h
      have hconsint : ∀ y : ℝ, Integrable (fun η => G (Fin.cons y η))
          (Measure.pi fun _ : Fin N => ν) :=
        fun y => integrable_of_lip_sq ν hsq _ (hconsm y) (fun j => c j.succ) (hconsLip y)
      set g : ℝ → ℝ := fun y => ∫ η, G (Fin.cons y η) ∂(Measure.pi fun _ : Fin N => ν)
        with hgdef
      have hgm : Measurable g := by
        have hfm : Measurable fun p : ℝ × (Fin N → ℝ) => G (Fin.cons p.1 p.2) :=
          hGm.comp measurable_cons_pair
        exact (hfm.stronglyMeasurable.integral_prod_right').measurable
      have hcons0 : ∀ (y z : ℝ) (η : Fin N → ℝ),
          |G (Fin.cons y η) - G (Fin.cons z η)| ≤ c 0 * |y - z| := by
        intro y z η
        have h := hLip (Fin.cons y η) 0 z
        rw [cons_update_zero] at h
        simpa using h
      have hglip : ∀ y z : ℝ, |g y - g z| ≤ c 0 * |y - z| := by
        intro y z
        have hrep : g y - g z = ∫ η, (G (Fin.cons y η) - G (Fin.cons z η))
            ∂(Measure.pi fun _ : Fin N => ν) := by
          rw [integral_sub (hconsint y) (hconsint z)]
        rw [hrep]
        calc |∫ η, (G (Fin.cons y η) - G (Fin.cons z η)) ∂(Measure.pi fun _ : Fin N => ν)|
            ≤ ∫ η, |G (Fin.cons y η) - G (Fin.cons z η)| ∂(Measure.pi fun _ : Fin N => ν) := by
              simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
                (μ := Measure.pi fun _ : Fin N => ν)
                (f := fun η => G (Fin.cons y η) - G (Fin.cons z η))
          _ ≤ ∫ _η : Fin N → ℝ, c 0 * |y - z| ∂(Measure.pi fun _ : Fin N => ν) :=
              integral_mono ((hconsint y).sub (hconsint z)).abs (integrable_const _)
                (fun η => hcons0 y z η)
          _ = c 0 * |y - z| := by simp
      have hgint : Integrable g ν := integrable_lip_one ν hsq g hgm (c 0) (hc 0) hglip
      have hgsq : ∀ a : ℝ, Integrable (fun y => (g y - a) ^ 2) ν :=
        fun a => integrable_sq_lip_one ν hsq g hgm (c 0) (hc 0) hglip a
      set EG : ℝ := ∫ ξ, G ξ ∂(Measure.pi fun _ : Fin (N + 1) => ν) with hEGdef
      have hEG : EG = ∫ y, g y ∂ν := integral_pi_succ ν G hGint
      -- the resampling energies
      set H : Fin (N + 1) → (Fin (N + 1) → ℝ) → ℝ :=
        fun i ξ => ∫ y, (G ξ - G (Function.update ξ i y)) ^ 2 ∂ν with hHdef
      have hHint : ∀ i, Integrable (H i) (Measure.pi fun _ : Fin (N + 1) => ν) :=
        fun i => integrable_resample ν hsq G hGm c hc hLip i
      have hHsplit : ∀ i, ∫ ξ, H i ξ ∂(Measure.pi fun _ : Fin (N + 1) => ν)
          = ∫ y, (∫ η, H i (Fin.cons y η) ∂(Measure.pi fun _ : Fin N => ν)) ∂ν :=
        fun i => integral_pi_succ ν (H i) (hHint i)
      have hRint : ∀ i, Integrable
          (fun y => ∫ η, H i (Fin.cons y η) ∂(Measure.pi fun _ : Fin N => ν)) ν :=
        fun i => integrable_integral_cons ν (H i) (hHint i)
      -- the tail term
      have hAle : ∀ y : ℝ,
          ∫ η, (G (Fin.cons y η) - g y) ^ 2 ∂(Measure.pi fun _ : Fin N => ν)
            ≤ ∑ j : Fin N, ∫ η, H j.succ (Fin.cons y η)
                ∂(Measure.pi fun _ : Fin N => ν) := by
        intro y
        have h := ih (fun η => G (Fin.cons y η)) (hconsm y) (fun j => c j.succ)
          (fun j => hc _) (hconsLip y)
        refine le_trans h (le_of_eq ?_)
        refine Finset.sum_congr rfl fun j _ => ?_
        refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
        show (∫ y', (G (Fin.cons y η) - G (Fin.cons y (Function.update η j y'))) ^ 2 ∂ν)
          = H j.succ (Fin.cons y η)
        rw [hHdef]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y' => ?_)
        show (G (Fin.cons y η) - G (Fin.cons y (Function.update η j y'))) ^ 2
          = (G (Fin.cons y η) - G (Function.update (Fin.cons y η) j.succ y')) ^ 2
        rw [cons_update_succ]
      set A : ℝ → ℝ :=
        fun y => ∫ η, (G (Fin.cons y η) - g y) ^ 2 ∂(Measure.pi fun _ : Fin N => ν)
        with hAdef
      have hAm : Measurable A := by
        have hfm : Measurable fun p : ℝ × (Fin N → ℝ) =>
            (G (Fin.cons p.1 p.2) - g p.1) ^ 2 :=
          (((hGm.comp measurable_cons_pair).sub (hgm.comp measurable_fst)).pow_const 2)
        exact (hfm.stronglyMeasurable.integral_prod_right').measurable
      have hAnn : ∀ y, 0 ≤ A y := fun y => integral_nonneg fun η => sq_nonneg _
      have hDomint : Integrable
          (fun y => ∑ j : Fin N, ∫ η, H j.succ (Fin.cons y η)
            ∂(Measure.pi fun _ : Fin N => ν)) ν :=
        integrable_finsetSum Finset.univ fun j _ => hRint j.succ
      have hAint : Integrable A ν :=
        Integrable.mono' hDomint hAm.aestronglyMeasurable
          (Filter.Eventually.of_forall fun y => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hAnn y)]
            exact hAle y)
      have hAsum : ∫ y, A y ∂ν
          ≤ ∑ j : Fin N, ∫ ξ, H j.succ ξ ∂(Measure.pi fun _ : Fin (N + 1) => ν) := by
        refine le_trans (integral_mono hAint hDomint hAle) (le_of_eq ?_)
        rw [integral_finsetSum Finset.univ fun j _ => hRint j.succ]
        exact Finset.sum_congr rfl fun j _ => (hHsplit j.succ).symm
      -- the head term
      set S : ℝ → ℝ → ℝ :=
        fun y y' => ∫ η, (G (Fin.cons y η) - G (Fin.cons y' η)) ^ 2
          ∂(Measure.pi fun _ : Fin N => ν) with hSdef
      have hSbound : ∀ y y' : ℝ, S y y' ≤ c 0 ^ 2 * (y - y') ^ 2 := by
        intro y y'
        have hpt : ∀ η : Fin N → ℝ,
            (G (Fin.cons y η) - G (Fin.cons y' η)) ^ 2 ≤ c 0 ^ 2 * (y - y') ^ 2 := by
          intro η
          have h := hcons0 y y' η
          have h1 : (G (Fin.cons y η) - G (Fin.cons y' η)) ^ 2 ≤ (c 0 * |y - y'|) ^ 2 := by
            rw [← sq_abs (G (Fin.cons y η) - G (Fin.cons y' η))]
            exact pow_le_pow_left₀ (abs_nonneg _) h 2
          calc (G (Fin.cons y η) - G (Fin.cons y' η)) ^ 2 ≤ (c 0 * |y - y'|) ^ 2 := h1
            _ = c 0 ^ 2 * (y - y') ^ 2 := by rw [mul_pow, sq_abs]
        have hint : Integrable
            (fun η => (G (Fin.cons y η) - G (Fin.cons y' η)) ^ 2)
            (Measure.pi fun _ : Fin N => ν) :=
          Integrable.mono' (integrable_const (c 0 ^ 2 * (y - y') ^ 2))
            ((((hconsm y).sub (hconsm y')).pow_const 2)).aestronglyMeasurable
            (Filter.Eventually.of_forall fun η => by
              rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
              exact hpt η)
        calc S y y' ≤ ∫ _η : Fin N → ℝ, c 0 ^ 2 * (y - y') ^ 2
              ∂(Measure.pi fun _ : Fin N => ν) :=
              integral_mono hint (integrable_const _) hpt
          _ = c 0 ^ 2 * (y - y') ^ 2 := by simp
      have hSjensen : ∀ y y' : ℝ, (g y - g y') ^ 2 ≤ S y y' := by
        intro y y'
        have hrep : g y - g y' = ∫ η, (G (Fin.cons y η) - G (Fin.cons y' η))
            ∂(Measure.pi fun _ : Fin N => ν) := by
          rw [integral_sub (hconsint y) (hconsint y')]
        have hint2 : Integrable
            (fun η => (G (Fin.cons y η) - G (Fin.cons y' η)) ^ 2)
            (Measure.pi fun _ : Fin N => ν) := by
          refine Integrable.mono' (integrable_const (c 0 ^ 2 * (y - y') ^ 2))
            ((((hconsm y).sub (hconsm y')).pow_const 2)).aestronglyMeasurable
            (Filter.Eventually.of_forall fun η => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          have h := hcons0 y y' η
          have h1 : (G (Fin.cons y η) - G (Fin.cons y' η)) ^ 2 ≤ (c 0 * |y - y'|) ^ 2 := by
            rw [← sq_abs (G (Fin.cons y η) - G (Fin.cons y' η))]
            exact pow_le_pow_left₀ (abs_nonneg _) h 2
          calc (G (Fin.cons y η) - G (Fin.cons y' η)) ^ 2 ≤ (c 0 * |y - y'|) ^ 2 := h1
            _ = c 0 ^ 2 * (y - y') ^ 2 := by rw [mul_pow, sq_abs]
        rw [hrep]
        exact sq_integral_le _ _ ((hconsint y).sub (hconsint y')) hint2
      have hid : Integrable (fun z : ℝ => z) ν := by
        refine Integrable.mono' ((integrable_const (1 : ℝ)).add hsq)
          measurable_id.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
        simp only [Real.norm_eq_abs, Pi.add_apply]
        nlinarith [sq_nonneg (|z| - 1), abs_nonneg z, sq_abs z, le_abs_self z]
      have hquadint : ∀ y : ℝ, Integrable (fun y' : ℝ => c 0 ^ 2 * (y - y') ^ 2) ν := by
        intro y
        refine Integrable.const_mul ?_ _
        have he : (fun y' : ℝ => (y - y') ^ 2)
            = fun y' : ℝ => (y ^ 2 - 2 * y * y') + y' ^ 2 := by funext y'; ring
        rw [he]
        exact ((integrable_const _).sub (hid.const_mul (2 * y))).add hsq
      have hSm : Measurable fun p : ℝ × ℝ => S p.1 p.2 := by
        have hf : Measurable fun q : (ℝ × ℝ) × (Fin N → ℝ) =>
            (G (Fin.cons q.1.1 q.2) - G (Fin.cons q.1.2 q.2)) ^ 2 := by
          have h1 : Measurable fun q : (ℝ × ℝ) × (Fin N → ℝ) => G (Fin.cons q.1.1 q.2) :=
            hGm.comp (measurable_cons_pair.comp
              ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
          have h2 : Measurable fun q : (ℝ × ℝ) × (Fin N → ℝ) => G (Fin.cons q.1.2 q.2) :=
            hGm.comp (measurable_cons_pair.comp
              ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
          exact (h1.sub h2).pow_const 2
        exact (hf.stronglyMeasurable.integral_prod_right').measurable
      have hSint : ∀ y : ℝ, Integrable (fun y' => S y y') ν := by
        intro y
        refine Integrable.mono' (hquadint y)
          ((hSm.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
          (Filter.Eventually.of_forall fun y' => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun η => sq_nonneg _)]
        exact hSbound y y'
      have hPint : ∀ y : ℝ, Integrable (fun y' => (g y - g y') ^ 2) ν := fun y =>
        (hgsq (g y)).congr (Filter.Eventually.of_forall fun y' => by ring)
      have hhead1 : ∀ y : ℝ, (g y - EG) ^ 2 ≤ ∫ y', S y y' ∂ν := by
        intro y
        have hrep : g y - EG = ∫ y', (g y - g y') ∂ν := by
          rw [integral_sub (integrable_const _) hgint, integral_const, hEG]
          simp
        have h1 : (g y - EG) ^ 2 ≤ ∫ y', (g y - g y') ^ 2 ∂ν := by
          rw [hrep]
          exact sq_integral_le ν _ ((integrable_const _).sub hgint) (hPint y)
        exact le_trans h1 (integral_mono (hPint y) (hSint y) (hSjensen y))
      have hheadint : Integrable (fun y => ∫ y', S y y' ∂ν) ν := by
        have hm : Measurable fun y => ∫ y', S y y' ∂ν :=
          (hSm.stronglyMeasurable.integral_prod_right').measurable
        have hdom : Integrable
            (fun y : ℝ => c 0 ^ 2 * (y ^ 2 - 2 * y * (∫ z, z ∂ν) + ∫ z, z ^ 2 ∂ν)) ν := by
          refine Integrable.const_mul ?_ _
          exact ((hsq.sub (hid.const_mul (2 * (∫ z, z ∂ν)))).congr
            (Filter.Eventually.of_forall fun y => by
              simp only [Pi.sub_apply]; ring)).add
            (integrable_const (∫ z, z ^ 2 ∂ν))
        refine Integrable.mono' hdom hm.aestronglyMeasurable
          (Filter.Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y' => integral_nonneg
          fun η => sq_nonneg _)]
        refine le_trans (integral_mono (hSint y) (hquadint y) (hSbound y)) (le_of_eq ?_)
        rw [integral_const_mul]
        congr 1
        have he : (fun y' : ℝ => (y - y') ^ 2)
            = fun y' : ℝ => (y ^ 2 - 2 * y * y') + y' ^ 2 := by funext y'; ring
        have hA : Integrable (fun y' : ℝ => y ^ 2 - 2 * y * y') ν :=
          (integrable_const (y ^ 2)).sub (hid.const_mul (2 * y))
        rw [he, integral_add hA hsq,
          integral_sub (integrable_const (y ^ 2)) (hid.const_mul (2 * y)), integral_const,
          integral_const_mul]
        simp only [smul_eq_mul, probReal_univ, one_mul]
      have hhead2 : ∫ y, (g y - EG) ^ 2 ∂ν ≤ ∫ y, (∫ y', S y y' ∂ν) ∂ν :=
        integral_mono (hgsq EG) hheadint hhead1
      have hswap : ∀ y : ℝ, ∫ y', S y y' ∂ν
          = ∫ η, H 0 (Fin.cons y η) ∂(Measure.pi fun _ : Fin N => ν) := by
        intro y
        have hunc : Measurable (Function.uncurry
            fun (y' : ℝ) (η : Fin N → ℝ) => (G (Fin.cons y η) - G (Fin.cons y' η)) ^ 2) := by
          have h1 : Measurable fun q : ℝ × (Fin N → ℝ) => G (Fin.cons y q.2) :=
            hGm.comp ((measurable_cons y).comp measurable_snd)
          have h2 : Measurable fun q : ℝ × (Fin N → ℝ) => G (Fin.cons q.1 q.2) :=
            hGm.comp measurable_cons_pair
          exact (h1.sub h2).pow_const 2
        have hsw := integral_swap_bounded ν (Measure.pi fun _ : Fin N => ν)
          (fun (y' : ℝ) (η : Fin N → ℝ) => (G (Fin.cons y η) - G (Fin.cons y' η)) ^ 2)
          hunc (fun y' => c 0 ^ 2 * (y - y') ^ 2) (hquadint y) (fun y' η => by
            rw [abs_of_nonneg (sq_nonneg _)]
            have h := hcons0 y y' η
            have h1 : (G (Fin.cons y η) - G (Fin.cons y' η)) ^ 2 ≤ (c 0 * |y - y'|) ^ 2 := by
              rw [← sq_abs (G (Fin.cons y η) - G (Fin.cons y' η))]
              exact pow_le_pow_left₀ (abs_nonneg _) h 2
            calc (G (Fin.cons y η) - G (Fin.cons y' η)) ^ 2 ≤ (c 0 * |y - y'|) ^ 2 := h1
              _ = c 0 ^ 2 * (y - y') ^ 2 := by rw [mul_pow, sq_abs])
        rw [show (∫ y', S y y' ∂ν)
            = ∫ y', (∫ η, (G (Fin.cons y η) - G (Fin.cons y' η)) ^ 2
              ∂(Measure.pi fun _ : Fin N => ν)) ∂ν from rfl, hsw]
        refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
        show (∫ y', (G (Fin.cons y η) - G (Fin.cons y' η)) ^ 2 ∂ν) = H 0 (Fin.cons y η)
        rw [hHdef]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y' => ?_)
        show (G (Fin.cons y η) - G (Fin.cons y' η)) ^ 2
          = (G (Fin.cons y η) - G (Function.update (Fin.cons y η) 0 y')) ^ 2
        rw [cons_update_zero]
      have hhead3 : ∫ y, (∫ y', S y y' ∂ν) ∂ν
          = ∫ ξ, H 0 ξ ∂(Measure.pi fun _ : Fin (N + 1) => ν) := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hswap), ← hHsplit 0]
      have hperY : ∀ y : ℝ, ∫ η, (G (Fin.cons y η) - EG) ^ 2
          ∂(Measure.pi fun _ : Fin N => ν) = A y + (g y - EG) ^ 2 := by
        intro y
        have hA2 : Integrable (fun η => (G (Fin.cons y η) - g y) ^ 2)
            (Measure.pi fun _ : Fin N => ν) :=
          integrable_sq_of_lip ν hsq _ (hconsm y) (fun j => c j.succ) (fun j => hc _)
            (hconsLip y) (g y)
        have hA1 : Integrable (fun η => G (Fin.cons y η) - g y)
            (Measure.pi fun _ : Fin N => ν) := (hconsint y).sub (integrable_const _)
        have hmean : ∫ η, (G (Fin.cons y η) - g y) ∂(Measure.pi fun _ : Fin N => ν) = 0 := by
          rw [integral_sub (hconsint y) (integrable_const _), integral_const]
          simp [hgdef]
        have hpt : ∀ η : Fin N → ℝ, (G (Fin.cons y η) - EG) ^ 2
            = (G (Fin.cons y η) - g y) ^ 2
              + (2 * (g y - EG)) * (G (Fin.cons y η) - g y) + (g y - EG) ^ 2 :=
          fun η => by ring
        have hB : Integrable (fun η : Fin N → ℝ =>
            (G (Fin.cons y η) - g y) ^ 2 + 2 * (g y - EG) * (G (Fin.cons y η) - g y))
            (Measure.pi fun _ : Fin N => ν) := hA2.add (hA1.const_mul (2 * (g y - EG)))
        rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
          integral_add hB (integrable_const ((g y - EG) ^ 2)),
          integral_add hA2 (hA1.const_mul (2 * (g y - EG))), integral_const_mul, hmean,
          integral_const]
        simp only [smul_eq_mul, probReal_univ, one_mul, mul_zero, add_zero]
        rfl
      have hdecomp : ∫ ξ, (G ξ - EG) ^ 2 ∂(Measure.pi fun _ : Fin (N + 1) => ν)
          = ∫ y, A y ∂ν + ∫ y, (g y - EG) ^ 2 ∂ν := by
        rw [integral_pi_succ ν (fun ξ => (G ξ - EG) ^ 2)
          (integrable_sq_of_lip ν hsq G hGm c hc hLip EG),
          integral_congr_ae (Filter.Eventually.of_forall hperY),
          integral_add hAint (hgsq EG)]
      rw [hdecomp]
      have hh0 : ∫ y, (g y - EG) ^ 2 ∂ν
          ≤ ∫ ξ, H 0 ξ ∂(Measure.pi fun _ : Fin (N + 1) => ν) := by
        rw [← hhead3]
        exact hhead2
      have hfinal : ∫ y, A y ∂ν + ∫ y, (g y - EG) ^ 2 ∂ν
          ≤ (∑ j : Fin N, ∫ ξ, H j.succ ξ ∂(Measure.pi fun _ : Fin (N + 1) => ν))
            + ∫ ξ, H 0 ξ ∂(Measure.pi fun _ : Fin (N + 1) => ν) := by
        linarith [hAsum, hh0]
      refine le_trans hfinal (le_of_eq ?_)
      rw [Fin.sum_univ_succ]
      ring

end LatticeProb
