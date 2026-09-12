/-
Regular variation at infinity and Potter's bounds.

A function `f` is regularly varying at infinity with index `ρ` when
`f (λ r) / f r → λ ^ ρ` as `r → ∞`, for every `λ > 0`.  The quantitative form of that
limit used in practice is Potter's bounds: for every `δ > 0` the ratio `f s / f r` at two
large arguments is at most `(1 + δ) max ((s/r) ^ (ρ+δ)) ((s/r) ^ (ρ-δ))`.

The ratio limit alone does NOT give Potter's bounds: the passage from the limit at each
fixed `λ` to a bound uniform in the ratio is the uniform convergence theorem, which is
false for functions with no regularity (the classical statements assume measurability, the
Baire property, or monotonicity).  Here the extra hypothesis is monotonicity, which is what
a tail `t ↦ P(X > t)` and its integral have for free, and it makes the chaining elementary:
a single ratio `f (a x) / f x` is controlled uniformly in `x` by the definition, the chain
`f (a^k x) ≤ q^k f x` follows by induction, and an arbitrary ratio `s / r` is squeezed
between two consecutive powers of `a` by monotonicity.

The reference for the statement is de Haan and Ferreira, Proposition B.1.9(5).
-/
import Mathlib

open Filter Topology

namespace LatticeProb

/-- **Regular variation at infinity with index `ρ`**: the ratio limit
`f (λ r) / f r → λ ^ ρ` for every `λ > 0`. -/
def RegularlyVaryingAtTop (f : ℝ → ℝ) (ρ : ℝ) : Prop :=
  ∀ lam : ℝ, 0 < lam → Tendsto (fun r : ℝ => f (lam * r) / f r) atTop (𝓝 (lam ^ ρ))

/-- Regular variation is preserved by scaling the argument: this is what turns a statement
about `P(X > t)` into one about `P(c X > t)`. -/
theorem RegularlyVaryingAtTop.comp_const_mul {f : ℝ → ℝ} {ρ : ℝ}
    (hf : RegularlyVaryingAtTop f ρ) {a : ℝ} (ha : 0 < a) :
    RegularlyVaryingAtTop (fun t => f (a * t)) ρ := by
  intro lam hlam
  have hcomp : Tendsto (fun r : ℝ => a * r) atTop atTop :=
    Filter.Tendsto.const_mul_atTop ha tendsto_id
  have h := (hf lam hlam).comp hcomp
  refine h.congr fun r => ?_
  simp only [Function.comp_apply]
  rw [show a * (lam * r) = lam * (a * r) by ring]

/-- Regular variation is preserved by scaling the value. -/
theorem RegularlyVaryingAtTop.const_mul {f : ℝ → ℝ} {ρ : ℝ} (hf : RegularlyVaryingAtTop f ρ)
    {c : ℝ} (hc : c ≠ 0) : RegularlyVaryingAtTop (fun t => c * f t) ρ := by
  intro lam hlam
  refine (hf lam hlam).congr fun r => ?_
  rw [mul_div_mul_left _ _ hc]

/-- An antitone function that is eventually positive is positive everywhere. -/
theorem pos_of_antitone_of_eventually_pos {f : ℝ → ℝ} (hmono : Antitone f)
    (hpos : ∀ᶠ r in atTop, 0 < f r) (r : ℝ) : 0 < f r := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hpos
  have h1 : 0 < f (max r N) := hN (max r N) (le_max_right r N)
  have h2 : f (max r N) ≤ f r := hmono (le_max_left r N)
  linarith

/-- A regularly varying function is eventually nonzero: at `λ = 1` the ratio would be the
junk value `0` on a set where `f` vanishes, and the limit is `1`. -/
theorem RegularlyVaryingAtTop.eventually_ne_zero {f : ℝ → ℝ} {ρ : ℝ}
    (hf : RegularlyVaryingAtTop f ρ) : ∀ᶠ r in atTop, f r ≠ 0 := by
  have h := hf 1 one_pos
  rw [Real.one_rpow] at h
  have h2 : ∀ᶠ r : ℝ in Filter.atTop, (0 : ℝ) < f (1 * r) / f r :=
    h.eventually_const_lt (by norm_num)
  filter_upwards [h2] with r hr
  intro hfr
  rw [hfr, div_zero] at hr
  exact lt_irrefl 0 hr

/-- The chain of a one-step upper bound: if `f (a x) ≤ q f x` for every `x ≥ r₀`, then
`f (a^k x) ≤ q^k f x`. -/
theorem chain_le_of_step {f : ℝ → ℝ} {a q r₀ : ℝ} (ha : 1 ≤ a) (hq : 0 ≤ q) (hr₀ : 0 < r₀)
    (hstep : ∀ x, r₀ ≤ x → f (a * x) ≤ q * f x) (k : ℕ) :
    ∀ x, r₀ ≤ x → f (a ^ k * x) ≤ q ^ k * f x := by
  induction k with
  | zero => intro x hx; simp
  | succ k ih =>
      intro x hx
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hr₀ hx
      have hak : (1 : ℝ) ≤ a ^ k := one_le_pow₀ ha
      have hxk : r₀ ≤ a ^ k * x := le_trans hx (le_mul_of_one_le_left hx0.le hak)
      have h1 : f (a * (a ^ k * x)) ≤ q * f (a ^ k * x) := hstep _ hxk
      have h2 : f (a ^ k * x) ≤ q ^ k * f x := ih x hx
      have h3 : a ^ (k + 1) * x = a * (a ^ k * x) := by ring
      rw [h3]
      calc f (a * (a ^ k * x)) ≤ q * f (a ^ k * x) := h1
        _ ≤ q * (q ^ k * f x) := by nlinarith [h2, hq]
        _ = q ^ (k + 1) * f x := by ring

/-- The chain of a one-step lower bound: if `p f x ≤ f (a x)` for every `x ≥ r₀`, then
`p^k f x ≤ f (a^k x)`. -/
theorem le_chain_of_step {f : ℝ → ℝ} {a p r₀ : ℝ} (ha : 1 ≤ a) (hp : 0 ≤ p) (hr₀ : 0 < r₀)
    (hstep : ∀ x, r₀ ≤ x → p * f x ≤ f (a * x)) (k : ℕ) :
    ∀ x, r₀ ≤ x → p ^ k * f x ≤ f (a ^ k * x) := by
  induction k with
  | zero =>
      intro x hx
      simp
  | succ k ih =>
      intro x hx
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hr₀ hx
      have hak : (1 : ℝ) ≤ a ^ k := one_le_pow₀ ha
      have hxk : r₀ ≤ a ^ k * x := le_trans hx (le_mul_of_one_le_left hx0.le hak)
      have h1 : p * f (a ^ k * x) ≤ f (a * (a ^ k * x)) := hstep _ hxk
      have h2 : p ^ k * f x ≤ f (a ^ k * x) := ih x hx
      have h3 : a ^ (k + 1) * x = a * (a ^ k * x) := by ring
      rw [h3]
      calc p ^ (k + 1) * f x = p * (p ^ k * f x) := by ring
        _ ≤ p * f (a ^ k * x) := by nlinarith [h2, hp]
        _ ≤ f (a * (a ^ k * x)) := h1

/-- Every `L ≥ 1` lies between two consecutive powers of a base `a > 1`. -/
theorem exists_bracket_rpow {a L : ℝ} (ha : 1 < a) (hL : 1 ≤ L) :
    ∃ k : ℕ, a ^ (k : ℝ) ≤ L ∧ L ≤ a ^ ((k : ℝ) + 1) := by
  have ha0 : (0 : ℝ) < a := lt_trans one_pos ha
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlL : 0 ≤ Real.log L := Real.log_nonneg hL
  set t : ℝ := Real.log L / Real.log a with ht
  have ht0 : 0 ≤ t := div_nonneg hlL hla.le
  refine ⟨⌊t⌋₊, ?_, ?_⟩
  · have hk : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
    have h1 : Real.log a * (⌊t⌋₊ : ℝ) ≤ Real.log L := by
      have h2 := mul_le_mul_of_nonneg_left hk hla.le
      rw [ht] at h2
      field_simp at h2
      exact h2
    rw [Real.rpow_def_of_pos ha0]
    calc Real.exp (Real.log a * (⌊t⌋₊ : ℝ)) ≤ Real.exp (Real.log L) := Real.exp_le_exp.mpr h1
      _ = L := Real.exp_log hL0
  · have hk : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
    have h1 : Real.log L ≤ Real.log a * ((⌊t⌋₊ : ℝ) + 1) := by
      have h2 := mul_le_mul_of_nonneg_left hk.le hla.le
      rw [ht] at h2
      field_simp at h2
      exact h2
    rw [Real.rpow_def_of_pos ha0]
    calc L = Real.exp (Real.log L) := (Real.exp_log hL0).symm
      _ ≤ Real.exp (Real.log a * ((⌊t⌋₊ : ℝ) + 1)) := Real.exp_le_exp.mpr h1

/-- Inside such a bracket, a power of `a` is a power of `L` up to the fixed factor
`a ^ |c|`, whatever the sign of the exponent `c`. -/
theorem rpow_bracket_le {a L c : ℝ} (ha : 1 < a) (hL : 1 ≤ L) {k : ℕ}
    (h1 : a ^ (k : ℝ) ≤ L) (h2 : L ≤ a ^ ((k : ℝ) + 1)) :
    a ^ ((k : ℝ) * c) ≤ L ^ c * a ^ |c| := by
  have ha0 : (0 : ℝ) < a := lt_trans one_pos ha
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc]
    have e1 : a ^ ((k : ℝ) * c) = (a ^ (k : ℝ)) ^ c := Real.rpow_mul ha0.le _ _
    have h3 : (a ^ (k : ℝ)) ^ c ≤ L ^ c :=
      Real.rpow_le_rpow (Real.rpow_nonneg ha0.le _) h1 hc
    have h4 : (1 : ℝ) ≤ a ^ c := Real.one_le_rpow ha.le hc
    have h5 : (0 : ℝ) ≤ L ^ c := Real.rpow_nonneg hL0.le _
    rw [e1]
    nlinarith [h3, h4, h5]
  · rw [abs_of_nonpos hc]
    have e1 : (k : ℝ) * c = ((k : ℝ) + 1) * c + (-c) := by ring
    have e2 : a ^ ((k : ℝ) * c) = a ^ (((k : ℝ) + 1) * c) * a ^ (-c) := by
      rw [e1, Real.rpow_add ha0]
    have e3 : a ^ (((k : ℝ) + 1) * c) = (a ^ ((k : ℝ) + 1)) ^ c := Real.rpow_mul ha0.le _ _
    have h3 : (a ^ ((k : ℝ) + 1)) ^ c ≤ L ^ c :=
      Real.rpow_le_rpow_of_nonpos hL0 h2 hc
    have h4 : (0 : ℝ) ≤ a ^ (-c) := Real.rpow_nonneg ha0.le _
    rw [e2, e3]
    exact mul_le_mul_of_nonneg_right h3 h4

/-- The base used in Potter's bounds: `(1+δ)^(1/E)` raised to any exponent at most `E` is
at most `1 + δ`. -/
theorem rpow_base_le {δ E e : ℝ} (hδ : 0 < δ) (hE : 0 < E) (he : e ≤ E) :
    ((1 + δ) ^ (1 / E)) ^ e ≤ 1 + δ := by
  have hd : (0 : ℝ) < 1 + δ := by linarith
  have ha1 : (1 : ℝ) ≤ (1 + δ) ^ (1 / E) :=
    Real.one_le_rpow (by linarith) (by positivity)
  have h1 : ((1 + δ) ^ (1 / E)) ^ e ≤ ((1 + δ) ^ (1 / E)) ^ E :=
    Real.rpow_le_rpow_of_exponent_le ha1 he
  have h2 : ((1 + δ) ^ (1 / E)) ^ E = 1 + δ := by
    rw [← Real.rpow_mul hd.le, one_div_mul_cancel (ne_of_gt hE), Real.rpow_one]
  linarith [h1, h2.le, h2.ge]

/-- That base exceeds `1`. -/
theorem one_lt_rpow_base {δ E : ℝ} (hδ : 0 < δ) (hE : 0 < E) :
    1 < (1 + δ) ^ (1 / E) := by
  have hd : (1 : ℝ) < 1 + δ := by linarith
  have hEinv : (0 : ℝ) < 1 / E := by positivity
  exact (Real.one_lt_rpow_iff_of_pos (by linarith)).mpr (Or.inl ⟨hd, hEinv⟩)


/-- **Potter's bound at ratios `≥ 1`.**  For a monotone regularly varying `f` of index `ρ`
and every `δ > 0`, `f s / f r ≤ (1+δ) (s/r)^(ρ+δ)` at all large `r ≤ s`. -/
theorem potter_upper {f : ℝ → ℝ} {ρ : ℝ} (hf : RegularlyVaryingAtTop f ρ) (hmono : Antitone f)
    (hpos : ∀ᶠ r in atTop, 0 < f r) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r s : ℝ, r₀ ≤ r → r ≤ s →
      f s / f r ≤ (1 + δ) * (s / r) ^ (ρ + δ) := by
  have hfpos : ∀ x, 0 < f x := pos_of_antitone_of_eventually_pos hmono hpos
  set E : ℝ := 2 * |ρ| + δ + 1 with hEdef
  have hEpos : 0 < E := by rw [hEdef]; nlinarith [abs_nonneg ρ]
  set a : ℝ := (1 + δ) ^ (1 / E) with hadef
  have ha1 : 1 < a := by rw [hadef]; exact one_lt_rpow_base hδ hEpos
  have ha0 : (0 : ℝ) < a := lt_trans one_pos ha1
  set q : ℝ := a ^ (ρ + δ / 2) with hqdef
  have hqpos : 0 < q := by rw [hqdef]; exact Real.rpow_pos_of_pos ha0 _
  have hlt : a ^ ρ < q := by
    rw [hqdef]; exact Real.rpow_lt_rpow_of_exponent_lt ha1 (by linarith)
  have hstep : ∀ᶠ x in atTop, f (a * x) ≤ q * f x := by
    have h := (hf a ha0).eventually_lt_const hlt
    filter_upwards [h] with x hx
    have h2 := (div_lt_iff₀ (hfpos x)).mp hx
    linarith
  obtain ⟨r₀, hr₀pos, hr₀⟩ : ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ x, r₀ ≤ x → f (a * x) ≤ q * f x := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp hstep
    exact ⟨max N 1, lt_of_lt_of_le one_pos (le_max_right N 1),
      fun x hx => hN x (le_trans (le_max_left N 1) hx)⟩
  refine ⟨r₀, hr₀pos, fun r s hr hrs => ?_⟩
  have hr0 : 0 < r := lt_of_lt_of_le hr₀pos hr
  set L : ℝ := s / r with hLdef
  have hL1 : 1 ≤ L := by rw [hLdef]; exact (one_le_div hr0).mpr hrs
  obtain ⟨k, hk1, hk2⟩ := exists_bracket_rpow ha1 hL1
  have hak : a ^ (k : ℝ) = a ^ k := Real.rpow_natCast a k
  have hkr : a ^ k * r ≤ s := by
    rw [← hak]
    have : a ^ (k : ℝ) * r ≤ L * r := by nlinarith [hk1, hr0]
    rw [hLdef] at this
    calc a ^ (k : ℝ) * r ≤ s / r * r := this
      _ = s := by field_simp
  have h1 : f s ≤ f (a ^ k * r) := hmono hkr
  have h2 : f (a ^ k * r) ≤ q ^ k * f r :=
    chain_le_of_step ha1.le hqpos.le hr₀pos hr₀ k r hr
  have h3 : f s / f r ≤ q ^ k := by
    rw [div_le_iff₀ (hfpos r)]; linarith
  have h4 : q ^ k = a ^ ((k : ℝ) * (ρ + δ / 2)) := by
    rw [hqdef, ← Real.rpow_natCast (a ^ (ρ + δ / 2)) k, ← Real.rpow_mul ha0.le, mul_comm]
  have h5 : a ^ ((k : ℝ) * (ρ + δ / 2)) ≤ L ^ (ρ + δ / 2) * a ^ |ρ + δ / 2| :=
    rpow_bracket_le ha1 hL1 hk1 hk2
  have h6 : L ^ (ρ + δ / 2) ≤ L ^ (ρ + δ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have h7 : a ^ |ρ + δ / 2| ≤ 1 + δ := by
    rw [hadef]
    refine rpow_base_le hδ hEpos ?_
    have habs := abs_add_le ρ (δ / 2)
    rw [abs_of_pos (show (0 : ℝ) < δ / 2 by linarith)] at habs
    rw [hEdef]
    nlinarith [abs_nonneg ρ]
  have h8 : (0 : ℝ) ≤ L ^ (ρ + δ / 2) := Real.rpow_nonneg (by linarith) _
  have h9 : (0 : ℝ) < a ^ |ρ + δ / 2| := Real.rpow_pos_of_pos ha0 _
  have h10 : (0 : ℝ) ≤ L ^ (ρ + δ) := Real.rpow_nonneg (by linarith) _
  calc f s / f r ≤ q ^ k := h3
    _ = a ^ ((k : ℝ) * (ρ + δ / 2)) := h4
    _ ≤ L ^ (ρ + δ / 2) * a ^ |ρ + δ / 2| := h5
    _ ≤ L ^ (ρ + δ) * (1 + δ) := by nlinarith [h6, h7, h8, h9, h10]
    _ = (1 + δ) * L ^ (ρ + δ) := by ring


/-- **Potter's bound at ratios `≤ 1`.**  For a monotone regularly varying `f` of index `ρ`
and every `δ > 0`, `f s / f r ≤ (1+δ) (s/r)^(ρ-δ)` at all large `s ≤ r`. -/
theorem potter_lower {f : ℝ → ℝ} {ρ : ℝ} (hf : RegularlyVaryingAtTop f ρ) (hmono : Antitone f)
    (hpos : ∀ᶠ r in atTop, 0 < f r) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r s : ℝ, r₀ ≤ s → s ≤ r →
      f s / f r ≤ (1 + δ) * (s / r) ^ (ρ - δ) := by
  have hfpos : ∀ x, 0 < f x := pos_of_antitone_of_eventually_pos hmono hpos
  set E : ℝ := 2 * |ρ| + δ + 1 with hEdef
  have hEpos : 0 < E := by rw [hEdef]; nlinarith [abs_nonneg ρ]
  set a : ℝ := (1 + δ) ^ (1 / E) with hadef
  have ha1 : 1 < a := by rw [hadef]; exact one_lt_rpow_base hδ hEpos
  have ha0 : (0 : ℝ) < a := lt_trans one_pos ha1
  set p : ℝ := a ^ (ρ - δ / 2) with hpdef
  have hppos : 0 < p := by rw [hpdef]; exact Real.rpow_pos_of_pos ha0 _
  have hlt : p < a ^ ρ := by
    rw [hpdef]; exact Real.rpow_lt_rpow_of_exponent_lt ha1 (by linarith)
  have hstep : ∀ᶠ x in atTop, p * f x ≤ f (a * x) := by
    have h := (hf a ha0).eventually_const_lt hlt
    filter_upwards [h] with x hx
    have h2 := (lt_div_iff₀ (hfpos x)).mp hx
    linarith
  obtain ⟨r₀, hr₀pos, hr₀⟩ : ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ x, r₀ ≤ x → p * f x ≤ f (a * x) := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp hstep
    exact ⟨max N 1, lt_of_lt_of_le one_pos (le_max_right N 1),
      fun x hx => hN x (le_trans (le_max_left N 1) hx)⟩
  refine ⟨r₀, hr₀pos, fun r s hs hsr => ?_⟩
  have hs0 : 0 < s := lt_of_lt_of_le hr₀pos hs
  have hr0 : 0 < r := lt_of_lt_of_le hs0 hsr
  set L : ℝ := r / s with hLdef
  have hL1 : 1 ≤ L := by rw [hLdef]; exact (one_le_div hs0).mpr hsr
  have hL0 : (0 : ℝ) ≤ L := by linarith
  obtain ⟨k, hk1, hk2⟩ := exists_bracket_rpow ha1 hL1
  have hak : a ^ ((k : ℝ) + 1) = a ^ (k + 1) := by
    rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hrs' : r ≤ a ^ (k + 1) * s := by
    rw [← hak]
    have hmul : L * s ≤ a ^ ((k : ℝ) + 1) * s := by nlinarith [hk2, hs0]
    rw [hLdef] at hmul
    calc r = r / s * s := by field_simp
      _ ≤ a ^ ((k : ℝ) + 1) * s := hmul
  have h1 : f (a ^ (k + 1) * s) ≤ f r := hmono hrs'
  have h2 : p ^ (k + 1) * f s ≤ f (a ^ (k + 1) * s) :=
    le_chain_of_step ha1.le hppos.le hr₀pos hr₀ (k + 1) s hs
  have hpk : (0 : ℝ) < p ^ (k + 1) := pow_pos hppos _
  have h3 : f s / f r ≤ (p ^ (k + 1))⁻¹ := by
    rw [div_le_iff₀ (hfpos r), inv_mul_eq_div, le_div_iff₀ hpk]
    nlinarith [h1, h2]
  have h4 : (p ^ (k + 1))⁻¹ = a ^ (((k : ℝ) + 1) * (δ / 2 - ρ)) := by
    rw [hpdef, ← Real.rpow_natCast (a ^ (ρ - δ / 2)) (k + 1), ← Real.rpow_mul ha0.le,
      ← Real.rpow_neg ha0.le]
    congr 1
    push_cast
    ring
  have h5 : a ^ ((k : ℝ) * (δ / 2 - ρ)) ≤ L ^ (δ / 2 - ρ) * a ^ |δ / 2 - ρ| :=
    rpow_bracket_le ha1 hL1 hk1 hk2
  have hsplit : a ^ (((k : ℝ) + 1) * (δ / 2 - ρ))
      = a ^ ((k : ℝ) * (δ / 2 - ρ)) * a ^ (δ / 2 - ρ) := by
    rw [← Real.rpow_add ha0]; congr 1; ring
  have h6 : L ^ (δ / 2 - ρ) ≤ L ^ (δ - ρ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have h7 : a ^ |δ / 2 - ρ| * a ^ (δ / 2 - ρ) ≤ 1 + δ := by
    rw [← Real.rpow_add ha0, hadef]
    refine rpow_base_le hδ hEpos ?_
    rcases le_or_gt 0 (δ / 2 - ρ) with hc | hc
    · rw [abs_of_nonneg hc, hEdef]; nlinarith [abs_nonneg ρ, neg_abs_le ρ, le_abs_self ρ]
    · rw [abs_of_neg hc, hEdef]; nlinarith [abs_nonneg ρ, neg_abs_le ρ, le_abs_self ρ]
  have h8 : (0 : ℝ) ≤ L ^ (δ / 2 - ρ) := Real.rpow_nonneg hL0 _
  have h9 : (0 : ℝ) < a ^ |δ / 2 - ρ| := Real.rpow_pos_of_pos ha0 _
  have h10 : (0 : ℝ) < a ^ (δ / 2 - ρ) := Real.rpow_pos_of_pos ha0 _
  have h11 : (0 : ℝ) ≤ L ^ (δ - ρ) := Real.rpow_nonneg hL0 _
  have hfin : (s / r) ^ (ρ - δ) = L ^ (δ - ρ) := by
    have hsr2 : s / r = L⁻¹ := by rw [hLdef, inv_div]
    rw [hsr2, Real.inv_rpow hL0, ← Real.rpow_neg hL0, neg_sub]
  rw [hfin]
  calc f s / f r ≤ (p ^ (k + 1))⁻¹ := h3
    _ = a ^ (((k : ℝ) + 1) * (δ / 2 - ρ)) := h4
    _ = a ^ ((k : ℝ) * (δ / 2 - ρ)) * a ^ (δ / 2 - ρ) := hsplit
    _ ≤ L ^ (δ / 2 - ρ) * a ^ |δ / 2 - ρ| * a ^ (δ / 2 - ρ) := by nlinarith [h5, h10]
    _ = L ^ (δ / 2 - ρ) * (a ^ |δ / 2 - ρ| * a ^ (δ / 2 - ρ)) := by ring
    _ ≤ L ^ (δ - ρ) * (1 + δ) := by nlinarith [h6, h7, h8, h9, h10, h11]
    _ = (1 + δ) * L ^ (δ - ρ) := by ring


/-- **Potter's bounds** (de Haan and Ferreira, Proposition B.1.9(5)) for a monotone
regularly varying function: for every `δ > 0` there is a level beyond which the ratio of
the function at two arguments is at most `(1+δ)` times the larger of the two powers of the
ratio of the arguments. -/
theorem potter_bounds_pos {f : ℝ → ℝ} {ρ : ℝ} (hf : RegularlyVaryingAtTop f ρ)
    (hmono : Antitone f) (hpos : ∀ᶠ r in atTop, 0 < f r) (δ : ℝ) (hδ : 0 < δ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r s : ℝ, r₀ ≤ r → r₀ ≤ s →
      f s / f r ≤ (1 + δ) * max ((s / r) ^ (ρ + δ)) ((s / r) ^ (ρ - δ)) := by
  obtain ⟨r1, hr1, h1⟩ := potter_upper hf hmono hpos hδ
  obtain ⟨r2, _, h2⟩ := potter_lower hf hmono hpos hδ
  refine ⟨max r1 r2, lt_of_lt_of_le hr1 (le_max_left _ _), fun r s hr hs => ?_⟩
  have hδ0 : (0 : ℝ) ≤ 1 + δ := by linarith
  rcases le_or_gt r s with hrs | hrs
  · refine le_trans (h1 r s (le_trans (le_max_left _ _) hr) hrs) ?_
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hδ0
  · refine le_trans (h2 r s (le_trans (le_max_right _ _) hs) hrs.le) ?_
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) hδ0

/-- **Potter's bounds**, in the shape the consumer asked for. -/
theorem potter_bounds {f : ℝ → ℝ} {ρ : ℝ} (hf : RegularlyVaryingAtTop f ρ) (hmono : Antitone f)
    (hpos : ∀ᶠ r in atTop, 0 < f r) (δ : ℝ) (hδ : 0 < δ) :
    ∃ r₀ : ℝ, ∀ r s : ℝ, r₀ ≤ r → r₀ ≤ s →
      f s / f r ≤ (1 + δ) * max ((s / r) ^ (ρ + δ)) ((s / r) ^ (ρ - δ)) := by
  obtain ⟨r₀, _, h⟩ := potter_bounds_pos hf hmono hpos δ hδ
  exact ⟨r₀, h⟩

/-- **The lower half of Potter's bounds** (de Haan and Ferreira, Proposition B.1.9(5) is
two-sided): the same comparison from below, with the minimum of the two powers. -/
theorem potter_bounds_lower {f : ℝ → ℝ} {ρ : ℝ} (hf : RegularlyVaryingAtTop f ρ)
    (hmono : Antitone f) (hpos : ∀ᶠ r in atTop, 0 < f r) (δ : ℝ) (hδ : 0 < δ) :
    ∃ r₀ : ℝ, ∀ r s : ℝ, r₀ ≤ r → r₀ ≤ s →
      (1 + δ)⁻¹ * min ((s / r) ^ (ρ + δ)) ((s / r) ^ (ρ - δ)) ≤ f s / f r := by
  have hfpos : ∀ x, 0 < f x := pos_of_antitone_of_eventually_pos hmono hpos
  obtain ⟨r₀, hr₀, hup⟩ := potter_bounds_pos hf hmono hpos δ hδ
  refine ⟨r₀, fun r s hr hs => ?_⟩
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hs0 : 0 < s := lt_of_lt_of_le hr₀ hs
  have hA : 0 < f s / f r := div_pos (hfpos s) (hfpos r)
  have hsr : (0 : ℝ) < s / r := div_pos hs0 hr0
  have hswap := hup s r hs hr
  have hinv : ∀ c : ℝ, (r / s) ^ c = ((s / r) ^ c)⁻¹ := by
    intro c
    rw [← Real.inv_rpow (le_of_lt hsr), inv_div]
  rw [hinv (ρ + δ), hinv (ρ - δ)] at hswap
  have hp1 : (0 : ℝ) < (s / r) ^ (ρ + δ) := Real.rpow_pos_of_pos hsr _
  have hp2 : (0 : ℝ) < (s / r) ^ (ρ - δ) := Real.rpow_pos_of_pos hsr _
  have hmax : max (((s / r) ^ (ρ + δ))⁻¹) (((s / r) ^ (ρ - δ))⁻¹)
      = (min ((s / r) ^ (ρ + δ)) ((s / r) ^ (ρ - δ)))⁻¹ := by
    rcases le_total ((s / r) ^ (ρ + δ)) ((s / r) ^ (ρ - δ)) with h | h
    · rw [min_eq_left h, max_eq_left (inv_anti₀ hp1 h)]
    · rw [min_eq_right h, max_eq_right (inv_anti₀ hp2 h)]
  rw [hmax] at hswap
  rw [show f r / f s = (f s / f r)⁻¹ from (inv_div (f s) (f r)).symm] at hswap
  have hfin := inv_anti₀ (inv_pos.mpr hA) hswap
  rw [inv_inv] at hfin
  calc (1 + δ)⁻¹ * min ((s / r) ^ (ρ + δ)) ((s / r) ^ (ρ - δ))
      = ((1 + δ) * (min ((s / r) ^ (ρ + δ)) ((s / r) ^ (ρ - δ)))⁻¹)⁻¹ := by
        rw [mul_inv, inv_inv]
    _ ≤ f s / f r := hfin

/-- The form of Potter's bounds used at comparable arguments: the ratio `f s / f r` is
bounded on `s / r ∈ [c, 1/c]`.  Monotonicity alone gives it, from the ratio limit at the
single value `λ = c`. -/
theorem regularlyVarying_ratio_bddAbove {f : ℝ → ℝ} {ρ c : ℝ}
    (hf : RegularlyVaryingAtTop f ρ) (hmono : Antitone f) (hpos : ∀ᶠ r in atTop, 0 < f r)
    (hc : 0 < c) :
    ∃ C r₀ : ℝ, ∀ r s : ℝ, r₀ ≤ r → c * r ≤ s → s ≤ r / c → f s / f r ≤ C := by
  have hfpos : ∀ x, 0 < f x := pos_of_antitone_of_eventually_pos hmono hpos
  have hlim := hf c hc
  have hev : ∀ᶠ r in atTop, f (c * r) / f r < c ^ ρ + 1 :=
    hlim.eventually_lt_const (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨c ^ ρ + 1, N, fun r s hr hcr _ => ?_⟩
  have h1 : f s ≤ f (c * r) := hmono hcr
  have h2 : f s / f r ≤ f (c * r) / f r := by
    exact div_le_div_of_nonneg_right h1 (hfpos r).le
  exact le_trans h2 (hN r hr).le

end LatticeProb
