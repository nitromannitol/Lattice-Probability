/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Section2.Lemma23Aux at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Lemma23
import LatticeProb.Bonanno.LQGDimension.Gaussian.Basic
import LatticeProb.Bonanno.LQGDimension.Gaussian.MaxInequality
import LatticeProb.Bonanno.LQGDimension.Section2.ZCovPSD
import LatticeProb.Bonanno.LQGDimension.Section2.SubadditiveAux
import Mathlib.Algebra.Order.Chebyshev

/-!
# Auxiliary lemmas for Lemma 2.3

* Finite suprema `⨆ i : F, g i` over a `Finset` (real valued).
* Gaussian estimates derived from `Blueprint.MaxConcentration`:
  - `integral_max_sub_zero_le`: `E (max_F ⟪v i, x⟫ - s)⁺ ≤ exp (E max - s + π²σ²/8)`;
  - `integral_fsup_fsup_le`: for a finite family of maxima `X_c` of Gaussian families with
    variance parameter `σ²` and means at most `B`,
    `E max_c X_c ≤ log (#cells) / t + B + π² t σ² / 8`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension.L23

/-! ## Finite suprema -/

section FSup

variable {ι : Type*}

lemma le_fsup {F : Finset ι} (g : ι → ℝ) {i : ι} (hi : i ∈ F) : g i ≤ ⨆ j : F, g j :=
  le_ciSup (f := fun j : F => g j) (Set.finite_range _).bddAbove ⟨i, hi⟩

lemma fsup_le {F : Finset ι} {g : ι → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i ∈ F, g i ≤ c) :
    ⨆ j : F, g j ≤ c :=
  Real.iSup_le (fun j => h j j.2) hc

lemma fsup_le' {F : Finset ι} (hF : F.Nonempty) {g : ι → ℝ} {c : ℝ} (h : ∀ i ∈ F, g i ≤ c) :
    ⨆ j : F, g j ≤ c := by
  have : Nonempty F := hF.to_subtype
  exact ciSup_le fun j => h j j.2

lemma fsup_empty (g : ι → ℝ) : ⨆ j : (∅ : Finset ι), g j = 0 := by
  have : IsEmpty (∅ : Finset ι) := ⟨fun j => Finset.notMem_empty _ j.2⟩
  exact Real.iSup_of_isEmpty _

lemma exists_eq_fsup {F : Finset ι} (hF : F.Nonempty) (g : ι → ℝ) :
    ∃ i ∈ F, ⨆ j : F, g j = g i := by
  have : Nonempty F := hF.to_subtype
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun j : F => g j)
  exact ⟨j, j.2, hj.symm⟩

lemma fsup_image {κ : Type*} [DecidableEq κ] (F : Finset ι) (φ : ι → κ) (g : κ → ℝ) :
    ⨆ k : F.image φ, g k = ⨆ j : F, g (φ j) := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · rw [Finset.image_empty, fsup_empty, fsup_empty (fun j => g (φ j))]
  · apply le_antisymm
    · apply fsup_le' (hF.image φ)
      intro k hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hk
      exact le_fsup (fun j => g (φ j)) hj
    · apply fsup_le' hF (g := fun j => g (φ j))
      intro j hj
      exact le_fsup g (Finset.mem_image_of_mem φ hj)

lemma integrable_fsup {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (F : Finset ι)
    (g : ι → Ω → ℝ) (hg : ∀ i ∈ F, Integrable (g i) μ) :
    Integrable (fun x => ⨆ i : F, g i x) μ := by
  refine Integrable.mono' (integrable_finsetSum F fun i hi => (hg i hi).abs) ?_ ?_
  · exact (AEMeasurable.iSup fun i : F => (hg i i.2).aemeasurable).aestronglyMeasurable
  · filter_upwards with x
    rcases F.eq_empty_or_nonempty with rfl | hF
    · rw [fsup_empty (fun i => g i x)]
      simp
    · obtain ⟨j, hj, hjeq⟩ := exists_eq_fsup hF (fun i => g i x)
      rw [hjeq, Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun i => |g i x|) (fun i _ => abs_nonneg _) hj

end FSup

/-! ## Gaussian estimates -/

section Gauss

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
lemma measurable_fsup_inner (F : Finset ι) (v : ι → E) (b : ι → ℝ) :
    Measurable fun x : E => ⨆ i : F, ⟪v i, x⟫ + b i :=
  Measurable.iSup fun i => by fun_prop

/-- `exp (t (max_F (⟪v i, x⟫ + b i) - c))` is integrable for `t ≥ 0`. -/
lemma integrable_exp_mul_fsup (F : Finset ι) (v : ι → E) (b : ι → ℝ) {t : ℝ} (_ht : 0 ≤ t)
    (c : ℝ) :
    Integrable (fun x => Real.exp (t * ((⨆ i : F, ⟪v i, x⟫ + b i) - c))) (stdGaussian E) := by
  have hint : ∀ i, Integrable
      (fun x : E => Real.exp (t * (b i - c)) * Real.exp (t * ⟪v i, x⟫)) (stdGaussian E) :=
    fun i => (GaussianMax.integrable_exp_mul_inner (v i) t).const_mul _
  refine Integrable.mono' ((integrable_const (Real.exp (t * (0 - c)))).add
    (integrable_finsetSum F fun i _ => hint i)) ?_ ?_
  · exact (((measurable_fsup_inner F v b).sub_const c).const_mul t).exp.aestronglyMeasurable
  · filter_upwards with x
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hnn : 0 ≤ ∑ i ∈ F, Real.exp (t * (b i - c)) * Real.exp (t * ⟪v i, x⟫) :=
      Finset.sum_nonneg fun i _ => by positivity
    rcases F.eq_empty_or_nonempty with rfl | hF
    · rw [fsup_empty (fun i => ⟪v i, x⟫ + b i)]
      simp
    · obtain ⟨j, hj, hjeq⟩ := exists_eq_fsup hF (fun i => ⟪v i, x⟫ + b i)
      rw [hjeq]
      have h1 : Real.exp (t * (⟪v j, x⟫ + b j - c)) =
          Real.exp (t * (b j - c)) * Real.exp (t * ⟪v j, x⟫) := by
        rw [← Real.exp_add]
        ring_nf
      rw [h1]
      have h2 := Finset.single_le_sum
        (f := fun i => Real.exp (t * (b i - c)) * Real.exp (t * ⟪v i, x⟫))
        (fun i _ => by positivity) hj
      have h3 := Real.exp_pos (t * (0 - c))
      linarith

lemma integrable_fsup_inner (F : Finset ι) (v : ι → E) :
    Integrable (fun x => ⨆ i : F, ⟪v i, x⟫) (stdGaussian E) := by
  have := integrable_iSup_inner_add F v (fun _ => 0)
  simpa only [add_zero] using this

end Gauss

section GaussConc

variable {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Concentration in the form used below (drift `0`). -/
lemma integral_exp_mul_fsup_sub_le (hC : Blueprint.MaxConcentration) (F : Finset ι)
    (v : ι → E) {σ : ℝ} (hv : ∀ i ∈ F, ‖v i‖ ≤ σ) (t : ℝ) :
    ∫ x, Real.exp (t * ((⨆ i : F, ⟪v i, x⟫) - vecExpectedMax F v (fun _ => 0)))
      ∂(stdGaussian E) ≤ Real.exp (π ^ 2 / 8 * t ^ 2 * σ ^ 2) := by
  have h := hC ι E F v (fun _ => 0) σ hv t
  simpa only [add_zero] using h

/-- `E (max_F ⟪v i, x⟫ - s)⁺ ≤ exp (E max_F ⟪v i, x⟫ - s + π² σ² / 8)`. -/
lemma integral_max_sub_zero_le (hC : Blueprint.MaxConcentration) (F : Finset ι) (v : ι → E)
    {σ : ℝ} (hv : ∀ i ∈ F, ‖v i‖ ≤ σ) (s : ℝ) :
    ∫ x, max ((⨆ i : F, ⟪v i, x⟫) - s) 0 ∂(stdGaussian E) ≤
      Real.exp (vecExpectedMax F v (fun _ => 0) - s + π ^ 2 / 8 * σ ^ 2) := by
  set m := vecExpectedMax F v (fun _ => 0) with hm
  have hconc := integral_exp_mul_fsup_sub_le hC F v hv 1
  have hexpint : Integrable (fun x => Real.exp (1 * ((⨆ i : F, ⟪v i, x⟫) - m)))
      (stdGaussian E) := by
    have := integrable_exp_mul_fsup F v (fun _ => 0) zero_le_one m
    simpa only [add_zero] using this
  have hpt : ∀ x : E, max ((⨆ i : F, ⟪v i, x⟫) - s) 0 ≤
      Real.exp (m - s) * Real.exp (1 * ((⨆ i : F, ⟪v i, x⟫) - m)) := by
    intro x
    rw [← Real.exp_add]
    have : m - s + 1 * ((⨆ i : F, ⟪v i, x⟫) - m) = (⨆ i : F, ⟪v i, x⟫) - s := by ring
    rw [this]
    refine max_le ?_ (Real.exp_pos _).le
    linarith [Real.add_one_le_exp ((⨆ i : F, ⟪v i, x⟫) - s)]
  calc ∫ x, max ((⨆ i : F, ⟪v i, x⟫) - s) 0 ∂(stdGaussian E)
      ≤ ∫ x, Real.exp (m - s) * Real.exp (1 * ((⨆ i : F, ⟪v i, x⟫) - m)) ∂(stdGaussian E) :=
        integral_mono ((integrable_fsup_inner F v).sub (integrable_const s)).pos_part
          (hexpint.const_mul _) hpt
    _ = Real.exp (m - s) * ∫ x, Real.exp (1 * ((⨆ i : F, ⟪v i, x⟫) - m)) ∂(stdGaussian E) :=
        integral_const_mul _ _
    _ ≤ Real.exp (m - s) * Real.exp (π ^ 2 / 8 * 1 ^ 2 * σ ^ 2) :=
        mul_le_mul_of_nonneg_left hconc (Real.exp_pos _).le
    _ = Real.exp (m - s + π ^ 2 / 8 * σ ^ 2) := by
        rw [← Real.exp_add]
        ring_nf

/-- **Maximum over cells.**  Let `X_c = max_{f ∈ cell c} ⟪w c f, x⟫` for `c ∈ C`, with
`‖w c f‖ ≤ σ` and `E X_c ≤ B`.  Then `E max_c X_c ≤ log |C| / t + B + π² t σ² / 8` for `t > 0`. -/
lemma integral_fsup_fsup_le (hC : Blueprint.MaxConcentration) {κ : Type*} (C : Finset κ)
    (cell : κ → Finset ι) (w : κ → ι → E) {σ B t : ℝ} (ht : 0 < t) (hB0 : 0 ≤ B)
    (hw : ∀ c ∈ C, ∀ f ∈ cell c, ‖w c f‖ ≤ σ)
    (hB : ∀ c ∈ C, vecExpectedMax (cell c) (w c) (fun _ => 0) ≤ B) :
    ∫ x, (⨆ c : C, ⨆ f : cell c, ⟪w c f, x⟫) ∂(stdGaussian E) ≤
      Real.log C.card / t + B + π ^ 2 / 8 * t * σ ^ 2 := by
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · have h0 : (fun x : E => ⨆ c : (∅ : Finset κ), ⨆ f : cell c, ⟪w c f, x⟫) = fun _ => 0 := by
      funext x
      exact fsup_empty (fun c => ⨆ f : cell c, ⟪w c f, x⟫)
    rw [h0, integral_zero, Finset.card_empty, Nat.cast_zero, Real.log_zero, zero_div, zero_add]
    have : 0 ≤ π ^ 2 / 8 * t * σ ^ 2 := by positivity
    linarith
  set N : ℝ := (C.card : ℝ) with hNdef
  have hN : 0 < N := by rw [hNdef]; exact_mod_cast hCne.card_pos
  set X : κ → E → ℝ := fun c x => ⨆ f : cell c, ⟪w c f, x⟫ with hXdef
  set s : ℝ := t * B + π ^ 2 / 8 * t ^ 2 * σ ^ 2 with hsdef
  set a : ℝ := Real.log N + s with hadef
  have hpt : ∀ x, t * (⨆ c : C, X c x) ≤
      (a - 1) + Real.exp (-a) * ∑ c ∈ C, Real.exp (t * X c x) := by
    intro x
    obtain ⟨c₀, hc₀, heq⟩ := exists_eq_fsup hCne (fun c => X c x)
    rw [heq]
    have h1 := Real.add_one_le_exp (t * X c₀ x - a)
    have h2 : Real.exp (t * X c₀ x - a) = Real.exp (-a) * Real.exp (t * X c₀ x) := by
      rw [← Real.exp_add]
      ring_nf
    have h3 : Real.exp (t * X c₀ x) ≤ ∑ c ∈ C, Real.exp (t * X c x) :=
      Finset.single_le_sum (f := fun c => Real.exp (t * X c x))
        (fun c _ => (Real.exp_pos _).le) hc₀
    have h4 := mul_le_mul_of_nonneg_left h3 (Real.exp_pos (-a)).le
    linarith
  have hXint : ∀ c, Integrable (X c) (stdGaussian E) := fun c =>
    integrable_fsup_inner (cell c) (w c)
  have hEint : ∀ c, Integrable (fun x => Real.exp (t * X c x)) (stdGaussian E) := by
    intro c
    have := integrable_exp_mul_fsup (cell c) (w c) (fun _ => 0) ht.le 0
    simpa only [add_zero, sub_zero] using this
  have hEbound : ∀ c ∈ C, ∫ x, Real.exp (t * X c x) ∂(stdGaussian E) ≤ Real.exp s := by
    intro c hc
    have hconc := integral_exp_mul_fsup_sub_le hC (cell c) (w c) (hw c hc) t
    set m := vecExpectedMax (cell c) (w c) (fun _ => 0) with hm
    have e : ∀ x, Real.exp (t * X c x) = Real.exp (t * m) * Real.exp (t * (X c x - m)) := by
      intro x
      rw [← Real.exp_add]
      ring_nf
    have hmB : t * m ≤ t * B := mul_le_mul_of_nonneg_left (hB c hc) ht.le
    calc ∫ x, Real.exp (t * X c x) ∂(stdGaussian E)
        = ∫ x, Real.exp (t * m) * Real.exp (t * (X c x - m)) ∂(stdGaussian E) := by
          simp_rw [e]
      _ = Real.exp (t * m) * ∫ x, Real.exp (t * (X c x - m)) ∂(stdGaussian E) :=
          integral_const_mul _ _
      _ ≤ Real.exp (t * m) * Real.exp (π ^ 2 / 8 * t ^ 2 * σ ^ 2) :=
          mul_le_mul_of_nonneg_left hconc (Real.exp_pos _).le
      _ ≤ Real.exp (t * B) * Real.exp (π ^ 2 / 8 * t ^ 2 * σ ^ 2) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hmB) (Real.exp_pos _).le
      _ = Real.exp s := by rw [hsdef, Real.exp_add]
  have hint_main := integrable_fsup C X (fun c _ => hXint c)
  have hsumint : Integrable (fun x => ∑ c ∈ C, Real.exp (t * X c x)) (stdGaussian E) :=
    integrable_finsetSum C fun c _ => hEint c
  have hRint : Integrable (fun x => (a - 1) + Real.exp (-a) * ∑ c ∈ C, Real.exp (t * X c x))
      (stdGaussian E) := (integrable_const (a - 1)).add (hsumint.const_mul (Real.exp (-a)))
  have hLint : Integrable (fun x => t * ⨆ c : C, X c x) (stdGaussian E) :=
    hint_main.const_mul t
  have hmono := integral_mono hLint hRint hpt
  rw [integral_const_mul, integral_add (integrable_const _) (hsumint.const_mul _),
    integral_const, integral_const_mul, integral_finsetSum C fun c _ => hEint c] at hmono
  simp only [probReal_univ, one_smul] at hmono
  have hsum : ∑ c ∈ C, ∫ x, Real.exp (t * X c x) ∂(stdGaussian E) ≤ N * Real.exp s := by
    calc _ ≤ ∑ _c ∈ C, Real.exp s := Finset.sum_le_sum hEbound
      _ = N * Real.exp s := by rw [Finset.sum_const, nsmul_eq_mul]
  have hexp : Real.exp (-a) * (N * Real.exp s) = 1 := by
    rw [hadef, Real.exp_neg, Real.exp_add, Real.exp_log hN]
    field_simp
  have h5 := mul_le_mul_of_nonneg_left hsum (Real.exp_pos (-a)).le
  have h6 : t * ∫ x, (⨆ c : C, X c x) ∂(stdGaussian E) ≤ a := by linarith
  have h7 : ∫ x, (⨆ c : C, X c x) ∂(stdGaussian E) ≤ a / t := by
    rw [le_div_iff₀ ht]
    linarith
  calc ∫ x, (⨆ c : C, X c x) ∂(stdGaussian E) ≤ a / t := h7
    _ = Real.log N / t + B + π ^ 2 / 8 * t * σ ^ 2 := by
      rw [hadef, hsdef]
      field_simp
      ring

end GaussConc

/-! ## Piecewise-linear functions of `V n` -/

section Vfun

variable {n : ℕ}

lemma V_sub {f g : ℝ → ℝ} (hf : f ∈ V n) (hg : g ∈ V n) : f - g ∈ V n := by
  refine ⟨by simp [hf.1, hg.1], by simp [hf.2.1, hg.2.1],
    fun x hx => by simp [hf.2.2.1 x hx, hg.2.2.1 x hx], fun k hk => ?_⟩
  obtain ⟨α, β, h⟩ := hf.2.2.2 k hk
  obtain ⟨α', β', h'⟩ := hg.2.2.2 k hk
  exact ⟨α - α', β - β', fun x hx => by simp only [Pi.sub_apply, h x hx, h' x hx]; ring⟩

lemma zero_mem_V : (0 : ℝ → ℝ) ∈ V n :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => ⟨0, 0, fun x _ => by simp⟩⟩

/-- The zero function as an element of `V n`. -/
def zeroV (n : ℕ) : V n := ⟨0, zero_mem_V⟩

/-- `f - c` as an element of `V n`. -/
def subV (c f : V n) : V n := ⟨f.1 - c.1, V_sub f.2 c.2⟩

lemma exists_piece {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ k : ℕ, k < 16 ^ n ∧ x ∈ Icc ((k : ℝ) / 16 ^ n) (((k : ℝ) + 1) / 16 ^ n) := by
  have hN : (0 : ℝ) < 16 ^ n := by positivity
  have hx0 : 0 ≤ x := hx.1
  rcases lt_or_eq_of_le hx.2 with h1 | h1
  · have h0 : (0 : ℝ) ≤ 16 ^ n * x := by positivity
    refine ⟨⌊16 ^ n * x⌋₊, ?_, ?_, ?_⟩
    · exact (Nat.floor_lt h0).2 (by push_cast; nlinarith)
    · rw [div_le_iff₀ hN]
      have := Nat.floor_le h0
      linarith
    · rw [le_div_iff₀ hN]
      have := Nat.lt_floor_add_one (16 ^ n * x)
      linarith
  · have hc : ((16 ^ n - 1 : ℕ) : ℝ) = 16 ^ n - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]
      push_cast
      ring
    refine ⟨16 ^ n - 1, Nat.sub_lt (by positivity) one_pos, ?_, ?_⟩
    · rw [hc, h1, div_le_iff₀ hN]
      linarith
    · rw [hc, h1, le_div_iff₀ hN]
      linarith

/-- A function of `V n` bounded by `δ` at the mesh points is bounded by `δ` everywhere. -/
lemma abs_le_of_nodes {f : ℝ → ℝ} (hf : f ∈ V n) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ k : ℕ, k ≤ 16 ^ n → |f ((k : ℝ) / 16 ^ n)| ≤ δ) (x : ℝ) : |f x| ≤ δ := by
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · obtain ⟨k, hk, hxk⟩ := exists_piece (n := n) hx
    have hN : (0 : ℝ) < 16 ^ n := by positivity
    rw [Subadd.V_piece hf hk hxk]
    have h1 := h k hk.le
    have h2 := h (k + 1) hk
    push_cast at h2
    have hθ0 : 0 ≤ 16 ^ n * x - k := by
      have := hxk.1
      rw [div_le_iff₀ hN] at this
      linarith
    have hθ1 : 16 ^ n * x - k ≤ 1 := by
      have := hxk.2
      rw [le_div_iff₀ hN] at this
      linarith
    set θ := 16 ^ n * x - k
    set a := f ((k : ℝ) / 16 ^ n)
    set b := f (((k : ℝ) + 1) / 16 ^ n)
    rw [abs_le] at h1 h2 ⊢
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left h1.1 (sub_nonneg.2 hθ1),
        mul_le_mul_of_nonneg_left h2.1 hθ0]
    · nlinarith [mul_le_mul_of_nonneg_left h1.2 (sub_nonneg.2 hθ1),
        mul_le_mul_of_nonneg_left h2.2 hθ0]
  · rw [hf.2.2.1 x hx, abs_zero]
    exact hδ

/-- Two functions of `V n` agreeing at the mesh points are equal. -/
lemma V_ext_nodes {f g : ℝ → ℝ} (hf : f ∈ V n) (hg : g ∈ V n)
    (h : ∀ k : ℕ, k ≤ 16 ^ n → f ((k : ℝ) / 16 ^ n) = g ((k : ℝ) / 16 ^ n)) : f = g := by
  funext x
  have := abs_le_of_nodes (V_sub hf hg) le_rfl (fun k hk => by simp [h k hk]) x
  simp only [Pi.sub_apply, abs_nonpos_iff, sub_eq_zero] at this
  exact this

lemma node_eq_sum {f : ℝ → ℝ} (hf : f ∈ V n) (k : ℕ) :
    f ((k : ℝ) / 16 ^ n) = ∑ i ∈ Finset.range k,
      (f (((i : ℝ) + 1) / 16 ^ n) - f ((i : ℝ) / 16 ^ n)) := by
  have := Finset.sum_range_sub (fun i : ℕ => f ((i : ℝ) / 16 ^ n)) k
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div, hf.1, sub_zero] at this
  exact this.symm

/-- `f(k/16ⁿ)² ≤ 2 E(f)` (Cauchy–Schwarz). -/
lemma node_sq_le {f : ℝ → ℝ} (hf : f ∈ V n) {k : ℕ} (hk : k ≤ 16 ^ n) :
    f ((k : ℝ) / 16 ^ n) ^ 2 ≤ 2 * energy f := by
  rw [node_eq_sum hf, Subadd.V_energy hf]
  set d : ℕ → ℝ := fun i => f (((i : ℝ) + 1) / 16 ^ n) - f ((i : ℝ) / 16 ^ n) with hd
  have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.range k) (f := d)
  rw [Finset.card_range] at h1
  have h2 : ∑ i ∈ Finset.range k, d i ^ 2 ≤ ∑ i ∈ Finset.range (16 ^ n), d i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk) (fun _ _ _ => sq_nonneg _)
  have h3 : (k : ℝ) ≤ 16 ^ n := by exact_mod_cast hk
  have h4 : 0 ≤ ∑ i ∈ Finset.range k, d i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc (∑ i ∈ Finset.range k, d i) ^ 2 ≤ k * ∑ i ∈ Finset.range k, d i ^ 2 := h1
    _ ≤ 16 ^ n * ∑ i ∈ Finset.range (16 ^ n), d i ^ 2 := mul_le_mul h3 h2 h4 (by positivity)
    _ = 2 * (16 ^ n / 2 * ∑ i ∈ Finset.range (16 ^ n), d i ^ 2) := by ring

/-- A function of `V n` bounded by `δ` at the mesh points has energy at most `2 M² δ²`. -/
lemma energy_le_of_nodes {h : ℝ → ℝ} (hh : h ∈ V n) {δ : ℝ}
    (hn : ∀ k : ℕ, k ≤ 16 ^ n → |h ((k : ℝ) / 16 ^ n)| ≤ δ) :
    energy h ≤ 2 * (16 ^ n) ^ 2 * δ ^ 2 := by
  rw [Subadd.V_energy hh]
  have hterm : ∀ k ∈ Finset.range (16 ^ n),
      (h (((k : ℝ) + 1) / 16 ^ n) - h ((k : ℝ) / 16 ^ n)) ^ 2 ≤ 4 * δ ^ 2 := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have h1 := hn k hk'.le
    have h2 := hn (k + 1) hk'
    push_cast at h2
    have h3 : |h (((k : ℝ) + 1) / 16 ^ n) - h ((k : ℝ) / 16 ^ n)| ≤ 2 * δ := by
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith
    have h0 : 0 ≤ 2 * δ := le_trans (abs_nonneg _) h3
    calc _ = |h (((k : ℝ) + 1) / 16 ^ n) - h ((k : ℝ) / 16 ^ n)| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * δ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
      _ = 4 * δ ^ 2 := by ring
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  push_cast at hsum
  have hN : (0 : ℝ) ≤ 16 ^ n / 2 := by positivity
  calc _ ≤ 16 ^ n / 2 * ((16 ^ n) * (4 * δ ^ 2)) := mul_le_mul_of_nonneg_left hsum hN
    _ = _ := by ring

/-- Energy change under a perturbation of size `δ` at the mesh points. -/
lemma energy_le_of_near {f g : ℝ → ℝ} (hf : f ∈ V n) (hg : g ∈ V n) {δ : ℝ} (hδ : 0 < δ)
    (hn : ∀ k : ℕ, k ≤ 16 ^ n → |g ((k : ℝ) / 16 ^ n) - f ((k : ℝ) / 16 ^ n)| ≤ δ) :
    energy g ≤ energy f + δ * energy f + 2 * (16 ^ n) ^ 2 * (δ + δ ^ 2) := by
  rw [Subadd.V_energy hf, Subadd.V_energy hg]
  have hterm : ∀ k ∈ Finset.range (16 ^ n),
      (g (((k : ℝ) + 1) / 16 ^ n) - g ((k : ℝ) / 16 ^ n)) ^ 2 ≤
        (1 + δ) * (f (((k : ℝ) + 1) / 16 ^ n) - f ((k : ℝ) / 16 ^ n)) ^ 2 +
          4 * (δ + δ ^ 2) := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have h1 := hn k hk'.le
    have h2 := hn (k + 1) hk'
    push_cast at h2
    set a := f (((k : ℝ) + 1) / 16 ^ n) - f ((k : ℝ) / 16 ^ n) with ha
    set d := (g (((k : ℝ) + 1) / 16 ^ n) - f (((k : ℝ) + 1) / 16 ^ n)) -
      (g ((k : ℝ) / 16 ^ n) - f ((k : ℝ) / 16 ^ n)) with hd
    have hdb : |d| ≤ 2 * δ := by
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith
    have hga : g (((k : ℝ) + 1) / 16 ^ n) - g ((k : ℝ) / 16 ^ n) = a + d := by
      rw [ha, hd]
      ring
    rw [hga]
    have hd2 : d ^ 2 ≤ 4 * δ ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg d) hdb 2
      rw [sq_abs] at this
      nlinarith
    have hamgm : 2 * a * d ≤ δ * a ^ 2 + d ^ 2 / δ := by
      have h0 : 0 ≤ (δ * a - d) ^ 2 / δ := by positivity
      have e : (δ * a - d) ^ 2 / δ = δ * a ^ 2 - 2 * a * d + d ^ 2 / δ := by
        field_simp
        ring
      linarith
    have hd3 : d ^ 2 / δ ≤ 4 * δ := by
      rw [div_le_iff₀ hδ]
      nlinarith
    calc (a + d) ^ 2 = a ^ 2 + 2 * a * d + d ^ 2 := by ring
      _ ≤ (1 + δ) * a ^ 2 + 4 * (δ + δ ^ 2) := by nlinarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  push_cast at hsum
  have hN : (0 : ℝ) ≤ 16 ^ n / 2 := by positivity
  set S := ∑ k ∈ Finset.range (16 ^ n), (f (((k : ℝ) + 1) / 16 ^ n) - f ((k : ℝ) / 16 ^ n)) ^ 2
  calc _ ≤ 16 ^ n / 2 * ((1 + δ) * S + 16 ^ n * (4 * (δ + δ ^ 2))) :=
        mul_le_mul_of_nonneg_left hsum hN
    _ = 16 ^ n / 2 * S + δ * (16 ^ n / 2 * S) + 2 * (16 ^ n) ^ 2 * (δ + δ ^ 2) := by ring

end Vfun

/-! ## Rounding to a grid -/

section Round

variable {n : ℕ}

/-- The values of `f` inside `(0,1)` rounded to the grid `η ℤ` (and `0` elsewhere). -/
def rnd (η : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ∈ Ioo (0 : ℝ) 1 then η * round (f x / η) else 0

lemma rnd_coarse_mem (η : ℝ) (f : ℝ → ℝ) : Subadd.coarse n (rnd η f) ∈ V n := by
  refine Subadd.coarse_mem n ?_ ?_ ?_
  · simp [rnd]
  · simp [rnd]
  · intro x hx
    have : x ∉ Ioo (0 : ℝ) 1 := fun h => hx (Ioo_subset_Icc_self h)
    simp [rnd, this]

/-- The rounded function: the linear interpolation of the rounded mesh values. -/
def roundV (η : ℝ) (f : V n) : V n := ⟨Subadd.coarse n (rnd η f), rnd_coarse_mem η f⟩

lemma roundV_node (η : ℝ) (f : V n) (k : ℕ) :
    (roundV η f : ℝ → ℝ) ((k : ℝ) / 16 ^ n) = rnd η f ((k : ℝ) / 16 ^ n) :=
  Subadd.coarse_node n _ (k : ℝ) ⟨k, by simp⟩

lemma roundV_node_err {η : ℝ} (hη : 0 < η) (f : V n) {k : ℕ} (hk : k ≤ 16 ^ n) :
    |(roundV η f : ℝ → ℝ) ((k : ℝ) / 16 ^ n) - (f : ℝ → ℝ) ((k : ℝ) / 16 ^ n)| ≤ η / 2 := by
  rw [roundV_node]
  unfold rnd
  split_ifs with h
  · set y := (f : ℝ → ℝ) ((k : ℝ) / 16 ^ n)
    have hy : η * (y / η) = y := by field_simp
    have e : η * round (y / η) - y = -(η * (y / η - round (y / η))) := by
      rw [mul_sub, hy]
      ring
    rw [e, abs_neg, abs_mul, abs_of_pos hη]
    have := abs_sub_round (y / η)
    calc η * |y / η - round (y / η)| ≤ η * (1 / 2) := mul_le_mul_of_nonneg_left this hη.le
      _ = η / 2 := by ring
  · have hN : (0 : ℝ) < 16 ^ n := by positivity
    have h1 : (k : ℝ) / 16 ^ n ≤ 1 := by
      rw [div_le_one hN]
      exact_mod_cast hk
    have h2 : (k : ℝ) / 16 ^ n ≤ 0 ∨ 1 ≤ (k : ℝ) / 16 ^ n := by
      simp only [mem_Ioo, not_and_or, not_lt] at h
      exact h
    rw [Subadd.V_zero_of_le f.2 h2]
    simp only [sub_zero, abs_zero]
    positivity

lemma roundV_err {η : ℝ} (hη : 0 < η) (f : V n) (x : ℝ) :
    |(roundV η f : ℝ → ℝ) x - (f : ℝ → ℝ) x| ≤ η / 2 := by
  have := abs_le_of_nodes (V_sub (roundV η f).2 f.2) (by positivity)
    (fun k hk => roundV_node_err hη f hk) x
  simpa only [Pi.sub_apply] using this

lemma roundV_node_grid {η : ℝ} (hη : 0 < η) (f : V n) (k : ℕ) :
    (roundV η f : ℝ → ℝ) ((k : ℝ) / 16 ^ n) =
      η * round ((roundV η f : ℝ → ℝ) ((k : ℝ) / 16 ^ n) / η) := by
  rw [roundV_node]
  unfold rnd
  split_ifs
  · rw [mul_div_cancel_left₀ _ hη.ne', round_intCast]
  · simp

lemma abs_round_roundV_le {η : ℝ} (hη : 0 < η) (f : V n) {k : ℕ} (hk : k ≤ 16 ^ n) {A : ℝ}
    (hA : |(f : ℝ → ℝ) ((k : ℝ) / 16 ^ n)| ≤ A) :
    |round ((roundV η f : ℝ → ℝ) ((k : ℝ) / 16 ^ n) / η)| ≤ (⌈A / η⌉₊ : ℤ) + 1 := by
  set c := (roundV η f : ℝ → ℝ) ((k : ℝ) / 16 ^ n)
  have h1 : |c| ≤ A + η / 2 := by
    have := roundV_node_err hη f hk
    rw [abs_le] at this hA ⊢
    constructor <;> linarith
  have h2 : |c / η| ≤ A / η + 1 / 2 := by
    rw [abs_div, abs_of_pos hη, div_le_iff₀ hη]
    calc |c| ≤ A + η / 2 := h1
      _ = (A / η + 1 / 2) * η := by field_simp
  have h3 : |(round (c / η) : ℝ)| ≤ A / η + 1 := by
    have := abs_sub_round (c / η)
    rw [abs_le] at this h2 ⊢
    constructor <;> linarith
  have h4 : A / η ≤ ⌈A / η⌉₊ := Nat.le_ceil _
  have h5 : ((|round (c / η)| : ℤ) : ℝ) ≤ (((⌈A / η⌉₊ : ℤ) + 1 : ℤ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h5

end Round

/-! ## The covariance `zCov` -/

section Cov

lemma zCov_eq {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) :
    zCov f g = π * ((∫ x in (0 : ℝ)..1, |f x|) + (∫ x in (0 : ℝ)..1, |g x|) -
      ∫ x in (0 : ℝ)..1, |f x - g x|) := by
  unfold zCov
  rw [intervalIntegral.integral_sub (hf.abs.add hg.abs) (hf.sub hg).abs,
    intervalIntegral.integral_add hf.abs hg.abs]

lemma zCov_dist {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) :
    zCov f f + zCov g g - 2 * zCov f g = 2 * π * ∫ x in (0 : ℝ)..1, |f x - g x| := by
  rw [zCov_eq hf hf, zCov_eq hg hg, zCov_eq hf hg]
  simp only [sub_self, abs_zero, intervalIntegral.integral_zero]
  ring

lemma zCov_sub_sub {f g c : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) (hc : IntervalIntegrable c volume 0 1) :
    zCov (f - c) (g - c) = zCov f g - zCov f c - zCov c g + zCov c c := by
  rw [zCov_eq (f := f - c) (g := g - c) (hf.sub hc) (hg.sub hc), zCov_eq hf hg, zCov_eq hf hc, zCov_eq hc hg,
    zCov_eq hc hc]
  have e1 : (∫ x in (0 : ℝ)..1, |(f - c) x - (g - c) x|) = ∫ x in (0 : ℝ)..1, |f x - g x| := by
    congr 1
    funext x
    simp only [Pi.sub_apply]
    rw [show f x - c x - (g x - c x) = f x - g x by ring]
  have e2 : (∫ x in (0 : ℝ)..1, |c x - g x|) = ∫ x in (0 : ℝ)..1, |(g - c) x| := by
    congr 1
    funext x
    simp only [Pi.sub_apply]
    rw [abs_sub_comm]
  have e3 : (∫ x in (0 : ℝ)..1, |c x - c x|) = 0 := by simp
  have e4 : (∫ x in (0 : ℝ)..1, |(f - c) x|) = ∫ x in (0 : ℝ)..1, |f x - c x| := rfl
  rw [e1, e2, e3, e4]
  ring

lemma zCov_zero : zCov 0 0 = 0 := by
  simp [zCov]

end Cov

/-! ## Miscellaneous -/

section Misc

lemma energy_zero : energy 0 = 0 := by
  have h : deriv (0 : ℝ → ℝ) = 0 := by
    funext x
    exact deriv_const x 0
  simp [energy, h]

lemma gEM_empty {ι : Type*} (C : ι → ι → ℝ) (b : ι → ℝ) :
    gaussianExpectedMax (∅ : Finset ι) C b = 0 := by
  have : IsEmpty (∅ : Finset ι) := ⟨fun j => Finset.notMem_empty _ j.2⟩
  unfold gaussianExpectedMax
  rw [integral_eq_zero_of_ae]
  filter_upwards with x
  exact Real.iSup_of_isEmpty _

lemma vecExpectedMax_image {ι κ E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [DecidableEq κ] (F : Finset ι) (φ : ι → κ)
    (u : κ → E) (b : κ → ℝ) :
    vecExpectedMax (F.image φ) u b = vecExpectedMax F (fun i => u (φ i)) (fun i => b (φ i)) := by
  unfold vecExpectedMax
  congr 1
  funext x
  exact fsup_image F φ (fun k => ⟪u k, x⟫ + b k)

/-- The expected maximum of `Z` on a subfamily of a family `G` realised by Gram vectors. -/
lemma gEM_eq_vec {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ} {G F : Finset (V n)}
    (hFG : F ⊆ G) (v : V n → E) (hv : ∀ f ∈ G, ∀ g ∈ G, ⟪v f, v g⟫ = zCov f g)
    (b : V n → ℝ) :
    gaussianExpectedMax F (fun f g => zCov f g) b = vecExpectedMax F v b := by
  rw [← gaussianExpectedMax_gram_eq_vecExpectedMax]
  exact gaussianExpectedMax_congr F b fun f hf g hg => (hv f (hFG hf) g (hFG hg)).symm

lemma rpow_aux {x A : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) :
    x ^ (3 / 4 : ℝ) * (A ^ 4 * x) ^ (1 / 4 : ℝ) = A * x := by
  rw [Real.mul_rpow (by positivity) hx]
  have h1 : (A ^ 4) ^ (1 / 4 : ℝ) = A := by
    have := Real.pow_rpow_inv_natCast hA (n := 4) (by norm_num)
    convert this using 2
    norm_num
  rw [h1]
  have h2 : x ^ (3 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x := by
    rw [← Real.rpow_add' hx (by norm_num)]
    norm_num
  calc x ^ (3 / 4 : ℝ) * (A * x ^ (1 / 4 : ℝ)) = A * (x ^ (3 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) := by
        ring
    _ = A * x := by rw [h2]

/-- The energy of the shell `2^j K n ≤ E < 2^{j+1} K n` fits the ball of (2.2) of radius
`(2^j K / (4 C))⁴ n`, when `K = 8 C²`. -/
lemma shell_energy_le {CS K : ℝ} (hCS1 : 1 ≤ CS) (hK : K = 8 * CS ^ 2) (j : ℕ) {x : ℝ}
    (hx : 0 ≤ x) : 2 ^ (j + 1) * (K * x) ≤ (2 ^ j * K / (4 * CS)) ^ 4 * x := by
  have hj : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hK8 : 8 * CS ^ 2 ≤ 2 ^ j * K := by
    rw [hK]
    nlinarith [sq_nonneg CS]
  have hu0 : 0 ≤ 2 ^ j * K := by rw [hK]; positivity
  have hCS4 : CS ^ 4 ≤ CS ^ 6 := pow_le_pow_right₀ hCS1 (by norm_num)
  have hu3 : 512 * CS ^ 4 ≤ (2 ^ j * K) ^ 3 := by
    have h1 : (8 * CS ^ 2) ^ 3 ≤ (2 ^ j * K) ^ 3 := pow_le_pow_left₀ (by positivity) hK8 3
    have h2 : (8 * CS ^ 2) ^ 3 = 512 * CS ^ 6 := by ring
    linarith
  have key : 2 * (2 ^ j * K) ≤ (2 ^ j * K / (4 * CS)) ^ 4 := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    calc 2 * (2 ^ j * K) * (4 * CS) ^ 4 = (2 ^ j * K) * (512 * CS ^ 4) := by ring
      _ ≤ (2 ^ j * K) * (2 ^ j * K) ^ 3 := mul_le_mul_of_nonneg_left hu3 hu0
      _ = (2 ^ j * K) ^ 4 := by ring
  calc 2 ^ (j + 1) * (K * x) = (2 * (2 ^ j * K)) * x := by rw [pow_succ]; ring
    _ ≤ (2 ^ j * K / (4 * CS)) ^ 4 * x := mul_le_mul_of_nonneg_right key hx

/-- The variance term is dominated by a quarter of the energy level. -/
lemma var_bound {CV u : ℝ} (hCV0 : 0 ≤ CV) (hu : π ^ 4 * CV ^ 2 / 2 ≤ u) :
    π ^ 2 / 8 * (CV * Real.sqrt (2 * u)) ≤ u / 4 := by
  have hu0 : 0 ≤ u := le_trans (by positivity) hu
  have hs0 : 0 ≤ Real.sqrt (2 * u) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (2 * u) ^ 2 = 2 * u := Real.sq_sqrt (by linarith)
  have hps : π ^ 2 * CV ≤ Real.sqrt (2 * u) := by
    rw [← pow_le_pow_iff_left₀ (by positivity) hs0 two_ne_zero, hs2]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hps hs0]

lemma sum_exp_le {K : ℝ} (hK1 : 1 ≤ K) {n : ℕ} (hn14 : 14 ≤ n) (J : ℕ) :
    ∑ j ∈ Finset.range J, Real.exp (-(2 ^ j * (K * n)) / 2) ≤ 1 / 4 := by
  have hn : (14 : ℝ) ≤ n := by exact_mod_cast hn14
  have he7 : Real.exp (-7) ≤ 1 / 8 := by
    have h := Real.add_one_le_exp 7
    have hpos := Real.exp_pos 7
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ hpos (by norm_num)]
    linarith
  have hterm : ∀ j : ℕ, Real.exp (-(2 ^ j * (K * n)) / 2) ≤ 1 / 8 * (1 / 2) ^ j := by
    intro j
    have hj : (j : ℝ) + 1 ≤ 2 ^ j := by
      have : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
      exact_mod_cast this
    have hKn : (14 : ℝ) ≤ K * n := by nlinarith
    have h2 : ((j : ℝ) + 1) * 14 ≤ 2 ^ j * (K * n) :=
      mul_le_mul hj hKn (by norm_num) (by positivity)
    have h1 : -(2 ^ j * (K * n)) / 2 ≤ ((j + 1 : ℕ) : ℝ) * (-7) := by
      push_cast
      linarith
    calc Real.exp (-(2 ^ j * (K * n)) / 2) ≤ Real.exp (((j + 1 : ℕ) : ℝ) * (-7)) :=
          Real.exp_le_exp.2 h1
      _ = Real.exp (-7) ^ (j + 1) := Real.exp_nat_mul _ _
      _ ≤ (1 / 8) ^ (j + 1) := pow_le_pow_left₀ (Real.exp_pos _).le he7 _
      _ ≤ 1 / 8 * (1 / 2) ^ j := by
          rw [pow_succ']
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by norm_num) (by norm_num) j) (by norm_num)
  calc _ ≤ ∑ j ∈ Finset.range J, 1 / 8 * (1 / 2 : ℝ) ^ j := Finset.sum_le_sum fun j _ => hterm j
    _ = 1 / 8 * ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j := by rw [Finset.mul_sum]
    _ ≤ 1 / 8 * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le J) (by norm_num)
    _ = 1 / 4 := by norm_num

/-- The rounded family has at most `(2P + 1)^M` elements when the rounded mesh values are
`η m` with `|m| ≤ P`. -/
lemma card_image_roundV_le {n : ℕ} [DecidableEq (V n)] {η : ℝ} (hη : 0 < η)
    (L : Finset (V n)) (P : ℕ)
    (hP : ∀ f ∈ L, ∀ k : ℕ, k ≤ 16 ^ n →
      |round ((roundV η f : ℝ → ℝ) ((k : ℝ) / 16 ^ n) / η)| ≤ (P : ℤ)) :
    ((L.image (roundV η)).card : ℝ) ≤ (2 * (P : ℝ) + 1) ^ (16 ^ n) := by
  classical
  set C := L.image (roundV η) with hC
  let node : V n → (Fin (16 ^ n) → ℤ) := fun c k =>
    round ((c : ℝ → ℝ) (((k : ℕ) : ℝ) / 16 ^ n) / η)
  have hmaps : ∀ c ∈ C,
      node c ∈ Fintype.piFinset (fun _ : Fin (16 ^ n) => Finset.Icc (-(P : ℤ)) P) := by
    intro c hc
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hc
    rw [Fintype.mem_piFinset]
    intro k
    rw [Finset.mem_Icc, ← abs_le]
    exact hP f hf k k.2.le
  have hinj : Set.InjOn node C := by
    intro c hc c' hc' heq
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.1 hc'
    apply Subtype.ext
    apply V_ext_nodes (roundV η f).2 (roundV η f').2
    intro k hk
    rcases lt_or_eq_of_le hk with hk | rfl
    · rw [roundV_node_grid hη f k, roundV_node_grid hη f' k]
      have := congrFun heq ⟨k, hk⟩
      simp only [node] at this
      rw [this]
    · have h1 : ((16 ^ n : ℕ) : ℝ) / 16 ^ n = 1 := by
        push_cast
        exact div_self (by positivity)
      rw [h1, (roundV η f).2.2.1, (roundV η f').2.2.1]
  have hcard := Finset.card_le_card_of_injOn node (fun c hc => hmaps c hc) hinj
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Int.card_Icc] at hcard
  have e : ((P : ℤ) + 1 - -(P : ℤ)).toNat = 2 * P + 1 := by omega
  rw [e] at hcard
  exact_mod_cast hcard

end Misc

end LQGDimension.L23
