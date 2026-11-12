/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Section2.LowerBound at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Section2.LowerBoundAux

/-!
# Lemma 2.2: `a_n ≥ 3 · 2^{-13/3} n`

For `b = 2^{-5/3}` and the functions `f_σ = b Σ_I σ_I ψ_I ∈ V n` of `LowerBoundAux`, we compare
the process `Z_{f_σ} - E(f_σ)` with the tree Gaussian `Y_σ = √(π b / 8) Σ_I |I| G_{I, σ|I}` by the
Sudakov–Fernique inequality, and bound `E max_σ Y_σ` from below by the greedy choice of signs
from the root to the leaves.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped Classical RealInnerProductSpace

namespace LQGDimension

namespace LowerBound22

/-! ## Coordinates of the tree Gaussian -/

/-- Coordinates `(I, w)`: an interval and a binary word of signs along its ancestry. -/
def cs (n : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((ivs n).sigma fun p => Finset.range (2 ^ (p.1 + 1))).map
    (Equiv.sigmaEquivProd (ℕ × ℕ) ℕ).toEmbedding

lemma mem_cs {n : ℕ} {c : (ℕ × ℕ) × ℕ} : c ∈ cs n ↔ c.1 ∈ ivs n ∧ c.2 < 2 ^ (c.1.1 + 1) := by
  obtain ⟨p, w⟩ := c
  simp [cs]

lemma sum_cs {M : Type*} [AddCommMonoid M] (n : ℕ) (f : (ℕ × ℕ) × ℕ → M) :
    ∑ c ∈ cs n, f c = ∑ p ∈ ivs n, ∑ w ∈ Finset.range (2 ^ (p.1 + 1)), f (p, w) := by
  rw [cs, Finset.sum_map, Finset.sum_sigma]
  rfl

/-- The (finite) coordinate type. -/
abbrev Co (n : ℕ) : Type := ↥(cs n)

/-- Reading a coordinate of `ω`, with `0` outside the coordinate set. -/
def xr {n : ℕ} (ω : Co n → ℝ) (c : (ℕ × ℕ) × ℕ) : ℝ := if h : c ∈ cs n then ω ⟨c, h⟩ else 0

lemma xr_coe {n : ℕ} (ω : Co n → ℝ) (c : Co n) : xr ω c.1 = ω c := by
  simp [xr, c.2]

lemma xr_of_mem {n : ℕ} (ω : Co n → ℝ) {c : (ℕ × ℕ) × ℕ} (h : c ∈ cs n) : xr ω c = ω ⟨c, h⟩ := by
  simp [xr, h]

/-! ## The tree vectors `y_σ` -/

/-- Coordinates of the tree vector `y_σ = A Σ_I |I| e_{I, σ|I}`. -/
def yG {n : ℕ} (A : ℝ) (σ : SA n) (c : (ℕ × ℕ) × ℕ) : ℝ :=
  if c.2 = ancW σ c.1.1 c.1.2 then A * sc c.1.1 else 0

/-- The tree vector `y_σ`. -/
def yv {n : ℕ} (A : ℝ) (σ : SA n) : EuclideanSpace ℝ (Co n) :=
  WithLp.toLp 2 (fun c : Co n => yG A σ c.1)

lemma sum_word_sq (N a a' : ℕ) (ha : a < N) (ha' : a' < N) (c : ℝ) :
    ∑ w ∈ Finset.range N, ((if w = a then c else 0) - (if w = a' then c else 0)) ^ 2 =
      if a = a' then 0 else 2 * c ^ 2 := by
  split_ifs with h
  · subst h; simp
  · have e : ∀ w, ((if w = a then c else 0) - (if w = a' then c else 0)) ^ 2 =
        (if w = a then c ^ 2 else 0) + (if w = a' then c ^ 2 else 0) := by
      intro w
      by_cases h1 : w = a
      · subst h1; simp [h]
      · by_cases h2 : w = a'
        · subst h2; simp [h1]
        · simp [h1, h2]
    rw [Finset.sum_congr rfl fun w _ => e w, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.mpr ha),
      ite_eq_left (Finset.mem_range.mpr ha')]
    ring

lemma norm_yv_sub_sq {n : ℕ} (A : ℝ) (σ τ : SA n) :
    ‖yv A σ - yv A τ‖ ^ 2 = 2 * A ^ 2 *
      ∑ q ∈ ivs n, (if ancW σ q.1 q.2 = ancW τ q.1 q.2 then 0 else sc q.1 ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [yv, WithLp.ofLp_sub, Pi.sub_apply]
  rw [Finset.sum_coe_sort (cs n) (fun c => (yG A σ c - yG A τ c) ^ 2), sum_cs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [yG]
  rw [sum_word_sq _ _ _ (ancW_lt σ q.1 q.2) (ancW_lt τ q.1 q.2)]
  split_ifs <;> ring

/-! ## The greedy choice of signs -/

/-- `1` if the first value is at least the second. -/
def pick (a b : ℝ) : ℕ := if b ≤ a then 1 else 0

lemma pick_le (a b : ℝ) : pick a b ≤ 1 := by unfold pick; split_ifs <;> norm_num

/-- The greedy word at the interval `(j, k)`: at each interval along the ancestry, the sign
with the larger of the two new standard normals is chosen. -/
def gW {n : ℕ} (ω : Co n → ℝ) : ℕ → ℕ → ℕ
  | 0, k => pick (xr ω ((0, k), 1)) (xr ω ((0, k), 0))
  | j + 1, k => 2 * gW ω j (k / 16) +
      pick (xr ω ((j + 1, k), 2 * gW ω j (k / 16) + 1)) (xr ω ((j + 1, k), 2 * gW ω j (k / 16)))

/-- The greedy word of the parent (empty word at the root). -/
def pw {n : ℕ} (ω : Co n → ℝ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | j + 1, k => gW ω j (k / 16)

lemma gW_eq {n : ℕ} (ω : Co n → ℝ) (j k : ℕ) :
    gW ω j k = 2 * pw ω j k +
      pick (xr ω ((j, k), 2 * pw ω j k + 1)) (xr ω ((j, k), 2 * pw ω j k)) := by
  cases j with
  | zero => simp [gW, pw]
  | succ j => rfl

lemma gW_lt {n : ℕ} (ω : Co n → ℝ) : ∀ j k, gW ω j k < 2 ^ (j + 1)
  | 0, k => by
    have := pick_le (xr ω ((0, k), 1)) (xr ω ((0, k), 0))
    simp only [gW, zero_add, pow_one]; omega
  | j + 1, k => by
    have ih := gW_lt ω j (k / 16)
    have := pick_le (xr ω ((j + 1, k), 2 * gW ω j (k / 16) + 1))
      (xr ω ((j + 1, k), 2 * gW ω j (k / 16)))
    simp only [gW, pow_succ 2 (j + 1)]
    generalize 2 ^ (j + 1) = N at *
    omega

lemma pw_lt {n : ℕ} (ω : Co n → ℝ) (j k : ℕ) : pw ω j k < 2 ^ j := by
  cases j with
  | zero => simp [pw]
  | succ j => exact gW_lt ω j (k / 16)

/-- The greedy sign assignment. -/
def gσ {n : ℕ} (ω : Co n → ℝ) : SA n := fun p => decide (gW ω p.1.1 p.1.2 % 2 = 1)

lemma toNat_decide_mod (m : ℕ) : (decide (m % 2 = 1)).toNat = m % 2 := by
  rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h]

lemma ancW_gσ {n : ℕ} (ω : Co n → ℝ) : ∀ j k, (j, k) ∈ ivs n → ancW (gσ ω) j k = gW ω j k
  | 0, k, h => by
    have h2 := gW_lt ω 0 k
    simp only [ancW, sv, h, dite_true, gσ, toNat_decide_mod]
    simp only [zero_add, pow_one] at h2
    omega
  | j + 1, k, h => by
    obtain ⟨h1, h2⟩ := mem_ivs.mp h
    simp only at h1 h2
    have hj : (j, k / 16) ∈ ivs n := by
      rw [mem_ivs]
      refine ⟨by simp only; omega, ?_⟩
      simp only
      rw [Nat.div_lt_iff_lt_mul (by norm_num), ← pow_succ]
      exact h2
    rw [ancW, ancW_gσ ω j (k / 16) hj]
    simp only [sv, h, dite_true, gσ, toNat_decide_mod]
    have := pick_le (xr ω ((j + 1, k), 2 * gW ω j (k / 16) + 1))
      (xr ω ((j + 1, k), 2 * gW ω j (k / 16)))
    have e : gW ω (j + 1) k = 2 * gW ω j (k / 16) +
        pick (xr ω ((j + 1, k), 2 * gW ω j (k / 16) + 1))
          (xr ω ((j + 1, k), 2 * gW ω j (k / 16))) := rfl
    rw [e]
    omega

/-- The value collected by the greedy choice at the interval `p`. -/
def Mx {n : ℕ} (ω : Co n → ℝ) (p : ℕ × ℕ) : ℝ :=
  max (xr ω (p, 2 * pw ω p.1 p.2 + 1)) (xr ω (p, 2 * pw ω p.1 p.2))

lemma xr_gW {n : ℕ} (ω : Co n → ℝ) (p : ℕ × ℕ) : xr ω (p, gW ω p.1 p.2) = Mx ω p := by
  obtain ⟨j, k⟩ := p
  rw [gW_eq]
  simp only [Mx, pick]
  split_ifs with h
  · rw [max_eq_left h]
  · rw [max_eq_right (not_le.mp h).le, add_zero]

lemma inner_yv_gσ {n : ℕ} (A : ℝ) (ω : Co n → ℝ) :
    ⟪yv A (gσ ω), WithLp.toLp 2 ω⟫ = ∑ p ∈ ivs n, A * sc p.1 * Mx ω p := by
  rw [yv, EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct, Pi.star_apply, star_trivial]
  rw [show (∑ c : Co n, ω c * yG A (gσ ω) c.1) = ∑ c : Co n, xr ω c.1 * yG A (gσ ω) c.1 from
    Finset.sum_congr rfl fun c _ => by rw [xr_coe]]
  rw [Finset.sum_coe_sort (cs n) (fun c => xr ω c * yG A (gσ ω) c), sum_cs]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp only [yG, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' (Finset.range _) (ancW (gσ ω) p.1 p.2),
    ite_eq_left (Finset.mem_range.mpr (ancW_lt _ _ _)),
    ancW_gσ ω p.1 p.2 (by rw [Prod.mk.eta]; exact hp), xr_gW]
  ring

/-! ## Measurability and locality of the greedy choice -/

lemma measurable_xr {n : ℕ} (c : (ℕ × ℕ) × ℕ) : Measurable fun ω : Co n → ℝ => xr ω c := by
  by_cases h : c ∈ cs n
  · simp only [xr, h, dite_true]; exact measurable_pi_apply _
  · simp only [xr, h, dite_false]; exact measurable_const

lemma measurable_pick {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun x => pick (f x) (g x) := by
  unfold pick
  exact Measurable.ite (measurableSet_le hg hf) measurable_const measurable_const

lemma measurable_gW {n : ℕ} (j : ℕ) : ∀ k, Measurable fun ω : Co n → ℝ => gW ω j k := by
  induction j with
  | zero => intro k; exact measurable_pick (measurable_xr _) (measurable_xr _)
  | succ j ih =>
    intro k
    have hH : Measurable fun q : (Co n → ℝ) × ℕ =>
        2 * q.2 + pick (xr q.1 ((j + 1, k), 2 * q.2 + 1)) (xr q.1 ((j + 1, k), 2 * q.2)) := by
      apply measurable_from_prod_countable_left
      intro m
      dsimp only
      exact (measurable_from_nat (f := fun t : ℕ => 2 * m + t)).comp
        (measurable_pick (measurable_xr _) (measurable_xr _))
    simp only [gW]
    exact hH.comp (measurable_id.prodMk (ih (k / 16)))

lemma measurable_pw {n : ℕ} (j k : ℕ) : Measurable fun ω : Co n → ℝ => pw ω j k := by
  cases j with
  | zero => exact measurable_const
  | succ j => exact measurable_gW j (k / 16)

lemma xr_local {n : ℕ} {ω ω' : Co n → ℝ} {j : ℕ} (h : ∀ c : Co n, c.1.1.1 ≤ j → ω c = ω' c)
    {c : (ℕ × ℕ) × ℕ} (hc : c.1.1 ≤ j) : xr ω c = xr ω' c := by
  unfold xr
  split_ifs with hm
  · exact h ⟨c, hm⟩ hc
  · rfl

lemma gW_local {n : ℕ} {ω ω' : Co n → ℝ} : ∀ j, (∀ c : Co n, c.1.1.1 ≤ j → ω c = ω' c) →
    ∀ k, gW ω j k = gW ω' j k
  | 0, h, k => by
    simp only [gW]
    rw [xr_local h (c := ((0, k), 1)) le_rfl, xr_local h (c := ((0, k), 0)) le_rfl]
  | j + 1, h, k => by
    have ih := gW_local j (fun c hc => h c (Nat.le_succ_of_le hc)) (k / 16)
    simp only [gW]
    rw [ih, xr_local h (c := ((j + 1, k), 2 * gW ω' j (k / 16) + 1)) le_rfl,
      xr_local h (c := ((j + 1, k), 2 * gW ω' j (k / 16))) le_rfl]

lemma pw_local {n : ℕ} {ω ω' : Co n → ℝ} {j : ℕ} (h : ∀ c : Co n, c.1.1.1 < j → ω c = ω' c)
    (k : ℕ) : pw ω j k = pw ω' j k := by
  cases j with
  | zero => rfl
  | succ j => exact gW_local j (fun c hc => h c (Nat.lt_succ_of_le hc)) (k / 16)

lemma Mx_eq_sum {n : ℕ} (ω : Co n → ℝ) (p : ℕ × ℕ) :
    Mx ω p = ∑ w ∈ Finset.range (2 ^ p.1),
      (if pw ω p.1 p.2 = w then (1 : ℝ) else 0) * max (xr ω (p, 2 * w + 1)) (xr ω (p, 2 * w)) := by
  rw [Finset.sum_eq_single_of_mem (pw ω p.1 p.2) (Finset.mem_range.mpr (pw_lt ω p.1 p.2))]
  · simp [Mx]
  · intro w _ hw
    rw [ite_eq_right (Ne.symm hw), zero_mul]

/-! ## Gaussian computations -/

/-- `E[Z⁺] = 1/√π` for `Z ~ N(0, 2)`. -/
lemma integral_max_zero_gaussianReal_two :
    ∫ z, max z 0 ∂(gaussianReal 0 2) = 1 / √π := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have h4 : (2 : ℝ) * π * ((2 : NNReal) : ℝ) = 4 * π := by push_cast; ring
  have e : ∀ z : ℝ, gaussianPDFReal 0 2 z • max z 0 = (Ioi (0 : ℝ)).indicator
      (fun z => (√(4 * π))⁻¹ * (z ^ (1 : ℝ) * rexp (-(1 / 4) * z ^ (2 : ℝ)))) z := by
    intro z
    have h5 : -(z - 0) ^ 2 / (2 * ((2 : NNReal) : ℝ)) = -(1 / 4) * z ^ 2 := by push_cast; ring
    simp only [gaussianPDFReal, smul_eq_mul, Set.indicator_apply, mem_Ioi]
    split_ifs with hz
    · rw [max_eq_left hz.le, Real.rpow_one, Real.rpow_two, h4, h5]; ring
    · rw [max_eq_right (not_lt.mp hz), mul_zero]
  simp_rw [e]
  rw [integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by norm_num)]
  have hs : √(4 * π) = 2 * √π := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hpi : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  rw [show (-(1 + 1) / 2 : ℝ) = -1 by norm_num, show ((1 : ℝ) + 1) / 2 = 1 by norm_num,
    Real.rpow_neg_one, Real.Gamma_one, hs]
  field_simp
  norm_num

lemma integrable_coord {ι : Type*} [Fintype ι] (a : ι) :
    Integrable (fun ω : ι → ℝ => ω a) (Measure.pi fun _ : ι => gaussianReal 0 1) :=
  integrable_eval IsGaussian.integrable_id

/-- `E max(G₁, G₂) = 1/√π` for two distinct coordinates of a standard Gaussian vector. -/
lemma integral_max_coords {ι : Type*} [Fintype ι] {a b : ι} (hab : a ≠ b) :
    ∫ ω, max (ω a) (ω b) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) = 1 / √π := by
  set μ := Measure.pi fun _ : ι => gaussianReal 0 1 with hμ
  have hind : iIndepFun (fun i (ω : ι → ℝ) => ω i) μ :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hla : HasLaw (fun ω : ι → ℝ => ω a) (gaussianReal 0 1) μ :=
    ⟨(measurable_pi_apply a).aemeasurable, (measurePreserving_eval _ a).map_eq⟩
  have hlb : HasLaw (fun ω : ι → ℝ => ω b) (gaussianReal 0 1) μ :=
    ⟨(measurable_pi_apply b).aemeasurable, (measurePreserving_eval _ b).map_eq⟩
  have hlb' : HasLaw (-fun ω : ι → ℝ => ω b) (gaussianReal 0 1) μ := by
    simpa using gaussianReal_neg hlb
  have hsum := gaussianReal_add_gaussianReal_of_indepFun ((hind.indepFun hab).neg_right) hla hlb'
  have hg : gaussianReal ((0 : ℝ) + 0) ((1 : NNReal) + 1) = gaussianReal 0 2 := by
    congr 1 <;> norm_num
  rw [hg] at hsum
  have ia := integrable_coord (ι := ι) a
  have ib := integrable_coord (ι := ι) b
  have e : ∀ ω : ι → ℝ, max (ω a) (ω b) =
      ω b + max (((fun ω : ι → ℝ => ω a) + -fun ω : ι → ℝ => ω b) ω) 0 := by
    intro ω
    simp only [Pi.add_apply, Pi.neg_apply]
    rcases le_total (ω a) (ω b) with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]; ring
    · rw [max_eq_left h, max_eq_left (by linarith)]; ring
  simp_rw [e]
  rw [integral_add ib (ia.add ib.neg).pos_part]
  have h0 : ∫ ω, ω b ∂μ = 0 := by
    have := integral_map (μ := μ) hlb.aemeasurable (f := fun x : ℝ => x)
      aestronglyMeasurable_id
    rw [hlb.map_eq, integral_id_gaussianReal] at this
    exact this.symm
  have h1 : ∫ ω, max (((fun ω : ι → ℝ => ω a) + -fun ω : ι → ℝ => ω b) ω) 0 ∂μ = 1 / √π := by
    have := integral_map (μ := μ) (φ := (fun ω : ι → ℝ => ω a) + -fun ω : ι → ℝ => ω b)
      (by fun_prop) (f := fun z : ℝ => max z 0)
      (continuous_id.max continuous_const).aestronglyMeasurable
    rw [hsum, integral_max_zero_gaussianReal_two] at this
    exact this.symm
  rw [h0, h1, zero_add]

/-! ## The expected value of the greedy choice -/

lemma integrable_xr {n : ℕ} (c : (ℕ × ℕ) × ℕ) :
    Integrable (fun ω : Co n → ℝ => xr ω c) (Measure.pi fun _ : Co n => gaussianReal 0 1) := by
  by_cases h : c ∈ cs n
  · simp only [xr, h, dite_true]; exact integrable_coord _
  · simp only [xr, h, dite_false]; exact integrable_zero _ _ _

lemma integrable_max_xr {n : ℕ} (c c' : (ℕ × ℕ) × ℕ) :
    Integrable (fun ω : Co n → ℝ => max (xr ω c) (xr ω c'))
      (Measure.pi fun _ : Co n => gaussianReal 0 1) :=
  (integrable_xr c).sup (integrable_xr c')

lemma measurable_ind {n : ℕ} (j k w : ℕ) :
    Measurable fun ω : Co n → ℝ => if pw ω j k = w then (1 : ℝ) else 0 :=
  Measurable.ite ((measurable_pw j k) (measurableSet_singleton w)) measurable_const
    measurable_const

lemma integrable_ind {n : ℕ} (j k w : ℕ) :
    Integrable (fun ω : Co n → ℝ => if pw ω j k = w then (1 : ℝ) else 0)
      (Measure.pi fun _ : Co n => gaussianReal 0 1) :=
  Integrable.of_bound (measurable_ind j k w).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => by split_ifs <;> norm_num)

lemma integrable_ind_mul_max {n : ℕ} (p : ℕ × ℕ) (w : ℕ) :
    Integrable (fun ω : Co n → ℝ => (if pw ω p.1 p.2 = w then (1 : ℝ) else 0) *
      max (xr ω (p, 2 * w + 1)) (xr ω (p, 2 * w))) (Measure.pi fun _ : Co n => gaussianReal 0 1) :=
  (integrable_max_xr _ _).bdd_mul (c := 1) (measurable_ind p.1 p.2 w).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by split_ifs <;> norm_num)

lemma integrable_Mx {n : ℕ} (p : ℕ × ℕ) :
    Integrable (fun ω : Co n → ℝ => Mx ω p) (Measure.pi fun _ : Co n => gaussianReal 0 1) := by
  simp_rw [Mx_eq_sum]
  exact integrable_finsetSum _ fun w _ => integrable_ind_mul_max p w

/-- The ancestral choice is independent of the two new normals at `p`. -/
lemma integral_ind_mul_max {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ ivs n) {w : ℕ} (hw : w < 2 ^ p.1) :
    ∫ ω, (if pw ω p.1 p.2 = w then (1 : ℝ) else 0) * max (xr ω (p, 2 * w + 1)) (xr ω (p, 2 * w))
      ∂(Measure.pi fun _ : Co n => gaussianReal 0 1) =
    (∫ ω, (if pw ω p.1 p.2 = w then (1 : ℝ) else 0)
      ∂(Measure.pi fun _ : Co n => gaussianReal 0 1)) * (1 / √π) := by
  set μ := Measure.pi fun _ : Co n => gaussianReal 0 1 with hμ
  have hc1 : (p, 2 * w + 1) ∈ cs n :=
    mem_cs.mpr ⟨hp, show 2 * w + 1 < 2 ^ (p.1 + 1) by rw [pow_succ]; omega⟩
  have hc0 : (p, 2 * w) ∈ cs n :=
    mem_cs.mpr ⟨hp, show 2 * w < 2 ^ (p.1 + 1) by rw [pow_succ]; omega⟩
  let c1 : Co n := ⟨(p, 2 * w + 1), hc1⟩
  let c0 : Co n := ⟨(p, 2 * w), hc0⟩
  have hne : c1 ≠ c0 := fun h => by
    have := congrArg (fun c : Co n => c.1.2) h
    simp [c1, c0] at this
  let S : Finset (Co n) := Finset.univ.filter fun c => c.1.1.1 < p.1
  let T : Finset (Co n) := {c1, c0}
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro c hcS hcT
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hcS
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hcT
    rcases hcT with rfl | rfl <;> simp [c1, c0] at hcS
  have hind : iIndepFun (fun c (ω : Co n → ℝ) => ω c) μ :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hST' := hind.indepFun_finset S T hST (fun c => measurable_pi_apply c)
  let ext : (S → ℝ) → (Co n → ℝ) := fun y c => if h : c ∈ S then y ⟨c, h⟩ else 0
  have hext : Measurable ext := by
    apply Measurable.of_eval
    intro c
    by_cases h : c ∈ S
    · simp only [ext, h, dite_true]; exact measurable_pi_apply _
    · simp only [ext, h, dite_false]; exact measurable_const
  let φ : (S → ℝ) → ℝ := fun y => if pw (ext y) p.1 p.2 = w then 1 else 0
  have h1T : c1 ∈ T := by simp [T]
  have h0T : c0 ∈ T := by simp [T]
  let ψ : (T → ℝ) → ℝ := fun z => max (z ⟨c1, h1T⟩) (z ⟨c0, h0T⟩)
  have hφ : Measurable φ := (measurable_ind p.1 p.2 w).comp hext
  have hψ : Measurable ψ := (measurable_pi_apply _).max (measurable_pi_apply _)
  have hloc : ∀ ω : Co n → ℝ, pw (ext fun i : S => ω i) p.1 p.2 = pw ω p.1 p.2 := fun ω =>
    pw_local (fun c hc => by
      have hcS : c ∈ S := by simp [S, hc]
      simp [ext, hcS]) p.2
  have hindep : IndepFun (fun ω : Co n → ℝ => if pw ω p.1 p.2 = w then (1 : ℝ) else 0)
      (fun ω => max (xr ω (p, 2 * w + 1)) (xr ω (p, 2 * w))) μ := by
    convert hST'.comp hφ hψ using 1
    · funext ω
      simp only [Function.comp_apply, φ, hloc]
    · funext ω
      simp only [Function.comp_apply, ψ, xr_of_mem ω hc1, xr_of_mem ω hc0, c1, c0]
  rw [hindep.integral_fun_mul_eq_mul_integral (measurable_ind p.1 p.2 w).aestronglyMeasurable
    ((measurable_xr _).max (measurable_xr _)).aestronglyMeasurable]
  congr 1
  simp only [xr_of_mem _ hc1, xr_of_mem _ hc0]
  exact integral_max_coords hne

/-- The greedy choice collects `E max(G₁, G₂) = 1/√π` at every interval. -/
lemma integral_Mx {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ ivs n) :
    ∫ ω, Mx ω p ∂(Measure.pi fun _ : Co n => gaussianReal 0 1) = 1 / √π := by
  simp_rw [Mx_eq_sum]
  rw [integral_finsetSum _ fun w _ => integrable_ind_mul_max p w,
    Finset.sum_congr rfl fun w hw => integral_ind_mul_max hp (Finset.mem_range.mp hw),
    ← Finset.sum_mul, ← integral_finsetSum _ fun w _ => integrable_ind p.1 p.2 w]
  have hsum1 : ∀ ω : Co n → ℝ,
      ∑ w ∈ Finset.range (2 ^ p.1), (if pw ω p.1 p.2 = w then (1 : ℝ) else 0) = 1 := by
    intro ω
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr (pw_lt ω p.1 p.2))]
  simp [hsum1]

lemma integral_greedy {n : ℕ} (A : ℝ) :
    ∫ ω, ∑ p ∈ ivs n, A * sc p.1 * Mx ω p ∂(Measure.pi fun _ : Co n => gaussianReal 0 1) =
      A * n / √π := by
  rw [integral_finsetSum _ fun p _ => (integrable_Mx p).const_mul _,
    Finset.sum_congr rfl (g := fun p => A * sc p.1 * (1 / √π))
      fun p hp => by rw [integral_const_mul, integral_Mx hp],
    ← Finset.sum_mul, ← Finset.mul_sum, sum_sc]
  ring

/-! ## The covariance of `Z` -/

lemma integral_abs_add_sub {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v) :
    ∫ x in (0 : ℝ)..1, (|u x| + |v x| - |u x - v x|) =
      (∫ x in (0 : ℝ)..1, |u x|) + (∫ x in (0 : ℝ)..1, |v x|) - ∫ x in (0 : ℝ)..1, |u x - v x| := by
  rw [intervalIntegral.integral_sub (f := fun x => |u x| + |v x|) (g := fun x => |u x - v x|)
      ((hu.abs.add hv.abs).intervalIntegrable 0 1) ((hu.sub hv).abs.intervalIntegrable 0 1),
    intervalIntegral.integral_add (f := fun x => |u x|) (g := fun x => |v x|)
      (hu.abs.intervalIntegrable 0 1) (hv.abs.intervalIntegrable 0 1)]

/-- `E(Z_u - Z_v)² = 2π ∫₀¹ |u - v|`. -/
lemma zCov_sub_sq {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v) :
    zCov u u - 2 * zCov u v + zCov v v = 2 * π * ∫ x in (0 : ℝ)..1, |u x - v x| := by
  unfold zCov
  rw [integral_abs_add_sub hu hu, integral_abs_add_sub hu hv, integral_abs_add_sub hv hv]
  simp only [sub_self, abs_zero, intervalIntegral.integral_zero]
  ring

lemma gEM_congr_lb22 {ι : Type*} (F : Finset ι) (C C' : ι → ι → ℝ) (b : ι → ℝ)
    (h : ∀ i ∈ F, ∀ j ∈ F, C i j = C' i j) :
    gaussianExpectedMax F C b = gaussianExpectedMax F C' b := by
  have : (Matrix.of fun i j : F => C i j) = Matrix.of fun i j : F => C' i j := by
    ext i j
    simp only [Matrix.of_apply]
    exact h _ i.2 _ j.2
  unfold gaussianExpectedMax
  rw [this]

lemma final_arith (n : ℕ) :
    √((2 : ℝ) ^ (-5 / 3 : ℝ) / 8) * n - n * ((2 : ℝ) ^ (-5 / 3 : ℝ)) ^ 2 / 2 =
      3 * (2 : ℝ) ^ (-13 / 3 : ℝ) * n := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hr : (2 : ℝ) ^ (-7 / 3 : ℝ) = 4 * (2 : ℝ) ^ (-13 / 3 : ℝ) := by
    rw [show (-7 / 3 : ℝ) = 2 + (-13 / 3) by norm_num, Real.rpow_add h2]
    norm_num
  have h8 : (2 : ℝ) ^ (-5 / 3 : ℝ) / 8 = ((2 : ℝ) ^ (-7 / 3 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2.le,
      show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num,
      ← Real.rpow_sub h2]
    norm_num
  have hb2 : ((2 : ℝ) ^ (-5 / 3 : ℝ)) ^ 2 = (2 : ℝ) ^ (-13 / 3 : ℝ) * 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2.le,
      show ((-5 / 3 : ℝ) * ((2 : ℕ) : ℝ)) = -13 / 3 + 1 by norm_num, Real.rpow_add h2,
      Real.rpow_one]
  rw [h8, Real.sqrt_sq (by positivity), hr, hb2]
  ring

end LowerBound22

/-! ## Lemma 2.2 -/

open LowerBound22 in
/-- **Lemma 2.2**: `a_n ≥ 3 · 2^{-13/3} n` for every `n`. -/
theorem aLinearLowerBound_of (hSF : Blueprint.SudakovFernique) (hGB : Blueprint.GramBridge)
    (hGR : Blueprint.GramRepresentation) (hMI : Blueprint.MaxIntegrable)
    (hPSD : Blueprint.ZCovPSD) : Blueprint.ALinearLowerBound := by
  intro n
  set b : ℝ := (2 : ℝ) ^ (-5 / 3 : ℝ) with hb
  have hb0 : 0 < b := by positivity
  set A : ℝ := √(π * b / 8) with hA
  have hA2 : 2 * A ^ 2 = π * b / 4 := by
    rw [hA, Real.sq_sqrt (by positivity)]; ring
  let fV : SA n → V n := fun σ => ⟨fS b σ, fS_mem_V b σ⟩
  -- the map `σ ↦ f_σ` is injective
  have hinj : Function.Injective fV := by
    intro σ τ h
    have h' : fS b σ = fS b τ := congrArg Subtype.val h
    have hle := tree_dist_le σ τ hb0.le
    rw [h'] at hle
    simp only [sub_self, abs_zero, intervalIntegral.integral_zero, mul_zero] at hle
    apply eq_of_ancW_eq
    intro q hq
    by_contra hne
    have hpos : 0 < ∑ q ∈ ivs n,
        (if ancW σ q.1 q.2 = ancW τ q.1 q.2 then 0 else sc q.1 ^ 2) :=
      Finset.sum_pos' (fun q _ => by split_ifs <;> positivity)
        ⟨q, hq, by rw [ite_eq_right hne]; exact pow_pos (sc_pos _) 2⟩
    have : 0 < π * b / 4 * ∑ q ∈ ivs n,
        (if ancW σ q.1 q.2 = ancW τ q.1 q.2 then 0 else sc q.1 ^ 2) :=
      mul_pos (by have := Real.pi_pos; positivity) hpos
    linarith
  let F₀ : Finset (V n) := Finset.univ.image fV
  have hmem : ∀ f ∈ F₀, ∃ σ, f = fV σ := by
    intro f hf
    obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hf
    exact ⟨σ, rfl⟩
  -- the Gram representation of the covariance of `Z` on `F₀`
  have hpsd : PSDOn F₀ (fun f g : V n => zCov f g) := by
    have h1 := hPSD (F₀.map (Function.Embedding.subtype _)) (by
      intro f hf
      obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp hf
      obtain ⟨σ, rfl⟩ := hmem g hg
      exact (continuous_fS b σ).intervalIntegrable 0 1)
    unfold PSDOn at h1 ⊢
    exact h1.submatrix (fun i : F₀ =>
      (⟨i.1.1, Finset.mem_map_of_mem _ i.2⟩ : ↥(F₀.map (Function.Embedding.subtype _))))
  obtain ⟨v, hv⟩ := hGR (V n) F₀ (fun f g => zCov f g) hpsd
  set bf : V n → ℝ := fun f => -energy f with hbf
  have hgem : gaussianExpectedMax F₀ (fun f g : V n => zCov f g) bf = vecExpectedMax F₀ v bf := by
    rw [← hGB (V n) (EuclideanSpace ℝ F₀) F₀ v bf]
    exact gEM_congr_lb22 F₀ _ _ bf (fun i hi j hj => (hv i hi j hj).symm)
  -- the tree family, indexed by `V n`
  let w : V n → EuclideanSpace ℝ (Co n) := fun f => yv A (Function.invFun fV f)
  have hw : ∀ σ, w (fV σ) = yv A σ := fun σ => by
    simp only [w]; rw [Function.leftInverse_invFun hinj σ]
  have hdist : ∀ i ∈ F₀, ∀ j ∈ F₀, ‖w i - w j‖ ≤ ‖v i - v j‖ := by
    intro i hi j hj
    obtain ⟨σ, rfl⟩ := hmem i hi
    obtain ⟨τ, rfl⟩ := hmem j hj
    rw [hw, hw, ← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero,
      norm_yv_sub_sq, hA2, norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, hv _ hi _ hi, hv _ hi _ hj, hv _ hj _ hj]
    have e : zCov (↑(fV σ)) ↑(fV σ) - 2 * zCov ↑(fV σ) ↑(fV τ) + zCov ↑(fV τ) ↑(fV τ) =
        2 * π * ∫ x in (0 : ℝ)..1, |fS b σ x - fS b τ x| :=
      zCov_sub_sq (continuous_fS b σ) (continuous_fS b τ)
    rw [e]
    exact tree_dist_le σ τ hb0.le
  have hSF' := hSF (V n) (EuclideanSpace ℝ (Co n)) (EuclideanSpace ℝ F₀) F₀ w v bf hdist
  -- the greedy lower bound for the tree family
  have hlow : A * n / √π - n * b ^ 2 / 2 ≤ vecExpectedMax F₀ w bf := by
    set μ := Measure.pi fun _ : Co n => gaussianReal 0 1 with hμ
    have hmap : μ.map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ (Co n)) :=
      map_pi_eq_stdGaussian
    have hMI' := hMI (V n) (EuclideanSpace ℝ (Co n)) F₀ w bf
    unfold vecExpectedMax
    rw [← hmap] at hMI' ⊢
    have hmeas : AEMeasurable (WithLp.toLp 2 : (Co n → ℝ) → EuclideanSpace ℝ (Co n)) μ := by
      fun_prop
    rw [integral_map hmeas hMI'.aestronglyMeasurable]
    have hint2 := (integrable_map_measure hMI'.aestronglyMeasurable hmeas).mp hMI'
    have hsumint : Integrable (fun ω : Co n → ℝ => ∑ p ∈ ivs n, A * sc p.1 * Mx ω p) μ :=
      integrable_finsetSum _ fun p _ => (integrable_Mx p).const_mul _
    calc A * n / √π - n * b ^ 2 / 2
        = ∫ ω, (∑ p ∈ ivs n, A * sc p.1 * Mx ω p - n * b ^ 2 / 2) ∂μ := by
          rw [integral_sub hsumint (integrable_const _), integral_greedy, integral_const]
          simp
      _ ≤ ∫ ω, (⨆ i : F₀, ⟪w i, WithLp.toLp 2 ω⟫ + bf i) ∂μ := by
          apply integral_mono (hsumint.sub (integrable_const _)) hint2
          intro ω
          have hi₀ : fV (gσ ω) ∈ F₀ := Finset.mem_image_of_mem _ (Finset.mem_univ _)
          refine le_trans (le_of_eq ?_)
            (le_ciSup (Set.finite_range _).bddAbove (⟨fV (gσ ω), hi₀⟩ : F₀))
          simp only [Pi.sub_apply, hw, inner_yv_gσ, hbf, fV, energy_fS]
          ring
  have hAeq : A * n / √π = √(b / 8) * n := by
    have hpi : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
    rw [hA, show π * b / 8 = π * (b / 8) by ring, Real.sqrt_mul Real.pi_pos.le]
    field_simp
  have key : 3 * (2 : ℝ) ^ (-13 / 3 : ℝ) * n ≤
      gaussianExpectedMax F₀ (fun f g : V n => zCov f g) bf := by
    rw [hgem]
    calc 3 * (2 : ℝ) ^ (-13 / 3 : ℝ) * n = √(b / 8) * n - n * b ^ 2 / 2 := (final_arith n).symm
      _ = A * n / √π - n * b ^ 2 / 2 := by rw [hAeq]
      _ ≤ vecExpectedMax F₀ w bf := hlow
      _ ≤ vecExpectedMax F₀ v bf := hSF'
  calc (((3 * (2 : ℝ) ^ (-13 / 3 : ℝ)) * n : ℝ) : EReal)
      ≤ ((gaussianExpectedMax F₀ (fun f g : V n => zCov f g) bf : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr key
    _ ≤ aE n := le_iSup (fun F : Finset (V n) =>
        ((gaussianExpectedMax F (fun f g : V n => zCov f g) (fun f => -energy f) : ℝ) : EReal)) F₀

end LQGDimension
