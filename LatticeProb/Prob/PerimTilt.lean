import Mathlib

/-!
# The tilted Cauchy-Schwarz chain for the Gaussian orthant-layer perimeter (packet Q7)

Setting: `μ = Measure.pi (fun _ : Fin m => gaussianReal 0 1)` on `Fin m → ℝ`, `h : Fin m → ℝ`,
`p_j x = max (x j - h j) 0`, `N2 x = ∑ p_j ^ 2`, `k x = #{j | h j < x j}`,
`V x = ∑ j, if h j < x j then x j * p_j x - 1 else 0`, tilt `w x = exp (-N2 x / t ^ 2)`.
Given the Stein-type second-moment bound (G3) as a hypothesis, we prove
`Psi t ≤ e ^ 2 * exp (-U) * √(min 1 Q) * √(2 Q + 2 t ^ 2 E2 + 4 E4 + 4 e E2 ^ 2)`.
-/

namespace LatticeProb

open MeasureTheory ProbabilityTheory Set Finset

/-! ### Definitions -/

/-- The positive part `max (z - c) 0` of the `c`-shifted coordinate. -/
noncomputable def perimPos (c z : ℝ) : ℝ := max (z - c) 0

/-- The one-coordinate tilt factor `exp (-p ^ 2 / t ^ 2)`. -/
noncomputable def perimWt (t c z : ℝ) : ℝ := Real.exp (-(perimPos c z ^ 2) / t ^ 2)

/-- The one-coordinate indicator of the active set `c < z`, as a real number. -/
noncomputable def perimAct (c z : ℝ) : ℝ := if c < z then 1 else 0

/-- The one-coordinate summand `g` of `V`: `z p - 1` on the active set, `0` elsewhere. -/
noncomputable def perimTG (c z : ℝ) : ℝ := if c < z then z * perimPos c z - 1 else 0

/-- `∫ w_j` (one coordinate, standard Gaussian). -/
noncomputable def perimA (t c : ℝ) : ℝ := ∫ z, perimWt t c z ∂(gaussianReal 0 1)

/-- `u_j = ∫ over act_j of (1 - w_j)`. -/
noncomputable def perimU (t c : ℝ) : ℝ := ∫ z in Ioi c, (1 - perimWt t c z) ∂(gaussianReal 0 1)

/-- `q_j = ∫ over act_j of w_j`. -/
noncomputable def perimQ (t c : ℝ) : ℝ := ∫ z in Ioi c, perimWt t c z ∂(gaussianReal 0 1)

/-- `e2_j = ∫ over act_j of (p_j / t) ^ 2 w_j`. -/
noncomputable def perimE2 (t c : ℝ) : ℝ :=
  ∫ z in Ioi c, (perimPos c z / t) ^ 2 * perimWt t c z ∂(gaussianReal 0 1)

/-- `e4_j = ∫ over act_j of (p_j / t) ^ 4 w_j`. -/
noncomputable def perimE4 (t c : ℝ) : ℝ :=
  ∫ z in Ioi c, (perimPos c z / t) ^ 4 * perimWt t c z ∂(gaussianReal 0 1)

section Vector

variable {m : ℕ}

/-- `N2 x = ∑ j, p_j x ^ 2`. -/
noncomputable def perimTN2 (h x : Fin m → ℝ) : ℝ := ∑ j, perimPos (h j) (x j) ^ 2

/-- `k x = #{j | act_j x}`, as a real number. -/
noncomputable def perimTK (h x : Fin m → ℝ) : ℝ := ((univ.filter fun j => h j < x j).card : ℝ)

/-- `V x = ∑ j, (if act_j x then x j * p_j x - 1 else 0)`. -/
noncomputable def perimTV (h x : Fin m → ℝ) : ℝ := ∑ j, perimTG (h j) (x j)

/-- The tilt `w x = exp (-N2 x / t ^ 2)`. -/
noncomputable def perimTilt (h : Fin m → ℝ) (t : ℝ) (x : Fin m → ℝ) : ℝ :=
  Real.exp (-perimTN2 h x / t ^ 2)

/-- `Psi t = ∫ over {N2 < t ^ 2} of |V|`. -/
noncomputable def perimPsi (h : Fin m → ℝ) (t : ℝ) : ℝ :=
  ∫ x in {x : Fin m → ℝ | perimTN2 h x < t ^ 2}, |perimTV h x|
    ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)

/-- `U = ∑ u_j`. -/
noncomputable def perimUsum (h : Fin m → ℝ) (t : ℝ) : ℝ := ∑ j, perimU t (h j)

/-- `Q = ∑ q_j`. -/
noncomputable def perimQsum (h : Fin m → ℝ) (t : ℝ) : ℝ := ∑ j, perimQ t (h j)

/-- `E2 = ∑ e2_j`. -/
noncomputable def perimE2sum (h : Fin m → ℝ) (t : ℝ) : ℝ := ∑ j, perimE2 t (h j)

/-- `E4 = ∑ e4_j`. -/
noncomputable def perimE4sum (h : Fin m → ℝ) (t : ℝ) : ℝ := ∑ j, perimE4 t (h j)

end Vector

/-! ### One-coordinate elementary facts -/

theorem perimPos_nonneg (c z : ℝ) : 0 ≤ perimPos c z := le_max_right _ _

theorem perimPos_of_le {c z : ℝ} (h : z ≤ c) : perimPos c z = 0 := by
  unfold perimPos; exact max_eq_right (by linarith)

theorem perimPos_of_lt {c z : ℝ} (h : c < z) : perimPos c z = z - c := by
  unfold perimPos; exact max_eq_left (by linarith)

theorem perimPos_le_abs (c z : ℝ) : perimPos c z ≤ |z| + |c| := by
  unfold perimPos
  refine max_le ?_ (by positivity)
  have := le_abs_self z
  have := neg_abs_le c
  linarith

theorem measurable_perimPos (c : ℝ) : Measurable (perimPos c) := by
  unfold perimPos; fun_prop

theorem measurable_perimWt (t c : ℝ) : Measurable (perimWt t c) := by
  unfold perimWt; have := measurable_perimPos c; fun_prop

theorem measurable_perimAct (c : ℝ) : Measurable (perimAct c) := by
  unfold perimAct
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    measurable_const

theorem measurable_perimTG (c : ℝ) : Measurable (perimTG c) := by
  unfold perimTG
  have := measurable_perimPos c
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (by fun_prop) measurable_const

theorem perimWt_pos (t c z : ℝ) : 0 < perimWt t c z := Real.exp_pos _

theorem perimWt_le_one (t c z : ℝ) : perimWt t c z ≤ 1 := by
  unfold perimWt
  rw [Real.exp_le_one_iff]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (perimPos c z)]) (sq_nonneg t)

theorem perimWt_of_le (t : ℝ) {c z : ℝ} (h : z ≤ c) : perimWt t c z = 1 := by
  unfold perimWt; rw [perimPos_of_le h]; simp

theorem perimAct_nonneg (c z : ℝ) : 0 ≤ perimAct c z := by
  unfold perimAct; split_ifs <;> norm_num

theorem perimAct_le_one (c z : ℝ) : perimAct c z ≤ 1 := by
  unfold perimAct; split_ifs <;> norm_num


/-! ### One-coordinate integrability -/

theorem integrable_perimPos_pow (c : ℝ) (n : ℕ) :
    Integrable (fun z => perimPos c z ^ n) (gaussianReal 0 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hm : MemLp (fun z : ℝ => z - c) n (gaussianReal 0 1) :=
      (memLp_id_gaussianReal' (μ := 0) (v := 1) (n : ENNReal) (ENNReal.natCast_ne_top n)).sub
        (memLp_const c)
    have hi := hm.integrable_norm_pow hn.ne'
    refine hi.mono' ((measurable_perimPos c).pow_const n).aestronglyMeasurable ?_
    filter_upwards with z
    have h0 : 0 ≤ perimPos c z ^ n := pow_nonneg (perimPos_nonneg c z) n
    rw [Real.norm_of_nonneg h0, Real.norm_eq_abs]
    refine pow_le_pow_left₀ (perimPos_nonneg c z) ?_ n
    unfold perimPos
    exact max_le (le_abs_self _) (abs_nonneg _)

theorem integrable_perimWt (t c : ℝ) : Integrable (perimWt t c) (gaussianReal 0 1) :=
  Integrable.mono' (integrable_const (1 : ℝ)) (measurable_perimWt t c).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (perimWt_pos t c z).le]; exact perimWt_le_one t c z)

theorem integrable_perimAct (c : ℝ) : Integrable (perimAct c) (gaussianReal 0 1) :=
  Integrable.mono' (integrable_const (1 : ℝ)) (measurable_perimAct c).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (perimAct_nonneg c z)]; exact perimAct_le_one c z)

theorem perimTG_sq_le (c z : ℝ) :
    perimTG c z ^ 2 ≤ 3 * (perimPos c z ^ 4 + c ^ 2 * perimPos c z ^ 2 + 1) := by
  unfold perimTG
  split_ifs with hc
  · have hp : perimPos c z = z - c := perimPos_of_lt hc
    rw [hp]
    nlinarith [sq_nonneg ((z - c) ^ 2 - c * (z - c)), sq_nonneg (c * (z - c) + 1),
      sq_nonneg ((z - c) ^ 2 + 1), sq_nonneg (z - c)]
  · have h1 := pow_nonneg (perimPos_nonneg c z) 4
    have h2 := mul_nonneg (sq_nonneg c) (sq_nonneg (perimPos c z))
    nlinarith

theorem integrable_perimTG_sq (c : ℝ) :
    Integrable (fun z => perimTG c z ^ 2) (gaussianReal 0 1) := by
  have hd : Integrable (fun z => 3 * (perimPos c z ^ 4 + c ^ 2 * perimPos c z ^ 2 + 1))
      (gaussianReal 0 1) :=
    (((integrable_perimPos_pow c 4).add ((integrable_perimPos_pow c 2).const_mul (c ^ 2))).add
      (integrable_const (1 : ℝ))).const_mul 3
  refine hd.mono' ((measurable_perimTG c).pow_const 2).aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact perimTG_sq_le c z

/-- A `perimWt`-weighted integrable function is integrable. -/
theorem integrable_mul_perimWt (t c : ℝ) {C : ℝ → ℝ} (hC : Integrable C (gaussianReal 0 1))
    (hm : Measurable C) : Integrable (fun z => C z * perimWt t c z) (gaussianReal 0 1) := by
  refine hC.norm.mono' (hm.mul (measurable_perimWt t c)).aestronglyMeasurable ?_
  filter_upwards with z
  rw [norm_mul, Real.norm_of_nonneg (perimWt_pos t c z).le]
  exact mul_le_of_le_one_right (norm_nonneg _) (perimWt_le_one t c z)


/-! ### (a) Product formulas on `Measure.pi` -/

section Prod

variable {m : ℕ}

/-- Pointwise rewriting of a marked product as a product of one-coordinate functions. -/
theorem perim_prod_marked (S : Finset (Fin m)) (C F : Fin m → ℝ → ℝ) (x : Fin m → ℝ) :
    (∏ l ∈ S, C l (x l)) * ∏ l, F l (x l) =
      ∏ l, ((if l ∈ S then C l (x l) else 1) * F l (x l)) := by
  rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]

/-- **Product formula.** The integral over `Measure.pi` of `∏_{l ∈ S} C_l(x_l) · ∏_l F_l(x_l)` is
`∏_{l ∈ S} ∫ C_l F_l · ∏_{l ∉ S} ∫ F_l`. -/
theorem perim_integral_marked (S : Finset (Fin m)) (C F : Fin m → ℝ → ℝ) :
    ∫ x, (∏ l ∈ S, C l (x l)) * ∏ l, F l (x l) ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = (∏ l ∈ S, ∫ z, C l z * F l z ∂(gaussianReal 0 1)) *
        ∏ l ∈ univ \ S, ∫ z, F l z ∂(gaussianReal 0 1) := by
  classical
  simp_rw [perim_prod_marked]
  rw [integral_fintype_prod_eq_prod (fun l z => (if l ∈ S then C l z else 1) * F l z)]
  have h1 : ∀ l : Fin m, ∫ z, (if l ∈ S then C l z else 1) * F l z ∂(gaussianReal 0 1) =
      if l ∈ S then ∫ z, C l z * F l z ∂(gaussianReal 0 1)
        else ∫ z, F l z ∂(gaussianReal 0 1) := by
    intro l
    by_cases hl : l ∈ S <;> simp [hl]
  simp_rw [h1]
  rw [← Finset.prod_sdiff (Finset.subset_univ S), mul_comm]
  congr 1
  · exact Finset.prod_congr rfl fun l hl => if_pos hl
  · exact Finset.prod_congr rfl fun l hl => if_neg (Finset.mem_sdiff.mp hl).2

/-- Integrability of a marked product. -/
theorem perim_integrable_marked (S : Finset (Fin m)) (C F : Fin m → ℝ → ℝ)
    (hC : ∀ l ∈ S, Integrable (fun z => C l z * F l z) (gaussianReal 0 1))
    (hF : ∀ l ∉ S, Integrable (F l) (gaussianReal 0 1)) :
    Integrable (fun x => (∏ l ∈ S, C l (x l)) * ∏ l, F l (x l))
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  classical
  simp_rw [perim_prod_marked]
  refine Integrable.fintype_prod (f := fun l z => (if l ∈ S then C l z else 1) * F l z) ?_
  intro l
  by_cases hl : l ∈ S
  · simpa [hl] using hC l hl
  · simpa [hl] using hF l hl

/-- Product formula with one marked coordinate. -/
theorem perim_integral_single (j : Fin m) (c : ℝ → ℝ) (F : Fin m → ℝ → ℝ) :
    ∫ x, c (x j) * ∏ l, F l (x l) ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = (∫ z, c z * F j z ∂(gaussianReal 0 1)) *
        ∏ l ∈ univ.erase j, ∫ z, F l z ∂(gaussianReal 0 1) := by
  classical
  have := perim_integral_marked {j} (fun _ => c) F
  simpa [Finset.sdiff_singleton_eq_erase] using this

/-- Integrability with one marked coordinate. -/
theorem perim_integrable_single (j : Fin m) (c : ℝ → ℝ) (F : Fin m → ℝ → ℝ)
    (hc : Integrable (fun z => c z * F j z) (gaussianReal 0 1))
    (hF : ∀ l, l ≠ j → Integrable (F l) (gaussianReal 0 1)) :
    Integrable (fun x => c (x j) * ∏ l, F l (x l))
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  classical
  have := perim_integrable_marked {j} (fun _ => c) F (by simpa using hc)
    (by intro l hl; exact hF l (by simpa using hl))
  simpa using this

/-- Product formula with two distinct marked coordinates. -/
theorem perim_integral_pair {i j : Fin m} (hij : i ≠ j) (c₁ c₂ : ℝ → ℝ) (F : Fin m → ℝ → ℝ) :
    ∫ x, c₁ (x i) * c₂ (x j) * ∏ l, F l (x l) ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = ((∫ z, c₁ z * F i z ∂(gaussianReal 0 1)) * ∫ z, c₂ z * F j z ∂(gaussianReal 0 1)) *
        ∏ l ∈ univ \ {i, j}, ∫ z, F l z ∂(gaussianReal 0 1) := by
  classical
  have := perim_integral_marked {i, j} (fun l => if l = i then c₁ else c₂) F
  simp only [Finset.prod_pair hij, if_true, if_neg hij.symm] at this
  simpa [mul_assoc] using this

/-- Integrability with two distinct marked coordinates. -/
theorem perim_integrable_pair {i j : Fin m} (hij : i ≠ j) (c₁ c₂ : ℝ → ℝ) (F : Fin m → ℝ → ℝ)
    (h1 : Integrable (fun z => c₁ z * F i z) (gaussianReal 0 1))
    (h2 : Integrable (fun z => c₂ z * F j z) (gaussianReal 0 1))
    (hF : ∀ l, l ≠ i → l ≠ j → Integrable (F l) (gaussianReal 0 1)) :
    Integrable (fun x => c₁ (x i) * c₂ (x j) * ∏ l, F l (x l))
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  classical
  have := perim_integrable_marked {i, j} (fun l => if l = i then c₁ else c₂) F
    (by
      intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl'
      · simpa using h1
      · have : l = j := Finset.mem_singleton.mp hl'
        subst this
        simpa [hij.symm] using h2)
    (by
      intro l hl
      exact hF l (fun h => hl (by simp [h])) (fun h => hl (by simp [h])))
  simp only [Finset.prod_pair hij, if_true, if_neg hij.symm] at this
  simpa [mul_assoc] using this

end Prod


/-! ### One-coordinate constants -/

theorem perimU_nonneg (t c : ℝ) : 0 ≤ perimU t c :=
  setIntegral_nonneg measurableSet_Ioi fun z _ => sub_nonneg.mpr (perimWt_le_one t c z)

theorem perimU_eq_integral (t c : ℝ) :
    perimU t c = ∫ z, (1 - perimWt t c z) ∂(gaussianReal 0 1) := by
  unfold perimU
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
  rw [perimWt_of_le t (not_lt.mp hz)]; simp

theorem perimA_eq (t c : ℝ) : perimA t c = 1 - perimU t c := by
  unfold perimA
  rw [perimU_eq_integral, integral_sub (integrable_const 1) (integrable_perimWt t c)]
  simp

theorem perimA_nonneg (t c : ℝ) : 0 ≤ perimA t c :=
  integral_nonneg fun z => (perimWt_pos t c z).le

theorem perimU_le_one (t c : ℝ) : perimU t c ≤ 1 := by
  have := perimA_nonneg t c
  rw [perimA_eq] at this
  linarith

theorem perimA_le_exp (t c : ℝ) : perimA t c ≤ Real.exp (-perimU t c) := by
  rw [perimA_eq]
  have := Real.add_one_le_exp (-perimU t c)
  linarith

theorem perimQ_nonneg (t c : ℝ) : 0 ≤ perimQ t c :=
  setIntegral_nonneg measurableSet_Ioi fun z _ => (perimWt_pos t c z).le

theorem perimE2_nonneg (t c : ℝ) : 0 ≤ perimE2 t c :=
  setIntegral_nonneg measurableSet_Ioi fun z _ =>
    mul_nonneg (sq_nonneg _) (perimWt_pos t c z).le

theorem perimE4_nonneg (t c : ℝ) : 0 ≤ perimE4 t c :=
  setIntegral_nonneg measurableSet_Ioi fun z _ =>
    mul_nonneg (by positivity) (perimWt_pos t c z).le

/-- Full-line form of `q`. -/
theorem perimQ_eq_integral (t c : ℝ) :
    ∫ z, perimAct c z * perimWt t c z ∂(gaussianReal 0 1) = perimQ t c := by
  unfold perimQ
  rw [← integral_indicator measurableSet_Ioi]
  congr 1
  ext z
  by_cases hz : c < z <;> simp [perimAct, hz, Set.indicator]

/-- Full-line form of `t ^ 2 * e2`. -/
theorem perimE2_eq_integral {t : ℝ} (ht : t ≠ 0) (c : ℝ) :
    ∫ z, perimPos c z ^ 2 * perimWt t c z ∂(gaussianReal 0 1) = t ^ 2 * perimE2 t c := by
  unfold perimE2
  rw [← integral_const_mul]
  have : ∀ z, t ^ 2 * ((perimPos c z / t) ^ 2 * perimWt t c z)
      = perimPos c z ^ 2 * perimWt t c z := by
    intro z; field_simp
  simp_rw [this]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
  rw [perimPos_of_le (not_lt.mp hz)]; simp

/-- Full-line form of `e2`. -/
theorem perimE2_eq_integral' (t c : ℝ) :
    ∫ z, (perimPos c z / t) ^ 2 * perimWt t c z ∂(gaussianReal 0 1) = perimE2 t c := by
  unfold perimE2
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
  rw [perimPos_of_le (not_lt.mp hz)]; simp

/-- Full-line form of `e4`. -/
theorem perimE4_eq_integral (t c : ℝ) :
    ∫ z, (perimPos c z / t) ^ 4 * perimWt t c z ∂(gaussianReal 0 1) = perimE4 t c := by
  unfold perimE4
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
  rw [perimPos_of_le (not_lt.mp hz)]; simp


/-! ### Vector-level elementary facts -/

section Vec

variable {m : ℕ}

theorem perimTilt_eq_prod (h : Fin m → ℝ) (t : ℝ) (x : Fin m → ℝ) :
    perimTilt h t x = ∏ l, perimWt t (h l) (x l) := by
  unfold perimTilt perimWt perimTN2
  rw [← Real.exp_sum, ← Finset.sum_div, ← Finset.sum_neg_distrib]

theorem perimTilt_pos (h : Fin m → ℝ) (t : ℝ) (x : Fin m → ℝ) : 0 < perimTilt h t x :=
  Real.exp_pos _

/-- Unfolding of `perimTN2` in plain terms (for matching with other packets' `N2`). -/
theorem perimTN2_eq (h x : Fin m → ℝ) : perimTN2 h x = ∑ j, max (x j - h j) 0 ^ 2 := rfl

/-- Unfolding of `perimTK` in plain terms. -/
theorem perimTK_eq_card (h x : Fin m → ℝ) :
    perimTK h x = ((univ.filter fun j => h j < x j).card : ℝ) := rfl

/-- Unfolding of `perimTV` in plain terms. -/
theorem perimTV_eq (h x : Fin m → ℝ) :
    perimTV h x = ∑ j, if h j < x j then x j * max (x j - h j) 0 - 1 else 0 := rfl

theorem perimTN2_nonneg (h x : Fin m → ℝ) : 0 ≤ perimTN2 h x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem perimTK_eq_sum (h x : Fin m → ℝ) : perimTK h x = ∑ j, perimAct (h j) (x j) := by
  unfold perimTK perimAct
  rw [Finset.sum_boole]

theorem perimTK_nonneg (h x : Fin m → ℝ) : 0 ≤ perimTK h x := Nat.cast_nonneg _

theorem measurable_perimTN2 (h : Fin m → ℝ) : Measurable (perimTN2 h) := by
  unfold perimTN2
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_perimPos (h j)).comp (measurable_pi_apply j)).pow_const 2

theorem measurable_perimTV (h : Fin m → ℝ) : Measurable (perimTV h) := by
  unfold perimTV
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (measurable_perimTG (h j)).comp (measurable_pi_apply j)

theorem measurable_perimTK (h : Fin m → ℝ) : Measurable (perimTK h) := by
  have : perimTK h = fun x => ∑ j, perimAct (h j) (x j) := funext (perimTK_eq_sum h)
  rw [this]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (measurable_perimAct (h j)).comp (measurable_pi_apply j)

theorem measurable_perimTilt (h : Fin m → ℝ) (t : ℝ) : Measurable (perimTilt h t) := by
  unfold perimTilt
  have := measurable_perimTN2 h
  fun_prop


/-- **Tail product bound.** Removing the factors of a finite set `S` costs at most `e ^ #S`:
`∏_{l ∉ S} a_l ≤ e ^ #S * exp (-U)`, because `a_l = 1 - u_l ≤ exp (-u_l)` and `u_l ≤ 1`. -/
theorem perim_tail_prod_le (t : ℝ) (h : Fin m → ℝ) (S : Finset (Fin m)) :
    ∏ l ∈ univ \ S, perimA t (h l) ≤ Real.exp 1 ^ S.card * Real.exp (-perimUsum h t) := by
  classical
  have h1 : ∏ l ∈ univ \ S, perimA t (h l) ≤ ∏ l ∈ univ \ S, Real.exp (-perimU t (h l)) :=
    Finset.prod_le_prod (fun l _ => perimA_nonneg t (h l)) (fun l _ => perimA_le_exp t (h l))
  rw [← Real.exp_sum] at h1
  have h2 : ∑ l ∈ univ \ S, perimU t (h l) + ∑ l ∈ S, perimU t (h l) = perimUsum h t :=
    Finset.sum_sdiff (Finset.subset_univ S)
  have h3 : ∑ l ∈ S, perimU t (h l) ≤ S.card := by
    have := Finset.sum_le_card_nsmul S (fun l => perimU t (h l)) 1
      (fun l _ => perimU_le_one t (h l))
    simpa using this
  refine h1.trans ?_
  have h4 : Real.exp 1 ^ S.card = Real.exp ((S.card : ℝ) * 1) := (Real.exp_nat_mul 1 S.card).symm
  rw [h4, ← Real.exp_add, Real.exp_le_exp, Finset.sum_neg_distrib]
  linarith

theorem perim_integral_tilt (h : Fin m → ℝ) (t : ℝ) :
    ∫ x, perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = ∏ j, perimA t (h j) := by
  simp_rw [perimTilt_eq_prod]
  exact integral_fintype_prod_eq_prod (fun l z => perimWt t (h l) z)

theorem integrable_perimTilt (h : Fin m → ℝ) (t : ℝ) :
    Integrable (perimTilt h t) (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  have : perimTilt h t = fun x => ∏ l, perimWt t (h l) (x l) := funext (perimTilt_eq_prod h t)
  rw [this]
  exact Integrable.fintype_prod (fun l => integrable_perimWt t (h l))

theorem perim_integrable_single_tilt (h : Fin m → ℝ) (t : ℝ) (j : Fin m) {c : ℝ → ℝ}
    (hc : Integrable c (gaussianReal 0 1)) (hm : Measurable c) :
    Integrable (fun x => c (x j) * perimTilt h t x)
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  have : (fun x => c (x j) * perimTilt h t x) = fun x => c (x j) * ∏ l, perimWt t (h l) (x l) :=
    funext fun x => by rw [perimTilt_eq_prod]
  rw [this]
  exact perim_integrable_single j c (fun l => perimWt t (h l))
    (integrable_mul_perimWt t (h j) hc hm) (fun l _ => integrable_perimWt t (h l))

theorem perim_integral_single_tilt (h : Fin m → ℝ) (t : ℝ) (j : Fin m) (c : ℝ → ℝ) :
    ∫ x, c (x j) * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = (∫ z, c z * perimWt t (h j) z ∂(gaussianReal 0 1)) *
        ∏ l ∈ univ.erase j, perimA t (h l) := by
  simp_rw [perimTilt_eq_prod]
  exact perim_integral_single j c (fun l => perimWt t (h l))

theorem perim_integrable_pair_tilt (h : Fin m → ℝ) (t : ℝ) {i j : Fin m} (hij : i ≠ j)
    {c₁ c₂ : ℝ → ℝ} (h1 : Integrable c₁ (gaussianReal 0 1)) (m1 : Measurable c₁)
    (h2 : Integrable c₂ (gaussianReal 0 1)) (m2 : Measurable c₂) :
    Integrable (fun x => c₁ (x i) * c₂ (x j) * perimTilt h t x)
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  have : (fun x => c₁ (x i) * c₂ (x j) * perimTilt h t x)
      = fun x => c₁ (x i) * c₂ (x j) * ∏ l, perimWt t (h l) (x l) :=
    funext fun x => by rw [perimTilt_eq_prod]
  rw [this]
  exact perim_integrable_pair hij c₁ c₂ (fun l => perimWt t (h l))
    (integrable_mul_perimWt t (h i) h1 m1) (integrable_mul_perimWt t (h j) h2 m2)
    (fun l _ _ => integrable_perimWt t (h l))

theorem perim_integral_pair_tilt (h : Fin m → ℝ) (t : ℝ) {i j : Fin m} (hij : i ≠ j)
    (c₁ c₂ : ℝ → ℝ) :
    ∫ x, c₁ (x i) * c₂ (x j) * perimTilt h t x
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = ((∫ z, c₁ z * perimWt t (h i) z ∂(gaussianReal 0 1)) *
          ∫ z, c₂ z * perimWt t (h j) z ∂(gaussianReal 0 1)) *
        ∏ l ∈ univ \ {i, j}, perimA t (h l) := by
  simp_rw [perimTilt_eq_prod]
  exact perim_integral_pair hij c₁ c₂ (fun l => perimWt t (h l))


theorem perim_tail_prod_empty_le (h : Fin m → ℝ) (t : ℝ) :
    ∏ l, perimA t (h l) ≤ Real.exp (-perimUsum h t) := by
  simpa using perim_tail_prod_le t h ∅

theorem perim_tail_prod_erase_le (h : Fin m → ℝ) (t : ℝ) (j : Fin m) :
    ∏ l ∈ univ.erase j, perimA t (h l) ≤ Real.exp 1 * Real.exp (-perimUsum h t) := by
  simpa [Finset.sdiff_singleton_eq_erase] using perim_tail_prod_le t h {j}

theorem perim_tail_prod_pair_le (h : Fin m → ℝ) (t : ℝ) {i j : Fin m} (hij : i ≠ j) :
    ∏ l ∈ univ \ {i, j}, perimA t (h l) ≤ Real.exp 1 ^ 2 * Real.exp (-perimUsum h t) := by
  simpa [Finset.card_pair hij] using perim_tail_prod_le t h {i, j}

theorem perimA_prod_nonneg (h : Fin m → ℝ) (t : ℝ) (S : Finset (Fin m)) :
    0 ≤ ∏ l ∈ S, perimA t (h l) :=
  Finset.prod_nonneg fun l _ => perimA_nonneg t (h l)

/-- `E w ≤ exp (-U)`. -/
theorem perim_integral_tilt_le (h : Fin m → ℝ) (t : ℝ) :
    ∫ x, perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      ≤ Real.exp (-perimUsum h t) := by
  rw [perim_integral_tilt]; exact perim_tail_prod_empty_le h t

/-- `E[k w] = ∑_j q_j ∏_{i ≠ j} a_i`. -/
theorem perim_integral_K_tilt (h : Fin m → ℝ) (t : ℝ) :
    ∫ x, perimTK h x * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = ∑ j, perimQ t (h j) * ∏ l ∈ univ.erase j, perimA t (h l) := by
  have e1 : ∀ x, perimTK h x * perimTilt h t x
      = ∑ j, perimAct (h j) (x j) * perimTilt h t x := by
    intro x; rw [perimTK_eq_sum, Finset.sum_mul]
  simp_rw [e1]
  rw [integral_finsetSum _ (fun j _ => perim_integrable_single_tilt h t j
    (integrable_perimAct _) (measurable_perimAct _))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [perim_integral_single_tilt, perimQ_eq_integral]

/-- `E[k w] ≤ e * exp (-U) * Q`. -/
theorem perim_integral_K_tilt_le (h : Fin m → ℝ) (t : ℝ) :
    ∫ x, perimTK h x * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      ≤ Real.exp 1 * Real.exp (-perimUsum h t) * perimQsum h t := by
  rw [perim_integral_K_tilt]
  unfold perimQsum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (perim_tail_prod_erase_le h t j) (perimQ_nonneg t (h j))

/-- `E[N2 w] = t ^ 2 ∑_j e2_j ∏_{i ≠ j} a_i`. -/
theorem perim_integral_N2_tilt (h : Fin m → ℝ) {t : ℝ} (ht : t ≠ 0) :
    ∫ x, perimTN2 h x * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = ∑ j, t ^ 2 * perimE2 t (h j) * ∏ l ∈ univ.erase j, perimA t (h l) := by
  have e1 : ∀ x, perimTN2 h x * perimTilt h t x
      = ∑ j, perimPos (h j) (x j) ^ 2 * perimTilt h t x := by
    intro x; unfold perimTN2; rw [Finset.sum_mul]
  simp_rw [e1]
  rw [integral_finsetSum _ (fun j _ => perim_integrable_single_tilt h t j
    (integrable_perimPos_pow (h j) 2) ((measurable_perimPos (h j)).pow_const 2))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [perim_integral_single_tilt (c := fun z => perimPos (h j) z ^ 2), perimE2_eq_integral ht]

/-- `E[N2 w] ≤ e * exp (-U) * (t ^ 2 * E2)`. -/
theorem perim_integral_N2_tilt_le (h : Fin m → ℝ) {t : ℝ} (ht : t ≠ 0) :
    ∫ x, perimTN2 h x * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      ≤ Real.exp 1 * Real.exp (-perimUsum h t) * (t ^ 2 * perimE2sum h t) := by
  rw [perim_integral_N2_tilt h ht]
  unfold perimE2sum
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (perim_tail_prod_erase_le h t j)
    (mul_nonneg (sq_nonneg t) (perimE2_nonneg t (h j)))


theorem integrable_perimPos_div_pow (c t : ℝ) (n : ℕ) :
    Integrable (fun z => (perimPos c z / t) ^ n) (gaussianReal 0 1) := by
  simp_rw [div_pow]
  exact (integrable_perimPos_pow c n).div_const _

theorem measurable_perimPos_div_pow (c t : ℝ) (n : ℕ) :
    Measurable (fun z => (perimPos c z / t) ^ n) :=
  ((measurable_perimPos c).div_const t).pow_const n

/-- Expansion of a square of a sum into diagonal and off-diagonal terms. -/
theorem perim_sq_sum_expand (s : Fin m → ℝ) (W : ℝ) :
    (∑ i, s i) ^ 2 * W = ∑ i, (s i * s i * W + ∑ j ∈ univ.erase i, s i * s j * W) := by
  rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]

/-- `E[(N2 / t ^ 2) ^ 2 w]`: diagonal terms `e4_i ∏_{l ≠ i} a_l` and cross terms
`e2_i e2_j ∏_{l ∉ {i, j}} a_l`. -/
theorem perim_integral_N2sq_tilt (h : Fin m → ℝ) (t : ℝ) :
    ∫ x, (perimTN2 h x / t ^ 2) ^ 2 * perimTilt h t x
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = ∑ i, (perimE4 t (h i) * ∏ l ∈ univ.erase i, perimA t (h l) +
          ∑ j ∈ univ.erase i, (perimE2 t (h i) * perimE2 t (h j)) *
            ∏ l ∈ univ \ {i, j}, perimA t (h l)) := by
  have e1 : ∀ x, (perimTN2 h x / t ^ 2) ^ 2 * perimTilt h t x
      = ∑ i, ((perimPos (h i) (x i) / t) ^ 4 * perimTilt h t x +
          ∑ j ∈ univ.erase i, (perimPos (h i) (x i) / t) ^ 2 * (perimPos (h j) (x j) / t) ^ 2 *
            perimTilt h t x) := by
    intro x
    have hN : perimTN2 h x / t ^ 2 = ∑ i, (perimPos (h i) (x i) / t) ^ 2 := by
      unfold perimTN2; rw [Finset.sum_div]; simp [div_pow]
    rw [hN, perim_sq_sum_expand]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring
  have hdiag : ∀ i, Integrable (fun x => (perimPos (h i) (x i) / t) ^ 4 * perimTilt h t x)
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := fun i =>
    perim_integrable_single_tilt h t i (c := fun z => (perimPos (h i) z / t) ^ 4)
      (integrable_perimPos_div_pow _ _ 4) (measurable_perimPos_div_pow _ _ 4)
  have hoff : ∀ i, ∀ j ∈ univ.erase i,
      Integrable (fun x => (perimPos (h i) (x i) / t) ^ 2 * (perimPos (h j) (x j) / t) ^ 2 *
        perimTilt h t x) (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
    intro i j hj
    exact perim_integrable_pair_tilt h t (Finset.ne_of_mem_erase hj).symm
      (c₁ := fun z => (perimPos (h i) z / t) ^ 2) (c₂ := fun z => (perimPos (h j) z / t) ^ 2)
      (integrable_perimPos_div_pow _ _ 2) (measurable_perimPos_div_pow _ _ 2)
      (integrable_perimPos_div_pow _ _ 2) (measurable_perimPos_div_pow _ _ 2)
  have hoffsum : ∀ i, Integrable (fun x => ∑ j ∈ univ.erase i,
      (perimPos (h i) (x i) / t) ^ 2 * (perimPos (h j) (x j) / t) ^ 2 * perimTilt h t x)
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := fun i => integrable_finsetSum _ (hoff i)
  have hterm : ∀ i, Integrable (fun x => (perimPos (h i) (x i) / t) ^ 4 * perimTilt h t x +
      ∑ j ∈ univ.erase i, (perimPos (h i) (x i) / t) ^ 2 * (perimPos (h j) (x j) / t) ^ 2 *
        perimTilt h t x) (Measure.pi fun _ : Fin m => gaussianReal 0 1) :=
    fun i => (hdiag i).add (hoffsum i)
  simp_rw [e1]
  rw [integral_finsetSum _ (fun i _ => hterm i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_add (hdiag i) (hoffsum i), integral_finsetSum _ (hoff i)]
  congr 1
  · rw [perim_integral_single_tilt (c := fun z => (perimPos (h i) z / t) ^ 4), perimE4_eq_integral]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [perim_integral_pair_tilt h t (Finset.ne_of_mem_erase hj).symm
      (fun z => (perimPos (h i) z / t) ^ 2) (fun z => (perimPos (h j) z / t) ^ 2),
      perimE2_eq_integral', perimE2_eq_integral']

/-- `E[(N2 / t ^ 2) ^ 2 w] ≤ e * exp (-U) * (E4 + e * E2 ^ 2)`. -/
theorem perim_integral_N2sq_tilt_le (h : Fin m → ℝ) (t : ℝ) :
    ∫ x, (perimTN2 h x / t ^ 2) ^ 2 * perimTilt h t x
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      ≤ Real.exp 1 * Real.exp (-perimUsum h t) *
        (perimE4sum h t + Real.exp 1 * perimE2sum h t ^ 2) := by
  rw [perim_integral_N2sq_tilt]
  set E := Real.exp (-perimUsum h t) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hsum : ∀ i, perimE4 t (h i) * ∏ l ∈ univ.erase i, perimA t (h l) +
        ∑ j ∈ univ.erase i, (perimE2 t (h i) * perimE2 t (h j)) *
          ∏ l ∈ univ \ {i, j}, perimA t (h l)
      ≤ Real.exp 1 * E * perimE4 t (h i) +
        Real.exp 1 ^ 2 * E * (perimE2 t (h i) * ∑ j, perimE2 t (h j)) := by
    intro i
    have h1 : perimE4 t (h i) * ∏ l ∈ univ.erase i, perimA t (h l)
        ≤ perimE4 t (h i) * (Real.exp 1 * E) :=
      mul_le_mul_of_nonneg_left (perim_tail_prod_erase_le h t i) (perimE4_nonneg t (h i))
    have h2 : ∑ j ∈ univ.erase i, (perimE2 t (h i) * perimE2 t (h j)) *
          ∏ l ∈ univ \ {i, j}, perimA t (h l)
        ≤ ∑ j ∈ univ.erase i, (perimE2 t (h i) * perimE2 t (h j)) * (Real.exp 1 ^ 2 * E) := by
      refine Finset.sum_le_sum fun j hj => ?_
      exact mul_le_mul_of_nonneg_left (perim_tail_prod_pair_le h t (Finset.ne_of_mem_erase hj).symm)
        (mul_nonneg (perimE2_nonneg t (h i)) (perimE2_nonneg t (h j)))
    have h3 : ∑ j ∈ univ.erase i, (perimE2 t (h i) * perimE2 t (h j)) * (Real.exp 1 ^ 2 * E)
        ≤ ∑ j, (perimE2 t (h i) * perimE2 t (h j)) * (Real.exp 1 ^ 2 * E) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i univ) fun j _ _ =>
        mul_nonneg (mul_nonneg (perimE2_nonneg t (h i)) (perimE2_nonneg t (h j)))
          (by positivity)
    have h4 : ∑ j, (perimE2 t (h i) * perimE2 t (h j)) * (Real.exp 1 ^ 2 * E)
        = Real.exp 1 ^ 2 * E * (perimE2 t (h i) * ∑ j, perimE2 t (h j)) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
    linarith
  refine (Finset.sum_le_sum fun i _ => hsum i).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
  unfold perimE4sum perimE2sum
  have : (∑ i, perimE2 t (h i)) * ∑ j, perimE2 t (h j) = (∑ i, perimE2 t (h i)) ^ 2 := by ring
  nlinarith [this]


/-! ### The second moment and the Cauchy-Schwarz step -/

/-- The indicator of `k x ≠ 0` (some coordinate is active), as a real number. -/
noncomputable def perimS (h x : Fin m → ℝ) : ℝ := if perimTK h x = 0 then 0 else 1

theorem perimS_nonneg (h x : Fin m → ℝ) : 0 ≤ perimS h x := by
  unfold perimS; split_ifs <;> norm_num

theorem perimS_le_one (h x : Fin m → ℝ) : perimS h x ≤ 1 := by
  unfold perimS; split_ifs <;> norm_num

theorem perimS_le_K (h x : Fin m → ℝ) : perimS h x ≤ perimTK h x := by
  unfold perimS
  split_ifs with hk
  · exact perimTK_nonneg h x
  · have hpos : (0 : ℝ) < perimTK h x := lt_of_le_of_ne (perimTK_nonneg h x) (Ne.symm hk)
    unfold perimTK at hpos ⊢
    have : (0 : ℕ) < (univ.filter fun j => h j < x j).card := by exact_mod_cast hpos
    exact Nat.one_le_cast.mpr this

theorem perimS_eq_zero_or_one (h x : Fin m → ℝ) : perimS h x = 0 ∨ perimS h x = 1 := by
  unfold perimS; split_ifs <;> simp

theorem measurable_perimS (h : Fin m → ℝ) : Measurable (perimS h) := by
  unfold perimS
  exact Measurable.ite (measurableSet_eq_fun (measurable_perimTK h) measurable_const)
    measurable_const measurable_const

/-- If no coordinate is active, `V = 0`. -/
theorem perimTV_eq_zero_of_S (h x : Fin m → ℝ) (hS : perimS h x = 0) : perimTV h x = 0 := by
  have hK : perimTK h x = 0 := by
    unfold perimS at hS
    by_contra hne
    simp [hne] at hS
  rw [perimTK_eq_sum] at hK
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => perimAct_nonneg (h j) (x j))).mp hK
  unfold perimTV
  refine Finset.sum_eq_zero fun j _ => ?_
  have hj := hz j (Finset.mem_univ j)
  unfold perimAct at hj
  unfold perimTG
  by_cases hc : h j < x j
  · simp [hc] at hj
  · simp [hc]

theorem perimTV_sq_tilt_integrable (h : Fin m → ℝ) (t : ℝ) :
    Integrable (fun x => perimTV h x ^ 2 * perimTilt h t x)
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  have hd : Integrable (fun x => ((univ : Finset (Fin m)).card : ℝ) *
      ∑ j, perimTG (h j) (x j) ^ 2 * perimTilt h t x)
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) :=
    (integrable_finsetSum _ fun j _ => perim_integrable_single_tilt h t j
      (c := fun z => perimTG (h j) z ^ 2) (integrable_perimTG_sq (h j))
      ((measurable_perimTG (h j)).pow_const 2)).const_mul _
  refine hd.mono' (((measurable_perimTV h).pow_const 2).mul
    (measurable_perimTilt h t)).aestronglyMeasurable ?_
  filter_upwards with x
  have h1 := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin m)))
    (f := fun j => perimTG (h j) (x j))
  have hw := (perimTilt_pos h t x).le
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hw), ← Finset.sum_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h1 hw

theorem perimTV_abs_tilt_integrable (h : Fin m → ℝ) (t : ℝ) :
    Integrable (fun x => |perimTV h x| * perimTilt h t x)
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  have hd : Integrable (fun x => (perimTV h x ^ 2 * perimTilt h t x + perimTilt h t x) / 2)
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) :=
    ((perimTV_sq_tilt_integrable h t).add (integrable_perimTilt h t)).div_const 2
  refine hd.mono' (((measurable_perimTV h).abs).mul (measurable_perimTilt h t)).aestronglyMeasurable
    ?_
  filter_upwards with x
  have hw := (perimTilt_pos h t x).le
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hw)]
  have : |perimTV h x| ≤ (perimTV h x ^ 2 + 1) / 2 := by
    nlinarith [sq_nonneg (|perimTV h x| - 1), sq_abs (perimTV h x)]
  nlinarith

theorem perimS_tilt_integrable (h : Fin m → ℝ) (t : ℝ) :
    Integrable (fun x => perimS h x * perimTilt h t x)
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  refine (integrable_perimTilt h t).mono' ((measurable_perimS h).mul
    (measurable_perimTilt h t)).aestronglyMeasurable ?_
  filter_upwards with x
  have hw := (perimTilt_pos h t x).le
  rw [Real.norm_of_nonneg (mul_nonneg (perimS_nonneg h x) hw)]
  exact mul_le_of_le_one_left hw (perimS_le_one h x)

theorem perimTK_tilt_integrable (h : Fin m → ℝ) (t : ℝ) :
    Integrable (fun x => perimTK h x * perimTilt h t x)
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  have e1 : ∀ x, perimTK h x * perimTilt h t x
      = ∑ j, perimAct (h j) (x j) * perimTilt h t x := by
    intro x; rw [perimTK_eq_sum, Finset.sum_mul]
  simp_rw [e1]
  exact integrable_finsetSum _ fun j _ => perim_integrable_single_tilt h t j
    (integrable_perimAct _) (measurable_perimAct _)

/-- `E[S w] ≤ exp (-U)`. -/
theorem perim_integral_S_tilt_le_exp (h : Fin m → ℝ) (t : ℝ) :
    ∫ x, perimS h x * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      ≤ Real.exp (-perimUsum h t) := by
  refine le_trans ?_ (perim_integral_tilt_le h t)
  refine integral_mono (perimS_tilt_integrable h t) (integrable_perimTilt h t) fun x => ?_
  exact mul_le_of_le_one_left (perimTilt_pos h t x).le (perimS_le_one h x)

/-- `E[S w] ≤ E[k w]`. -/
theorem perim_integral_S_tilt_le_K (h : Fin m → ℝ) (t : ℝ) :
    ∫ x, perimS h x * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      ≤ ∫ x, perimTK h x * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) :=
  integral_mono (perimS_tilt_integrable h t) (perimTK_tilt_integrable h t) fun x =>
    mul_le_mul_of_nonneg_right (perimS_le_K h x) (perimTilt_pos h t x).le


end Vec

/-! ### (b) The abstract real inequalities -/

/-- **Cauchy-Schwarz in AM-GM form.** If `I ≤ (c A + B / c) / 2` for every `c > 0`, then
`I ≤ √(A B)`. -/
theorem perim_cs_amgm {I A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ c : ℝ, 0 < c → I ≤ (c * A + B / c) / 2) : I ≤ √(A * B) := by
  by_cases hI : I ≤ 0
  · exact hI.trans (Real.sqrt_nonneg _)
  replace hI : 0 < I := not_le.mp hI
  refine Real.le_sqrt_of_sq_le ?_
  rcases hA.eq_or_lt with hA0 | hApos
  · exfalso
    have h1 := h ((B + 1) / I) (by positivity)
    rw [← hA0] at h1
    have h2 : B / ((B + 1) / I) = B * I / (B + 1) := by field_simp
    have h3 : B * I / (B + 1) < I := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    rw [h2] at h1
    linarith
  · have h1 := h (I / A) (by positivity)
    have h2 : I / A * A = I := by field_simp
    have h3 : B / (I / A) = B * A / I := by field_simp
    rw [h2, h3] at h1
    have h4 : I ≤ B * A / I := by linarith
    rw [le_div_iff₀ hI] at h4
    nlinarith

/-- **The real-number chain.** Given the five scalar inequalities produced by the probabilistic
steps, `Psi ≤ e ^ 2 * E * √(min 1 Q) * √(2Q + 2 t ^ 2 E2 + 4 E4 + 4 e E2 ^ 2)`,
with `E = exp (-U)`. -/
theorem perim_tilt_real_chain {Ψ I A B E Q E2 E4 t : ℝ}
    (hE : 0 ≤ E) (hQ : 0 ≤ Q) (hE2 : 0 ≤ E2) (hE4 : 0 ≤ E4) (hB0 : 0 ≤ B)
    (hΨ : Ψ ≤ Real.exp 1 * I) (hI : I ≤ √(A * B))
    (hA : A ≤ 2 * (Real.exp 1 * E * Q) + 2 * (Real.exp 1 * E * (t ^ 2 * E2)) +
      4 * (Real.exp 1 * E * (E4 + Real.exp 1 * E2 ^ 2)))
    (hB1 : B ≤ E) (hB2 : B ≤ Real.exp 1 * E * Q) :
    Ψ ≤ Real.exp 1 ^ 2 * E * √(min 1 Q) *
      √(2 * Q + 2 * t ^ 2 * E2 + 4 * E4 + 4 * Real.exp 1 * E2 ^ 2) := by
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  set K := Real.exp 1 * E with hK
  have hK0 : 0 ≤ K := mul_nonneg he0.le hE
  set R := 2 * Q + 2 * t ^ 2 * E2 + 4 * E4 + 4 * Real.exp 1 * E2 ^ 2 with hR
  have hR0 : 0 ≤ R := by positivity
  have hm0 : 0 ≤ min 1 Q := le_min zero_le_one hQ
  have hA' : A ≤ K * R := by
    have : 2 * (K * Q) + 2 * (K * (t ^ 2 * E2)) + 4 * (K * (E4 + Real.exp 1 * E2 ^ 2))
        = K * R := by rw [hR]; ring
    exact hA.trans this.le
  have hB' : B ≤ K * min 1 Q := by
    rcases le_total 1 Q with hq | hq
    · rw [min_eq_left hq]
      calc B ≤ E := hB1
        _ ≤ K * 1 := by rw [hK]; nlinarith
    · rw [min_eq_right hq]; exact hB2
  have hAB : A * B ≤ (K * R) * (K * min 1 Q) := mul_le_mul hA' hB' hB0 (mul_nonneg hK0 hR0)
  have hsq : √(A * B) ≤ K * (√(min 1 Q) * √R) := by
    refine (Real.sqrt_le_sqrt hAB).trans (le_of_eq ?_)
    have : K * R * (K * min 1 Q) = (K * K) * (min 1 Q * R) := by ring
    rw [this, Real.sqrt_mul (mul_self_nonneg K), Real.sqrt_mul_self hK0, Real.sqrt_mul hm0]
  calc Ψ ≤ Real.exp 1 * I := hΨ
    _ ≤ Real.exp 1 * (K * (√(min 1 Q) * √R)) :=
        mul_le_mul_of_nonneg_left (hI.trans hsq) he0.le
    _ = Real.exp 1 ^ 2 * E * √(min 1 Q) * √R := by rw [hK]; ring


/-! ### (c) The tilted Cauchy-Schwarz chain -/

section Chain

variable {m : ℕ}

/-- First step: on `{N2 < t ^ 2}` the tilt is at least `e⁻¹`, so `Psi ≤ e E[|V| w]`. -/
theorem perim_Psi_le (h : Fin m → ℝ) {t : ℝ} (ht : 0 < t) :
    perimPsi h t ≤ Real.exp 1 * ∫ x, |perimTV h x| * perimTilt h t x
      ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  have hmeas : MeasurableSet {x : Fin m → ℝ | perimTN2 h x < t ^ 2} :=
    measurableSet_lt (measurable_perimTN2 h) measurable_const
  unfold perimPsi
  rw [← integral_indicator hmeas, ← integral_const_mul]
  refine integral_mono_of_nonneg ?_ ((perimTV_abs_tilt_integrable h t).const_mul _) ?_
  · filter_upwards with x
    exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) x
  · filter_upwards with x
    by_cases hx : x ∈ {x : Fin m → ℝ | perimTN2 h x < t ^ 2}
    · rw [Set.indicator_of_mem hx]
      have hx' : perimTN2 h x < t ^ 2 := hx
      have hdiv : perimTN2 h x / t ^ 2 < 1 := (div_lt_one (by positivity)).mpr hx'
      have h1 : 1 ≤ Real.exp 1 * perimTilt h t x := by
        unfold perimTilt
        rw [← Real.exp_add]
        refine Real.one_le_exp ?_
        rw [neg_div]
        linarith
      calc |perimTV h x| = |perimTV h x| * 1 := (mul_one _).symm
        _ ≤ |perimTV h x| * (Real.exp 1 * perimTilt h t x) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = Real.exp 1 * (|perimTV h x| * perimTilt h t x) := by ring
    · rw [Set.indicator_of_notMem hx]
      exact mul_nonneg (Real.exp_pos 1).le (mul_nonneg (abs_nonneg _) (perimTilt_pos h t x).le)

/-- Second step: Cauchy-Schwarz, `E[|V| w] ≤ √(E[V² w] E[S w])`. -/
theorem perim_cs_tilt (h : Fin m → ℝ) (t : ℝ) :
    ∫ x, |perimTV h x| * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) ≤
      √((∫ x, perimTV h x ^ 2 * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)) *
        ∫ x, perimS h x * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)) := by
  refine perim_cs_amgm
    (integral_nonneg fun x => mul_nonneg (sq_nonneg _) (perimTilt_pos h t x).le)
    (integral_nonneg fun x => mul_nonneg (perimS_nonneg h x) (perimTilt_pos h t x).le) ?_
  intro c hc
  have hpt : ∀ x, |perimTV h x| * perimTilt h t x ≤
      (c * (perimTV h x ^ 2 * perimTilt h t x) + (perimS h x * perimTilt h t x) / c) / 2 := by
    intro x
    have hw := (perimTilt_pos h t x).le
    rcases perimS_eq_zero_or_one h x with hS | hS
    · have hV := perimTV_eq_zero_of_S h x hS
      simp [hV, hS]
    · rw [hS, ← sq_abs (perimTV h x)]
      have key : 2 * |perimTV h x| ≤ c * |perimTV h x| ^ 2 + 1 / c := by
        have h1 : c * |perimTV h x| ^ 2 + 1 / c - 2 * |perimTV h x|
            = (c * |perimTV h x| - 1) ^ 2 / c := by
          field_simp
          ring
        have h2 : 0 ≤ (c * |perimTV h x| - 1) ^ 2 / c := by positivity
        linarith
      have := mul_le_mul_of_nonneg_right key hw
      calc |perimTV h x| * perimTilt h t x
          = (2 * |perimTV h x|) * perimTilt h t x / 2 := by ring
        _ ≤ (c * |perimTV h x| ^ 2 + 1 / c) * perimTilt h t x / 2 := by linarith
        _ = (c * (|perimTV h x| ^ 2 * perimTilt h t x) + (1 * perimTilt h t x) / c) / 2 := by
            ring
  calc ∫ x, |perimTV h x| * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      ≤ ∫ x, (c * (perimTV h x ^ 2 * perimTilt h t x) + (perimS h x * perimTilt h t x) / c) / 2
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) :=
        integral_mono (perimTV_abs_tilt_integrable h t)
          ((((perimTV_sq_tilt_integrable h t).const_mul c).add
            ((perimS_tilt_integrable h t).div_const c)).div_const 2) hpt
    _ = (c * (∫ x, perimTV h x ^ 2 * perimTilt h t x
            ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)) +
          (∫ x, perimS h x * perimTilt h t x
            ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)) / c) / 2 := by
        rw [integral_div, integral_add ((perimTV_sq_tilt_integrable h t).const_mul c)
          ((perimS_tilt_integrable h t).div_const c), integral_const_mul, integral_div]

/-- **The tilted Cauchy-Schwarz chain (`(**)` of the feasibility study).**
Assume the Stein-type second-moment bound (G3) at `λ = 1/t²`:
`E[V² w] ≤ 2 E[k w] + 2 E[N2 w] + 4 E[(N2/t²)² w]`.
Then for every `t > 0`,
`Psi t ≤ e ^ 2 * exp (-U) * √(min 1 Q) * √(2 Q + 2 t ^ 2 E2 + 4 E4 + 4 e E2 ^ 2)`. -/
theorem perim_tilt_chain (h : Fin m → ℝ) {t : ℝ} (ht : 0 < t)
    (hG3 : ∫ x, perimTV h x ^ 2 * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      ≤ 2 * ∫ x, perimTK h x * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
        + 2 * ∫ x, perimTN2 h x * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
        + 4 * ∫ x, (perimTN2 h x / t ^ 2) ^ 2 * perimTilt h t x
            ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)) :
    perimPsi h t ≤ Real.exp 1 ^ 2 * Real.exp (-perimUsum h t) * √(min 1 (perimQsum h t)) *
      √(2 * perimQsum h t + 2 * t ^ 2 * perimE2sum h t + 4 * perimE4sum h t
        + 4 * Real.exp 1 * perimE2sum h t ^ 2) := by
  have ht0 : t ≠ 0 := ht.ne'
  have hQ : 0 ≤ perimQsum h t := Finset.sum_nonneg fun j _ => perimQ_nonneg t (h j)
  have hE2 : 0 ≤ perimE2sum h t := Finset.sum_nonneg fun j _ => perimE2_nonneg t (h j)
  have hE4 : 0 ≤ perimE4sum h t := Finset.sum_nonneg fun j _ => perimE4_nonneg t (h j)
  have hK := perim_integral_K_tilt_le h t
  have hN := perim_integral_N2_tilt_le h ht0
  have hN2 := perim_integral_N2sq_tilt_le h t
  refine perim_tilt_real_chain (Real.exp_pos _).le hQ hE2 hE4
    (integral_nonneg fun x => mul_nonneg (perimS_nonneg h x) (perimTilt_pos h t x).le)
    (perim_Psi_le h ht) (perim_cs_tilt h t) ?_
    (perim_integral_S_tilt_le_exp h t)
    ((perim_integral_S_tilt_le_K h t).trans hK)
  linarith

end Chain

end LatticeProb
