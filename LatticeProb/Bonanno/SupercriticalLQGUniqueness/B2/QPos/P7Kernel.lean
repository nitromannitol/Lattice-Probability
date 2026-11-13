/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P7Kernel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P7DST
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFModel
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFBoxDegree

 











set_option autoImplicit false
noncomputable section

open Real Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P7

attribute [local instance] Classical.propDecidable

 
def mu (N : ℕ) (k : ℤ) : ℝ := (N : ℝ) ^ 2 * (1 - Real.cos (k * π / (2 * N)))

lemma mu_nonneg (N : ℕ) (k : ℤ) : 0 ≤ mu N k :=
  mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (Real.cos_le_one _))

 
lemma one_sub_cos_ge {x : ℝ} (hx : 0 ≤ x) (hxπ : x ≤ π) :
    2 * x ^ 2 / π ^ 2 ≤ 1 - Real.cos x := by
  have hπ := Real.pi_pos
  have h1 : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    have h0 := Real.cos_two_mul (x / 2)
    rw [show 2 * (x / 2) = x by ring] at h0
    have h2 := Real.sin_sq_add_cos_sq (x / 2)
    linarith
  have h3 : 2 / π * (x / 2) ≤ Real.sin (x / 2) :=
    Real.mul_le_sin (by linarith) (by linarith)
  have h4 : 0 ≤ 2 / π * (x / 2) := by positivity
  rw [h1]
  have h5 : (2 / π * (x / 2)) ^ 2 ≤ Real.sin (x / 2) ^ 2 := pow_le_pow_left₀ h4 h3 2
  have h6 : (2 / π * (x / 2)) ^ 2 = x ^ 2 / π ^ 2 := by field_simp
  rw [h6] at h5
  have : 2 * x ^ 2 / π ^ 2 = 2 * (x ^ 2 / π ^ 2) := by ring
  rw [this]; linarith

 
lemma mu_ge (N : ℕ) {k : ℤ} (hk : k ∈ modes N) : (k : ℝ) ^ 2 / 2 ≤ mu N k := by
  simp only [modes, mem_Icc] at hk
  have hN : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hπ := Real.pi_pos
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
  have hk2 : (k : ℝ) ≤ 2 * N - 1 := by exact_mod_cast hk.2
  have hx0 : 0 ≤ (k : ℝ) * π / (2 * N) := by positivity
  have hxπ : (k : ℝ) * π / (2 * N) ≤ π := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have := one_sub_cos_ge hx0 hxπ
  unfold mu
  have e : (N : ℝ) ^ 2 * (2 * ((k : ℝ) * π / (2 * N)) ^ 2 / π ^ 2) = (k : ℝ) ^ 2 / 2 := by
    field_simp
  rw [← e]
  exact mul_le_mul_of_nonneg_left this (sq_nonneg _)

lemma mu_pos (N : ℕ) {k : ℤ} (hk : k ∈ modes N) : 0 < mu N k := by
  have h := mu_ge N hk
  have hk1 : (1 : ℝ) ≤ k := by
    simp only [modes, mem_Icc] at hk; exact_mod_cast hk.1
  have : (0 : ℝ) < (k : ℝ) ^ 2 / 2 := by positivity
  linarith

 
def qker (N : ℕ) (t : ℝ) (a b : ℤ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ k ∈ modes N, Real.exp (-t * mu N k) * dsin N k a * dsin N k b

lemma qker_symm (N : ℕ) (t : ℝ) (a b : ℤ) : qker N t a b = qker N t b a := by
  unfold qker; congr 1; refine sum_congr rfl fun k _ => by ring

 
theorem qker_semigroup (N : ℕ) (hN : 0 < N) (s t : ℝ) (a b : ℤ) :
    ∑ c ∈ sites1 N, qker N s a c * qker N t c b = qker N (s + t) a b := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold qker
  have expand : ∀ c ∈ sites1 N,
      ((N : ℝ)⁻¹ * ∑ k ∈ modes N, Real.exp (-s * mu N k) * dsin N k a * dsin N k c) *
        ((N : ℝ)⁻¹ * ∑ l ∈ modes N, Real.exp (-t * mu N l) * dsin N l c * dsin N l b) =
      (N : ℝ)⁻¹ * (N : ℝ)⁻¹ * ∑ k ∈ modes N, ∑ l ∈ modes N,
        (Real.exp (-s * mu N k) * dsin N k a * Real.exp (-t * mu N l) * dsin N l b) *
          (dsin N k c * dsin N l c) := by
    intro c _
    rw [mul_mul_mul_comm, sum_mul_sum]
    congr 1
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring
  rw [sum_congr rfl expand, ← mul_sum]
  have inner : ∀ k ∈ modes N, ∑ c ∈ sites1 N, ∑ l ∈ modes N,
      (Real.exp (-s * mu N k) * dsin N k a * Real.exp (-t * mu N l) * dsin N l b) *
        (dsin N k c * dsin N l c) =
      N * (Real.exp (-(s + t) * mu N k) * dsin N k a * dsin N k b) := by
    intro k hk
    rw [sum_comm]
    have hl : ∀ l ∈ modes N, ∑ c ∈ sites1 N,
        (Real.exp (-s * mu N k) * dsin N k a * Real.exp (-t * mu N l) * dsin N l b) *
          (dsin N k c * dsin N l c) =
        (Real.exp (-s * mu N k) * dsin N k a * Real.exp (-t * mu N l) * dsin N l b) *
          (if k = l then (N : ℝ) else 0) := by
      intro l hl
      rw [← mul_sum, dsin_orth_modes N hN hk hl]
    rw [sum_congr rfl hl]
    simp only [mul_ite, mul_zero, sum_ite_eq, hk, ite_true]
    rw [show -(s + t) * mu N k = -s * mu N k + -t * mu N k by ring, Real.exp_add]
    ring
  rw [sum_comm, sum_congr rfl inner, ← mul_sum]
  field_simp

 
lemma mul_qker_diag (N : ℕ) (hN : 0 < N) (t : ℝ) (a : ℤ) :
    (N : ℝ) * qker N t a a = ∑ k ∈ modes N, Real.exp (-t * mu N k) * dsin N k a ^ 2 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold qker
  rw [← mul_assoc, mul_inv_cancel₀ hN', one_mul]
  refine sum_congr rfl fun k _ => by ring

lemma qker_diag_nonneg (N : ℕ) (hN : 0 < N) (t : ℝ) (a : ℤ) : 0 ≤ qker N t a a := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := mul_qker_diag N hN t a
  have : 0 ≤ (N : ℝ) * qker N t a a := by
    rw [h]; exact sum_nonneg fun k _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  by_contra hneg
  push_neg at hneg
  have := mul_neg_of_pos_of_neg hN' hneg
  linarith

 
lemma qker_diag_le_one (N : ℕ) (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) {a : ℤ}
    (ha : a ∈ sites1 N) : qker N t a a ≤ 1 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := mul_qker_diag N hN t a
  have hc := dsin_complete N hN ha ha
  simp only [if_true] at hc
  have hle : ∑ k ∈ modes N, Real.exp (-t * mu N k) * dsin N k a ^ 2 ≤
      ∑ k ∈ modes N, dsin N k a * dsin N k a := by
    refine sum_le_sum fun k _ => ?_
    have h1 : Real.exp (-t * mu N k) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mu_nonneg N k])
    nlinarith [sq_nonneg (dsin N k a)]
  rw [hc, ← h] at hle
  nlinarith

 
lemma mul_qker_diag_le (N : ℕ) (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) (a : ℤ) :
    (N : ℝ) * qker N t a a ≤ ∑ k ∈ modes N, Real.exp (-t * ((k : ℝ) ^ 2 / 2)) := by
  rw [mul_qker_diag N hN]
  refine sum_le_sum fun k hk => ?_
  have h1 : Real.exp (-t * mu N k) ≤ Real.exp (-t * ((k : ℝ) ^ 2 / 2)) :=
    Real.exp_le_exp.mpr (by nlinarith [mu_ge N hk])
  have h2 : dsin N k a ^ 2 ≤ 1 := by
    have := abs_dsin_le N k a
    nlinarith [abs_nonneg (dsin N k a), sq_abs (dsin N k a)]
  calc Real.exp (-t * mu N k) * dsin N k a ^ 2 ≤ Real.exp (-t * mu N k) * 1 :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ ≤ _ := by rw [mul_one]; exact h1

 
lemma sum_modes_range (N : ℕ) (f : ℤ → ℝ) :
    ∑ k ∈ modes N, f k = ∑ i ∈ range (2 * N - 1), f ((i : ℤ) + 1) := by
  symm
  refine sum_nbij' (fun i : ℕ => (i : ℤ) + 1) (fun k : ℤ => (k - 1).toNat) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [mem_range] at hi; simp only [modes, mem_Icc]; omega
  · intro k hk; simp only [modes, mem_Icc] at hk; simp only [mem_range]; omega
  · intro i _; simp
  · intro k hk; simp only [modes, mem_Icc] at hk
    show (((k - 1).toNat : ℕ) : ℤ) + 1 = k
    omega
  · intro i _; rfl

 
lemma sum_modes_exp_le (N : ℕ) {b : ℝ} (hb : 0 < b) :
    ∑ k ∈ modes N, Real.exp (-b * (k : ℝ) ^ 2) ≤ Real.sqrt (π / b) / 2 := by
  rw [sum_modes_range]
  set M := 2 * N - 1
  have hanti : AntitoneOn (fun x : ℝ => Real.exp (-b * x ^ 2)) (Set.Icc 0 (0 + M)) := by
    intro x hx y hy hxy
    simp only [Set.mem_Icc] at hx hy
    have hsq : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx.1 hxy 2
    have hbsq := mul_le_mul_of_nonneg_left hsq hb.le
    exact Real.exp_le_exp.mpr (by linarith)
  have h1 := hanti.sum_le_integral
  have h2 : ∫ x in (0 : ℝ)..(0 + M), Real.exp (-b * x ^ 2) ≤
      ∫ x in Set.Ioi (0 : ℝ), Real.exp (-b * x ^ 2) := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    refine MeasureTheory.setIntegral_mono_set ?_ ?_ ?_
    · exact (integrable_exp_neg_mul_sq hb).integrableOn
    · exact Filter.Eventually.of_forall fun x => (Real.exp_pos _).le
    · exact Filter.Eventually.of_forall Set.Ioc_subset_Ioi_self
  rw [integral_gaussian_Ioi] at h2
  calc ∑ i ∈ range M, Real.exp (-b * (((i : ℤ) + 1 : ℤ) : ℝ) ^ 2)
      = ∑ i ∈ range M, Real.exp (-b * (0 + ((i + 1 : ℕ) : ℝ)) ^ 2) := by
        refine sum_congr rfl fun i _ => by push_cast; ring_nf
    _ ≤ _ := h1.trans h2

 

 
abbrev Nn (n : ℕ) : ℕ := 2 ^ n

lemma Nn_pos (n : ℕ) : 0 < Nn n := by positivity

lemma mem_interiorSites_iff (n : ℕ) (z : ℤ × ℤ) :
    z ∈ interiorSites n ↔ z.1 ∈ sites1 (Nn n) ∧ z.2 ∈ sites1 (Nn n) := by
  simp [interiorSites, Finset.mem_product, Finset.mem_Icc, interiorRadius, sites1, Nn]

lemma site_fst_mem (n : ℕ) (v : DGFFSite n) : v.1.1 ∈ sites1 (Nn n) :=
  ((mem_interiorSites_iff n v.1).mp v.2).1

lemma site_snd_mem (n : ℕ) (v : DGFFSite n) : v.1.2 ∈ sites1 (Nn n) :=
  ((mem_interiorSites_iff n v.1).mp v.2).2

 
def Gmat (n : ℕ) : Matrix (DGFFSite n) (DGFFSite n) ℝ := fun v u =>
  π * ∑ k ∈ modes (Nn n), ∑ l ∈ modes (Nn n),
    dsin (Nn n) k v.1.1 * dsin (Nn n) k u.1.1 * dsin (Nn n) l v.1.2 * dsin (Nn n) l u.1.2 /
      (mu (Nn n) k + mu (Nn n) l)

 
lemma sum_adjacent_eq (n : ℕ) (v : DGFFSite n) (f : ℤ × ℤ → ℝ)
    (hf : ∀ w : ℤ × ℤ, w ∉ interiorSites n → f w = 0) :
    ∑ w : DGFFSite n, (if latticeAdjacent v.1 w.1 then (1 : ℝ) else 0) * f w.1 =
      f (v.1.1 + 1, v.1.2) + f (v.1.1 - 1, v.1.2) + f (v.1.1, v.1.2 + 1) +
        f (v.1.1, v.1.2 - 1) := by
  classical
  have hs : ∑ w : DGFFSite n, (if latticeAdjacent v.1 w.1 then (1 : ℝ) else 0) * f w.1 =
      ∑ w ∈ interiorSites n, (if latticeAdjacent v.1 w then (1 : ℝ) else 0) * f w :=
    (Finset.sum_subtype (interiorSites n) (by simp)
      (fun w => (if latticeAdjacent v.1 w then (1 : ℝ) else 0) * f w)).symm
  rw [hs]
  have hext : ∑ w ∈ interiorSites n, (if latticeAdjacent v.1 w then (1 : ℝ) else 0) * f w =
      ∑ w ∈ interiorSites n ∪ {(v.1.1 + 1, v.1.2), (v.1.1 - 1, v.1.2),
        (v.1.1, v.1.2 + 1), (v.1.1, v.1.2 - 1)},
        (if latticeAdjacent v.1 w then (1 : ℝ) else 0) * f w := by
    refine sum_subset subset_union_left fun w _ hw => by rw [hf w hw, mul_zero]
  rw [hext]
  have hsub : ({(v.1.1 + 1, v.1.2), (v.1.1 - 1, v.1.2), (v.1.1, v.1.2 + 1),
      (v.1.1, v.1.2 - 1)} : Finset (ℤ × ℤ)) ⊆ interiorSites n ∪ {(v.1.1 + 1, v.1.2),
        (v.1.1 - 1, v.1.2), (v.1.1, v.1.2 + 1), (v.1.1, v.1.2 - 1)} := subset_union_right
  rw [← sum_subset hsub]
  · have h1 : (v.1.1 + 1, v.1.2) ∉
        ({(v.1.1 - 1, v.1.2), (v.1.1, v.1.2 + 1), (v.1.1, v.1.2 - 1)} : Finset (ℤ × ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]; omega
    have h2 : (v.1.1 - 1, v.1.2) ∉
        ({(v.1.1, v.1.2 + 1), (v.1.1, v.1.2 - 1)} : Finset (ℤ × ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]; omega
    have h3 : (v.1.1, v.1.2 + 1) ∉ ({(v.1.1, v.1.2 - 1)} : Finset (ℤ × ℤ)) := by
      simp only [Finset.mem_singleton, Prod.mk.injEq, not_and]; omega
    rw [sum_insert h1, sum_insert h2, sum_insert h3, sum_singleton]
    simp [latticeAdjacent]
    ring
  · intro w _ hw
    have : ¬ latticeAdjacent v.1 w := by
      intro hadj
      apply hw
      rcases hadj with h | h | h | h <;>
        · rcases w with ⟨x, y⟩
          simp only at h
          simp [Prod.mk.injEq, h.1, h.2]
    simp [this]

 
lemma precision_mul_dsin (n : ℕ) (v : DGFFSite n) {k l : ℤ} :
    ∑ w : DGFFSite n, (boxConductances n).precision v w *
        (dsin (Nn n) k w.1.1 * dsin (Nn n) l w.1.2) =
      (mu (Nn n) k + mu (Nn n) l) / (π * (Nn n : ℝ) ^ 2) *
        (dsin (Nn n) k v.1.1 * dsin (Nn n) l v.1.2) := by
  classical
  set N := Nn n
  have hN : 0 < N := Nn_pos n
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hπ : π ≠ 0 := Real.pi_ne_zero
  set f : ℤ × ℤ → ℝ := fun w => dsin N k w.1 * dsin N l w.2 with hfdef
  have hf0 : ∀ w : ℤ × ℤ, w ∉ interiorSites n → latticeAdjacent v.1 w → f w = 0 := by
    intro w hw hadj
    rw [mem_interiorSites_iff] at hw
    have h1 := site_fst_mem n v
    have h2 := site_snd_mem n v
    simp only [sites1, Finset.mem_Icc] at h1 h2 hw
    rcases hadj with h | h | h | h <;>
    · rcases w with ⟨x, y⟩
      simp only at h
      obtain ⟨hx, hy⟩ := h
      by_cases hxN : x = (N : ℤ)
      · simp [hfdef, hxN, dsin_pos_boundary N hN]
      by_cases hxN' : x = -(N : ℤ)
      · simp [hfdef, hxN', dsin_neg_boundary]
      by_cases hyN : y = (N : ℤ)
      · simp [hfdef, hyN, dsin_pos_boundary N hN]
      by_cases hyN' : y = -(N : ℤ)
      · simp [hfdef, hyN', dsin_neg_boundary]
      exfalso; apply hw; omega
  
  have hsplit : ∀ w : DGFFSite n, (boxConductances n).precision v w * f w.1 =
      (if v = w then 2 / π * f w.1 else 0) -
        dgffConductance * ((if latticeAdjacent v.1 w.1 then (1 : ℝ) else 0) * f w.1) := by
    intro w
    by_cases hvw : v = w
    · subst hvw
      have hrate := box_totalRate_eq n v
      simp only [WiredConductances.totalRate] at hrate
      simp only [WiredConductances.precision, if_true, not_latticeAdjacent_self, if_false]
      rw [hrate]; ring
    · simp only [WiredConductances.precision, hvw, if_false, boxConductances]
      split_ifs <;> ring
  rw [sum_congr rfl fun w _ => hsplit w, sum_sub_distrib, ← mul_sum]
  simp only [sum_ite_eq, mem_univ, if_true]
  have hadj := sum_adjacent_eq n v (fun w => if latticeAdjacent v.1 w then f w else 0)
    (fun w hw => by split_ifs with h; exact hf0 w hw h; rfl)
  have hadj' : ∑ w : DGFFSite n, (if latticeAdjacent v.1 w.1 then (1 : ℝ) else 0) * f w.1 =
      ∑ w : DGFFSite n, (if latticeAdjacent v.1 w.1 then (1 : ℝ) else 0) *
        (if latticeAdjacent v.1 w.1 then f w.1 else 0) := by
    refine sum_congr rfl fun w _ => by split_ifs <;> ring
  rw [hadj', hadj]
  simp only [latticeAdjacent, true_or, or_true, if_true, and_self]
  simp only [hfdef]
  have e1 := dsin_add_one_add_sub_one N k v.1.1
  have e2 := dsin_add_one_add_sub_one N l v.1.2
  have hsum : dsin N k (v.1.1 + 1) * dsin N l v.1.2 + dsin N k (v.1.1 - 1) * dsin N l v.1.2 +
      dsin N k v.1.1 * dsin N l (v.1.2 + 1) + dsin N k v.1.1 * dsin N l (v.1.2 - 1) =
      (2 * Real.cos (k * π / (2 * N)) + 2 * Real.cos (l * π / (2 * N))) *
        (dsin N k v.1.1 * dsin N l v.1.2) := by
    have : dsin N k (v.1.1 + 1) * dsin N l v.1.2 + dsin N k (v.1.1 - 1) * dsin N l v.1.2 +
        dsin N k v.1.1 * dsin N l (v.1.2 + 1) + dsin N k v.1.1 * dsin N l (v.1.2 - 1) =
        (dsin N k (v.1.1 + 1) + dsin N k (v.1.1 - 1)) * dsin N l v.1.2 +
          dsin N k v.1.1 * (dsin N l (v.1.2 + 1) + dsin N l (v.1.2 - 1)) := by ring
    rw [this, e1, e2]; ring
  rw [hsum]
  unfold mu dgffConductance
  field_simp
  ring

 
theorem precision_mul_Gmat (n : ℕ) : (boxConductances n).precision * Gmat n = 1 := by
  classical
  set N := Nn n
  have hN : 0 < N := Nn_pos n
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hπ : π ≠ 0 := Real.pi_ne_zero
  ext v u
  rw [Matrix.mul_apply]
  unfold Gmat
  have step : ∀ w : DGFFSite n, (boxConductances n).precision v w *
      (π * ∑ k ∈ modes N, ∑ l ∈ modes N,
        dsin N k w.1.1 * dsin N k u.1.1 * dsin N l w.1.2 * dsin N l u.1.2 /
          (mu N k + mu N l)) =
      π * ∑ k ∈ modes N, ∑ l ∈ modes N, (dsin N k u.1.1 * dsin N l u.1.2 /
          (mu N k + mu N l)) *
        ((boxConductances n).precision v w * (dsin N k w.1.1 * dsin N l w.1.2)) := by
    intro w
    rw [mul_left_comm, mul_sum]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun l _ => by ring
  rw [sum_congr rfl fun w _ => step w, ← mul_sum]
  rw [sum_comm]
  have inner : ∀ k ∈ modes N, ∑ w : DGFFSite n, ∑ l ∈ modes N,
      (dsin N k u.1.1 * dsin N l u.1.2 / (mu N k + mu N l)) *
        ((boxConductances n).precision v w * (dsin N k w.1.1 * dsin N l w.1.2)) =
      ∑ l ∈ modes N, (π * (N : ℝ) ^ 2)⁻¹ *
        (dsin N k v.1.1 * dsin N k u.1.1) * (dsin N l v.1.2 * dsin N l u.1.2) := by
    intro k hk
    rw [sum_comm]
    refine sum_congr rfl fun l hl => ?_
    rw [← mul_sum, precision_mul_dsin n v]
    have hpos : 0 < mu N k + mu N l := add_pos (mu_pos N hk) (mu_pos N hl)
    field_simp
    ring
  rw [sum_congr rfl inner]
  simp_rw [← mul_sum, ← sum_mul]
  rw [show ∑ k ∈ modes N, (π * (N : ℝ) ^ 2)⁻¹ * (dsin N k v.1.1 * dsin N k u.1.1) =
      (π * (N : ℝ) ^ 2)⁻¹ * ∑ k ∈ modes N, dsin N k v.1.1 * dsin N k u.1.1 by rw [mul_sum]]
  rw [dsin_complete N hN (site_fst_mem n v) (site_fst_mem n u),
    dsin_complete N hN (site_snd_mem n v) (site_snd_mem n u)]
  rw [Matrix.one_apply]
  by_cases hvu : v = u
  · subst hvu; simp; field_simp
  · have : ¬ (v.1.1 = u.1.1 ∧ v.1.2 = u.1.2) := fun h =>
      hvu (Subtype.ext (Prod.ext h.1 h.2))
    by_cases h1 : v.1.1 = u.1.1
    · have h2 : ¬ v.1.2 = u.1.2 := fun h2 => this ⟨h1, h2⟩
      simp [hvu, h1, h2]
    · simp [hvu, h1]

 
theorem Gmat_eq_inv (n : ℕ) : Gmat n = (boxConductances n).precision⁻¹ :=
  (Matrix.inv_eq_right_inv (precision_mul_Gmat n)).symm

end SupercriticalLQGUniqueness.B2.QPos.P7
