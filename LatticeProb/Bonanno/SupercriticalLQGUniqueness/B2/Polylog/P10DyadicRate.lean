/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P10DyadicRate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.InputsPLA
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.ApproxMultiplicativity
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.BoundedAdditive

 



















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology

namespace SupercriticalLQGUniqueness.B2.Polylog

 
def bF (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (ε r : Set.Ioi (0 : ℝ)) : ℝ :=
  (r : ℝ) * (m ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos (Set.mem_Ioi.mp ε.2)
    (Set.mem_Ioi.mp r.2))⟩ : ℝ) / (m ε : ℝ)

 
def divI (ε r : Set.Ioi (0 : ℝ)) : Set.Ioi (0 : ℝ) :=
  ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos (Set.mem_Ioi.mp ε.2) (Set.mem_Ioi.mp r.2))⟩

 
def mulI (r s : Set.Ioi (0 : ℝ)) : Set.Ioi (0 : ℝ) :=
  ⟨(r : ℝ) * s, Set.mem_Ioi.mpr (mul_pos (Set.mem_Ioi.mp r.2) (Set.mem_Ioi.mp s.2))⟩

lemma bF_pos (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (ε r : Set.Ioi (0 : ℝ)) : 0 < bF m ε r := by
  unfold bF
  have h1 : (0 : ℝ) < r := r.2
  have h2 : (0 : ℝ) < (m ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos (Set.mem_Ioi.mp ε.2)
    (Set.mem_Ioi.mp r.2))⟩ : ℝ) := (m _).2
  have h3 : (0 : ℝ) < (m ε : ℝ) := (m ε).2
  positivity

 
lemma bF_mul (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (ε r s : Set.Ioi (0 : ℝ)) :
    bF m ε (mulI r s) = bF m ε r * bF m (divI ε r) s := by
  unfold bF
  have hm : (m ⟨(ε : ℝ) / (mulI r s : ℝ), Set.mem_Ioi.mpr (div_pos (Set.mem_Ioi.mp ε.2)
      (Set.mem_Ioi.mp (mulI r s).2))⟩ : ℝ) =
      (m ⟨((divI ε r : ℝ)) / s, Set.mem_Ioi.mpr (div_pos (Set.mem_Ioi.mp (divI ε r).2)
        (Set.mem_Ioi.mp s.2))⟩ : ℝ) := by
    congr 2
    apply Subtype.ext
    show (ε : ℝ) / ((r : ℝ) * s) = (ε : ℝ) / r / s
    rw [div_div]
  have hmr : (m (divI ε r) : ℝ) = (m ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos (Set.mem_Ioi.mp ε.2)
      (Set.mem_Ioi.mp r.2))⟩ : ℝ) := rfl
  rw [hm, hmr]
  have h2 : (0 : ℝ) < (m ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos (Set.mem_Ioi.mp ε.2)
    (Set.mem_Ioi.mp r.2))⟩ : ℝ) := (m _).2
  have h3 : (0 : ℝ) < (m ε : ℝ) := (m ε).2
  show (r : ℝ) * s * _ / _ = _
  field_simp

lemma rpow_half_le_of_le {ε t : ℝ} (ht : 0 ≤ t) (h : ε ≤ (t / 100) ^ 2) :
    100 * ε ^ (1 - (1 / 2 : ℝ)) ≤ t := by
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  have : Real.sqrt ε ≤ t / 100 := by
    rw [Real.sqrt_le_left (by positivity)]; exact h
  linarith

 
lemma ratioUniform_half (hRU : PLRatioUniform) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (hQ : IsLFPPExponent ξ Q) {D : LQGMetric.DistC → LSCMetric}
    {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} (hD : Iface.IsPfeWeakMetric ξ D c)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε)) :
    ∃ C : ℝ, 1 < C ∧ ∀ R : ℝ, 1 ≤ R → ∃ εs : ℝ, 0 < εs ∧
      ∀ ε r : Set.Ioi (0 : ℝ), (ε : ℝ) ≤ εs → (ε : ℝ) ≤ ((r : ℝ) / 100) ^ 2 → (r : ℝ) ≤ R →
        C⁻¹ * (c r : ℝ) ≤ bF m ε r ∧ bF m ε r ≤ C * (c r : ℝ) := by
  obtain ⟨C, hC, hR⟩ := hRU ξ Q hQ D c hD m hm (1 / 2) (by norm_num) (by norm_num)
  refine ⟨C, hC, fun R hR1 => ?_⟩
  obtain ⟨εs, hεs, hb⟩ := hR R hR1
  refine ⟨εs, hεs, fun ε r h1 h2 h3 => ?_⟩
  obtain ⟨b1, b2⟩ := hb ε r h1 (rpow_half_le_of_le (le_of_lt r.2) h2) h3
  have hc : (0 : ℝ) < c r := (c r).2
  have he : (r : ℝ) * (m ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos (Set.mem_Ioi.mp ε.2)
      (Set.mem_Ioi.mp r.2))⟩ : ℝ) / ((c r : ℝ) * (m ε : ℝ)) = bF m ε r / c r := by
    unfold bF; rw [div_div, mul_comm (m ε : ℝ)]
  rw [he] at b1 b2
  constructor
  · rw [le_div_iff₀ hc] at b1; linarith
  · rw [div_le_iff₀ hc] at b2; linarith

 
theorem pl_submult_of_ratioUniform (hRU : PLRatioUniform) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (hQ : IsLFPPExponent ξ Q) {D : LQGMetric.DistC → LSCMetric}
    {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} (hD : Iface.IsPfeWeakMetric ξ D c)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε)) :
    ∃ K : ℝ, 1 < K ∧ ∀ r s : Set.Ioi (0 : ℝ),
      (K⁻¹) ^ 3 * ((c r : ℝ) * c s) ≤ c (mulI r s) ∧ (c (mulI r s) : ℝ) ≤ K ^ 3 * ((c r : ℝ) * c s) := by
  obtain ⟨C, hC, hR⟩ := ratioUniform_half hRU ξ Q hQ hD m hm
  refine ⟨C, hC, fun r s => ?_⟩
  have hr : (0 : ℝ) < r := r.2
  have hs : (0 : ℝ) < s := s.2
  set R := max 1 (max (r : ℝ) (max (s : ℝ) ((r : ℝ) * s)))
  have hR1 : 1 ≤ R := le_max_left _ _
  obtain ⟨εs, hεs, hb⟩ := hR R hR1
  
  set ε0 : ℝ := min εs (min ((r / 100) ^ 2) (min (((r : ℝ) * s / 100) ^ 2)
    (min (εs * r) (((s : ℝ) / 100) ^ 2 * r))))
  have hε0 : 0 < ε0 := by
    simp only [ε0]
    refine lt_min hεs (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
      (by positivity))))
  set ε : Set.Ioi (0 : ℝ) := ⟨ε0, hε0⟩
  have e1 : (ε : ℝ) ≤ εs := min_le_left _ _
  have e2 : (ε : ℝ) ≤ ((r : ℝ) / 100) ^ 2 := (min_le_right _ _).trans (min_le_left _ _)
  have e3 : (ε : ℝ) ≤ ((mulI r s : ℝ) / 100) ^ 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have e4 : (divI ε r : ℝ) ≤ εs := by
    show ε0 / r ≤ εs
    rw [div_le_iff₀ hr]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))
  have e5 : (divI ε r : ℝ) ≤ ((s : ℝ) / 100) ^ 2 := by
    show ε0 / r ≤ _
    rw [div_le_iff₀ hr]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))
  have hRr : (r : ℝ) ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRs : (s : ℝ) ≤ R := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hRrs : (mulI r s : ℝ) ≤ R :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  obtain ⟨a1, a2⟩ := hb ε r e1 e2 hRr
  obtain ⟨b1, b2⟩ := hb (divI ε r) s e4 e5 hRs
  obtain ⟨c1, c2⟩ := hb ε (mulI r s) e1 e3 hRrs
  rw [bF_mul] at c1 c2
  exact approx_mul_of_three_comparisons C (c r) (c s) (c (mulI r s)) (bF m ε r)
    (bF m (divI ε r) s) (by linarith) (c r).2.le (c s).2.le ⟨a1, a2⟩ ⟨b1, b2⟩ ⟨c1, c2⟩

 

 
def dyad (n : ℕ) : Set.Ioi (0 : ℝ) := ⟨(2 : ℝ)⁻¹ ^ n, Set.mem_Ioi.mpr (by positivity)⟩

lemma mulI_dyad (n k : ℕ) : mulI (dyad n) (dyad k) = dyad (n + k) := by
  apply Subtype.ext
  show (2 : ℝ)⁻¹ ^ n * (2 : ℝ)⁻¹ ^ k = (2 : ℝ)⁻¹ ^ (n + k)
  rw [pow_add]

lemma log_dyad (n : ℕ) : Real.log (dyad n : ℝ) = -(n * Real.log 2) := by
  show Real.log ((2 : ℝ)⁻¹ ^ n) = _
  rw [Real.log_pow, Real.log_inv]; ring

 
lemma log_c_dyad_bounded_additive {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {K : ℝ} (hK : 1 < K)
    (hsub : ∀ r s : Set.Ioi (0 : ℝ),
      (K⁻¹) ^ 3 * ((c r : ℝ) * c s) ≤ c (mulI r s) ∧ (c (mulI r s) : ℝ) ≤ K ^ 3 * ((c r : ℝ) * c s))
    (n k : ℕ) :
    Real.log (c (dyad n)) + Real.log (c (dyad k)) - 3 * Real.log K ≤ Real.log (c (dyad (n + k))) ∧
      Real.log (c (dyad (n + k))) ≤ Real.log (c (dyad n)) + Real.log (c (dyad k)) + 3 * Real.log K := by
  have hK0 : 0 < K := by linarith
  have hn : (0 : ℝ) < c (dyad n) := (c _).2
  have hk : (0 : ℝ) < c (dyad k) := (c _).2
  have hnk : (0 : ℝ) < c (dyad (n + k)) := (c _).2
  obtain ⟨h1, h2⟩ := hsub (dyad n) (dyad k)
  rw [mulI_dyad] at h1 h2
  constructor
  · have := Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hn.ne' hk.ne', Real.log_pow,
      Real.log_inv] at this
    push_cast at this; linarith
  · have := Real.log_le_log hnk h2
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hn.ne' hk.ne', Real.log_pow] at this
    push_cast at this; linarith

 
lemma nonpos_of_mul_le {a b : ℝ} (h : ∀ n : ℕ, 0 < n → a * n ≤ b) : a ≤ 0 := by
  by_contra ha
  push Not at ha
  obtain ⟨n, hn⟩ := exists_nat_gt (b / a)
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      have := h 1 one_pos
      simp only [Nat.cast_one, mul_one] at this
      have : b / a ≥ 1 := by rw [ge_iff_le, le_div_iff₀ ha]; linarith
      push_cast at hn; linarith
    · exact h0
  have := h n hn0
  rw [div_lt_iff₀ ha] at hn
  linarith

 

theorem pl_dyadic_rate_of_ratioUniform (hRU : PLRatioUniform) (hS4 : Iface.DG20Section4)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q) {D : LQGMetric.DistC → LSCMetric}
    {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} (hD : Iface.IsPfeWeakMetric ξ D c)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε)) :
    ∃ k : ℝ, 0 ≤ k ∧ ∀ n : ℕ,
      Real.exp (-k) * (dyad n : ℝ) ^ ((ξ : ℝ) * Q) ≤ c (dyad n) ∧
        (c (dyad n) : ℝ) ≤ Real.exp k * (dyad n : ℝ) ^ ((ξ : ℝ) * Q) := by
  obtain ⟨K, hK, hsub⟩ := pl_submult_of_ratioUniform hRU ξ Q hQ hD m hm
  set κ := 3 * Real.log K
  have hκ : 0 ≤ κ := by have := Real.log_pos hK; positivity
  set x : ℕ → ℝ := fun n => Real.log (c (dyad n))
  obtain ⟨β, hβ⟩ := bounded_additive_real_slope x κ hκ (log_c_dyad_bounded_additive hK hsub)
  have hβn : ∀ n : ℕ, 0 < n → |x n - β * n| ≤ κ := fun n hn => by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := hβ n hn
    have e : x n - β * n = (x n / n - β) * n := by field_simp
    rw [e, abs_mul, abs_of_pos hn']
    calc |x n / ↑n - β| * ↑n ≤ κ / n * n := mul_le_mul_of_nonneg_right h hn'.le
      _ = κ := by field_simp
  
  obtain ⟨C, hC, hR⟩ := ratioUniform_half hRU ξ Q hQ hD m hm
  obtain ⟨εs, hεs, hb⟩ := hR 1 le_rfl
  have hS := (hS4 ξ Q hQ m hm).2.1
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have key : ∀ ζ : ℝ, 0 < ζ → ∃ L : ℝ, ∀ n : ℕ, 0 < n →
      x n ≤ L - ((ξ : ℝ) * Q - ζ) * (n * Real.log 2) ∧
        -L - ((ξ : ℝ) * Q + ζ) * (n * Real.log 2) ≤ x n := by
    intro ζ hζ
    obtain ⟨C', hC', hC'b⟩ := hS ζ hζ
    refine ⟨Real.log C + Real.log C', fun n hn => ?_⟩
    set r := dyad n
    have hr0 : (0 : ℝ) < r := r.2
    have hr1 : (r : ℝ) < 1 := by
      show (2 : ℝ)⁻¹ ^ n < 1
      exact pow_lt_one₀ (by norm_num) (by norm_num) hn.ne'
    set e0 : ℝ := min εs (min (((r : ℝ) / 100) ^ 2) ((r : ℝ) / 2))
    have he0 : 0 < e0 := lt_min hεs (lt_min (by positivity) (by positivity))
    have he1 : e0 ≤ εs := min_le_left _ _
    have he2 : e0 ≤ ((r : ℝ) / 100) ^ 2 := (min_le_right _ _).trans (min_le_left _ _)
    have he3 : e0 < r := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
    obtain ⟨a1, a2⟩ := hb ⟨e0, he0⟩ r he1 he2 hr1.le
    obtain ⟨d1, d2⟩ := hC'b ⟨r, hr0, hr1⟩ ⟨e0, he0, he3⟩
    have hbF : bF m ⟨e0, he0⟩ r = (r : ℝ) * (m ⟨e0 / r, Set.mem_Ioi.mpr (div_pos he0 hr0)⟩ : ℝ) /
        (m ⟨e0, Set.mem_Ioi.mpr he0⟩ : ℝ) := rfl
    have hcpos : (0 : ℝ) < c r := (c r).2
    have hbpos := bF_pos m ⟨e0, he0⟩ r
    have hlr : Real.log (r : ℝ) = -(n * Real.log 2) := log_dyad n
    have hC0 : 0 < C := by linarith
    have hCinv : 0 < C⁻¹ := inv_pos.2 hC0
    have hC'inv : 0 < C'⁻¹ := inv_pos.2 hC'
    constructor
    · 
      have h0 : (c r : ℝ) ≤ C * bF m ⟨e0, he0⟩ r := by
        rw [inv_mul_le_iff₀ hC0] at a1; exact a1
      have h1 : (c r : ℝ) ≤ C * (C' * (r : ℝ) ^ ((ξ : ℝ) * Q - ζ)) :=
        h0.trans (mul_le_mul_of_nonneg_left (by rw [hbF]; exact d2) hC0.le)
      have := Real.log_le_log hcpos h1
      rw [Real.log_mul hC0.ne' (by positivity), Real.log_mul hC'.ne' (by positivity),
        Real.log_rpow hr0, hlr] at this
      show Real.log (c r) ≤ _
      linarith
    · 
      have h0 : C⁻¹ * bF m ⟨e0, he0⟩ r ≤ c r := by
        calc C⁻¹ * bF m ⟨e0, he0⟩ r ≤ C⁻¹ * (C * c r) := mul_le_mul_of_nonneg_left a2 hCinv.le
          _ = c r := by field_simp
      have h1 : C⁻¹ * (C'⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q + ζ)) ≤ c r :=
        le_trans (mul_le_mul_of_nonneg_left (by rw [hbF]; exact d1) hCinv.le) h0
      have hpos : 0 < C⁻¹ * (C'⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q + ζ)) := by positivity
      have := Real.log_le_log hpos h1
      rw [Real.log_mul hCinv.ne' (by positivity), Real.log_mul hC'inv.ne' (by positivity),
        Real.log_inv, Real.log_inv, Real.log_rpow hr0, hlr] at this
      show _ ≤ Real.log (c r)
      linarith
  
  have hup : ∀ ζ : ℝ, 0 < ζ → β ≤ -(((ξ : ℝ) * Q - ζ) * Real.log 2) := by
    intro ζ hζ
    obtain ⟨L, hL⟩ := key ζ hζ
    have : β + ((ξ : ℝ) * Q - ζ) * Real.log 2 ≤ 0 := by
      refine nonpos_of_mul_le (b := L + κ) fun n hn => ?_
      have h1 := (hL n hn).1
      have h2 := hβn n hn
      rw [abs_le] at h2
      nlinarith [h2.1]
    linarith
  have hlow : ∀ ζ : ℝ, 0 < ζ → -(((ξ : ℝ) * Q + ζ) * Real.log 2) ≤ β := by
    intro ζ hζ
    obtain ⟨L, hL⟩ := key ζ hζ
    have : -(β + ((ξ : ℝ) * Q + ζ) * Real.log 2) ≤ 0 := by
      refine nonpos_of_mul_le (b := L + κ) fun n hn => ?_
      have h1 := (hL n hn).2
      have h2 := hβn n hn
      rw [abs_le] at h2
      nlinarith [h2.2]
    linarith
  have hβeq : β = -((ξ : ℝ) * Q * Real.log 2) := by
    apply le_antisymm
    · refine le_of_forall_pos_lt_add fun δ hδ => ?_
      have := hup (δ / (2 * Real.log 2)) (by positivity)
      have e : (δ / (2 * Real.log 2)) * Real.log 2 = δ / 2 := by field_simp
      nlinarith
    · refine le_of_forall_pos_lt_add fun δ hδ => ?_
      have := hlow (δ / (2 * Real.log 2)) (by positivity)
      have e : (δ / (2 * Real.log 2)) * Real.log 2 = δ / 2 := by field_simp
      nlinarith
  
  refine ⟨max κ |x 0|, le_max_of_le_left hκ, fun n => ?_⟩
  have hdev : |x n + (ξ : ℝ) * Q * (n * Real.log 2)| ≤ max κ |x 0| := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · have := hβn n h0
      rw [hβeq] at this
      refine (le_of_eq ?_).trans (this.trans (le_max_left _ _))
      congr 1; ring
  have hr0 : (0 : ℝ) < dyad n := (dyad n).2
  have hcpos : (0 : ℝ) < c (dyad n) := (c _).2
  have hpow : (0 : ℝ) < (dyad n : ℝ) ^ ((ξ : ℝ) * Q) := Real.rpow_pos_of_pos hr0 _
  have hlogq : Real.log ((c (dyad n) : ℝ) / (dyad n : ℝ) ^ ((ξ : ℝ) * Q)) =
      x n + (ξ : ℝ) * Q * (n * Real.log 2) := by
    rw [Real.log_div hcpos.ne' hpow.ne', Real.log_rpow hr0, log_dyad]; ring
  rw [← hlogq, abs_le] at hdev
  have hq := div_pos hcpos hpow
  constructor
  · have := Real.exp_le_exp.2 hdev.1
    rw [Real.exp_log hq, le_div_iff₀ hpow] at this
    linarith
  · have := Real.exp_le_exp.2 hdev.2
    rw [Real.exp_log hq, div_le_iff₀ hpow] at this
    linarith

end SupercriticalLQGUniqueness.B2.Polylog
