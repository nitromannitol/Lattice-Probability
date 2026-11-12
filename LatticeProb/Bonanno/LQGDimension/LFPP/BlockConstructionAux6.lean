/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.BlockConstructionAux6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.BlockConstructionAux5

/-!
# Node `B57`, auxiliary file 6: the exact recursion (5.7)

For the child `(a, i)` (similarity `T = T^{f_a}_i` of ratio `r`) and a point `p ∈ S k`, the
depth-`(k+1)` field at `T p` splits into four bands:
`(ε_{k+1}, ρ] = (4ρ/M, ρ] ∪ (rρ, 4ρ/M] ∪ (rε_k, rρ] ∪ (ε_{k+1}, rε_k]`
(triples `qX`, `qY1`, `qC = tau a i (ε_k, ρ, p)`, `qY2`).  The root band decides the profile,
the band `qC` is the child's own field (its law is that of the depth-`k` field, by similarity
invariance), and the two unused bands have total variance `log 4`.  Independence of the three
groups gives the exact recursion

`m_{k+1} = 4^{ξ²/2} E min_a C_{f_a}(M_k)`   (`Good.step`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped RealInnerProductSpace Classical

namespace LQGDimension.BlockCons

open Blueprint.Draft

theorem exp_split4 (ξ A B C D : ℝ) :
    Real.exp (ξ * (A + B + C + D)) = Real.exp (ξ * A) * (Real.exp (ξ * (B + D)) * Real.exp (ξ * C)) := by
  rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- Linear relations with four terms are inherited by Gram vectors. -/
theorem gram_eq_add4 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Finset Tri) (β : Tri → E) (hβ : ∀ q ∈ F, ∀ q' ∈ F, ⟪β q, β q'⟫ = kap q q')
    (q q1 q2 q3 q4 : Tri) (hq : q ∈ F) (h1 : q1 ∈ F) (h2 : q2 ∈ F) (h3 : q3 ∈ F) (h4 : q4 ∈ F)
    (hrel : ∀ q' ∈ F, kap q q' = kap q1 q' + kap q2 q' + kap q3 q' + kap q4 q') :
    β q = β q1 + β q2 + β q3 + β q4 := by
  have h0 : ∀ q' ∈ F, ⟪β q', β q - (β q1 + β q2 + β q3 + β q4)⟫ = 0 := by
    intro q' hq'
    simp only [inner_sub_right, inner_add_right]
    rw [hβ q' hq' q hq, hβ q' hq' q1 h1, hβ q' hq' q2 h2, hβ q' hq' q3 h3, hβ q' hq' q4 h4,
      kap_comm q' q, kap_comm q' q1, kap_comm q' q2, kap_comm q' q3, kap_comm q' q4,
      hrel q' hq']
    ring
  have hvv : ⟪β q - (β q1 + β q2 + β q3 + β q4), β q - (β q1 + β q2 + β q3 + β q4)⟫ = 0 := by
    rw [inner_sub_left, inner_add_left, inner_add_left, inner_add_left, h0 q hq, h0 q1 h1,
      h0 q2 h2, h0 q3 h3, h0 q4 h4]
    ring
  exact sub_eq_zero.1 (inner_self_eq_zero.1 hvv)

namespace BParams

variable {P : BParams}

/-! ## The four bands at a child point -/

variable (P) in
def qX (a : Fin (P.K + 1)) (i : ℕ) (p : ℂ) : Tri := (P.top, P.ρ, app (P.sim a i) p)

variable (P) in
def qY1 (a : Fin (P.K + 1)) (i : ℕ) (p : ℂ) : Tri := (P.rr a i * P.ρ, P.top, app (P.sim a i) p)

variable (P) in
def qY2 (k : ℕ) (a : Fin (P.K + 1)) (i : ℕ) (p : ℂ) : Tri :=
  (P.eps (k + 1), P.rr a i * P.eps k, app (P.sim a i) p)

variable (P) in
def qC (k : ℕ) (a : Fin (P.K + 1)) (i : ℕ) (p : ℂ) : Tri := P.tau a i (P.eps k, P.ρ, p)

variable (P) in
def qT (k : ℕ) (a : Fin (P.K + 1)) (i : ℕ) (p : ℂ) : Tri := (P.eps (k + 1), P.ρ, app (P.sim a i) p)

theorem Good.kap_rel (hP : P.Good) (k : ℕ) (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) (p : ℂ)
    (q' : Tri) :
    kap (P.qT k a i p) q' = kap (P.qX a i p) q' + kap (P.qY1 a i p) q' + kap (P.qC k a i p) q' +
      kap (P.qY2 k a i p) q' := by
  have hr := hP.rr_pos a hi
  have h1 : P.eps (k + 1) ≤ P.rr a i * P.eps k := hP.eps_succ_le a hi k le_rfl
  have h2 : P.rr a i * P.eps k ≤ P.rr a i * P.ρ := mul_le_mul_of_nonneg_left (hP.eps_le k) hr.le
  have h3 : P.rr a i * P.ρ ≤ P.top := hP.rr_mul_le_top a hi hP.ρ_pos.le le_rfl
  have h4 : P.top ≤ P.ρ := hP.top_le
  have hpos1 := hP.eps_pos (k + 1)
  have hpos2 : 0 < P.rr a i * P.eps k := mul_pos hr (hP.eps_pos k)
  have hpos3 : 0 < P.rr a i * P.ρ := mul_pos hr hP.ρ_pos
  unfold qT qX qY1 qC qY2 tau
  simp only
  rw [kap_split hpos1 h1 (h2.trans (h3.trans h4)), kap_split hpos2 h2 (h3.trans h4),
    kap_split hpos3 h3 h4]
  ring

theorem mem_qT {k : ℕ} (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) {p : ℂ} (hp : p ∈ P.S k) :
    P.qT k a i p ∈ P.Qs (k + 1) := mem_Qs_tot (sim_mem_S a hi hp)

theorem mem_qX {k : ℕ} (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) {p : ℂ} (hp : p ∈ P.S k) :
    P.qX a i p ∈ P.XS k := mem_XS (sim_mem_S a hi hp)

theorem XS_subset (k : ℕ) : P.XS k ⊆ P.Qs (k + 1) := by
  intro q hq
  simp only [Qs, Finset.mem_union]
  exact Or.inl (Or.inl hq)

theorem mem_qY1 {k : ℕ} (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) {p : ℂ} (hp : p ∈ P.S k) :
    P.qY1 a i p ∈ P.Qs (k + 1) := mem_Qs_succ_Y1 a hi hp

theorem mem_qY2 {k : ℕ} (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) {p : ℂ} (hp : p ∈ P.S k) :
    P.qY2 k a i p ∈ P.Qs (k + 1) := mem_Qs_succ_Y2 a hi hp

theorem mem_qC {k : ℕ} (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) {p : ℂ} (hp : p ∈ P.S k) :
    P.qC k a i p ∈ P.Qs (k + 1) := mem_Qs_succ_tau a hi (mem_Qs_tot hp)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem Good.gram_rel (hP : P.Good) (k : ℕ) {β : Tri → E}
    (hβ : ∀ q ∈ P.Qs (k + 1), ∀ q' ∈ P.Qs (k + 1), ⟪β q, β q'⟫ = kap q q')
    (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) {p : ℂ} (hp : p ∈ P.S k) :
    β (P.qT k a i p) = β (P.qX a i p) + β (P.qY1 a i p) + β (P.qC k a i p) +
      β (P.qY2 k a i p) :=
  gram_eq_add4 (P.Qs (k + 1)) β hβ _ _ _ _ _ (mem_qT a hi hp) (XS_subset k (mem_qX a hi hp))
    (mem_qY1 a hi hp) (mem_qC a hi hp) (mem_qY2 a hi hp) fun q' _ => hP.kap_rel k a hi p q'

theorem Good.field_rel (hP : P.Good) (k : ℕ) {β : Tri → E}
    (hβ : ∀ q ∈ P.Qs (k + 1), ∀ q' ∈ P.Qs (k + 1), ⟪β q, β q'⟫ = kap q q') (x : E)
    (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) {p : ℂ} (hp : p ∈ P.S k) :
    Yf β x (P.qT k a i p) = Yf β x (P.qX a i p) + Yf β x (P.qY1 a i p) + Yf β x (P.qC k a i p) +
      Yf β x (P.qY2 k a i p) := by
  simp only [Yf]
  rw [hP.gram_rel k hβ a hi hp, inner_add_left, inner_add_left, inner_add_left]

/-! ## The three factors -/

variable (P) in
/-- Root factor: the choice indicator times the root-band weight. -/
def Aφ (k : ℕ) (a : Fin (P.K + 1)) (i : ℕ) (p : ℂ) (Y : Tri → ℝ) : ℝ :=
  (if amin (P.bcs k (P.Mw k) Y) = a then 1 else 0) * Real.exp (P.ξ * Y (P.qX a i p))

variable (P) in
/-- Unused-bands factor. -/
def Bφ (k : ℕ) (a : Fin (P.K + 1)) (i : ℕ) (p : ℂ) (Y : Tri → ℝ) : ℝ :=
  Real.exp (P.ξ * (Y (P.qY1 a i p) + Y (P.qY2 k a i p)))

variable (P) in
/-- Child factor: the child's own weighted occupation. -/
def Cφ (k : ℕ) (a : Fin (P.K + 1)) (i : ℕ) (p : ℂ) (Y : Tri → ℝ) : ℝ :=
  P.occ k p fun q => Y (P.tau a i q)

theorem bcs_eq (k : ℕ) (w : ℂ → ℝ) (Y : Tri → ℝ) (a : Fin (P.K + 1)) :
    P.bcs k w Y a = ∑ i : Fin P.M, ∑ p ∈ P.S k,
      P.rr a i * (w p * Real.exp (P.ξ * Y (P.qX a i p))) := by
  unfold bcs blockCost
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [P.edgeSim_eq]
  rfl

theorem bcs_amin_eq (k : ℕ) (Y : Tri → ℝ) :
    P.bcs k (P.Mw k) Y (amin (P.bcs k (P.Mw k) Y)) =
      ∑ a, ∑ i : Fin P.M, ∑ p ∈ P.S k, P.rr a i * (P.Mw k p * P.Aφ k a i p Y) := by
  have : ∀ a, ∑ i : Fin P.M, ∑ p ∈ P.S k, P.rr a i * (P.Mw k p * P.Aφ k a i p Y) =
      if amin (P.bcs k (P.Mw k) Y) = a then P.bcs k (P.Mw k) Y a else 0 := by
    intro a
    unfold Aφ
    by_cases h : amin (P.bcs k (P.Mw k) Y) = a
    · rw [if_pos h, bcs_eq]
      simp [h]
    · rw [if_neg h]
      simp [h]
  rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_ite_eq]
  simp

theorem Good.RC_succ_eq (hP : P.Good) (k : ℕ) (Y : Tri → ℝ)
    (hrel : ∀ a, ∀ i < P.M, ∀ p ∈ P.S k,
      Y (P.qT k a i p) = Y (P.qX a i p) + Y (P.qY1 a i p) + Y (P.qC k a i p) + Y (P.qY2 k a i p)) :
    P.RC (k + 1) Y = ∑ a, ∑ i : Fin P.M, ∑ p ∈ P.S k,
      P.rr a i * (P.Aφ k a i p Y * (P.Bφ k a i p Y * P.Cφ k a i p Y)) := by
  set d := P.dec (k + 1) Y with hd
  set a0 := amin (P.bcs k (P.Mw k) Y) with ha0
  have hdfst : d.fst = a0 := rfl
  have hdsnd : ∀ i, d.snd i = P.dec k (fun q => Y (P.tau a0 i q)) := fun i => rfl
  have hL : P.RC (k + 1) Y = ∑ i : Fin P.M, ∑ p ∈ P.S k, P.rr a0 i *
      (Real.exp (P.ξ * Y (P.qX a0 i p)) * (P.Bφ k a0 i p Y * P.Cφ k a0 i p Y)) := by
    unfold RC
    rw [riemannCost_eq_rcW]
    change rcW P.N (glueFn P.M fun i => (P.polyOf k (d.snd i)).map (app (P.sim d.fst i))) _ = _
    rw [rcW_glueFn _ _ _ (hP.pieces_ne_nil k d) (hP.junction k d)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rcW_map_app, rcW_eq_sum_dlt _ _ _ (hP.riemannPts_subset k _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [rcW_dlt, hdfst]
    unfold Bφ Cφ
    rw [occ_eq, hdsnd]
    have hr := hrel a0 i i.2 p hp
    simp only [qT] at hr
    try dsimp only
    rw [hr, exp_split4]
    simp only [qC, rr]
    ring
  rw [hL]
  have : ∀ a, ∑ i : Fin P.M, ∑ p ∈ P.S k,
      P.rr a i * (P.Aφ k a i p Y * (P.Bφ k a i p Y * P.Cφ k a i p Y)) =
      if a0 = a then ∑ i : Fin P.M, ∑ p ∈ P.S k, P.rr a i *
        (Real.exp (P.ξ * Y (P.qX a i p)) * (P.Bφ k a i p Y * P.Cφ k a i p Y)) else 0 := by
    intro a
    unfold Aφ
    rw [← ha0]
    by_cases h : a0 = a
    · rw [if_pos h]
      simp [h]
    · rw [if_neg h]
      simp [h]
  rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_ite_eq]
  simp

/-! ## Measurability and locality of the factors -/

theorem measurable_Aφ (k : ℕ) (a : Fin (P.K + 1)) (i : ℕ) (p : ℂ) : Measurable (P.Aφ k a i p) := by
  unfold Aφ
  refine Measurable.mul ?_ (measurable_exp_eval _ _)
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_amin_eq (fun b Y => P.bcs k (P.Mw k) Y b) (fun b => measurable_bcs k _ b) a

theorem measurable_Bφ (k : ℕ) (a : Fin (P.K + 1)) (i : ℕ) (p : ℂ) : Measurable (P.Bφ k a i p) := by
  unfold Bφ
  have h1 : Measurable fun Y : Tri → ℝ => Y (P.qY1 a i p) := measurable_pi_apply _
  have h2 : Measurable fun Y : Tri → ℝ => Y (P.qY2 k a i p) := measurable_pi_apply _
  have h3 : Measurable fun Y : Tri → ℝ => P.ξ * (Y (P.qY1 a i p) + Y (P.qY2 k a i p)) :=
    measurable_const.mul (h1.add h2)
  exact h3.exp

theorem measurable_Cφ (k : ℕ) (a : Fin (P.K + 1)) (i : ℕ) (p : ℂ) : Measurable (P.Cφ k a i p) :=
  (measurable_occ k p).comp (measurable_comp_tri _)

theorem bcs_loc (k : ℕ) (w : ℂ → ℝ) (Y Y' : Tri → ℝ) (h : ∀ q ∈ P.XS k, Y q = Y' q) :
    P.bcs k w Y = P.bcs k w Y' := by
  funext a
  rw [bcs_eq, bcs_eq]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p hp => ?_
  rw [h _ (mem_qX a i.2 hp)]

theorem Aφ_loc (k : ℕ) (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) {p : ℂ} (hp : p ∈ P.S k) :
    IsLoc (P.XS k) (P.Aφ k a i p) := by
  intro Y Y' h
  unfold Aφ
  rw [bcs_loc k _ Y Y' h, h _ (mem_qX a hi hp)]

theorem Bφ_loc (k : ℕ) (a : Fin (P.K + 1)) (i : ℕ) (p : ℂ) :
    IsLoc {P.qY1 a i p, P.qY2 k a i p} (P.Bφ k a i p) := by
  intro Y Y' h
  unfold Bφ
  rw [h (P.qY1 a i p) (by simp), h (P.qY2 k a i p) (by simp)]

theorem Good.Cφ_loc (hP : P.Good) (k : ℕ) (a : Fin (P.K + 1)) (i : ℕ) (p : ℂ) :
    IsLoc ((P.Qs k).image (P.tau a i)) (P.Cφ k a i p) := by
  intro Y Y' h
  unfold Cφ
  exact hP.occ_loc k p _ _ fun q hq => h _ (Finset.mem_image_of_mem _ hq)

/-! ## Orthogonality -/

theorem Good.orth_X (hP : P.Good) (k : ℕ) {β : Tri → E}
    (hβ : ∀ q ∈ P.Qs (k + 1), ∀ q' ∈ P.Qs (k + 1), ⟪β q, β q'⟫ = kap q q')
    (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) {p : ℂ} (hp : p ∈ P.S k) :
    ∀ q ∈ P.XS k, ∀ q' ∈ ({P.qY1 a i p, P.qY2 k a i p} ∪ (P.Qs k).image (P.tau a i) : Finset Tri),
      ⟪β q, β q'⟫ = 0 := by
  intro q hq q' hq'
  have hqQ : q ∈ P.Qs (k + 1) := XS_subset k hq
  have hq1 : q.1 = P.top := by
    simp only [XS, Finset.mem_image] at hq
    obtain ⟨z, -, rfl⟩ := hq
    rfl
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image] at hq'
  rcases hq' with (rfl | rfl) | ⟨q'', hq'', rfl⟩
  · rw [hβ q hqQ _ (mem_qY1 a hi hp)]
    exact kap_eq_zero_of_le' (by rw [hq1]; exact le_rfl)
  · rw [hβ q hqQ _ (mem_qY2 a hi hp)]
    refine kap_eq_zero_of_le' ?_
    rw [hq1]
    exact hP.rr_mul_le_top a hi (hP.eps_pos k).le (hP.eps_le k)
  · rw [hβ q hqQ _ (mem_Qs_succ_tau a hi hq'')]
    refine kap_eq_zero_of_le' ?_
    rw [hq1]
    obtain ⟨h1, h2, h3⟩ := hP.Qs_band k q'' hq''
    exact hP.rr_mul_le_top a hi (by linarith [hP.eps_pos k]) h3

theorem Good.orth_BC (hP : P.Good) (k : ℕ) {β : Tri → E}
    (hβ : ∀ q ∈ P.Qs (k + 1), ∀ q' ∈ P.Qs (k + 1), ⟪β q, β q'⟫ = kap q q')
    (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) {p : ℂ} (hp : p ∈ P.S k) :
    ∀ q ∈ ({P.qY1 a i p, P.qY2 k a i p} : Finset Tri), ∀ q' ∈ (P.Qs k).image (P.tau a i),
      ⟪β q, β q'⟫ = 0 := by
  intro q hq q' hq'
  obtain ⟨q'', hq'', rfl⟩ := Finset.mem_image.1 hq'
  have hr := hP.rr_pos a hi
  obtain ⟨h1, h2, h3⟩ := hP.Qs_band k q'' hq''
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · rw [hβ _ (mem_qY1 a hi hp) _ (mem_Qs_succ_tau a hi hq'')]
    exact kap_eq_zero_of_le' (mul_le_mul_of_nonneg_left h3 hr.le)
  · rw [hβ _ (mem_qY2 a hi hp) _ (mem_Qs_succ_tau a hi hq'')]
    exact kap_eq_zero_of_le (mul_le_mul_of_nonneg_left h1 hr.le)

/-! ## The expectations of the factors -/

theorem Good.integral_Bφ (hP : P.Good) (k : ℕ) {β : Tri → E}
    (hβ : ∀ q ∈ P.Qs (k + 1), ∀ q' ∈ P.Qs (k + 1), ⟪β q, β q'⟫ = kap q q')
    (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) {p : ℂ} (hp : p ∈ P.S k) :
    ∫ x, P.Bφ k a i p (Yf β x) ∂stdGaussian E = (4 : ℝ) ^ (P.ξ ^ 2 / 2) := by
  have hr := hP.rr_pos a hi
  have hfun : (fun x => P.Bφ k a i p (Yf β x)) =
      fun x => Real.exp (P.ξ * ⟪β (P.qY1 a i p) + β (P.qY2 k a i p), x⟫) := by
    funext x
    simp only [Bφ, Yf, inner_add_left]
  rw [hfun, integral_exp_inner]
  have h11 : ⟪β (P.qY1 a i p), β (P.qY1 a i p)⟫ = Real.log (P.top / (P.rr a i * P.ρ)) := by
    rw [hβ _ (mem_qY1 a hi hp) _ (mem_qY1 a hi hp)]
    exact kap_diag (mul_pos hr hP.ρ_pos) (hP.rr_mul_le_top a hi hP.ρ_pos.le le_rfl) _
  have h22 : ⟪β (P.qY2 k a i p), β (P.qY2 k a i p)⟫ =
      Real.log (P.rr a i * P.eps k / P.eps (k + 1)) := by
    rw [hβ _ (mem_qY2 a hi hp) _ (mem_qY2 a hi hp)]
    exact kap_diag (hP.eps_pos _) (hP.eps_succ_le a hi k le_rfl) _
  have h12 : ⟪β (P.qY1 a i p), β (P.qY2 k a i p)⟫ = 0 := by
    rw [hβ _ (mem_qY1 a hi hp) _ (mem_qY2 a hi hp)]
    exact kap_eq_zero_of_le' (mul_le_mul_of_nonneg_left (hP.eps_le k) hr.le)
  have hnorm : ‖β (P.qY1 a i p) + β (P.qY2 k a i p)‖ ^ 2 = Real.log 4 := by
    rw [norm_add_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, h11, h22,
      h12, mul_zero, add_zero, ← Real.log_mul]
    · congr 1
      rw [eps_succ, top]
      have hM := hP.M_pos.ne'
      have he := (hP.eps_pos k).ne'
      have hρ := hP.ρ_pos.ne'
      have hr' := hr.ne'
      first
        | (field_simp; ring)
        | field_simp
    · exact (div_pos hP.top_pos (mul_pos hr hP.ρ_pos)).ne'
    · exact (div_pos (mul_pos hr (hP.eps_pos k)) (hP.eps_pos _)).ne'
  rw [hnorm, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4)]
  congr 1
  ring

theorem Good.gram_tau (hP : P.Good) (k : ℕ) {β : Tri → E}
    (hβ : ∀ q ∈ P.Qs (k + 1), ∀ q' ∈ P.Qs (k + 1), ⟪β q, β q'⟫ = kap q q')
    (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) :
    ∀ q ∈ P.Qs k, ∀ q' ∈ P.Qs k, ⟪β (P.tau a i q), β (P.tau a i q')⟫ = kap q q' := by
  intro q hq q' hq'
  rw [hβ _ (mem_Qs_succ_tau a hi hq) _ (mem_Qs_succ_tau a hi hq')]
  exact kap_sim (hP.rr_pos a hi) (app (P.sim a i)) (P.app_sim_sub a i) q q'

theorem Good.integral_Cφ (hP : P.Good) (k : ℕ) {β : Tri → E}
    (hβ : ∀ q ∈ P.Qs (k + 1), ∀ q' ∈ P.Qs (k + 1), ⟪β q, β q'⟫ = kap q q')
    (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) (p : ℂ) :
    ∫ x, P.Cφ k a i p (Yf β x) ∂stdGaussian E = P.Mw k p := by
  have := transfer_integral (P.Qs k) (fun q => β (P.tau a i q)) (hP.gram_tau k hβ a hi)
    (measurable_occ k p) (hP.occ_loc k p)
  rw [Mw_eq, ← this]
  rfl

/-! ## Integrability of the terms -/

theorem Good.integrable_Aφ (hP : P.Good) (k : ℕ) (β : Tri → E) (a : Fin (P.K + 1)) (i : ℕ)
    (p : ℂ) : Integrable (fun x => P.Aφ k a i p (Yf β x)) (stdGaussian E) := by
  refine integrable_of_le_exp (((measurable_Aφ k a i p).comp (measurable_Yf β)).aestronglyMeasurable)
    1 P.ξ (β (P.qX a i p)) fun x => ?_
  simp only [Function.comp, Aφ, one_mul]
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_of_le_one_left (Real.exp_pos _).le ?_
  split_ifs <;> norm_num

theorem Good.integrable_ABC (hP : P.Good) (k : ℕ) {β : Tri → E}
    (hβ : ∀ q ∈ P.Qs (k + 1), ∀ q' ∈ P.Qs (k + 1), ⟪β q, β q'⟫ = kap q q')
    (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) {p : ℂ} (hp : p ∈ P.S k) :
    Integrable (fun x => P.Aφ k a i p (Yf β x) * (P.Bφ k a i p (Yf β x) * P.Cφ k a i p (Yf β x)))
      (stdGaussian E) := by
  refine integrable_of_le_exp ((((measurable_Aφ k a i p).mul ((measurable_Bφ k a i p).mul
    (measurable_Cφ k a i p))).comp (measurable_Yf β)).aestronglyMeasurable)
    (P.Lb k p) P.ξ (β (P.qT k a i p)) fun x => ?_
  have hA0 : 0 ≤ P.Aφ k a i p (Yf β x) := by
    unfold Aφ; split_ifs <;> positivity
  have hA : P.Aφ k a i p (Yf β x) ≤ Real.exp (P.ξ * Yf β x (P.qX a i p)) := by
    unfold Aφ
    refine mul_le_of_le_one_left (Real.exp_pos _).le ?_
    split_ifs <;> norm_num
  have hB0 : 0 ≤ P.Bφ k a i p (Yf β x) := (Real.exp_pos _).le
  have hC0 : 0 ≤ P.Cφ k a i p (Yf β x) := occ_nonneg _ _ _
  have hC : P.Cφ k a i p (Yf β x) ≤ P.Lb k p * Real.exp (P.ξ * Yf β x (P.qC k a i p)) :=
    occ_le k p _
  have hrel := hP.field_rel k hβ x a hi hp
  rw [abs_of_nonneg (mul_nonneg hA0 (mul_nonneg hB0 hC0))]
  have hexp : Real.exp (P.ξ * ⟪β (P.qT k a i p), x⟫) = Real.exp (P.ξ * Yf β x (P.qX a i p)) *
      (P.Bφ k a i p (Yf β x) * Real.exp (P.ξ * Yf β x (P.qC k a i p))) := by
    change Real.exp (P.ξ * Yf β x (P.qT k a i p)) = _
    rw [hrel, exp_split4]
    rfl
  rw [hexp]
  calc P.Aφ k a i p (Yf β x) * (P.Bφ k a i p (Yf β x) * P.Cφ k a i p (Yf β x))
      ≤ Real.exp (P.ξ * Yf β x (P.qX a i p)) * (P.Bφ k a i p (Yf β x) *
          (P.Lb k p * Real.exp (P.ξ * Yf β x (P.qC k a i p)))) :=
        mul_le_mul hA (mul_le_mul_of_nonneg_left hC hB0) (mul_nonneg hB0 hC0) (Real.exp_pos _).le
    _ = P.Lb k p * (Real.exp (P.ξ * Yf β x (P.qX a i p)) * (P.Bφ k a i p (Yf β x) *
          Real.exp (P.ξ * Yf β x (P.qC k a i p)))) := by ring

/-! ## The recursion -/

/-- **The exact recursion (5.7)**, with the integrability of the depth-`(k+1)` cost. -/
theorem Good.step (hP : P.Good) (k : ℕ) {β : Tri → E}
    (hβ : ∀ q ∈ P.Qs (k + 1), ∀ q' ∈ P.Qs (k + 1), ⟪β q, β q'⟫ = kap q q') :
    Integrable (fun x => P.RC (k + 1) (Yf β x)) (stdGaussian E) ∧
    P.mm (k + 1) = (4 : ℝ) ^ (P.ξ ^ 2 / 2) *
      ∫ x, ⨅ a, P.bcs k (P.Mw k) (Yf β x) a ∂stdGaussian E := by
  have hpt : ∀ x, P.RC (k + 1) (Yf β x) = ∑ a, ∑ i : Fin P.M, ∑ p ∈ P.S k,
      P.rr a i * (P.Aφ k a i p (Yf β x) * (P.Bφ k a i p (Yf β x) * P.Cφ k a i p (Yf β x))) :=
    fun x => hP.RC_succ_eq k _ fun a i hi p hp => hP.field_rel k hβ x a hi hp
  -- integrability of the terms (terms with `p ∉ S k` do not occur)
  have hint : ∀ a (i : Fin P.M) (p : ℂ), p ∈ P.S k → Integrable (fun x => P.rr a i *
      (P.Aφ k a i p (Yf β x) * (P.Bφ k a i p (Yf β x) * P.Cφ k a i p (Yf β x))))
      (stdGaussian E) := fun a i p hp => (hP.integrable_ABC k hβ a i.2 hp).const_mul _
  have hsum_int : Integrable (fun x => ∑ a, ∑ i : Fin P.M, ∑ p ∈ P.S k,
      P.rr a i * (P.Aφ k a i p (Yf β x) * (P.Bφ k a i p (Yf β x) * P.Cφ k a i p (Yf β x))))
      (stdGaussian E) :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun p hp => hint a i p hp
  refine ⟨?_, ?_⟩
  · simp_rw [hpt]; exact hsum_int
  -- the recursion
  have hmm : P.mm (k + 1) = ∫ x, P.RC (k + 1) (Yf β x) ∂stdGaussian E :=
    (transfer_integral (P.Qs (k + 1)) β hβ (measurable_RC (k + 1)) (hP.RC_loc (k + 1))).symm
  have hterm : ∀ a (i : Fin P.M) (p : ℂ), p ∈ P.S k →
      ∫ x, P.rr a i * (P.Aφ k a i p (Yf β x) * (P.Bφ k a i p (Yf β x) * P.Cφ k a i p (Yf β x)))
        ∂stdGaussian E =
      P.rr a i * ((∫ x, P.Aφ k a i p (Yf β x) ∂stdGaussian E) *
        ((4 : ℝ) ^ (P.ξ ^ 2 / 2) * P.Mw k p)) := by
    intro a i p hp
    rw [integral_const_mul]
    congr 1
    have h1 := integral_mul_of_orth β (P.XS k) ({P.qY1 a i p, P.qY2 k a i p} ∪
        (P.Qs k).image (P.tau a i)) (hP.orth_X k hβ a i.2 hp) (Φ := P.Aφ k a i p)
        (Ψ := fun Y => P.Bφ k a i p Y * P.Cφ k a i p Y) (measurable_Aφ k a i p)
        ((measurable_Bφ k a i p).mul (measurable_Cφ k a i p)) (Aφ_loc k a i.2 hp)
        (fun Y Y' h => by
          change P.Bφ k a i p Y * P.Cφ k a i p Y = P.Bφ k a i p Y' * P.Cφ k a i p Y'
          rw [Bφ_loc k a i p Y Y' fun q hq => h q (Finset.mem_union_left _ hq),
            hP.Cφ_loc k a i p Y Y' fun q hq => h q (Finset.mem_union_right _ hq)])
    have h2 := integral_mul_of_orth β _ _ (hP.orth_BC k hβ a i.2 hp) (measurable_Bφ k a i p)
      (measurable_Cφ k a i p) (Bφ_loc k a i p) (hP.Cφ_loc k a i p)
    calc ∫ x, P.Aφ k a i p (Yf β x) * (P.Bφ k a i p (Yf β x) * P.Cφ k a i p (Yf β x))
          ∂stdGaussian E
        = (∫ x, P.Aφ k a i p (Yf β x) ∂stdGaussian E) *
            ∫ x, P.Bφ k a i p (Yf β x) * P.Cφ k a i p (Yf β x) ∂stdGaussian E := h1
      _ = (∫ x, P.Aφ k a i p (Yf β x) ∂stdGaussian E) *
            ((∫ x, P.Bφ k a i p (Yf β x) ∂stdGaussian E) *
              ∫ x, P.Cφ k a i p (Yf β x) ∂stdGaussian E) := by rw [h2]
      _ = _ := by rw [hP.integral_Bφ k hβ a i.2 hp, hP.integral_Cφ k hβ a i.2 p]
  have hL : P.mm (k + 1) = ∑ a, ∑ i : Fin P.M, ∑ p ∈ P.S k, P.rr a i *
      ((∫ x, P.Aφ k a i p (Yf β x) ∂stdGaussian E) * ((4 : ℝ) ^ (P.ξ ^ 2 / 2) * P.Mw k p)) := by
    rw [hmm]
    simp_rw [hpt]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun p hp => hint a i p hp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun p hp => hint a i p hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun p hp => hint a i p hp]
    exact Finset.sum_congr rfl fun p hp => hterm a i p hp
  have hR : ∫ x, ⨅ a, P.bcs k (P.Mw k) (Yf β x) a ∂stdGaussian E =
      ∑ a, ∑ i : Fin P.M, ∑ p ∈ P.S k, P.rr a i *
        (P.Mw k p * ∫ x, P.Aφ k a i p (Yf β x) ∂stdGaussian E) := by
    have hintA : ∀ a (i : Fin P.M) (p : ℂ), Integrable
        (fun x => P.rr a i * (P.Mw k p * P.Aφ k a i p (Yf β x))) (stdGaussian E) :=
      fun a i p => ((hP.integrable_Aφ k β a i p).const_mul _).const_mul _
    simp_rw [iInf_eq_amin, bcs_amin_eq]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun p _ => hintA a i p]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun p _ => hintA a i p]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun p _ => hintA a i p]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_const_mul, integral_const_mul]
  rw [hL, hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

end BParams

end LQGDimension.BlockCons
