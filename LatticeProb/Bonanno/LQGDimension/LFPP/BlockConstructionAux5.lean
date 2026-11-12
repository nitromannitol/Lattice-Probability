/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.BlockConstructionAux5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.BlockConstructionAux4

/-!
# Node `B57`, auxiliary file 5: locality, measurability, occupation measures

* `dec_loc`: the depth-`k` rule only reads the field on `Qs k`; `dec_meas`: it is measurable.
* `occ k p Y`: the Riemann-weighted occupation of the point `p` (integrand of `Mw k p`);
  its locality, measurability and exponential domination.
* `Mw_nonneg`, `mm_eq_sum` (`m_k = Σ_p M_k(p)`), `mm_zero` (`m_0 = 1`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped RealInnerProductSpace Classical

namespace LQGDimension.BlockCons

open Blueprint.Draft

/-! ## Measurability helpers -/

theorem measurable_list_sum {α : Type*} [MeasurableSpace α] (l : List (ℂ × ℂ))
    {F : α → ℂ × ℂ → ℝ} (hF : ∀ e, Measurable fun x => F x e) :
    Measurable fun x => (l.map (F x)).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil]; exact measurable_const
  | cons e l ih => simp only [List.map_cons, List.sum_cons]; exact (hF e).add ih

theorem measurable_rcW {α : Type*} [MeasurableSpace α] (N : ℕ) (z : List ℂ) {G : α → ℂ → ℝ}
    (hG : ∀ w, Measurable fun x => G x w) : Measurable fun x => rcW N z (G x) := by
  unfold rcW
  refine measurable_list_sum _ fun e => ?_
  unfold ew
  exact measurable_const.mul (Finset.measurable_sum _ fun q _ => hG _)

theorem measurable_comp_tri (τ : Tri → Tri) : Measurable fun Y : Tri → ℝ => fun q => Y (τ q) :=
  Measurable.of_eval fun q => measurable_pi_apply _

theorem measurable_exp_eval (ξ : ℝ) (q : Tri) :
    Measurable fun Y : Tri → ℝ => Real.exp (ξ * Y q) :=
  (measurable_const.mul (measurable_pi_apply q)).exp

theorem measurable_dlt_exp (ξ : ℝ) (p : ℂ) (f : ℂ → Tri) (w : ℂ) :
    Measurable fun Y : Tri → ℝ => dlt p (fun z => Real.exp (ξ * Y (f z))) w := by
  unfold dlt
  split_ifs
  · exact measurable_exp_eval ξ _
  · exact measurable_const

namespace BParams

variable {P : BParams}

theorem measurable_bcs (k : ℕ) (w : ℂ → ℝ) (a : Fin (P.K + 1)) :
    Measurable fun Y : Tri → ℝ => P.bcs k w Y a := by
  unfold bcs blockCost
  exact Finset.measurable_sum _ fun i _ => measurable_const.mul
    (Finset.measurable_sum _ fun z _ => measurable_const.mul (measurable_exp_eval _ _))

theorem measurable_dec : ∀ k, Measurable (P.dec k)
  | 0 => measurable_const
  | k + 1 => by
    refine measurable_to_countable' fun d => ?_
    have ih := measurable_dec k
    have hset : P.dec (k + 1) ⁻¹' {d} = {Y | amin (fun a => P.bcs k (P.Mw k) Y a) = d.fst} ∩
        ⋂ i : Fin P.M, (fun Y : Tri → ℝ => fun q => Y (P.tau d.fst i q)) ⁻¹'
          (P.dec k ⁻¹' {d.snd i}) := by
      ext Y
      simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_setOf_eq, mem_iInter]
      rw [dec_succ, DT.ext_iff']
      simp only [DT.fst_mk, DT.snd_mk]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun i => ?_⟩
        rw [← h1]
        exact congrFun h2 i
      · rintro ⟨h1, h2⟩
        refine ⟨h1, funext fun i => ?_⟩
        rw [h1]
        exact h2 i
    rw [hset]
    refine (measurableSet_amin_eq (fun a Y => P.bcs k (P.Mw k) Y a)
      (fun a => measurable_bcs k _ a) _).inter (MeasurableSet.iInter fun i => ?_)
    exact (ih.comp (measurable_comp_tri _)) (measurableSet_singleton _)

theorem measurable_of_dec {k : ℕ} {Φ : DT P.K P.M k → (Tri → ℝ) → ℝ}
    (hΦ : ∀ d, Measurable (Φ d)) : Measurable fun Y => Φ (P.dec k Y) Y := by
  have h : Measurable fun p : DT P.K P.M k × (Tri → ℝ) => Φ p.1 p.2 :=
    measurable_from_prod_countable_right fun d => hΦ d
  exact h.comp ((measurable_dec k).prodMk measurable_id)

/-! ## Locality -/

theorem Good.dec_loc (hP : P.Good) :
    ∀ k (Y Y' : Tri → ℝ), (∀ q ∈ P.Qs k, Y q = Y' q) → P.dec k Y = P.dec k Y'
  | 0, _, _, _ => rfl
  | k + 1, Y, Y', h => by
    have hb : P.bcs k (P.Mw k) Y = P.bcs k (P.Mw k) Y' := by
      funext a
      unfold bcs blockCost
      refine Finset.sum_congr rfl fun i hi => ?_
      congr 1
      refine Finset.sum_congr rfl fun z hz => ?_
      have hq := mem_Qs_succ_X (P := P) (sim_mem_S a (Finset.mem_range.1 hi) hz)
      rw [← P.edgeSim_eq] at hq
      simp only [h _ hq]
    rw [dec_succ, dec_succ, hb]
    congr 1
    funext i
    exact Good.dec_loc hP k _ _ fun q hq => h _ (mem_Qs_succ_tau _ i.2 hq)

/-! ## Occupation weights -/

/-- The Riemann-weighted occupation of `p` by the depth-`k` rule under the field `Y`. -/
def occ (P : BParams) (k : ℕ) (p : ℂ) (Y : Tri → ℝ) : ℝ :=
  rcW P.N (P.polyOf k (P.dec k Y)) (dlt p fun z => Real.exp (P.ξ * Y (P.eps k, P.ρ, z)))

theorem Mw_eq (k : ℕ) (p : ℂ) : P.Mw k p = ∫ Y, P.occ k p Y ∂gLaw (P.Qs k) := rfl

theorem occ_nonneg (k : ℕ) (p : ℂ) (Y : Tri → ℝ) : 0 ≤ P.occ k p Y :=
  rcW_nonneg _ _ fun w => by
    unfold dlt; split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl

theorem occ_eq (k : ℕ) (p : ℂ) (Y : Tri → ℝ) :
    P.occ k p Y = Real.exp (P.ξ * Y (P.eps k, P.ρ, p)) *
      rcW P.N (P.polyOf k (P.dec k Y)) (dlt p fun _ => 1) := by
  unfold occ
  rw [rcW_dlt]

theorem measurable_occ (k : ℕ) (p : ℂ) : Measurable (P.occ k p) :=
  measurable_of_dec (Φ := fun d Y => rcW P.N (P.polyOf k d)
    (dlt p fun z => Real.exp (P.ξ * Y (P.eps k, P.ρ, z))))
    fun d => measurable_rcW _ _ fun w => measurable_dlt_exp _ _ _ w

theorem Good.occ_loc (hP : P.Good) (k : ℕ) (p : ℂ) : IsLoc (P.Qs k) (P.occ k p) := by
  intro Y Y' h
  unfold occ
  rw [hP.dec_loc k Y Y' h]
  refine rcW_congr _ _ fun z hz => ?_
  have hzS : z ∈ P.S k := hP.riemannPts_subset k _ hz
  simp only [dlt]
  split_ifs
  · rw [h _ (mem_Qs_tot hzS)]
  · rfl

/-- A bound for the occupation weights of all depth-`k` polygons. -/
def Lb (P : BParams) (k : ℕ) (p : ℂ) : ℝ :=
  ∑ d : DT P.K P.M k, rcW P.N (P.polyOf k d) (dlt p fun _ => 1)

theorem rcW_le_Lb (k : ℕ) (p : ℂ) (d : DT P.K P.M k) :
    rcW P.N (P.polyOf k d) (dlt p fun _ => 1) ≤ P.Lb k p :=
  Finset.single_le_sum (f := fun d => rcW P.N (P.polyOf k d) (dlt p fun _ => 1))
    (fun d _ => rcW_nonneg _ _ (dlt_one_nonneg p)) (Finset.mem_univ d)

theorem occ_le (k : ℕ) (p : ℂ) (Y : Tri → ℝ) :
    P.occ k p Y ≤ P.Lb k p * Real.exp (P.ξ * Y (P.eps k, P.ρ, p)) := by
  rw [occ_eq, mul_comm (P.Lb k p)]
  exact mul_le_mul_of_nonneg_left (rcW_le_Lb k p _) (Real.exp_pos _).le

theorem Mw_nonneg (k : ℕ) (p : ℂ) : 0 ≤ P.Mw k p :=
  integral_nonneg fun Y => occ_nonneg k p Y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem integrable_occ_x (k : ℕ) (p : ℂ) (β : Tri → E) :
    Integrable (fun x => P.occ k p (Yf β x)) (stdGaussian E) := by
  refine integrable_of_le_exp (((measurable_occ k p).comp (measurable_Yf β)).aestronglyMeasurable)
    (P.Lb k p) P.ξ (β (P.eps k, P.ρ, p)) fun x => ?_
  rw [abs_of_nonneg (occ_nonneg k p _)]
  exact occ_le k p _

theorem Good.integrable_occ (hP : P.Good) (k : ℕ) (p : ℂ) {β : Tri → E}
    (hβ : ∀ q ∈ P.Qs k, ∀ q' ∈ P.Qs k, ⟪β q, β q'⟫ = kap q q') :
    Integrable (P.occ k p) (gLaw (P.Qs k)) :=
  (transfer_integrable (P.Qs k) β hβ (measurable_occ k p) (hP.occ_loc k p)).1
    (integrable_occ_x k p β)

/-! ## The Riemann cost -/

theorem RC_eq_sum (hP : P.Good) (k : ℕ) (Y : Tri → ℝ) :
    P.RC k Y = ∑ p ∈ P.S k, P.occ k p Y := by
  unfold RC occ
  rw [riemannCost_eq_rcW, rcW_eq_sum_dlt _ _ _ (hP.riemannPts_subset k _)]

theorem RC_eq_rcW (k : ℕ) : P.RC k = fun Y => rcW P.N (P.polyOf k (P.dec k Y))
    (fun w => Real.exp (P.ξ * Y (P.eps k, P.ρ, w))) := by
  funext Y
  exact riemannCost_eq_rcW _ _ _ _

theorem measurable_RC (k : ℕ) : Measurable (P.RC k) := by
  rw [RC_eq_rcW]
  exact measurable_of_dec (Φ := fun d Y => rcW P.N (P.polyOf k d)
    (fun w => Real.exp (P.ξ * Y (P.eps k, P.ρ, w))))
    fun d => measurable_rcW _ _ fun w => measurable_exp_eval _ _

theorem Good.RC_loc (hP : P.Good) (k : ℕ) : IsLoc (P.Qs k) (P.RC k) := by
  intro Y Y' h
  rw [RC_eq_sum hP, RC_eq_sum hP]
  exact Finset.sum_congr rfl fun p _ => hP.occ_loc k p Y Y' h

theorem Good.exists_gram (hP : P.Good) (k : ℕ) :
    ∃ d : ℕ, ∃ β : Tri → EuclideanSpace ℝ (Fin d),
      ∀ q ∈ P.Qs k, ∀ q' ∈ P.Qs k, ⟪β q, β q'⟫ = kap q q' :=
  exists_gram_kap (P.Qs k) (hP.Qs_pos k)

/-- `m_k = Σ_p M_k(p)`. -/
theorem Good.mm_eq_sum (hP : P.Good) (k : ℕ) : P.mm k = ∑ p ∈ P.S k, P.Mw k p := by
  obtain ⟨d, β, hβ⟩ := hP.exists_gram k
  unfold mm
  simp_rw [RC_eq_sum hP k]
  rw [integral_finsetSum _ fun p _ => hP.integrable_occ k p hβ]
  rfl

theorem Good.mm_nonneg (hP : P.Good) (k : ℕ) : 0 ≤ P.mm k := by
  rw [hP.mm_eq_sum]
  exact Finset.sum_nonneg fun p _ => Mw_nonneg k p

/-- `m_0 = 1`. -/
theorem Good.mm_zero (hP : P.Good) : P.mm 0 = 1 := by
  obtain ⟨d, β, hβ⟩ := hP.exists_gram 0
  unfold mm
  rw [← transfer_integral (P.Qs 0) β hβ (measurable_RC 0) (hP.RC_loc 0)]
  have hzero : ∀ q ∈ P.Qs 0, β q = 0 := by
    intro q hq
    have h1 := hβ q hq q hq
    simp only [Qs, Finset.mem_image] at hq
    obtain ⟨p, -, rfl⟩ := hq
    have h2 : kap (P.eps 0, P.ρ, p) (P.eps 0, P.ρ, p) = 0 := by
      rw [kap_diag (hP.eps_pos 0) (hP.eps_le 0), eps_zero, div_self hP.ρ_pos.ne', Real.log_one]
    rw [h2] at h1
    exact inner_self_eq_zero.1 h1
  have hRC : ∀ x, P.RC 0 (Yf β x) = 1 := by
    intro x
    unfold RC
    rw [riemannCost_eq_rcW]
    have : rcW P.N (P.polyOf 0 (P.dec 0 (Yf β x)))
        (fun w => Real.exp (P.ξ * Yf β x (P.eps 0, P.ρ, w))) =
        rcW P.N (P.polyOf 0 (P.dec 0 (Yf β x))) (fun _ => 1) := by
      refine rcW_congr _ _ fun z hz => ?_
      have hzS := hP.riemannPts_subset 0 _ hz
      simp [Yf, hzero _ (mem_Qs_tot hzS)]
    rw [this]
    simp only [polyOf, rcW, edges_cons_cons, edges_single, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, ew, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hN : (P.N : ℝ) ≠ 0 := by have := hP.N_pos; positivity
    field_simp
    simp
  simp [hRC]

end BParams

end LQGDimension.BlockCons
