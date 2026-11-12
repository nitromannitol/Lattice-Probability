/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasE3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE2

/-!
# Jordan parametrizations of `∂𝓑^•_s` as Polish witnesses (task P2-E3d, decision D65 (ii))

GM = Gwynne–Miller, arXiv:1905.00383v3; the parametrizations are those of
`Blueprint.IsPosJordanParam` (CONF Lemma 2.4 reading, CONFDefs). Own descriptive-set-theory
argument (GM do not discuss measurability).

* `gmE_isPosJordanParam_iff`: a `2π`-periodic positively oriented Jordan parametrization is
  `t ↦ φ(t mod 2π)` with `φ ∈ C(ℝ/2πℤ, ℂ)` injective with range `Γ`, angle lift
  `t ↦ t + ψ(t mod 2π)`, `ψ ∈ C(ℝ/2πℤ, ℝ)` (`gmJordanC`);
* `gmE_jordanC_iff`: for `Γ = ∂𝓑^•_s(𝕫; d)`, `d ∈ lenSet`, `gmJordanC` is the countable
  condition `gmJordF` (injectivity via the dense sequence `gmDT` of the circle, `range φ ⊆ Γ` on
  `gmDT`, `Γ ⊆ range φ` by rational balls, the polar identity at rational times);
* `gmE_measurable_jordF_comp`: `gmJordF` is Borel.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

/-- the circle `ℝ/2πℤ` -/
local notation "𝕋" => AddCircle (2 * Real.pi)

instance gmE_fact_twoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

lemma gmE_continuous_coe : Continuous fun t : ℝ => (t : 𝕋) := continuous_quotient_mk'

lemma gmE_exists_lift {X : Type} [TopologicalSpace X] {f : ℝ → X} (hf : Continuous f)
    (hp : Function.Periodic f (2 * Real.pi)) : ∃ g : C(𝕋, X), ∀ t : ℝ, g t = f t :=
  ⟨⟨hp.lift, isQuotientMap_quotient_mk'.continuous_iff.2 hf⟩, fun _ => rfl⟩

/-- the Jordan conditions on `(φ, ψ) ∈ C(𝕋, ℂ) × C(𝕋, ℝ)` -/
def gmJordanC (Γ : Set ℂ) (z : ℂ) (φ : C(𝕋, ℂ)) (ψ : C(𝕋, ℝ)) : Prop :=
  Function.Injective φ ∧ range φ = Γ ∧
    ∀ t : ℝ, φ t - z = (‖φ t - z‖ : ℂ) * Complex.exp (((t + ψ t : ℝ) : ℂ) * Complex.I)

lemma gmE_exists_Ico (a : 𝕋) : ∃ t ∈ Ico 0 (2 * Real.pi), (t : 𝕋) = a :=
  ⟨_, by simpa using (AddCircle.equivIco (2 * Real.pi) 0 a).2, AddCircle.coe_equivIco⟩

/-- **Jordan parametrizations through the circle** -/
theorem gmE_isPosJordanParam_iff (Γ : Set ℂ) (z : ℂ) (φ : ℝ → ℂ) :
    IsPosJordanParam Γ z φ ↔
      ∃ (φ' : C(𝕋, ℂ)) (ψ : C(𝕋, ℝ)), (∀ t : ℝ, φ' t = φ t) ∧ gmJordanC Γ z φ' ψ := by
  constructor
  · rintro ⟨hc, hper, hinj, hran, θ, hθc, hθp, hpol⟩
    obtain ⟨φ', hφ'⟩ := gmE_exists_lift hc hper
    have hψp : Function.Periodic (fun t => θ t - t) (2 * Real.pi) := fun t => by
      simp only [hθp]; ring
    obtain ⟨ψ, hψ⟩ := gmE_exists_lift (hθc.sub continuous_id) hψp
    refine ⟨φ', ψ, hφ', fun a b hab => ?_, ?_, fun t => ?_⟩
    · obtain ⟨t, ht, rfl⟩ := gmE_exists_Ico a
      obtain ⟨u, hu, rfl⟩ := gmE_exists_Ico b
      rw [hφ', hφ'] at hab
      rw [hinj ht hu hab]
    · rw [← hran]
      ext w
      constructor
      · rintro ⟨a, rfl⟩
        obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective a
        exact ⟨t, (hφ' t).symm⟩
      · rintro ⟨t, rfl⟩
        exact ⟨t, hφ' t⟩
    · have e1 : t + (θ - id : ℝ → ℝ) t = θ t := by simp only [Pi.sub_apply, id_eq]; ring
      rw [hφ', hψ, e1]
      exact hpol t
  · rintro ⟨φ', ψ, hφ', hinj, hran, hpol⟩
    have e : φ = fun t : ℝ => φ' (t : 𝕋) := funext fun t => (hφ' t).symm
    subst e
    refine ⟨φ'.continuous.comp gmE_continuous_coe, fun t => by
      simp only [AddCircle.coe_add_period], fun a ha b hb hab => ?_, ?_, fun t => t + ψ t,
      continuous_id.add (ψ.continuous.comp gmE_continuous_coe), fun t => ?_, fun t => hpol t⟩
    · exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0) (by rwa [zero_add])
        (by rwa [zero_add])).1 (hinj hab)
    · rw [← hran]
      ext w
      constructor
      · rintro ⟨t, rfl⟩; exact ⟨t, rfl⟩
      · rintro ⟨a, rfl⟩
        obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective a
        exact ⟨t, rfl⟩
    · simp only [AddCircle.coe_add_period]; ring

/-- a dense sequence of the circle -/
def gmDT : ℕ → 𝕋 := TopologicalSpace.denseSeq 𝕋

lemma gmE_denseRange_DT : DenseRange gmDT := TopologicalSpace.denseRange_denseSeq 𝕋

lemma gmE_injective_iff (φ : C(𝕋, ℂ)) : Function.Injective φ ↔
    ∀ m : ℕ, ∃ k : ℕ, ∀ a b : ℕ, 1 / ((m : ℝ) + 1) ≤ dist (gmDT a) (gmDT b) →
      1 / ((k : ℝ) + 1) ≤ dist (φ (gmDT a)) (φ (gmDT b)) := by
  constructor
  · intro hinj m
    set C := {p : 𝕋 × 𝕋 | 1 / ((m : ℝ) + 1) ≤ dist p.1 p.2}
    have hCc : IsCompact C := (isClosed_le continuous_const continuous_dist).isCompact
    rcases C.eq_empty_or_nonempty with hC | hC
    · refine ⟨0, fun a b hab => ?_⟩
      have : (gmDT a, gmDT b) ∈ C := hab
      rw [hC] at this
      exact absurd this (notMem_empty _)
    obtain ⟨p₀, hp₀, hmin⟩ := hCc.exists_isMinOn hC
      ((φ.continuous.comp continuous_fst).dist (φ.continuous.comp continuous_snd)).continuousOn
    have hpos : 0 < dist (φ p₀.1) (φ p₀.2) := by
      rw [dist_pos]
      intro h
      have h1 := hinj h
      have h2 : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      have h3 : 1 / ((m : ℝ) + 1) ≤ dist p₀.1 p₀.2 := hp₀
      rw [h1, dist_self] at h3
      linarith
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
    exact ⟨k, fun a b hab => hk.le.trans (hmin (show (gmDT a, gmDT b) ∈ C from hab))⟩
  · intro H a b hab
    by_contra hne
    have hd : 0 < dist a b := dist_pos.2 hne
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hd)
    obtain ⟨k, hk⟩ := H m
    have hk0 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨δa, hδa, hca⟩ := Metric.continuous_iff.1 φ.continuous a _ (half_pos hk0)
    obtain ⟨δb, hδb, hcb⟩ := Metric.continuous_iff.1 φ.continuous b _ (half_pos hk0)
    obtain ⟨e, he⟩ : ∃ e, e = min (min δa δb) (dist a b / 4) := ⟨_, rfl⟩
    have he0 : 0 < e := he ▸ lt_min (lt_min hδa hδb) (by linarith)
    have e1 : e ≤ δa := he ▸ (min_le_left _ _).trans (min_le_left _ _)
    have e2 : e ≤ δb := he ▸ (min_le_left _ _).trans (min_le_right _ _)
    have e3 : e ≤ dist a b / 4 := he ▸ min_le_right _ _
    obtain ⟨i, hi⟩ := gmE_denseRange_DT.exists_dist_lt a he0
    obtain ⟨j, hj⟩ := gmE_denseRange_DT.exists_dist_lt b he0
    have hab' : 1 / ((m : ℝ) + 1) ≤ dist (gmDT i) (gmDT j) := by
      have := dist_triangle4 a (gmDT i) (gmDT j) b
      rw [dist_comm (gmDT j) b] at this
      linarith
    have h1 := hca (gmDT i) (by rw [dist_comm]; linarith)
    have h2 := hcb (gmDT j) (by rw [dist_comm]; linarith)
    have h3 := dist_triangle (φ (gmDT i)) (φ a) (φ (gmDT j))
    rw [hab, dist_comm (φ b)] at h3
    rw [hab] at h1
    have := hk i j hab'
    linarith

lemma gmE_range_subset_iff (φ : C(𝕋, ℂ)) {F : Set ℂ} (hF : IsClosed F) :
    range φ ⊆ F ↔ ∀ a : ℕ, φ (gmDT a) ∈ F := by
  constructor
  · intro h a; exact h ⟨_, rfl⟩
  · rintro h _ ⟨x, rfl⟩
    exact gmE_denseRange_DT.induction_on (p := fun x => φ x ∈ F) x
      (hF.preimage φ.continuous) h

lemma gmE_subset_range_iff (φ : C(𝕋, ℂ)) (Γ : Set ℂ) :
    Γ ⊆ range φ ↔ ∀ j n : ℕ, (∃ m : ℕ, ∀ a : ℕ,
      1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1) ≤ dist (φ (gmDT a)) (qd j)) →
        ball (qd j) (1 / ((n : ℝ) + 1)) ∩ Γ = ∅ := by
  constructor
  · rintro h j n ⟨m, hm⟩
    refine eq_empty_iff_forall_notMem.2 fun v ⟨hv, hvΓ⟩ => ?_
    obtain ⟨x, rfl⟩ := h hvΓ
    have : 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1) ≤ dist (φ x) (qd j) :=
      gmE_denseRange_DT.induction_on
        (p := fun x => 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1) ≤ dist (φ x) (qd j)) x
        (isClosed_le continuous_const (φ.continuous.dist continuous_const)) hm
    have h1 : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    rw [mem_ball] at hv
    linarith
  · intro H y hy
    by_contra hny
    have hcl : IsClosed (range φ) := (isCompact_range φ.continuous).isClosed
    have hpos : 0 < infDist y (range φ) := (hcl.notMem_iff_infDist_pos (range_nonempty φ)).1 hny
    obtain ⟨ε, hε⟩ : ∃ ε, ε = infDist y (range φ) / 4 := ⟨_, rfl⟩
    have hε0 : 0 < ε := by rw [hε]; positivity
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε0
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε0
    obtain ⟨j, hj⟩ := denseRange_qd.exists_dist_lt y
      (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
    have hH := H j n ⟨m, fun a => ?_⟩
    · exact (eq_empty_iff_forall_notMem.1 hH) y ⟨mem_ball.2 hj, hy⟩
    · have h1 := infDist_le_dist_of_mem (x := y) (mem_range_self (f := φ) (gmDT a))
      have h2 := dist_triangle y (qd j) (φ (gmDT a))
      rw [dist_comm (qd j)] at h2
      linarith

lemma gmE_polar_iff (φ : C(𝕋, ℂ)) (ψ : C(𝕋, ℝ)) (z : ℂ) :
    (∀ t : ℝ, φ t - z = (‖φ t - z‖ : ℂ) * Complex.exp (((t + ψ t : ℝ) : ℂ) * Complex.I)) ↔
    ∀ q : ℚ, φ ((q : ℝ) : 𝕋) - z = (‖φ ((q : ℝ) : 𝕋) - z‖ : ℂ) *
      Complex.exp ((((q : ℝ) + ψ ((q : ℝ) : 𝕋) : ℝ) : ℂ) * Complex.I) := by
  constructor
  · intro h q; exact h q
  · intro h t
    have hc1 : Continuous fun t : ℝ => φ t := φ.continuous.comp gmE_continuous_coe
    have hc2 : Continuous fun t : ℝ => ψ t := ψ.continuous.comp gmE_continuous_coe
    exact Rat.denseRange_cast.induction_on
      (p := fun t : ℝ => φ t - z = (‖φ t - z‖ : ℂ) *
        Complex.exp (((t + ψ t : ℝ) : ℂ) * Complex.I)) t
      (isClosed_eq (hc1.sub continuous_const) ((Complex.continuous_ofReal.comp
        (hc1.sub continuous_const).norm).mul (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp (continuous_id.add hc2)).mul continuous_const)))) h

/-- the Jordan conditions for `Γ = ∂𝓑^•_s(𝕫; d)`, countable form -/
def gmJordF (d : ContMetric) (𝕫 : ℂ) (s : ℝ) (φ : C(𝕋, ℂ)) (ψ : C(𝕋, ℝ)) : Prop :=
  (∀ m : ℕ, ∃ k : ℕ, ∀ a b : ℕ, 1 / ((m : ℝ) + 1) ≤ dist (gmDT a) (gmDT b) →
      1 / ((k : ℝ) + 1) ≤ dist (φ (gmDT a)) (φ (gmDT b))) ∧
  ((∀ a : ℕ, gmFrF d 𝕫 s (φ (gmDT a))) ∧
    ∀ j n : ℕ, (∃ m : ℕ, ∀ a : ℕ,
      1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1) ≤ dist (φ (gmDT a)) (qd j)) →
        gmBallOffF d 𝕫 s (qd j) (1 / ((n : ℝ) + 1))) ∧
  ∀ q : ℚ, φ ((q : ℝ) : 𝕋) - 𝕫 = (‖φ ((q : ℝ) : 𝕋) - 𝕫‖ : ℂ) *
      Complex.exp ((((q : ℝ) + ψ ((q : ℝ) : 𝕋) : ℝ) : ℂ) * Complex.I)

theorem gmE_jordanC_iff {d : ContMetric} (hd : d ∈ lenSet) (𝕫 : ℂ) (s : ℝ) (φ : C(𝕋, ℂ))
    (ψ : C(𝕋, ℝ)) :
    gmJordanC (frontier (filledBall d 𝕫 s)) 𝕫 φ ψ ↔ gmJordF d 𝕫 s φ ψ := by
  rw [gmJordanC, gmJordF, gmE_injective_iff, Set.Subset.antisymm_iff,
    gmE_range_subset_iff φ isClosed_frontier, gmE_subset_range_iff, gmE_polar_iff]
  exact and_congr Iff.rfl (and_congr (and_congr
    (forall_congr' fun a => gmE_mem_frontier_iff hd _ _ _)
    (forall_congr' fun j => forall_congr' fun n => imp_congr_right fun _ =>
      gmE_ball_inter_frontier_iff hd _ _ _ (by positivity))) Iff.rfl)

lemma gmE_measurable_jordF_comp {X : Type} [MeasurableSpace X] {f : X → ContMetric}
    {s : X → ℝ} {φ : X → C(𝕋, ℂ)} {ψ : X → C(𝕋, ℝ)} (hf : Measurable f) (hs : Measurable s)
    (hφ : Measurable φ) (hψ : Measurable ψ) (𝕫 : ℂ) :
    Measurable fun q => gmJordF (f q) 𝕫 (s q) (φ q) (ψ q) := by
  have ev : ∀ a : 𝕋, Measurable fun q => φ q a := fun a =>
    (continuous_eval_const a).measurable.comp hφ
  have evψ : ∀ a : 𝕋, Measurable fun q => ψ q a := fun a =>
    (continuous_eval_const a).measurable.comp hψ
  refine (Measurable.forall fun m => Measurable.exists fun k => Measurable.forall fun a =>
    Measurable.forall fun b => measurable_const.imp (measurableSet_setOfPred.1
      (measurableSet_le measurable_const ((ev _).dist (ev _))))).and
    (((Measurable.forall fun a => gmE_measurable_frF_comp hf hs (ev _) 𝕫).and
      (Measurable.forall fun j => Measurable.forall fun n => (Measurable.exists fun m =>
        Measurable.forall fun a => measurableSet_setOfPred.1 (measurableSet_le measurable_const
          ((ev _).dist measurable_const))).imp
        (gmE_measurable_ballOffF_comp hf hs 𝕫 _ _))).and
      (Measurable.forall fun q => measurableSet_setOfPred.1 (measurableSet_eq_fun
        ((ev _).sub_const _) ((Complex.measurable_ofReal.comp ((ev _).sub_const _).norm).mul
          (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
            (measurable_const.add (evψ _))).mul_const _))))))

end LQGMetric.GM
