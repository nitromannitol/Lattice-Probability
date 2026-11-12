/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12P3A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P2G
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_9ProofGeom

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.2, Step 2 at the LFPP level: truncation of `D^ε(·,·;W̄)` (Weyl input W1)

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Theorem 1.2,
Step 2 (T:1368–1372): for close points the internal LFPP on `W̄` agrees with the LFPP
(eqn-localized-property, T:1218–1223, and T:982–986). Deterministic statement, for a field with
continuous mollification:

* `trunc_eq_of_frontier` — the algebra of `trunc_dW_eq` for any pair `D ≤ d` on `W̄ × W̄` with
  `d = D` on close pairs and `d(a, ∂W) ≤ D(a, ∂W)`;
* `lfppDOn_frontier_lt` — the internal LFPP distance on `W̄` from `a ∈ W̄` to `∂W` is at most
  the LFPP distance from `a` to any point of `∂W` (a near-optimal path stopped when it first
  leaves `W` stays in `W̄`);
* `truncW_lfppSqC_eq` — `truncW W (𝔞⁻¹D^ε_g(·,·;W̄)) = truncD W (𝔞⁻¹D^ε_g)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.T12

open Blueprint MetricGeometry LFPP

/-- **the truncation identity, abstract form** -/
theorem trunc_eq_of_frontier (W : dyadicDomainsC)
    {D d : closure (W : Set ℂ) × closure (W : Set ℂ) → ℝ} (hD0 : ∀ p, 0 ≤ D p)
    (h1 : ∀ p, D p ≤ d p)
    (h2 : ∀ a b : closure (W : Set ℂ), (∀ w : closure (W : Set ℂ), w.1 ∈ frontier (W : Set ℂ) →
      D (a, b) < D (a, w)) → d (a, b) ≤ D (a, b))
    (hfr : ∀ a w₀ : closure (W : Set ℂ), w₀.1 ∈ frontier (W : Set ℂ) → ∀ η : ℝ, 0 < η →
      ∃ w : closure (W : Set ℂ), w.1 ∈ frontier (W : Set ℂ) ∧ d (a, w) ≤ D (a, w₀) + η)
    (a b : closure (W : Set ℂ)) :
    min (d (a, b)) (infFr W d a) = min (D (a, b)) (infFr W D a) := by
  have hinf : infFr W d a = infFr W D a := by
    rcases isEmpty_or_nonempty (α := {w : closure (W : Set ℂ) // w.1 ∈ frontier (W : Set ℂ)})
      with he | hne
    · simp only [infFr, Real.iInf_of_isEmpty]
    have hbd : BddBelow (range fun w : {w : closure (W : Set ℂ) // w.1 ∈ frontier (W : Set ℂ)} =>
        D (a, w.1)) := ⟨0, by rintro _ ⟨w, rfl⟩; exact hD0 _⟩
    have hbd' : BddBelow (range fun w : {w : closure (W : Set ℂ) // w.1 ∈ frontier (W : Set ℂ)} =>
        d (a, w.1)) := ⟨0, by rintro _ ⟨w, rfl⟩; exact (hD0 _).trans (h1 _)⟩
    refine le_antisymm ?_ (ciInf_mono hbd fun w => h1 (a, w.1))
    refine le_of_forall_pos_le_add fun η hη => ?_
    have key : ∀ w₀ : {w : closure (W : Set ℂ) // w.1 ∈ frontier (W : Set ℂ)},
        infFr W d a - η ≤ D (a, w₀.1) := by
      intro w₀
      obtain ⟨w, hw, hle⟩ := hfr a w₀.1 w₀.2 η hη
      have := (ciInf_le hbd' ⟨w, hw⟩).trans hle
      simp only [infFr] at this ⊢
      linarith
    have := le_ciInf key
    simp only [infFr] at this ⊢
    linarith
  rw [hinf]
  set m := infFr W D a
  rcases lt_or_ge (D (a, b)) m with hlt | hge
  · have hab : ∀ w : closure (W : Set ℂ), w.1 ∈ frontier (W : Set ℂ) → D (a, b) < D (a, w) :=
      fun w hw => hlt.trans_le (ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact hD0 _⟩
        (⟨w, hw⟩ : {w : closure (W : Set ℂ) // w.1 ∈ frontier (W : Set ℂ)}))
    rw [le_antisymm (h2 a b hab) (h1 (a, b))]
  · rw [min_eq_right hge, min_eq_right (hge.trans (h1 (a, b)))]

/-- **exit through `∂W` inside `W̄`** (LFPP level) -/
theorem lfppDOn_frontier_lt {ξ : ℝ} {φ : ℂ → ℝ} {W : Set ℂ} (hWo : IsOpen W) {a w₀ : ℂ}
    (ha : a ∈ closure W) (hw₀ : w₀ ∈ frontier W) {c : ℝ≥0∞} (hc : lfppDOn ξ φ univ a w₀ < c) :
    ∃ w ∈ frontier W, lfppDOn ξ φ (closure W) a w < c := by
  by_cases haW : a ∈ W
  swap
  · refine ⟨a, ⟨ha, by rw [hWo.interior_eq]; exact haW⟩, ?_⟩
    refine lt_of_le_of_lt ?_ ((zero_le).trans_lt hc)
    refine (lfppDOn_anti_set (S := {a}) (fun x hx => by rw [mem_singleton_iff.1 hx]; exact ha)
      a a).trans ?_
    rw [lfppDOn_self (convex_singleton a) (mem_singleton a)]
  obtain ⟨P, hP⟩ := iInf_lt_iff.1 hc
  obtain ⟨hPp, -⟩ := P.2
  have hA : IsClosed Wᶜ := hWo.isClosed_compl
  have h1 : P.1 1 ∈ Wᶜ := by
    rw [hPp.target]; intro h; exact hw₀.2 (by rw [hWo.interior_eq]; exact h)
  obtain ⟨s, hs, hsA, hbefore⟩ :=
    exists_first_hit hPp.continuousOn hA ⟨1, ⟨zero_le_one, le_rfl⟩, h1⟩
  have hin : ∀ t ∈ Ico 0 s, P.1 t ∈ W := fun t ht => not_not.1 (hbefore t ht)
  have hs0 : 0 < s := by
    rcases hs.1.eq_or_lt with h | h
    · exfalso; rw [← h, hPp.source] at hsA; exact hsA haW
    · exact h
  -- `P s ∈ ∂W`
  have hsK : P.1 s ∈ closure W := by
    have hcs : ContinuousWithinAt P.1 (Ico 0 s) s :=
      (hPp.continuousOn s hs).mono fun t ht => ⟨ht.1, ht.2.le.trans hs.2⟩
    have hne : (𝓝[Ico 0 s] s).NeBot := right_nhdsWithin_Ico_neBot hs0
    exact mem_closure_of_tendsto hcs (eventually_nhdsWithin_of_forall hin)
  have hsF : P.1 s ∈ frontier W := ⟨hsK, by rw [hWo.interior_eq]; exact hsA⟩
  refine ⟨P.1 s, hsF, lt_of_le_of_lt ?_ hP⟩
  have hsub := isPiecewiseC1Path_subPath hPp le_rfl hs0 hs.2
  rw [hPp.source] at hsub
  have hmem : ∀ u ∈ Icc (0 : ℝ) 1, subPath P.1 0 s u ∈ closure W := by
    intro u hu
    simp only [subPath, sub_zero, add_zero]
    have hsu : s * u ∈ Icc 0 s := ⟨mul_nonneg hs0.le hu.1, by nlinarith [hu.2]⟩
    rcases hsu.2.lt_or_eq with hlt | heq
    · exact subset_closure (hin _ ⟨hsu.1, hlt⟩)
    · rw [heq]; exact hsK
  refine (lfppDOn_le hsub hmem).trans ?_
  rw [lfppLen_subPath P.1 hs0, lfppLen_eq]
  exact lintegral_mono_set (Icc_subset_Icc le_rfl hs.2)

/-- **W1**: the truncated internal LFPP on `W̄` is the truncated LFPP -/
theorem truncW_lfppSqC_eq {ξ ε : ℝ} {g : DistC} (hc : Continuous (heatMollify ε g))
    (W : dyadicDomainsC) :
    truncW W (lfppSqC ξ ε g (closure W)) = truncD W (lfppC ξ ε g) := by
  have hWo : IsOpen (W : Set ℂ) := W.2.1.isOpen
  have hc0 : 0 ≤ (aEpsDF ξ ε)⁻¹ := inv_nonneg.2 (aEpsDF_nonneg_sq _ _)
  have hD : ∀ p : closure (W : Set ℂ) × closure (W : Set ℂ),
      restrSq (closure (W : Set ℂ)) (lfppC ξ ε g) p =
        (aEpsDF ξ ε)⁻¹ * (lfppDistE ξ ε g p.1.1 p.2.1).toReal := fun p => by
    rw [restrSq_apply, lfppC_apply_of_continuous hc]
  have hd : ∀ p : closure (W : Set ℂ) × closure (W : Set ℂ), lfppSqC ξ ε g (closure W) p =
      (aEpsDF ξ ε)⁻¹ * (lfppDOn ξ (heatMollify ε g) (closure W) p.1.1 p.2.1).toReal :=
    fun p => lfppSqC_closure_apply W.2.1 W.2.2 hc p
  have hC1 : ∀ a b : closure (W : Set ℂ), lfppC ξ ε g (a.1, b.1) ≤ lfppSqC ξ ε g (closure W) (a, b) :=
    lfppJoint_mem_dyC1 hc W
  have hC2 : ∀ a b : closure (W : Set ℂ),
      (∀ w : closure (W : Set ℂ), w.1 ∈ frontier (closure (W : Set ℂ)) →
        lfppC ξ ε g (a.1, b.1) < lfppC ξ ε g (a.1, w.1)) →
      lfppSqC ξ ε g (closure W) (a, b) ≤ lfppC ξ ε g (a.1, b.1) := lfppJoint_mem_dyC2 hc W
  ext p
  show truncW W (lfppSqC ξ ε g (closure W)) p =
    truncW W (restrSq (closure (W : Set ℂ)) (lfppC ξ ε g)) p
  rw [truncW_apply, truncW_apply]
  refine trunc_eq_of_frontier W (D := restrSq (closure (W : Set ℂ)) (lfppC ξ ε g))
    (d := lfppSqC ξ ε g (closure W)) (fun q => ?_) (fun q => hC1 q.1 q.2)
    (fun a b hab => hC2 a b fun w hw => hab w (frontier_closure_subset_dy _ hw))
    (fun a w₀ hw₀ η hη => ?_) p.1 p.2
  · rw [hD]; exact mul_nonneg hc0 ENNReal.toReal_nonneg
  · rcases hc0.eq_or_lt with h0 | h0
    · refine ⟨w₀, hw₀, ?_⟩
      show lfppSqC ξ ε g (closure W) (a, w₀) ≤ restrSq (closure (W : Set ℂ)) (lfppC ξ ε g) (a, w₀) + η
      rw [hd, hD, ← h0]; simp only [zero_mul, zero_add]; exact hη.le
    have hfin := lfppDistE_ne_top' (ξ := ξ) hc a.1 w₀.1
    set c : ℝ≥0∞ := ENNReal.ofReal ((lfppDistE ξ ε g a.1 w₀.1).toReal + η / (aEpsDF ξ ε)⁻¹)
    have hlt : lfppDOn ξ (heatMollify ε g) univ a.1 w₀.1 < c := by
      rw [← lfppDistE_eq_lfppDOn, ← ENNReal.ofReal_toReal hfin]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith [div_pos hη h0])
    obtain ⟨w, hwF, hw⟩ := lfppDOn_frontier_lt hWo a.2 hw₀ hlt
    refine ⟨⟨w, frontier_subset_closure hwF⟩, hwF, ?_⟩
    show lfppSqC ξ ε g (closure W) (a, ⟨w, _⟩) ≤ restrSq (closure (W : Set ℂ)) (lfppC ξ ε g) (a, w₀) + η
    rw [hd, hD]
    have hle := (ENNReal.toReal_le_of_le_ofReal (by positivity) hw.le)
    have : (aEpsDF ξ ε)⁻¹ * (η / (aEpsDF ξ ε)⁻¹) = η := mul_div_cancel₀ η h0.ne'
    calc (aEpsDF ξ ε)⁻¹ * (lfppDOn ξ (heatMollify ε g) (closure W) a.1 w).toReal
        ≤ (aEpsDF ξ ε)⁻¹ * ((lfppDistE ξ ε g a.1 w₀.1).toReal + η / (aEpsDF ξ ε)⁻¹) :=
          mul_le_mul_of_nonneg_left hle hc0
      _ = _ := by rw [mul_add, this]

end LQGMetric.DFGPS.T12
