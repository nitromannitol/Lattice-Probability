/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.Measurable at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.ChainInf
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyUnif

/-!
# Measurability of `D^ε_h`, `lfppCross` and `lfppCrossIn` in the field

Task P2-LFPP, item 2. On the event where `h*_ε` is continuous (a.s. for a whole-plane GFF plus a
bounded continuous function, `IsGFFPlusBddCont.ae_tendstoLocallyUniformly_heatMollify`), the
LFPP quantities equal countable infima of chain costs (`LFPP/ChainInf.lean`), and each chain cost
is measurable in `h` (joint measurability of `(h, z) ↦ h*_ε(z)`, `measurable_heatMollify`).
Hence they are a.e.-measurable for every law of such a field, in particular for `normGFFLaw`
(GM l. 223; the median steps of GM §1.4 need this). DFGPS and GM use these measurabilities
without comment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace LFPP

variable {ξ : ℝ} {φ : ℂ → ℝ} {S : Set ℂ}

theorem norm_le_two_of_side {c : ℝ} (hc : |c| ≤ 1) {z : ℂ}
    (hz : z ∈ {z : ℂ | z.re = c ∧ 0 ≤ z.im ∧ z.im ≤ 1}) : ‖z‖ ≤ 2 := by
  obtain ⟨h1, h2, h3⟩ := hz
  refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
  rw [h1, abs_of_nonneg h2]
  linarith

/-- **Reduction of the side-to-side infimum to rational points of the sides.** -/
theorem iInf_sides_eq (hφ : Continuous φ) (hS : Convex ℝ S) (hLS : leftSide ⊆ S)
    (hRS : rightSide ⊆ S) :
    (⨅ z ∈ leftSide, ⨅ w ∈ rightSide, lfppDOn ξ φ S z w) =
      ⨅ (a : sideRat 0) (b : sideRat 1), lfppDOn ξ φ S a b := by
  refine le_antisymm (le_iInf fun a => le_iInf fun b =>
    iInf₂_le_of_le a.1 (sideRat_subset 0 a.2) (iInf₂_le_of_le b.1 (sideRat_subset 1 b.2) le_rfl))
    (le_iInf₂ fun z hz => le_iInf₂ fun w hw => ?_)
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  set E : ℂ → ℝ := fun x => Real.exp (ξ * φ x)
  have hE : Continuous E := Real.continuous_exp.comp (continuous_const.mul hφ)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 3).exists_bound_of_continuousOn hE.continuousOn
  set ρ := min 1 ((δ : ℝ) / (2 * (|M| + 1)))
  have hρ : 0 < ρ := lt_min one_pos (by have : (0 : ℝ) < δ := hδ; positivity)
  obtain ⟨a, ha, haz⟩ := sideRat_dense hz hρ
  obtain ⟨b, hb, hbw⟩ := sideRat_dense hw hρ
  have hseg : ∀ x y : ℂ, ‖x‖ ≤ 2 → ‖y - x‖ < ρ →
      segCost ξ φ x y ≤ ENNReal.ofReal ((δ : ℝ) / 2) := by
    intro x y hx hxy
    refine (segCost_le (B := |M|) fun u hu => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
    · have hu' : u ∈ Metric.closedBall (0 : ℂ) 3 := by
        rw [Metric.mem_closedBall, dist_zero_right]
        rw [Metric.mem_closedBall, dist_eq_norm] at hu
        have := norm_le_norm_add_norm_sub' u x
        linarith [min_le_left 1 ((δ : ℝ) / (2 * (|M| + 1)))]
      exact (Real.le_norm_self _).trans ((hM u hu').trans (le_abs_self M))
    · have h1 : ρ ≤ (δ : ℝ) / (2 * (|M| + 1)) := min_le_right _ _
      rw [le_div_iff₀ (by positivity)] at h1
      nlinarith [abs_nonneg M]
  have hab := (lfppDOn_triangle (ξ := ξ) (φ := φ) (S := S) (a : ℂ) z b).trans (add_le_add_right
    (lfppDOn_triangle (ξ := ξ) (φ := φ) (S := S) z w b) _)
  refine (iInf_le_of_le (⟨a, ha⟩ : sideRat 0) (iInf_le_of_le (⟨b, hb⟩ : sideRat 1) hab)).trans ?_
  have h1 := (lfppDOn_le_segCost (ξ := ξ) (φ := φ) hS (hLS (sideRat_subset 0 ha)) (hLS hz)).trans
    (hseg a z (norm_le_two_of_side (by simp) (sideRat_subset 0 ha))
      (by rw [norm_sub_rev]; exact haz))
  have h2 := (lfppDOn_le_segCost (ξ := ξ) (φ := φ) hS (hRS hw) (hRS (sideRat_subset 1 hb))).trans
    (hseg w b (norm_le_two_of_side (by simp) hw) hbw)
  calc lfppDOn ξ φ S a z + (lfppDOn ξ φ S z w + lfppDOn ξ φ S w b)
      ≤ ENNReal.ofReal ((δ : ℝ) / 2) + (lfppDOn ξ φ S z w + ENNReal.ofReal ((δ : ℝ) / 2)) :=
        add_le_add h1 (add_le_add_right h2 _)
    _ = lfppDOn ξ φ S z w + δ := by
      rw [add_comm, add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity), add_halves,
        ENNReal.ofReal_coe_nnreal]

/-! ### Measurability in the field -/

theorem measurable_segCost (ξ ε : ℝ) (a b : ℂ) :
    Measurable fun h : DistC => segCost ξ (heatMollify ε h) a b := by
  have hseg : Continuous (segPath a b) := by unfold segPath; fun_prop
  have h1 : Measurable fun p : DistC × ℝ => ((p.1, segPath a b p.2) : DistC × ℂ) :=
    measurable_fst.prodMk (hseg.measurable.comp measurable_snd)
  have h2 : Measurable fun p : DistC × ℝ => heatMollify ε p.1 (segPath a b p.2) := by
    have := Measurable.comp (g := fun q : DistC × ℂ => heatMollify ε q.1 q.2)
      (f := fun p : DistC × ℝ => ((p.1, segPath a b p.2) : DistC × ℂ))
      (measurable_heatMollify ε) h1
    exact this
  have h3 : Measurable fun p : DistC × ℝ => ‖deriv (segPath a b) p.2‖ :=
    (measurable_deriv _).norm.comp measurable_snd
  have hj : Measurable fun p : DistC × ℝ => ENNReal.ofReal
      (Real.exp (ξ * heatMollify ε p.1 (segPath a b p.2)) * ‖deriv (segPath a b) p.2‖) :=
    ((h2.const_mul ξ).exp.mul h3).ennreal_ofReal
  show Measurable fun h : DistC => ∫⁻ t in Icc (0 : ℝ) 1,
    ENNReal.ofReal (Real.exp (ξ * heatMollify ε h (segPath a b t)) * ‖deriv (segPath a b) t‖)
  exact Measurable.lintegral_prod_right' (ν := volume.restrict (Icc (0 : ℝ) 1)) hj

theorem measurable_iInf_chainCost (ξ ε : ℝ) {C : Set ℂ} (hC : C.Countable) (z w : ℂ) :
    Measurable fun h : DistC => ⨅ (N : ℕ) (q : Fin N → C), chainCost ξ (heatMollify ε h) z w N q := by
  have := hC.to_subtype
  refine Measurable.iInf fun N => Measurable.iInf fun q => ?_
  exact Finset.measurable_sum _ fun i _ => measurable_segCost ξ ε _ _

/-- the countable-chain version of `lfppDistE` -/
def lfppDistChain (ξ ε : ℝ) (h : DistC) (z w : ℂ) : ℝ≥0∞ :=
  ⨅ (N : ℕ) (q : Fin N → gaussRat), chainCost ξ (heatMollify ε h) z w N q

theorem lfppDistE_eq_chain {ε : ℝ} {h : DistC} (hc : Continuous (heatMollify ε h)) (z w : ℂ) :
    lfppDistE ξ ε h z w = lfppDistChain ξ ε h z w := by
  rw [lfppDistE_eq_lfppDOn]
  exact lfppDOn_eq_iInf_chain hc convex_univ (subset_univ _)
    (fun x _ ρ hρ => gaussRat_dense x hρ) (mem_univ _) (mem_univ _)

/-- the countable version of `lfppCross` -/
def lfppCrossChain (ξ ε : ℝ) (h : DistC) : ℝ :=
  (⨅ (a : sideRat 0) (b : sideRat 1), lfppDistChain ξ ε h a b).toReal

theorem lfppCross_eq_chain {ε : ℝ} {h : DistC} (hc : Continuous (heatMollify ε h)) :
    lfppCross ξ ε h = lfppCrossChain ξ ε h := by
  rw [lfppCross_eq, iInf_sides_eq hc convex_univ (subset_univ _) (subset_univ _), lfppCrossChain]
  simp only [← lfppDistE_eq_lfppDOn, lfppDistE_eq_chain hc]

/-- the countable version of `lfppCrossIn` -/
def lfppCrossInChain (ξ ε : ℝ) (h : DistC) : ℝ :=
  (⨅ (a : sideRat 0) (b : sideRat 1), ⨅ (N : ℕ) (q : Fin N → ↥(gaussRat ∩ Blueprint.closedUnitSquare)),
    chainCost ξ (heatMollify ε h) a b N q).toReal

theorem convex_closedUnitSquare : Convex ℝ Blueprint.closedUnitSquare := by
  have : Blueprint.closedUnitSquare = (Complex.reLm ⁻¹' Icc 0 1) ∩ (Complex.imLm ⁻¹' Icc 0 1) := by
    ext z; simp [Blueprint.closedUnitSquare, and_assoc]
  rw [this]
  exact ((convex_Icc 0 1).linear_preimage _).inter ((convex_Icc 0 1).linear_preimage _)

theorem leftSide_subset_square : leftSide ⊆ Blueprint.closedUnitSquare := fun z ⟨h1, h2, h3⟩ =>
  ⟨h1.ge, by rw [h1]; exact zero_le_one, h2, h3⟩

theorem rightSide_subset_square : rightSide ⊆ Blueprint.closedUnitSquare := fun z ⟨h1, h2, h3⟩ =>
  ⟨by rw [h1]; exact zero_le_one, h1.le, h2, h3⟩

theorem lfppCrossIn_eq_chain {ε : ℝ} {h : DistC} (hc : Continuous (heatMollify ε h)) :
    Blueprint.lfppCrossIn ξ ε h = lfppCrossInChain ξ ε h := by
  rw [lfppCrossIn_eq, iInf_sides_eq hc convex_closedUnitSquare leftSide_subset_square
    rightSide_subset_square, lfppCrossInChain]
  congr 1
  refine iInf_congr fun a => iInf_congr fun b => ?_
  exact lfppDOn_eq_iInf_chain hc convex_closedUnitSquare inter_subset_right
    (fun x hx ρ hρ => gaussRat_square_dense hx hρ)
    (leftSide_subset_square (sideRat_subset 0 a.2)) (rightSide_subset_square (sideRat_subset 1 b.2))

theorem measurable_lfppDistChain (ξ ε : ℝ) (z w : ℂ) :
    Measurable fun h => lfppDistChain ξ ε h z w :=
  measurable_iInf_chainCost ξ ε gaussRat_countable z w

theorem measurable_lfppCrossChain (ξ ε : ℝ) : Measurable (lfppCrossChain ξ ε) := by
  have := (sideRat_countable 0).to_subtype
  have := (sideRat_countable 1).to_subtype
  exact ENNReal.measurable_toReal.comp (Measurable.iInf fun a => Measurable.iInf fun b =>
    measurable_lfppDistChain ξ ε _ _)

theorem measurable_lfppCrossInChain (ξ ε : ℝ) : Measurable (lfppCrossInChain ξ ε) := by
  have := (sideRat_countable 0).to_subtype
  have := (sideRat_countable 1).to_subtype
  exact ENNReal.measurable_toReal.comp (Measurable.iInf fun a => Measurable.iInf fun b =>
    measurable_iInf_chainCost ξ ε (gaussRat_countable.mono inter_subset_left) _ _)

/-! ### A.e.-measurability -/

variable {μ : Measure DistC} {ε : ℝ}

theorem aemeasurable_lfppCross (hμ : ∀ᵐ h ∂μ, Continuous (heatMollify ε h)) :
    AEMeasurable (lfppCross ξ ε) μ :=
  ⟨_, measurable_lfppCrossChain ξ ε, by
    filter_upwards [hμ] with h hc using lfppCross_eq_chain hc⟩

theorem aemeasurable_lfppCrossIn (hμ : ∀ᵐ h ∂μ, Continuous (heatMollify ε h)) :
    AEMeasurable (Blueprint.lfppCrossIn ξ ε) μ :=
  ⟨_, measurable_lfppCrossInChain ξ ε, by
    filter_upwards [hμ] with h hc using lfppCrossIn_eq_chain hc⟩

/-- a.s. continuity of `h*_ε` under `normGFFLaw` (trivial if the law is the junk `0`) -/
theorem ae_continuous_heatMollify_normGFFLaw (hε : ε ≠ 0) :
    ∀ᵐ h ∂normGFFLaw, Continuous (heatMollify ε h) := by
  unfold normGFFLaw
  split_ifs with hμ
  · filter_upwards [(hμ.choose_spec.2.1).ae_tendstoLocallyUniformly_heatMollify ε hε] with h hh
    exact hh.2
  · simp

/-- **The input of the median steps of GM §1.4** (`P2-M1D`). -/
theorem aemeasurable_lfppCross_normGFFLaw (ξ ε : ℝ) (hε : 0 < ε) :
    AEMeasurable (lfppCross ξ ε) normGFFLaw :=
  aemeasurable_lfppCross (ae_continuous_heatMollify_normGFFLaw hε.ne')

/-- **Same for DFGPS's internal crossing distance.** -/
theorem aemeasurable_lfppCrossIn_normGFFLaw (ξ ε : ℝ) (hε : 0 < ε) :
    AEMeasurable (Blueprint.lfppCrossIn ξ ε) normGFFLaw :=
  aemeasurable_lfppCrossIn (ae_continuous_heatMollify_normGFFLaw hε.ne')

section Field

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- For a whole-plane GFF plus a bounded continuous function, `ω ↦ D^ε_{h(ω)}(z, w)` is
a.e.-measurable. -/
theorem IsGFFPlusBddCont.aemeasurable_lfppDistE (hh : IsGFFPlusBddCont h P) (hε : ε ≠ 0)
    (z w : ℂ) : AEMeasurable (fun ω => lfppDistE ξ ε (h ω) z w) P :=
  ⟨_, (measurable_lfppDistChain ξ ε z w).comp hh.1, by
    filter_upwards [hh.ae_tendstoLocallyUniformly_heatMollify ε hε] with ω hω
    exact lfppDistE_eq_chain hω.2 z w⟩

end Field

end LFPP
end LQGMetric
