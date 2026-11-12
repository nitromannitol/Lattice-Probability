/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D114S4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_1B
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L33
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc

/-!
# Trace of `σ(A, h|_A)` mod constants on `{A ⊆ U}`

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, C:472–474 (local sets, "`A` is determined by
`h|_U` on `{A ⊂ U}`") and C:1431–1437 (Step 3 of Lemma 3.6: "since `𝓑^•_τ` is a local set …
the event … is a.s. determined by `h|_{ℂ∖𝔘}`"); decision D114 §4 C2 (ii).

`conf36_trace_local0`: the mod-constant version (`localSigma0`, `fieldSigma0On`,
`IsLocalSetDet0`; D108, D110) of `conf21_trace_local` (L2_1B, same proof): for a closed, a.s.
bounded local set `A` and `G ∈ σ(A, h|_A)` mod constants, `{A ⊆ U} ∩ G` is a.s. an event of
`σ(h|_U)` mod constants.
Also `conf36_isClosed_filledBall` (the filled ball is always closed: the unbounded components of
the open set `(cl 𝓑_s)ᶜ` are open) and `conf36_fieldSigma0On_mono`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint GM LocalEvent

/-- the filled ball is closed -/
theorem conf36_isClosed_filledBall (d : ContMetric) (z : ℂ) (s : ℝ) :
    IsClosed (filledBall d z s) := by
  set X := closure (ballM d z s)
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  have hxX : x ∉ X := fun h => hx (Or.inl h)
  have hub : ¬ Bornology.IsBounded (connectedComponentIn Xᶜ x) := fun h => hx (Or.inr ⟨hxX, h⟩)
  refine ⟨connectedComponentIn Xᶜ x, fun y hy hyF => ?_,
    isClosed_closure.isOpen_compl.connectedComponentIn, mem_connectedComponentIn hxX⟩
  have hyX : y ∈ Xᶜ := connectedComponentIn_subset _ _ hy
  rcases hyF with h | ⟨_, hb⟩
  · exact hyX h
  · rw [← connectedComponentIn_eq hy] at hb
    exact hub hb

/-- `σ(h|_V)` mod constants is monotone in `V` -/
theorem conf36_fieldSigma0On_mono {Ω : Type} (h : Ω → DistC) {V U : Set ℂ} (hVU : V ⊆ U) :
    fieldSigma0On h V ≤ fieldSigma0On h U := by
  refine @Measurable.comap_le _ _ (fieldSigma0On h U) _ _
    (@measurable_pi_iff Ω _ _ (fieldSigma0On h U) _ _ |>.2 fun ψ => ?_)
  exact (measurable_pi_apply (⟨ψ.1, ψ.2.trans hVU⟩ :
    {ψ : TestC0 // tsupport (ψ.1 : ℂ → ℝ) ⊆ U})).comp
    (comap_measurable (fun ω (ψ : {ψ : TestC0 // tsupport (ψ.1 : ℂ → ℝ) ⊆ U}) => h ω ψ.1.1))

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- **trace of `σ(A, h|_A)` mod constants on `{A ⊆ U}`** (port of `conf21_trace_local`) -/
theorem conf36_trace_local0M (h : Ω → DistC) {A : Ω → Set ℂ} (hAc : ∀ ω, IsClosed (A ω))
    (hloc : IsLocalSetDet0 P h A) {U : Set ℂ} (_hU : IsOpen U)
    (hmar : ∀ᵐ ω ∂P, A ω ⊆ U → ∃ δ > 0, thickening δ (A ω) ⊆ U)
    {G : Set Ω} (hG : MeasurableSet[localSigma0 h A] G) :
    AEEventIn P (fieldSigma0On h U) ({ω | A ω ⊆ U} ∩ G) := by
  let O : ℕ → Set ℂ := fun n => interior {x | closedBall x (2 / 2 ^ n) ⊆ U}
  have hOo : ∀ n, IsOpen (O n) := fun n => isOpen_interior
  have hOU : ∀ n, O n ⊆ U := fun n x hx =>
    (interior_subset hx : closedBall x _ ⊆ U) (mem_closedBall_self (by positivity))
  have hlocU : ∀ {V : Set ℂ}, IsOpen V → V ⊆ U →
      AEEventIn P (fieldSigma0On h U) {ω | A ω ⊆ V} :=
    fun hV hVU => by
      obtain ⟨F, hF, hEF⟩ := hloc _ hV
      exact ⟨F, conf36_fieldSigma0On_mono h hVU _ hF, hEF⟩
  let En : ℕ → Set Ω := fun n => {ω | A ω ⊆ O n}
  have hEn : ∀ n, AEEventIn P (fieldSigma0On h U) (En n) := fun n => hlocU (hOo n) (hOU n)
  have key : ∀ n, hullSigma0 h A n ≤ conf21Tr P (fieldSigma0On h U) (En n) (hEn n) := by
    intro n
    have hset : setSigma A ≤ conf21Tr P (fieldSigma0On h U) (En n) (hEn n) := by
      refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨V, hV, rfl⟩
      have hc : MeasurableSet[conf21Tr P (fieldSigma0On h U) (En n) (hEn n)]
          {ω | (A ω ∩ V).Nonempty}ᶜ := by
        obtain ⟨F, hFc, hFV, hFU, -⟩ := hV.exists_iUnion_isClosed
        have e : En n ∩ {ω | (A ω ∩ V).Nonempty}ᶜ = ⋂ j, {ω | A ω ⊆ O n ∩ (F j)ᶜ} := by
          ext ω
          simp only [En, mem_inter_iff, mem_ofPred_eq, mem_compl_iff, mem_iInter,
            subset_inter_iff, not_nonempty_iff_eq_empty]
          constructor
          · rintro ⟨h1, h2⟩ j
            refine ⟨h1, fun x hx hxF => ?_⟩
            have : x ∈ A ω ∩ V := ⟨hx, hFV j hxF⟩
            rw [h2] at this
            exact this
          · intro H
            refine ⟨(H 0).1, eq_empty_iff_forall_notMem.2 fun x ⟨hx, hxV⟩ => ?_⟩
            rw [← hFU, mem_iUnion] at hxV
            obtain ⟨j, hj⟩ := hxV
            exact (H j).2 hx hj
        show AEEventIn P (fieldSigma0On h U) (En n ∩ _)
        rw [e]
        exact conf21_ae_iInter fun j =>
          hlocU ((hOo n).inter (hFc j).isOpen_compl) (inter_subset_left.trans (hOU n))
      simpa only [compl_compl] using hc.compl
    have hgen : MeasurableSpace.generateFrom {E | ∃ (S : Set ℂ) (F : Set Ω),
        MeasurableSet[fieldSigma0On h (interior S)] F ∧
          E = {ω | dyadicHull n (A ω) = S} ∩ F} ≤
          conf21Tr P (fieldSigma0On h U) (En n) (hEn n) := by
      refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨S, F, hF, rfl⟩
      show AEEventIn P (fieldSigma0On h U) (En n ∩ ({ω | dyadicHull n (A ω) = S} ∩ F))
      by_cases hSU : S ⊆ U
      · rw [← inter_assoc]
        have h1 : AEEventIn P (fieldSigma0On h U) (En n ∩ {ω | dyadicHull n (A ω) = S}) :=
          hset _ (measurableSet_hull_eq hAc n S)
        have h2 : MeasurableSet[fieldSigma0On h U] F :=
          conf36_fieldSigma0On_mono h (interior_subset.trans hSU) _ hF
        exact conf21_ae_inter h1 ⟨F, h2, EventuallyEq.rfl⟩
      · have e : En n ∩ ({ω | dyadicHull n (A ω) = S} ∩ F) = ∅ := by
          refine eq_empty_iff_forall_notMem.2 fun ω ⟨hAO, hS, _⟩ => hSU ?_
          have hS' : dyadicHull n (A ω) = S := hS
          rw [← hS']
          intro y hy
          simp only [dyadicHull, mem_iUnion] at hy
          obtain ⟨k, ⟨a, haS, haA⟩, hyk⟩ := hy
          have ha : closedBall a (2 / 2 ^ n) ⊆ U := interior_subset (hAO haA)
          exact ha (by rw [mem_closedBall]; exact conf21_sq_dist hyk haS)
        rw [e]
        exact ⟨∅, @MeasurableSet.empty _ (fieldSigma0On h U), EventuallyEq.rfl⟩
    exact sup_le hset hgen
  have hGn : ∀ n, MeasurableSet[hullSigma0 h A n] G := fun n =>
    MeasurableSpace.measurableSet_iInf.1 hG n
  have hae : ({ω | A ω ⊆ U} ∩ G) =ᵐ[P] ⋃ n, (En n ∩ G) := by
    filter_upwards [hmar] with ω hb
    refine propext ⟨fun ⟨hAU, hGω⟩ => ?_, fun hω => ?_⟩
    · obtain ⟨δ, hδ, hδA⟩ := hb hAU
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < δ / 4 by positivity)
        (show (1 / 2 : ℝ) < 1 by norm_num)
      have h3 : (2 : ℝ) / 2 ^ n = 2 * (1 / 2) ^ n := by rw [one_div_pow, mul_one_div]
      refine mem_iUnion.2 ⟨n, ?_, hGω⟩
      intro x hx
      refine mem_interior.2 ⟨ball x (δ / 2), fun y hy w hw =>
        hδA (mem_thickening_iff.2 ⟨x, hx, ?_⟩), isOpen_ball, mem_ball_self (by positivity)⟩
      have h1 := mem_ball.1 hy
      have h2 := mem_closedBall.1 hw
      linarith [dist_triangle w y x]
    · obtain ⟨n, hAO, hGω⟩ := mem_iUnion.1 hω
      exact ⟨fun x hx => hOU n (hAO hx), hGω⟩
  obtain ⟨F, hF, hEF⟩ := conf21_ae_iUnion (m := fieldSigma0On h U) fun n => key n G (hGn n)
  exact ⟨F, hF, hae.trans hEF⟩

/-- the trace lemma for an a.s. bounded local set (as `conf21_trace_local`) -/
theorem conf36_trace_local0 (h : Ω → DistC) {A : Ω → Set ℂ} (hAc : ∀ ω, IsClosed (A ω))
    (hAb : ∀ᵐ ω ∂P, Bornology.IsBounded (A ω)) (hloc : IsLocalSetDet0 P h A)
    {U : Set ℂ} (hU : IsOpen U) {G : Set Ω} (hG : MeasurableSet[localSigma0 h A] G) :
    AEEventIn P (fieldSigma0On h U) ({ω | A ω ⊆ U} ∩ G) := by
  refine conf36_trace_local0M h hAc hloc hU ?_ hG
  filter_upwards [hAb] with ω hb hAU
  exact (isCompact_of_isClosed_isBounded (hAc ω) hb).exists_thickening_subset_open hU hAU

/-- the trace lemma for an open set `U` with compact complement (no boundedness of `A`
needed) -/
theorem conf36_trace_local0C (h : Ω → DistC) {A : Ω → Set ℂ} (hAc : ∀ ω, IsClosed (A ω))
    (hloc : IsLocalSetDet0 P h A) {U : Set ℂ} (hU : IsOpen U) (hUc : IsCompact Uᶜ)
    {G : Set Ω} (hG : MeasurableSet[localSigma0 h A] G) :
    AEEventIn P (fieldSigma0On h U) ({ω | A ω ⊆ U} ∩ G) := by
  refine conf36_trace_local0M h hAc hloc hU (Eventually.of_forall fun ω hAU => ?_) hG
  obtain ⟨δ, hδ, hδC⟩ := hUc.exists_thickening_subset_open (hAc ω).isOpen_compl
    (fun x hx hxA => hx (hAU hxA))
  refine ⟨δ, hδ, fun y hy => ?_⟩
  by_contra hyU
  obtain ⟨x, hxA, hxy⟩ := mem_thickening_iff.1 hy
  exact hδC (mem_thickening_iff.2 ⟨y, hyU, by rw [dist_comm]; exact hxy⟩) hxA

omit [MeasurableSpace Ω] in
/-- `σ(h|_V mod constants) ≤ σ((h − h_ρ(w))|_K)` for `V ⊆ K` (mean-zero pairings do not see the
normalization; D108 §1) -/
theorem conf36_fieldSigma0On_le_recSigma (h : Ω → DistC) (ρ : ℝ) (w : ℂ) {V K : Set ℂ}
    (hVK : V ⊆ K) : fieldSigma0On h V ≤ recSigma h ρ w K := by
  refine le_iInf₂ fun ε hε => ?_
  refine @Measurable.comap_le _ _ (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) ρ w))
    (nbhdO ε K)) _ _ (@measurable_pi_iff Ω _ _ (fieldSigma _ _) _ _ |>.2 fun ψ => ?_)
  have e : (fun ω => h ω ψ.1.1) = fun ω => addConst (h ω) (-circleAvg (h ω) ρ w) ψ.1.1 := by
    funext ω
    rw [GFFInv.addConst_apply, ψ.1.2, zero_mul, add_zero]
  rw [e]
  exact GM.measurable_pair_fieldSigma _ ψ.1.1
    (ψ.2.trans (hVK.trans (self_subset_thickening hε K)))

/-- on `Q = {A ⊆ V}`, `V ⊆ K` open with compact complement: every event of `σ(A, h|_A)` mod constants is a.s. an event of
`σ((h − h_ρ(w))|_K)` -/
theorem conf36_trace_recSigma (h : Ω → DistC) {A : Ω → Set ℂ} (hAc : ∀ ω, IsClosed (A ω))
    (hloc : IsLocalSetDet0 P h A)
    {V K : Set ℂ} (hV : IsOpen V) (hVc : IsCompact Vᶜ) (hVK : V ⊆ K) (ρ : ℝ) (w : ℂ) {G : Set Ω}
    (hG : MeasurableSet[localSigma0 h A] G) :
    AEEventIn P (recSigma h ρ w K) ({ω | A ω ⊆ V} ∩ G) := by
  obtain ⟨F, hF, hEF⟩ := conf36_trace_local0C h hAc hloc hV hVc hG
  exact ⟨F, conf36_fieldSigma0On_le_recSigma h ρ w hVK _ hF, hEF⟩

end LQGMetric.CONF
