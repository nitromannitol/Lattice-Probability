/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasE2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE1
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Analytic relations: combinators, the frontier of the filled ball, Jordan parametrizations
(task P2-E3d, decision D65 (ii))

GM = Gwynne–Miller, arXiv:1905.00383v3. GM do not discuss measurability; own
descriptive-set-theory argument.

* `gmAn_*`: closure properties of `GMAnalyticOn` (Borel sets, `∩`, `∃` over a standard Borel
  space, measurable preimages, agreement on `L`);
* `gmE_mem_frontier_iff`: `y ∈ ∂𝓑^•_s(𝕫; d)` in countable form (`gmFrF`) for `d ∈ lenSet`;
* `gmE_ball_inter_frontier_iff`: a ball misses `∂𝓑^•_s` iff it lies in `𝓑^•_s` or in its
  complement, in countable form (`gmBallOffF`);
* `gmE_isPosJordanParam_iff`: `2π`-periodic Jordan parametrizations with angle lift are exactly
  the maps `t ↦ φ(t mod 2π)` with `φ ∈ C(ℝ/2πℤ, ℂ)` injective, with an angle lift
  `t + ψ(t mod 2π)`, `ψ ∈ C(ℝ/2πℤ, ℝ)` (Polish witness spaces).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

/-! ## Combinators -/

section An
variable {α : Type} [MeasurableSpace α]

theorem gmAn_of_measurableSet {L A : Set α} (hA : MeasurableSet A) : GMAnalyticOn L A :=
  ⟨Unit, inferInstance, inferInstance, A ×ˢ univ, hA.prod MeasurableSet.univ,
    fun a _ => by simp⟩

theorem gmAn_congr {L A B : Set α} (h : GMAnalyticOn L A) (e : ∀ a ∈ L, (a ∈ A ↔ a ∈ B)) :
    GMAnalyticOn L B := by
  obtain ⟨β, m, sb, S, hS, hA⟩ := h
  exact ⟨β, m, sb, S, hS, fun a ha => (e a ha).symm.trans (hA a ha)⟩

theorem gmAn_inter {L A B : Set α} (hA : GMAnalyticOn L A) (hB : GMAnalyticOn L B) :
    GMAnalyticOn L (A ∩ B) := by
  obtain ⟨β₁, m₁, sb₁, S₁, hS₁, h₁⟩ := hA
  obtain ⟨β₂, m₂, sb₂, S₂, hS₂, h₂⟩ := hB
  refine ⟨β₁ × β₂, inferInstance, inferInstance, {q | (q.1, q.2.1) ∈ S₁ ∧ (q.1, q.2.2) ∈ S₂},
    (hS₁.preimage (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).inter
      (hS₂.preimage (measurable_fst.prodMk (measurable_snd.comp measurable_snd))),
    fun a ha => ?_⟩
  rw [mem_inter_iff, h₁ a ha, h₂ a ha]
  constructor
  · rintro ⟨⟨b₁, hb₁⟩, ⟨b₂, hb₂⟩⟩; exact ⟨(b₁, b₂), hb₁, hb₂⟩
  · rintro ⟨⟨b₁, b₂⟩, hb₁, hb₂⟩; exact ⟨⟨b₁, hb₁⟩, ⟨b₂, hb₂⟩⟩

theorem gmAn_exists {γ : Type} [MeasurableSpace γ] [StandardBorelSpace γ] {L : Set α}
    {A : Set (α × γ)} (hA : GMAnalyticOn {p | p.1 ∈ L} A) :
    GMAnalyticOn L {a | ∃ c, (a, c) ∈ A} := by
  obtain ⟨β, m, sb, S, hS, h⟩ := hA
  refine ⟨γ × β, inferInstance, inferInstance, {q | ((q.1, q.2.1), q.2.2) ∈ S},
    hS.preimage ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)), fun a ha => ?_⟩
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨b, hb⟩ := (h (a, c) ha).1 hc
    exact ⟨(c, b), hb⟩
  · rintro ⟨⟨c, b⟩, hb⟩
    exact ⟨c, (h (a, c) ha).2 ⟨b, hb⟩⟩

theorem gmAn_preimage {α' : Type} [MeasurableSpace α'] {f : α' → α} (hf : Measurable f)
    {L A : Set α} (h : GMAnalyticOn L A) : GMAnalyticOn (f ⁻¹' L) (f ⁻¹' A) := by
  obtain ⟨β, m, sb, S, hS, hA⟩ := h
  exact ⟨β, m, sb, {q | (f q.1, q.2) ∈ S},
    hS.preimage ((hf.comp measurable_fst).prodMk measurable_snd), fun a ha => hA (f a) ha⟩

theorem gmAn_mono {L L' A : Set α} (h : GMAnalyticOn L A) (hL : L' ⊆ L) : GMAnalyticOn L' A := by
  obtain ⟨β, m, sb, S, hS, hA⟩ := h
  exact ⟨β, m, sb, S, hS, fun a ha => hA a (hL ha)⟩

end An

/-! ## The frontier of the filled ball -/

/-- `y ∈ ∂𝓑^•_s(𝕫; d)`, countable form -/
def gmFrF (d : ContMetric) (𝕫 : ℂ) (s : ℝ) (y : ℂ) : Prop :=
  ¬ gmOutF d 𝕫 s y ∧ ∀ m : ℕ, ∃ i : ℕ, dist (qd i) y < 1 / ((m : ℝ) + 1) ∧ gmOutF d 𝕫 s (qd i)

theorem gmE_isClosed_filledBall {d : ContMetric} (hd : d ∈ lenSet) (𝕫 : ℂ) (s : ℝ) :
    IsClosed (filledBall d 𝕫 s) :=
  jb_isClosed_filledBall ((gm_isCompact_closure_ballM hd 𝕫 s).isBounded.subset subset_closure)

lemma gmE_mem_filledBall_iff (d : ContMetric) (𝕫 : ℂ) (s : ℝ) (x : ℂ) :
    x ∈ filledBall d 𝕫 s ↔ ¬ gmOutF d 𝕫 s x := by
  rw [← gmE_notMem_filledBall_iff, not_not]

theorem gmE_mem_frontier_iff {d : ContMetric} (hd : d ∈ lenSet) (𝕫 : ℂ) (s : ℝ) (y : ℂ) :
    y ∈ frontier (filledBall d 𝕫 s) ↔ gmFrF d 𝕫 s y := by
  have hK := gmE_isClosed_filledBall hd 𝕫 s
  rw [frontier_eq_closure_inter_closure, hK.closure_eq, mem_inter_iff,
    gmE_mem_closure_open_iff hK.isOpen_compl]
  simp only [gmFrF, mem_compl_iff, gmE_mem_filledBall_iff, not_not]

lemma gmE_measurable_outF (𝕫 : ℂ) :
    Measurable fun p : ContMetric × ℝ × ℂ => gmOutF p.1 𝕫 p.2.1 p.2.2 :=
  measurableSet_setOfPred.1 (gmE_measurableSet_outF 𝕫)

lemma gmE_measurable_outF_comp {X : Type} [MeasurableSpace X] {f : X → ContMetric} {s : X → ℝ}
    {x : X → ℂ} (hf : Measurable f) (hs : Measurable s) (hx : Measurable x) (𝕫 : ℂ) :
    Measurable fun q => gmOutF (f q) 𝕫 (s q) (x q) :=
  (gmE_measurable_outF 𝕫).comp (hf.prodMk (hs.prodMk hx))

lemma gmE_measurable_frF_comp {X : Type} [MeasurableSpace X] {f : X → ContMetric} {s : X → ℝ}
    {x : X → ℂ} (hf : Measurable f) (hs : Measurable s) (hx : Measurable x) (𝕫 : ℂ) :
    Measurable fun q => gmFrF (f q) 𝕫 (s q) (x q) :=
  (gmE_measurable_outF_comp hf hs hx 𝕫).not.and (Measurable.forall fun m => Measurable.exists
    fun i => (measurableSet_setOfPred.1 (measurableSet_lt (measurable_const.dist hx)
      measurable_const)).and (gmE_measurable_outF_comp hf hs measurable_const 𝕫))

/-- a ball misses `∂𝓑^•_s`, countable form -/
def gmBallOffF (d : ContMetric) (𝕫 : ℂ) (s : ℝ) (c : ℂ) (r : ℝ) : Prop :=
  (∀ i : ℕ, dist (qd i) c < r → ¬ gmOutF d 𝕫 s (qd i)) ∨
    ((∀ i : ℕ, dist (qd i) c < r → s ≤ d.1 (𝕫, qd i)) ∧ gmOutF d 𝕫 s c)

lemma gmE_notMem_filledBall_iff' (d : ContMetric) (𝕫 : ℂ) (s : ℝ) (x : ℂ) :
    x ∉ filledBall d 𝕫 s ↔ x ∈ (closure (ballM d 𝕫 s))ᶜ ∧
      ¬ Bornology.IsBounded (connectedComponentIn (closure (ballM d 𝕫 s))ᶜ x) := by
  simp only [filledBall, mem_union, mem_ofPred_eq, not_or, not_and, mem_compl_iff]
  tauto

theorem gmE_ball_inter_frontier_iff {d : ContMetric} (hd : d ∈ lenSet) (𝕫 : ℂ) (s : ℝ) (c : ℂ)
    {r : ℝ} (hr : 0 < r) :
    ball c r ∩ frontier (filledBall d 𝕫 s) = ∅ ↔ gmBallOffF d 𝕫 s c r := by
  set K := filledBall d 𝕫 s
  have hK := gmE_isClosed_filledBall hd 𝕫 s
  have hdq : ∀ V : Set ℂ, IsOpen V → V ⊆ closure (V ∩ range qd) := fun V hV =>
    denseRange_qd.open_subset_closure_inter hV
  have e1 : ball c r ∩ frontier K = ∅ ↔ ball c r ⊆ K ∨ ball c r ⊆ Kᶜ := by
    constructor
    · intro h
      have hsub : ball c r ⊆ interior K ∪ Kᶜ := fun v hv => by
        by_cases hvK : v ∈ K
        · left
          by_contra hint
          have : v ∈ frontier K := by rw [hK.frontier_eq]; exact ⟨hvK, hint⟩
          exact (eq_empty_iff_forall_notMem.1 h) v ⟨hv, this⟩
        · exact Or.inr hvK
      rcases (convex_ball c r).isPreconnected.subset_or_subset isOpen_interior hK.isOpen_compl
        (disjoint_compl_right.mono_left interior_subset) hsub with h1 | h1
      · exact Or.inl (h1.trans interior_subset)
      · exact Or.inr h1
    · rintro (h | h)
      · refine eq_empty_iff_forall_notMem.2 fun v ⟨hv, hvf⟩ => ?_
        rw [hK.frontier_eq] at hvf
        exact hvf.2 (interior_maximal h isOpen_ball hv)
      · exact eq_empty_iff_forall_notMem.2 fun v ⟨hv, hvf⟩ => h hv (hK.frontier_subset hvf)
  rw [e1, gmBallOffF]
  have e2 : ball c r ⊆ K ↔ ∀ i : ℕ, dist (qd i) c < r → ¬ gmOutF d 𝕫 s (qd i) := by
    constructor
    · intro h i hi; exact (gmE_mem_filledBall_iff d 𝕫 s _).1 (h (mem_ball.2 hi))
    · intro h v hv
      have := hdq _ isOpen_ball hv
      refine hK.closure_subset (closure_mono ?_ this)
      rintro _ ⟨hw, i, rfl⟩
      exact (gmE_mem_filledBall_iff d 𝕫 s _).2 (h i hw)
  have e3 : ball c r ⊆ Kᶜ ↔ (∀ i : ℕ, dist (qd i) c < r → s ≤ d.1 (𝕫, qd i)) ∧
      gmOutF d 𝕫 s c := by
    constructor
    · intro h
      refine ⟨fun i hi => ?_, (gmE_notMem_filledBall_iff d 𝕫 s c).1 (h (mem_ball_self hr))⟩
      have := ((gmE_notMem_filledBall_iff' d 𝕫 s _).1 (h (mem_ball.2 hi))).1
      by_contra hlt
      exact this (subset_closure (show qd i ∈ ballM d 𝕫 s from not_le.1 hlt))
    · rintro ⟨h1, h2⟩
      have hO : ball c r ⊆ (closure (ballM d 𝕫 s))ᶜ := by
        intro v hv hvc
        have h3 := isOpen_ball.inter_closure ⟨hv, hvc⟩
        obtain ⟨i, hi⟩ := denseRange_qd.exists_mem_open
          (isOpen_ball.inter (gmE_isOpen_ballM d 𝕫 s)) (closure_nonempty_iff.1 ⟨v, h3⟩)
        exact not_le.2 hi.2 (h1 i hi.1)
      have hc := (gmE_notMem_filledBall_iff' d 𝕫 s c).1
        ((gmE_notMem_filledBall_iff d 𝕫 s c).2 h2)
      intro v hv
      have hsub := (convex_ball c r).isPreconnected.subset_connectedComponentIn
        (mem_ball_self hr) hO
      refine (gmE_notMem_filledBall_iff' d 𝕫 s v).2 ⟨hO hv, ?_⟩
      rw [← connectedComponentIn_eq (hsub hv)]
      exact hc.2
  rw [e2, e3]

lemma gmE_measurable_ballOffF_comp {X : Type} [MeasurableSpace X] {f : X → ContMetric}
    {s : X → ℝ} (hf : Measurable f) (hs : Measurable s) (𝕫 c : ℂ) (r : ℝ) :
    Measurable fun q => gmBallOffF (f q) 𝕫 (s q) c r :=
  (Measurable.forall fun i => measurable_const.imp
      (gmE_measurable_outF_comp hf hs measurable_const 𝕫).not).or
    ((Measurable.forall fun i => measurable_const.imp (measurableSet_setOfPred.1
      (measurableSet_le hs ((measurable_apply (𝕫, qd i)).comp hf)))).and
      (gmE_measurable_outF_comp hf hs measurable_const 𝕫))

end LQGMetric.GM
