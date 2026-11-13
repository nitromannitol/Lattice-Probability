/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cP.LocalBorel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.LocalEvents
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.JointMeasurable

/-!
# The local escape and inner-degree events are Borel

`SegSpace = ℚ × ℚ → C(ℝ, ℂ)` carries the product of the compact-open Borel σ-algebras, which is the Borel
σ-algebra of the product topology (countable product of second-countable spaces). For disk-shaped
`S = B_r(w)` and `U = B_R(w')`, the events `locEsc` and `locInner` of `GMS4cP/LocalEvents.lean` are
countable unions of projections of closed sets along σ-compact factors, together with the open
segment-separation conditions; hence Borel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4cP

open MatedCRTHarmonic.GMS4b

/-- The projection of a closed set along a σ-compact factor is `F_σ`, hence Borel. -/
theorem measurableSet_exists_of_isClosed_sigmaCompact {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [TopologicalSpace Y] [SigmaCompactSpace Y]
    {F : Set (X × Y)} (hF : IsClosed F) : MeasurableSet {x | ∃ y, (x, y) ∈ F} := by
  have heq : {x | ∃ y, (x, y) ∈ F} =
      ⋃ n : ℕ, {x | ∃ y ∈ compactCovering Y n, (x, y) ∈ F} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨n, hn⟩ := exists_mem_compactCovering y
      exact ⟨n, y, hn, hy⟩
    · rintro ⟨n, y, -, hy⟩
      exact ⟨y, hy⟩
  rw [heq]
  exact MeasurableSet.iUnion fun n =>
    (isClosed_exists_mem_of_isCompact (isCompact_compactCovering Y n) hF).measurableSet

theorem continuous_segEval {Z : Type*} [TopologicalSpace Z] {f : Z → SegSpace} {g : Z → ℝ}
    (hf : Continuous f) (hg : Continuous g) (q : ℚ × ℚ) :
    Continuous fun z => f z q (g z) :=
  continuous_eval.comp' (((continuous_apply q).comp' hf).prodMk hg)

/-- The window diameter `diam σ_q([s − ε, s + ε])` is jointly continuous. -/
theorem continuous_segWindowDiam {Z : Type*} [TopologicalSpace Z] {f : Z → SegSpace}
    {g : Z → ℝ} (hf : Continuous f) (hg : Continuous g) (ε : ℝ) (q : ℚ × ℚ) :
    Continuous fun z => diam (locWindow ε (f z q) (g z)) := by
  have hc : Continuous fun z => curveShift (f z q) (g z) :=
    continuous_curveShift.comp' (((continuous_apply q).comp' hf).prodMk hg)
  have h : ∀ z, diam (locWindow ε (f z q) (g z)) =
      diam (locWindow ε (curveShift (f z q) (g z)) 0) := fun z => by
    rw [← locWindow_curveShift]
  simp only [h]
  exact (continuous_diam_window ε 0).comp' hc

theorem mem_ball_iff_exists_nat {z w : ℂ} {r : ℝ} :
    z ∈ ball w r ↔ ∃ n : ℕ, dist z w ≤ r - 1 / ((n : ℝ) + 1) := by
  rw [mem_ball]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
    exact ⟨n, by linarith⟩
  · rintro ⟨n, hn⟩
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- **`locEsc` is Borel** for disks `S = B_r(w)`, `U = B_R(w')`. -/
theorem measurableSet_locEsc (L : Set (ℚ × ℚ)) (w w' : ℂ) (r R ε : ℝ) :
    MeasurableSet (locEsc L (ball w r) (ball w' R) ε) := by
  let F : ℚ × ℚ → ℕ → Set (SegSpace × (ℝ × ℂ)) := fun q n =>
    {p | dist (p.1 q p.2.1) w ≤ r - 1 / ((n : ℝ) + 1) ∧
      dist p.2.2 (p.1 q p.2.1) ≤ 4 * diam (locWindow ε (p.1 q) p.2.1) ∧ R ≤ dist p.2.2 w'}
  have hF : ∀ q n, IsClosed (F q n) := by
    intro q n
    have hev : Continuous fun p : SegSpace × (ℝ × ℂ) => p.1 q p.2.1 :=
      continuous_segEval continuous_fst (continuous_fst.comp continuous_snd) q
    have hdiam : Continuous fun p : SegSpace × (ℝ × ℂ) => diam (locWindow ε (p.1 q) p.2.1) :=
      continuous_segWindowDiam continuous_fst (continuous_fst.comp continuous_snd) ε q
    have hp : Continuous fun p : SegSpace × (ℝ × ℂ) => p.2.2 := continuous_snd.comp continuous_snd
    exact (isClosed_le (hev.dist continuous_const) continuous_const).inter
      ((isClosed_le (hp.dist hev) (continuous_const.mul hdiam)).inter
        (isClosed_le continuous_const (hp.dist continuous_const)))
  have heq : locEsc L (ball w r) (ball w' R) ε =
      ⋃ q ∈ L, ⋃ n : ℕ, {σ | ∃ y, (σ, y) ∈ F q n} := by
    ext σ
    simp only [locEsc, mem_ofPred_eq, mem_iUnion, exists_prop, F]
    constructor
    · rintro ⟨q, hq, s, hs, hnot⟩
      obtain ⟨n, hn⟩ := mem_ball_iff_exists_nat.1 hs
      rw [not_subset] at hnot
      obtain ⟨p, hp, hpU⟩ := hnot
      rw [locBall, mem_closedBall] at hp
      rw [mem_ball, not_lt] at hpU
      exact ⟨q, hq, n, (s, p), hn, hp, hpU⟩
    · rintro ⟨q, hq, n, ⟨s, p⟩, hn, hp, hpU⟩
      refine ⟨q, hq, s, mem_ball_iff_exists_nat.2 ⟨n, hn⟩, ?_⟩
      rw [not_subset]
      exact ⟨p, by rw [locBall, mem_closedBall]; exact hp, by rw [mem_ball, not_lt]; exact hpU⟩
  rw [heq]
  exact MeasurableSet.biUnion (Set.to_countable L) fun q _ =>
    MeasurableSet.iUnion fun n => measurableSet_exists_of_isClosed_sigmaCompact (hF q n)

/-- Coordinates of the local inner-degree family. -/
theorem isLocFamily_iff (L : Set (ℚ × ℚ)) (ε : ℝ) (σ : SegSpace) (q : ℚ × ℚ) (s : ℝ) {N : ℕ}
    (lab : Fin N → ℚ × ℚ) (b : Fin N → ℝ) :
    IsLocFamily L ε σ q s lab b ↔
      (∀ i, lab i ∈ L) ∧
      (∀ i j, i ≠ j → lab i = lab j → min (b i + ε) (b j + ε) ≤ max (b i) (b j)) ∧
      (∀ i j, lab i ≠ lab j → σ (lab i) ≠ σ (lab j)) ∧
      (∀ i, ∀ u ∈ Icc (0 : ℝ) ε,
        dist (σ (lab i) (b i + u)) (σ q s) ≤ 4 * diam (locWindow ε (σ q) s)) ∧
      (∀ i, ∃ y ∈ Icc (0 : ℝ) ε ×ˢ Icc (-ε) ε, σ (lab i) (b i + y.1) = σ q (s + y.2)) := by
  simp only [IsLocFamily, Ioo_disjoint_Ioo]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  rw [← forall_and]
  refine forall_congr' fun i => and_congr ?_ ?_
  · constructor
    · intro h u hu
      have := h (mem_image_of_mem (σ (lab i))
        (show b i + u ∈ Icc (b i) (b i + ε) from ⟨by linarith [hu.1], by linarith [hu.2]⟩))
      exact mem_closedBall.mp this
    · rintro h _ ⟨t, ht, rfl⟩
      have := h (t - b i) ⟨by linarith [ht.1], by linarith [ht.2]⟩
      rw [add_sub_cancel] at this
      exact mem_closedBall.mpr this
  · constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, ⟨u, hu, hut⟩⟩
      refine ⟨(t - b i, u - s), ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩,
        ⟨by linarith [hu.1], by linarith [hu.2]⟩⟩, ?_⟩
      simp only [add_sub_cancel]
      exact hut.symm
    · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, h⟩
      exact ⟨σ (lab i) (b i + u), ⟨b i + u, ⟨by linarith [hu.1], by linarith [hu.2]⟩, rfl⟩,
        ⟨s + v, ⟨by linarith [hv.1], by linarith [hv.2]⟩, h.symm⟩⟩

/-- **`locInner` is Borel** for disks `S = B_r(w)`, `U = B_R(w')`. -/
theorem measurableSet_locInner (L : Set (ℚ × ℚ)) (w w' : ℂ) (r R ε : ℝ) (N : ℕ) :
    MeasurableSet (locInner L (ball w r) (ball w' R) ε N) := by
  classical
  -- the closed part, for fixed labels
  let G : ℚ × ℚ → (Fin N → ℚ × ℚ) → ℕ → Set (SegSpace × (ℝ × (Fin N → ℝ))) := fun q lab n =>
    {p | dist (p.1 q p.2.1) w ≤ r - 1 / ((n : ℝ) + 1)} ∩
      ((⋂ i, ⋂ j, ⋂ (_ : i ≠ j), ⋂ (_ : lab i = lab j),
        {p | min (p.2.2 i + ε) (p.2.2 j + ε) ≤ max (p.2.2 i) (p.2.2 j)}) ∩
      ((⋂ i, ⋂ u ∈ Icc (0 : ℝ) ε,
        {p | dist (p.1 (lab i) (p.2.2 i + u)) (p.1 q p.2.1) ≤
          4 * diam (locWindow ε (p.1 q) p.2.1)}) ∩
      (⋂ i, {p | ∃ y ∈ Icc (0 : ℝ) ε ×ˢ Icc (-ε) ε,
        p.1 (lab i) (p.2.2 i + y.1) = p.1 q (p.2.1 + y.2)})))
  have hG : ∀ q lab n, IsClosed (G q lab n) := by
    intro q lab n
    have hs : Continuous fun p : SegSpace × (ℝ × (Fin N → ℝ)) => p.2.1 :=
      continuous_fst.comp continuous_snd
    have hb : ∀ i, Continuous fun p : SegSpace × (ℝ × (Fin N → ℝ)) => p.2.2 i := fun i =>
      (continuous_apply i).comp (continuous_snd.comp continuous_snd)
    have hev : Continuous fun p : SegSpace × (ℝ × (Fin N → ℝ)) => p.1 q p.2.1 :=
      continuous_segEval continuous_fst hs q
    have hdiam : Continuous fun p : SegSpace × (ℝ × (Fin N → ℝ)) =>
        diam (locWindow ε (p.1 q) p.2.1) :=
      continuous_segWindowDiam continuous_fst hs ε q
    have hevi : ∀ i (u : ℝ), Continuous fun p : SegSpace × (ℝ × (Fin N → ℝ)) =>
        p.1 (lab i) (p.2.2 i + u) := fun i u =>
      continuous_segEval continuous_fst ((hb i).add continuous_const) (lab i)
    have h1 : IsClosed {p : SegSpace × (ℝ × (Fin N → ℝ)) |
        dist (p.1 q p.2.1) w ≤ r - 1 / ((n : ℝ) + 1)} :=
      isClosed_le (hev.dist continuous_const) continuous_const
    have h2 : IsClosed (⋂ i, ⋂ j, ⋂ (_ : i ≠ j), ⋂ (_ : lab i = lab j),
        {p : SegSpace × (ℝ × (Fin N → ℝ)) |
          min (p.2.2 i + ε) (p.2.2 j + ε) ≤ max (p.2.2 i) (p.2.2 j)}) := by
      refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => ?_
      exact isClosed_le (((hb i).add continuous_const).min ((hb j).add continuous_const))
        ((hb i).max (hb j))
    have h3 : IsClosed (⋂ i, ⋂ u ∈ Icc (0 : ℝ) ε,
        {p : SegSpace × (ℝ × (Fin N → ℝ)) | dist (p.1 (lab i) (p.2.2 i + u)) (p.1 q p.2.1) ≤
          4 * diam (locWindow ε (p.1 q) p.2.1)}) := by
      refine isClosed_iInter fun i => isClosed_iInter fun u => isClosed_iInter fun _ => ?_
      exact isClosed_le ((hevi i u).dist hev) (continuous_const.mul hdiam)
    have h4 : IsClosed (⋂ i, {p : SegSpace × (ℝ × (Fin N → ℝ)) |
        ∃ y ∈ Icc (0 : ℝ) ε ×ˢ Icc (-ε) ε,
          p.1 (lab i) (p.2.2 i + y.1) = p.1 q (p.2.1 + y.2)}) := by
      refine isClosed_iInter fun i => ?_
      have hF : IsClosed {z : (SegSpace × (ℝ × (Fin N → ℝ))) × (ℝ × ℝ) |
          z.1.1 (lab i) (z.1.2.2 i + z.2.1) = z.1.1 q (z.1.2.1 + z.2.2)} :=
        isClosed_eq
          (continuous_segEval (continuous_fst.comp continuous_fst)
            (((hb i).comp continuous_fst).add (continuous_fst.comp continuous_snd)) (lab i))
          (continuous_segEval (continuous_fst.comp continuous_fst)
            ((hs.comp continuous_fst).add (continuous_snd.comp continuous_snd)) q)
      exact isClosed_exists_mem_of_isCompact
        ((isCompact_Icc : IsCompact (Icc (0 : ℝ) ε)).prod
          (isCompact_Icc : IsCompact (Icc (-ε) ε))) hF
    exact h1.inter (h2.inter (h3.inter h4))
  let Sep : (Fin N → ℚ × ℚ) → Set SegSpace := fun lab =>
    ⋂ i, ⋂ j, {σ | lab i ≠ lab j → σ (lab i) ≠ σ (lab j)}
  have hSep : ∀ lab, MeasurableSet (Sep lab) := by
    intro lab
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    by_cases hij : lab i = lab j
    · simp only [hij, ne_eq, not_true_eq_false, IsEmpty.forall_iff, ofPred_true,
        MeasurableSet.univ]
    · have hcl : IsClosed {σ : SegSpace | σ (lab i) = σ (lab j)} :=
        isClosed_eq (continuous_apply _) (continuous_apply _)
      have : {σ : SegSpace | lab i ≠ lab j → σ (lab i) ≠ σ (lab j)} =
          {σ : SegSpace | σ (lab i) = σ (lab j)}ᶜ := by
        ext σ
        simp [hij]
      rw [this]
      exact hcl.measurableSet.compl
  let Lab : Set (Fin N → ℚ × ℚ) := {lab | ∀ i, lab i ∈ L}
  have heq : locInner L (ball w r) (ball w' R) ε N =
      (⋃ q ∈ L, ⋃ lab ∈ Lab, ⋃ n : ℕ, Sep lab ∩ {σ | ∃ y, (σ, y) ∈ G q lab n}) \
        locEsc L (ball w r) (ball w' R) ε := by
    ext σ
    simp only [locInner, Set.mem_sdiff, mem_ofPred_eq, mem_iUnion, exists_prop, mem_inter_iff, G,
      Sep, Lab, mem_iInter, isLocFamily_iff]
    refine and_congr ?_ Iff.rfl
    constructor
    · rintro ⟨q, hq, s, hs, lab, b, hL, hdisj, hsep, hcell, hwin⟩
      obtain ⟨n, hn⟩ := mem_ball_iff_exists_nat.1 hs
      exact ⟨q, hq, lab, hL, n, fun i j => hsep i j, (s, b), hn, hdisj, hcell, hwin⟩
    · rintro ⟨q, hq, lab, hL, n, hsep, ⟨s, b⟩, hn, hdisj, hcell, hwin⟩
      exact ⟨q, hq, s, mem_ball_iff_exists_nat.2 ⟨n, hn⟩, lab, b, hL, hdisj, hsep, hcell, hwin⟩
  rw [heq]
  refine MeasurableSet.diff ?_ (measurableSet_locEsc L w w' r R ε)
  refine MeasurableSet.biUnion (Set.to_countable L) fun q _ => ?_
  refine MeasurableSet.biUnion (Set.to_countable Lab) fun lab _ => ?_
  exact MeasurableSet.iUnion fun n =>
    (hSep lab).inter (measurableSet_exists_of_isClosed_sigmaCompact (hG q lab n))

end MatedCRTHarmonic.GMS4cP
