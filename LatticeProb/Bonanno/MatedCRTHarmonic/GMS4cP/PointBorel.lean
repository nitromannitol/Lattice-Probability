/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cP.PointBorel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.PointPrime
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.LocalBorel
import LatticeProb.Bonanno.LQGMetric.Meas.UM

/-!
# Universal measurability of the local all-visit point observables

The local window test, `DA′`, `deg′_in` and `deg′_out` of `GMS4cP/PointPrime.lean` are suprema over the local
visits `{(q, s) : σ q s = z}`; their threshold sets are projections of Borel relations on
`SegSpace × (parameters)` along standard Borel parameter spaces, hence universally measurable (Lusin;
`LQGMetric.UMeasurableSet.setOf_exists`). Consequently the observables are null measurable for every finite
measure on `SegSpace`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4cP

open MatedCRTHarmonic.GMS4b
open LQGMetric (UMeasurableSet)

attribute [local instance] Classical.propDecidable

/-- `k ≤ sup` for a positive integer `k` is witnessed by one term. -/
theorem natCast_le_iSup_iff {ι : Sort*} {f : ι → ℕ∞} {k : ℕ} (hk : 1 ≤ k) :
    (k : ℕ∞) ≤ ⨆ i, f i ↔ ∃ i, (k : ℕ∞) ≤ f i := by
  constructor
  · intro h
    have hlt : ((k - 1 : ℕ) : ℕ∞) < ⨆ i, f i :=
      lt_of_lt_of_le (by exact_mod_cast Nat.sub_lt hk one_pos) h
    obtain ⟨i, hi⟩ := lt_iSup_iff.1 hlt
    refine ⟨i, ?_⟩
    have h2 : ((k - 1 : ℕ) : ℕ∞) + 1 ≤ f i := Order.add_one_le_of_lt hi
    have e : ((k - 1 : ℕ) : ℕ∞) + 1 = (k : ℕ∞) := by
      have : k - 1 + 1 = k := Nat.sub_add_cancel hk
      exact_mod_cast this
    rwa [e] at h2
  · rintro ⟨i, hi⟩
    exact hi.trans (le_iSup f i)

/-- A countable union over labels of universally measurable sets. -/
theorem um_iUnion_label {S : ℚ × ℚ → Set SegSpace} (h : ∀ q, UMeasurableSet (S q)) :
    UMeasurableSet (⋃ q, S q) :=
  UMeasurableSet.iUnion h

section

variable (L : Set (ℚ × ℚ)) (z : ℂ) (ε r₀ : ℝ)

theorem um_not_locWinOK : UMeasurableSet {σ : SegSpace | ¬ locWinOK L z ε r₀ σ} := by
  let R : ℚ × ℚ → Set (SegSpace × ℝ) := fun q =>
    {p | p.1 q p.2 = z ∧ r₀ < diam (locWindow ε (p.1 q) p.2)}
  have hR : ∀ q, MeasurableSet (R q) := by
    intro q
    have hev : Continuous fun p : SegSpace × ℝ => p.1 q p.2 :=
      continuous_segEval continuous_fst continuous_snd q
    have hd : Continuous fun p : SegSpace × ℝ => diam (locWindow ε (p.1 q) p.2) :=
      continuous_segWindowDiam continuous_fst continuous_snd ε q
    exact (isClosed_eq hev continuous_const).measurableSet.inter
      (isOpen_lt continuous_const hd).measurableSet
  have heq : {σ : SegSpace | ¬ locWinOK L z ε r₀ σ} =
      ⋃ q, (if q ∈ L then {σ | ∃ s, (σ, s) ∈ R q} else ∅) := by
    ext σ
    simp only [locWinOK, IsLocVisit, mem_ofPred_eq, mem_iUnion, R]
    constructor
    · intro h
      push Not at h
      obtain ⟨q, s, ⟨hq, hz⟩, hd⟩ := h
      exact ⟨q, by simp only [hq, ite_true, mem_ofPred_eq]; exact ⟨s, hz, hd⟩⟩
    · rintro ⟨q, hq⟩
      split_ifs at hq with hqL
      · obtain ⟨s, hz, hd⟩ := hq
        intro hall
        exact absurd (hall q s ⟨hqL, hz⟩) (not_le.2 hd)
      · exact absurd hq (Set.notMem_empty σ)
  rw [heq]
  refine um_iUnion_label fun q => ?_
  split_ifs
  · exact UMeasurableSet.setOf_exists (hR q)
  · exact UMeasurableSet.empty

theorem um_lt_locDAPrime (a : ℝ≥0∞) :
    UMeasurableSet {σ : SegSpace | a < locDAPrime L z ε σ} := by
  let R : ℚ × ℚ → Set (SegSpace × ℝ) := fun q =>
    {p | p.1 q p.2 = z ∧ a < locDA ε (p.1 q) p.2}
  have hR : ∀ q, MeasurableSet (R q) := by
    intro q
    have hev : Continuous fun p : SegSpace × ℝ => p.1 q p.2 :=
      continuous_segEval continuous_fst continuous_snd q
    have hpair : Continuous fun p : SegSpace × ℝ => ((p.1 q, p.2) : C(ℝ, ℂ) × ℝ) :=
      ((continuous_apply q).comp continuous_fst).prodMk continuous_snd
    have hsh : Continuous fun p : SegSpace × ℝ => curveShift (p.1 q) p.2 :=
      continuous_curveShift.comp hpair
    have hda : Measurable fun p : SegSpace × ℝ => locDA ε (p.1 q) p.2 := by
      have h := (measurable_locDA ε 0).comp hsh.measurable
      convert h using 1
      funext p
      exact locDA_curveShift ε (p.1 q) p.2
    exact (isClosed_eq hev continuous_const).measurableSet.inter
      (measurableSet_lt measurable_const hda)
  have heq : {σ : SegSpace | a < locDAPrime L z ε σ} =
      ⋃ q, (if q ∈ L then {σ | ∃ s, (σ, s) ∈ R q} else ∅) := by
    ext σ
    simp only [locDAPrime, IsLocVisit, mem_ofPred_eq, mem_iUnion, R, lt_iSup_iff]
    constructor
    · rintro ⟨q, s, ⟨hq, hz⟩, hd⟩
      exact ⟨q, by simp only [hq, ite_true, mem_ofPred_eq]; exact ⟨s, hz, hd⟩⟩
    · rintro ⟨q, hq⟩
      split_ifs at hq with hqL
      · obtain ⟨s, hz, hd⟩ := hq
        exact ⟨q, s, ⟨hqL, hz⟩, hd⟩
      · exact absurd hq (Set.notMem_empty σ)
  rw [heq]
  refine um_iUnion_label fun q => ?_
  split_ifs
  · exact UMeasurableSet.setOf_exists (hR q)
  · exact UMeasurableSet.empty

/-- The label-separation condition depends only on the segments and is Borel. -/
theorem measurableSet_sep {N : ℕ} (lab : Fin N → ℚ × ℚ) :
    MeasurableSet {σ : SegSpace | ∀ i j, lab i ≠ lab j → σ (lab i) ≠ σ (lab j)} := by
  have heq : {σ : SegSpace | ∀ i j, lab i ≠ lab j → σ (lab i) ≠ σ (lab j)} =
      ⋂ i, ⋂ j, {σ | lab i ≠ lab j → σ (lab i) ≠ σ (lab j)} := by
    ext σ
    simp
  rw [heq]
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

theorem um_le_locDegInPrime (k : ℕ) (hk : 1 ≤ k) :
    UMeasurableSet {σ : SegSpace | (k : ℕ∞) ≤ locDegInPrime L z ε σ} := by
  let R : ℚ × ℚ → (Fin k → ℚ × ℚ) → Set (SegSpace × (ℝ × (Fin k → ℝ))) := fun q lab =>
    {p | p.1 q p.2.1 = z} ∩
      ((⋂ i, ⋂ j, ⋂ (_ : i ≠ j), ⋂ (_ : lab i = lab j),
        {p | min (p.2.2 i + ε) (p.2.2 j + ε) ≤ max (p.2.2 i) (p.2.2 j)}) ∩
      ({p | ∀ i j, lab i ≠ lab j → p.1 (lab i) ≠ p.1 (lab j)} ∩
      ((⋂ i, ⋂ u ∈ Icc (0 : ℝ) ε,
        {p | dist (p.1 (lab i) (p.2.2 i + u)) (p.1 q p.2.1) ≤
          4 * diam (locWindow ε (p.1 q) p.2.1)}) ∩
      (⋂ i, {p | ∃ y ∈ Icc (0 : ℝ) ε ×ˢ Icc (-ε) ε,
        p.1 (lab i) (p.2.2 i + y.1) = p.1 q (p.2.1 + y.2)}))))
  have hR : ∀ q lab, MeasurableSet (R q lab) := by
    intro q lab
    have hs : Continuous fun p : SegSpace × (ℝ × (Fin k → ℝ)) => p.2.1 :=
      continuous_fst.comp continuous_snd
    have hb : ∀ i, Continuous fun p : SegSpace × (ℝ × (Fin k → ℝ)) => p.2.2 i := fun i =>
      (continuous_apply i).comp (continuous_snd.comp continuous_snd)
    have hev : Continuous fun p : SegSpace × (ℝ × (Fin k → ℝ)) => p.1 q p.2.1 :=
      continuous_segEval continuous_fst hs q
    have hdiam : Continuous fun p : SegSpace × (ℝ × (Fin k → ℝ)) =>
        diam (locWindow ε (p.1 q) p.2.1) :=
      continuous_segWindowDiam continuous_fst hs ε q
    have hevi : ∀ i (u : ℝ), Continuous fun p : SegSpace × (ℝ × (Fin k → ℝ)) =>
        p.1 (lab i) (p.2.2 i + u) := fun i u =>
      continuous_segEval continuous_fst ((hb i).add continuous_const) (lab i)
    have h1 : MeasurableSet {p : SegSpace × (ℝ × (Fin k → ℝ)) | p.1 q p.2.1 = z} :=
      (isClosed_eq hev continuous_const).measurableSet
    have h2 : MeasurableSet (⋂ i, ⋂ j, ⋂ (_ : i ≠ j), ⋂ (_ : lab i = lab j),
        {p : SegSpace × (ℝ × (Fin k → ℝ)) |
          min (p.2.2 i + ε) (p.2.2 j + ε) ≤ max (p.2.2 i) (p.2.2 j)}) := by
      refine (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => ?_).measurableSet
      exact isClosed_le (((hb i).add continuous_const).min ((hb j).add continuous_const))
        ((hb i).max (hb j))
    have h3 : MeasurableSet {p : SegSpace × (ℝ × (Fin k → ℝ)) |
        ∀ i j, lab i ≠ lab j → p.1 (lab i) ≠ p.1 (lab j)} :=
      measurable_fst (measurableSet_sep lab)
    have h4 : MeasurableSet (⋂ i, ⋂ u ∈ Icc (0 : ℝ) ε,
        {p : SegSpace × (ℝ × (Fin k → ℝ)) | dist (p.1 (lab i) (p.2.2 i + u)) (p.1 q p.2.1) ≤
          4 * diam (locWindow ε (p.1 q) p.2.1)}) := by
      refine (isClosed_iInter fun i => isClosed_iInter fun u => isClosed_iInter fun _ =>
        ?_).measurableSet
      exact isClosed_le ((hevi i u).dist hev) (continuous_const.mul hdiam)
    have h5 : MeasurableSet (⋂ i, {p : SegSpace × (ℝ × (Fin k → ℝ)) |
        ∃ y ∈ Icc (0 : ℝ) ε ×ˢ Icc (-ε) ε,
          p.1 (lab i) (p.2.2 i + y.1) = p.1 q (p.2.1 + y.2)}) := by
      refine (isClosed_iInter fun i => ?_).measurableSet
      have hF : IsClosed {w : (SegSpace × (ℝ × (Fin k → ℝ))) × (ℝ × ℝ) |
          w.1.1 (lab i) (w.1.2.2 i + w.2.1) = w.1.1 q (w.1.2.1 + w.2.2)} :=
        isClosed_eq
          (continuous_segEval (continuous_fst.comp continuous_fst)
            (((hb i).comp continuous_fst).add (continuous_fst.comp continuous_snd)) (lab i))
          (continuous_segEval (continuous_fst.comp continuous_fst)
            ((hs.comp continuous_fst).add (continuous_snd.comp continuous_snd)) q)
      exact isClosed_exists_mem_of_isCompact
        ((isCompact_Icc : IsCompact (Icc (0 : ℝ) ε)).prod
          (isCompact_Icc : IsCompact (Icc (-ε) ε))) hF
    exact h1.inter (h2.inter (h3.inter (h4.inter h5)))
  have heq : {σ : SegSpace | (k : ℕ∞) ≤ locDegInPrime L z ε σ} =
      ⋃ q, ⋃ lab : Fin k → ℚ × ℚ,
        (if q ∈ L ∧ ∀ i, lab i ∈ L then {σ | ∃ p, (σ, p) ∈ R q lab} else ∅) := by
    ext σ
    simp only [locDegInPrime, mem_ofPred_eq, mem_iUnion]
    rw [natCast_le_iSup_iff hk]
    simp only [natCast_le_iSup_iff hk, le_locInAt_iff, isLocFamily_iff, IsLocVisit]
    constructor
    · rintro ⟨q, s, ⟨hq, hz⟩, lab, b, hL, hdisj, hsep, hcell, hwin⟩
      refine ⟨q, lab, ?_⟩
      rw [ite_eq_left ⟨hq, hL⟩]
      refine ⟨(s, b), hz, ?_, hsep, ?_, ?_⟩
      · simp only [mem_iInter, mem_ofPred_eq]
        exact hdisj
      · simp only [mem_iInter, mem_ofPred_eq]
        exact fun i u hu => hcell i u hu
      · simp only [mem_iInter, mem_ofPred_eq]
        exact hwin
    · rintro ⟨q, lab, hmem⟩
      split_ifs at hmem with hql
      · obtain ⟨⟨s, b⟩, hz, hdisj, hsep, hcell, hwin⟩ := hmem
        simp only [mem_iInter, mem_ofPred_eq] at hdisj hcell hwin
        exact ⟨q, s, ⟨hql.1, hz⟩, lab, b, hql.2, fun i j hij hl => hdisj i j hij hl, hsep,
          fun i u hu => hcell i u hu, hwin⟩
      · exact absurd hmem (Set.notMem_empty σ)
  rw [heq]
  refine um_iUnion_label fun q => UMeasurableSet.iUnion fun lab => ?_
  split_ifs
  · exact UMeasurableSet.setOf_exists (hR q lab)
  · exact UMeasurableSet.empty

/-- An open time interval is the union of its compact affine sub-intervals. -/
theorem forall_Ioo_iff_forall_nat {α β : ℝ} (hαβ : α < β) {P : ℝ → Prop} :
    (∀ u ∈ Ioo α β, P u) ↔
      ∀ n : ℕ, ∀ τ ∈ Icc (1 / ((n : ℝ) + 2)) (1 - 1 / ((n : ℝ) + 2)), P (α + τ * (β - α)) := by
  have hd : 0 < β - α := sub_pos.2 hαβ
  constructor
  · intro h n τ hτ
    have h2 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    apply h
    constructor
    · have : 0 < τ * (β - α) := mul_pos (by linarith [hτ.1]) hd
      linarith
    · have : τ * (β - α) < 1 * (β - α) := mul_lt_mul_of_pos_right (by linarith [hτ.2]) hd
      linarith
  · intro h u hu
    set τ := (u - α) / (β - α)
    have hτ0 : 0 < τ := div_pos (by linarith [hu.1]) hd
    have hτ1 : τ < 1 := (div_lt_one hd).2 (by linarith [hu.2])
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min hτ0 (sub_pos.2 hτ1))
    have hn2 : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have hmin1 := min_le_left τ (1 - τ)
    have hmin2 := min_le_right τ (1 - τ)
    have := h n τ ⟨by linarith, by linarith⟩
    have e : α + τ * (β - α) = u := by
      simp only [τ]
      field_simp
      ring
    rwa [e] at this

/-- Coordinates of the local outer-degree family. -/
theorem isLocOutFamily_iff (L : Set (ℚ × ℚ)) (ε : ℝ) (σ : SegSpace) (q : ℚ × ℚ) (s : ℝ)
    {N : ℕ} (lab : Fin N → ℚ × ℚ) (α β : Fin N → ℝ) :
    IsLocOutFamily L ε σ q s lab α β ↔
      (∀ i, lab i ∈ L) ∧ (∀ i, α i < β i) ∧
      (∀ i j, i ≠ j → lab i = lab j → min (β i) (β j) ≤ max (α i) (α j)) ∧
      (∀ i j, lab i ≠ lab j → σ (lab i) ≠ σ (lab j)) ∧
      (∀ i, ∀ n : ℕ, ∀ τ ∈ Icc (1 / ((n : ℝ) + 2)) (1 - 1 / ((n : ℝ) + 2)),
        dist (σ (lab i) (α i + τ * (β i - α i))) (σ q s) < 4 * diam (locWindow ε (σ q) s)) ∧
      (∀ i, (dist (σ (lab i) (α i)) (σ q s) = 4 * diam (locWindow ε (σ q) s) ∧
          ∃ y ∈ Icc (-ε) ε, σ (lab i) (β i) = σ q (s + y)) ∨
        (dist (σ (lab i) (β i)) (σ q s) = 4 * diam (locWindow ε (σ q) s) ∧
          ∃ y ∈ Icc (-ε) ε, σ (lab i) (α i) = σ q (s + y))) := by
  have hwin : ∀ w : ℂ, w ∈ locWindow ε (σ q) s ↔ ∃ y ∈ Icc (-ε) ε, w = σ q (s + y) := by
    intro w
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u - s, ⟨by linarith [hu.1], by linarith [hu.2]⟩, by congr 1; ring⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨s + y, ⟨by linarith [hy.1], by linarith [hy.2]⟩, rfl⟩
  have hfr : ∀ w : ℂ, w ∈ frontier (locBall ε (σ q) s) ↔
      dist w (σ q s) = 4 * diam (locWindow ε (σ q) s) := by
    intro w
    rw [locBall, frontier_closedBall', mem_sphere]
  unfold IsLocOutFamily
  constructor
  · rintro ⟨hL, hlt, hdisj, hsep, hcross⟩
    refine ⟨hL, hlt, fun i j hij hl => ?_, hsep, fun i => ?_, fun i => ?_⟩
    · have := hdisj i j hij hl
      rwa [Ioo_disjoint_Ioo] at this
    · rw [← forall_Ioo_iff_forall_nat (P := fun u =>
        dist (σ (lab i) u) (σ q s) < 4 * diam (locWindow ε (σ q) s)) (hlt i)]
      intro u hu
      have := (hcross i).1 (mem_image_of_mem _ hu)
      rwa [locBall, interior_closedBall', mem_ball] at this
    · rcases (hcross i).2 with h | h
      · exact Or.inl ⟨(hfr _).1 h.1, by obtain ⟨y, hy, hy'⟩ := (hwin _).1 h.2; exact ⟨y, hy, hy'⟩⟩
      · exact Or.inr ⟨(hfr _).1 h.1, by obtain ⟨y, hy, hy'⟩ := (hwin _).1 h.2; exact ⟨y, hy, hy'⟩⟩
  · rintro ⟨hL, hlt, hdisj, hsep, hin, hcross⟩
    refine ⟨hL, hlt, fun i j hij hl => ?_, hsep, fun i => ⟨?_, ?_⟩⟩
    · rw [Ioo_disjoint_Ioo]
      exact hdisj i j hij hl
    · rintro _ ⟨u, hu, rfl⟩
      rw [locBall, interior_closedBall', mem_ball]
      exact (forall_Ioo_iff_forall_nat (P := fun u =>
        dist (σ (lab i) u) (σ q s) < 4 * diam (locWindow ε (σ q) s)) (hlt i)).2 (hin i) u hu
    · rcases hcross i with h | h
      · exact Or.inl ⟨(hfr _).2 h.1, (hwin _).2 h.2⟩
      · exact Or.inr ⟨(hfr _).2 h.1, (hwin _).2 h.2⟩

theorem um_le_locDegOutPrime (k : ℕ) (hk : 1 ≤ k) :
    UMeasurableSet {σ : SegSpace | (k : ℕ∞) ≤ locDegOutPrime L z ε σ} := by
  let R : ℚ × ℚ → (Fin k → ℚ × ℚ) →
      Set (SegSpace × (ℝ × ((Fin k → ℝ) × (Fin k → ℝ)))) := fun q lab =>
    {p | p.1 q p.2.1 = z} ∩
      ((⋂ i, {p | p.2.2.1 i < p.2.2.2 i}) ∩
      ((⋂ i, ⋂ j, ⋂ (_ : i ≠ j), ⋂ (_ : lab i = lab j),
        {p | min (p.2.2.2 i) (p.2.2.2 j) ≤ max (p.2.2.1 i) (p.2.2.1 j)}) ∩
      ({p | ∀ i j, lab i ≠ lab j → p.1 (lab i) ≠ p.1 (lab j)} ∩
      ((⋂ i, ⋂ n : ℕ, {p | ∀ τ ∈ Icc (1 / ((n : ℝ) + 2)) (1 - 1 / ((n : ℝ) + 2)),
        dist (p.1 (lab i) (p.2.2.1 i + τ * (p.2.2.2 i - p.2.2.1 i))) (p.1 q p.2.1) <
          4 * diam (locWindow ε (p.1 q) p.2.1)}) ∩
      (⋂ i, {p | (dist (p.1 (lab i) (p.2.2.1 i)) (p.1 q p.2.1) =
            4 * diam (locWindow ε (p.1 q) p.2.1) ∧
          ∃ y ∈ Icc (-ε) ε, p.1 (lab i) (p.2.2.2 i) = p.1 q (p.2.1 + y)) ∨
        (dist (p.1 (lab i) (p.2.2.2 i)) (p.1 q p.2.1) = 4 * diam (locWindow ε (p.1 q) p.2.1) ∧
          ∃ y ∈ Icc (-ε) ε, p.1 (lab i) (p.2.2.1 i) = p.1 q (p.2.1 + y))})))))
  have hR : ∀ q lab, MeasurableSet (R q lab) := by
    intro q lab
    let T := SegSpace × (ℝ × ((Fin k → ℝ) × (Fin k → ℝ)))
    have hs : Continuous fun p : T => p.2.1 := continuous_fst.comp continuous_snd
    have ha : ∀ i, Continuous fun p : T => p.2.2.1 i := fun i =>
      (continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))
    have hb : ∀ i, Continuous fun p : T => p.2.2.2 i := fun i =>
      (continuous_apply i).comp (continuous_snd.comp (continuous_snd.comp continuous_snd))
    have hev : Continuous fun p : T => p.1 q p.2.1 := continuous_segEval continuous_fst hs q
    have hdiam : Continuous fun p : T => diam (locWindow ε (p.1 q) p.2.1) :=
      continuous_segWindowDiam continuous_fst hs ε q
    have h1 : MeasurableSet {p : T | p.1 q p.2.1 = z} :=
      (isClosed_eq hev continuous_const).measurableSet
    have h2 : MeasurableSet (⋂ i, {p : T | p.2.2.1 i < p.2.2.2 i}) :=
      MeasurableSet.iInter fun i => (isOpen_lt (ha i) (hb i)).measurableSet
    have h3 : MeasurableSet (⋂ i, ⋂ j, ⋂ (_ : i ≠ j), ⋂ (_ : lab i = lab j),
        {p : T | min (p.2.2.2 i) (p.2.2.2 j) ≤ max (p.2.2.1 i) (p.2.2.1 j)}) := by
      refine (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => ?_).measurableSet
      exact isClosed_le ((hb i).min (hb j)) ((ha i).max (ha j))
    have h4 : MeasurableSet {p : T | ∀ i j, lab i ≠ lab j → p.1 (lab i) ≠ p.1 (lab j)} :=
      measurable_fst (measurableSet_sep lab)
    have h5 : MeasurableSet (⋂ i, ⋂ n : ℕ, {p : T |
        ∀ τ ∈ Icc (1 / ((n : ℝ) + 2)) (1 - 1 / ((n : ℝ) + 2)),
          dist (p.1 (lab i) (p.2.2.1 i + τ * (p.2.2.2 i - p.2.2.1 i))) (p.1 q p.2.1) <
            4 * diam (locWindow ε (p.1 q) p.2.1)}) := by
      refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun n => ?_
      have hF : IsClosed {w : T × ℝ |
          4 * diam (locWindow ε (w.1.1 q) w.1.2.1) ≤
            dist (w.1.1 (lab i) (w.1.2.2.1 i + w.2 * (w.1.2.2.2 i - w.1.2.2.1 i)))
              (w.1.1 q w.1.2.1)} := by
        refine isClosed_le (continuous_const.mul (hdiam.comp continuous_fst)) ?_
        exact (continuous_segEval (continuous_fst.comp continuous_fst)
          (((ha i).comp continuous_fst).add (continuous_snd.mul
            (((hb i).comp continuous_fst).sub ((ha i).comp continuous_fst)))) (lab i)).dist
          (hev.comp continuous_fst)
      have hcl := isClosed_exists_mem_of_isCompact
        (isCompact_Icc : IsCompact (Icc (1 / ((n : ℝ) + 2)) (1 - 1 / ((n : ℝ) + 2)))) hF
      have : {p : T | ∀ τ ∈ Icc (1 / ((n : ℝ) + 2)) (1 - 1 / ((n : ℝ) + 2)),
          dist (p.1 (lab i) (p.2.2.1 i + τ * (p.2.2.2 i - p.2.2.1 i))) (p.1 q p.2.1) <
            4 * diam (locWindow ε (p.1 q) p.2.1)} =
          {p : T | ∃ τ ∈ Icc (1 / ((n : ℝ) + 2)) (1 - 1 / ((n : ℝ) + 2)), (p, τ) ∈
            {w : T × ℝ | 4 * diam (locWindow ε (w.1.1 q) w.1.2.1) ≤
              dist (w.1.1 (lab i) (w.1.2.2.1 i + w.2 * (w.1.2.2.2 i - w.1.2.2.1 i)))
                (w.1.1 q w.1.2.1)}}ᶜ := by
        ext p
        simp only [mem_ofPred_eq, mem_compl_iff, not_exists, not_and, not_le]
      rw [this]
      exact hcl.isOpen_compl.measurableSet
    have h6 : MeasurableSet (⋂ i, {p : T | (dist (p.1 (lab i) (p.2.2.1 i)) (p.1 q p.2.1) =
            4 * diam (locWindow ε (p.1 q) p.2.1) ∧
          ∃ y ∈ Icc (-ε) ε, p.1 (lab i) (p.2.2.2 i) = p.1 q (p.2.1 + y)) ∨
        (dist (p.1 (lab i) (p.2.2.2 i)) (p.1 q p.2.1) = 4 * diam (locWindow ε (p.1 q) p.2.1) ∧
          ∃ y ∈ Icc (-ε) ε, p.1 (lab i) (p.2.2.1 i) = p.1 q (p.2.1 + y))}) := by
      refine (isClosed_iInter fun i => ?_).measurableSet
      have hwinc : ∀ (f : T → ℝ), Continuous f →
          IsClosed {p : T | ∃ y ∈ Icc (-ε) ε, p.1 (lab i) (f p) = p.1 q (p.2.1 + y)} := by
        intro f hf
        have hF : IsClosed {w : T × ℝ | w.1.1 (lab i) (f w.1) = w.1.1 q (w.1.2.1 + w.2)} :=
          isClosed_eq (continuous_segEval (continuous_fst.comp continuous_fst)
              (hf.comp continuous_fst) (lab i))
            (continuous_segEval (continuous_fst.comp continuous_fst)
              ((hs.comp continuous_fst).add continuous_snd) q)
        exact isClosed_exists_mem_of_isCompact (isCompact_Icc : IsCompact (Icc (-ε) ε)) hF
      have hdα : Continuous fun p : T => dist (p.1 (lab i) (p.2.2.1 i)) (p.1 q p.2.1) :=
        (continuous_segEval continuous_fst (ha i) (lab i)).dist hev
      have hdβ : Continuous fun p : T => dist (p.1 (lab i) (p.2.2.2 i)) (p.1 q p.2.1) :=
        (continuous_segEval continuous_fst (hb i) (lab i)).dist hev
      exact ((isClosed_eq hdα (continuous_const.mul hdiam)).inter (hwinc _ (hb i))).union
        ((isClosed_eq hdβ (continuous_const.mul hdiam)).inter (hwinc _ (ha i)))
    exact h1.inter (h2.inter (h3.inter (h4.inter (h5.inter h6))))
  have heq : {σ : SegSpace | (k : ℕ∞) ≤ locDegOutPrime L z ε σ} =
      ⋃ q, ⋃ lab : Fin k → ℚ × ℚ,
        (if q ∈ L ∧ ∀ i, lab i ∈ L then {σ | ∃ p, (σ, p) ∈ R q lab} else ∅) := by
    ext σ
    simp only [locDegOutPrime, mem_ofPred_eq, mem_iUnion]
    rw [natCast_le_iSup_iff hk]
    simp only [natCast_le_iSup_iff hk, le_locOutAt_iff, isLocOutFamily_iff, IsLocVisit]
    constructor
    · rintro ⟨q, s, ⟨hq, hz⟩, lab, α, β, hL, hlt, hdisj, hsep, hin, hcross⟩
      refine ⟨q, lab, ?_⟩
      rw [ite_eq_left ⟨hq, hL⟩]
      refine ⟨(s, (α, β)), hz, ?_, ?_, hsep, ?_, ?_⟩
      · simp only [mem_iInter, mem_ofPred_eq]
        exact hlt
      · simp only [mem_iInter, mem_ofPred_eq]
        exact hdisj
      · simp only [mem_iInter, mem_ofPred_eq]
        exact fun i n τ hτ => hin i n τ hτ
      · simp only [mem_iInter, mem_ofPred_eq]
        exact hcross
    · rintro ⟨q, lab, hmem⟩
      split_ifs at hmem with hql
      · obtain ⟨⟨s, α, β⟩, hz, hlt, hdisj, hsep, hin, hcross⟩ := hmem
        simp only [mem_iInter, mem_ofPred_eq] at hlt hdisj hin hcross
        exact ⟨q, s, ⟨hql.1, hz⟩, lab, α, β, hql.2, hlt, fun i j hij hl => hdisj i j hij hl,
          hsep, fun i n τ hτ => hin i n τ hτ, hcross⟩
      · exact absurd hmem (Set.notMem_empty σ)
  rw [heq]
  refine um_iUnion_label fun q => UMeasurableSet.iUnion fun lab => ?_
  split_ifs
  · exact UMeasurableSet.setOf_exists (hR q lab)
  · exact UMeasurableSet.empty

end

end MatedCRTHarmonic.GMS4cP
