/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K0
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114U1
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_1A
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_1B
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_4S1
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J6
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D110C

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9, packet J6c (part 1): the stopped σ-algebra of an a.s. stopping time

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1300–1302 ("if `τ` is a stopping time for `{(𝓑^•_t, h|_{𝓑^•_t})}`, then so is `σ^ε_{τ,𝕣}`")
at a random base, with `h` modulo additive constants (C:1154; decision D130 §4, L1).

The standard fact used there (tacitly) is that for a stopping time `s` of the filtration
`𝓕⁰_t = ⨆_{u ≤ t} σ(𝓑^•_u, h|_{𝓑^•_u} mod const)` the σ-algebra `σ(𝓑^•_s, h|_{𝓑^•_s} mod const)`
is contained in `𝓕⁰_t` on `{s < q}`, `q < t`. Proved here, in the a.s. form needed for
`IsFilledBallStoppingTimeAE0`, with the a.s. trace σ-algebra `t39jTrAE` (S3T39J5a):

* `t39k_setSigma_le_trAE`: `σ(𝓑^•_s) ≤ 𝓕⁰_t` on `{s < q}`: `{𝓑^•_s ⊆ V} = ⋃_{w ∈ ℚ} {s < w, 𝓑^•_w ⊆ V}`
  for `s > 0` (right-continuity of filled balls, `conf21_rc_filled`, P2-CONF21), `𝓑^•_s = ∅` for
  `s ≤ 0`, and open hits are complements of countable intersections of such events (`Uᶜ` is `G_δ`);
* **`t39k_localSigma0_le_trAE`**: `σ(𝓑^•_s, h|_{𝓑^•_s} mod const) ≤ 𝓕⁰_t` on `{s < q}`: on the
  pieces `{int (𝓑^•_s)^{(n)} ⊆ 𝓑^•_v}` (`v = (q+t)/2`, they cover `{s < q}` since `𝓑^•_s ⊆ int 𝓑^•_v`,
  `filledBall_subset_interior`) a level-`n` field event is a field event inside `𝓑^•_v`
  (`conf36_local_ae`, P2-D114).

Own routine argument (the stopped-σ-algebra inclusion is standard and not spelled out in CONF).
-/

noncomputable section

open MeasureTheory MeasurableSpace Set Filter Metric
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.CONF

variable {Ω : Type}

/-- the mod-constant filled-ball filtration `𝓕⁰_t = ⨆_{u ≤ t} σ(𝓑^•_u, h|_{𝓑^•_u} mod const)` -/
def t39kF0 (D : DistC → ContMetric) (h : Ω → DistC) (z₀ : ℂ) (t : ℝ) : MeasurableSpace Ω :=
  ⨆ (u : ℝ) (_ : u ≤ t), localSigma0 h (fun ω => filledBall (D (h ω)) z₀ u)

theorem t39k_local_le_F0 (D : DistC → ContMetric) (h : Ω → DistC) (z₀ : ℂ) {u t : ℝ}
    (hut : u ≤ t) : localSigma0 h (fun ω => filledBall (D (h ω)) z₀ u) ≤ t39kF0 D h z₀ t :=
  le_iSup₂ (f := fun (u : ℝ) (_ : u ≤ t) => localSigma0 h (fun ω => filledBall (D (h ω)) z₀ u))
    u hut

theorem t39k_F0_mono (D : DistC → ContMetric) (h : Ω → DistC) (z₀ : ℂ) {a t : ℝ}
    (hat : a ≤ t) : t39kF0 D h z₀ a ≤ t39kF0 D h z₀ t :=
  iSup₂_le fun _ hu => t39k_local_le_F0 D h z₀ (hu.trans hat)

theorem t39k_aeEventIn_mono {m m' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (hmm : m ≤ m')
    {E : Set Ω} (hE : AEEventIn P m E) : AEEventIn P m' E :=
  let ⟨F, hF, hEF⟩ := hE
  ⟨F, hmm _ hF, hEF⟩

/-! ## The a.s. trace σ-algebra -/

section Trace
variable {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {C : Set Ω}

theorem t39k_trAE_of_meas {Y : Set Ω} (hY : MeasurableSet[m] Y) :
    MeasurableSet[t39jTrAE P m C] Y := ⟨Y, hY, EventuallyEq.rfl⟩

theorem t39k_trAE_of_ae {Y : Set Ω} (hY : AEEventIn P m Y) :
    MeasurableSet[t39jTrAE P m C] Y := by
  obtain ⟨F, hF, hYF⟩ := hY
  exact ⟨F, hF, hYF.inter EventuallyEq.rfl⟩

theorem t39k_trAE_anti {C' : Set Ω} (hCC : C' ⊆ C) : t39jTrAE P m C ≤ t39jTrAE P m C' := by
  rintro S ⟨B, hB, hSB⟩
  refine ⟨B, hB, ?_⟩
  have e1 : S ∩ C' = (S ∩ C) ∩ C' := by rw [inter_assoc, inter_eq_right.2 hCC]
  have e2 : B ∩ C' = (B ∩ C) ∩ C' := by rw [inter_assoc, inter_eq_right.2 hCC]
  rw [e1, e2]
  exact hSB.inter EventuallyEq.rfl

/-- trace events may be changed off `C` and on null sets -/
theorem t39k_trAE_congr_on {S S' : Set Ω} (hS' : MeasurableSet[t39jTrAE P m C] S')
    (hSS : ∀ᵐ ω ∂P, ω ∈ C → (ω ∈ S ↔ ω ∈ S')) : MeasurableSet[t39jTrAE P m C] S := by
  obtain ⟨B, hB, hSB⟩ := hS'
  refine ⟨B, hB, ?_⟩
  filter_upwards [hSB, hSS] with ω h1 h2
  have h1' : (ω ∈ S' ∧ ω ∈ C) = (ω ∈ B ∧ ω ∈ C) := h1
  show (ω ∈ S ∧ ω ∈ C) = (ω ∈ B ∧ ω ∈ C)
  rw [← h1']
  exact propext ⟨fun ⟨a, b⟩ => ⟨(h2 b).1 a, b⟩, fun ⟨a, b⟩ => ⟨(h2 b).2 a, b⟩⟩

/-- a trace event on an a.s. event `C` of `m` gives the a.s. event `S ∩ C` of `m` -/
theorem t39k_aeEventIn_of_trAE {S : Set Ω} (hC : AEEventIn P m C)
    (hS : MeasurableSet[t39jTrAE P m C] S) : AEEventIn P m (S ∩ C) := by
  obtain ⟨B, hB, hSB⟩ := hS
  obtain ⟨F, hF, hCF⟩ := hC
  exact ⟨B ∩ F, hB.inter hF, hSB.trans (Filter.EventuallyEq.inter (Filter.EventuallyEq.refl _ B) hCF)⟩

/-- **gluing**: an event which is a trace event on each piece `C ∩ A n` of an a.s. cover of `C`
by trace events `A n` is a trace event on `C` -/
theorem t39k_trAE_glue {A : ℕ → Set Ω} {S : Set Ω}
    (hA : ∀ n, MeasurableSet[t39jTrAE P m C] (A n))
    (hS : ∀ n, MeasurableSet[t39jTrAE P m (C ∩ A n)] S)
    (hcov : ∀ᵐ ω ∂P, ω ∈ C → ∃ n, ω ∈ A n) : MeasurableSet[t39jTrAE P m C] S := by
  choose A' hA' hAA using hA
  choose B hB hSB using hS
  refine ⟨⋃ n, B n ∩ A' n, MeasurableSet.iUnion fun n => (hB n).inter (hA' n), ?_⟩
  filter_upwards [ae_all_iff.2 hAA, ae_all_iff.2 hSB, hcov] with ω h1 h2 h3
  have h1' : ∀ n, (ω ∈ A n ∧ ω ∈ C) ↔ (ω ∈ A' n ∧ ω ∈ C) := fun n => Iff.of_eq (h1 n)
  have h2' : ∀ n, (ω ∈ S ∧ ω ∈ C ∧ ω ∈ A n) ↔ (ω ∈ B n ∧ ω ∈ C ∧ ω ∈ A n) :=
    fun n => Iff.of_eq (h2 n)
  show (ω ∈ S ∩ C) = (ω ∈ (⋃ n, B n ∩ A' n) ∩ C)
  apply propext
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨hSω, hCω⟩
    obtain ⟨n, hn⟩ := h3 hCω
    exact ⟨⟨n, ((h2' n).1 ⟨hSω, hCω, hn⟩).1, ((h1' n).1 ⟨hn, hCω⟩).1⟩, hCω⟩
  · rintro ⟨⟨n, hBn, hAn'⟩, hCω⟩
    have hAn := ((h1' n).2 ⟨hAn', hCω⟩).1
    exact ⟨((h2' n).2 ⟨hBn, hCω, hAn⟩).1, hCω⟩

end Trace

/-! ## The stopped σ-algebra -/

section Stopped
variable [mΩ : MeasurableSpace Ω] {P : Measure Ω} {D : DistC → ContMetric} {h : Ω → DistC} {z₀ : ℂ}

omit mΩ in
/-- `{𝓑^•_w ⊆ V}` (`V` open) is an event of `𝓕⁰_t` for `w ≤ t` -/
theorem t39k_ball_subset_meas (D : DistC → ContMetric) (h : Ω → DistC) (z₀ : ℂ) {w t : ℝ}
    (hwt : w ≤ t) {V : Set ℂ} (hV : IsOpen V) :
    MeasurableSet[t39kF0 D h z₀ t] {ω | filledBall (D (h ω)) z₀ w ⊆ V} := by
  have e : {ω | filledBall (D (h ω)) z₀ w ⊆ V} =
      {ω | (filledBall (D (h ω)) z₀ w ∩ Vᶜ).Nonempty}ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, ← not_disjoint_iff_nonempty_inter, not_not,
      subset_compl_iff_disjoint_right.symm, compl_compl]
  rw [e]
  refine MeasurableSet.compl (t39k_local_le_F0 D h z₀ hwt _
    (confD110_setSigma_le_localSigma0 h _ _ ?_))
  exact GM.gm_setSigma_hit_closed (fun ω => GM.gm_filledBall_isClosed _ _ _) hV.isClosed_compl

/-- **`σ(𝓑^•_s) ≤ 𝓕⁰_t` on `{s < q}`** for an a.s. stopping time `s` and `q < t` -/
theorem t39k_setSigma_le_trAE (hlen : ∀ᵐ ω ∂P, D (h ω) ∈ lenSet) {s : Ω → ℝ}
    (hs : IsFilledBallStoppingTimeAE0 P D h z₀ s) {q t : ℝ} (hqt : q < t) :
    setSigma (fun ω => filledBall (D (h ω)) z₀ (s ω)) ≤
      t39jTrAE P (t39kF0 D h z₀ t) {ω | s ω < q} := by
  have hlt : ∀ w : ℝ, w ≤ t → MeasurableSet[t39jTrAE P (t39kF0 D h z₀ t) {ω | s ω < q}] {ω | s ω < w} := fun w hw =>
    t39k_trAE_of_ae (t39k_aeEventIn_mono (t39k_F0_mono D h z₀ hw) (hs w))
  have h0 : MeasurableSet[t39jTrAE P (t39kF0 D h z₀ t) {ω | s ω < q}] {ω | s ω ≤ 0} := by
    refine t39k_trAE_congr_on (S' := ⋂ k : ℕ, {ω | s ω < min t (1 / ((k : ℝ) + 1))})
      (MeasurableSet.iInter fun k => hlt _ (min_le_left _ _)) (Eventually.of_forall ?_)
    intro ω hC
    have hst : s ω < t := lt_trans hC hqt
    simp only [mem_ofPred_eq, mem_iInter, lt_min_iff]
    constructor
    · intro h0 k
      exact ⟨hst, lt_of_le_of_lt h0 (by positivity)⟩
    · intro hk
      by_contra hpos
      push_neg at hpos
      obtain ⟨k, hk'⟩ := exists_nat_one_div_lt hpos
      exact absurd (hk k).2 (not_lt.2 hk'.le)
  have hsub : ∀ V : Set ℂ, IsOpen V →
      MeasurableSet[t39jTrAE P (t39kF0 D h z₀ t) {ω | s ω < q}] {ω | filledBall (D (h ω)) z₀ (s ω) ⊆ V} := by
    intro V hV
    refine t39k_trAE_congr_on (S' := {ω | s ω ≤ 0} ∪ ⋃ (w : ℚ) (_ : (w : ℝ) ≤ t),
      ({ω | s ω < w} ∩ {ω | filledBall (D (h ω)) z₀ w ⊆ V}))
      (h0.union (MeasurableSet.iUnion fun w => MeasurableSet.iUnion fun hw =>
        (hlt _ hw).inter (t39k_trAE_of_meas (t39k_ball_subset_meas D h z₀ hw hV)))) ?_
    filter_upwards [hlen] with ω hω hC
    have hst : s ω < t := lt_trans hC hqt
    simp only [mem_ofPred_eq, mem_union, mem_iUnion, mem_inter_iff, exists_prop]
    constructor
    · intro hK
      by_cases hs0 : s ω ≤ 0
      · exact Or.inl hs0
      · push_neg at hs0
        obtain ⟨ε, hε, hεV⟩ := conf21_rc_filled hω z₀ hs0 hV hK
        obtain ⟨w, hw1, hw2⟩ := exists_rat_btwn (lt_min (lt_add_of_pos_right (s ω) hε) hst)
        refine Or.inr ⟨w, (lt_min_iff.1 hw2).2.le, hw1, ?_⟩
        exact (GM.gm_filledBall_mono _ _ (lt_min_iff.1 hw2).1.le).trans hεV
    · rintro (hs0 | ⟨w, -, hw, hwV⟩)
      · rw [t39j6_filledBall_nonpos _ _ hs0]; exact empty_subset _
      · exact (GM.gm_filledBall_mono _ _ hw.le).trans hwV
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨U, hU, rfl⟩
  obtain ⟨T, hTo, hTc, hTe⟩ := hU.isClosed_compl.isGδ
  have e : {ω | (filledBall (D (h ω)) z₀ (s ω) ∩ U).Nonempty} =
      (⋂ V ∈ T, {ω | filledBall (D (h ω)) z₀ (s ω) ⊆ V})ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, mem_iInter]
    rw [← subset_sInter_iff, ← hTe, subset_compl_iff_disjoint_right, not_disjoint_iff_nonempty_inter]
  rw [e]
  exact (MeasurableSet.biInter hTc fun V hV => hsub V (hTo V hV)).compl

/-- **the stopped σ-algebra**: `σ(𝓑^•_s, h|_{𝓑^•_s} mod const) ≤ 𝓕⁰_t` on `{s < q}` (a.s. trace),
for an a.s. stopping time `s` of `𝓕⁰` and `q < t` -/
theorem t39k_localSigma0_le_trAE (hlen : ∀ᵐ ω ∂P, D (h ω) ∈ lenSet) {s : Ω → ℝ}
    (hs : IsFilledBallStoppingTimeAE0 P D h z₀ s) {q t : ℝ} (hqt : q < t) :
    localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (s ω)) ≤
      t39jTrAE P (t39kF0 D h z₀ t) {ω | s ω < q} := by
  intro E hE
  set K : Ω → Set ℂ := fun ω => filledBall (D (h ω)) z₀ (s ω) with hKdef
  set v : ℝ := (q + t) / 2 with hv
  set Bv : Ω → Set ℂ := fun ω => filledBall (D (h ω)) z₀ v with hBvdef
  set C : Set Ω := {ω | s ω < q} with hCdef
  set A : ℕ → Set Ω := fun n => {ω | interior (dyadicHull n (K ω)) ⊆ Bv ω} with hAdef
  have hKc : ∀ ω, IsClosed (K ω) := fun ω => GM.gm_filledBall_isClosed _ _ _
  have hBvc : ∀ ω, IsClosed (Bv ω) := fun ω => GM.gm_filledBall_isClosed _ _ _
  have hBvb : ∀ᵐ ω ∂P, Bornology.IsBounded (Bv ω) ∨ Bv ω = univ :=
    hlen.mono fun ω hω => Or.inl (GM.gm_filledBall_isBounded_of_lenSet hω z₀ v)
  have hset := t39k_setSigma_le_trAE hlen hs hqt
  have hBvF : localSigma0 h Bv ≤ t39kF0 D h z₀ t := t39k_local_le_F0 D h z₀ (by linarith)
  refine t39k_trAE_glue (A := A) (fun n => ?_) (fun n => ?_) ?_
  · -- the pieces are trace events
    refine t39k_trAE_congr_on (S' := ⋃ S ∈ conf36HullShapes n,
      ({ω | dyadicHull n (K ω) = S} ∩ {ω | interior S ⊆ Bv ω}))
      (MeasurableSet.biUnion (conf36HullShapes_countable n) fun S _ =>
        (hset _ (measurableSet_hull_eq hKc n S)).inter (t39k_trAE_of_meas (hBvF _
          (confD110_setSigma_le_localSigma0 h Bv _
            (conf36_setSigma_subset_open hBvc isOpen_interior))))) ?_
    filter_upwards [hlen] with ω hω _
    have hsh := conf36_hull_mem_shapes
      (Or.inl (GM.gm_filledBall_isBounded_of_lenSet hω z₀ (s ω))) n
    simp only [hAdef, mem_ofPred_eq, mem_iUnion, mem_inter_iff, exists_prop]
    exact ⟨fun hA => ⟨_, hsh, rfl, hA⟩, fun ⟨S, _, hS, hA⟩ => hS ▸ hA⟩
  · -- on each piece, `hullSigma0 h K n` is in the trace
    have hEn : MeasurableSet[hullSigma0 h K n] E := MeasurableSpace.measurableSet_iInf.1 hE n
    refine (show hullSigma0 h K n ≤ t39jTrAE P (t39kF0 D h z₀ t) (C ∩ A n) from
      sup_le (hset.trans (t39k_trAE_anti inter_subset_left))
        (MeasurableSpace.generateFrom_le ?_)) E hEn
    rintro _ ⟨S, F, hF, rfl⟩
    obtain ⟨Y₁, hY₁, hY₁e⟩ := hset _ (measurableSet_hull_eq hKc n S)
    obtain ⟨Y₂, hY₂, hY₂e⟩ := conf36_local_ae h hBvc hBvb isOpen_interior (Y := F)
      ⟨F, hF, EventuallyEq.rfl⟩
    refine ⟨Y₁ ∩ Y₂, hY₁.inter (hBvF _ hY₂), ?_⟩
    filter_upwards [hY₁e, hY₂e] with ω h1 h2
    have h1' : (dyadicHull n (K ω) = S ∧ s ω < q) ↔ (ω ∈ Y₁ ∧ s ω < q) := Iff.of_eq h1
    have h2' : (ω ∈ F ∧ interior S ⊆ Bv ω) ↔ ω ∈ Y₂ := Iff.of_eq h2
    show (ω ∈ {ω | dyadicHull n (K ω) = S} ∩ F ∧ ω ∈ C ∧ ω ∈ A n) =
      (ω ∈ Y₁ ∩ Y₂ ∧ ω ∈ C ∧ ω ∈ A n)
    apply propext
    simp only [mem_inter_iff, mem_ofPred_eq, hCdef, hAdef]
    constructor
    · rintro ⟨⟨hS, hFω⟩, hC, hA⟩
      have hSB : interior S ⊆ Bv ω := hS ▸ hA
      exact ⟨⟨(h1'.1 ⟨hS, hC⟩).1, h2'.1 ⟨hFω, hSB⟩⟩, hC, hA⟩
    · rintro ⟨⟨hY1, hY2⟩, hC, hA⟩
      exact ⟨⟨(h1'.2 ⟨hY1, hC⟩).1, (h2'.2 hY2).1⟩, hC, hA⟩
  · -- the pieces cover `{s < q}`
    filter_upwards [hlen] with ω hω hC
    have hsv : s ω < v := by simp only [hCdef, mem_ofPred_eq] at hC; rw [hv]; linarith
    have hKi : K ω ⊆ interior (Bv ω) := filledBall_subset_interior hsv
    have hKcpt : IsCompact (K ω) :=
      Metric.isCompact_of_isClosed_isBounded (hKc ω)
        (GM.gm_filledBall_isBounded_of_lenSet hω z₀ (s ω))
    obtain ⟨δ, hδ, hδK⟩ := hKcpt.exists_thickening_subset_open isOpen_interior hKi
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hδ) (by norm_num : (1 / 2 : ℝ) < 1)
    have e2 : (2 : ℝ) / 2 ^ n = 2 * (1 / 2) ^ n := by rw [one_div_pow]; ring
    have hn' : (2 : ℝ) / 2 ^ n < δ := by rw [e2]; linarith
    refine ⟨n, (interior_subset.trans fun x hx => ?_).trans (hδK.trans interior_subset)⟩
    simp only [dyadicHull, mem_iUnion] at hx
    obtain ⟨k, ⟨y, hyk, hyK⟩, hxk⟩ := hx
    exact mem_thickening_iff.2 ⟨y, hyK, lt_of_le_of_lt (conf21_sq_dist hxk hyk) hn'⟩

end Stopped

end LQGMetric.CONF
