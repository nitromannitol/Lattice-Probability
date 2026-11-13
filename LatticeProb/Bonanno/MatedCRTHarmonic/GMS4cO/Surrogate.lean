/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cO.Surrogate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.Concat
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.DetLocality
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.Excursions
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.ContVersion
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.Defs
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.JointMeasurable

/-!
# The surrogate curve of a family of stored excursions

The measurable form of [18] Lemma 4.3 at the root of the curve.

Given rationally labelled continuous segments `σ q` with lengths `M q` (in the application: the area-time
excursion segments of the space-filling SLE into `U = B_R(0)`, recovered from the local configuration), the
**surrogate curve** glues, in the order of an enumeration of `ℚ × ℚ`, the segments of the labels `q` with
`ratPt q ∈ U` whose segment differs from all earlier ones (one representative per excursion), joining consecutive
pieces by connectors of time length `1` along the circle `|w| = R` and replacing non-representatives by constant
pieces at `R`. The surrogate is a Borel function of `(σ, M)` (`L43O.measurable_surrogate`).

For an actual curve `c` with an excursion family into `U` (`GMS4cP.IsExcursionFamily`), whose stored segments are
`σ q = clampSeg c (e q) (x q)` with `M q = x q − e q`, distinct excursions having distinct segments, and whose root
`c 0 = 0` is visited only at time `0`, the times of `c` and of the surrogate spent in `U` match by time translations
(`L43O.surrogate_matching`). By deterministic locality (`GMS4cO/DetLocality.lean`) the masked observables of `c` at
time `0` equal those of the surrogate at its root time (`L43O.maskedLocUStarAt_surrogate`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.L43O

open GMS4b

attribute [local instance] Classical.propDecidable

/-! ## Building blocks -/

/-- The enumeration of labels. -/
def qOf (n : ℕ) : ℚ × ℚ := Denumerable.ofNat (ℚ × ℚ) n

/-- A continuous curve clamped to `[0, ℓ]`. -/
def clampC (c : C(ℝ, ℂ)) (ℓ : ℝ) : C(ℝ, ℂ) :=
  ⟨fun t => c (clampT ℓ t), c.continuous.comp (continuous_clampT ℓ)⟩

/-- The connector from `p` to `p'`: modulus and argument interpolated linearly over time `[0, 1]`. -/
def connC (p p' : ℂ) : C(ℝ, ℂ) :=
  ⟨fun t => ((‖p‖ + clampT 1 t * (‖p'‖ - ‖p‖) : ℝ) : ℂ) *
      Complex.exp (((Complex.arg p + clampT 1 t * (Complex.arg p' - Complex.arg p) : ℝ) : ℂ) *
        Complex.I), by
    have h := continuous_clampT 1
    fun_prop⟩

theorem connC_zero (p p' : ℂ) : connC p p' 0 = p := by
  change (((‖p‖ + clampT 1 0 * (‖p'‖ - ‖p‖) : ℝ) : ℂ) *
    Complex.exp (((Complex.arg p + clampT 1 0 * (Complex.arg p' - Complex.arg p) : ℝ) : ℂ) *
      Complex.I)) = p
  rw [clampT_of_nonpos zero_le_one le_rfl]
  simp only [zero_mul, add_zero]
  exact Complex.norm_mul_exp_arg_mul_I p

theorem connC_one (p p' : ℂ) : connC p p' 1 = p' := by
  change (((‖p‖ + clampT 1 1 * (‖p'‖ - ‖p‖) : ℝ) : ℂ) *
    Complex.exp (((Complex.arg p + clampT 1 1 * (Complex.arg p' - Complex.arg p) : ℝ) : ℂ) *
      Complex.I)) = p'
  rw [clampT_of_ge zero_le_one le_rfl]
  simp only [one_mul, add_sub_cancel]
  exact Complex.norm_mul_exp_arg_mul_I p'

theorem norm_connC {R : ℝ} (hR : 0 ≤ R) {p p' : ℂ} (hp : ‖p‖ = R) (hp' : ‖p'‖ = R) (t : ℝ) :
    ‖connC p p' t‖ = R := by
  change ‖(((‖p‖ + clampT 1 t * (‖p'‖ - ‖p‖) : ℝ) : ℂ) *
    Complex.exp (((Complex.arg p + clampT 1 t * (Complex.arg p' - Complex.arg p) : ℝ) : ℂ) *
      Complex.I))‖ = R
  rw [hp, hp', sub_self, mul_zero, add_zero, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR]

/-! ## The surrogate -/

section surrogate

variable (R : ℝ) (σ : ℚ × ℚ → C(ℝ, ℂ)) (M : ℚ × ℚ → ℝ)

/-- Label `qOf n` lies in `U = B_R(0)`. -/
def InU (n : ℕ) : Prop := GMS4c.ratPt (qOf n) ∈ ball (0 : ℂ) R

/-- `qOf n` represents its excursion: it lies in `U`, has positive length, and no earlier label in `U` with
positive length carries the same segment. -/
def IsRep (n : ℕ) : Prop :=
  InU R n ∧ 0 < M (qOf n) ∧ ∀ m < n, InU R m → 0 < M (qOf m) → σ (qOf m) ≠ σ (qOf n)

/-- The `n`th piece: the clamped representative segment, or the constant `R`. -/
def piece (n : ℕ) : C(ℝ, ℂ) :=
  if IsRep R σ M n then clampC (σ (qOf n)) (M (qOf n)) else ContinuousMap.const ℝ (R : ℂ)

/-- The length of the `n`th piece. -/
def pieceLen (n : ℕ) : ℝ := if IsRep R σ M n then M (qOf n) else 1

/-- The alternating sequence of pieces and connectors. -/
def seqPath (k : ℕ) : C(ℝ, ℂ) :=
  if k % 2 = 0 then piece R σ M (k / 2)
  else connC (piece R σ M (k / 2) (pieceLen R σ M (k / 2))) (piece R σ M (k / 2 + 1) 0)

/-- Lengths of the alternating sequence. -/
def seqLen (k : ℕ) : ℝ := if k % 2 = 0 then pieceLen R σ M (k / 2) else 1

theorem pieceLen_pos (n : ℕ) : 0 < pieceLen R σ M n := by
  unfold pieceLen
  split_ifs with h
  · exact h.2.1
  · exact one_pos

theorem seqLen_pos (k : ℕ) : 0 < seqLen R σ M k := by
  unfold seqLen
  split_ifs
  · exact pieceLen_pos R σ M _
  · exact one_pos

theorem seqLen_even (n : ℕ) : seqLen R σ M (2 * n) = pieceLen R σ M n := by
  simp [seqLen]

theorem seqLen_odd (n : ℕ) : seqLen R σ M (2 * n + 1) = 1 := by
  simp [seqLen, Nat.add_mod]

theorem seqPath_even (n : ℕ) : seqPath R σ M (2 * n) = piece R σ M n := by
  simp [seqPath]

theorem seqPath_odd (n : ℕ) : seqPath R σ M (2 * n + 1) =
    connC (piece R σ M n (pieceLen R σ M n)) (piece R σ M (n + 1) 0) := by
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  simp [seqPath, h1, h2]

theorem cumT_seq_ge (n : ℕ) : (n : ℝ) ≤ cumT (seqLen R σ M) (2 * n) := by
  induction n with
  | zero => simp [cumT_zero]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, cumT_succ, cumT_succ, seqLen_odd]
    push_cast
    linarith [seqLen_pos R σ M (2 * n)]

theorem seq_unbounded : ∀ K : ℝ, ∃ N, K ≤ cumT (seqLen R σ M) N := by
  intro K
  obtain ⟨n, hn⟩ := exists_nat_ge K
  exact ⟨2 * n, hn.trans (cumT_seq_ge R σ M n)⟩

theorem seq_match (k : ℕ) :
    seqPath R σ M k (seqLen R σ M k) = seqPath R σ M (k + 1) 0 := by
  rcases Nat.even_or_odd' k with ⟨n, rfl | rfl⟩
  · rw [seqLen_even, seqPath_even, seqPath_odd, connC_zero]
  · rw [seqLen_odd, seqPath_odd, connC_one, show 2 * n + 1 + 1 = 2 * (n + 1) by ring,
      seqPath_even]

/-- **The surrogate curve.** -/
def surrogate : C(ℝ, ℂ) :=
  ⟨concatPath (fun k => ⇑(seqPath R σ M k)) (seqLen R σ M),
    continuous_concatPath (seqLen_pos R σ M) (seq_unbounded R σ M)
      (fun k => (seqPath R σ M k).continuous) (seq_match R σ M)⟩

theorem surrogate_apply (t : ℝ) :
    surrogate R σ M t = concatPath (fun k => ⇑(seqPath R σ M k)) (seqLen R σ M) t := rfl

/-- `qOf n` is a root representative: a representative whose segment passes through `0`. -/
def IsRootRep (n : ℕ) : Prop :=
  IsRep R σ M n ∧ (0 : ℂ) ∈ (σ (qOf n)) '' Icc 0 (M (qOf n))

/-- The index of the root representative. -/
def rootIdx : ℕ := if h : ∃ n, IsRootRep R σ M n then Nat.find h else 0

/-- The root time of the surrogate. -/
def rootTime : ℝ :=
  cumT (seqLen R σ M) (2 * rootIdx R σ M) + hitTime (σ (qOf (rootIdx R σ M))) 0

end surrogate

/-! ## Measurability -/

section measurability

theorem measurable_clampC : Measurable fun p : C(ℝ, ℂ) × ℝ => clampC p.1 p.2 := by
  refine (GMS4c.measurableEmbedding_ratRestrict.measurable_comp_iff).1 ?_
  refine measurable_pi_iff.mpr fun t => ?_
  change Measurable fun p : C(ℝ, ℂ) × ℝ => p.1 (clampT p.2 (t : ℝ))
  exact continuous_eval.measurable.comp (measurable_fst.prodMk
    (measurable_clampT_joint.comp (measurable_snd.prodMk measurable_const)))

theorem measurable_connC : Measurable fun p : ℂ × ℂ => connC p.1 p.2 := by
  refine (GMS4c.measurableEmbedding_ratRestrict.measurable_comp_iff).1 ?_
  refine measurable_pi_iff.mpr fun t => ?_
  change Measurable fun p : ℂ × ℂ =>
    ((‖p.1‖ + clampT 1 (t : ℝ) * (‖p.2‖ - ‖p.1‖) : ℝ) : ℂ) *
      Complex.exp (((Complex.arg p.1 + clampT 1 (t : ℝ) * (Complex.arg p.2 - Complex.arg p.1) : ℝ) :
        ℂ) * Complex.I)
  have h1 : Measurable fun p : ℂ × ℂ => ‖p.1‖ := measurable_norm.comp measurable_fst
  have h2 : Measurable fun p : ℂ × ℂ => ‖p.2‖ := measurable_norm.comp measurable_snd
  have h3 : Measurable fun p : ℂ × ℂ => Complex.arg p.1 := Complex.measurable_arg.comp measurable_fst
  have h4 : Measurable fun p : ℂ × ℂ => Complex.arg p.2 := Complex.measurable_arg.comp measurable_snd
  refine (Complex.measurable_ofReal.comp (h1.add (measurable_const.mul (h2.sub h1)))).mul ?_
  exact Complex.measurable_exp.comp
    ((Complex.measurable_ofReal.comp (h3.add (measurable_const.mul (h4.sub h3)))).mul_const _)

/-- Equality of two measurable families of continuous curves is a measurable condition. -/
theorem measurableSet_eq_curves {α : Type*} [MeasurableSpace α] {f g : α → C(ℝ, ℂ)}
    (hf : Measurable f) (hg : Measurable g) : MeasurableSet {a | f a = g a} := by
  have heq : {a | f a = g a} = ⋂ t : ℚ, {a | f a (t : ℝ) = g a (t : ℝ)} := by
    ext a
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h t
      rw [h]
    · intro h
      exact GMS4c.ratRestrict_injective (funext h)
  rw [heq]
  exact MeasurableSet.iInter fun t => measurableSet_eq_fun
    ((continuous_eval_const (t : ℝ)).measurable.comp hf)
    ((continuous_eval_const (t : ℝ)).measurable.comp hg)

variable {R : ℝ}

/-- The parameter space `(σ, M)`. -/
abbrev SurrData : Type := (ℚ × ℚ → C(ℝ, ℂ)) × (ℚ × ℚ → ℝ)

theorem measurable_σ_apply (q : ℚ × ℚ) : Measurable fun ξ : SurrData => ξ.1 q :=
  (measurable_pi_apply q).comp measurable_fst

theorem measurable_M_apply (q : ℚ × ℚ) : Measurable fun ξ : SurrData => ξ.2 q :=
  (measurable_pi_apply q).comp measurable_snd

theorem measurableSet_isRep (n : ℕ) : MeasurableSet {ξ : SurrData | IsRep R ξ.1 ξ.2 n} := by
  have hσ : ∀ q, Measurable fun ξ : SurrData => ξ.1 q := fun q =>
    (measurable_pi_apply q).comp measurable_fst
  have hM : ∀ q, Measurable fun ξ : SurrData => ξ.2 q := fun q =>
    (measurable_pi_apply q).comp measurable_snd
  have hset : {ξ : SurrData | IsRep R ξ.1 ξ.2 n} =
      {ξ : SurrData | InU R n} ∩ ({ξ : SurrData | 0 < ξ.2 (qOf n)} ∩
        ⋂ m ∈ Finset.range n, {ξ : SurrData | InU R m → 0 < ξ.2 (qOf m) →
          ξ.1 (qOf m) ≠ ξ.1 (qOf n)}) := by
    ext ξ
    simp only [IsRep, mem_ofPred_eq, mem_inter_iff, mem_iInter, Finset.mem_range]
  rw [hset]
  refine MeasurableSet.inter (MeasurableSet.const _)
    ((measurableSet_lt (measurable_const (a := (0 : ℝ))) (hM (qOf n))).inter
      (Finset.measurableSet_biInter _ fun m _ => ?_))
  by_cases hm : InU R m
  · simp only [hm, true_implies]
    have h1 : MeasurableSet {ξ : SurrData | 0 < ξ.2 (qOf m)} :=
      measurableSet_lt measurable_const (hM (qOf m))
    have h2 : MeasurableSet {ξ : SurrData | ξ.1 (qOf m) = ξ.1 (qOf n)} :=
      measurableSet_eq_curves (hσ (qOf m)) (hσ (qOf n))
    refine (h1.compl.union h2.compl).congr ?_
    ext ξ
    simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_lt]
    constructor
    · rintro (h | h)
      · exact fun hpos => absurd hpos (not_lt.2 h)
      · exact fun _ => h
    · intro h
      by_cases hpos : 0 < ξ.2 (qOf m)
      · exact Or.inr (h hpos)
      · exact Or.inl (not_lt.1 hpos)
  · simp only [hm, false_implies, setOf_true, MeasurableSet.univ]

theorem measurable_piece (n : ℕ) : Measurable fun ξ : SurrData => piece R ξ.1 ξ.2 n := by
  unfold piece
  refine Measurable.ite (measurableSet_isRep n) ?_ measurable_const
  exact measurable_clampC.comp ((measurable_σ_apply (qOf n)).prodMk (measurable_M_apply (qOf n)))

theorem measurable_pieceLen (n : ℕ) : Measurable fun ξ : SurrData => pieceLen R ξ.1 ξ.2 n := by
  unfold pieceLen
  exact Measurable.ite (measurableSet_isRep n) (measurable_M_apply (qOf n)) measurable_const

theorem measurable_seqPath (k : ℕ) : Measurable fun ξ : SurrData => seqPath R ξ.1 ξ.2 k := by
  unfold seqPath
  split_ifs
  · exact measurable_piece _
  · refine measurable_connC.comp (Measurable.prodMk ?_ ?_)
    · exact continuous_eval.measurable.comp ((measurable_piece _).prodMk (measurable_pieceLen _))
    · exact (continuous_eval_const (0 : ℝ)).measurable.comp (measurable_piece _)

theorem measurable_seqLen (k : ℕ) : Measurable fun ξ : SurrData => seqLen R ξ.1 ξ.2 k := by
  unfold seqLen
  split_ifs
  · exact measurable_pieceLen _
  · exact measurable_const

theorem measurable_surrogate_apply (t : ℝ) :
    Measurable fun ξ : SurrData => surrogate R ξ.1 ξ.2 t := by
  have hF : ∀ k, Measurable fun ξ : SurrData => seqPath R ξ.1 ξ.2 k :=
    fun k => measurable_seqPath (R := R) k
  have hL : ∀ k, Measurable fun ξ : SurrData => seqLen R ξ.1 ξ.2 k :=
    fun k => measurable_seqLen (R := R) k
  have h := measurable_concatPath_apply (F := fun (ξ : SurrData) k => seqPath R ξ.1 ξ.2 k)
    (Len := fun (ξ : SurrData) k => seqLen R ξ.1 ξ.2 k) hF hL t
  exact h

/-- **The surrogate is a Borel function of the stored data.** -/
theorem measurable_surrogate : Measurable fun ξ : SurrData => surrogate R ξ.1 ξ.2 := by
  refine (GMS4c.measurableEmbedding_ratRestrict.measurable_comp_iff).1 ?_
  exact measurable_pi_iff.mpr fun t => measurable_surrogate_apply (t : ℝ)

/-- A closed set projected along `ℝ` is measurable. -/
theorem measurableSet_exists_real_of_isClosed {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {F : Set (X × ℝ)} (hF : IsClosed F) :
    MeasurableSet {x | ∃ y, (x, y) ∈ F} := by
  have heq : {x | ∃ y, (x, y) ∈ F} = ⋃ n : ℕ, {x | ∃ y ∈ compactCovering ℝ n, (x, y) ∈ F} := by
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
    (isClosed_exists_mem_of_isCompact (isCompact_compactCovering ℝ n) hF).measurableSet

theorem measurableSet_zero_mem_image :
    MeasurableSet {p : C(ℝ, ℂ) × ℝ | (0 : ℂ) ∈ p.1 '' Icc 0 p.2} := by
  have hF : IsClosed {y : (C(ℝ, ℂ) × ℝ) × ℝ | 0 ≤ y.2 ∧ y.2 ≤ y.1.2 ∧ y.1.1 y.2 = 0} := by
    refine (isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_snd (continuous_snd.comp continuous_fst)).inter ?_)
    exact isClosed_eq (continuous_eval.comp
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd)) continuous_const
  refine (measurableSet_exists_real_of_isClosed hF).congr ?_
  ext p
  simp only [mem_ofPred_eq, mem_image, mem_Icc]
  constructor
  · rintro ⟨u, h1, h2, h3⟩
    exact ⟨u, ⟨h1, h2⟩, h3⟩
  · rintro ⟨u, ⟨h1, h2⟩, h3⟩
    exact ⟨u, h1, h2, h3⟩

theorem measurableSet_isRootRep (n : ℕ) :
    MeasurableSet {ξ : SurrData | IsRootRep R ξ.1 ξ.2 n} := by
  unfold IsRootRep
  refine (measurableSet_isRep n).inter ?_
  exact measurableSet_zero_mem_image.preimage
    ((measurable_σ_apply (qOf n)).prodMk (measurable_M_apply (qOf n)))

theorem measurable_rootIdx : Measurable fun ξ : SurrData => rootIdx R ξ.1 ξ.2 := by
  refine measurable_to_countable' fun n => ?_
  have hE : MeasurableSet {ξ : SurrData | ∃ m, IsRootRep R ξ.1 ξ.2 m} := by
    rw [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun m => measurableSet_isRootRep m
  have heq : (fun ξ : SurrData => rootIdx R ξ.1 ξ.2) ⁻¹' {n} =
      ({ξ | ∃ m, IsRootRep R ξ.1 ξ.2 m} ∩ ({ξ | IsRootRep R ξ.1 ξ.2 n} ∩
        ⋂ m ∈ Finset.range n, {ξ | IsRootRep R ξ.1 ξ.2 m}ᶜ)) ∪
      ({ξ | ∃ m, IsRootRep R ξ.1 ξ.2 m}ᶜ ∩ (if n = 0 then univ else ∅)) := by
    ext ξ
    simp only [mem_preimage, mem_singleton_iff, rootIdx, mem_union, mem_inter_iff,
      mem_ofPred_eq, mem_iInter, Finset.mem_range, mem_compl_iff]
    by_cases hex : ∃ m, IsRootRep R ξ.1 ξ.2 m
    · simp only [hex, ↓reduceDIte, true_and, not_true_eq_false, false_and, or_false]
      rw [Nat.find_eq_iff]
    · simp only [hex, ↓reduceDIte, false_and, not_false_eq_true, true_and, false_or]
      by_cases hn : n = 0
      · simp [hn]
      · simp [hn, Ne.symm hn]
  rw [heq]
  refine (hE.inter ((measurableSet_isRootRep n).inter
    (Finset.measurableSet_biInter _ fun m _ => (measurableSet_isRootRep m).compl))).union
    (hE.compl.inter ?_)
  split_ifs
  · exact MeasurableSet.univ
  · exact MeasurableSet.empty

theorem measurable_rootTime : Measurable fun ξ : SurrData => rootTime R ξ.1 ξ.2 := by
  unfold rootTime
  refine Measurable.add ?_ ?_
  · exact measurable_natSelect measurable_rootIdx (g := fun n ξ =>
      cumT (seqLen R ξ.1 ξ.2) (2 * n)) fun n => measurable_cumT (fun k => measurable_seqLen k) _
  · exact measurable_natSelect measurable_rootIdx (g := fun n ξ => hitTime (ξ.1 (qOf n)) 0)
      fun n => by
        have h := GMS4b.measurable_hitTime.comp
          ((measurable_σ_apply (qOf n)).prodMk (measurable_const (a := (0 : ℂ))))
        exact h

end measurability

end MatedCRTHarmonic.L43O
