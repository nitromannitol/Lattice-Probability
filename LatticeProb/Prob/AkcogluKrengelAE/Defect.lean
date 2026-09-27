import LatticeProb.Prob.AkcogluKrengelAE.UpperBound

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-!
# The lower bound: route, and the additive part and defect (Step 4, part A)

Route for the lower bound `γ ≤ ∫ liminf cubeRatio f n`, where `γ := inf_{n ≥ 1} ∫ cubeRatio f n`;
the remaining parts (B)-(F) live in the sibling files of this directory. For a process `F` with the
file's hypotheses, `addPart F B` sums `F` over the unit cells of `B` and `boxDefect F B` is the
resulting defect of subadditivity. Guillotine splitting down to unit cells shows `boxDefect F` is
nonnegative on boxes, superadditive along two-box splits, monotone under inclusion of boxes,
stationary, and bounded by `C` times the volume; and `addPart F (Q_k) = k ^ d` times the grid
average of `F` on unit cells, so `cubeRatio F k = gridAvg - boxDefect F (Q_k) / k ^ d`.
-/

open MeasureTheory Filter Topology

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The constant of the maximal inequality. -/
noncomputable def akMaxConst (d : ℕ) : ℝ := 2 * (4 * (d : ℝ)) ^ d

/-- Sum of `F` over the unit cells of `B`. -/
noncomputable def addPart {d : ℕ} (F : Finset (Site d) → Ω → ℝ) (B : Finset (Site d)) (ω : Ω) :
    ℝ :=
  ∑ z ∈ B, F {z} ω

/-- The defect of subadditivity with respect to unit cells. -/
noncomputable def boxDefect {d : ℕ} (F : Finset (Site d) → Ω → ℝ) (B : Finset (Site d))
    (ω : Ω) : ℝ :=
  addPart F B ω - F B ω

/-- The dyadic cell of level `j`, offset `u` and index `c`: `u + 2^j c + [0, 2^j)^d`. -/
noncomputable def dyCell {d : ℕ} (u : Site d) (j : ℕ) (c : Site d) : Finset (Site d) :=
  latticeBox (u + (2 ^ j : ℤ) • c) (u + (2 ^ j : ℤ) • c + fun _ => (2 ^ j : ℤ) - 1)

/-- The union of the level-`J` cells of offset `u` meeting `[-2^J, N + 2^J)^d`, a cube of side
`(N / 2^J + 4) 2^J` with lower corner `u - 2 · 2^J`. -/
noncomputable def dyBig {d : ℕ} (u : Site d) (J N : ℕ) : Finset (Site d) :=
  (latticeCube d ((N / 2 ^ J + 4) * 2 ^ J)).map
    (Equiv.addRight (u - fun _ => 2 * (2 ^ J : ℤ))).toEmbedding

/-- Blow-up by the factor `m`: the site `z` becomes the cube `m z + [0, m)^d`. -/
noncomputable def blowup {d : ℕ} (m : ℕ) (B : Finset (Site d)) : Finset (Site d) :=
  B.biUnion fun z => (latticeCube d m).map (Equiv.addRight ((m : ℤ) • z)).toEmbedding

/-- The coarse-grained process at scale `m`, normalised per fine site. -/
noncomputable def coarse {d : ℕ} (f : Finset (Site d) → Ω → ℝ) (m : ℕ) (B : Finset (Site d))
    (ω : Ω) : ℝ :=
  f (blowup m B) ω / (m : ℝ) ^ d

/-- The maximal-inequality constant `akMaxConst d = 2 (4d) ^ d` is positive. -/
theorem akMaxConst_pos {d : ℕ} (hd : 1 ≤ d) : 0 < akMaxConst d := by
  unfold akMaxConst
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

/-! #### (A) Additive part and defect -/

/-- A box with at least two sites has a coordinate where the lower and upper corners differ. -/
theorem exists_lt_of_two_le_card_latticeBox {d : ℕ} (a b : Site d) (h : 2 ≤ (latticeBox a
    b).card) :
    ∃ i, a i < b i := by
  by_contra hne
  push Not at hne
  have hsub : latticeBox a b ⊆ {a} := by
    intro x hx
    have hx' := (mem_latticeBox_iff a b x).1 hx
    rw [Finset.mem_singleton]
    funext i
    exact le_antisymm ((hx' i).2.trans (hne i)) (hx' i).1
  have := Finset.card_le_card hsub
  rw [Finset.card_singleton] at this
  omega

/-- Cutting a box with `a ≤ b` at a strict coordinate `i` produces two strictly smaller pieces (each
contains one of the two corners). -/
theorem card_latticeBox_update_lt_of_lt {d : ℕ} (a b : Site d) (hab : a ≤ b) (i : Fin d) (hi
    : a i < b i) :
    (latticeBox a (Function.update b i (b i - 1))).card < (latticeBox a b).card ∧
      (latticeBox (Function.update a i (b i)) b).card < (latticeBox a b).card := by
  have hs := isBoxSplit_latticeBox_update_of_mem a b i (b i) hi.le (by omega)
  have hcard := hs.2.2.2.2 ▸ Finset.card_union_of_disjoint hs.2.2.2.1
  have ha : a ∈ latticeBox a (Function.update b i (b i - 1)) := by
    rw [mem_latticeBox_iff]; intro j
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self]; exact ⟨le_rfl, by omega⟩
    · rw [Function.update_of_ne hj]; exact ⟨le_rfl, hab j⟩
  have hb : b ∈ latticeBox (Function.update a i (b i)) b := by
    rw [mem_latticeBox_iff]; intro j
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self]; exact ⟨le_rfl, le_rfl⟩
    · rw [Function.update_of_ne hj]; exact ⟨hab j, le_rfl⟩
  have h1 := Finset.card_pos.2 ⟨a, ha⟩
  have h2 := Finset.card_pos.2 ⟨b, hb⟩
  omega

omit [MeasurableSpace Ω] in
/-- A box of at most one site satisfies `F box ≤ addPart F box`, directly from the empty or
singleton case. -/
theorem boxFun_le_addPart_of_card_le_one {d : ℕ} {F : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ F A ω ∧ F A ω ≤ C * A.card) (a b : Site d)
    (hcard : (latticeBox a b).card ≤ 1) (ω : Ω) :
    F (latticeBox a b) ω ≤ addPart F (latticeBox a b) ω := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hcard with h0 | h1
  · rw [Finset.card_eq_zero.1 h0, boxFun_empty_eq_zero hC ω]
    simp [addPart]
  · obtain ⟨z, hz⟩ := Finset.card_eq_one.1 h1
    rw [hz]
    simp [addPart]

omit [MeasurableSpace Ω] in
/-- `addPart F` is additive along a two-box split. -/
theorem addPart_eq_add_of_isBoxSplit {d : ℕ} (F : Finset (Site d) → Ω → ℝ) {B B₁ B₂ : Finset
    (Site d)}
    (h : IsBoxSplit B B₁ B₂) (ω : Ω) :
    addPart F B ω = addPart F B₁ ω + addPart F B₂ ω := by
  unfold addPart
  rw [← h.2.2.2.2, Finset.sum_union h.2.2.2.1]

omit [MeasurableSpace Ω] in
/-- Guillotine splitting down to unit cells gives `F box ≤ addPart F box` for every box, by strong
induction on the number of sites. -/
theorem boxFun_le_addPart {d : ℕ} {F : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ F A ω ∧ F A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → F B ω ≤ F B₁ ω + F B₂ ω) (a b : Site d) (ω : Ω) :
    F (latticeBox a b) ω ≤ addPart F (latticeBox a b) ω := by
  induction hn : (latticeBox a b).card using Nat.strong_induction_on generalizing a b with
  | _ n ih =>
    rcases le_or_gt n 1 with h1 | h2
    · exact boxFun_le_addPart_of_card_le_one hC a b (hn ▸ h1) ω
    · obtain ⟨i, hi⟩ := exists_lt_of_two_le_card_latticeBox a b (by omega)
      have hab : a ≤ b := Finset.nonempty_Icc.1 (Finset.card_pos.1 (by
          unfold latticeBox at hn; omega))
      have hs := isBoxSplit_latticeBox_update_of_mem a b i (b i) hi.le (by omega)
      obtain ⟨c1, c2⟩ := card_latticeBox_update_lt_of_lt a b hab i hi
      have e1 := ih _ (hn ▸ c1) _ _ rfl
      have e2 := ih _ (hn ▸ c2) _ _ rfl
      rw [addPart_eq_add_of_isBoxSplit F hs ω]
      linarith [hsub _ _ _ ω hs]

omit [MeasurableSpace Ω] in
/-- `addPart F B` lies between `0` and `C * B.card`. -/
theorem addPart_nonneg_le {d : ℕ} {F : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ F A ω ∧ F A ω ≤ C * A.card) (B : Finset (Site d)) (ω : Ω) :
    0 ≤ addPart F B ω ∧ addPart F B ω ≤ C * B.card := by
  unfold addPart
  refine ⟨Finset.sum_nonneg fun z _ => (hC {z} ω).1, ?_⟩
  calc ∑ z ∈ B, F {z} ω ≤ ∑ _z ∈ B, C :=
        Finset.sum_le_sum fun z _ => by simpa using (hC {z} ω).2
    _ = C * B.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

omit [MeasurableSpace Ω] in
/-- `boxDefect F` is nonnegative on boxes and bounded above by `C * B.card`. -/
theorem boxDefect_latticeBox_nonneg_le {d : ℕ} {F : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ F A ω ∧ F A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → F B ω ≤ F B₁ ω + F B₂ ω) :
    (∀ a b ω, 0 ≤ boxDefect F (latticeBox a b) ω) ∧
      ∀ B ω, boxDefect F B ω ≤ C * B.card := by
  refine ⟨fun a b ω => ?_, fun B ω => ?_⟩
  · have := boxFun_le_addPart hC hsub a b ω
    unfold boxDefect; linarith
  · have := (addPart_nonneg_le hC B ω).2
    have := (hC B ω).1
    unfold boxDefect; linarith

omit [MeasurableSpace Ω] in
/-- `boxDefect F` is superadditive along a two-box split. -/
theorem boxDefect_superadditive_of_isBoxSplit {d : ℕ} {F : Finset (Site d) → Ω → ℝ}
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → F B ω ≤ F B₁ ω + F B₂ ω)
    {B B₁ B₂ : Finset (Site d)} (h : IsBoxSplit B B₁ B₂) (ω : Ω) :
    boxDefect F B₁ ω + boxDefect F B₂ ω ≤ boxDefect F B ω := by
  have h1 := addPart_eq_add_of_isBoxSplit F h ω
  have h2 := hsub B B₁ B₂ ω h
  unfold boxDefect; linarith

omit [MeasurableSpace Ω] in
/-- The auxiliary process `A ↦ min (F A) (addPart F A) - addPart F A + C * A.card` satisfies the
file's nonnegativity/volume bound and two-box subadditivity hypotheses. -/
theorem defectAuxProcess_bound_and_subadditive {d : ℕ} {F : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ F A ω ∧ F A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → F B ω ≤ F B₁ ω + F B₂ ω) :
    (∀ A ω, 0 ≤ min (F A ω) (addPart F A ω) - addPart F A ω + C * A.card ∧
        min (F A ω) (addPart F A ω) - addPart F A ω + C * A.card ≤ C * A.card) ∧
      ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ →
        min (F B ω) (addPart F B ω) - addPart F B ω + C * B.card ≤
          (min (F B₁ ω) (addPart F B₁ ω) - addPart F B₁ ω + C * B₁.card) +
            (min (F B₂ ω) (addPart F B₂ ω) - addPart F B₂ ω + C * B₂.card) := by
  refine ⟨?_, ?_⟩
  · intro A ω
    have had := addPart_nonneg_le hC A ω
    have hF := hC A ω
    constructor
    · rcases le_total (F A ω) (addPart F A ω) with hmin | hmin
      · rw [min_eq_left hmin]; linarith [had.1, had.2, hF.1, hF.2]
      · rw [min_eq_right hmin]; linarith [had.1, had.2, hF.1, hF.2]
    · linarith [min_le_right (F A ω) (addPart F A ω)]
  · intro B B1 B2 ω h
    obtain ⟨hB, hB1, hB2, hdisj, hunion⟩ := h
    obtain ⟨a, b, hab⟩ := hB
    obtain ⟨c, d, hcd⟩ := hB1
    obtain ⟨e, g, heg⟩ := hB2
    subst hab
    subst hcd
    subst heg
    have h4 := boxFun_le_addPart hC hsub
    have h8 := boxDefect_superadditive_of_isBoxSplit hsub ⟨⟨a, b, rfl⟩, ⟨c, d, rfl⟩, ⟨e, g, rfl⟩,
        hdisj, hunion⟩ ω
    simp only [boxDefect] at h8
    have hcardnat : (latticeBox a b).card = (latticeBox c d).card + (latticeBox e g).card :=
      (congrArg Finset.card hunion).symm.trans (Finset.card_union_of_disjoint hdisj)
    have hcard : ((latticeBox a b).card : ℝ) =
        ((latticeBox c d).card : ℝ) + ((latticeBox e g).card : ℝ) :=
      (congrArg (fun t : ℕ => (t : ℝ)) hcardnat).trans (Nat.cast_add _ _)
    have hCcard : C * ((latticeBox a b).card : ℝ) =
        C * ((latticeBox c d).card : ℝ) + C * ((latticeBox e g).card : ℝ) :=
      (congrArg (fun t : ℝ => C * t) hcard).trans (mul_add C _ _)
    have e1 : min (F (latticeBox c d) ω) (addPart F (latticeBox c d) ω) =
        F (latticeBox c d) ω := min_eq_left (h4 c d ω)
    have e2 : min (F (latticeBox e g) ω) (addPart F (latticeBox e g) ω) =
        F (latticeBox e g) ω := min_eq_left (h4 e g ω)
    have emin : min (F (latticeBox a b) ω) (addPart F (latticeBox a b) ω) ≤
        F (latticeBox a b) ω := min_le_left _ _
    linarith [h8, hCcard, e1, e2, emin]


omit [MeasurableSpace Ω] in
/-- `boxDefect F` is monotone under inclusion of boxes: a smaller box has smaller defect. -/
theorem boxDefect_mono_of_subset {d : ℕ} {F : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ F A ω ∧ F A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → F B ω ≤ F B₁ ω + F B₂ ω)
    (a b a' b' : Site d) (ha : a ≤ a') (hb : b' ≤ b) (ω : Ω) :
    boxDefect F (latticeBox a' b') ω ≤ boxDefect F (latticeBox a b) ω := by
  obtain ⟨hG, hGsub⟩ := defectAuxProcess_bound_and_subadditive hC hsub
  have h9 := boxFun_le_nested_add_defect (f := fun A ω => min (F A ω) (addPart F A ω) - addPart F A
      ω + C * A.card)
    hG hGsub a b a' b' ha hb ω
  rw [min_eq_left (boxFun_le_addPart hC hsub a b ω), min_eq_left (boxFun_le_addPart hC hsub a' b'
      ω)] at h9
  unfold boxDefect
  linarith

omit [MeasurableSpace Ω] in
/-- `boxDefect F` is stationary under the translation action `τ`. -/
theorem boxDefect_map_addRight_eq {d : ℕ} {F : Finset (Site d) → Ω → ℝ} (τ : Site d → Ω → Ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      F (A.map (Equiv.addRight z).toEmbedding) ω = F A (τ z ω))
    (B : Finset (Site d)) (z : Site d) (ω : Ω) :
    boxDefect F (B.map (Equiv.addRight z).toEmbedding) ω = boxDefect F B (τ z ω) := by
  unfold boxDefect addPart
  rw [hstat B z ω]
  congr 1
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.map_singleton (Equiv.addRight z).toEmbedding x, hstat {x} z ω]


/-- `boxDefect F B` is measurable. -/
theorem measurable_boxDefect {d : ℕ} {F : Finset (Site d) → Ω → ℝ} (hmeas : ∀ A, Measurable
    (F A))
    (B : Finset (Site d)) : Measurable (boxDefect F B) := by
  exact (Finset.measurable_sum _ fun z _ => hmeas {z}).sub (hmeas B)

omit [MeasurableSpace Ω] in
/-- `F` of the singleton `{z}` equals `F` of the unit cube composed with the action at `z`. -/
theorem boxFun_singleton_eq_apply_cube_one {d : ℕ} {F : Finset (Site d) → Ω → ℝ} (τ : Site d
    → Ω → Ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      F (A.map (Equiv.addRight z).toEmbedding) ω = F A (τ z ω)) (z : Site d) (ω : Ω) :
    F {z} ω = F (latticeCube d 1) (τ z ω) := by
  have h1 : latticeCube d 1 = {0} := by
    simp [latticeCube]
    rfl
  have h2 : ({z} : Finset (Site d)) = (latticeCube d 1).map (Equiv.addRight z).toEmbedding := by
    rw [h1, Finset.map_singleton]; simp
  rw [h2, hstat]

/-- A sum over the cube `latticeCube d k` reindexes, via `natToSite`, as a sum over the full grid
`gridSet d Finset.univ k`. -/
theorem sum_latticeCube_eq_sum_gridSet_natToSite {d : ℕ} {M : Type*} [AddCommMonoid M] (k :
    ℕ) (g : Site d → M) :
    ∑ z ∈ latticeCube d k, g z = ∑ w ∈ gridSet d Finset.univ k, g (natToSite w) := by
  refine Finset.sum_nbij' (fun (z : Site d) (i : Fin d) => (z i).toNat)
    (fun w : Fin d → ℕ => natToSite w) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rw [gridSet, Fintype.mem_piFinset]
    simp only [Finset.mem_univ, if_true, Finset.mem_range]
    intro i
    rw [latticeCube, Finset.mem_Icc] at hz
    simp only [Pi.le_def, Pi.zero_apply] at hz
    have h1 := hz.1 i
    have h2 := hz.2 i
    exact (Int.toNat_lt h1).2 (by omega)
  · intro w hw
    rw [gridSet, Fintype.mem_piFinset] at hw
    simp only [Finset.mem_univ, if_true, Finset.mem_range] at hw
    rw [latticeCube, Finset.mem_Icc]
    simp only [Pi.le_def, Pi.zero_apply, natToSite]
    refine ⟨fun i => Int.natCast_nonneg (w i), ?_⟩
    intro i
    have h := hw i
    omega
  · intro z hz
    funext i
    rw [latticeCube, Finset.mem_Icc] at hz
    simp only [Pi.le_def, Pi.zero_apply] at hz
    simp only [natToSite]
    exact Int.toNat_of_nonneg (hz.1 i)
  · intro w hw
    funext i
    simp only [natToSite]
    exact Int.toNat_natCast (w i)
  · intro z hz
    rw [latticeCube, Finset.mem_Icc] at hz
    simp only [Pi.le_def, Pi.zero_apply] at hz
    congr 1
    funext i
    simp only [natToSite]
    exact (Int.toNat_of_nonneg (hz.1 i)).symm


omit [MeasurableSpace Ω] in
/-- `addPart F` of the cube of side `k` equals `k ^ d` times the grid average of `F (latticeCube d
1)`. -/
theorem addPart_cube_eq_pow_mul_gridAvg {d : ℕ} {F : Finset (Site d) → Ω → ℝ} (τ : Site d →
    Ω → Ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      F (A.map (Equiv.addRight z).toEmbedding) ω = F A (τ z ω)) {k : ℕ} (hk : 1 ≤ k) (ω : Ω) :
    addPart F (latticeCube d k) ω =
      (k : ℝ) ^ d * gridAvg τ (F (latticeCube d 1)) Finset.univ k ω := by
  unfold addPart
  rw [sum_latticeCube_eq_sum_gridSet_natToSite]
  rw [gridAvg]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [mul_div_cancel₀ _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega : k ≠ 0)))]
  exact Finset.sum_congr rfl fun w _ => (boxFun_singleton_eq_apply_cube_one τ hstat (natToSite w) ω)

end LatticeProb
