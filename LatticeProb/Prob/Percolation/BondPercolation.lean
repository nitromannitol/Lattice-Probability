/-
Moved from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and
Yuval Peres.  Sources:

* `Rotor/Percolation.lean` (`BondConfig`, `bondLaw`, `half_le_one`, `IsOpenPath`,
  `boxCrossing`), where these are introduced for Bernoulli bond percolation on
  `ℤ²`, `rotor.tex:1658-1668`;
* `Rotor/External/LSS.lean` (only the `bernoulli` law on `Bool` used by
  `bondLaw`; the file's other content is the paper's frozen Liggett-Schonmann-
  Stacey domination hypothesis, which is specific to the rotor-routing
  termination argument and is not moved here);
* `Rotor/Support/BondFinite.lean` (`cylBonds` through `bondLaw_half_le_of_flip`),
  Proposition 5.1 (`prop:square-passage`), part 2;
* the closing "Bernoulli(p) on finitely many bonds" section of
  `Rotor/Support/FiniteProduct.lean` (`bondLaw_cyl`, `bondLaw_eq_sum`,
  `bondLaw_toReal_eq_fpr`), which connects the finite-parameter Russo/pivotal
  calculus of `LatticeProb.Prob.Percolation.FiniteProductPivotal` to `bondLaw`.

`Rotor/Percolation.lean` also imports `Rotor.External.LSS`, whose remaining
content (`bernoulliField`, `IsIncreasing`, `KDependent`, `LSS`) is not needed
by anything moved here and is not moved; only the `bernoulli` law is taken.
`rotor-23` additionally depends on `anthropics/formal-math`'s
`PercolationContinuity` package, but that dependency is used only by
`Rotor/Bridge/SubcriticalDecay.lean`, nowhere in the import chain of the
declarations below (verified directly against the source), so this module
does not, and must not, gain that dependency: everything here is over
Mathlib and `LatticeProb.Lattice.Planar` alone.

`Rotor.IsPath` (`Rotor/Model.lean`, `l.Nodup ∧ l.IsChain G.Adj` for a bare
`SimpleGraph V`) is unfolded directly into `IsOpenPath` below rather than
introduced as a separate declaration, since nothing else in this cluster uses
it.  `Rotor`'s own `linfDist` on `Site` is not redefined: it is already the
declaration `LatticeProb.Lattice.Planar.linfDist`.
-/
import LatticeProb.Lattice.Planar.Metric
import LatticeProb.Prob.Percolation.FiniteProductPivotal

/-!
# Bernoulli bond percolation on the square lattice

A bond configuration on `ℤ²` is a function from the edges (`Sym2 Site`) to
`Bool`; `bondLaw p hp` is Bernoulli bond percolation with parameter `p`, the
product of independent Bernoulli(`p`) coordinates.  `IsOpenPath` and
`boxCrossing` record the standard percolation-crossing event: `x` is joined by
an open path to the `ℓ^∞`-sphere of radius `r` about it.

The rest of the file develops the finite-dimensional structure of `bondLaw`
needed to apply Russo's formula (`LatticeProb.Prob.Percolation.
FiniteProductPivotal`) to it: an event determined by finitely many bonds
(`BondDetermined`) has a probability that is a finite sum over the
configurations of those bonds (`bondLaw_half_eq_sum`, `bondLaw_eq_sum`), which
is exactly the finite-model probability `fpr` computed on the parameters
restricted to those bonds (`bondLaw_toReal_eq_fpr`); and flipping a single
closed bond in a witnessing configuration cannot decrease the probability of
an increasing event determined by the same finite set (`bondLaw_half_le_of_flip`).
-/

open MeasureTheory Finset ENNReal Classical LatticeProb.Lattice.Planar

namespace LatticeProb.Percolation

/-! ### The Bernoulli law on `Bool` -/

-- `PMF.bernoulli` is deprecated in favour of `ProbabilityTheory.bernoulliMeasure`, but this
-- definition is read by `bondLaw` below, so it is kept verbatim (changing it would change what
-- `bondLaw` computes).
set_option linter.deprecated false in
/-- The Bernoulli law on `Bool` with success probability `p`. -/
noncomputable def bernoulli (p : NNReal) (hp : p ≤ 1) : Measure Bool := (PMF.bernoulli p hp).toMeasure

instance (p : NNReal) (hp : p ≤ 1) : IsProbabilityMeasure (bernoulli p hp) :=
  PMF.toMeasure.isProbabilityMeasure _

/-- `1/2` is a probability. -/
theorem half_le_one : (1 / 2 : NNReal) ≤ 1 := by
  rw [div_le_one (by norm_num)]; norm_num

/-! ### Bond configurations -/

/-- A bond configuration on `ℤ²`. -/
abbrev BondConfig := Sym2 Site → Bool

/-- Bernoulli bond percolation `ℙ_p`: the product of independent Bernoulli(`p`)
laws over every edge. -/
noncomputable def bondLaw (p : NNReal) (hp : p ≤ 1) : Measure BondConfig :=
  Measure.infinitePi (fun _ : Sym2 Site => bernoulli p hp)

instance (p : NNReal) (hp : p ≤ 1) : IsProbabilityMeasure (bondLaw p hp) := by
  unfold bondLaw; infer_instance

/-- An open path: consecutive sites are adjacent in the square lattice, without
repetition, and the bond between them is open. -/
def IsOpenPath (ω : BondConfig) (l : List Site) : Prop :=
  (l.Nodup ∧ l.IsChain squareGraph.Adj) ∧ l.IsChain (fun u v => ω s(u, v) = true)

/-- `x` is joined to `{y : |y-x|_∞ = r}` by an open path inside
`{y : |y-x|_∞ ≤ r}`. -/
def boxCrossing (x : Site) (r : ℕ) : Set BondConfig :=
  {ω | ∃ l : List Site, IsOpenPath ω l ∧ l.head? = some x ∧ (∀ y ∈ l, linfDist y x ≤ r) ∧
    ∃ y ∈ l.getLast?, linfDist y x = r}

/-! ### Events determined by finitely many bonds -/

/-- The configurations agreeing with `ξ` on the bonds `F`. -/
def cylBonds (F : Finset (Sym2 Site)) (ξ : Sym2 Site → Bool) : Set BondConfig :=
  {ω | ∀ b ∈ F, ω b = ξ b}

theorem measurableSet_cylBonds (F : Finset (Sym2 Site)) (ξ : Sym2 Site → Bool) :
    MeasurableSet (cylBonds F ξ) := by
  have : cylBonds F ξ = ⋂ b ∈ F, (fun ω : BondConfig => ω b) ⁻¹' {ξ b} := by
    ext ω; simp [cylBonds]
  rw [this]
  exact MeasurableSet.biInter (Finset.countable_toSet F)
    (fun b _ => measurable_pi_apply b MeasurableSet.of_discrete)

set_option linter.deprecated false in
theorem bondLaw_half_cyl (F : Finset (Sym2 Site)) (ξ : Sym2 Site → Bool) :
    bondLaw (1 / 2) half_le_one (cylBonds F ξ) = (1 / 2 : ℝ≥0∞) ^ F.card := by
  have hset : cylBonds F ξ = Set.pi (↑F) (fun b => {ξ b}) := by
    ext ω; simp [cylBonds, Set.pi]
  rw [hset]
  unfold bondLaw
  have key := Measure.infinitePi_pi (μ := fun _ : Sym2 Site => bernoulli (1 / 2) half_le_one)
    (s := F) (t := fun b => {ξ b}) (fun _ _ => MeasurableSet.of_discrete)
  refine key.trans ?_
  have hb : ∀ b, bernoulli (1 / 2) half_le_one {ξ b} = 1 / 2 := by
    intro b
    unfold bernoulli
    rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.of_discrete), PMF.bernoulli_apply]
    rcases ξ b with _ | _ <;> simp
  simp only [hb, Finset.prod_const]

/-- `E` depends only on the bonds in `F`. -/
def BondDetermined (F : Finset (Sym2 Site)) (E : Set BondConfig) : Prop :=
  ∀ ω ω' : BondConfig, (∀ b ∈ F, ω b = ω' b) → (ω ∈ E ↔ ω' ∈ E)

/-- The configuration on `F` given by `ξ`, closed elsewhere. -/
def extF (F : Finset (Sym2 Site)) (ξ : ↥F → Bool) : BondConfig :=
  fun b => if h : b ∈ F then ξ ⟨b, h⟩ else false

/-- The restriction of `ω` to `F`. -/
def resF (F : Finset (Sym2 Site)) (ω : BondConfig) : ↥F → Bool := fun b => ω b.1

theorem mem_cylBonds_extF (F : Finset (Sym2 Site)) (ξ : ↥F → Bool) (ω : BondConfig) :
    ω ∈ cylBonds F (extF F ξ) ↔ resF F ω = ξ := by
  constructor
  · intro h
    funext b
    have := h b.1 b.2
    simp only [extF, b.2, dite_true] at this
    exact this
  · intro h b hb
    rw [← h]
    simp [extF, hb, resF]

theorem cylBonds_extF_disjoint (F : Finset (Sym2 Site)) {ξ ξ' : ↥F → Bool} (h : ξ ≠ ξ') :
    Disjoint (cylBonds F (extF F ξ)) (cylBonds F (extF F ξ')) := by
  rw [Set.disjoint_left]
  intro ω h1 h2
  rw [mem_cylBonds_extF] at h1 h2
  exact h (h1.symm.trans h2)

theorem determined_inter_cyl (F : Finset (Sym2 Site)) {E : Set BondConfig} (hE : BondDetermined F E)
    (ξ : ↥F → Bool) :
    E ∩ cylBonds F (extF F ξ) = if extF F ξ ∈ E then cylBonds F (extF F ξ) else ∅ := by
  ext ω
  split_ifs with hξ
  · simp only [Set.mem_inter_iff, and_iff_right_iff_imp]
    intro hω
    exact (hE _ _ (fun b hb => (hω b hb).symm)).1 hξ
  · simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hω hcyl
    exact hξ ((hE _ _ (fun b hb => hcyl b hb)).1 hω)

theorem iUnion_cylBonds_extF (F : Finset (Sym2 Site)) :
    ⋃ ξ : ↥F → Bool, cylBonds F (extF F ξ) = Set.univ := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨resF F ω, by rw [mem_cylBonds_extF]⟩

theorem measurableSet_of_determined (F : Finset (Sym2 Site)) {E : Set BondConfig}
    (hE : BondDetermined F E) : MeasurableSet E := by
  have : E = ⋃ ξ : ↥F → Bool, (E ∩ cylBonds F (extF F ξ)) := by
    rw [← Set.inter_iUnion, iUnion_cylBonds_extF, Set.inter_univ]
  rw [this]
  refine MeasurableSet.iUnion (fun ξ => ?_)
  rw [determined_inter_cyl F hE]
  split_ifs
  · exact measurableSet_cylBonds F _
  · exact MeasurableSet.empty

/-- Bernoulli(1/2) of an `F`-determined event counts its configurations on `F`. -/
theorem bondLaw_half_eq_sum (F : Finset (Sym2 Site)) {E : Set BondConfig}
    (hE : BondDetermined F E) :
    bondLaw (1 / 2) half_le_one E =
      ∑ ξ : ↥F → Bool, if extF F ξ ∈ E then (1 / 2 : ℝ≥0∞) ^ F.card else 0 := by
  classical
  have hunion : E = ⋃ ξ : ↥F → Bool, (E ∩ cylBonds F (extF F ξ)) := by
    rw [← Set.inter_iUnion, iUnion_cylBonds_extF, Set.inter_univ]
  conv_lhs => rw [hunion]
  rw [measure_iUnion (fun ξ ξ' hne => Set.disjoint_of_subset Set.inter_subset_right
      Set.inter_subset_right (cylBonds_extF_disjoint F hne))
    (fun ξ => (measurableSet_of_determined F hE).inter (measurableSet_cylBonds F _))]
  rw [tsum_fintype]
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  rw [determined_inter_cyl F hE]
  split_ifs
  · exact bondLaw_half_cyl F _
  · exact measure_empty

/-- Flipping the bond `b` open: if it maps `E₁ ⊆ {b closed}` into `E₂`, then
`μ E₁ ≤ μ E₂` (both determined by `F ∋ b`). -/
theorem bondLaw_half_le_of_flip (F : Finset (Sym2 Site)) {E₁ E₂ : Set BondConfig}
    (h₁ : BondDetermined F E₁) (h₂ : BondDetermined F E₂) {b : Sym2 Site} (hb : b ∈ F)
    (hclosed : ∀ ω ∈ E₁, ω b = false) (hflip : ∀ ω ∈ E₁, Function.update ω b true ∈ E₂) :
    bondLaw (1 / 2) half_le_one E₁ ≤ bondLaw (1 / 2) half_le_one E₂ := by
  classical
  rw [bondLaw_half_eq_sum F h₁, bondLaw_half_eq_sum F h₂]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  refine (ENNReal.mul_le_mul_iff_left (pow_ne_zero _ (by norm_num)) (ENNReal.pow_ne_top (by norm_num))).2
    (Nat.cast_le.2 ?_)
  -- the injection `ξ ↦ ξ[b := true]`
  refine Finset.card_le_card_of_injOn (fun ξ : ↥F → Bool => Function.update ξ (⟨b, hb⟩ : ↥F) true) ?_ ?_
  · intro ξ hξ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hξ ⊢
    have := hflip _ hξ
    have hext : extF F (Function.update ξ ⟨b, hb⟩ true) = Function.update (extF F ξ) b true := by
      funext c
      by_cases hcb : c = b
      · subst hcb
        simp [extF, hb]
      · have hne : ∀ (hc : c ∈ F), (⟨c, hc⟩ : ↥F) ≠ ⟨b, hb⟩ := fun hc h => hcb (congrArg Subtype.val h)
        by_cases hc : c ∈ F
        · simp [extF, hc, Function.update_of_ne (hne hc), Function.update_of_ne hcb]
        · simp [extF, hc, Function.update_of_ne hcb]
    rw [hext]; exact this
  · intro ξ hξ ξ' hξ' heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hξ hξ'
    have hξb : ξ ⟨b, hb⟩ = false := by
      have := hclosed _ hξ; simpa [extF, hb] using this
    have hξ'b : ξ' ⟨b, hb⟩ = false := by
      have := hclosed _ hξ'; simpa [extF, hb] using this
    funext c
    by_cases hc : c = ⟨b, hb⟩
    · subst hc; rw [hξb, hξ'b]
    · have := congrFun heq c
      simpa [Function.update, hc] using this

/-! ### Bernoulli(`p`) on finitely many bonds, and the finite-parameter model -/

set_option linter.deprecated false in
theorem bondLaw_cyl (p : NNReal) (hp : p ≤ 1) (F : Finset (Sym2 Site)) (ξ : Sym2 Site → Bool) :
    bondLaw p hp (cylBonds F ξ) = ∏ b ∈ F, (if ξ b then (p : ℝ≥0∞) else 1 - p) := by
  have hset : cylBonds F ξ = Set.pi (↑F) (fun b => {ξ b}) := by
    ext ω; simp [cylBonds, Set.pi]
  rw [hset]
  unfold bondLaw
  have key := MeasureTheory.Measure.infinitePi_pi (μ := fun _ : Sym2 Site => bernoulli p hp)
    (s := F) (t := fun b => {ξ b}) (fun _ _ => MeasurableSet.of_discrete)
  refine key.trans ?_
  refine Finset.prod_congr rfl (fun b _ => ?_)
  unfold bernoulli
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.of_discrete), PMF.bernoulli_apply]
  rcases ξ b with _ | _ <;> simp

/-- Bernoulli(`p`) of an `F`-determined event counts its configurations on `F`,
weighted by `p`. -/
theorem bondLaw_eq_sum (p : NNReal) (hp : p ≤ 1) (F : Finset (Sym2 Site)) {E : Set BondConfig}
    (hE : BondDetermined F E) :
    bondLaw p hp E = ∑ ξ : ↥F → Bool,
      if extF F ξ ∈ E then ∏ b : ↥F, (if ξ b then (p : ℝ≥0∞) else 1 - p) else 0 := by
  have hunion : E = ⋃ ξ : ↥F → Bool, (E ∩ cylBonds F (extF F ξ)) := by
    rw [← Set.inter_iUnion, iUnion_cylBonds_extF, Set.inter_univ]
  conv_lhs => rw [hunion]
  rw [MeasureTheory.measure_iUnion (fun ξ ξ' hne => Set.disjoint_of_subset Set.inter_subset_right
      Set.inter_subset_right (cylBonds_extF_disjoint F hne))
    (fun ξ => (measurableSet_of_determined F hE).inter (measurableSet_cylBonds F _))]
  rw [tsum_fintype]
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  rw [determined_inter_cyl F hE]
  split_ifs
  · rw [bondLaw_cyl, ← Finset.prod_coe_sort F]
    refine Fintype.prod_congr _ _ (fun b => ?_)
    simp [extF, b.2]
  · exact MeasureTheory.measure_empty

/-- The finite model of `bondLaw p` on the bonds `F` is the finite-parameter
probability `fpr` of `LatticeProb.Prob.Percolation.FiniteProductPivotal`, on
the parameters `par b = p` for every bond `b ∈ F`, restricted to the event
`{ξ | extF F ξ ∈ E}`. -/
theorem bondLaw_toReal_eq_fpr (p : NNReal) (hp : p ≤ 1) (F : Finset (Sym2 Site)) {E : Set BondConfig}
    (hE : BondDetermined F E) :
    (bondLaw p hp E).toReal = fpr (fun _ : ↥F => (p : ℝ)) {ξ | extF F ξ ∈ E} := by
  rw [bondLaw_eq_sum p hp F hE, ENNReal.toReal_sum (fun ξ _ => by
    split_ifs
    · exact ENNReal.prod_ne_top (fun b _ => by split_ifs <;> simp)
    · simp)]
  unfold fpr fpw
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  simp only [Set.mem_setOf_eq]
  split_ifs with h
  · rw [ENNReal.toReal_prod]
    refine Fintype.prod_congr _ _ (fun b => ?_)
    split_ifs
    · simp
    · rw [ENNReal.toReal_sub_of_le (by exact_mod_cast hp) ENNReal.one_ne_top]; simp
  · simp

end LatticeProb.Percolation
