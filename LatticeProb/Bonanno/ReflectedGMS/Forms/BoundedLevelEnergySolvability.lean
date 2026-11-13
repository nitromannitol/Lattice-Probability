/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.BoundedLevelEnergySolvability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteMinimizerPointwiseConvergence

/-!
# Solvability of an anchored trace problem from bounded level energies

`Forms/FiniteDirichletEnergyLimit.lean` and `Forms/FiniteMinimizerPointwiseConvergence.lean`
both carry the hypothesis `hu : G.HasFiniteEnergy u` on the *reference field* `u` whose
trace is prescribed on the anchor set `A`.  That hypothesis is exactly what is unavailable
in the block-interpolation problem: there the reference is the cell centroid map, whose full
Dirichlet energy on a patch is in general infinite, and whether *some* finite-energy field
carries the centroid trace is precisely the question being asked.

This module removes the hypothesis.  Two things are extracted and then combined.

* **Bounded level energies imply finite energy.**
  `hasFiniteEnergy_of_restrictedEnergy_le` is the standalone form of the lower
  semicontinuity step that until now existed only inline inside
  `FiniteDirichletEnergyLimit.tendsto_levelEnergy_of_tendsto_pointwise`: if the restricted
  energies of a *single* field `g` along a monotone exhausting family of finite levels are
  bounded by `M`, then `g` has finite energy and `G.Energy g ≤ M`.  No minimality, no
  reference field, and no anchoring occur.  (The analogue in the other tree,
  `ReflectedWalk/FiniteApproximation.lean`'s `hasFiniteEnergy_and_Energy_le_of_energyOn_le`,
  needs a connected `G.Exhaustion`; this one needs neither connectivity nor an exhaustion
  structure.)

* **A bare constant replaces the reference energy in the pointwise bound.**
  `exists_pointwise_uniform_bound_of_levelEnergy_le` is
  `FiniteMinimizerPointwiseConvergence.exists_pointwise_uniform_bound` with `G.Energy u`
  replaced by an arbitrary upper bound `C` for the level energies.  The proof of the
  original uses `hu` only through `levelEnergy_le_energy`, so this is a verbatim
  substitution; the minimality hypothesis `hmin` disappears with it.

Combining them, `exists_finiteEnergy_trace_of_levelEnergy_le` produces an actual
finite-energy field with the prescribed trace out of nothing but a uniform bound on the
level energies, and `exists_finiteEnergy_trace_iff_bddAbove` turns this into an
**equivalence**:

  some finite-energy field carries the trace  ↔  the level minimum energies are bounded.

`exists_finiteEnergy_trace_iff_exists_nat` records the same equivalence with a natural
number threshold, the form in which the right-hand side is a countable union of
level-energy sublevel events.

The graph may be disconnected and infinite, `A` may be infinite, no level is connected, and
the competition class is the full finite-energy space throughout.

**This file proves no main theorem.**
-/

set_option autoImplicit false

namespace ReflectedGMS

namespace BoundedLevelEnergySolvability

open Filter Topology
open FiniteDirichletEnergyLimit FiniteMinimizerPointwiseConvergence

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

/-! ### Bounded level energies imply finite energy -/

/-- **Bounded restricted energies along a monotone exhausting family imply finite energy.**

Only one field is involved: no minimizer, no reference field, no anchor set.  Every finite
block of edges is contained in a single level, where the block bound
`sum_gradSq_le_two_restrictedEnergy` applies, so all finite partial sums of `gradSq g` are
bounded by `2 * M` and the full energy is summable with `G.Energy g ≤ M`.

This is the standalone form of the step that previously existed only inline inside
`FiniteDirichletEnergyLimit.tendsto_levelEnergy_of_tendsto_pointwise`. -/
theorem hasFiniteEnergy_of_restrictedEnergy_le {L : ℕ → Finset V} (hmono : Monotone L)
    (hcover : ∀ x : V, ∃ n, x ∈ L n) (g : V → ℝ) {M : ℝ}
    (hlevel : ∀ m : ℕ, restrictedEnergy G (↑(L m) : Set V) g ≤ M) :
    G.HasFiniteEnergy g ∧ G.Energy g ≤ M := by
  classical
  have hgnonneg : ∀ p : V × V, 0 ≤ G.gradSq g p := fun p => G.gradSq_nonneg g p
  have hsum : ∀ t : Finset (V × V), ∑ p ∈ t, G.gradSq g p ≤ 2 * M := by
    intro t
    obtain ⟨m, hm⟩ :=
      exists_level_superset hmono hcover (t.image Prod.fst ∪ t.image Prod.snd)
    have ht : ∀ p ∈ t, p.1 ∈ (↑(L m) : Set V) ∧ p.2 ∈ (↑(L m) : Set V) := by
      intro p hp
      refine ⟨Finset.mem_coe.2 (hm (Finset.mem_union_left _ ?_)),
        Finset.mem_coe.2 (hm (Finset.mem_union_right _ ?_))⟩
      · exact Finset.mem_image_of_mem _ hp
      · exact Finset.mem_image_of_mem _ hp
    have h1 := sum_gradSq_le_two_restrictedEnergy G g
      (hasFiniteEnergy_restrict_finset G (L m) g) t ht
    have h2 : restrictedEnergy G (↑(L m) : Set V) g ≤ M := hlevel m
    linarith
  refine ⟨summable_of_sum_le hgnonneg hsum, ?_⟩
  have hts := Real.tsum_le_of_sum_le hgnonneg hsum
  rw [G.tsum_gradSq_eq] at hts
  linarith

section Levels

variable {A : Set V} {u : V → ℝ} {L : ℕ → Finset V} {F : ℕ → V → ℝ}

/-! ### The uniform pointwise bound from a bare constant -/

/-- **The level fields are bounded at every vertex, uniformly in the level, from a bare
bound on the level energies.**

This is `FiniteMinimizerPointwiseConvergence.exists_pointwise_uniform_bound` with the
reference energy `G.Energy u` replaced by an arbitrary upper bound `C`.  The original uses
its finite-energy hypothesis `hu` only through `levelEnergy_le_energy`, which is what
supplies such a bound; since a bound is now assumed, neither `hu` nor the minimality
hypothesis `hmin` is needed. -/
theorem exists_pointwise_uniform_bound_of_levelEnergy_le (hA : BoundaryAnchored G A)
    (hmono : Monotone L) (hcover : ∀ x : V, ∃ n, x ∈ L n)
    (htrace : ∀ n, ∀ a ∈ A, a ∈ L n → F n a = u a)
    {C : ℝ} (hEle : ∀ n, restrictedEnergy G (↑(L n) : Set V) (F n) ≤ C) :
    ∃ B : V → ℝ, ∀ (n : ℕ) (x : V), |F n x| ≤ B x := by
  classical
  have key : ∀ x : V, ∃ b : ℝ, ∀ n : ℕ, |F n x| ≤ b := by
    intro x
    obtain ⟨a, haA, hreach⟩ := hA x
    obtain ⟨w⟩ := hreach.symm
    obtain ⟨m, hm⟩ := exists_level_superset hmono hcover w.support.toFinset
    have hwc : 0 ≤ G.walkConst w := G.walkConst_nonneg w
    have htail : ∀ n : ℕ, m ≤ n →
        |F n x| ≤ |u a| + G.walkConst w * Real.sqrt (2 * C) := by
      intro n hn
      have hsupp : ∀ y ∈ w.support, y ∈ (↑(L n) : Set V) := by
        intro y hy
        have hym : y ∈ L m := hm (by simpa using hy)
        exact Finset.mem_coe.2 (hmono hn hym)
      have hbound := abs_sub_le_walkConst_mul_restrictedEnergy G
        (hasFiniteEnergy_restrict_finset G (L n) (F n)) w hsupp
      have haL : a ∈ L n := Finset.mem_coe.1 (hsupp a w.start_mem_support)
      have hFa : F n a = u a := htrace n a haA haL
      have habs : |F n a| = |u a| := by rw [hFa]
      have hsq : Real.sqrt (2 * restrictedEnergy G (↑(L n) : Set V) (F n))
          ≤ Real.sqrt (2 * C) := Real.sqrt_le_sqrt (by linarith [hEle n])
      have hchain : |F n x - F n a| ≤ G.walkConst w * Real.sqrt (2 * C) :=
        hbound.trans (mul_le_mul_of_nonneg_left hsq hwc)
      have hx1 : |F n x| - |F n a| ≤ |F n x - F n a| := abs_sub_abs_le_abs_sub _ _
      linarith
    refine ⟨|u a| + G.walkConst w * Real.sqrt (2 * C)
      + ∑ k ∈ Finset.range m, |F k x|, ?_⟩
    intro n
    have hnn : (0:ℝ) ≤ ∑ k ∈ Finset.range m, |F k x| :=
      Finset.sum_nonneg fun k _ => abs_nonneg _
    rcases le_or_gt m n with hmn | hnm
    · have := htail n hmn
      linarith
    · have hmem : n ∈ Finset.range m := Finset.mem_range.2 hnm
      have hle : |F n x| ≤ ∑ k ∈ Finset.range m, |F k x| :=
        Finset.single_le_sum (f := fun k => |F k x|)
          (fun k _ => abs_nonneg (F k x)) hmem
      have h0 : (0:ℝ) ≤ |u a| + G.walkConst w * Real.sqrt (2 * C) :=
        le_trans (abs_nonneg (F m x)) (htail m le_rfl)
      linarith
  choose B hB using key
  exact ⟨B, fun n x => hB x n⟩

/-! ### A pointwise convergent subsequence from a bare constant -/

/-- **A pointwise convergent subsequence of the level fields.**  As in
`FiniteMinimizerPointwiseConvergence.exists_subseq_tendsto_pointwise`, the uniform bounds
confine the sequence to a product of compact intervals, which is sequentially compact on a
countable vertex type. -/
theorem exists_subseq_tendsto_pointwise_of_levelEnergy_le [Countable V]
    (hA : BoundaryAnchored G A) (hmono : Monotone L) (hcover : ∀ x : V, ∃ n, x ∈ L n)
    (htrace : ∀ n, ∀ a ∈ A, a ∈ L n → F n a = u a)
    {C : ℝ} (hEle : ∀ n, restrictedEnergy G (↑(L n) : Set V) (F n) ≤ C) :
    ∃ (φ : ℕ → ℕ) (g : V → ℝ), StrictMono φ ∧
      ∀ x : V, Tendsto (fun n => F (φ n) x) atTop (𝓝 (g x)) := by
  obtain ⟨B, hB⟩ :=
    exists_pointwise_uniform_bound_of_levelEnergy_le G hA hmono hcover htrace hEle
  have hcompact : IsCompact (Set.pi Set.univ (fun x : V => Set.Icc (-B x) (B x))) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hmemF : ∀ n : ℕ, F n ∈ Set.pi Set.univ (fun x : V => Set.Icc (-B x) (B x)) := by
    intro n x _
    exact abs_le.1 (hB n x)
  obtain ⟨g, -, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hmemF
  exact ⟨φ, g, hφ, fun x => tendsto_pi_nhds.1 hlim x⟩

/-! ### The solvability criterion -/

/-- **A finite-energy field with the prescribed trace, produced from a uniform bound on the
level energies alone.**

No hypothesis is placed on the reference field `u`: it need not have finite energy, and no
full anchored minimizer is assumed to exist.  The level fields need only carry the trace on
`A ∩ L n`; they need not be minimizers. -/
theorem exists_finiteEnergy_trace_of_levelEnergy_le [Countable V] (hA : BoundaryAnchored G A)
    (hmono : Monotone L) (hcover : ∀ x : V, ∃ n, x ∈ L n)
    (htrace : ∀ n, ∀ a ∈ A, a ∈ L n → F n a = u a)
    {C : ℝ} (hEle : ∀ n, restrictedEnergy G (↑(L n) : Set V) (F n) ≤ C) :
    ∃ g : V → ℝ, G.HasFiniteEnergy g ∧ (∀ a ∈ A, g a = u a) ∧ G.Energy g ≤ C := by
  obtain ⟨φ, g, hφ, hg⟩ :=
    exists_subseq_tendsto_pointwise_of_levelEnergy_le G hA hmono hcover htrace hEle
  have hgtrace : ∀ a ∈ A, g a = u a := by
    intro a ha
    obtain ⟨n₀, hn₀⟩ := hcover a
    refine tendsto_nhds_unique (hg a) (Tendsto.congr' ?_ tendsto_const_nhds)
    filter_upwards [eventually_ge_atTop n₀] with n hn
    exact (htrace (φ n) a ha (hmono (hn.trans hφ.le_apply) hn₀)).symm
  have hlevel_g : ∀ m : ℕ, restrictedEnergy G (↑(L m) : Set V) g ≤ C := by
    intro m
    haveI : Fintype (↑(L m) : Set V) := (L m).finite_toSet.fintype
    have hlim : Tendsto (fun n => restrictedEnergy G (↑(L m) : Set V) (F (φ n))) atTop
        (𝓝 (restrictedEnergy G (↑(L m) : Set V) g)) := by
      simp only [restrictedEnergy, ReflectedWalk.ConductanceGraph.Energy, tsum_fintype,
        ReflectedWalk.ConductanceGraph.gradSq]
      refine Tendsto.div_const (tendsto_finset_sum _ fun q _ => ?_) 2
      exact (((hg ((q.2 : V))).sub (hg ((q.1 : V)))).pow 2).const_mul _
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    have h1 : restrictedEnergy G (↑(L m) : Set V) (F (φ n))
        ≤ restrictedEnergy G (↑(L (φ n)) : Set V) (F (φ n)) :=
      restrictedEnergy_mono_of_subset G
        (Finset.coe_subset.2 (hmono (hn.trans hφ.le_apply))) (F (φ n))
        (hasFiniteEnergy_restrict_finset G (L (φ n)) (F (φ n)))
    exact h1.trans (hEle (φ n))
  obtain ⟨hgE, hgle⟩ := hasFiniteEnergy_of_restrictedEnergy_le G hmono hcover g hlevel_g
  exact ⟨g, hgE, hgtrace, hgle⟩

/-- **Solvability of the anchored trace problem is exactly boundedness of the level minimum
energies.**

The forward direction is `levelEnergy_le_energy`: any full competitor bounds every level
minimum.  The reverse direction is `exists_finiteEnergy_trace_of_levelEnergy_le`.  Neither
direction assumes that the reference field `u` has finite energy, and the right-hand side
mentions only the finite-level data. -/
theorem exists_finiteEnergy_trace_iff_bddAbove [Countable V] (hA : BoundaryAnchored G A)
    (hmono : Monotone L) (hcover : ∀ x : V, ∃ n, x ∈ L n)
    (htrace : ∀ n, ∀ a ∈ A, a ∈ L n → F n a = u a)
    (hmin : ∀ n, ∀ w : V → ℝ, (∀ a ∈ A, a ∈ L n → w a = u a) →
      restrictedEnergy G (↑(L n) : Set V) (F n) ≤ restrictedEnergy G (↑(L n) : Set V) w) :
    (∃ g : V → ℝ, G.HasFiniteEnergy g ∧ ∀ a ∈ A, g a = u a)
      ↔ ∃ C : ℝ, ∀ n : ℕ, restrictedEnergy G (↑(L n) : Set V) (F n) ≤ C := by
  constructor
  · rintro ⟨g, hgE, hgtrace⟩
    exact ⟨G.Energy g, fun n => levelEnergy_le_energy G hmin hgE hgtrace n⟩
  · rintro ⟨C, hC⟩
    obtain ⟨g, hgE, hgtrace, -⟩ :=
      exists_finiteEnergy_trace_of_levelEnergy_le G hA hmono hcover htrace hC
    exact ⟨g, hgE, hgtrace⟩

/-- **The same criterion with a natural-number threshold.**  This is the form in which the
right-hand side is a countable union of sublevel conditions on the level energies, and is
what the measurability of the solvability event uses. -/
theorem exists_finiteEnergy_trace_iff_exists_nat [Countable V] (hA : BoundaryAnchored G A)
    (hmono : Monotone L) (hcover : ∀ x : V, ∃ n, x ∈ L n)
    (htrace : ∀ n, ∀ a ∈ A, a ∈ L n → F n a = u a)
    (hmin : ∀ n, ∀ w : V → ℝ, (∀ a ∈ A, a ∈ L n → w a = u a) →
      restrictedEnergy G (↑(L n) : Set V) (F n) ≤ restrictedEnergy G (↑(L n) : Set V) w) :
    (∃ g : V → ℝ, G.HasFiniteEnergy g ∧ ∀ a ∈ A, g a = u a)
      ↔ ∃ k : ℕ, ∀ n : ℕ, restrictedEnergy G (↑(L n) : Set V) (F n) ≤ (k : ℝ) := by
  rw [exists_finiteEnergy_trace_iff_bddAbove G hA hmono hcover htrace hmin]
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨k, hk⟩ := exists_nat_ge C
    exact ⟨k, fun n => (hC n).trans hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨(k : ℝ), hk⟩

end Levels

end BoundedLevelEnergySolvability

end ReflectedGMS
