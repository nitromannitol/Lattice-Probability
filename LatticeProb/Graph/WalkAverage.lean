/-
The finite-horizon walk average is the integral against the law of the walk.

`walkExp G n x F` is the expectation of `F` written as the first-step average of
the walk, iterated `n` times.  It is a finite average over the trajectories of
length `n` and needs no measure, which is what lets the representation theorem
be proved by a plain induction.  On the lattice the same expectation is an
integral against the law of the whole trajectory, and the two agree for every
functional settled by the positions up to time `n`.

The induction is the Markov property at time one.  The only work is the
boundedness the Markov lemma asks for: `F` need not be bounded on all of path
space, but `walkExp` reads it only on the nearest-neighbour paths started at
`x`, and the walk stays on those almost surely.  Those paths lie in the box of
radius `n` about `x` up to time `n`, so `F` restricted to them takes finitely
many values; replacing `F` by the functional that agrees with it there and
vanishes elsewhere changes neither side and is bounded.
-/
import LatticeProb.Graph.Zd
import LatticeProb.Graph.WalkLemmas
import LatticeProb.Walk.Markov
import LatticeProb.ParticleHoleLemmas

open MeasureTheory

noncomputable section

namespace LatticeProb.Graph

/-! ### `walkExp` reads only the nearest-neighbour paths -/

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

theorem walkExp_congr_adj {n : ℕ} {x : V} {F F' : (ℕ → V) → ℝ}
    (h : ∀ X : ℕ → V, X 0 = x → (∀ k < n, G.Adj (X k) (X (k + 1))) → F X = F' X) :
    walkExp G n x F = walkExp G n x F' := by
  induction n generalizing x F F' with
  | zero => exact h _ rfl (fun k hk => absurd hk (by omega))
  | succ n ih =>
      rw [walkExp_succ, walkExp_succ]
      congr 1
      refine Finset.sum_congr rfl fun y hy => ?_
      have hxy : G.Adj x y := (SimpleGraph.mem_neighborFinset G x y).mp hy
      refine ih fun X hX0 hXadj => ?_
      refine h (cons x X) rfl fun k hk => ?_
      cases k with
      | zero => simpa [cons, hX0] using hxy
      | succ k => exact hXadj k (by omega)

end LatticeProb.Graph

namespace LatticeProb

open LatticeProb.Graph

variable {d : ℕ}

/-! ### What the walk does almost surely -/

/-- A property that every path of the form `sitePath x ξ` has holds almost
surely. -/
theorem ae_siteWalkLaw [NeZero d] (x : Site d) {p : (ℕ → Site d) → Prop}
    (hp : MeasurableSet {X | p X}) (h : ∀ ξ, p (sitePath x ξ)) :
    ∀ᵐ X ∂(siteWalkLaw d x), p X := by
  have hc : MeasurableSet {a : ℕ → Site d | ¬ p a} := hp.compl
  rw [ae_iff, siteWalkLaw, Measure.map_apply (measurable_sitePath x) hc]
  have he : (sitePath x) ⁻¹' {a | ¬ p a} = ∅ := by
    ext ξ
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact h ξ
  rw [he, measure_empty]

/-- The set of unit steps. -/
def unitSteps (d : ℕ) : Set (Site d) := Set.range (dirVec : Dir d → Site d)

theorem measurableSet_unitSteps (d : ℕ) : MeasurableSet (unitSteps d) :=
  (Set.finite_range _).countable.measurableSet

theorem incLaw_compl_unitSteps [NeZero d] : incLaw d (unitSteps d)ᶜ = 0 := by
  rw [incLaw, instructionLaw, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  have hterm : ∀ i : Fin d,
      (Measure.dirac ((0 : Site d) + unit i) + Measure.dirac ((0 : Site d) - unit i))
        (unitSteps d)ᶜ = 0 := by
    intro i
    have h1 : ((0 : Site d) + unit i) ∈ unitSteps d := ⟨(i, true), by
      simp [dirVec_eq_unit]⟩
    have h2 : ((0 : Site d) - unit i) ∈ unitSteps d := ⟨(i, false), by
      simp [dirVec_eq_neg_unit, sub_eq_add_neg]⟩
    rw [Measure.coe_add, Pi.add_apply,
      Measure.dirac_apply' _ (measurableSet_unitSteps d).compl,
      Measure.dirac_apply' _ (measurableSet_unitSteps d).compl,
      Set.indicator_of_notMem (by simpa using h1),
      Set.indicator_of_notMem (by simpa using h2), add_zero]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  simp

theorem ae_unitSteps [NeZero d] :
    ∀ᵐ ξ ∂(incPathLaw d), ∀ k : ℕ, ξ k ∈ unitSteps d := by
  rw [ae_all_iff]
  intro k
  rw [ae_iff]
  have hpre : {ξ : ℕ → Site d | ¬ ξ k ∈ unitSteps d} = (fun ξ : ℕ → Site d => ξ k) ⁻¹'
      (unitSteps d)ᶜ := rfl
  rw [hpre, ← Measure.map_apply (measurable_pi_apply k) (measurableSet_unitSteps d).compl,
    incPathLaw, Measure.infinitePi_map_eval]
  exact incLaw_compl_unitSteps

/-- Almost surely the walk is a nearest-neighbour path started at `x`. -/
theorem ae_adj_siteWalkLaw [NeZero d] (x : Site d) :
    ∀ᵐ X ∂(siteWalkLaw d x), X 0 = x ∧ ∀ k : ℕ, (lattice d).Adj (X k) (X (k + 1)) := by
  have hPm : MeasurableSet {X : ℕ → Site d |
      X 0 = x ∧ ∀ k : ℕ, (lattice d).Adj (X k) (X (k + 1))} := by
    have h0 : MeasurableSet {X : ℕ → Site d | X 0 = x} := by
      have he : {X : ℕ → Site d | X 0 = x} = (fun X : ℕ → Site d => X 0) ⁻¹' {x} := rfl
      rw [he]
      exact (measurable_pi_apply 0) (MeasurableSet.singleton x)
    have hk : ∀ k : ℕ, MeasurableSet {X : ℕ → Site d | (lattice d).Adj (X k) (X (k + 1))} := by
      intro k
      have he : {X : ℕ → Site d | (lattice d).Adj (X k) (X (k + 1))}
          = (fun X : ℕ → Site d => (X k, X (k + 1))) ⁻¹'
            {q : Site d × Site d | (lattice d).Adj q.1 q.2} := rfl
      rw [he]
      exact ((measurable_pi_apply k).prodMk (measurable_pi_apply (k + 1)))
        (Set.Countable.measurableSet (Set.to_countable _))
    have : {X : ℕ → Site d | X 0 = x ∧ ∀ k : ℕ, (lattice d).Adj (X k) (X (k + 1))}
        = {X : ℕ → Site d | X 0 = x} ∩ ⋂ k : ℕ,
            {X : ℕ → Site d | (lattice d).Adj (X k) (X (k + 1))} := by
      ext X; simp [Set.mem_iInter]
    rw [this]
    exact h0.inter (MeasurableSet.iInter hk)
  rw [siteWalkLaw, ae_map_iff (measurable_sitePath x).aemeasurable hPm]
  filter_upwards [ae_unitSteps (d := d)] with ξ hξ
  refine ⟨sitePath_zero x ξ, fun k => ?_⟩
  obtain ⟨a, ha⟩ := hξ k
  have hstep : sitePath x ξ (k + 1) = sitePath x ξ k + ξ k := by
    simp only [sitePath, Finset.sum_range_succ]
    abel
  rcases a with ⟨i, b⟩
  cases b
  · refine ⟨i, Or.inr ?_⟩
    rw [hstep, ← ha, dirVec_eq_neg_unit]
    abel
  · refine ⟨i, Or.inl ?_⟩
    rw [hstep, ← ha, dirVec_eq_unit]

/-! ### The identity, for a bounded functional -/

/-- For a bounded functional settled by the positions up to time `n`, the
finite-horizon walk average is the integral against the law of the walk. -/
theorem walkExp_eq_integral_of_bounded [NeZero d] :
    ∀ (n : ℕ) (x : Site d) (F : (ℕ → Site d) → ℝ), DependsUpTo n F →
      ∀ {C : ℝ}, (∀ X, ‖F X‖ ≤ C) →
      LatticeProb.Graph.walkExp (lattice d) n x F = ∫ X, F X ∂(siteWalkLaw d x) := by
  intro n
  induction n with
  | zero =>
      intro x F hF C hFb
      have h1 : ∫ X, F X ∂(siteWalkLaw d x)
          = ∫ _X : ℕ → Site d, F (fun _ => x) ∂(siteWalkLaw d x) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_adj_siteWalkLaw x] with X hX
        exact hF X (fun _ => x) fun k hk => by rw [Nat.le_zero.mp hk, hX.1]
      rw [h1, integral_const]
      simp [LatticeProb.Graph.walkExp]
  | succ n ih =>
      intro x F hF C hFb
      set Fc : (ℕ → Site d) → ℝ := fun Y => F (LatticeProb.Graph.cons x Y) with hFc
      have hFcdep : DependsUpTo n Fc := by
        intro Y Y' hYY'
        refine hF (LatticeProb.Graph.cons x Y) (LatticeProb.Graph.cons x Y') fun k hk => ?_
        cases k with
        | zero => rfl
        | succ k => exact hYY' k (by omega)
      have hFcb : ∀ Y, ‖Fc Y‖ ≤ C := fun Y => hFb _
      have hL : LatticeProb.Graph.walkExp (lattice d) (n + 1) x F
          = LatticeProb.walkOp (fun y => LatticeProb.Graph.walkExp (lattice d) n y Fc) x := by
        rw [LatticeProb.Graph.walkExp_succ, ← LatticeProb.Graph.Zd.walkOp_eq,
          LatticeProb.Graph.walkOp]
      have hR : ∫ X, F X ∂(siteWalkLaw d x)
          = ∫ X, Fc (shiftPath 1 X) ∂(siteWalkLaw d x) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_adj_siteWalkLaw x] with X hX
        have hcons : LatticeProb.Graph.cons x (shiftPath 1 X) = X := by
          funext k
          cases k with
          | zero => exact hX.1.symm
          | succ k =>
              show X (1 + k) = X (k + 1)
              congr 1
              omega
        rw [hFc]
        simp only
        rw [hcons]
      rw [hL, hR, integral_comp_shiftPath d 1 x Fc (measurable_of_dependsUpTo hFcdep) hFcb,
        Function.iterate_one]
      congr 1
      funext y
      show LatticeProb.Graph.walkExp (lattice d) n y Fc = pathExpect d Fc y
      rw [pathExpect]
      exact ih y Fc hFcdep hFcb

/-! ### The identity, unconditional -/

open scoped Classical in
/-- The truncation of `F` to the nearest-neighbour paths started at `x`. -/
noncomputable def onAdjPaths (n : ℕ) (x : Site d) (F : (ℕ → Site d) → ℝ) :
    (ℕ → Site d) → ℝ :=
  fun X => if X 0 = x ∧ ∀ k < n, (lattice d).Adj (X k) (X (k + 1)) then F X else 0

/-- A nearest-neighbour path started at `x` stays in the box of radius `n` about
`x` up to time `n`. -/
theorem mem_boxFinset_of_adj {n : ℕ} {x : Site d} {X : ℕ → Site d} (h0 : X 0 = x)
    (hadj : ∀ k < n, (lattice d).Adj (X k) (X (k + 1))) {k : ℕ} (hk : k ≤ n) :
    X k ∈ boxFinset x n := by
  refine mem_boxFinset_iff.mpr fun i => ?_
  have key : ∀ m : ℕ, m ≤ n → |X m i - x i| ≤ (m : ℤ) := by
    intro m
    induction m with
    | zero => intro _; rw [h0]; simp
    | succ m ihm =>
        intro hm
        have hstep : |X (m + 1) i - X m i| ≤ 1 := by
          obtain ⟨j, hj⟩ := hadj m (by omega)
          rcases hj with hj | hj
          · rw [hj]
            by_cases hij : i = j <;> simp [unit, hij]
          · rw [hj]
            by_cases hij : i = j <;> simp [unit, hij]
        have hprev := ihm (by omega)
        have htri : |X (m + 1) i - x i| ≤ |X (m + 1) i - X m i| + |X m i - x i| := by
          have : X (m + 1) i - x i = (X (m + 1) i - X m i) + (X m i - x i) := by ring
          rw [this]; exact abs_add_le _ _
        push_cast
        linarith
  exact le_trans (key k hk) (by exact_mod_cast hk)

/-- The canonical extension of a prefix of length `n + 1`. -/
def prefixExt (n : ℕ) (a : Fin (n + 1) → Site d) : ℕ → Site d :=
  fun k => if h : k < n + 1 then a ⟨k, h⟩ else a ⟨n, Nat.lt_succ_self n⟩

theorem prefixExt_apply {n : ℕ} (a : Fin (n + 1) → Site d) {k : ℕ} (hk : k ≤ n) :
    prefixExt n a k = a ⟨k, by omega⟩ := by
  rw [prefixExt, dif_pos (by omega : k < n + 1)]

/-- **The identity, unconditional.**  For a functional settled by the positions
up to time `n`, the finite-horizon walk average is the integral against the law
of the walk.  No boundedness is needed: the walk stays on the nearest-neighbour
paths started at `x`, which lie in a box up to time `n`, so the functional takes
finitely many values there. -/
theorem walkExp_eq_integral [NeZero d] (n : ℕ) (x : Site d) (F : (ℕ → Site d) → ℝ)
    (hF : ∀ X Y : ℕ → Site d, (∀ j ≤ n, X j = Y j) → F X = F Y) :
    LatticeProb.Graph.walkExp (lattice d) n x F = ∫ X, F X ∂(siteWalkLaw d x) := by
  classical
  have hxB : x ∈ boxFinset x n := mem_boxFinset_iff.mpr fun i => by simp
  haveI : Nonempty {y // y ∈ boxFinset x n} := ⟨⟨x, hxB⟩⟩
  set M : ℝ := Finset.univ.sup' Finset.univ_nonempty
    (fun a : Fin (n + 1) → {y // y ∈ boxFinset x n} =>
      |F (prefixExt n fun i => (a i : Site d))|) with hM
  set Fb : (ℕ → Site d) → ℝ := onAdjPaths n x F with hFb
  have hcond : ∀ X : ℕ → Site d,
      (X 0 = x ∧ ∀ k < n, (lattice d).Adj (X k) (X (k + 1))) → Fb X = F X := by
    intro X hX
    rw [hFb, onAdjPaths, if_pos hX]
  have hnot : ∀ X : ℕ → Site d,
      ¬ (X 0 = x ∧ ∀ k < n, (lattice d).Adj (X k) (X (k + 1))) → Fb X = 0 := by
    intro X hX
    rw [hFb, onAdjPaths, if_neg hX]
  have hMnn : 0 ≤ M := by
    have h := Finset.le_sup'
      (f := fun a : Fin (n + 1) → {y // y ∈ boxFinset x n} =>
        |F (prefixExt n fun i => (a i : Site d))|)
      (Finset.mem_univ (fun _ : Fin (n + 1) => (⟨x, hxB⟩ : {y // y ∈ boxFinset x n})))
    exact le_trans (abs_nonneg _) h
  have hFbb : ∀ X, ‖Fb X‖ ≤ M := by
    intro X
    by_cases hX : X 0 = x ∧ ∀ k < n, (lattice d).Adj (X k) (X (k + 1))
    · rw [hcond X hX, Real.norm_eq_abs]
      have hmem : ∀ i : Fin (n + 1), X (i : ℕ) ∈ boxFinset x n := fun i =>
        mem_boxFinset_of_adj hX.1 hX.2 (by omega : (i : ℕ) ≤ n)
      have hFX : F X = F (prefixExt n fun i => ((⟨X (i : ℕ), hmem i⟩ :
          {y // y ∈ boxFinset x n}) : Site d)) := by
        refine hF X _ fun j hj => ?_
        rw [prefixExt_apply _ hj]
      rw [hFX]
      exact Finset.le_sup'
        (f := fun a : Fin (n + 1) → {y // y ∈ boxFinset x n} =>
          |F (prefixExt n fun i => (a i : Site d))|)
        (Finset.mem_univ (fun i : Fin (n + 1) =>
          (⟨X (i : ℕ), hmem i⟩ : {y // y ∈ boxFinset x n})))
    · rw [hnot X hX, norm_zero]
      exact hMnn
  have hFbdep : DependsUpTo n Fb := by
    intro X Y hXY
    have hiff : (X 0 = x ∧ ∀ k < n, (lattice d).Adj (X k) (X (k + 1)))
        ↔ (Y 0 = x ∧ ∀ k < n, (lattice d).Adj (Y k) (Y (k + 1))) := by
      constructor
      · rintro ⟨h0, hadj⟩
        exact ⟨(hXY 0 (by omega)) ▸ h0, fun k hk => by
          rw [← hXY k (by omega), ← hXY (k + 1) (by omega)]; exact hadj k hk⟩
      · rintro ⟨h0, hadj⟩
        exact ⟨(hXY 0 (by omega)).symm ▸ h0, fun k hk => by
          rw [hXY k (by omega), hXY (k + 1) (by omega)]; exact hadj k hk⟩
    by_cases hX : X 0 = x ∧ ∀ k < n, (lattice d).Adj (X k) (X (k + 1))
    · rw [hcond X hX, hcond Y (hiff.mp hX)]
      exact hF X Y hXY
    · rw [hnot X hX, hnot Y (fun hc => hX (hiff.mpr hc))]
  have hLHS : LatticeProb.Graph.walkExp (lattice d) n x F
      = LatticeProb.Graph.walkExp (lattice d) n x Fb :=
    LatticeProb.Graph.walkExp_congr_adj fun X h0 hadj => (hcond X ⟨h0, hadj⟩).symm
  have hRHS : ∫ X, F X ∂(siteWalkLaw d x) = ∫ X, Fb X ∂(siteWalkLaw d x) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_adj_siteWalkLaw x] with X hX
    exact (hcond X ⟨hX.1, fun k _ => hX.2 k⟩).symm
  rw [hLHS, hRHS]
  exact walkExp_eq_integral_of_bounded n x Fb hFbdep hFbb

end LatticeProb

/-- For a functional of the trajectory settled by the positions up to time `n`,
the finite-horizon walk average is the integral against the law of the walk. -/
def LatticeProb.Graph.WalkAverageIsIntegral : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (n : ℕ) (x : LatticeProb.Site d)
    (F : (ℕ → LatticeProb.Site d) → ℝ),
    (∀ X Y : ℕ → LatticeProb.Site d, (∀ j ≤ n, X j = Y j) → F X = F Y) →
    LatticeProb.Graph.walkExp (LatticeProb.lattice d) n x F
      = ∫ X, F X ∂(LatticeProb.siteWalkLaw d x)

/-- The identity holds; it is no longer an assumption. -/
theorem LatticeProb.Graph.walkAverageIsIntegral :
    LatticeProb.Graph.WalkAverageIsIntegral := by
  intro d hd n x F hF
  haveI : NeZero d := ⟨by omega⟩
  exact LatticeProb.walkExp_eq_integral n x F hF

end
