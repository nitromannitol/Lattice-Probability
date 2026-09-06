/-
The Markov property of simple random walk on the lattice, at a fixed time and at
a bounded stopping time.

The walk is built the way the papers build it: the increments are independent
and uniform on the `2d` unit vectors, and `sitePath x` accumulates them from `x`,
so `siteWalkLaw d x` is a measure on the space `ℕ → Site d` of position paths.
A stopping time is a function of the path whose value at `k` is settled by the
positions up to time `k`, which is `IsWalkStopping`.

Everything rests on one splitting lemma in the increment space.  Write
`truncInc n` for the increments before time `n`, padded with zeros, and
`shiftInc n` for the increments from time `n` on.  Under the product measure the
two are independent, and `shiftInc n` preserves the measure, so the joint law of
the pair is the product of the law of the first and the measure itself; Fubini
then says that an integral of a function of the pair may be computed by
integrating the second argument out against a fresh copy of the measure.  That
is `integral_truncInc_shiftInc`, and it is the only place where measure theory
happens.

The rest is bookkeeping.  Shifting a path by `n` gives the path started at its
own position at time `n` and driven by the shifted increments, so the fixed-time
Markov property follows at once.  A bounded stopping time takes finitely many
values, and on the event that it takes the value `k` the shift is the shift by
`k` and the conditioning data is settled by the first `k` positions, so summing
the fixed-time statement over `k` gives the strong Markov property.
-/
import LatticeProb.IID
import LatticeProb.Walk.Infinite
import LatticeProb.Prob.ZeroOne

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

variable {d : ℕ}

/-! ### The law of one increment -/

/-- The law of one increment of simple random walk: uniform on the `2d` unit
vectors.  This is `LatticeProb.instructionLaw` at the origin, the measure the
instruction stacks of `LatticeProb.IID` are built from. -/
noncomputable def incLaw (d : ℕ) : Measure (Site d) := instructionLaw (0 : Site d)

theorem incLaw_univ (hd : 0 < d) : incLaw d Set.univ = 1 := by
  have hd0 : (d : ENNReal) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hdtop : (d : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top d
  rw [incLaw, instructionLaw]
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  have hterm : ∀ i : Fin d,
      (Measure.dirac ((0 : Site d) + unit i) + Measure.dirac ((0 : Site d) - unit i))
        Set.univ = 2 := by
    intro i
    rw [Measure.coe_add, Pi.add_apply, Measure.dirac_apply' _ MeasurableSet.univ,
      Measure.dirac_apply' _ MeasurableSet.univ]
    simp
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
  rw [mul_comm (d : ENNReal) 2,
    ENNReal.inv_mul_cancel (by simp [hd0]) (by finiteness)]

instance incLaw_isProbabilityMeasure (d : ℕ) [NeZero d] :
    IsProbabilityMeasure (incLaw d) :=
  ⟨incLaw_univ (Nat.pos_of_ne_zero (NeZero.ne d))⟩

/-- The law of the increment sequence. -/
noncomputable def incPathLaw (d : ℕ) [NeZero d] : Measure (ℕ → Site d) :=
  Measure.infinitePi fun _ : ℕ => incLaw d

instance incPathLaw_isProbabilityMeasure (d : ℕ) [NeZero d] :
    IsProbabilityMeasure (incPathLaw d) := by
  unfold incPathLaw; infer_instance

/-! ### Splitting the increments at time `n` -/

/-- The increments before time `n`, padded with zeros. -/
def truncInc (n : ℕ) (ξ : ℕ → Site d) : ℕ → Site d := fun i => if i < n then ξ i else 0

/-- The increments from time `n` on. -/
def shiftInc (n : ℕ) (ξ : ℕ → Site d) : ℕ → Site d := fun k => ξ (n + k)

theorem measurable_truncInc (n : ℕ) : Measurable (truncInc (d := d) n) :=
  measurable_pi_lambda _ fun i => by
    by_cases h : i < n
    · simpa only [truncInc, if_pos h] using measurable_pi_apply i
    · simpa only [truncInc, if_neg h] using
        (measurable_const : Measurable fun _ : ℕ → Site d => (0 : Site d))

theorem measurable_shiftInc (n : ℕ) : Measurable (shiftInc (d := d) n) :=
  measurable_pi_lambda _ fun k => measurable_pi_apply (n + k)

theorem shiftInc_eq_coordShift (n : ℕ) :
    shiftInc (d := d) n = coordShift fun k : ℕ => n + k := rfl

/-- The shift of the increments preserves their law. -/
theorem measurePreserving_shiftInc (d n : ℕ) [NeZero d] :
    MeasurePreserving (shiftInc (d := d) n) (incPathLaw d) (incPathLaw d) := by
  rw [shiftInc_eq_coordShift, incPathLaw]
  exact measurePreserving_coordShift _ (add_right_injective n) fun _ => rfl

/-- A map into path space is measurable for a sigma algebra as soon as each of
its coordinates is. -/
theorem comap_le_of_coordinates {α : Type*} {m : MeasurableSpace α}
    (f : α → (ℕ → Site d))
    (h : ∀ j : ℕ, MeasurableSpace.comap (fun a => f a j) inferInstance ≤ m) :
    MeasurableSpace.comap f inferInstance ≤ m := by
  rw [show (inferInstance : MeasurableSpace (ℕ → Site d))
      = ⨆ j : ℕ, MeasurableSpace.comap (fun ξ : ℕ → Site d => ξ j) inferInstance from rfl,
    MeasurableSpace.comap_iSup]
  refine iSup_le fun j => ?_
  rw [MeasurableSpace.comap_comp]
  exact h j

/-- The increments before time `n` and the increments from time `n` on are
independent. -/
theorem indepFun_truncInc_shiftInc (d n : ℕ) [NeZero d] :
    IndepFun (truncInc (d := d) n) (shiftInc (d := d) n) (incPathLaw d) := by
  classical
  set S : Set ℕ := {i : ℕ | i < n} with hS
  set s : ℕ → MeasurableSpace (ℕ → Site d) := fun i =>
    MeasurableSpace.comap (fun ξ : ℕ → Site d => ξ i) inferInstance with hs
  have hcoord : iIndepFun (fun (i : ℕ) (ξ : ℕ → Site d) => ξ i) (incPathLaw d) := by
    rw [incPathLaw]
    exact iIndepFun_infinitePi (X := fun _ a => a) fun _ => measurable_id
  have hind : iIndep s (incPathLaw d) := (iIndepFun_iff_iIndep _ _ _).mp hcoord
  have hle : ∀ i : ℕ, s i ≤ (inferInstance : MeasurableSpace (ℕ → Site d)) := fun i =>
    (measurable_pi_apply i).comap_le
  have hsplit := indep_biSup_compl hle hind S
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le hsplit ?_ ?_
  · refine comap_le_of_coordinates _ fun j => ?_
    by_cases hj : j < n
    · have he : (fun ξ : ℕ → Site d => truncInc n ξ j) = fun ξ => ξ j := by
        funext ξ; simp only [truncInc, if_pos hj]
      rw [he]
      exact le_biSup s (show j ∈ S from hj)
    · have he : (fun ξ : ℕ → Site d => truncInc n ξ j) = fun _ => (0 : Site d) := by
        funext ξ; simp only [truncInc, if_neg hj]
      rw [he, MeasurableSpace.comap_const]
      exact bot_le
  · refine comap_le_of_coordinates _ fun k => ?_
    exact le_biSup s (show n + k ∈ Sᶜ by simp [hS])

/-- **The splitting lemma.**  An integral of a function of the increments before
time `n` and the increments from time `n` on may be computed by integrating the
second argument out against a fresh copy of the law. -/
theorem integral_truncInc_shiftInc (d n : ℕ) [NeZero d]
    (Φ : (ℕ → Site d) → (ℕ → Site d) → ℝ) (hΦ : Measurable (Function.uncurry Φ))
    {C : ℝ} (hC : ∀ a b, ‖Φ a b‖ ≤ C) :
    ∫ ξ, Φ (truncInc n ξ) (shiftInc n ξ) ∂(incPathLaw d)
      = ∫ ξ, (∫ η, Φ (truncInc n ξ) η ∂(incPathLaw d)) ∂(incPathLaw d) := by
  set μ := incPathLaw d with hμ
  have hmeas : Measurable fun ξ : ℕ → Site d => (truncInc n ξ, shiftInc n ξ) :=
    (measurable_truncInc n).prodMk (measurable_shiftInc n)
  have hpair : Measure.map (fun ξ => (truncInc (d := d) n ξ, shiftInc (d := d) n ξ)) μ
      = (Measure.map (truncInc (d := d) n) μ).prod (Measure.map (shiftInc (d := d) n) μ) :=
    (indepFun_iff_map_prod_eq_prod_map_map (measurable_truncInc n).aemeasurable
      (measurable_shiftInc n).aemeasurable).mp (indepFun_truncInc_shiftInc d n)
  have hshift : Measure.map (shiftInc (d := d) n) μ = μ :=
    (measurePreserving_shiftInc d n).map_eq
  have hprodmeas : IsProbabilityMeasure (Measure.map (truncInc (d := d) n) μ) :=
    Measure.isProbabilityMeasure_map (measurable_truncInc n).aemeasurable
  have hint : Integrable (Function.uncurry Φ)
      ((Measure.map (truncInc (d := d) n) μ).prod μ) :=
    Integrable.of_bound hΦ.aestronglyMeasurable C (Filter.Eventually.of_forall fun p => hC p.1 p.2)
  have h1 : ∫ ξ, Φ (truncInc n ξ) (shiftInc n ξ) ∂μ
      = ∫ p, Function.uncurry Φ p
          ∂(Measure.map (fun ξ => (truncInc (d := d) n ξ, shiftInc (d := d) n ξ)) μ) := by
    rw [integral_map hmeas.aemeasurable hΦ.aestronglyMeasurable]
    rfl
  rw [h1, hpair, hshift, integral_prod _ hint,
    integral_map (measurable_truncInc n).aemeasurable
      (hΦ.stronglyMeasurable.integral_prod_right').aestronglyMeasurable]
  rfl

/-! ### The walk on position paths -/

/-- The path started at `x` with increments `ξ`. -/
def sitePath (x : Site d) (ξ : ℕ → Site d) (k : ℕ) : Site d :=
  x + ∑ j ∈ Finset.range k, ξ j

/-- The law of simple random walk started at `x`, as a measure on the space of
position paths. -/
noncomputable def siteWalkLaw (d : ℕ) (x : Site d) : Measure (ℕ → Site d) :=
  (Measure.infinitePi fun _ : ℕ => incLaw d).map (sitePath x)

/-- The path shifted by `n`. -/
def shiftPath (n : ℕ) (X : ℕ → Site d) : ℕ → Site d := fun k => X (n + k)

theorem measurable_sitePath (x : Site d) : Measurable (sitePath x) :=
  measurable_pi_lambda _ fun _ => by
    refine Measurable.const_add ?_ x
    exact Finset.measurable_sum _ fun j _ => measurable_pi_apply j

theorem measurable_sitePath_uncurry :
    Measurable fun p : Site d × (ℕ → Site d) => sitePath p.1 p.2 :=
  measurable_pi_lambda _ fun _ =>
    (measurable_fst).add (Finset.measurable_sum _ fun _ _ => measurable_snd.eval)

theorem measurable_shiftPath (n : ℕ) : Measurable (shiftPath (d := d) n) :=
  measurable_pi_lambda _ fun k => measurable_pi_apply (n + k)

instance siteWalkLaw_isProbabilityMeasure (d : ℕ) [NeZero d] (x : Site d) :
    IsProbabilityMeasure (siteWalkLaw d x) := by
  rw [siteWalkLaw]
  exact Measure.isProbabilityMeasure_map (measurable_sitePath x).aemeasurable

theorem siteWalkLaw_eq (d : ℕ) [NeZero d] (x : Site d) :
    siteWalkLaw d x = (incPathLaw d).map (sitePath x) := rfl

theorem sitePath_zero (x : Site d) (ξ : ℕ → Site d) : sitePath x ξ 0 = x := by
  simp [sitePath]

/-- Shifting a path by `n` gives the path started at its own position at time
`n` and driven by the shifted increments. -/
theorem shiftPath_sitePath (n : ℕ) (x : Site d) (ξ : ℕ → Site d) :
    shiftPath n (sitePath x ξ) = sitePath (sitePath x ξ n) (shiftInc n ξ) := by
  funext k
  simp only [shiftPath, sitePath, shiftInc]
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_range_add]

/-- Up to time `n` the path is driven by the increments before time `n`. -/
theorem sitePath_truncInc {n k : ℕ} (hk : k ≤ n) (x : Site d) (ξ : ℕ → Site d) :
    sitePath x (truncInc n ξ) k = sitePath x ξ k := by
  simp only [sitePath]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [truncInc, if_pos (lt_of_lt_of_le (Finset.mem_range.mp hj) hk)]

/-! ### Stopping times and the conditioning data -/

/-- `τ` is a stopping time of the walk: whether it takes the value `k` is
settled by the positions up to time `k`.  This is the form the papers use. -/
def IsWalkStopping (τ : (ℕ → Site d) → ℕ) : Prop :=
  ∀ (k : ℕ) (X Y : ℕ → Site d), (∀ j ≤ k, X j = Y j) → τ X = k → τ Y = k

/-- `f` is settled by the positions up to time `n`, that is, it is measurable for
the `n`-th sigma algebra of the coordinate filtration. -/
def DependsUpTo {α : Type*} (n : ℕ) (f : (ℕ → Site d) → α) : Prop :=
  ∀ X Y : ℕ → Site d, (∀ k ≤ n, X k = Y k) → f X = f Y

/-- A function settled by finitely many positions is measurable: the positions
form a countable set, so a function of finitely many of them factors through a
countable space. -/
theorem measurable_of_dependsUpTo {α : Type*} [MeasurableSpace α] {n : ℕ}
    {f : (ℕ → Site d) → α} (hf : DependsUpTo n f) : Measurable f := by
  classical
  set r : (ℕ → Site d) → (Fin (n + 1) → Site d) := fun X i => X i with hr
  set g : (Fin (n + 1) → Site d) → α :=
    fun a => f fun k => if h : k < n + 1 then a ⟨k, h⟩ else 0 with hg
  have hfact : f = g ∘ r := by
    funext X
    refine (hf X _ fun k hk => ?_).symm ▸ rfl
    rw [dif_pos (by omega : k < n + 1)]
  rw [hfact]
  exact (measurable_of_countable g).comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)

/-- A bounded stopping time is settled by the positions up to its bound. -/
theorem dependsUpTo_of_isWalkStopping {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ)
    {N : ℕ} (hτN : ∀ X, τ X ≤ N) : DependsUpTo N τ := by
  intro X Y hXY
  exact (hτ (τ X) X Y (fun j hj => hXY j (le_trans hj (hτN X))) rfl).symm

theorem measurable_isWalkStopping {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ)
    {N : ℕ} (hτN : ∀ X, τ X ≤ N) : Measurable τ :=
  measurable_of_dependsUpTo (dependsUpTo_of_isWalkStopping hτ hτN)

/-! ### The Markov property at a fixed time -/

/-- The expectation of a bounded measurable function of the path, as a function
of the starting site. -/
noncomputable def pathExpect (d : ℕ) (F : (ℕ → Site d) → ℝ) (y : Site d) : ℝ :=
  ∫ Y, F Y ∂(siteWalkLaw d y)

theorem measurable_pathExpect (d : ℕ) (F : (ℕ → Site d) → ℝ) :
    Measurable (pathExpect d F) := measurable_of_countable _

/-- **The Markov property at a fixed time.**  For a bounded measurable `F` on
paths and a bounded `H` settled by the positions up to time `n`,
`E_x[F(θ_n X) H(X)] = E_x[E_{X_n}[F] H(X)]`. -/
theorem markov_fixed (d : ℕ) [NeZero d] (n : ℕ) (x : Site d)
    (F : (ℕ → Site d) → ℝ) (hFm : Measurable F) {CF : ℝ} (hFb : ∀ X, ‖F X‖ ≤ CF)
    (H : (ℕ → Site d) → ℝ) {CH : ℝ} (hHb : ∀ X, ‖H X‖ ≤ CH) (hH : DependsUpTo n H) :
    ∫ X, F (shiftPath n X) * H X ∂(siteWalkLaw d x)
      = ∫ X, pathExpect d F (X n) * H X ∂(siteWalkLaw d x) := by
  classical
  have hHm : Measurable H := measurable_of_dependsUpTo hH
  set μ : Measure (ℕ → Site d) := incPathLaw d with hμ
  set Φ : (ℕ → Site d) → (ℕ → Site d) → ℝ :=
    fun a b => F (sitePath (sitePath x a n) b) * H (sitePath x a) with hΦdef
  have hCF : 0 ≤ CF := le_trans (norm_nonneg _) (hFb fun _ => 0)
  have hCH : 0 ≤ CH := le_trans (norm_nonneg _) (hHb fun _ => 0)
  have hΦm : Measurable (Function.uncurry Φ) := by
    refine Measurable.mul ?_ ?_
    · exact hFm.comp (measurable_sitePath_uncurry.comp
        (((measurable_pi_apply n).comp ((measurable_sitePath x).comp measurable_fst)).prodMk
          measurable_snd))
    · exact hHm.comp ((measurable_sitePath x).comp measurable_fst)
  have hΦb : ∀ a b, ‖Φ a b‖ ≤ CF * CH := by
    intro a b
    rw [hΦdef, norm_mul]
    exact mul_le_mul (hFb _) (hHb _) (norm_nonneg _) hCF
  -- the integrand, pulled back to the increments, is a function of the two halves
  have hkey : ∀ ξ : ℕ → Site d,
      F (shiftPath n (sitePath x ξ)) * H (sitePath x ξ)
        = Φ (truncInc n ξ) (shiftInc n ξ) := by
    intro ξ
    have h1 : sitePath x (truncInc n ξ) n = sitePath x ξ n := sitePath_truncInc le_rfl x ξ
    have h2 : H (sitePath x (truncInc n ξ)) = H (sitePath x ξ) :=
      hH _ _ fun k hk => sitePath_truncInc hk x ξ
    rw [hΦdef]
    simp only
    rw [h1, h2, shiftPath_sitePath]
  -- and the inner integral is the expectation from the position at time `n`
  have hinner : ∀ a : ℕ → Site d,
      (∫ η, Φ a η ∂μ) = pathExpect d F (sitePath x a n) * H (sitePath x a) := by
    intro a
    rw [hΦdef]
    simp only
    rw [integral_mul_const, pathExpect, siteWalkLaw,
      integral_map (measurable_sitePath _).aemeasurable hFm.aestronglyMeasurable]
    rfl
  have hm1 : Measurable fun X : ℕ → Site d => F (shiftPath n X) * H X :=
    (hFm.comp (measurable_shiftPath n)).mul hHm
  have hm2 : Measurable fun X : ℕ → Site d => pathExpect d F (X n) * H X :=
    ((measurable_pathExpect d F).comp (measurable_pi_apply n)).mul hHm
  calc ∫ X, F (shiftPath n X) * H X ∂(siteWalkLaw d x)
      = ∫ ξ, F (shiftPath n (sitePath x ξ)) * H (sitePath x ξ) ∂μ := by
        rw [siteWalkLaw, integral_map (measurable_sitePath x).aemeasurable
          hm1.aestronglyMeasurable]
        rfl
    _ = ∫ ξ, Φ (truncInc n ξ) (shiftInc n ξ) ∂μ := by
        exact integral_congr_ae (Filter.Eventually.of_forall hkey)
    _ = ∫ ξ, (∫ η, Φ (truncInc n ξ) η ∂μ) ∂μ := integral_truncInc_shiftInc d n Φ hΦm hΦb
    _ = ∫ ξ, pathExpect d F (sitePath x (truncInc n ξ) n) * H (sitePath x (truncInc n ξ)) ∂μ := by
        exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => hinner _)
    _ = ∫ ξ, pathExpect d F (sitePath x ξ n) * H (sitePath x ξ) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        have e1 : sitePath x (truncInc n ξ) n = sitePath x ξ n := sitePath_truncInc le_rfl x ξ
        have e2 : H (sitePath x (truncInc n ξ)) = H (sitePath x ξ) :=
          hH _ _ fun k hk => sitePath_truncInc hk x ξ
        simp only [e1, e2]
    _ = ∫ X, pathExpect d F (X n) * H X ∂(siteWalkLaw d x) := by
        rw [siteWalkLaw, integral_map (measurable_sitePath x).aemeasurable
          hm2.aestronglyMeasurable]
        rfl

/-! ### The strong Markov property -/

/-- **The strong Markov property at a bounded stopping time.**  For a bounded
measurable `F` on paths, a stopping time `τ` bounded by `N`, and a bounded `G`
which on the event `τ = k` is settled by the positions up to time `k` (that is,
`G` is measurable for the sigma algebra of `τ`),
`E_x[F(θ_τ X) G(X)] = E_x[E_{X_τ}[F] G(X)]`. -/
theorem markov_stopping (d : ℕ) [NeZero d] (N : ℕ) (x : Site d)
    (τ : (ℕ → Site d) → ℕ) (hτ : IsWalkStopping τ) (hτN : ∀ X, τ X ≤ N)
    (F : (ℕ → Site d) → ℝ) (hFm : Measurable F) {CF : ℝ} (hFb : ∀ X, ‖F X‖ ≤ CF)
    (G : (ℕ → Site d) → ℝ) {CG : ℝ} (hGb : ∀ X, ‖G X‖ ≤ CG)
    (hG : ∀ (k : ℕ) (X Y : ℕ → Site d), (∀ j ≤ k, X j = Y j) → τ X = k → G X = G Y) :
    ∫ X, F (shiftPath (τ X) X) * G X ∂(siteWalkLaw d x)
      = ∫ X, pathExpect d F (X (τ X)) * G X ∂(siteWalkLaw d x) := by
  classical
  have hτm : Measurable τ := measurable_isWalkStopping hτ hτN
  set Hk : ℕ → (ℕ → Site d) → ℝ :=
    fun k X => G X * (if τ X = k then 1 else 0) with hHk
  have hGm : Measurable G := by
    refine measurable_of_dependsUpTo (n := N) fun X Y hXY => ?_
    exact hG (τ X) X Y (fun j hj => hXY j (le_trans hj (hτN X))) rfl
  have hHkdep : ∀ k, DependsUpTo k (Hk k) := by
    intro k X Y hXY
    by_cases hk : τ X = k
    · have hkY : τ Y = k := hτ k X Y hXY hk
      have : G X = G Y := hG k X Y hXY hk
      simp [hHk, hk, hkY, this]
    · have hkY : τ Y ≠ k := fun hc => hk (hτ k Y X (fun j hj => (hXY j hj).symm) hc)
      simp [hHk, hk, hkY]
  have hHkb : ∀ k X, ‖Hk k X‖ ≤ CG := by
    intro k X
    rw [hHk]
    simp only
    by_cases hk : τ X = k
    · simpa [hk] using hGb X
    · simpa [hk] using le_trans (norm_nonneg (G X)) (hGb X)
  have hHkm : ∀ k, Measurable (Hk k) := fun k => measurable_of_dependsUpTo (hHkdep k)
  -- split both integrands over the value of the stopping time
  have hsplitL : ∀ X : ℕ → Site d,
      F (shiftPath (τ X) X) * G X
        = ∑ k ∈ Finset.range (N + 1), F (shiftPath k X) * Hk k X := by
    intro X
    rw [Finset.sum_eq_single_of_mem (τ X) (Finset.mem_range.mpr (by have := hτN X; omega : τ X < N + 1))]
    · simp [hHk]
    · intro b _ hb
      simp [hHk, Ne.symm hb]
  have hsplitR : ∀ X : ℕ → Site d,
      pathExpect d F (X (τ X)) * G X
        = ∑ k ∈ Finset.range (N + 1), pathExpect d F (X k) * Hk k X := by
    intro X
    rw [Finset.sum_eq_single_of_mem (τ X) (Finset.mem_range.mpr (by have := hτN X; omega : τ X < N + 1))]
    · simp [hHk]
    · intro b _ hb
      simp [hHk, Ne.symm hb]
  have hintL : ∀ k ∈ Finset.range (N + 1),
      Integrable (fun X => F (shiftPath k X) * Hk k X) (siteWalkLaw d x) := by
    intro k _
    refine Integrable.of_bound
      (((hFm.comp (measurable_shiftPath k)).mul (hHkm k)).aestronglyMeasurable)
      (CF * CG) (Filter.Eventually.of_forall fun X => ?_)
    rw [norm_mul]
    exact mul_le_mul (hFb _) (hHkb k X) (norm_nonneg _)
      (le_trans (norm_nonneg _) (hFb fun _ => 0))
  have hintR : ∀ k ∈ Finset.range (N + 1),
      Integrable (fun X => pathExpect d F (X k) * Hk k X) (siteWalkLaw d x) := by
    intro k _
    refine Integrable.of_bound
      ((((measurable_pathExpect d F).comp (measurable_pi_apply k)).mul
        (hHkm k)).aestronglyMeasurable)
      (CF * CG) (Filter.Eventually.of_forall fun X => ?_)
    rw [norm_mul]
    refine mul_le_mul ?_ (hHkb k X) (norm_nonneg _)
      (le_trans (norm_nonneg _) (hFb fun _ => 0))
    rw [pathExpect]
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (integrable_const CF) (Filter.Eventually.of_forall hFb)) ?_
    simp
  calc ∫ X, F (shiftPath (τ X) X) * G X ∂(siteWalkLaw d x)
      = ∫ X, ∑ k ∈ Finset.range (N + 1), F (shiftPath k X) * Hk k X ∂(siteWalkLaw d x) :=
        integral_congr_ae (Filter.Eventually.of_forall hsplitL)
    _ = ∑ k ∈ Finset.range (N + 1), ∫ X, F (shiftPath k X) * Hk k X ∂(siteWalkLaw d x) :=
        integral_finsetSum _ hintL
    _ = ∑ k ∈ Finset.range (N + 1), ∫ X, pathExpect d F (X k) * Hk k X ∂(siteWalkLaw d x) :=
        Finset.sum_congr rfl fun k _ =>
          markov_fixed d k x F hFm hFb (Hk k) (hHkb k) (hHkdep k)
    _ = ∫ X, ∑ k ∈ Finset.range (N + 1), pathExpect d F (X k) * Hk k X ∂(siteWalkLaw d x) :=
        (integral_finsetSum _ hintR).symm
    _ = ∫ X, pathExpect d F (X (τ X)) * G X ∂(siteWalkLaw d x) :=
        integral_congr_ae (Filter.Eventually.of_forall fun X => (hsplitR X).symm)

/-! ### The transition operator -/

theorem integral_incLaw (d : ℕ) [NeZero d] (f : Site d → ℝ) :
    ∫ v, f v ∂(incLaw d) = (∑ i : Fin d, (f (unit i) + f (-unit i))) / (2 * (d : ℝ)) := by
  have hint : ∀ a : Site d, Integrable f (Measure.dirac a) := fun a =>
    integrable_dirac (by simp [enorm_lt_top])
  have hstep : ∀ i : Fin d,
      ∫ v, f v ∂(Measure.dirac ((0 : Site d) + unit i) + Measure.dirac ((0 : Site d) - unit i))
        = f (unit i) + f (-unit i) := by
    intro i
    rw [integral_add_measure (hint _) (hint _), integral_dirac, integral_dirac]
    simp [sub_eq_add_neg]
  rw [incLaw, instructionLaw, integral_smul_measure,
    integral_finsetSum_measure fun i _ => (hint _).add_measure (hint _),
    Finset.sum_congr rfl fun i _ => hstep i]
  rw [ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast, smul_eq_mul]
  ring

/-- One step of the walk applies the simple random walk operator. -/
theorem integral_incLaw_add (d : ℕ) [NeZero d] (ψ : Site d → ℝ) (x : Site d) :
    ∫ v, ψ (x + v) ∂(incLaw d) = walkOp ψ x := by
  rw [integral_incLaw, walkOp, nbrSum]
  simp [sub_eq_add_neg]

theorem norm_walkOp_le {d : ℕ} (hd : 0 < d) {C : ℝ} {ψ : Site d → ℝ}
    (h : ∀ y, ‖ψ y‖ ≤ C) (x : Site d) : ‖walkOp ψ x‖ ≤ C := by
  have hdR : (0 : ℝ) < 2 * (d : ℝ) := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hsum : ‖nbrSum ψ x‖ ≤ 2 * (d : ℝ) * C := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ i : Fin d, ‖ψ (x + unit i) + ψ (x - unit i)‖ ≤ 2 * C := by
      intro i
      refine le_trans (norm_add_le _ _) ?_
      linarith [h (x + unit i), h (x - unit i)]
    refine le_trans (Finset.sum_le_sum fun i _ => hterm i) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring_nf
    linarith
  have h2 : ‖(2 * (d : ℝ))‖ = 2 * (d : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_pos hdR]
  rw [walkOp, norm_div, h2, div_le_iff₀ hdR]
  nlinarith [hsum]

theorem norm_walkOp_iterate_le {d : ℕ} (hd : 0 < d) {C : ℝ} (n : ℕ) :
    ∀ {ψ : Site d → ℝ}, (∀ y, ‖ψ y‖ ≤ C) → ∀ x, ‖walkOp^[n] ψ x‖ ≤ C := by
  induction n with
  | zero => intro ψ h x; simpa using h x
  | succ n ih =>
      intro ψ h x
      rw [Function.iterate_succ_apply]
      exact ih (fun y => norm_walkOp_le hd h y) x

/-- The law of the position at a fixed time: `E_x[φ(X_n)] = (P^n φ)(x)`, with
`P` the simple random walk operator `LatticeProb.walkOp`. -/
theorem integral_apply_eq_walkOp_iterate (d : ℕ) [NeZero d] (n : ℕ) (φ : Site d → ℝ)
    {C : ℝ} (hφ : ∀ y, ‖φ y‖ ≤ C) (x : Site d) :
    ∫ X, φ (X n) ∂(siteWalkLaw d x) = walkOp^[n] φ x := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  induction n generalizing x with
  | zero =>
      have hmm : Measurable fun X : ℕ → Site d => φ (X 0) :=
        (measurable_of_countable φ).comp (measurable_pi_apply 0)
      rw [siteWalkLaw, integral_map (measurable_sitePath x).aemeasurable
        hmm.aestronglyMeasurable]
      simp only [sitePath_zero, Function.iterate_zero_apply]
      rw [integral_const]
      simp
  | succ n ih =>
      have hFm : Measurable fun Y : ℕ → Site d => φ (Y n) :=
        (measurable_of_countable φ).comp (measurable_pi_apply n)
      have hmk := markov_fixed d 1 x (fun Y : ℕ → Site d => φ (Y n)) hFm
        (fun Y => hφ (Y n)) (fun _ : ℕ → Site d => (1 : ℝ))
        (CH := 1) (fun _ => le_of_eq (by simp)) (fun _ _ _ => rfl)
      simp only [mul_one] at hmk
      have hL : (∫ X, φ (shiftPath 1 X n) ∂(siteWalkLaw d x))
          = ∫ X, φ (X (n + 1)) ∂(siteWalkLaw d x) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
        show φ (X (1 + n)) = φ (X (n + 1))
        congr 2
        omega
      have hR : (∫ X, pathExpect d (fun Y : ℕ → Site d => φ (Y n)) (X 1) ∂(siteWalkLaw d x))
          = ∫ X, walkOp^[n] φ (X 1) ∂(siteWalkLaw d x) :=
        integral_congr_ae (Filter.Eventually.of_forall fun X => ih (X 1))
      have hstep : ∫ X, walkOp^[n] φ (X 1) ∂(siteWalkLaw d x)
          = walkOp (walkOp^[n] φ) x := by
        set ψ : Site d → ℝ := walkOp^[n] φ with hψ
        have hmm : Measurable fun X : ℕ → Site d => ψ (X 1) :=
          (measurable_of_countable ψ).comp (measurable_pi_apply 1)
        have h1 : ∫ X, ψ (X 1) ∂(siteWalkLaw d x)
            = ∫ ξ, ψ (sitePath x ξ 1) ∂(incPathLaw d) := by
          rw [siteWalkLaw, integral_map (measurable_sitePath x).aemeasurable
            hmm.aestronglyMeasurable]
          rfl
        have h2 : ∀ ξ : ℕ → Site d, sitePath x ξ 1 = x + ξ 0 := fun ξ => by
          simp [sitePath]
        have h3 : ∫ ξ, ψ (sitePath x ξ 1) ∂(incPathLaw d)
            = ∫ ξ, ψ (x + ξ 0) ∂(incPathLaw d) :=
          integral_congr_ae (Filter.Eventually.of_forall fun ξ => by simp only [h2])
        have h4 : ∫ v, ψ (x + v) ∂(incLaw d) = ∫ ξ, ψ (x + ξ 0) ∂(incPathLaw d) := by
          have hmm2 : Measurable fun ξ : ℕ → Site d => ψ (x + ξ 0) :=
            (measurable_of_countable fun v : Site d => ψ (x + v)).comp (measurable_pi_apply 0)
          conv_lhs => rw [← Measure.infinitePi_map_eval (fun _ : ℕ => incLaw d) 0]
          rw [integral_map (measurable_pi_apply 0).aemeasurable
            ((measurable_of_countable fun v : Site d => ψ (x + v)).aestronglyMeasurable)]
          rfl
        rw [h1, h3, ← h4, integral_incLaw_add]
      rw [Function.iterate_succ_apply']
      exact hL.symm.trans (hmk.trans (hR.trans hstep))

/-- `E_x[F(θ_n X)] = (P^n φ)(x)` with `φ(y) = E_y[F]`: the expectation of a
bounded measurable function of the shifted path is the `n`-th iterate of the
simple random walk operator applied to the expectation as a function of the
starting site. -/
theorem integral_comp_shiftPath (d : ℕ) [NeZero d] (n : ℕ) (x : Site d)
    (F : (ℕ → Site d) → ℝ) (hFm : Measurable F) {CF : ℝ} (hFb : ∀ X, ‖F X‖ ≤ CF) :
    ∫ X, F (shiftPath n X) ∂(siteWalkLaw d x) = walkOp^[n] (pathExpect d F) x := by
  have hpb : ∀ y, ‖pathExpect d F y‖ ≤ CF := by
    intro y
    rw [pathExpect]
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine le_trans (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (integrable_const CF) (Filter.Eventually.of_forall hFb)) ?_
    simp
  have hmk := markov_fixed d n x F hFm hFb (fun _ : ℕ → Site d => (1 : ℝ))
    (CH := 1) (fun _ => le_of_eq (by simp)) (fun _ _ _ => rfl)
  simp only [mul_one] at hmk
  rw [hmk]
  exact integral_apply_eq_walkOp_iterate d n (pathExpect d F) hpb x

end LatticeProb

end
