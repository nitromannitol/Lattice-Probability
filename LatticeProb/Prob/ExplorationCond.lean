/-
The exploration lemma in conditional form.

`LatticeProb/Prob/Exploration.lean` shows that the sequence an exploration
reveals is an independent sequence with the common law `ν` of the values.  A
martingale argument needs the conditional form of the same fact: the index the
exploration reads at step `n` is a function of what it has already revealed,
and conditionally on the first `n` revealed values the `n`-th is a fresh draw
from `ν`.

The second is the product-space statement transported along `map_revealed`:
under an independent sequence, the conditional expectation of a function of the
`n`-th coordinate given the first `n` is its mean, and conditioning on a
sigma-algebra a measurable map pulls back is conditioning downstream and
reading the answer back through the map.

The first does NOT follow from `IsExploration`.  Its `pred` field says only
that the `n`-th index is unchanged when ONE unread coordinate is overwritten,
which is invariance under finite modifications and leaves, for instance, a
tail function of the configuration free to choose the index.  What is true, and
is what a concrete exploration satisfies, is `ReadsOnlyRevealed`: two
configurations on which the exploration has taken the same steps and seen the
same values so far give the same next index.  That implies `pred`, and with
values read through an injective `g` it gives the congruence in terms of the
revealed values alone.
-/
import Mathlib
import LatticeProb.Prob.Exploration

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

/-! ### A conditional expectation transported along a measurable map -/

/-- **A conditional expectation transported along a measurable map.**
Conditioning on the sigma-algebra a map pulls back is conditioning downstream
and reading the answer back through the map. -/
theorem condExp_comap_map {Ω Ω' : Type*} [MeasurableSpace Ω] {G : MeasurableSpace Ω'}
    [m0 : MeasurableSpace Ω'] (hG : G ≤ m0)
    (P : Measure Ω) [IsFiniteMeasure P] (Φ : Ω → Ω') (hΦ : Measurable Φ)
    (f : Ω' → ℝ) (hf : Integrable f (P.map Φ)) :
    P[fun ω => f (Φ ω) | MeasurableSpace.comap Φ G]
      =ᵐ[P] fun ω => ((P.map Φ)[f | G]) (Φ ω) := by
  classical
  have hcomap : MeasurableSpace.comap Φ G ≤ (inferInstanceAs (MeasurableSpace Ω)) := by
    rintro A ⟨B, hB, rfl⟩
    exact hΦ (hG B hB)
  have hfΦ : Integrable (fun ω => f (Φ ω)) P :=
    (integrable_map_measure hf.aestronglyMeasurable hΦ.aemeasurable).mp hf
  have hcond : Integrable ((P.map Φ)[f | G]) (P.map Φ) := integrable_condExp
  have hcondΦ : Integrable (fun ω => ((P.map Φ)[f | G]) (Φ ω)) P :=
    (integrable_map_measure hcond.aestronglyMeasurable hΦ.aemeasurable).mp hcond
  have hΦmeas : Measurable[MeasurableSpace.comap Φ G, G] Φ :=
    measurable_iff_comap_le.mpr le_rfl
  refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hcomap hfΦ
    (fun A _ _ => hcondΦ.integrableOn) ?_ ?_).symm
  · rintro A ⟨B, hB, rfl⟩ -
    have h1 : ∫ ω in Φ ⁻¹' B, f (Φ ω) ∂P = ∫ y in B, f y ∂(P.map Φ) :=
      (setIntegral_map (hG B hB) hf.aestronglyMeasurable hΦ.aemeasurable).symm
    have h2 : ∫ y in B, f y ∂(P.map Φ) = ∫ y in B, ((P.map Φ)[f | G]) y ∂(P.map Φ) :=
      (setIntegral_condExp hG hf hB).symm
    have h3 : ∫ y in B, ((P.map Φ)[f | G]) y ∂(P.map Φ)
        = ∫ ω in Φ ⁻¹' B, ((P.map Φ)[f | G]) (Φ ω) ∂P :=
      setIntegral_map (hG B hB) hcond.aestronglyMeasurable hΦ.aemeasurable
    rw [← h3, ← h2, ← h1]
  · exact (stronglyMeasurable_condExp.comp_measurable hΦmeas).aestronglyMeasurable

/-! ### The sigma-algebra of the first `n` coordinates -/

variable {α : Type*} [MeasurableSpace α]

/-- The first `n` coordinates of a sequence. -/
def prefixCoords (α : Type*) (n : ℕ) (x : ℕ → α) : Fin n → α := fun k => x (k : ℕ)

theorem measurable_prefixCoords (n : ℕ) : Measurable (prefixCoords α n) :=
  measurable_pi_lambda _ fun k => measurable_pi_apply (k : ℕ)

/-- The sigma-algebra of the first `n` coordinates of a sequence. -/
@[reducible] def prefixAlg (α : Type*) [MeasurableSpace α] (n : ℕ) :
    MeasurableSpace (ℕ → α) :=
  MeasurableSpace.comap (prefixCoords α n) inferInstance

theorem prefixAlg_le (n : ℕ) : prefixAlg α n ≤ (inferInstance : MeasurableSpace (ℕ → α)) :=
  (measurable_prefixCoords n).comap_le

omit [MeasurableSpace α] in
theorem prefixCoords_update (n : ℕ) (x : ℕ → α) (c : α) :
    prefixCoords α n (Function.update x n c) = prefixCoords α n x := by
  funext k
  exact Function.update_of_ne (by omega) _ _

/-- **Conditionally on the first `n` coordinates of an independent sequence, the
`n`-th is a fresh draw.** -/
theorem condExp_eval_prefixAlg (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ)
    {f : α → ℝ} (hf : Integrable f ν) :
    (Measure.infinitePi fun _ : ℕ => ν)[fun x : ℕ → α => f (x n) | prefixAlg α n]
      =ᵐ[Measure.infinitePi fun _ : ℕ => ν] fun _ => ∫ v, f v ∂ν := by
  classical
  haveI : Nonempty α := nonempty_of_isProbabilityMeasure ν
  set P : Measure (ℕ → α) := Measure.infinitePi fun _ : ℕ => ν with hP
  have hmapn : P.map (fun x : ℕ → α => x n) = ν := Measure.infinitePi_map_eval _ n
  have hle : prefixAlg α n ≤ (inferInstance : MeasurableSpace (ℕ → α)) := prefixAlg_le n
  have hfP : Integrable (fun x : ℕ → α => f (x n)) P := by
    rw [← hmapn] at hf
    exact (integrable_map_measure hf.aestronglyMeasurable
      (measurable_pi_apply n).aemeasurable).mp hf
  have hfae : AEStronglyMeasurable f (P.map fun x : ℕ → α => x n) := by
    rw [hmapn]; exact hf.aestronglyMeasurable
  refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hle hfP
    (fun s _ _ => (integrable_const _).integrableOn) ?_ ?_).symm
  · rintro s ⟨B, hB, rfl⟩ -
    set A : Set (ℕ → α) := prefixCoords α n ⁻¹' B with hA
    have hAm : MeasurableSet A := (measurable_prefixCoords n) hB
    set χ : (ℕ → α) → ℝ := A.indicator fun _ => (1 : ℝ) with hχ
    have hχm : Measurable χ := measurable_const.indicator hAm
    have hχinv : ∀ x : ℕ → α, χ (Function.update x n (Classical.arbitrary α)) = χ x := by
      intro x
      have hmem : Function.update x n (Classical.arbitrary α) ∈ A ↔ x ∈ A := by
        simp only [hA, Set.mem_preimage, prefixCoords_update]
      by_cases hx : x ∈ A
      · rw [hχ, Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem hx]
      · rw [hχ, Set.indicator_of_notMem (fun hc => hx (hmem.mp hc)),
          Set.indicator_of_notMem hx]
    have hind : IndepFun χ (fun x : ℕ → α => x n) P :=
      indepFun_of_update_invariant (fun _ : ℕ => ν) (Classical.arbitrary α) χ hχm hχinv
    have hkey : ∫ x, χ x * f (x n) ∂P = (∫ x, χ x ∂P) * ∫ x, f (x n) ∂P := by
      have := hind.integral_fun_comp_mul_comp (f := (id : ℝ → ℝ)) (g := f)
        hχm.aemeasurable (measurable_pi_apply n).aemeasurable
        (by exact aestronglyMeasurable_id) hfae
      simpa using this
    have hmul : ∀ (g : (ℕ → α) → ℝ) (x : ℕ → α), χ x * g x = A.indicator g x := by
      intro g x
      by_cases hx : x ∈ A <;> simp [hχ, hx]
    have hint1 : ∫ x, f (x n) ∂P = ∫ v, f v ∂ν :=
      integral_eval (fun _ : ℕ => ν) n f hf.aestronglyMeasurable
    have hint2 : ∫ x, χ x ∂P = (P A).toReal := by
      rw [hχ, integral_indicator hAm, integral_const, measureReal_def, smul_eq_mul, mul_one,
        Measure.restrict_apply_univ]
    rw [← integral_indicator hAm, ← integral_indicator hAm]
    calc ∫ x, A.indicator (fun _ => ∫ v, f v ∂ν) x ∂P
        = ∫ x, χ x * (∫ v, f v ∂ν) ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => (hmul _ x).symm)
      _ = (P A).toReal * ∫ v, f v ∂ν := by rw [integral_mul_const, hint2]
      _ = ∫ x, χ x * f (x n) ∂P := by rw [hkey, hint1, hint2]
      _ = ∫ x, A.indicator (fun x : ℕ → α => f (x n)) x ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall fun x =>
            hmul (fun x : ℕ → α => f (x n)) x)
  · exact aestronglyMeasurable_const

/-! ### The index is decided by what has been revealed -/

section Reads

variable {ι : Type*} [MeasurableSpace ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  [DecidableEq ι] {idx : ℕ → (Π i, X i) → ι} {g : ∀ i, X i → α}

/-- The index at step `n` is decided by the coordinates the exploration has
already read and the values it found there.  This is what `IsExploration.pred`
intends and is strictly stronger than it: `pred` is invariance under changing
ONE unread coordinate, which is invariance under finite modifications only. -/
def ReadsOnlyRevealed (idx : ℕ → (Π i, X i) → ι) : Prop :=
  ∀ (n : ℕ) (ω ω' : Π i, X i),
    (∀ k < n, idx k ω = idx k ω' ∧ ω (idx k ω) = ω' (idx k ω)) → idx n ω = idx n ω'

omit [MeasurableSpace ι] [∀ i, MeasurableSpace (X i)] in
/-- `ReadsOnlyRevealed` implies the `pred` field of `IsExploration`. -/
theorem idx_update_of_readsOnly (h : ReadsOnlyRevealed idx) {n : ℕ} {ω : Π i, X i} {j : ι}
    (c : X j) (hj : ∀ k < n, idx k ω ≠ j) :
    ∀ m, m ≤ n → idx m (Function.update ω j c) = idx m ω := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      intro hmn
      refine h m _ _ fun k hk => ?_
      have hkidx : idx k (Function.update ω j c) = idx k ω := ih k hk (by omega)
      refine ⟨hkidx, ?_⟩
      rw [hkidx]
      exact Function.update_of_ne (hj k (by omega)) _ _

omit [MeasurableSpace ι] [∀ i, MeasurableSpace (X i)] in
theorem pred_of_readsOnly (h : ReadsOnlyRevealed idx) (n : ℕ) (ω : Π i, X i) (j : ι) (c : X j)
    (hj : ∀ k < n, idx k ω ≠ j) : idx n (Function.update ω j c) = idx n ω :=
  idx_update_of_readsOnly h c hj n le_rfl

omit [MeasurableSpace ι] [MeasurableSpace α] [∀ i, MeasurableSpace (X i)] [DecidableEq ι] in
/-- **The index is a function of the values revealed before it.**  Two
configurations on which the exploration has revealed the same first `n` values
read the same coordinate at step `n`. -/
theorem idx_eq_of_revealed_eq (h : ReadsOnlyRevealed idx)
    (hginj : ∀ i, Function.Injective (g i)) :
    ∀ (n : ℕ) (ω ω' : Π i, X i),
      (∀ k < n, revealed idx g ω k = revealed idx g ω' k) → idx n ω = idx n ω' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro ω ω' hrev
      refine h n ω ω' fun k hk => ?_
      have hkidx : idx k ω = idx k ω' := ih k hk ω ω' fun m hm => hrev m (by omega)
      refine ⟨hkidx, ?_⟩
      have hv := hrev k hk
      unfold revealed at hv
      rw [← hkidx] at hv
      exact hginj (idx k ω) hv

/-- The first `n` values an exploration reveals. -/
def revealedPrefix (idx : ℕ → (Π i, X i) → ι) (g : ∀ i, X i → α) (n : ℕ)
    (ω : Π i, X i) : Fin n → α := prefixCoords α n (revealed idx g ω)

omit [MeasurableSpace ι] [MeasurableSpace α] [∀ i, MeasurableSpace (X i)] [DecidableEq ι] in
theorem revealed_eq_of_revealedPrefix_eq {n : ℕ} {ω ω' : Π i, X i}
    (h : revealedPrefix idx g n ω = revealedPrefix idx g n ω') :
    ∀ k < n, revealed idx g ω k = revealed idx g ω' k := by
  intro k hk
  have := congrFun h ⟨k, hk⟩
  exact this

variable [Countable ι] [MeasurableSingletonClass ι]

omit [∀ i, MeasurableSpace (X i)] [DecidableEq ι] [MeasurableSingletonClass ι] in
/-- **The index is measurable for the sigma-algebra of the values revealed
before it**, when the values live in a countable space. -/
theorem measurable_idx_comap_revealedPrefix [Countable α] [MeasurableSingletonClass α]
    (h : ReadsOnlyRevealed idx) (hginj : ∀ i, Function.Injective (g i)) (n : ℕ) :
    Measurable[MeasurableSpace.comap (revealedPrefix idx g n) inferInstance] (idx n) := by
  have hpre : ∀ j : ι,
      MeasurableSet[MeasurableSpace.comap (revealedPrefix idx g n) inferInstance]
        (idx n ⁻¹' {j}) := by
    intro j
    refine ⟨(revealedPrefix idx g n) '' (idx n ⁻¹' {j}), (Set.to_countable _).measurableSet, ?_⟩
    refine Set.Subset.antisymm ?_ (fun ω hω => ⟨ω, hω, rfl⟩)
    rintro ω ⟨ω', hω', heq⟩
    show idx n ω = j
    rw [idx_eq_of_revealed_eq h hginj n ω ω' (revealed_eq_of_revealedPrefix_eq heq.symm)]
    exact hω'
  exact @measurable_to_countable' ι (Π i, X i) _ _
    (MeasurableSpace.comap (revealedPrefix idx g n) inferInstance) (idx n) hpre

/-! ### The conditional law of the next revealed value -/

/-- **The exploration lemma in conditional form.**  Conditionally on the first
`n` values an exploration reveals, the `n`-th is a fresh draw from the common
law `ν`. -/
theorem condExp_revealed (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {ν : Measure α} (hidx : IsExploration idx) (hg : ∀ i, Measurable (g i))
    (hlaw : ∀ i, (μ i).map (g i) = ν) (n : ℕ) {f : α → ℝ} (hf : Integrable f ν) :
    (Measure.infinitePi μ)[fun ω => f (revealed idx g ω n) |
        MeasurableSpace.comap (revealedPrefix idx g n) inferInstance]
      =ᵐ[Measure.infinitePi μ] fun _ => ∫ v, f v ∂ν := by
  classical
  obtain ⟨i₀⟩ : Nonempty ι := nonempty_of_exploration μ idx
  haveI hν : IsProbabilityMeasure ν := by
    rw [← hlaw i₀]
    exact Measure.isProbabilityMeasure_map (hg i₀).aemeasurable
  set P : Measure (Π i, X i) := Measure.infinitePi μ with hP
  set Φ : (Π i, X i) → (ℕ → α) := revealed idx g with hΦdef
  have hΦ : Measurable Φ := measurable_pi_lambda _ fun k => measurable_revealed hidx.meas hg k
  have hmap : P.map Φ = Measure.infinitePi fun _ : ℕ => ν := map_revealed μ hidx hg hlaw
  have hcomap : MeasurableSpace.comap (revealedPrefix idx g n) inferInstance
      = MeasurableSpace.comap Φ (prefixAlg α n) := by
    rw [prefixAlg, MeasurableSpace.comap_comp]
    rfl
  have hint : Integrable (fun x : ℕ → α => f (x n)) (P.map Φ) := by
    rw [hmap]
    have hmapn : (Measure.infinitePi fun _ : ℕ => ν).map (fun x : ℕ → α => x n) = ν :=
      Measure.infinitePi_map_eval _ n
    rw [← hmapn] at hf
    exact (integrable_map_measure hf.aestronglyMeasurable
      (measurable_pi_apply n).aemeasurable).mp hf
  have h1 := condExp_comap_map (prefixAlg_le (α := α) n) P Φ hΦ (fun x : ℕ → α => f (x n)) hint
  rw [hcomap]
  refine h1.trans ?_
  have h2 : ((P.map Φ)[fun x : ℕ → α => f (x n) | prefixAlg α n])
      =ᵐ[P.map Φ] fun _ => ∫ v, f v ∂ν := by
    rw [hmap]
    exact (condExp_eval_prefixAlg ν n hf).symm.symm
  exact ae_eq_comp hΦ.aemeasurable h2

end Reads

end LatticeProb

end
