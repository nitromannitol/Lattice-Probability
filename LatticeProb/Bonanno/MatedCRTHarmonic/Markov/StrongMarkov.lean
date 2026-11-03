/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Markov.StrongMarkov at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.HitTime

/-!
# The strong Markov property on `{τ < ⊤}` and composite stopping times

For a stopping time `τ : (ℕ → S) → ℕ∞` of the canonical filtration `Filtration.piLE` (e.g. a
hitting time `hitTime A`, `isStoppingTime_hitTime`), an event `F` of the stopped
σ-algebra `ℱ_τ` (`hτ.measurableSpace`) and a measurable set of paths `B`:

  `P_z(F ∩ {τ < ⊤} ∩ {θ_τ ω ∈ B}) = ∫⁻_{F ∩ {τ < ⊤}} P_{ω τ}(B) dP_z`

(`chainLaw_inter_stopShift_preimage`), with a `lintegral` version (`setLIntegral_stopShift`),
a kernel version (`restrict_map_stopShift`), the hitting-time instance
(`chainLaw_inter_hitTime_stopShift_preimage`) and the two bounds used in successive-scale
arguments (`le_chainLaw_inter_stopShift_preimage`, `chainLaw_inter_stopShift_preimage_le`:
if `P_{ω τ}(B) ≥ p` (resp. `≤ q`) on `F ∩ {τ < ⊤}` then the left side is `≥ p · P_z(F ∩ {τ < ⊤})`
(resp. `≤ q · …`)). **No almost-sure finiteness of `τ` is
assumed**: the identity is restricted to `{τ < ⊤}`, as needed on transient graphs. The proof slices `{τ < ⊤}` along `{τ = j}` and applies the Markov
property at the deterministic time `j` on each slice (the architecture of
`ReflectedWalk.MarkovChain.chainLaw_map_walkShift_hitIndex`, which assumes `τ < ⊤` a.s.).

For successive stopping times (e.g. successive scale-hitting times) we define
`thenTime σ τ = σ + τ ∘ θ_σ` (the first time `τ` occurs for the path restarted at `σ`;
`thenTime σ (hitTime A)` is the first visit to `A` at or after `σ`) and prove:

* `isStoppingTime_thenTime`: it is again a stopping time;
* `measurableSet_thenTime_of_stopShift`: for `G ∈ ℱ_τ`, the event `{σ < ⊤, θ_σ ω ∈ G}` lies in
  `ℱ_{thenTime σ τ}`; and `ℱ_σ ≤ ℱ_{thenTime σ τ}` (`measurableSpace_le_thenTime`);
* `stopShift_thenTime`, `stopState_thenTime`: on `{thenTime σ τ < ⊤}`,
  `θ_{σ + τ∘θ_σ} = θ_τ ∘ θ_σ`;
* `hitTime_le_thenTime_hitTime`, `thenTime_hitTime_eq_hitTime`: the first visit to `A` after `σ`
  is `≥ τ_A`, with equality when `σ ≤ τ_A`.

To verify that a concrete path event is in `ℱ_τ`, use `measurableSet_stopping_of_forall_eq`:
a measurable event whose membership, on `{τ < ⊤}`, depends only on `ω 0, …, ω τ` is in `ℱ_τ`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal

namespace MatedCRTHarmonic.Markov

/-! ### Events of the stopped σ-algebra -/

section StoppedEvents

variable {S : Type*} [MeasurableSpace S] {τ : (ℕ → S) → ℕ∞}

/-- An event of `ℱ_τ` is measurable. -/
lemma measurableSet_of_measurableSet_stopping
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) τ) {F : Set (ℕ → S)}
    (hF : MeasurableSet[hτ.measurableSpace] F) : MeasurableSet F :=
  hτ.measurableSpace_le F hF

/-- For `F ∈ ℱ_τ`, the slice `F ∩ {τ = n}` is an event of the coordinates `≤ n`. -/
lemma measurableSet_inter_eq_piLE
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) τ) {F : Set (ℕ → S)}
    (hF : MeasurableSet[hτ.measurableSpace] F) (n : ℕ) :
    MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] (F ∩ {ω | τ ω = n}) := by
  have h1 : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] (F ∩ {ω | τ ω ≤ n}) :=
    hF.2 n
  have h2 : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] {ω | τ ω = n} :=
    hτ.measurableSet_eq n
  have : F ∩ {ω | τ ω = n} = (F ∩ {ω | τ ω ≤ n}) ∩ {ω | τ ω = n} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨hF, h⟩ => ⟨⟨hF, h.le⟩, h⟩, fun ⟨⟨hF, _⟩, h⟩ => ⟨hF, h⟩⟩
  rw [this]
  exact h1.inter h2

/-- For `F ∈ ℱ_τ`, the event `F ∩ {τ < ⊤}` is measurable. -/
lemma measurableSet_inter_lt_top
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) τ) {F : Set (ℕ → S)}
    (hF : MeasurableSet[hτ.measurableSpace] F) : MeasurableSet (F ∩ {ω | τ ω < ⊤}) :=
  (measurableSet_of_measurableSet_stopping hτ hF).inter
    (measurable_of_isStoppingTime hτ (MeasurableSet.of_discrete : MeasurableSet {x : ℕ∞ | x < ⊤}))

/-- A measurable event which depends only on the coordinates `≤ n` is an event of
`Filtration.piLE n`. -/
lemma measurableSet_piLE_of_forall_eq {n : ℕ} {G : Set (ℕ → S)} (hG : MeasurableSet G)
    (hdet : ∀ ω ω' : ℕ → S, (∀ m ≤ n, ω m = ω' m) → ω ∈ G → ω' ∈ G) :
    MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] G := by
  rcases isEmpty_or_nonempty S with hS | ⟨⟨s₀⟩⟩
  · rw [Set.eq_empty_of_isEmpty G]
    exact @MeasurableSet.empty _ (Filtration.piLE (X := fun _ : ℕ => S) n)
  · let ext : (Finset.Iic n → S) → (ℕ → S) := fun h i =>
      if hi : i ≤ n then h ⟨i, Finset.mem_Iic.mpr hi⟩ else s₀
    have hext : Measurable ext := by
      refine Measurable.of_eval fun i => ?_
      by_cases hi : i ≤ n
      · simp only [ext, hi, ↓reduceDIte]
        exact measurable_pi_apply _
      · simp only [ext, hi, ↓reduceDIte]
        exact measurable_const
    have hagree : ∀ ω : ℕ → S, ∀ m ≤ n, ω m = ext (frestrictLe n ω) m := fun ω m hm => by
      simp [ext, hm, frestrictLe_apply]
    have hG' : G = frestrictLe n ⁻¹' (ext ⁻¹' G) := by
      ext ω
      exact ⟨hdet _ _ (hagree ω), hdet _ _ fun m hm => (hagree ω m hm).symm⟩
    rw [hG', Filtration.piLE_eq_comap_frestrictLe]
    exact ⟨_, hext hG, rfl⟩

/-- If `τ ω = k` and `ω'` agrees with `ω` up to time `k`, then `τ ω' = k`. -/
lemma eq_of_isStoppingTime_of_forall_eq
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) τ) {ω ω' : ℕ → S} {k : ℕ}
    (hk : τ ω = k) (h : ∀ m ≤ k, ω m = ω' m) : τ ω' = k := by
  obtain ⟨s, -, hseq⟩ := exists_frestrictLe_preimage_of_piLE (hτ.measurableSet_eq k)
  have hω : ω ∈ frestrictLe k ⁻¹' s := by
    rw [hseq]
    exact hk
  have heq : frestrictLe k ω = frestrictLe k ω' :=
    funext fun i => h i (Finset.mem_Iic.mp i.2)
  have hω' : ω' ∈ frestrictLe k ⁻¹' s := by
    rw [Set.mem_preimage, ← heq]
    exact hω
  rw [hseq] at hω'
  exact hω'

/-- **Events determined by the path up to `τ` are in `ℱ_τ`**: if `G` is measurable and, for
`τ ω < ⊤`, membership in `G` only depends on `ω` up to time `τ ω`, then `G ∈ ℱ_τ`. -/
theorem measurableSet_stopping_of_forall_eq
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) τ) {G : Set (ℕ → S)}
    (hG : MeasurableSet G)
    (hdet : ∀ ω ω' : ℕ → S, τ ω < ⊤ → (∀ m : ℕ, (m : ℕ∞) ≤ τ ω → ω m = ω' m) → ω ∈ G →
      ω' ∈ G) :
    MeasurableSet[hτ.measurableSpace] G := by
  refine ⟨by rw [iSup_piLE]; exact hG, fun n => ?_⟩
  change MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] (G ∩ {ω | τ ω ≤ n})
  refine measurableSet_piLE_of_forall_eq
    (hG.inter (measurable_of_isStoppingTime hτ
      (MeasurableSet.of_discrete : MeasurableSet {x : ℕ∞ | x ≤ n}))) ?_
  rintro ω ω' hagree ⟨hωG, hωn⟩
  have hfin : τ ω ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top n) hωn
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
  have hkn : k ≤ n := by
    have : (k : ℕ∞) ≤ n := hk ▸ hωn
    exact_mod_cast this
  have hτ' : τ ω' = k :=
    eq_of_isStoppingTime_of_forall_eq hτ hk.symm fun m hm => hagree m (hm.trans hkn)
  refine ⟨hdet ω ω' (lt_top_iff_ne_top.mpr hfin) (fun m hm => hagree m ?_) hωG, ?_⟩
  · rw [← hk] at hm
    exact_mod_cast hm.trans (Nat.cast_le.mpr hkn)
  · show τ ω' ≤ n
    rw [hτ']
    exact_mod_cast hkn

omit [MeasurableSpace S] in
/-- `{τ < ⊤}` is the disjoint union of the slices `{τ = j}`. -/
lemma inter_lt_top_eq_iUnion (F : Set (ℕ → S)) :
    F ∩ {ω | τ ω < ⊤} = ⋃ j : ℕ, F ∩ {ω | τ ω = j} := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, lt_top_iff_ne_top]
  constructor
  · rintro ⟨hF, h⟩
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp h
    exact ⟨j, hF, hj.symm⟩
  · rintro ⟨j, hF, hj⟩
    exact ⟨hF, hj ▸ ENat.natCast_ne_top j⟩

omit [MeasurableSpace S] in
lemma pairwise_disjoint_inter_eq (F : Set (ℕ → S)) :
    Pairwise fun i j : ℕ => Disjoint (F ∩ {ω | τ ω = i}) (F ∩ {ω | τ ω = j}) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun ω hi hj => hij ?_
  exact Nat.cast_injective (hi.2.symm.trans hj.2)

end StoppedEvents

/-! ### The strong Markov property -/

section StrongMarkov

variable {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
  (κ : Kernel S S) [IsMarkovKernel κ]

/-- **Strong Markov property on `{τ < ⊤}`**, `lintegral` form: for a stopping time `τ` of the
canonical filtration, `F ∈ ℱ_τ` and measurable `f ≥ 0`,
`∫⁻_{F ∩ {τ<⊤}} f(θ_τ ω) dP_z = ∫⁻_{F ∩ {τ<⊤}} E_{ω τ}[f] dP_z`. No finiteness of `τ` is
assumed. -/
theorem setLIntegral_stopShift (z : S) {τ : (ℕ → S) → ℕ∞}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) τ) {F : Set (ℕ → S)}
    (hF : MeasurableSet[hτ.measurableSpace] F) {f : (ℕ → S) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω in F ∩ {ω | τ ω < ⊤}, f (stopShift τ ω) ∂chainLaw κ z =
      ∫⁻ ω in F ∩ {ω | τ ω < ⊤}, (∫⁻ ω', f ω' ∂chainLaw κ (stopState τ ω)) ∂chainLaw κ z := by
  have hT : ∀ j : ℕ, MeasurableSet (F ∩ {ω | τ ω = j}) := fun j =>
    measurableSet_of_measurableSet_piLE (measurableSet_inter_eq_piLE hτ hF j)
  rw [inter_lt_top_eq_iUnion, lintegral_iUnion hT (pairwise_disjoint_inter_eq F),
    lintegral_iUnion hT (pairwise_disjoint_inter_eq F)]
  congr 1
  funext j
  have h1 : ∫⁻ ω in F ∩ {ω | τ ω = j}, f (stopShift τ ω) ∂chainLaw κ z =
      ∫⁻ ω in F ∩ {ω | τ ω = j}, f (walkShift j ω) ∂chainLaw κ z :=
    setLIntegral_congr_fun (hT j) (fun ω hω => by rw [stopShift_eq_of_eq hω.2])
  have h2 : ∫⁻ ω in F ∩ {ω | τ ω = j}, (∫⁻ ω', f ω' ∂chainLaw κ (stopState τ ω)) ∂chainLaw κ z =
      ∫⁻ ω in F ∩ {ω | τ ω = j}, (∫⁻ ω', f ω' ∂chainLaw κ (ω j)) ∂chainLaw κ z :=
    setLIntegral_congr_fun (hT j) (fun ω hω => by rw [stopState_eq_of_eq hω.2])
  rw [h1, h2]
  exact setLIntegral_walkShift_of_piLE κ z j (measurableSet_inter_eq_piLE hτ hF j) hf

/-- **Strong Markov property on `{τ < ⊤}`**, set form: for a stopping time `τ` of the canonical
filtration, `F ∈ ℱ_τ` and measurable `B`,
`P_z(F ∩ {τ < ⊤} ∩ {θ_τ ω ∈ B}) = ∫⁻_{F ∩ {τ < ⊤}} P_{ω τ}(B) dP_z`.
No finiteness of `τ` is assumed. -/
theorem chainLaw_inter_stopShift_preimage (z : S) {τ : (ℕ → S) → ℕ∞}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) τ) {F : Set (ℕ → S)}
    (hF : MeasurableSet[hτ.measurableSpace] F) {B : Set (ℕ → S)} (hB : MeasurableSet B) :
    chainLaw κ z (F ∩ {ω | τ ω < ⊤} ∩ stopShift τ ⁻¹' B) =
      ∫⁻ ω in F ∩ {ω | τ ω < ⊤}, chainLaw κ (stopState τ ω) B ∂chainLaw κ z := by
  have hsh : Measurable (stopShift τ) := measurable_stopShift (measurable_of_isStoppingTime hτ)
  have h := setLIntegral_stopShift κ z hτ hF (measurable_one.indicator hB)
  simp only [lintegral_indicator_one hB] at h
  rw [← h, Set.inter_comm _ (stopShift τ ⁻¹' B), ← Measure.restrict_apply (hsh hB),
    ← lintegral_indicator_one (hsh hB)]
  rfl

/-- **Strong Markov property on `{τ < ⊤}`**, kernel form: the law of `θ_τ ω` under
`P_z(· ∩ F ∩ {τ < ⊤})` is the mixture of the chain laws `P_y` over the law of `ω τ`. -/
theorem restrict_map_stopShift (z : S) {τ : (ℕ → S) → ℕ∞}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) τ) {F : Set (ℕ → S)}
    (hF : MeasurableSet[hτ.measurableSpace] F) :
    ((chainLaw κ z).restrict (F ∩ {ω | τ ω < ⊤})).map (stopShift τ) =
      pathKernel κ ∘ₘ ((chainLaw κ z).restrict (F ∩ {ω | τ ω < ⊤})).map (stopState τ) := by
  have hm := measurable_of_isStoppingTime hτ
  have hE : MeasurableSet (F ∩ {ω | τ ω < ⊤}) :=
    (measurableSet_of_measurableSet_stopping hτ hF).inter
      (hm (MeasurableSet.of_discrete : MeasurableSet {x : ℕ∞ | x < ⊤}))
  ext B hB
  rw [Measure.map_apply (measurable_stopShift hm) hB, Measure.restrict_apply
      (measurable_stopShift hm hB), Measure.bind_apply hB (pathKernel κ).aemeasurable,
    lintegral_map (Kernel.measurable_coe _ hB) (measurable_stopState hm),
    Set.inter_comm, chainLaw_inter_stopShift_preimage κ z hτ hF hB]
  simp_rw [pathKernel_apply]

/-- Strong Markov property on `{τ < ⊤}` without a past event:
`P_z(τ < ⊤, θ_τ ω ∈ B) = ∫⁻_{τ < ⊤} P_{ω τ}(B) dP_z`. -/
theorem chainLaw_lt_top_inter_stopShift_preimage (z : S) {τ : (ℕ → S) → ℕ∞}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) τ) {B : Set (ℕ → S)}
    (hB : MeasurableSet B) :
    chainLaw κ z ({ω | τ ω < ⊤} ∩ stopShift τ ⁻¹' B) =
      ∫⁻ ω in {ω | τ ω < ⊤}, chainLaw κ (stopState τ ω) B ∂chainLaw κ z := by
  have h := chainLaw_inter_stopShift_preimage κ z hτ (F := Set.univ)
    (@MeasurableSet.univ _ hτ.measurableSpace) hB
  simpa only [Set.univ_inter] using h

/-- **Strong Markov property at a hitting time**, on `{τ_A < ⊤}` (no finiteness assumed):
for measurable `A`, `F ∈ ℱ_{τ_A}` and measurable `B`,
`P_z(F ∩ {τ_A < ⊤} ∩ {θ_{τ_A} ω ∈ B}) = ∫⁻_{F ∩ {τ_A < ⊤}} P_{ω τ_A}(B) dP_z`. -/
theorem chainLaw_inter_hitTime_stopShift_preimage (z : S) {A : Set S} (hA : MeasurableSet A)
    {F : Set (ℕ → S)} (hF : MeasurableSet[(isStoppingTime_hitTime hA).measurableSpace] F)
    {B : Set (ℕ → S)} (hB : MeasurableSet B) :
    chainLaw κ z (F ∩ {ω | hitTime A ω < ⊤} ∩ stopShift (hitTime A) ⁻¹' B) =
      ∫⁻ ω in F ∩ {ω | hitTime A ω < ⊤}, chainLaw κ (stopState (hitTime A) ω) B
        ∂chainLaw κ z :=
  chainLaw_inter_stopShift_preimage κ z (isStoppingTime_hitTime hA) hF hB

/-- Lower bound from the strong Markov property: if `P_{ω τ}(B) ≥ p` on `F ∩ {τ < ⊤}`, then
`P_z(F ∩ {τ < ⊤} ∩ {θ_τ ω ∈ B}) ≥ p · P_z(F ∩ {τ < ⊤})`. -/
theorem le_chainLaw_inter_stopShift_preimage (z : S) {τ : (ℕ → S) → ℕ∞}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) τ) {F : Set (ℕ → S)}
    (hF : MeasurableSet[hτ.measurableSpace] F) {B : Set (ℕ → S)} (hB : MeasurableSet B)
    {p : ℝ≥0∞} (hp : ∀ ω ∈ F ∩ {ω | τ ω < ⊤}, p ≤ chainLaw κ (stopState τ ω) B) :
    p * chainLaw κ z (F ∩ {ω | τ ω < ⊤}) ≤
      chainLaw κ z (F ∩ {ω | τ ω < ⊤} ∩ stopShift τ ⁻¹' B) := by
  rw [chainLaw_inter_stopShift_preimage κ z hτ hF hB, ← setLIntegral_const]
  exact setLIntegral_mono' (measurableSet_inter_lt_top hτ hF) hp

/-- Upper bound from the strong Markov property: if `P_{ω τ}(B) ≤ q` on `F ∩ {τ < ⊤}`, then
`P_z(F ∩ {τ < ⊤} ∩ {θ_τ ω ∈ B}) ≤ q · P_z(F ∩ {τ < ⊤})`. -/
theorem chainLaw_inter_stopShift_preimage_le (z : S) {τ : (ℕ → S) → ℕ∞}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) τ) {F : Set (ℕ → S)}
    (hF : MeasurableSet[hτ.measurableSpace] F) {B : Set (ℕ → S)} (hB : MeasurableSet B)
    {q : ℝ≥0∞} (hq : ∀ ω ∈ F ∩ {ω | τ ω < ⊤}, chainLaw κ (stopState τ ω) B ≤ q) :
    chainLaw κ z (F ∩ {ω | τ ω < ⊤} ∩ stopShift τ ⁻¹' B) ≤
      q * chainLaw κ z (F ∩ {ω | τ ω < ⊤}) := by
  rw [chainLaw_inter_stopShift_preimage κ z hτ hF hB, ← setLIntegral_const]
  exact setLIntegral_mono' (measurableSet_inter_lt_top hτ hF) hq

end StrongMarkov

/-! ### Composite stopping times: `σ` followed by `τ` on the restarted path -/

section ThenTime

variable {S : Type*}

/-- `σ` followed by `τ` on the path restarted at `σ`: `σ + τ ∘ θ_σ` (equal to `⊤` when
`σ = ⊤`, since `⊤ + x = ⊤`). For `τ = hitTime A` this is the first visit to `A` at or after
time `σ`. -/
noncomputable def thenTime (σ τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) : ℕ∞ := σ ω + τ (stopShift σ ω)

variable {σ τ : (ℕ → S) → ℕ∞} {ω : ℕ → S}

lemma thenTime_eq_of_eq {n : ℕ} (h : σ ω = n) : thenTime σ τ ω = n + τ (walkShift n ω) := by
  rw [thenTime, h, stopShift_eq_of_eq h]

lemma thenTime_eq_top_of_eq_top (h : σ ω = ⊤) : thenTime σ τ ω = ⊤ := by
  rw [thenTime, h, top_add]

lemma le_thenTime : σ ≤ thenTime σ τ := fun _ => le_self_add

lemma thenTime_lt_top_iff : thenTime σ τ ω < ⊤ ↔ σ ω < ⊤ ∧ τ (stopShift σ ω) < ⊤ := by
  rw [thenTime, ENat.add_lt_top]

lemma thenTime_le_coe_iff {n : ℕ} :
    thenTime σ τ ω ≤ n ↔ ∃ j ≤ n, σ ω = j ∧ τ (walkShift j ω) ≤ (n - j : ℕ) := by
  constructor
  · intro h
    have hσ : σ ω ≠ ⊤ := fun h' => by
      rw [thenTime_eq_top_of_eq_top h'] at h
      exact ENat.natCast_ne_top n (top_le_iff.mp h)
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hσ
    rw [thenTime_eq_of_eq hj.symm] at h
    have hτ : τ (walkShift j ω) ≠ ⊤ := fun h' => by
      rw [h', add_top] at h
      exact ENat.natCast_ne_top n (top_le_iff.mp h)
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hτ
    rw [← hk] at h
    have h' : j + k ≤ n := by exact_mod_cast h
    refine ⟨j, by omega, hj.symm, ?_⟩
    rw [← hk]
    exact_mod_cast (by omega : k ≤ n - j)
  · rintro ⟨j, hjn, hj, hτ⟩
    rw [thenTime_eq_of_eq hj]
    calc (j : ℕ∞) + τ (walkShift j ω) ≤ (j : ℕ∞) + ((n - j : ℕ) : ℕ∞) := by gcongr
      _ = n := by exact_mod_cast (by omega : j + (n - j) = n)

/-- On `{thenTime σ τ < ⊤}`, shifting by `σ + τ ∘ θ_σ` is shifting by `σ`, then by `τ`. -/
lemma stopShift_thenTime (h : thenTime σ τ ω ≠ ⊤) :
    stopShift (thenTime σ τ) ω = stopShift τ (stopShift σ ω) := by
  have h' := (thenTime_lt_top_iff (σ := σ) (τ := τ) (ω := ω)).mp (lt_top_iff_ne_top.mpr h)
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp h'.1.ne
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h'.2.ne
  have h1 : thenTime σ τ ω = ((j + k : ℕ) : ℕ∞) := by
    rw [thenTime, ← hj, ← hk]
    push_cast
    rfl
  rw [stopShift_eq_of_eq h1, stopShift_eq_of_eq hk.symm, stopShift_eq_of_eq hj.symm,
    walkShift_walkShift]

/-- On `{thenTime σ τ < ⊤}`, the state at `σ + τ ∘ θ_σ` is the state at `τ` of `θ_σ ω`. -/
lemma stopState_thenTime (h : thenTime σ τ ω ≠ ⊤) :
    stopState (thenTime σ τ) ω = stopState τ (stopShift σ ω) := by
  rw [← stopShift_zero_apply, stopShift_thenTime h, stopShift_zero_apply]

/-- The first visit to `A` at or after `σ` comes no earlier than the first visit to `A`. -/
lemma hitTime_le_thenTime_hitTime {A : Set S} : hitTime A ω ≤ thenTime σ (hitTime A) ω := by
  rcases eq_or_ne (thenTime σ (hitTime A) ω) ⊤ with h | h
  · rw [h]
    exact le_top
  · have h' := (thenTime_lt_top_iff (σ := σ) (τ := hitTime A) (ω := ω)).mp
      (lt_top_iff_ne_top.mpr h)
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp h'.1.ne
    rw [thenTime_eq_of_eq hj.symm]
    have h2 : hitTime A (walkShift j ω) ≠ ⊤ := by
      rw [← stopShift_eq_of_eq hj.symm]
      exact h'.2.ne
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h2
    have hmem : ω (j + k) ∈ A := (hitTime_eq_coe_iff.mp hk.symm).1
    rw [← hk]
    exact_mod_cast hitTime_le_of_mem (ω := ω) (n := j + k) hmem

/-- If `σ` occurs no later than the first visit to `A`, then the first visit to `A` at or after
`σ` is the first visit to `A`. -/
lemma thenTime_hitTime_eq_hitTime {A : Set S} (h : σ ω ≤ hitTime A ω) :
    thenTime σ (hitTime A) ω = hitTime A ω := by
  rcases eq_or_ne (σ ω) ⊤ with hσ | hσ
  · rw [thenTime_eq_top_of_eq_top hσ, eq_comm, ← top_le_iff, ← hσ]
    exact h
  · obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hσ
    have hj' : (j : ℕ∞) ≤ hitTime A ω := by
      rw [hj]
      exact h
    rw [thenTime_eq_of_eq hj.symm]
    exact (hitTime_eq_add_hitTime_walkShift hj').symm

variable [MeasurableSpace S]

/-- The preimage under `θ_j` of an event of the coordinates `≤ m` is an event of the coordinates
`≤ j + m`. -/
lemma measurableSet_piLE_walkShift_preimage {j m : ℕ} {G : Set (ℕ → S)}
    (hG : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) m] G) :
    MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) (j + m)] (walkShift j ⁻¹' G) := by
  obtain ⟨s, hs, rfl⟩ := exists_frestrictLe_preimage_of_piLE hG
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact ⟨shiftPrefix j m ⁻¹' s, measurable_shiftPrefix j m hs, rfl⟩

lemma measurableSet_piLE_mono {m n : ℕ} (hmn : m ≤ n) {G : Set (ℕ → S)}
    (hG : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) m] G) :
    MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] G :=
  (Filtration.piLE (X := fun _ : ℕ => S)).mono hmn G hG

omit [MeasurableSpace S] in
/-- The decomposition of `{thenTime σ τ ≤ n} ∩ {σ < ⊤, θ_σ ω ∈ G}` along the value of `σ`. -/
lemma inter_thenTime_le_eq (G : Set (ℕ → S)) (n : ℕ) :
    ({ω | σ ω < ⊤} ∩ stopShift σ ⁻¹' G) ∩ {ω | thenTime σ τ ω ≤ n} =
      ⋃ j ∈ Finset.range (n + 1),
        {ω | σ ω = j} ∩ walkShift j ⁻¹' (G ∩ {ω' | τ ω' ≤ (n - j : ℕ)}) := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_iUnion,
    Finset.mem_range, exists_prop]
  constructor
  · rintro ⟨⟨-, hG⟩, hle⟩
    obtain ⟨j, hjn, hj, hτ⟩ := thenTime_le_coe_iff.mp hle
    rw [stopShift_eq_of_eq hj] at hG
    exact ⟨j, Nat.lt_succ_of_le hjn, hj, hG, hτ⟩
  · rintro ⟨j, hjn, hj, hG, hτ⟩
    refine ⟨⟨by rw [hj]; exact ENat.natCast_lt_top j, by rw [stopShift_eq_of_eq hj]; exact hG⟩, ?_⟩
    exact thenTime_le_coe_iff.mpr ⟨j, Nat.le_of_lt_succ hjn, hj, hτ⟩

/-- **`σ` followed by `τ` is a stopping time.** -/
theorem isStoppingTime_thenTime
    (hσ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) σ)
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) τ) :
    IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) (thenTime σ τ) := by
  intro n
  have h := inter_thenTime_le_eq (σ := σ) (τ := τ) Set.univ n
  simp only [Set.preimage_univ, Set.inter_univ, Set.univ_inter] at h
  have hsub : {ω | thenTime σ τ ω ≤ n} = {ω | σ ω < ⊤} ∩ {ω | thenTime σ τ ω ≤ n} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    refine ⟨fun hle => ⟨lt_of_le_of_lt (le_thenTime ω) (lt_of_le_of_lt hle
      (ENat.natCast_lt_top n)), hle⟩, fun h => h.2⟩
  change MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] {ω | thenTime σ τ ω ≤ n}
  rw [hsub, h]
  refine Finset.measurableSet_biUnion _ fun j hj => ?_
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  refine (measurableSet_piLE_mono hjn (hσ.measurableSet_eq j)).inter ?_
  have := measurableSet_piLE_walkShift_preimage (j := j) (hτ (n - j))
  rwa [Nat.add_sub_cancel' hjn] at this

/-- For `G ∈ ℱ_τ`, the event `{σ < ⊤, θ_σ ω ∈ G}` lies in `ℱ_{σ + τ ∘ θ_σ}`. -/
theorem measurableSet_thenTime_of_stopShift
    (hσ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) σ)
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) τ) {G : Set (ℕ → S)}
    (hG : MeasurableSet[hτ.measurableSpace] G) :
    MeasurableSet[(isStoppingTime_thenTime hσ hτ).measurableSpace]
      ({ω | σ ω < ⊤} ∩ stopShift σ ⁻¹' G) := by
  refine ⟨?_, fun n => ?_⟩
  · rw [iSup_piLE]
    exact ((measurable_of_isStoppingTime hσ)
      (MeasurableSet.of_discrete : MeasurableSet {x : ℕ∞ | x < ⊤})).inter
      (measurable_stopShift (measurable_of_isStoppingTime hσ)
        (measurableSet_of_measurableSet_stopping hτ hG))
  · change MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n]
      (({ω | σ ω < ⊤} ∩ stopShift σ ⁻¹' G) ∩ {ω | thenTime σ τ ω ≤ n})
    rw [inter_thenTime_le_eq]
    refine Finset.measurableSet_biUnion _ fun j hj => ?_
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    refine (measurableSet_piLE_mono hjn (hσ.measurableSet_eq j)).inter ?_
    have := measurableSet_piLE_walkShift_preimage (j := j) (hG.2 (n - j))
    rwa [Nat.add_sub_cancel' hjn] at this

/-- Past events of `σ` are past events of `σ + τ ∘ θ_σ`: `ℱ_σ ≤ ℱ_{thenTime σ τ}`. -/
theorem measurableSpace_le_thenTime
    (hσ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) σ)
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) τ) :
    hσ.measurableSpace ≤ (isStoppingTime_thenTime hσ hτ).measurableSpace :=
  IsStoppingTime.measurableSpace_mono hσ _ le_thenTime

end ThenTime

end MatedCRTHarmonic.Markov
