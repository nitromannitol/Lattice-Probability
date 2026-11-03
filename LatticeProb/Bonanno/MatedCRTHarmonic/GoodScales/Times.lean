/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GoodScales.Times at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GoodScales.Geometry
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.StrongMarkov
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.HitTime
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Disconnects
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.AnnularEvent

/-!
# Scale times and scale successes for the good-scales estimate (the scale-time argument)

For plane data `J`, a centre `z` and radii `r`, with `C_j = V_K(∂B_{r_j}(z))` (`scaleSet`) and
`W_j = V_K(A_{r_j/2, 3r_j/2}(z))` (`bandSet`), we define on edge-end paths

* `sig j`: `sig 0` is the first visit to `C_0`; `sig (j+1)` is the first visit to `C_{j+1}` at or
  after `exitAfter j`;
* `exitAfter j`: the first exit from `W_j` at or after `sig j`;
* `scaleSuccess j = {sig j < ⊤, θ_{sig j} ω ∈ succEvent j}`: the annular event
  for the path restarted at `sig j`;
* `reach j = {sig j < ⊤} ∩ ⋂_{i<j} (scaleSuccess i)ᶜ` (0-indexed).

Defining `sig (j+1)` after `exitAfter j` (instead of the first visit to `C_{j+1}`) makes the times
increase on every path, so `scaleSuccess i` is an event of `ℱ_{sig j}` for `i < j` without the
geometric ordering A2; the geometry is only used on the paths that matter (`sig_lt_of_entry`).

Main results: stopping-time and measurability facts; `sig_lt_of_entry` (every scale time comes
before a first entry at `v`, the good-scale argument A3 Claim 1); `scaleSuccess_hits` and
`notMem_scaleSuccess_of_entry` (a success hits `A` inside the annulus, so it excludes a first
entry at `v`, the good-scale argument A3 Claim 2).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GoodScales

open Markov

variable {V E : Type*}

/-! ### Two facts about `thenTime σ (hitTime B)` -/

section ThenHit

variable {S : Type*} {σ : (ℕ → S) → ℕ∞} {B : Set S} {ω : ℕ → S}

/-- The first visit to `B` at or after `σ` is no later than any visit to `B` after `σ`. -/
theorem thenTime_hitTime_le_of_mem {m : ℕ} (hσ : σ ω ≤ m) (hm : ω m ∈ B) :
    thenTime σ (hitTime B) ω ≤ m := by
  have hne : σ ω ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top m) hσ
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  have hkm : k ≤ m := by
    rw [← hk] at hσ
    exact_mod_cast hσ
  rw [thenTime_eq_of_eq hk.symm]
  have hmem : walkShift k ω (m - k) ∈ B := by
    rw [walkShift_apply, Nat.add_sub_cancel' hkm]
    exact hm
  calc (k : ℕ∞) + hitTime B (walkShift k ω) ≤ (k : ℕ∞) + ((m - k : ℕ) : ℕ∞) := by
        gcongr
        exact hitTime_le_of_mem hmem
    _ = m := by exact_mod_cast Nat.add_sub_cancel' hkm

/-- The value `t` of the first visit to `B` at or after `σ`: `σ ≤ t`, `ω t ∈ B`, and `ω m ∉ B` for
`σ ≤ m < t`. -/
theorem thenTime_hitTime_spec {t : ℕ} (h : thenTime σ (hitTime B) ω = t) :
    σ ω ≤ t ∧ ω t ∈ B ∧ ∀ m : ℕ, σ ω ≤ m → m < t → ω m ∉ B := by
  have hσ : σ ω ≠ ⊤ := fun h' => by
    rw [thenTime_eq_top_of_eq_top h'] at h
    exact ENat.natCast_ne_top t h.symm
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hσ
  rw [thenTime_eq_of_eq hk.symm] at h
  have hτ : hitTime B (walkShift k ω) ≠ ⊤ := fun h' => by
    rw [h', add_top] at h
    exact ENat.natCast_ne_top t h.symm
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hτ
  rw [← hn] at h
  have hkn : k + n = t := by exact_mod_cast h
  obtain ⟨hmem, hmin⟩ := hitTime_eq_coe_iff.mp hn.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [← hk]
    exact_mod_cast (show k ≤ t by omega)
  · rw [← hkn]
    exact hmem
  · intro m hm hmt
    rw [← hk] at hm
    have hkm : k ≤ m := by exact_mod_cast hm
    have := hmin (m - k) (by omega)
    rwa [walkShift_apply, Nat.add_sub_cancel' hkm] at this

/-- If `ω` and `ω'` agree up to time `n` and `τ_B ω = n`, then `τ_B ω' = n`. -/
theorem hitTime_eq_of_forall_eq {ω' : ℕ → S} {n : ℕ} (hn : hitTime B ω = n)
    (h : ∀ m ≤ n, ω m = ω' m) : hitTime B ω' = n := by
  rw [hitTime_eq_coe_iff] at hn ⊢
  refine ⟨?_, fun i hi => ?_⟩
  · rw [← h n le_rfl]
    exact hn.1
  · rw [← h i hi.le]
    exact hn.2 i hi

end ThenHit

/-! ### The sets and times -/

section Defs

variable (G : LFMultigraph V E) (J : V → Set ℂ) (z : ℂ) (r : ℕ → ℝ)

/-- The states whose vertex lies in `B`. -/
def vset (B : Set V) : Set G.State := G.stateVertex ⁻¹' B

/-- `C_j = V_K(∂B_{r_j}(z))`. -/
def scaleSet (j : ℕ) : Set V := verticesMeeting J (sphere z (r j))

/-- `W_j = V_K(A_{r_j/2, 3r_j/2}(z))`. -/
def bandSet (j : ℕ) : Set V := verticesMeeting J (annulus z (r j / 2) (3 * r j / 2))

/-- The scale times: `sig 0` is the first visit to `C_0`; `sig (j+1)` is the first visit to
`C_{j+1}` at or after the first exit from `W_j` following `sig j`. -/
def sig : ℕ → (ℕ → G.State) → ℕ∞
  | 0 => hitTime (vset G (scaleSet J z r 0))
  | j + 1 => thenTime (thenTime (sig j) (hitTime (vset G ((bandSet J z r j)ᶜ))))
      (hitTime (vset G (scaleSet J z r (j + 1))))

/-- `T_j`: the first exit from `W_j` at or after `sig j`. -/
def exitAfter (j : ℕ) : (ℕ → G.State) → ℕ∞ :=
  thenTime (sig G J z r j) (hitTime (vset G ((bandSet J z r j)ᶜ)))

/-- The success event at scale `j`, for a path started at `C_j`. -/
def succEvent (j : ℕ) : Set (ℕ → G.State) := {ω | G.AnnularEvent J z (r j) (G.vertexPath ω)}

/-- `D_j`: success at scale `j` for the path restarted at `sig j`. -/
def scaleSuccess (j : ℕ) : Set (ℕ → G.State) :=
  {ω | sig G J z r j ω < ⊤} ∩ stopShift (sig G J z r j) ⁻¹' succEvent G J z r j

/-- Scale `j` is reached after failing at the scales `< j`. -/
def reach (j : ℕ) : Set (ℕ → G.State) :=
  {ω | sig G J z r j ω < ⊤ ∧ ∀ i < j, ω ∉ scaleSuccess G J z r i}

theorem sig_zero : sig G J z r 0 = hitTime (vset G (scaleSet J z r 0)) := rfl

theorem sig_succ (j : ℕ) :
    sig G J z r (j + 1) = thenTime (exitAfter G J z r j) (hitTime (vset G (scaleSet J z r (j + 1)))) :=
  rfl

theorem hitTime_vset (B : Set V) (ω : ℕ → G.State) :
    hitTime (vset G B) ω = hitTime B (G.vertexPath ω) := rfl

theorem vertexPath_walkShift (k : ℕ) (ω : ℕ → G.State) (m : ℕ) :
    G.vertexPath (walkShift k ω) m = G.vertexPath ω (k + m) := rfl

end Defs

variable {G : LFMultigraph V E} {J : V → Set ℂ} {z : ℂ} {r : ℕ → ℝ}

/-! ### Stopping times and order -/

theorem isStoppingTime_hitTime_vset (B : Set V) :
    IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => G.State)) (hitTime (vset G B)) :=
  isStoppingTime_hitTime MeasurableSet.of_discrete

theorem isStoppingTime_sig :
    ∀ j, IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => G.State)) (sig G J z r j)
  | 0 => isStoppingTime_hitTime_vset _
  | j + 1 => isStoppingTime_thenTime
      (isStoppingTime_thenTime (isStoppingTime_sig j) (isStoppingTime_hitTime_vset _))
      (isStoppingTime_hitTime_vset _)

theorem isStoppingTime_exitAfter (j : ℕ) :
    IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => G.State)) (exitAfter G J z r j) :=
  isStoppingTime_thenTime (isStoppingTime_sig j) (isStoppingTime_hitTime_vset _)

theorem sig_le_exitAfter (j : ℕ) : sig G J z r j ≤ exitAfter G J z r j := le_thenTime

theorem exitAfter_le_sig_succ (j : ℕ) : exitAfter G J z r j ≤ sig G J z r (j + 1) := le_thenTime

theorem sig_mono : Monotone (sig G J z r) :=
  monotone_nat_of_le_succ fun j => (sig_le_exitAfter j).trans (exitAfter_le_sig_succ j)

/-- At a finite scale time `sig j` the walk is in `C_j`. -/
theorem stopState_sig_mem {j : ℕ} {ω : ℕ → G.State} (h : sig G J z r j ω < ⊤) :
    stopState (sig G J z r j) ω ∈ vset G (scaleSet J z r j) := by
  cases j with
  | zero => exact stopState_hitTime_mem h.ne
  | succ j =>
    rw [sig_succ] at h ⊢
    rw [stopState_thenTime h.ne]
    exact stopState_hitTime_mem (thenTime_lt_top_iff.mp h).2.ne

/-! ### Measurability -/

/-- `{τ < ⊤}` is an event of `ℱ_τ`. -/
theorem measurableSet_lt_top_stopping {S : Type*} [MeasurableSpace S] {τ : (ℕ → S) → ℕ∞}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) τ) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω < ⊤} := by
  refine measurableSet_stopping_of_forall_eq hτ
    (measurable_of_isStoppingTime hτ (MeasurableSet.of_discrete : MeasurableSet {x : ℕ∞ | x < ⊤}))
    ?_
  intro ω ω' hlt hagree _
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hlt.ne
  have h' : τ ω' = k := eq_of_isStoppingTime_of_forall_eq hτ hk.symm fun m hm =>
    hagree m (by rw [← hk]; exact_mod_cast hm)
  show τ ω' < ⊤
  rw [h']
  exact ENat.natCast_lt_top k

/-- The annular event is determined by the path up to its exit time. -/
theorem annularEvent_of_forall_eq {ρ : ℝ} {X X' : ℕ → V} {n : ℕ}
    (hn : hitTime (verticesMeeting J (annulus z (ρ / 2) (3 * ρ / 2)))ᶜ X = n)
    (hagree : ∀ m ≤ n, X m = X' m) (h : G.AnnularEvent J z ρ X) : G.AnnularEvent J z ρ X' := by
  obtain ⟨τ, hτ, hdisc, hcont⟩ := h
  have hτn : τ = n := by
    rw [hτ] at hn
    exact_mod_cast hn
  subst hτn
  refine ⟨τ, hitTime_eq_of_forall_eq hτ hagree, ?_, fun m hm => ?_⟩
  · have hset : {y | ∃ m < τ, X' m = y} = {y | ∃ m < τ, X m = y} := by
      ext y
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨m, hm, rfl⟩
        exact ⟨m, hm, hagree m hm.le⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨m, hm, (hagree m hm.le).symm⟩
    rw [hset]
    exact hdisc
  · rw [← hagree m hm]
    exact hcont m hm

theorem succEvent_eq_iUnion (j : ℕ) :
    succEvent G J z r j = ⋃ n : ℕ, (succEvent G J z r j ∩
      {ω | hitTime (vset G ((bandSet J z r j)ᶜ)) ω = n}) := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨τ, hτ, hd, hc⟩
    exact ⟨τ, ⟨τ, hτ, hd, hc⟩, hτ⟩
  · rintro ⟨n, h, -⟩
    exact h

theorem measurableSet_succEvent [Countable G.State] (j : ℕ) :
    MeasurableSet (succEvent G J z r j) := by
  rw [succEvent_eq_iUnion]
  refine MeasurableSet.iUnion fun n => measurableSet_of_forall_eq_le n ?_
  rintro ω ω' hagree ⟨hω, hn⟩
  exact ⟨annularEvent_of_forall_eq hn (fun m hm => congrArg G.stateVertex (hagree m hm)) hω,
    hitTime_eq_of_forall_eq hn hagree⟩

/-- The success event is an event of the exit time from the band. -/
theorem measurableSet_succEvent_stopping [Countable G.State] (j : ℕ) :
    MeasurableSet[(isStoppingTime_hitTime_vset (G := G) ((bandSet J z r j)ᶜ)).measurableSpace]
      (succEvent G J z r j) := by
  refine measurableSet_stopping_of_forall_eq _ (measurableSet_succEvent j) ?_
  intro ω ω' hlt hagree hω
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hlt.ne
  exact annularEvent_of_forall_eq hn.symm
    (fun m hm => congrArg G.stateVertex (hagree m (by rw [← hn]; exact_mod_cast hm))) hω

theorem measurableSet_scaleSuccess_exitAfter [Countable G.State] (i : ℕ) :
    MeasurableSet[(isStoppingTime_exitAfter (G := G) (J := J) (z := z) (r := r) i).measurableSpace]
      (scaleSuccess G J z r i) :=
  measurableSet_thenTime_of_stopShift (isStoppingTime_sig i) (isStoppingTime_hitTime_vset _)
    (measurableSet_succEvent_stopping i)

/-- `D_i` is an event of `ℱ_{sig j}` for `i < j`. -/
theorem measurableSet_scaleSuccess_sig [Countable G.State] {i j : ℕ} (hij : i < j) :
    MeasurableSet[(isStoppingTime_sig (G := G) (J := J) (z := z) (r := r) j).measurableSpace]
      (scaleSuccess G J z r i) := by
  have h1 := IsStoppingTime.measurableSpace_mono (isStoppingTime_exitAfter (G := G) (J := J)
    (z := z) (r := r) i) (isStoppingTime_sig (i + 1)) (exitAfter_le_sig_succ i)
  have h2 := IsStoppingTime.measurableSpace_mono (isStoppingTime_sig (G := G) (J := J) (z := z)
    (r := r) (i + 1)) (isStoppingTime_sig j) (sig_mono (Nat.succ_le_of_lt hij))
  exact h2 _ (h1 _ (measurableSet_scaleSuccess_exitAfter i))

theorem measurableSet_scaleSuccess [Countable G.State] (i : ℕ) :
    MeasurableSet (scaleSuccess G J z r i) :=
  measurableSet_of_measurableSet_stopping (isStoppingTime_exitAfter i)
    (measurableSet_scaleSuccess_exitAfter i)

/-- `reach j` is an event of `ℱ_{sig j}`. -/
theorem measurableSet_reach [Countable G.State] (j : ℕ) :
    MeasurableSet[(isStoppingTime_sig (G := G) (J := J) (z := z) (r := r) j).measurableSpace]
      (reach G J z r j) := by
  have hset : reach G J z r j = {ω | sig G J z r j ω < ⊤} ∩
      ⋂ i, ⋂ (_ : i < j), (scaleSuccess G J z r i)ᶜ := by
    ext ω
    simp only [reach, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff]
  rw [hset]
  exact (measurableSet_lt_top_stopping (isStoppingTime_sig j)).inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun hi =>
      (measurableSet_scaleSuccess_sig hi).compl)

theorem measurableSet_reach' [Countable G.State] (j : ℕ) : MeasurableSet (reach G J z r j) :=
  measurableSet_of_measurableSet_stopping (isStoppingTime_sig j) (measurableSet_reach j)

/-! ### Order facts for `reach` -/

theorem reach_anti {i j : ℕ} (hij : j ≤ i) : reach G J z r i ⊆ reach G J z r j := by
  rintro ω ⟨hlt, hfail⟩
  exact ⟨lt_of_le_of_lt (sig_mono hij ω) hlt, fun l hl => hfail l (by omega)⟩

theorem reach_inter_scaleSuccess_eq (j : ℕ) :
    reach G J z r j ∩ {ω | sig G J z r j ω < ⊤} ∩ stopShift (sig G J z r j) ⁻¹' succEvent G J z r j =
      reach G J z r j ∩ scaleSuccess G J z r j := by
  ext ω
  simp only [reach, scaleSuccess, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h1.1, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

theorem reach_inter_lt_top (j : ℕ) :
    reach G J z r j ∩ {ω | sig G J z r j ω < ⊤} = reach G J z r j :=
  Set.inter_eq_left.mpr fun _ h => h.1

/-! ### Geometry along the walk -/

variable {A : Finset V} {v : V} {K : ℕ} {p : ℝ}

end MatedCRTHarmonic.GoodScales
