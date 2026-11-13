/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.CoordinateLocallySquareIntegrableLocalizer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedFormAssociationFastStopped
import LatticeProb.Bonanno.ReflectedGMS.Process.AreaTimeChangeJumpLaw

/-!
# Step (d) of bracket atom 1: the exit times used as the localizing sequence

The localizing sequence of `CoordinateLocallySquareIntegrable` is the sequence of exit times
`σ_n = StoppedFormAssociation.exitHitting` of the **area** path from the growing regions
`A_n = {‖z‖ ≤ R_n/2}` of step (a).  This file collects the pathwise facts about exit times the
assembly needs, none of them probabilistic:

* `hittingAfter_zero_eq_map_symm` / `exitHitting_eq_map_symm` — under an order-isomorphic time
  change `X_t = Y_{e⁻¹ t}` the hitting time of `Y` is the image of that of `X`, so the fast
  exit is `e⁻¹(σ_n)`;
* `mem_of_lt_exitHitting` — before the exit, every vertex visited is in the region;
* `exitHitting_pos` — starting inside the region and right-constant there, the exit is
  positive;
* `exitHitting_mono` — the exit is monotone in the region;
* `tendsto_exitHitting_top` — if on every bounded time window the vertices visited lie in some
  region of the sequence, the exits tend to `⊤`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.CoordinateLocallySquareIntegrableLocalizer

open ReflectedWalk ReflectedGMS.StoppedFormAssociation

universe u

/-! ## Hitting times under an order-isomorphic time change -/

section Hitting

variable {Ω Ω' β : Type*}

/-- Under `X_t = Y_{e⁻¹ t}` along one sample, the hitting time of `Y` is `e⁻¹` of that of `X`. -/
theorem hittingAfter_zero_eq_map_symm (X : ℝ≥0 → Ω → β) (Y : ℝ≥0 → Ω' → β) (s : Set β)
    (ω : Ω) (ω' : Ω') (e : ℝ≥0 ≃o ℝ≥0) (hXY : ∀ t, X t ω = Y (e.symm t) ω') :
    hittingAfter Y s 0 ω' = WithTop.map e.symm (hittingAfter X s 0 ω) := by
  have hset : {i : ℝ≥0 | 0 ≤ i ∧ Y i ω' ∈ s} =
      (e.symm : ℝ≥0 → ℝ≥0) '' {i : ℝ≥0 | 0 ≤ i ∧ X i ω ∈ s} := by
    ext q
    constructor
    · rintro ⟨-, hq⟩
      refine ⟨e q, ⟨zero_le, ?_⟩, e.symm_apply_apply q⟩
      rw [hXY, e.symm_apply_apply]
      exact hq
    · rintro ⟨t, ⟨-, ht⟩, rfl⟩
      refine ⟨zero_le, ?_⟩
      rw [← hXY]
      exact ht
  simp only [hittingAfter_def]
  by_cases hex : ∃ j, 0 ≤ j ∧ X j ω ∈ s
  · have hexY : ∃ j, 0 ≤ j ∧ Y j ω' ∈ s := by
      obtain ⟨j, -, hj⟩ := hex
      exact ⟨e.symm j, zero_le, by rw [← hXY]; exact hj⟩
    have hne : {i : ℝ≥0 | 0 ≤ i ∧ X i ω ∈ s}.Nonempty := hex
    rw [if_pos hexY, if_pos hex, WithTop.map_coe, hset,
      AreaTimeChangeJumpLaw.csInf_image_orderIso e.symm hne]
  · have hexY : ¬ ∃ j, 0 ≤ j ∧ Y j ω' ∈ s := by
      rintro ⟨j, -, hj⟩
      exact hex ⟨e j, zero_le, by rw [hXY, e.symm_apply_apply]; exact hj⟩
    rw [if_neg hexY, if_neg hex]
    rfl

end Hitting

/-! ## Exit times -/

section Exit

variable {V : Type u}

/-- **The fast exit is the time-changed area exit.** -/
theorem exitHitting_eq_map_symm (PFa PFf : ProcessFamily V) (A : Set V) (ω : PFa.Ω)
    (ω' : PFf.Ω) (e : ℝ≥0 ≃o ℝ≥0) (hXY : ∀ t, PFa.X t ω = PFf.X (e.symm t) ω') :
    exitHitting PFf A ω' = WithTop.map e.symm (exitHitting PFa A ω) :=
  hittingAfter_zero_eq_map_symm PFa.X PFf.X _ ω ω' e hXY

/-- Before the exit, every vertex visited lies in the region. -/
theorem mem_of_lt_exitHitting (PF : ProcessFamily V) (A : Set V) (ω : PF.Ω) {r : ℝ≥0}
    (hr : (r : WithTop ℝ≥0) < exitHitting PF A ω) {v : V} (hv : PF.X r ω = some v) :
    v ∈ A := by
  by_contra hvA
  have hle : exitHitting PF A ω ≤ (r : WithTop ℝ≥0) :=
    hittingAfter_le_of_mem (u := PF.X) (s := some '' Aᶜ) zero_le ⟨v, hvA, hv.symm⟩
  exact absurd hr (not_lt.2 hle)

/-- Starting inside the region at a vertex where the path is right-constant, the exit is
positive. -/
theorem exitHitting_pos (PF : ProcessFamily V) (A : Set V) (ω : PF.Ω) {z : V} (hz : z ∈ A)
    (h0 : PF.X 0 ω = some z) {ε : ℝ≥0} (hε : 0 < ε)
    (hconst : ∀ s ∈ Ico (0 : ℝ≥0) (0 + ε), PF.X s ω = PF.X 0 ω) :
    0 < exitHitting PF A ω := by
  have hge : ((ε : ℝ≥0) : WithTop ℝ≥0) ≤ exitHitting PF A ω := by
    by_contra hlt
    push Not at hlt
    obtain ⟨j, hj, v, hvA, hv⟩ :=
      (hittingAfter_lt_iff (u := PF.X) (s := some '' Aᶜ) (n := 0)).1 hlt
    have hj' := hconst j ⟨hj.1, by simpa using hj.2⟩
    rw [h0, ← hv] at hj'
    exact hvA (Option.some_injective _ hj' ▸ hz)
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 hε) hge

/-- The exit time is monotone in the region. -/
theorem exitHitting_mono (PF : ProcessFamily V) {A B : Set V} (hAB : A ⊆ B) (ω : PF.Ω) :
    exitHitting PF A ω ≤ exitHitting PF B ω :=
  hittingAfter_apply_anti PF.X 0 ω (image_mono (compl_subset_compl.2 hAB))

/-- **Divergence of the exits.**  If on every bounded time window the vertices visited lie in
one region of an increasing sequence, the exit times from those regions tend to `⊤`. -/
theorem tendsto_exitHitting_top (PF : ProcessFamily V) (A : ℕ → Set V) (hA : Monotone A)
    (ω : PF.Ω)
    (hbd : ∀ T : ℝ≥0, ∃ n, ∀ t : ℝ≥0, t ≤ T → ∀ v, PF.X t ω = some v → v ∈ A n) :
    Tendsto (fun n => exitHitting PF (A n) ω) atTop (𝓝 ⊤) := by
  have hmono : Monotone (fun n => exitHitting PF (A n) ω) := fun n m hnm =>
    exitHitting_mono PF (hA hnm) ω
  have htop : (⨆ n, exitHitting PF (A n) ω) = ⊤ := by
    refine iSup_eq_top.2 fun b hb => ?_
    obtain ⟨T, rfl⟩ := WithTop.ne_top_iff_exists.1 hb.ne
    obtain ⟨n, hn⟩ := hbd (T + 1)
    refine ⟨n, ?_⟩
    have hge : ((T + 1 : ℝ≥0) : WithTop ℝ≥0) ≤ exitHitting PF (A n) ω := by
      by_contra hlt
      push Not at hlt
      obtain ⟨j, hj, v, hvA, hv⟩ :=
        (hittingAfter_lt_iff (u := PF.X) (s := some '' (A n)ᶜ) (n := 0)).1 hlt
      exact hvA (hn j hj.2.le v hv.symm)
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 (lt_add_one T)) hge
  have h := tendsto_atTop_iSup hmono
  rwa [htop] at h

end Exit

end ReflectedGMS.CoordinateLocallySquareIntegrableLocalizer
