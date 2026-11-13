/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Recurrence.CountableTargetExcursion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.ExcursionEnergy

/-!
# The excursion energy bound for an arbitrary (countable) target

`Recurrence/ExcursionEnergy.lean` proves the excursion identity and the finite-energy bound
`P_o[τ_F < τ_o⁺] ≤ E(f)/π(o)` for a **finite** target `F`, where the event is described through
the first hitting time of the finite set `A = {o} ∪ F` at or after the departure time `σ_o`.

The recurrence/log-cutoff consumer needs the same bound for an **arbitrary** target `S ⊆ VG`
(all targets are countable, `V` being countable), e.g. the complement of a ball or the vertex
set of a branch of the graph.  For such an `S` neither the hitting time of `S` nor the value of
the process at it is available: the infimum `inf {t ≥ σ_o : X_t ∈ S}` need not be attained, and
even where it is attained the value need not lie in `S`.  Accordingly the event here is
*defined* pathwise, with no hitting-time attainment for `S`:

`visitsTargetBeforeReturn 𝓧 o S` = there is a time `t ≥ σ_o` with `X_t ∈ S` and with
`X_s ≠ o` for **every** `s ∈ [σ_o, t]`.

The departure time `σ_o` is the property-(iii) exit time `exitTime 𝓧.X o` (first time the
process leaves `o`), and the "no return" requirement is a condition on the whole interval
`[σ_o, t]`; first exit and first return are kept strictly apart.

The results are:

* `visitsTargetBeforeReturn_eq_iUnion_finsetSubset` — the arbitrary-target event is the
  **exact** union of its finite-target versions over the (countable, directed) family of finite
  subsets of `S`;
* `departureHitsTarget_subset_visitsTargetBeforeReturn` — every finite-target excursion event
  of `ExcursionEnergy` is contained in the pathwise event (exact, no null sets);
* `visitsTargetBeforeReturn_ae_eq_departureHitsTarget` — for a finite target the two agree
  almost surely, the missing inclusion being exactly the a.s. attainment of the hitting time of
  the finite set `{o} ∪ F` (`mem_of_hittingAfter_eq_of_rightRegular`);
* `measure_visitsTargetBeforeReturn_le_energy_div` — the bound `E(f)/π(o)`, obtained from the
  finite-target bound by continuity from below along the directed family.

The competitor `f` ranges over the full finite-energy space: no summable speed, finite support,
decay at infinity or finite-support closure is imposed, and `f` is only required to vanish at
`o` and to equal `1` on `S`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ReflectedWalk ReflectedWalk.Theorem16
open scoped NNReal ENNReal

namespace ReflectedGMS.CountableTargetExcursion

variable {V : Type*}

/-- **The arbitrary-target excursion event.**  The process visits the target set `S` at some
time `t` at or after the departure time `σ_o = exitTime 𝓧.X o`, and does not return to `o`
at any time of `[σ_o, t]`.

No hitting time of `S` and no attainment of one is used: the visit is witnessed by an explicit
time `t`, and "before the return to `o`" is the pointwise condition `X_s ≠ o` on `[σ_o, t]`. -/
def visitsTargetBeforeReturn (𝓧 : ProcessFamily V) (o : V) (S : Set V) : Set 𝓧.Ω :=
  {ω | ∃ t : ℝ≥0, (exitTime 𝓧.X o ω).untopA ≤ t ∧
      (∃ y ∈ S, 𝓧.X t ω = some y) ∧
      ∀ s : ℝ≥0, (exitTime 𝓧.X o ω).untopA ≤ s → s ≤ t → 𝓧.X s ω ≠ some o}

/-- The event is monotone in the target. -/
theorem visitsTargetBeforeReturn_mono (𝓧 : ProcessFamily V) (o : V) {S S' : Set V}
    (hSS' : S ⊆ S') : visitsTargetBeforeReturn 𝓧 o S ⊆ visitsTargetBeforeReturn 𝓧 o S' := by
  rintro ω ⟨t, hσt, ⟨y, hyS, hy⟩, hno⟩
  exact ⟨t, hσt, ⟨y, hSS' hyS, hy⟩, hno⟩

/-- **The exact exhaustion by finite targets.**  A visit to `S` before the return to `o` is a
visit to some finite subset of `S` before the return to `o`, and conversely.  This is an
equality of sets, not an almost-sure identity. -/
theorem visitsTargetBeforeReturn_eq_iUnion_finsetSubset (𝓧 : ProcessFamily V) (o : V)
    (S : Set V) :
    visitsTargetBeforeReturn 𝓧 o S =
      ⋃ i : {F : Finset V // (F : Set V) ⊆ S},
        visitsTargetBeforeReturn 𝓧 o ((i : Finset V) : Set V) := by
  ext ω
  constructor
  · rintro ⟨t, hσt, ⟨y, hyS, hy⟩, hno⟩
    refine Set.mem_iUnion.2 ⟨⟨{y}, ?_⟩, t, hσt, ⟨y, ?_, hy⟩, hno⟩
    · intro x hx
      rw [Finset.coe_singleton, Set.mem_singleton_iff] at hx
      exact hx ▸ hyS
    · simp
  · intro hω
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hω
    exact visitsTargetBeforeReturn_mono 𝓧 o i.2 hi

section Process

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer} {𝓧 : ProcessFamily V}
  [Countable V]

/-- **The almost-sure converse for a finite target.**  A visit to the finite set `F` before the
return to `o` forces the hitting time of `{o} ∪ F` after the departure to be finite, and at a
regular outcome that hitting time is attained (`mem_of_hittingAfter_eq_of_rightRegular`); the
value there cannot be `o`, because it occurs inside the interval on which the path avoids `o`.
This is the only place where a null set is discarded. -/
theorem visitsTargetBeforeReturn_ae_le_departureHitsTarget (h : IsReflectedWalk G w hmin 𝓧)
    {o : V} {F : Finset V} (hoF : o ∉ F) :
    visitsTargetBeforeReturn 𝓧 o (F : Set V) ≤ᵐ[𝓧.P o]
      ExcursionEnergy.departureHitsTarget 𝓧 o (Finset.cons o F hoF) F := by
  filter_upwards [ae_rightRegularAt (h o).2.2.1 (h o).2.2.2.1] with ω hω hmem
  obtain ⟨t, hσt, ⟨y, hyF, hXt⟩, hno⟩ := hmem
  have hmemA : 𝓧.X t ω ∈ some '' ((Finset.cons o F hoF : Finset V) : Set V) :=
    ⟨y, Finset.mem_coe.2 (Finset.mem_cons_of_mem (Finset.mem_coe.1 hyF)), hXt.symm⟩
  have hle : hittingAfter 𝓧.X (some '' ((Finset.cons o F hoF : Finset V) : Set V))
      (exitTime 𝓧.X o ω).untopA ω ≤ ((t : ℝ≥0) : WithTop ℝ≥0) :=
    hittingAfter_le_of_mem hσt hmemA
  have hne : hittingAfter 𝓧.X (some '' ((Finset.cons o F hoF : Finset V) : Set V))
      (exitTime 𝓧.X o ω).untopA ω ≠ ⊤ := by
    intro htop
    rw [htop] at hle
    exact (not_le.2 (WithTop.coe_lt_top t)) hle
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
  have hτr : hittingAfter 𝓧.X (some '' ((Finset.cons o F hoF : Finset V) : Set V))
      (exitTime 𝓧.X o ω).untopA ω = ((r : ℝ≥0) : WithTop ℝ≥0) := hr.symm
  have hrt : r ≤ t := by rw [hτr] at hle; exact_mod_cast hle
  have hσr : (exitTime 𝓧.X o ω).untopA ≤ r := by
    have h1 : (((exitTime 𝓧.X o ω).untopA : ℝ≥0) : WithTop ℝ≥0) ≤
        hittingAfter 𝓧.X (some '' ((Finset.cons o F hoF : Finset V) : Set V))
          (exitTime 𝓧.X o ω).untopA ω := le_hittingAfter ω
    rw [hτr] at h1
    exact_mod_cast h1
  obtain ⟨z, hzA, hz⟩ :=
    mem_of_hittingAfter_eq_of_rightRegular hω
      (admissibleTarget_image (Finset.cons o F hoF)) hτr
  have hzo : z ≠ o := by
    rintro rfl
    exact hno r hσr hrt hz.symm
  have hzF : z ∈ F := (Finset.mem_cons.1 (Finset.mem_coe.1 hzA)).resolve_left hzo
  have hval : stoppedValue 𝓧.X
      (ExcursionEnergy.postDepartureHitTime 𝓧 o (Finset.cons o F hoF)) ω = some z := by
    show 𝓧.X (ExcursionEnergy.postDepartureHitTime 𝓧 o (Finset.cons o F hoF) ω).untopA ω =
      some z
    have hpd : ExcursionEnergy.postDepartureHitTime 𝓧 o (Finset.cons o F hoF) ω =
        ((r : ℝ≥0) : WithTop ℝ≥0) := hτr
    rw [hpd, untopA_coe]
    exact hz.symm
  exact ⟨hne, z, hzF, hval⟩

/-- The finite-target case of the bound, in `ℝ≥0∞`. -/
theorem measure_visitsTargetBeforeReturn_finset_le_ofReal (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) {o : V} {F : Finset V} (hoF : o ∉ F)
    {f : V → ℝ} (hf : G.HasFiniteEnergy f) (hfo : f o = 0) (hfF : ∀ y ∈ F, f y = 1) :
    𝓧.P o (visitsTargetBeforeReturn 𝓧 o (F : Set V)) ≤
      ENNReal.ofReal (G.Energy f / G.pi o) := by
  have hnn : 0 ≤ G.Energy f / G.pi o := div_nonneg (G.Energy_nonneg f) (G.pi_nonneg o)
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · have hempty : visitsTargetBeforeReturn 𝓧 o (∅ : Set V) = ∅ := by
      ext ω
      constructor
      · rintro ⟨-, -, ⟨y, hy, -⟩, -⟩
        exact hy.elim
      · intro hω
        exact hω.elim
    rw [Finset.coe_empty, hempty, measure_empty]
    simp
  · refine le_trans
      (measure_mono_ae (visitsTargetBeforeReturn_ae_le_departureHitsTarget h hoF)) ?_
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hnn]
    exact ExcursionEnergy.measure_departureHitsTarget_le_energy_div h hG hFne
      (Finset.mem_cons_self o F) hoF (fun y hy => Finset.mem_cons_of_mem hy)
      (fun y hy hyo => (Finset.mem_cons.1 hy).resolve_left hyo) hf hfo hfF

/-- **The arbitrary-target excursion bound.**  For every target `S` with `o ∉ S` and every
finite-energy `f` with `f(o) = 0` and `f ≡ 1` on `S`,

  `P_o[ the walk visits S before returning to o ] ≤ E(f)/π(o)`.

The proof is continuity from below along the directed family of finite subsets of `S`, each
term being the finite-target bound of `ExcursionEnergy`.  The competitor class is the full
finite-energy space, and no first-hit attainment for the infinite target is used. -/
theorem measure_visitsTargetBeforeReturn_le_ofReal_energy_div (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) {o : V} {S : Set V} (hoS : o ∉ S)
    {f : V → ℝ} (hf : G.HasFiniteEnergy f) (hfo : f o = 0) (hfS : ∀ y ∈ S, f y = 1) :
    𝓧.P o (visitsTargetBeforeReturn 𝓧 o S) ≤ ENNReal.ofReal (G.Energy f / G.pi o) := by
  classical
  have hdir : Directed (· ⊆ ·) (fun i : {F : Finset V // (F : Set V) ⊆ S} =>
      visitsTargetBeforeReturn 𝓧 o ((i : Finset V) : Set V)) := by
    rintro ⟨F, hF⟩ ⟨F', hF'⟩
    refine ⟨⟨F ∪ F', ?_⟩, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hx) with hx' | hx'
      · exact hF (Finset.mem_coe.2 hx')
      · exact hF' (Finset.mem_coe.2 hx')
    · exact visitsTargetBeforeReturn_mono 𝓧 o
        (fun x hx => Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hx)))
    · exact visitsTargetBeforeReturn_mono 𝓧 o
        (fun x hx => Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 hx)))
  rw [visitsTargetBeforeReturn_eq_iUnion_finsetSubset 𝓧 o S, hdir.measure_iUnion]
  refine iSup_le fun i => measure_visitsTargetBeforeReturn_finset_le_ofReal h hG
    (fun hoF => hoS (i.2 (Finset.mem_coe.2 hoF))) hf hfo
    (fun y hy => hfS y (i.2 (Finset.mem_coe.2 hy)))

end Process

end ReflectedGMS.CountableTargetExcursion
