/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L45Meas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.SetupArc
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.SetupStop
import LatticeProb.Bonanno.LQGMetric.Prob.CondIndepDetermined

/-!
# GM Lemma 4.5 in σ-algebra form (packages E2a, E2b of `decisions/DEC-E.md` §3)

Source: GM = Gwynne–Miller, *Existence and uniqueness of the LQG metric*, arXiv:1905.00383,
`literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.5 (`lem-geo-sigma-algebra`) and its
proof, l. 1660–1676, with the remark l. 1654 ("by Axiom II (locality), `𝓘_k` is determined by
`𝓑^•_{t_k}` and `h|_{𝓑^•_{t_k}}`").

With `A := σ(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})` (`gmSigA`, the `localSigma` of the filled ball at the
random time `t_k`), `F := A ∨ σ(P|_{[0,s_k]})` (`gmSigF`) and
`F' := A ∨ σ(arc of 𝓘_k containing P(t_k))` (`gmSigF'`; the arc is `arcOf(P(s_k))` by
`gm_L4_5_arc_ae`, and a random set generates the σ-algebra of its hit events, as in `setSigma`):

* `gm_L4_5_E2a : AEDeterminedSigma F' F P` — the arc is `arcOf(P(s_k))`, `P(s_k)` is
  `F`-measurable, and the arc family is a function of `(𝓑^•_{t_k}, h|)` (`GMArcFamDet`).
* `gm_L4_5_E2b : AEDeterminedSigma F F' P` — GM's proof, l. 1665–1675: on `{𝕨 ∈ 𝓑^•_{t_k}}`
  the path is the (unique) geodesic to `𝕨`, determined by `(𝓑^•_{t_k}, h|)`; on the complement
  `P(s_k) ∈ Conf_k` is determined by the arc (`GMConfPtSel`) and `P|_{[0,s_k]}` is the unique
  geodesic from `𝕫` to `P(s_k)` (`gm_geodL_eqOn_of_unique`), determined by `(𝓑^•_{t_k}, h|)`
  through a measurable geodesic selection (`GMGeodSelDet`).

The three "determined by `(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})`" inputs `GMArcFamDet`, `GMGeodSelDet`,
`GMConfPtSel` are the instances of the general locality-measurability statement (an event or
object defined through the internal metric of `D_h` on the random local set `𝓑^•_{t_k}` is a.s.
`σ(𝓑^•_{t_k}, h|)`-measurable) which GM use without proof; they are explicit hypotheses here
(see `handoff/P2-E2a.md`). Everything else is proved. The generic σ-algebra facts
(`aeSigmaOf`: events a.s. equal to a `G`-event form a σ-algebra) are own elementary proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

set_option warn.classDefReducibility false

open MeasureTheory Filter Set MeasurableSpace
open LQGMetric.Blueprint

namespace LQGMetric.GM

section Generic
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- the events a.s. equal to an event of `G` form a σ-algebra -/
def aeSigmaOf (G : MeasurableSpace Ω) (μ : Measure[mΩ] Ω) : MeasurableSpace Ω where
  MeasurableSet' s := ∃ t, MeasurableSet[G] t ∧ s =ᵐ[μ] t
  measurableSet_empty := ⟨∅, MeasurableSet.empty, EventuallyEq.rfl⟩
  measurableSet_compl := fun _ ⟨t, ht, hst⟩ => ⟨tᶜ, ht.compl, EventuallyEqSet.compl hst⟩
  measurableSet_iUnion := fun f hf => by
    choose t ht hft using hf
    exact ⟨⋃ i, t i, MeasurableSet.iUnion ht, EventuallyEqSet.countable_iUnion hft⟩

theorem gm_aeDet_iff_le {A G : MeasurableSpace Ω} :
    AEDeterminedSigma A G μ ↔ A ≤ aeSigmaOf G μ := Iff.rfl

theorem gm_aeDet_sup {A B G : MeasurableSpace Ω} (hA : AEDeterminedSigma A G μ)
    (hB : AEDeterminedSigma B G μ) : AEDeterminedSigma (A ⊔ B) G μ :=
  gm_aeDet_iff_le.2 (sup_le (gm_aeDet_iff_le.1 hA) (gm_aeDet_iff_le.1 hB))

theorem gm_aeDet_of_le {A G : MeasurableSpace Ω} (h : A ≤ G) : AEDeterminedSigma A G μ :=
  fun s hs => ⟨s, h s hs, EventuallyEq.rfl⟩

/-- `σ(Y)` is a.s. determined by `G` if `Y` is a.s. equal to a `G`-measurable `Y'` -/
theorem gm_aeDet_comap {β : Type*} [mβ : MeasurableSpace β] {G : MeasurableSpace Ω}
    {Y Y' : Ω → β} (hY' : @Measurable Ω β G mβ Y') (h : Y =ᵐ[μ] Y') :
    AEDeterminedSigma (mβ.comap Y) G μ := by
  rintro _ ⟨B, hB, rfl⟩
  refine ⟨Y' ⁻¹' B, hY' hB, ?_⟩
  rw [eventuallyEqSet_iff]
  filter_upwards [h] with ω hω
  simp [hω]

/-- a family of events, as a `ℕ → Prop`-valued map, is measurable -/
theorem gm_measurable_pi_prop {Ω : Type*} (m : MeasurableSpace Ω) (f : Ω → ℕ → Prop)
    (hf : ∀ n, MeasurableSet[m] {ω | f ω n}) : @Measurable Ω (ℕ → Prop) m _ f := by
  let _ := m
  exact measurable_pi_iff.mpr fun n => measurableSet_setOfPred.mp (hf n)

end Generic

section GM
variable {Ω : Type}

/-- `σ(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})` -/
def gmSigA (D : DistC → ContMetric) (h : Ω → DistC) (𝕫 : ℂ) (tk : Ω → ℝ) : MeasurableSpace Ω :=
  localSigma h (fun ω => filledBall (D (h ω)) 𝕫 (tk ω))

/-- `P|_{[0,s_k]}`, reparametrized on `[0,1]`: `u ↦ P(s_k u)` (`P` = unit-speed form of `η`) -/
def gmPathK (D : DistC → ContMetric) (h : Ω → DistC) (𝕫 𝕨 : ℂ) (η : Ω → C(unitInterval, ℂ))
    (sk : Ω → ℝ) : Ω → unitInterval → ℂ :=
  fun ω u => geodL (D (h ω)) 𝕫 𝕨 (η ω) (sk ω * u)

/-- GM (4.8): `𝓕_k = σ(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}}, P|_{[0,s_k]})` -/
def gmSigF (D : DistC → ContMetric) (h : Ω → DistC) (𝕫 𝕨 : ℂ) (η : Ω → C(unitInterval, ℂ))
    (sk tk : Ω → ℝ) : MeasurableSpace Ω :=
  gmSigA D h 𝕫 tk ⊔ MeasurableSpace.comap (gmPathK D h 𝕫 𝕨 η sk) inferInstance

/-- the hit event `{arcOf(P(s_k)) ∩ U ≠ ∅}` -/
def gmArcHit (D : DistC → ContMetric) (h : Ω → DistC) (𝕫 𝕨 : ℂ) (η : Ω → C(unitInterval, ℂ))
    (sk tk : Ω → ℝ) (U : Set ℂ) : Set Ω :=
  {ω | (arcOf (D (h ω)) 𝕫 (tk ω) (geodL (D (h ω)) 𝕫 𝕨 (η ω) (sk ω)) ∩ U).Nonempty}

/-- GM (4.9): `σ(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}}, arc of 𝓘_k containing P(t_k))`, the arc being
`arcOf(P(s_k))` (`gm_L4_5_arc_ae`) and generating the σ-algebra of its hit events -/
def gmSigF' (D : DistC → ContMetric) (h : Ω → DistC) (𝕫 𝕨 : ℂ) (η : Ω → C(unitInterval, ℂ))
    (sk tk : Ω → ℝ) : MeasurableSpace Ω :=
  gmSigA D h 𝕫 tk ⊔ generateFrom {E | ∃ U : Set ℂ, IsOpen U ∧ E = gmArcHit D h 𝕫 𝕨 η sk tk U}

variable {D : DistC → ContMetric} {h : Ω → DistC} {𝕫 𝕨 : ℂ} {η : Ω → C(unitInterval, ℂ)}
  {sk tk : Ω → ℝ}

/-- `{𝕨 ∈ 𝓑^•_{t_k}} ∈ σ(𝓑^•_{t_k})` (Effros step for the closed set `{𝕨}`) -/
theorem gm_mem_filledBall_measurable (w : ℂ) :
    MeasurableSet[gmSigA D h 𝕫 tk] {ω | w ∈ filledBall (D (h ω)) 𝕫 (tk ω)} := by
  have e : {ω | w ∈ filledBall (D (h ω)) 𝕫 (tk ω)} =
      {ω | (filledBall (D (h ω)) 𝕫 (tk ω) ∩ {w}).Nonempty} := by
    ext ω
    simp only [mem_ofPred_eq, inter_singleton_nonempty]
  rw [e]
  exact gm_setSigma_le_localSigma h _ _
    (gm_setSigma_hit_closed (fun ω => gm_filledBall_isClosed _ _ _) isClosed_singleton)

end GM

end LQGMetric.GM
