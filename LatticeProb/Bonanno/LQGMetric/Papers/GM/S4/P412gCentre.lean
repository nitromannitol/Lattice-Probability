/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412gCentre at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412fSel
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412fHit
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEventRandom2

/-!
# GM L4.15 Step 3: centres from a random grid set with a.s.-local membership (decision D98)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Lemma 4.15, Step 3, l. 2159–2183: the points `z_y` are chosen "in a manner depending only
on `(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})`" and the union bound (4.40) runs over at most `ε^{-ω}` of them.

D98: the guard data is a random set `Q_k` of indices of a fixed countable grid `g : ℕ → ℂ`, whose
membership events `{i ∈ Q_k}` are a.s. events of `σ(K, h|_K)` (`K = 𝓑^•_{t_k}`) and with
`#Q_k ≤ N` a.s. CONF Lemma 3.6 (`CONFLem3_6At`) needs centres that are *surely*
`σ(K, h|_K)`-measurable and lie on `∂K` for every `ω`; this file produces `N` such centres.

* **`p412g_grid_centres`**: `x j` (`j ∈ ℕ`) surely `localSigma`-measurable, `x j ω ∈ ∂K(ω)`, and
  a.s. every `i ∈ Q_k(ω)` has some `j < N` with `x j ω ∈ cl B_ρ(g i)` whenever `∂K(ω)` meets
  `cl B_ρ(g i)` (the `j`-th element of `Q_k` in increasing order, through the measurable code of
  `exists_measurable_code`, and the frontier selections `p412f_frontier_select_near`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory MeasurableSpace Set Filter Metric
open scoped ENNReal
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

/-- the number of `true` coordinates below `i` is a measurable function of the code -/
theorem p412g_measurable_count (i : ℕ) :
    Measurable fun z : ℕ → Bool => Nat.count (fun k => z k = true) i := by
  have hr : Measurable fun z : ℕ → Bool => fun k : Fin i => z k :=
    measurable_pi_iff.mpr fun k => measurable_pi_apply (k : ℕ)
  have e : (fun z : ℕ → Bool => Nat.count (fun k => z k = true) i) =
      (fun w : Fin i → Bool => (Finset.univ.filter fun k : Fin i => w k = true).card) ∘
        (fun z : ℕ → Bool => fun k : Fin i => z k) := by
    funext z
    simp only [Function.comp_apply]
    rw [Nat.count_eq_card_filter_range]
    refine Finset.card_bij (fun a ha => ⟨a, Finset.mem_range.1 (Finset.mem_filter.1 ha).1⟩)
      (fun a ha => by simpa using (Finset.mem_filter.1 ha).2) (fun a _ b _ hab => by
        simpa using congrArg Fin.val hab) (fun b hb => ⟨b, by
          simpa using (Finset.mem_filter.1 hb).2, rfl⟩)
  rw [e]
  exact (measurable_of_countable _).comp hr

/-- the least index with code `true` and count `j` is the only one -/
theorem p412g_find_eq {z : ℕ → Bool} {i j : ℕ} (hi : z i = true)
    (hc : Nat.count (fun k => z k = true) i = j)
    (hx : ∃ i', z i' = true ∧ Nat.count (fun k => z k = true) i' = j) : Nat.find hx = i := by
  classical
  have hs := Nat.find_spec hx
  have hle : Nat.find hx ≤ i := Nat.find_min' hx ⟨hi, hc⟩
  rcases lt_or_eq_of_le hle with hlt | heq
  · have := Nat.count_strict_mono (p := fun k => z k = true) hs.1 hlt
    omega
  · exact heq

end LQGMetric.GM
