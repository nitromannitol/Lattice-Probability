/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412gTrace at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate2FiltA
import LatticeProb.Bonanno.LQGMetric.Blueprint.CONFDefs

/-!
# GM L4.15 Step 4: events of `σ(𝓑^•_{σ_k}, h|)` on `{σ_k ≤ s}` (decision D98 (b))

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Lemma 4.15, Step 4, l. 2189–2191: "The radius `σ_k` is a stopping time for
`{(𝓑^•_s, h|_{𝓑^•_s})}_{s ≥ 0}`, so the event inside the conditional probability in (4.40′)
belongs to `σ(𝓑^•_{s_{k+1}}, h|_{𝓑^•_{s_{k+1}}})`."

* `p412gTraceSig`: the trace σ-algebra `{E | E ∩ C ∈ m}` (for `C ∈ m`).
* **`p412g_inter_localSigma`** (sure, abstract): if two random sets agree on `C` and
  `C ∈ σ(A', h|_{A'})`, then `E ∈ σ(A, h|_A)` gives `E ∩ C ∈ σ(A', h|_{A'})`.
* **`p412g_inter_aeSigma`**: composed with `gm_localSigma_le_aeSigma` (`A' ⊆ B`, hit events of `A'`
  piecewise local for `B`): `E ∩ C` is an event of the a.s.-completed `σ(B, h|_B)`.
* **`p412g_stop_inter`**: the filled-ball form (D98 (b)): for a `[0,∞]`-valued radius `σ`, a real
  `s`, `E ∈ filledBallSigmaAt σ` gives `E ∩ {σ ≤ s} ∈ gmAESigma σ(𝓑^•_s, h|)`, given the two
  stopping-time inputs `{σ ≤ s} ∈ σ(𝓑^•_{σ∧s}, h|)` and the piecewise locality of the hit events
  of `𝓑^•_{σ∧s}` for `𝓑^•_s` (GM's "`σ_k` is a stopping time"; D98 packet (b2)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory MeasurableSpace Set Filter
open scoped ENNReal
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

variable {Ω : Type}

/-- the trace σ-algebra `{E | E ∩ C ∈ m}` of `m` on an event `C ∈ m` -/
def p412gTraceSig (m : MeasurableSpace Ω) (C : Set Ω) (hC : MeasurableSet[m] C) :
    MeasurableSpace Ω where
  MeasurableSet' s := MeasurableSet[m] (s ∩ C)
  measurableSet_empty := by simpa only [empty_inter] using @MeasurableSet.empty Ω m
  measurableSet_compl s hs := by
    have e : sᶜ ∩ C = C \ (s ∩ C) := by
      ext ω
      simp only [mem_inter_iff, mem_compl_iff, mem_diff]
      tauto
    rw [e]
    exact @MeasurableSet.diff Ω m _ _ hC hs
  measurableSet_iUnion f hf := by
    rw [iUnion_inter]
    exact @MeasurableSet.iUnion Ω _ m _ _ hf

/-- on `{σ ≤ s}`, `𝓑^•_σ = 𝓑^•_{σ∧s}` -/
theorem p412g_filledBallE_eq (d : ContMetric) (z₀ : ℂ) {σ : ℝ≥0∞} {s : ℝ} (hs : 0 ≤ s)
    (hσ : σ ≤ ENNReal.ofReal s) : filledBallE d z₀ σ = filledBall d z₀ (min σ.toReal s) := by
  have hne : σ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hσ
  have hle : σ.toReal ≤ s := ENNReal.toReal_le_of_le_ofReal hs hσ
  rw [filledBallE, if_neg hne, min_eq_left hle]

end LQGMetric.GM
