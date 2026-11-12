/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7L2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7L1
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P1A

/-!
# LM Theorem 1.7 from the conditional variance bound (packet P-LIM, DEC-107 §3(vi))

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), Theorem 1.7 (l. 306–311), proof l. 1000–1089, repaired by decision
D107 (`decisions/DEC-107.md` §3).

**Why a kernel form of N-VAR.** The node `LMT17VarNode` (Papers/LM/T1_7D1.lean) is stated with
unconditional Bochner integrals `∫ (F_{n+1} − E[F_{n+1}|h])² dP ≤ ∫ C(h)⁴ (F_n − F_{n+1}) F_{n+1} dP`.
Nothing in the hypotheses of `LMThm1_7` makes `C(h)⁴ F_n²` (or even `F_n`) integrable — `C` may
be replaced by any larger measurable function of `h` — and then both sides are the junk value `0`
and give no information; so N-LIM cannot be derived from it by the DEC-107 route. LM themselves
argue conditionally on `h` (l. 1011–1026, "`Var[D(z,w;V) | h]`", "Lemma 5.1 … conditional
law"), where everything is bounded by Lemma 5.1. `LMT17VarNodeK` is that conditional statement:
for `law(h)`-a.e. `g`, under the conditional law `κ_g := condDistrib D h P g` of `D` given `h = g`,
`Var_{κ_g}(F_{n+1}) ≤ C(g)⁴ E_{κ_g}[(F_n − F_{n+1}) F_{n+1}]`, with `F_m(d) := d(z,w;B_m(0))`
written through the measurable countable formula `chainInf` (`t17F`; equal to the internal metric
on length metrics, `ContMetric.internal_eq_chainInf`). It is what DEC-107 §3(v) proves before
"taking expectations", and it is integrable a.s. (Lemma 5.1).

**Proof of `lmThm1_7_of_varNodeK`** (DEC-107 §3(vi)):
1. LM Lemma 5.1 (`c18_condBded`) for `f = F_{n₀}`, with the copy bound `F_{n₀}(D̃) ≤ C F_{n₀}(D)`
   from `t17_chainInf_le` (needs only `D` length): `F_{n₀} ≤ C(g) E_{κ_g}[F_{n₀}] < ∞`
   `κ_g`-a.s.
2. Exhaustion (`t17_iInf_chainInf`): `F_m ↓ D(z,w)` for length metrics, transferred to `κ_g`-a.e.
   `d` by `t17_ae_kernel`.
3. Bounded convergence (`t17_var_limit`): `d(z,w) = E_{κ_g}[d(z,w)]` `κ_g`-a.s.
4. Countably many pairs (dense sequence of `ℂ × ℂ`) and continuity: `κ_g ⊗ κ_g`-a.s. `d = d'`,
   hence `D = D̃` a.s. under the copy measure, and `AEDeterminedBy D h P` by
   `aeDeterminedBy_of_condCopy_ae_eq` (LM l. 1084–1087).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint

lemma t17_measurable_apply (p : ℂ × ℂ) : Measurable fun d : ContMetric => d.1 p :=
  (continuous_eval_const p).measurable.comp measurable_subtype_coe

/-- **N-VAR, conditional (kernel) form** (DEC-107 §3(i)–(v) before taking expectations): under the
hypotheses of `LMThm1_7`, for `z, w ∈ B_n(0)` and `law(h)`-a.e. `g`, with `κ_g` the conditional
law of `D` given `h = g` and `F_m = t17F m z w` (`= D(z,w;B_m(0))` on length metrics):
`Var_{κ_g}(F_{n+1}) ≤ C(g)⁴ E_{κ_g}[(F_n − F_{n+1}) F_{n+1}]`. -/
def LMT17VarNodeK : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (D : Ω → ContMetric) (hh : IsWholePlaneGFF h P), IsLocalMetric P h D →
    ∀ C : DistC → ℝ, Measurable C → (∀ g, 1 < C g) →
      (∀ᵐ q ∂condCopyMeasure D h P hh.measurable, ∀ z w : ℂ,
        q.2.1 (z, w) ≤ C (h q.1) * (D q.1).1 (z, w)) →
      ∀ (z w : ℂ) (n : ℕ), ‖z‖ < n → ‖w‖ < n →
        ∀ᵐ g ∂P.map h,
          ∫ d, ((t17F (n + 1) z w d).toReal -
              ∫ d', (t17F (n + 1) z w d').toReal ∂condDistrib D h P g) ^ 2 ∂condDistrib D h P g ≤
            C g ^ 4 * ∫ d, ((t17F n z w d).toReal - (t17F (n + 1) z w d).toReal) *
              (t17F (n + 1) z w d).toReal ∂condDistrib D h P g

/-- steps 1–3: for each `z, w`, `law(h)`-a.e. `g`, `d(z,w)` is `κ_g`-a.s. constant -/
theorem t17_const_of_varNodeK (H : LMT17VarNodeK) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (D : Ω → ContMetric) (hh : IsWholePlaneGFF h P)
    (hloc : IsLocalMetric P h D) (C : DistC → ℝ) (hCm : Measurable C) (hC1 : ∀ g, 1 < C g)
    (hcopy : ∀ᵐ q ∂condCopyMeasure D h P hh.measurable, ∀ z w : ℂ,
        q.2.1 (z, w) ≤ C (h q.1) * (D q.1).1 (z, w)) (z w : ℂ) :
    ∀ᵐ g ∂P.map h, ∀ᵐ d ∂condDistrib D h P g,
      d.1 (z, w) = ∫ d', d'.1 (z, w) ∂condDistrib D h P g := by
  have hDm := hloc.1
  have hlen := hloc.2.1
  set κ := condDistrib D h P with hκ
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max ‖z‖ ‖w‖)
  have hz : ‖z‖ < n₀ := (le_max_left _ _).trans_lt hn₀
  have hw : ‖w‖ < n₀ := (le_max_right _ _).trans_lt hn₀
  set f := t17F n₀ z w with hfdef
  have hf : Measurable f := measurable_t17F n₀ z w
  -- LM Lemma 5.1 for `f`
  have hcb : ∀ᵐ q ∂condCopyMeasure D h P hh.measurable,
      f q.2 ≤ ENNReal.ofReal (C (h q.1)) * f (D q.1) := by
    filter_upwards [hcopy, c18_ae_fst (D := D) hh.measurable hlen] with q hq hl
    exact t17_chainInf_le hl (by linarith [hC1 (h q.1)]) hq Metric.isOpen_ball z w
  have hb := c18_condBded hh.measurable hDm hf (ENNReal.measurable_ofReal.comp hCm) hcb
  -- the properties of `(h, D)` to transfer to the conditional law
  set S : Set (DistC × ContMetric) := {p | (∀ m : ℕ, t17F (n₀ + m + 1) z w p.2 ≤
      t17F (n₀ + m) z w p.2) ∧ (⨅ m : ℕ, t17F (n₀ + m) z w p.2) = ENNReal.ofReal (p.2.1 (z, w)) ∧
      f p.2 ≤ ENNReal.ofReal (C p.1) * ∫⁻ d, f d ∂κ p.1} with hSdef
  have hS : MeasurableSet S := by
    simp only [hSdef, Set.ofPred_and, Set.ofPred_forall]
    exact (MeasurableSet.iInter fun m => measurableSet_le
      ((measurable_t17F _ z w).comp measurable_snd) ((measurable_t17F _ z w).comp measurable_snd)).inter
      ((measurableSet_eq_fun (Measurable.iInf fun m => (measurable_t17F _ z w).comp measurable_snd)
        (ENNReal.measurable_ofReal.comp ((t17_measurable_apply (z, w)).comp measurable_snd))).inter
      (measurableSet_le (hf.comp measurable_snd) ((ENNReal.measurable_ofReal.comp
        (hCm.comp measurable_fst)).mul (hf.lintegral_kernel.comp measurable_fst))))
  have hPS : ∀ᵐ ω ∂P, (h ω, D ω) ∈ S := by
    filter_upwards [hlen, hb] with ω hl hbω
    exact ⟨fun m => t17_chainInf_succ_le hl _ z w, t17_iInf_chainInf hl n₀ z w, hbω.2⟩
  have hK := t17_ae_kernel hh.measurable hDm hS hPS
  have hfin : ∀ᵐ g ∂P.map h, ∫⁻ d, f d ∂κ g < ⊤ := by
    have hmeas : MeasurableSet {g : DistC | ∫⁻ d, f d ∂κ g < ⊤} :=
      measurableSet_lt hf.lintegral_kernel measurable_const
    rw [ae_map_iff hh.measurable.aemeasurable hmeas]
    filter_upwards [hb, hlen] with ω hbω hl
    refine hbω.1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 ?_))
    rw [hfdef, t17F, ← (D ω).internal_eq_chainInf hl Metric.isOpen_ball]
    exact DFGPS.T12.internal_ne_top (D ω) hl Metric.isOpen_ball (convex_ball _ _).isPreconnected
      (mem_ball_zero_iff.2 hz) (mem_ball_zero_iff.2 hw)
  have hV := ae_all_iff.2 fun m : ℕ => H P h D hh hloc C hCm hC1 hcopy z w (n₀ + m)
    (hz.trans_le (by exact_mod_cast Nat.le_add_right n₀ m))
    (hw.trans_le (by exact_mod_cast Nat.le_add_right n₀ m))
  filter_upwards [hK, hfin, hV] with g hKg hfg hVg
  have hX : ENNReal.ofReal (C g) * ∫⁻ d, f d ∂κ g ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfg.ne
  have hprops := hKg.mono fun d hd => t17_seq_props (a := fun m => t17F (n₀ + m) z w d)
    (d.nonneg z w) hX hd.1 hd.2.1 (by exact hd.2.2)
  exact t17_var_limit (F := fun m d => (t17F (n₀ + m) z w d).toReal) (G := fun d => d.1 (z, w))
    (c := C g ^ 4) (fun m => (measurable_t17F _ z w).ennreal_toReal)
    (hprops.mono fun d hd => hd.1) (hprops.mono fun d hd => hd.2.1)
    (hprops.mono fun d hd => hd.2.2) (fun m => hVg m)

/-- **LM Theorem 1.7 from the conditional variance node** (DEC-107 §3(vi), N-LIM with N-VAR in
kernel form). -/
theorem lmThm1_7_of_varNodeK (H : LMT17VarNodeK) : LMThm1_7 := by
  intro Ω _ P _ h D hh hloc C hCm hC1 hcopy
  have hDm := hloc.1
  set κ := condDistrib D h P with hκ
  set p : ℕ → ℂ × ℂ := TopologicalSpace.denseSeq (ℂ × ℂ) with hp
  have hB : ∀ᵐ g ∂P.map h, ∀ᵐ d ∂κ g, ∀ k, d.1 (p k) = ∫ d', d'.1 (p k) ∂κ g := by
    have := ae_all_iff.2 fun k =>
      t17_const_of_varNodeK H P h D hh hloc C hCm hC1 hcopy (p k).1 (p k).2
    filter_upwards [this] with g hg
    exact ae_all_iff.2 fun k => hg k
  set T : Set (DistC × ContMetric × ContMetric) := {t | ∀ k, t.2.1.1 (p k) = t.2.2.1 (p k)}
    with hTdef
  have hT : MeasurableSet T := by
    simp only [hTdef, Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => measurableSet_eq_fun
      ((t17_measurable_apply (p k)).comp (measurable_fst.comp measurable_snd))
      ((t17_measurable_apply (p k)).comp (measurable_snd.comp measurable_snd))
  have hQ : ∀ᵐ t ∂(P.map h ⊗ₘ (κ ×ₖ κ)), ∀ k, t.2.1.1 (p k) = t.2.2.1 (p k) := by
    rw [Measure.ae_compProd_iff hT]
    filter_upwards [hB] with g hg
    rw [Kernel.prod_apply]
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := κ g) (ν := κ g)).ae hg
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := κ g) (ν := κ g)).ae hg
    filter_upwards [h1, h2] with q hq1 hq2
    exact fun k => (hq1 k).trans (hq2 k).symm
  rw [hκ, ← condCopyMeasure_map_triple hh.measurable hDm] at hQ
  have hm : Measurable fun q : Ω × ContMetric => (h q.1, D q.1, q.2) :=
    (hh.measurable.comp measurable_fst).prodMk ((hDm.comp measurable_fst).prodMk measurable_snd)
  have hQ' := ae_of_ae_map hm.aemeasurable hQ
  refine aeDeterminedBy_of_condCopy_ae_eq hh.measurable hDm ?_
  filter_upwards [hQ'] with q hq
  exact Subtype.ext (DFunLike.coe_injective (Continuous.ext_on
    (TopologicalSpace.denseRange_denseSeq (ℂ × ℂ)) (D q.1).1.continuous q.2.1.continuous
    (by rintro _ ⟨k, rfl⟩; exact hq k)))

end LQGMetric.LM
