/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412hQk1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412hFill
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412iConf
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412fEnd
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE5

/-!
# The guard set `Q_k` (D98 §2, packet P-Qk, part 1): membership is a.s. local

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, L4.15 Step 3, l. 2155–2163
(`𝒴_k` the endpoints of the arcs `𝓘_k`; `z_y` "in a manner depending only on
`(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})`"); GM.S4.1 (l. 1648–1654); decision D98 §2 ("`{q ∈ Q_k}` is
analytic … (`gm_arcRelAn`) …, saturated …, so it is a.s. a `σ(𝓑^•_{t_k}, h|)`-event").

* `p412hYk d 𝕫 s t` — the points lying in the closures of two distinct arcs `arcOf x`,
  `x ∈ Conf(s, t)`; on the event of GM.S4.1 it is GM's `𝒴_k = p412fEndSet` (`p412h_endSet_eq`),
  and it is analytic on `lenSet` (`p412h_YkAn`), whereas `p412fEndSet` involves the complement
  of an arc;
* `p412hXq` — the metric event `{∃ e ∈ 𝒴_k, gd(𝓑^•_{t_k}, e) = q}`, analytic on `lenSet`
  (`p412h_XqAn`, with `p412h_meas_gd`) and saturated for the internal metric near `𝓑^•_{t_k}`;
* **`p412h_Xq_aeEventIn`** — `{D_h ∈ p412hXq}` is a.s. an event of `σ(𝓑^•_{t_k}, h|)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology Bornology
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

/-- points in the closures of two distinct arcs of `Conf(s, t)` -/
def p412hYk (d : ContMetric) (𝕫 : ℂ) (s t : ℝ) : Set ℂ :=
  {e | ∃ x ∈ confPts d 𝕫 s t, ∃ x' ∈ confPts d 𝕫 s t, x ≠ x' ∧
    e ∈ closure (arcOf d 𝕫 t x) ∧ e ∈ closure (arcOf d 𝕫 t x')}

/-- on the event of GM.S4.1, `p412hYk = 𝒴_k` -/
theorem p412h_endSet_eq {d : ContMetric} {𝕫 : ℂ} {s t : ℝ} (hfin : (confPts d 𝕫 s t).Finite)
    (harc : ∀ x ∈ confPts d 𝕫 s t, IsBdyArc d 𝕫 t (arcOf d 𝕫 t x))
    (hdis : (confPts d 𝕫 s t).PairwiseDisjoint (arcOf d 𝕫 t))
    (hcov : ⋃ x ∈ confPts d 𝕫 s t, arcOf d 𝕫 t x = frontier (filledBall d 𝕫 t)) :
    p412fEndSet d 𝕫 s t = p412hYk d 𝕫 s t := by
  set C := confPts d 𝕫 s t
  have hJ : ∀ x ∈ C, frontier (filledBall d 𝕫 t) \ arcOf d 𝕫 t x =
      ⋃ x' ∈ C \ {x}, arcOf d 𝕫 t x' := by
    intro x hx
    ext z
    simp only [Set.mem_sdiff, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hz, hzx⟩
      rw [← hcov] at hz
      obtain ⟨x', hx', hz'⟩ := mem_iUnion₂.1 hz
      exact ⟨x', ⟨hx', fun h => hzx (h ▸ hz')⟩, hz'⟩
    · rintro ⟨x', ⟨hx', hne⟩, hz⟩
      exact ⟨(harc x' hx').1 hz, fun hzx => Set.disjoint_left.1 (hdis hx' hx hne) hz hzx⟩
  ext e
  simp only [p412fEndSet, p412fEndpts, mem_iUnion, mem_inter_iff, p412hYk, mem_ofPred_eq,
    exists_prop]
  constructor
  · rintro ⟨x, hx, he₁, he₂⟩
    rw [hJ x hx, (hfin.subset sdiff_subset).closure_biUnion] at he₂
    obtain ⟨x', ⟨hx', hne⟩, he'⟩ := mem_iUnion₂.1 he₂
    exact ⟨x, hx, x', hx', fun h => hne (mem_singleton_iff.2 h.symm), he₁, he'⟩
  · rintro ⟨x, hx, x', hx', hne, he₁, he₂⟩
    refine ⟨x, hx, he₁, ?_⟩
    rw [hJ x hx, (hfin.subset sdiff_subset).closure_biUnion]
    exact mem_iUnion₂.2 ⟨x', ⟨hx', fun h => hne (mem_singleton_iff.1 h).symm⟩, he₂⟩

/-- `x ∈ Conf`, `e ∈ cl(arcOf x)` is analytic on `lenSet` -/
theorem p412h_clArcAn (𝕫 : ℂ) :
    GMAnalyticOn {p : (ContMetric × ℝ × ℝ) × ℂ × ℂ | p.1.1 ∈ lenSet}
      {p | p.2.1 ∈ confPts p.1.1 𝕫 p.1.2.1 p.1.2.2 ∧
        p.2.2 ∈ closure (arcOf p.1.1 𝕫 p.1.2.2 p.2.1)} := by
  set L := {p : (ContMetric × ℝ × ℝ) × ℂ × ℂ | p.1.1 ∈ lenSet}
  have hf : Measurable fun q : ((ContMetric × ℝ × ℝ) × ℂ × ℂ) × ℂ => (q.1.1, (q.1.2.1, q.2)) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  have hm : ∀ m : ℕ, GMAnalyticOn L {p | ∃ y : ℂ, (p, y) ∈
      (fun q : ((ContMetric × ℝ × ℝ) × ℂ × ℂ) × ℂ => (q.1.1, (q.1.2.1, q.2))) ⁻¹'
        {p : (ContMetric × ℝ × ℝ) × ℂ × ℂ | p.2.1 ∈ confPts p.1.1 𝕫 p.1.2.1 p.1.2.2 ∧
          p.2.2 ∈ arcOf p.1.1 𝕫 p.1.2.2 p.2.1} ∩
        {q | dist q.2 q.1.2.2 < 1 / ((m : ℝ) + 1)}} := fun m =>
    gmAn_exists (gmAn_inter (gmAn_preimage hf (gm_arcRelAn 𝕫))
      (gmAn_of_measurableSet (measurableSet_lt (measurable_snd.dist
        (measurable_snd.comp (measurable_snd.comp measurable_fst))) measurable_const)))
  refine gmAn_congr (gmAn_iInter hm) fun p _ => ?_
  simp only [mem_iInter, mem_ofPred_eq, mem_inter_iff, mem_preimage]
  constructor
  · intro H
    obtain ⟨y, ⟨hx, -⟩, -⟩ := H 0
    refine ⟨hx, Metric.mem_closure_iff.2 fun δ hδ => ?_⟩
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    obtain ⟨y, ⟨-, hy⟩, hd⟩ := H m
    exact ⟨y, hy, by rw [dist_comm]; linarith⟩
  · rintro ⟨hx, he⟩ m
    obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.1 he (1 / ((m : ℝ) + 1)) (by positivity)
    exact ⟨y, ⟨hx, hy⟩, by rw [dist_comm]; exact hd⟩

/-- `p412hYk` is analytic on `lenSet` -/
theorem p412h_YkAn (𝕫 : ℂ) :
    GMAnalyticOn {p : (ContMetric × ℝ × ℝ) × ℂ | p.1.1 ∈ lenSet}
      {p | p.2 ∈ p412hYk p.1.1 𝕫 p.1.2.1 p.1.2.2} := by
  have hf₁ : Measurable fun q : ((ContMetric × ℝ × ℝ) × ℂ) × ℂ × ℂ => (q.1.1, (q.2.1, q.1.2)) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst))
  have hf₂ : Measurable fun q : ((ContMetric × ℝ × ℝ) × ℂ) × ℂ × ℂ => (q.1.1, (q.2.2, q.1.2)) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst))
  set L' := {q : ((ContMetric × ℝ × ℝ) × ℂ) × ℂ × ℂ |
    q.1 ∈ {p : (ContMetric × ℝ × ℝ) × ℂ | p.1.1 ∈ lenSet}}
  have hA := gmAn_exists (L := {p : (ContMetric × ℝ × ℝ) × ℂ | p.1.1 ∈ lenSet})
    (gmAn_inter (gmAn_inter (gmAn_mono (L' := L') (gmAn_preimage hf₁ (p412h_clArcAn 𝕫))
      fun q hq => hq)
    (gmAn_mono (L' := L') (gmAn_preimage hf₂ (p412h_clArcAn 𝕫)) fun q hq => hq))
      (gmAn_of_measurableSet
      (measurableSet_eq_fun (measurable_fst.comp measurable_snd)
        (measurable_snd.comp measurable_snd)).compl))
  refine gmAn_congr hA fun p _ => ?_
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff, p412hYk]
  constructor
  · rintro ⟨⟨x, x'⟩, ⟨⟨hx, he⟩, hx', he'⟩, hne⟩
    exact ⟨x, hx, x', hx', hne, he, he'⟩
  · rintro ⟨x, hx, x', hx', hne, he, he'⟩
    exact ⟨(x, x'), ⟨⟨hx, he⟩, hx', he'⟩, hne⟩

/-- the metric event `{∃ e ∈ 𝒴_k, gd(𝓑^•_{τc}, e) = q}` -/
def p412hXq (𝕫 : ℂ) (R c₁ c ε : ℝ) (q : ℂ) : Set ContMetric :=
  {d | ∃ e ∈ p412hYk d 𝕫 (tauD d 𝕫 R * c₁) (tauD d 𝕫 R * c),
    p412hGd (filledBall d 𝕫 (tauD d 𝕫 R * c)) e ε = q}

theorem p412h_XqAn (𝕫 : ℂ) {R c₁ c ε : ℝ} (hR : 0 < R) (hc : 0 < c) (hε : 0 < ε) (q : ℂ) :
    GMAnalyticOn lenSet (p412hXq 𝕫 R c₁ c ε q) := by
  obtain ⟨E₀, hE₀, hE⟩ := p412h_meas_gd (p412h_rc_filled 𝕫)
    (y := fun p : ContMetric × ℝ × ℂ => p.2.2) (measurable_snd.comp measurable_snd) hε q
  have hψ : Measurable fun p : (ContMetric × ℝ × ℝ) × ℂ => (p.1.1, p.1.2.2, p.2) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  have hW : GMAnalyticOn {a : ContMetric × ℝ × ℝ | a.1 ∈ lenSet ∧ 0 < a.2.2}
      {a | ∃ e : ℂ, (a, e) ∈ {p : (ContMetric × ℝ × ℝ) × ℂ |
        p.2 ∈ p412hYk p.1.1 𝕫 p.1.2.1 p.1.2.2} ∩
        (fun p : (ContMetric × ℝ × ℝ) × ℂ => (p.1.1, p.1.2.2, p.2)) ⁻¹' E₀} :=
    gmAn_exists (gmAn_inter (gmAn_mono (p412h_YkAn 𝕫) fun p hp => hp.1)
      (gmAn_of_measurableSet (hψ hE₀)))
  have hφ : Measurable fun d : ContMetric => (d, gmTauB 𝕫 R d * c₁, gmTauB 𝕫 R d * c) :=
    measurable_id.prodMk (((gm_measurable_tauB 𝕫 R).mul_const c₁).prodMk
      ((gm_measurable_tauB 𝕫 R).mul_const c))
  refine gmAn_congr (gmAn_mono (gmAn_preimage hφ hW) fun d hd => ⟨hd, ?_⟩) fun d hd => ?_
  · simp only [mem_preimage, mem_ofPred_eq, ← gm_tauD_eq_tauB hd]
    exact mul_pos (gm_tauD_pos d 𝕫 hR) hc
  have ht : 0 < tauD d 𝕫 R * c := mul_pos (gm_tauD_pos d 𝕫 hR) hc
  have hbd : IsBounded (ballM d 𝕫 (tauD d 𝕫 R * c)) :=
    (gm_filledBall_isBounded_of_lenSet hd 𝕫 _).subset fun w hw => Or.inl (subset_closure hw)
  have hgeo := (p412h_filled_geo ht (isLength_of_mem_lenSet hd) hbd).1
  simp only [mem_preimage, mem_ofPred_eq, mem_inter_iff, p412hXq, ← gm_tauD_eq_tauB hd]
  constructor
  · rintro ⟨e, he, heq⟩
    exact ⟨e, he, (hE (d, tauD d 𝕫 R * c, e) hgeo).2 heq⟩
  · rintro ⟨e, he, heq⟩
    exact ⟨e, he, (hE (d, tauD d 𝕫 R * c, e) hgeo).1 heq⟩

variable {γ : ℝ} {D : DistC → ContMetric} {c₀ : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- **`{q ∈ Q_k}` is a.s. local** (D98 §2) -/
theorem p412h_Xq_aeEventIn (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) {R c₁ c ε : ℝ}
    (hR : 0 < R) (hc₁ : c₁ ≤ c) (hc : 1 < c) (hε : 0 < ε) (q : ℂ) :
    AEEventIn P (localSigma h (fun ω => filledBall (D (h ω)) 𝕫 (tauD (D (h ω)) 𝕫 R * c)))
      {ω | D (h ω) ∈ p412hXq 𝕫 R c₁ c ε q} := by
  refine gm_aeEventIn_sigA_of_sat h38 hγ hγ2 hD hh 𝕫 hR hc
    (gm_uMeas_of_an (p412h_XqAn 𝕫 hR (by linarith) hε q))
    (fun d₁ h₁ d₂ h₂ U hU heq hKU hd => ?_)
  have l1 := isLength_of_mem_lenSet h₁
  have l2 := isLength_of_mem_lenSet h₂
  have hτpos := gm_tauD_pos d₁ 𝕫 hR
  obtain ⟨hτ, hball⟩ := gm_tk_congr l1 l2 hc hU heq hτpos hKU
  have hA : GMAgree d₁ d₂ U 𝕫 (tauD d₁ 𝕫 R * c) :=
    ⟨fun x _ y _ => by rw [heq], fun u hu => (hball u hu).symm, hKU,
      mul_pos hτpos (by linarith)⟩
  have h1 : tauD d₁ 𝕫 R * c₁ ≤ tauD d₁ 𝕫 R * c := mul_le_mul_of_nonneg_left hc₁ hτpos.le
  obtain ⟨e, ⟨x, hx, x', hx', hne, he, he'⟩, hq⟩ := hd
  refine ⟨e, ?_, ?_⟩
  · rw [hτ]
    exact ⟨x, gm_hitSet_transfer hA h1 le_rfl hx, x', gm_hitSet_transfer hA h1 le_rfl hx', hne,
      closure_mono (fun y hy => gm_arcOf_transfer hA le_rfl hy) he,
      closure_mono (fun y hy => gm_arcOf_transfer hA le_rfl hy) he'⟩
  · rw [hτ, hA.fb le_rfl]; exact hq

end LQGMetric.GM
