/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L2_4A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.SetupArc
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanPunct
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Geodesics
import LatticeProb.Bonanno.LQGMetric.Papers.MQ.SphereMain
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.LiftGeod

/-!
# CONF Lemmas 2.2, 2.3 and the compactness part of Lemma 2.4

Source: Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`.

* **CONF Lemma 2.2** (`lem-geo-unique`, l. 505–510), `confLem2_2`: "Almost surely, for each
  `q ∈ ℚ²` there is only one `D_h`-geodesic from 0 to `q`. *Proof.* This follows from the proof
  of [MQ, Theorem 1.2]." Here from `MQ.mqThm1_2Weak` (MQ Thm 1.2 for weak metrics, for every
  fixed pair of points, so no translation is needed) and a countable intersection
  (`GM.gm_S1_2_rat`).
* **CONF Lemma 2.3** (`lem-non-cross`, l. 516–527), `conf_L2_3_det` / `confLem2_3`: "the time
  when each of `P_q` and `P'` hits `u` is equal to `s := D_h(0,u)` … The concatenation of
  `P'|_{[0,s]}` and `P_q|_{[s,D_h(0,q)]}` is a `D_h`-geodesic from 0 to `q`. This `D_h`-geodesic
  must coincide with `P_q`" (concatenation: `GM.gm_geodL_eqOn_of_unique`).
* **CONF Lemma 2.4, proof l. 556**: "Since each `P_{q_n^-}` is a geodesic, the Arzelà–Ascoli
  theorem implies that after possibly passing to a subsequence, we can arrange that the paths
  converge uniformly to a continuous path `P_y^-`. The path `P_y^-` is a `D_h`-geodesic from 0
  to `y`": `exists_subseq_supDist` (mathlib `BoundedContinuousFunction.arzela_ascoli`; the
  geodesics are equicontinuous for the Euclidean metric because `D` and the Euclidean metric are
  uniformly equivalent on the compact `D`-ball, `euclid_modulus`) and `geod_of_tendsto`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric.Blueprint
open scoped BoundedContinuousFunction

namespace LQGMetric.CONF

/-! ## CONF Lemma 2.2 -/

/-- **CONF Lemma 2.2** (l. 505–510), from MQ Theorem 1.2 for weak LQG metrics. -/
theorem confLem2_2 (h38 : DFGPSLem3_8) : CONFLem2_2 := by
  intro γ hγ hγ2 D c hD Ω _ P _ h hh z₀
  rw [ae_all_iff]
  intro q
  exact GM.gm_S1_2 (MQ.mqThm1_2Weak h38) hγ hγ2 hD P h hh z₀ (ratPt q)

/-! ## CONF Lemma 2.3 -/

section Det
variable {D : ContMetric} {z w w' : ℂ}

/-- restriction of a unit-speed geodesic to `[0, a]` -/
theorem geodL_restr {P : ℝ → ℂ} {L a : ℝ} (hP : IsGeodesicL D P L z w) (ha : a ∈ Icc 0 L) :
    IsGeodesicL D P a z (P a) :=
  ⟨ha.1, hP.2.1, rfl, fun u hu v hv =>
    hP.2.2.2 u ⟨hu.1, hu.2.trans ha.2⟩ v ⟨hv.1, hv.2.trans ha.2⟩⟩

/-- **CONF Lemma 2.3** (l. 516–527), deterministic form: if the geodesic from `z` to `w` is
unique, `P_q` is it, `P'` is any geodesic from `z`, and `P_q(a) = P'(b)`, then `a = b`
(`= D(z, u)`) and `P_q = P'` on `[0, a]`. -/
theorem conf_L2_3_det (hU : UniqueGeod D z w) {Pq P' : ℝ → ℂ} {L L' : ℝ}
    (hPq : IsGeodesicL D Pq L z w) (hP' : IsGeodesicL D P' L' z w') {a b : ℝ}
    (ha : a ∈ Icc 0 L) (hb : b ∈ Icc 0 L') (hu : Pq a = P' b) :
    a = b ∧ EqOn Pq P' (Icc 0 a) := by
  have hab : a = b := by
    have h1 := DD.cl_geodL_dist hPq ha
    have h2 := DD.cl_geodL_dist hP' hb
    rw [hu] at h1
    linarith
  subst hab
  have hr : IsGeodesicL D P' a z (Pq a) := hu ▸ geodL_restr hP' hb
  exact ⟨rfl, fun t ht => (GM.gm_geodL_eqOn_of_unique hU hPq ha.2 hr ht).symm⟩

end Det

/-! ## Arzelà–Ascoli for geodesics (CONF l. 556) -/

section AA
variable {D : ContMetric} {z : ℂ}

/-- on a compact set the identity `(K, D) → (K, |·|)` is uniformly continuous -/
theorem euclid_modulus (D : ContMetric) {K : Set ℂ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, D.1 (x, y) < δ → ‖x - y‖ < ε := by
  set S : Set (ℂ × ℂ) := (K ×ˢ K) ∩ {p | ε ≤ ‖p.1 - p.2‖} with hSdef
  have hS : IsCompact S := (hK.prod hK).inter_right
    (isClosed_le continuous_const (continuous_fst.sub continuous_snd).norm)
  rcases S.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun x hx y hy _ => ?_⟩
    by_contra hc
    have : (x, y) ∈ S := ⟨⟨hx, hy⟩, not_lt.1 hc⟩
    rw [he] at this
    exact this
  · obtain ⟨p, hp, hmin⟩ := hS.exists_isMinOn hne (map_continuous D.1).continuousOn
    have hpos : 0 < D.1 p := by
      have hne' : p.1 ≠ p.2 := fun h0 => by
        have := hp.2
        simp only [mem_ofPred_eq, h0, sub_self, norm_zero] at this
        linarith
      rcases (GM.gm_D_nonneg D p.1 p.2).lt_or_eq with h1 | h1
      · exact h1
      · exact absurd (D.2.eq_of_eq_zero p.1 p.2 h1.symm) hne'
    refine ⟨D.1 p, hpos, fun x hx y hy hxy => ?_⟩
    by_contra hc
    have hm := hmin (show (x, y) ∈ S from ⟨⟨hx, hy⟩, not_lt.1 hc⟩)
    simp only [mem_ofPred_eq] at hm
    linarith

/-- pointwise convergence from uniform convergence on `[0, s]` -/
theorem tendsto_of_supDistOn {Pn : ℕ → ℝ → ℂ} {P : ℝ → ℂ} {s : ℝ}
    (hc : Tendsto (fun n => supDistOn (Pn n) P s) atTop (𝓝 0)) {t : ℝ} (ht : t ∈ Icc 0 s) :
    Tendsto (fun n => Pn n t) atTop (𝓝 (P t)) := by
  rw [tendsto_iff_edist_tendsto_0]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun _ => bot_le)
    (fun n => ?_)
  exact le_iSup₂ (f := fun t (_ : t ∈ Icc 0 s) => edist (Pn n t) (P t)) t ht

/-- **a pointwise limit of geodesics is a geodesic** (CONF l. 556) -/
theorem geod_of_tendsto {Pn : ℕ → ℝ → ℂ} {yn : ℕ → ℂ} {P : ℝ → ℂ} {s : ℝ} {y : ℂ}
    (hPn : ∀ n, IsGeodesicL D (Pn n) s z (yn n)) (hs : 0 ≤ s) (hy : Tendsto yn atTop (𝓝 y))
    (hc : ∀ t ∈ Icc 0 s, Tendsto (fun n => Pn n t) atTop (𝓝 (P t))) :
    IsGeodesicL D P s z y := by
  have h0 : (0 : ℝ) ∈ Icc 0 s := ⟨le_rfl, hs⟩
  have hsI : s ∈ Icc 0 s := ⟨hs, le_rfl⟩
  refine ⟨hs, ?_, ?_, fun a ha b hb => ?_⟩
  · exact tendsto_nhds_unique (hc 0 h0)
      (tendsto_const_nhds.congr fun n => ((hPn n).2.1).symm)
  · exact tendsto_nhds_unique (hc s hsI) (hy.congr fun n => ((hPn n).2.2.1).symm)
  · have hl : Tendsto (fun n => D.1 (Pn n a, Pn n b)) atTop (𝓝 (D.1 (P a, P b))) :=
      ((map_continuous D.1).tendsto _).comp ((hc a ha).prodMk_nhds (hc b hb))
    exact tendsto_nhds_unique hl
      (tendsto_const_nhds.congr fun n => ((hPn n).2.2.2 a ha b hb).symm)

/-- **Arzelà–Ascoli for geodesics** (CONF l. 556): if closed `D`-bounded sets are compact,
every sequence of geodesics of length `s` from `z` has a subsequence converging uniformly on
`[0, s]`. -/
theorem exists_subseq_supDist
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    {s : ℝ} (hs : 0 ≤ s) {Pn : ℕ → ℝ → ℂ} {yn : ℕ → ℂ}
    (hPn : ∀ n, IsGeodesicL D (Pn n) s z (yn n)) :
    ∃ (φ : ℕ → ℕ) (P : ℝ → ℂ), StrictMono φ ∧
      Tendsto (fun n => supDistOn (Pn (φ n)) P s) atTop (𝓝 0) := by
  set K : Set ℂ := {u | D.1 (z, u) ≤ s} with hKdef
  have hK : IsCompact K := by
    refine hbc K (isClosed_le (DD.cl_continuous_distFrom D z) continuous_const)
      ⟨2 * s, fun u hu v hv => ?_⟩
    have h1 := D.2.triangle u z v
    have h2 := D.2.symm u z
    simp only [hKdef, mem_ofPred_eq] at hu hv
    linarith
  have : CompactSpace (Icc (0 : ℝ) s) := isCompact_iff_compactSpace.mp isCompact_Icc
  let u : ℕ → Icc (0 : ℝ) s →ᵇ ℂ := fun n => BoundedContinuousFunction.mkOfCompact
    ⟨(Icc 0 s).domRestrict (Pn n), (DD.cl_geodL_continuousOn (hPn n)).domRestrict⟩
  have hu : ∀ n (t : Icc (0 : ℝ) s), u n t = Pn n t := fun _ _ => rfl
  have hin : ∀ (f : Icc (0 : ℝ) s →ᵇ ℂ) (t : Icc (0 : ℝ) s), f ∈ range u → f t ∈ K := by
    rintro _ t ⟨n, rfl⟩
    show D.1 (z, Pn n t) ≤ s
    rw [DD.cl_geodL_dist (hPn n) t.2]
    exact t.2.2
  have hequi : Equicontinuous ((↑) : range u → Icc (0 : ℝ) s → ℂ) := by
    refine UniformEquicontinuous.equicontinuous ?_
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := euclid_modulus D hK hε
    refine ⟨δ, hδ, fun t t' htt' => ?_⟩
    rintro ⟨_, ⟨n, rfl⟩⟩
    show dist (u n t) (u n t') < ε
    rw [hu, hu, dist_eq_norm]
    refine hδε _ (hin _ t ⟨n, rfl⟩) _ (hin _ t' ⟨n, rfl⟩) ?_
    show D.1 (Pn n t, Pn n t') < δ
    rw [(hPn n).2.2.2 t t.2 t' t'.2, abs_sub_comm]
    rwa [Subtype.dist_eq, Real.dist_eq] at htt'
  have hcpt := BoundedContinuousFunction.arzela_ascoli K hK (range u) hin hequi
  obtain ⟨f, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq (x := u) fun n => subset_closure ⟨n, rfl⟩
  refine ⟨φ, fun t => f (projIcc 0 s hs t), hφ, ?_⟩
  have hl := tendsto_iff_edist_tendsto_0.1 hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl (fun _ => bot_le)
    (fun n => ?_)
  refine iSup₂_le fun t ht => ?_
  have hp : projIcc 0 s hs t = ⟨t, ht⟩ := projIcc_of_mem hs ht
  simp only [Function.comp_apply, hp]
  rw [← hu (φ n) ⟨t, ht⟩, edist_dist, edist_dist]
  exact ENNReal.ofReal_le_ofReal (BoundedContinuousFunction.dist_coe_le_dist _)

end AA

end LQGMetric.CONF
