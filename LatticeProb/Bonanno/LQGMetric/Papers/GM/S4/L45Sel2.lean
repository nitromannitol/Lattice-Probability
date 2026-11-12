/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L45Sel2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Sel

/-!
# GM Lemma 4.5 without `GMGeodSelDet` (task P2-E2S)

GM, arXiv:1905.00383, `uniqueness-final.tex` Lemma 4.5 (`lem-geo-sigma-algebra`), proof
l. 1665–1675. `gm_L4_5_E2b_of_null`: `P|_{[0,s_k]}` is a.s. determined by
`𝓕'_k = σ(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}}, arc of 𝓘_k containing P(t_k))`. Following GM: on
`{𝕨 ∈ 𝓑^•_{t_k}}` the path is the (unique) geodesic to `𝕨`; otherwise `P(s_k) ∈ Conf_k` is the
point whose arc contains `P(t_k)` and `P|_{[0,s_k]}` is the unique geodesic from `𝕫` to `P(s_k)`
(`gm_geod01_eq_of_unique`). Each coordinate `P(s_k u)` is decoded by `gmXi` from the local field
events `gmGeodWSet`, `gmGeodCEv` (a.s. `σ(𝓑^•_{t_k}, h|)`-events by `gm_aeEventIn_Kt`, given their
null-measurability), and the path σ-algebra is the supremum over `u` of the coordinate σ-algebras.

`gm_L4_5_of_null'`: GM Lemma 4.5, both directions, with only null-measurability inputs
(`GMGeodSelDet` and the `gmConfEv` input `hnullC` of `gm_L4_5_of_null` are no longer needed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- **GM Lemma 4.5, E2b** at GM's `s_k`, `t_k`, from null-measurability of the decoding events -/
theorem gm_L4_5_E2b_of_null (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4) (hC27 : CONFLem2_7)
    (hC14 : CONFThm1_4) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    {c' : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c') {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P) {𝕫 𝕨 : ℂ}
    (h𝕫𝕨 : 𝕫 ≠ 𝕨) {η : Ω → C(unitInterval, ℂ)}
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (η ω) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    {ℓ 𝕣 ε β : ℝ} (k : ℕ) (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε) {V : ℕ → Set ℂ}
    (hVo : ∀ n, IsOpen (V n))
    (hV : ∀ (x : ℂ) (O : Set ℂ), IsOpen O → x ∈ O → ∃ n, x ∈ V n ∧ V n ⊆ O)
    (hnullGW : ∀ (u : unitInterval) (j : Bool × ℚ) (n : ℕ) (s : Finset (ℤ × ℤ)),
      NullMeasurableSet
        (gmGeodWSet D 𝕫 𝕨 (ℓ * 𝕣) (1 + k * ε ^ β) (1 + k * ε ^ β + ε ^ (2 * β)) u j ∩
        {g | dyadicHull n (gmKt D 𝕫 (ℓ * 𝕣) (1 + k * ε ^ β + ε ^ (2 * β)) g) =
          LocalEvent.hullFin n s}) (P.map h))
    (hnullGC : ∀ (u : unitInterval) (i : (Bool × ℚ) × Finset ℕ × Finset ℕ) (n : ℕ)
      (s : Finset (ℤ × ℤ)),
      NullMeasurableSet ({g | gmGeodCEv V (D g) 𝕫 (tauD (D g) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β))
        (tauD (D g) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β + ε ^ (2 * β))) u i} ∩
        {g | dyadicHull n (gmKt D 𝕫 (ℓ * 𝕣) (1 + k * ε ^ β + ε ^ (2 * β)) g) =
          LocalEvent.hullFin n s}) (P.map h)) :
    AEDeterminedSigma (gmSigF D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k))
      (gmSigF' D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k)) P := by
  classical
  set sk := s4S D h 𝕫 ℓ 𝕣 ε β k with hsk
  set tk := s4T D h 𝕫 ℓ 𝕣 ε β k with htk
  have h1 : 0 < ε ^ β := Real.rpow_pos_of_pos hε β
  have h2 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hc : 1 < 1 + k * ε ^ β + ε ^ (2 * β) := by nlinarith
  have hc₀ : 1 + k * ε ^ β ≤ 1 + k * ε ^ β + ε ^ (2 * β) := by linarith
  have hlen := ae_mem_lenSet h38 hγ hγ2 hD P h hh
  have hAF' : gmSigA D h 𝕫 tk ≤ (gmSigF' D h 𝕫 𝕨 η sk tk) := le_sup_left
  have hid : @Measurable Ω Ω (gmSigF' D h 𝕫 𝕨 η sk tk) (gmSigA D h 𝕫 tk) id :=
    Measurable.mono (@measurable_id Ω (gmSigA D h 𝕫 tk)) hAF' le_rfl
  set sig : Ω → ℕ → Prop := fun ω n =>
    (arcOf (D (h ω)) 𝕫 (tk ω) (geodL (D (h ω)) 𝕫 𝕨 (η ω) (sk ω)) ∩ V n).Nonempty with hsigdef
  have hsig : @Measurable Ω (ℕ → Prop) (gmSigF' D h 𝕫 𝕨 η sk tk) _ sig := by
    refine gm_measurable_pi_prop _ _ fun n => ?_
    exact (le_sup_right : _ ≤ (gmSigF' D h 𝕫 𝕨 η sk tk)) _ (MeasurableSpace.measurableSet_generateFrom ⟨V n, hVo n, rfl⟩)
  have hp : MeasurableSet[(gmSigF' D h 𝕫 𝕨 η sk tk)] {ω | 𝕨 ∈ filledBall (D (h ω)) 𝕫 (tk ω)} :=
    hAF' _ (gm_mem_filledBall_measurable 𝕨)
  refine gm_aeDet_sup (gm_aeDet_of_le hAF') ?_
  rw [gm_aeDet_iff_le]
  show MeasurableSpace.comap (gmPathK D h 𝕫 𝕨 η sk) MeasurableSpace.pi ≤ _
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  refine iSup_le fun u => ?_
  rw [MeasurableSpace.comap_comp, ← gm_aeDet_iff_le]
  -- the codes of the decoding events at `u`
  have hE1 : ∀ i : (Bool × ℚ) × Finset ℕ × Finset ℕ, AEEventIn P (gmSigA D h 𝕫 tk)
      (h ⁻¹' gmGeodWSet D 𝕫 𝕨 (ℓ * 𝕣) (1 + k * ε ^ β) (1 + k * ε ^ β + ε ^ (2 * β)) u i.1) :=
    fun i => by
      rw [htk, gm_gmSigA_s4T]
      exact gm_aeEventIn_Kt hD P h (Tight.isGFFPlusCont_of_wp hh) hlen 𝕫 hℓ𝕣 hc
        (hnullGW u i.1) (fun g₁ g₂ U h1 h2 hτe H hB => gm_geodWSet_sat u i.1 g₁ g₂ U h1 h2 hτe H hB)
  have hE2 : ∀ i : (Bool × ℚ) × Finset ℕ × Finset ℕ, AEEventIn P (gmSigA D h 𝕫 tk)
      (h ⁻¹' {g | gmGeodCEv V (D g) 𝕫 (tauD (D g) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β))
        (tauD (D g) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β + ε ^ (2 * β))) u i}) :=
    fun i => by
      rw [htk, gm_gmSigA_s4T]
      exact gm_aeEventIn_Kt hD P h (Tight.isGFFPlusCont_of_wp hh) hlen 𝕫 hℓ𝕣 hc
        (hnullGC u i) (fun g₁ g₂ U h1 h2 hτe H hB =>
          gm_geodCEv_sat hℓ𝕣 hc₀ u i g₁ g₂ U h1 h2 hτe H hB)
  obtain ⟨Z1, hZ1, hZ1E⟩ := LocalEvent.exists_measurable_code hE1
  obtain ⟨Z2, hZ2, hZ2E⟩ := LocalEvent.exists_measurable_code hE2
  set Y' : Ω → ℂ := fun ω =>
    if 𝕨 ∈ filledBall (D (h ω)) 𝕫 (tk ω) then gmXi Z1 (ω, sig ω) else gmXi Z2 (ω, sig ω)
    with hY'def
  have hf : @Measurable Ω ℂ (gmSigF' D h 𝕫 𝕨 η sk tk) _ (fun ω => gmXi Z1 (ω, sig ω)) :=
    (gm_measurable_gmXi _ hZ1).comp (hid.prodMk hsig)
  have hg : @Measurable Ω ℂ (gmSigF' D h 𝕫 𝕨 η sk tk) _ (fun ω => gmXi Z2 (ω, sig ω)) :=
    (gm_measurable_gmXi _ hZ2).comp (hid.prodMk hsig)
  have hY' : @Measurable Ω ℂ (gmSigF' D h 𝕫 𝕨 η sk tk) _ Y' := by
    intro B hB
    have e : Y' ⁻¹' B = ({ω | 𝕨 ∈ filledBall (D (h ω)) 𝕫 (tk ω)} ∩
        (fun ω => gmXi Z1 (ω, sig ω)) ⁻¹' B) ∪
        ({ω | 𝕨 ∈ filledBall (D (h ω)) 𝕫 (tk ω)}ᶜ ∩ (fun ω => gmXi Z2 (ω, sig ω)) ⁻¹' B) := by
      ext ω
      by_cases hw : 𝕨 ∈ filledBall (D (h ω)) 𝕫 (tk ω) <;> simp [Y', hw]
    rw [e]
    exact (hp.inter (hf hB)).union (hp.compl.inter (hg hB))
  refine gm_aeDet_comap hY' ?_
  filter_upwards [hη, hlen, hZ1E, hZ2E,
    gm_L4_5_arc_ae hC24 hC27 hC14 hγ hγ2 hD P h hh 𝕫 𝕨 h𝕫𝕨 η hη,
    gm_S4_1 hC24 hC27 hC14 hγ hγ2 hD P h hh 𝕫,
    gm_conf_hitPattern_injOn hC24 hC27 hC14 hγ hγ2 hD P h hh hlen 𝕫 hV hVo]
    with ω hηω hlenω hZ1ω hZ2ω harcω hS41 hinj
  show geodL (D (h ω)) 𝕫 𝕨 (η ω) (sk ω * u) = Y' ω
  obtain ⟨hs, hlt⟩ := gm_s4_pos_lt D h 𝕫 β k hℓ𝕣 hε ω
  have htkω : tk ω = tauD (D (h ω)) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β + ε ^ (2 * β)) :=
    gm_s4T_eq D h 𝕫 ℓ 𝕣 ε β k ω
  have hP := gm_geodL_isGeodesicL hηω.1 h𝕫𝕨
  by_cases hw : 𝕨 ∈ filledBall (D (h ω)) 𝕫 (tk ω)
  · simp only [Y', hw, ite_true]
    symm
    refine gm_gmXi_eq fun j => ?_
    have hZ : ∀ F G : Finset ℕ, Z1 ω (j, F, G) = true ↔
        h ω ∈ gmGeodWSet D 𝕫 𝕨 (ℓ * 𝕣) (1 + k * ε ^ β) (1 + k * ε ^ β + ε ^ (2 * β)) u j :=
      fun F G => hZ1ω (j, F, G)
    have hpre : gmPre Z1 ω (sig ω) j ↔
        h ω ∈ gmGeodWSet D 𝕫 𝕨 (ℓ * 𝕣) (1 + k * ε ^ β) (1 + k * ε ^ β + ε ^ (2 * β)) u j :=
      ⟨fun ⟨L, hL⟩ => (hZ _ _).1 (hL L le_rfl), fun hm => ⟨0, fun _ _ => (hZ _ _).2 hm⟩⟩
    rw [hpre]
    constructor
    · rintro ⟨-, Q, hQ, hQu⟩
      rw [hηω.2.unique hQ hηω.1] at hQu
      exact hQu
    · intro hm
      refine ⟨?_, η ω, hηω.1, hm⟩
      show 𝕨 ∈ filledBall (D (h ω)) 𝕫 (tauD (D (h ω)) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β + ε ^ (2 * β)))
      rw [← htkω]
      exact hw
  · simp only [Y', hw, ite_false]
    symm
    refine gm_gmXi_eq fun j => ?_
    set d := D (h ω)
    set x := geodL d 𝕫 𝕨 (η ω) (sk ω)
    obtain ⟨hxc, -, -⟩ := harcω (sk ω) (tk ω) hs hlt hw
    obtain ⟨hfin, -, -, -⟩ := hS41 _ _ hs hlt
    have hinj' := hinj _ _ hs hlt
    have htL := gm_lt_length_of_not_mem hP (hs.trans hlt) hw
    have hsL : sk ω ≤ d.1 (𝕫, 𝕨) := (hlt.trans htL).le
    have hZ : ∀ i, Z2 ω i = true ↔ gmGeodCEv V d 𝕫 (sk ω) (tk ω) u i := fun i => by
      rw [hZ2ω i, htkω]
      rfl
    have key := gm_conf_decode_pred (V := V) hfin hinj' hxc
      (fun x' => ∃ Q : C(unitInterval, ℂ), IsGeod01 d 𝕫 x' Q ∧ Q u ∈ gmHalf j)
    calc gmPre Z2 ω (sig ω) j
        ↔ ∃ L, ∀ L' ≥ L, gmGeodCEv V d 𝕫 (sk ω) (tk ω) u
          (j, gmPreF (sig ω) L', gmPreG (sig ω) L') :=
          exists_congr fun L => forall_congr' fun L' => forall_congr' fun _ => hZ _
      _ ↔ ∃ Q : C(unitInterval, ℂ), IsGeod01 d 𝕫 x Q ∧ Q u ∈ gmHalf j := key.symm
      _ ↔ geodL d 𝕫 𝕨 (η ω) (sk ω * u) ∈ gmHalf j := by
          constructor
          · rintro ⟨Q, hQ, hQu⟩
            rwa [gm_geod01_eq_of_unique hηω.2 hP hs hsL hQ u] at hQu
          · intro hm
            obtain ⟨Q, hQ⟩ := gm_exists_geod01_of_lenSet hlenω 𝕫 x
            exact ⟨Q, hQ, by rwa [gm_geod01_eq_of_unique hηω.2 hP hs hsL hQ u]⟩

end LQGMetric.GM
