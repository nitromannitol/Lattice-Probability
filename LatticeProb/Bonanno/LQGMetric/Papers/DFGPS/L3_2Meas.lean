/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_2Meas at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 3.2, measurability step (task P2-L32)

DFGPS = Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380,
`literature/src/1905.00380/lqg-metric-estimates-final.tex` ("T"), proof of Lemma 3.2, T:1476:
"By the locality of `D_h` and Axiom III, the event `E_r(z;C)` is determined by
`(h − h_{3r}(z))|_{𝔸_{r/2,2r}(z)}`."

We prove it in the form needed by LM Lemma 3.1 (`Blueprint.LMLem3_1a`): `E_r(z;C)` is a.s. equal
to an event of `σ((h − h_{3r}(z))|_{𝔸_{r/2,5r/2}(z)})` (`aeEventIn_annEvent`), and then, after
translating the centre to `0` and normalizing the field (as in `GM.aeEventIn_goodAnnulus_translate`),
an event of the σ-algebra in `AnnulusIterHyp` with `r_k = 3ρ`, `s₁ = 1/6`, `s₂ = 5/6`
(`annEvent_translate`).

Steps (the paper's "locality and Axiom III"):
* Weyl scaling by the constant `−h_{3r}(z)` (Axiom III, `IsWeakLQGMetric.ae_dist_addConst`) turns
  `E_r(z;C)` for `h` into `E_r(z;C)` for `h̃ = h − h_{3r}(z)` (`mem_annEvent_iff`);
* the internal diameter of `∂B_r(z)` in `U = 𝔸_{r/2,2r}(z)` is the supremum of `D_{h̃}(·,·;U)`
  over the pairs of a dense sequence of `∂B_r(z)` (continuity of internal metrics of length
  metrics, LM Lemma 1.1 = `ContMetric.continuousOn_internal`), and `D_{h̃}(∂B_r, ∂B_{2r})` is the
  infimum of `D_{h̃}(·,·;U')` over dense pairs, `U' = 𝔸_{r/2,5r/2}(z)`
  (`GM.setDist_spheres_eq_internal`);
* these internal distances are functions of `h̃|_U`, `h̃|_{U'}` (Axiom II, locality), and
  `h̃_r(z)` is `σ(h̃|_{U'})`-measurable (`GM.measurable_circleAvg_fieldSigma`).

Departure (DEV, proposed): the σ-algebra is that of the slightly larger annulus
`𝔸_{r/2,5r/2}(z)` instead of `𝔸_{r/2,2r}(z)`, because `∂B_{2r}(z)` is not inside the open annulus
`𝔸_{r/2,2r}(z)`; LM Lemma 3.1 is applied with `s₂ = 5/6` (any `s₂ < 1` is allowed there), so the
proof of Lemma 3.2 is unaffected.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric Topology
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

namespace L32M

/-- a dense sequence of a nonempty subset of `ℂ` -/
lemma exists_denseSeq {S : Set ℂ} (hS : S.Nonempty) :
    ∃ q : ℕ → ℂ, (∀ n, q n ∈ S) ∧ S ⊆ closure (range q) := by
  have : Nonempty S := hS.to_subtype
  refine ⟨fun n => (TopologicalSpace.denseSeq S n : ℂ), fun n => (TopologicalSpace.denseSeq S n).2,
    ?_⟩
  intro x hx
  rw [_root_.mem_closure_iff]
  intro o ho hxo
  obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq S).exists_mem_open
    (ho.preimage continuous_subtype_val) ⟨⟨x, hx⟩, hxo⟩
  exact ⟨_, hn, n, rfl⟩

/-- a function continuous on `V ×ˢ V` with values at the pairs of two dense sequences in a closed
set `Z` takes values in `Z` on the closures -/
lemma mem_of_dense {f : ℂ × ℂ → ℝ≥0∞} {V A B : Set ℂ} (hf : ContinuousOn f (V ×ˢ V))
    {a b : ℕ → ℂ} (ha : ∀ n, a n ∈ V) (hb : ∀ n, b n ∈ V)
    (hA : A ⊆ closure (range a)) (hB : B ⊆ closure (range b)) {Z : Set ℝ≥0∞} (hZ : IsClosed Z)
    (hT : ∀ i j, f (a i, b j) ∈ Z) {x y : ℂ} (hx : x ∈ A) (hy : y ∈ B) (hxV : x ∈ V)
    (hyV : y ∈ V) : f (x, y) ∈ Z := by
  have hs : range (Prod.map a b) ⊆ V ×ˢ V := by
    rintro _ ⟨⟨i, j⟩, rfl⟩; exact ⟨ha i, hb j⟩
  have hmem : (x, y) ∈ closure (range (Prod.map a b)) := by
    rw [range_prodMap, closure_prod_eq]; exact ⟨hA hx, hB hy⟩
  have := ContinuousWithinAt.mem_closure_image ((hf (x, y) ⟨hxV, hyV⟩).mono hs) hmem
  refine closure_minimal ?_ hZ this
  rintro _ ⟨_, ⟨⟨i, j⟩, rfl⟩, rfl⟩
  exact hT i j

/-- the internal diameter is a countable supremum (length metrics) -/
lemma internalDiam_eq_iSup (d : ContMetric) (hd : d.IsLength) {V A : Set ℂ} (hV : IsOpen V)
    (hAV : A ⊆ V) {a : ℕ → ℂ} (haA : ∀ n, a n ∈ A) (hA : A ⊆ closure (range a)) :
    internalDiam d A V = ⨆ p : ℕ × ℕ, d.internal V (a p.1) (a p.2) := by
  refine le_antisymm (iSup₂_le fun u hu => iSup₂_le fun v hv => ?_) (iSup_le fun p => ?_)
  · exact mem_of_dense (f := fun p : ℂ × ℂ => d.internal V p.1 p.2)
      (d.continuousOn_internal hd hV) (fun n => hAV (haA n)) (fun n => hAV (haA n)) hA hA
      isClosed_Iic (fun i j => le_iSup (fun p : ℕ × ℕ => d.internal V (a p.1) (a p.2)) (i, j))
      hu hv (hAV hu) (hAV hv)
  · exact le_iSup₂_of_le (a p.1) (haA p.1) (le_iSup₂_of_le (a p.2) (haA p.2) le_rfl)

/-- the distance across an annulus is a countable infimum of internal distances -/
lemma setDist_eq_iInf_dense (d : ContMetric) (hd : d.IsLength) {V : Set ℂ} (hV : IsOpen V)
    {z : ℂ} {ρ₁ ρ₂ : ℝ} (h12 : ρ₁ < ρ₂)
    (hsub : ∀ w : ℂ, ρ₁ ≤ ‖w - z‖ → ‖w - z‖ ≤ ρ₂ → w ∈ V) {a b : ℕ → ℂ}
    (ha : ∀ n, a n ∈ sphere z ρ₁) (hb : ∀ n, b n ∈ sphere z ρ₂)
    (hA : sphere z ρ₁ ⊆ closure (range a)) (hB : sphere z ρ₂ ⊆ closure (range b)) :
    setDist d (sphere z ρ₁) (sphere z ρ₂) = ⨅ p : ℕ × ℕ, d.internal V (a p.1) (b p.2) := by
  have h1 : sphere z ρ₁ ⊆ V := fun w hw =>
    hsub w (mem_sphere_iff_norm.1 hw).ge (by rw [mem_sphere_iff_norm.1 hw]; exact h12.le)
  have h2 : sphere z ρ₂ ⊆ V := fun w hw =>
    hsub w (by rw [mem_sphere_iff_norm.1 hw]; exact h12.le) (mem_sphere_iff_norm.1 hw).le
  rw [GM.setDist_spheres_eq_internal d hd h12 hsub]
  refine le_antisymm (le_iInf fun p => iInf₂_le_of_le (a p.1) (ha p.1)
    (iInf₂_le_of_le (b p.2) (hb p.2) le_rfl)) (le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_)
  exact mem_of_dense (f := fun p : ℂ × ℂ => d.internal V p.1 p.2)
    (d.continuousOn_internal hd hV) (fun n => h1 (ha n)) (fun n => h2 (hb n)) hA hB isClosed_Ici
    (fun i j => iInf_le (fun p : ℕ × ℕ => d.internal V (a p.1) (b p.2)) (i, j)) hx hy
    (h1 hx) (h2 hy)

lemma internalDiam_of_scale {D₁ D₂ : ContMetric} {e : ℝ} (he : 0 < e)
    (h : ∀ u v, D₂.1 (u, v) = e * D₁.1 (u, v)) (A V : Set ℂ) :
    internalDiam D₂ A V = ENNReal.ofReal e * internalDiam D₁ A V := by
  simp only [internalDiam, GM.internal_of_scale he h, ENNReal.mul_iSup]

/-- the countable data of `E_r(z;C)`: internal distances at dense pairs and `h_r(z)` -/
def annData (ξ : ℝ) (c : ℝ → ℝ) (C r : ℝ) :
    Set ((ℕ × ℕ → ℝ≥0∞) × (ℕ × ℕ → ℝ≥0∞) × ℝ) :=
  {x | (⨆ p, x.1 p) ≤ ENNReal.ofReal (C * (c r * Real.exp (ξ * x.2.2))) ∧
    ENNReal.ofReal (C⁻¹ * (c r * Real.exp (ξ * x.2.2))) ≤ ⨅ p, x.2.1 p}

lemma measurableSet_annData (ξ : ℝ) (c : ℝ → ℝ) (C r : ℝ) :
    MeasurableSet (annData ξ c C r) := by
  have h1 : Measurable fun x : (ℕ × ℕ → ℝ≥0∞) × (ℕ × ℕ → ℝ≥0∞) × ℝ => ⨆ p, x.1 p :=
    Measurable.iSup fun p => (measurable_pi_apply p).comp measurable_fst
  have h2 : Measurable fun x : (ℕ × ℕ → ℝ≥0∞) × (ℕ × ℕ → ℝ≥0∞) × ℝ => ⨅ p, x.2.1 p :=
    Measurable.iInf fun p => (measurable_pi_apply p).comp (measurable_fst.comp measurable_snd)
  have h3 : Measurable fun x : (ℕ × ℕ → ℝ≥0∞) × (ℕ × ℕ → ℝ≥0∞) × ℝ =>
      c r * Real.exp (ξ * x.2.2) :=
    (Real.measurable_exp.comp ((measurable_snd.comp measurable_snd).const_mul ξ)).const_mul _
  exact (measurableSet_le h1 (ENNReal.measurable_ofReal.comp (h3.const_mul C))).inter
    (measurableSet_le (ENNReal.measurable_ofReal.comp (h3.const_mul C⁻¹)) h2)

/-- **T:1476, deterministic part**: for `g' = g + t` with `D_{g'} = e^{ξt} D_g` a length metric
and `g'_r(z) = g_r(z) + t`, `g ∈ E_r(z;C)` iff the countable data of `g'` lie in `annData`. -/
theorem mem_annEvent_iff {ξ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {C r : ℝ} (hr : 0 < r)
    {z : ℂ} {g g' : DistC} {t : ℝ} (hl : (D g').IsLength)
    (hsc : ∀ u v, (D g').1 (u, v) = Real.exp (ξ * t) * (D g).1 (u, v))
    (hav : circleAvg g' r z = circleAvg g r z + t)
    {a b : ℕ → ℂ} (ha : ∀ n, a n ∈ sphere z r) (hb : ∀ n, b n ∈ sphere z (2 * r))
    (hA : sphere z r ⊆ closure (range a)) (hB : sphere z (2 * r) ⊆ closure (range b)) :
    g ∈ annEvent ξ D c C r z ↔
      ((fun p : ℕ × ℕ => (D g').internal (annulus z (r / 2) (2 * r)) (a p.1) (a p.2)),
        (fun p : ℕ × ℕ => (D g').internal (annulus z (r / 2) (5 / 2 * r)) (a p.1) (b p.2)),
        circleAvg g' r z) ∈ annData ξ c C r := by
  have he := Real.exp_pos (ξ * t)
  have hc0 : ENNReal.ofReal (Real.exp (ξ * t)) ≠ 0 := (ENNReal.ofReal_pos.2 he).ne'
  have hct : ENNReal.ofReal (Real.exp (ξ * t)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hle : ∀ x y : ℝ≥0∞, ENNReal.ofReal (Real.exp (ξ * t)) * x ≤
      ENNReal.ofReal (Real.exp (ξ * t)) * y ↔ x ≤ y := fun x y =>
    ENNReal.mul_le_mul_iff_right hc0 hct
  have hU : sphere z r ⊆ (annulus z (r / 2) (2 * r) : Set ℂ) := fun w hw => by
    have := mem_sphere_iff_norm.1 hw
    show r / 2 < ‖w - z‖ ∧ ‖w - z‖ < 2 * r
    rw [this]; constructor <;> linarith
  have hD1 := internalDiam_eq_iSup (D g') hl (annulus z (r / 2) (2 * r)).isOpen hU ha hA
  have hD2 := setDist_eq_iInf_dense (D g') hl (annulus z (r / 2) (5 / 2 * r)).isOpen
    (by linarith : r < 2 * r)
    (fun w h1 h2 => show r / 2 < ‖w - z‖ ∧ ‖w - z‖ < 5 / 2 * r from
      ⟨by linarith, by linarith⟩) ha hb hA hB
  have hsf : ∀ K : ℝ, K * (c r * Real.exp (ξ * circleAvg g' r z)) =
      Real.exp (ξ * t) * (K * scaleFac ξ c g r z) := fun K => by
    rw [hav, scaleFac, mul_add, Real.exp_add]; ring
  simp only [annData, mem_ofPred_eq, ← hD1, ← hD2, hsf, ENNReal.ofReal_mul he.le,
    internalDiam_of_scale he hsc, GM.setDist_of_scale he hsc, hle]
  rfl

end L32M

open L32M in
/-- **DFGPS T:1476**: `E_r(z;C)` is a.s. an event of `σ((h − h_{3r}(z))|_{𝔸_{r/2,5r/2}(z)})`. -/
theorem aeEventIn_annEvent {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (C : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) :
    ∃ E : Set Ω, MeasurableSet[fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) (3 * r) z))
      (annulus z (r / 2) (5 / 2 * r))] E ∧ E =ᵐ[P] h ⁻¹' annEvent (xiGamma γ) D c C r z := by
  set ht : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) (3 * r) z) with ht_def
  have hm : Measurable fun ω => -circleAvg (h ω) (3 * r) z :=
    ((measurable_circleAvg_left (3 * r) z).comp hh.measurable).neg
  have hX : IsWholePlaneGFF ht P := hh.addConst hm
  have hgp := GM.Tight.isGFFPlusCont_of_wp hX
  set U := annulus z (r / 2) (2 * r) with hU_def
  set U' := annulus z (r / 2) (5 / 2 * r) with hU'_def
  have hUU' : U ≤ U' := fun w hw =>
    show r / 2 < ‖w - z‖ ∧ ‖w - z‖ < 5 / 2 * r from ⟨hw.1, by linarith [hw.2]⟩
  have hSU : sphere z r ⊆ (U : Set ℂ) := fun w hw => by
    have := mem_sphere_iff_norm.1 hw
    show r / 2 < ‖w - z‖ ∧ ‖w - z‖ < 2 * r
    rw [this]; constructor <;> linarith
  have hSU' : sphere z (2 * r) ⊆ (U' : Set ℂ) := fun w hw => by
    have := mem_sphere_iff_norm.1 hw
    show r / 2 < ‖w - z‖ ∧ ‖w - z‖ < 5 / 2 * r
    rw [this]; constructor <;> linarith
  obtain ⟨Φ, hΦ, hΦae⟩ := hD.locality P ht hgp U
  obtain ⟨Φ', hΦ', hΦae'⟩ := hD.locality P ht hgp U'
  obtain ⟨a, haS, haD⟩ := exists_denseSeq (S := sphere z r) (NormedSpace.sphere_nonempty.2 hr.le)
  obtain ⟨b, hbS, hbD⟩ := exists_denseSeq (S := sphere z (2 * r))
    (NormedSpace.sphere_nonempty.2 (by linarith))
  set V : Ω → (ℕ × ℕ → ℝ≥0∞) × (ℕ × ℕ → ℝ≥0∞) × ℝ := fun ω =>
    (fun p => Φ (restrictTo U (ht ω)) (a p.1) (a p.2),
      fun p => Φ' (restrictTo U' (ht ω)) (a p.1) (b p.2), circleAvg (ht ω) r z) with hV_def
  have hV : Measurable[fieldSigma ht U'] V := by
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
    · have hG : Measurable fun x : DistOn U => fun p : ℕ × ℕ => Φ x (a p.1) (a p.2) :=
        measurable_pi_iff.2 fun p => (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hΦ)
      exact (hG.comp (Measurable.of_comap_le le_rfl)).mono (GM.fieldSigma_mono ht hUU') le_rfl
    · have hG : Measurable fun x : DistOn U' => fun p : ℕ × ℕ => Φ' x (a p.1) (b p.2) :=
        measurable_pi_iff.2 fun p => (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hΦ')
      exact hG.comp (Measurable.of_comap_le le_rfl)
    · refine (GM.measurable_circleAvg_fieldSigma ht r z (show (0 : ℝ) < r / 2 by linarith)).mono
        (GM.fieldSigma_mono ht ?_) le_rfl
      intro w hw
      obtain ⟨y, hy, hwy⟩ := mem_thickening_iff.1 hw
      have hyz : dist y z = r := by rw [mem_sphere.1 hy, abs_of_pos hr]
      have t1 := dist_triangle w y z
      have t2 := dist_triangle y w z
      rw [dist_comm y w] at t2
      show r / 2 < ‖w - z‖ ∧ ‖w - z‖ < 5 / 2 * r
      rw [← dist_eq_norm]; constructor <;> linarith
  refine ⟨V ⁻¹' annData (xiGamma γ) c C r, hV (measurableSet_annData _ _ _ _), ?_⟩
  filter_upwards [hΦae, hΦae', hD.length P ht hgp,
    hD.ae_dist_addConst (GM.Tight.isGFFPlusCont_of_wp hh),
    CircleAvg.ae_circleAvg_addConst hh z hr] with ω h1 h2 hl hsc hav
  have eV : V ω = ((fun p : ℕ × ℕ => (D (ht ω)).internal U (a p.1) (a p.2)),
      (fun p : ℕ × ℕ => (D (ht ω)).internal U' (a p.1) (b p.2)), circleAvg (ht ω) r z) :=
    Prod.ext (funext fun p => (h1 _ (hSU (haS _)) _ (hSU (haS _))).symm)
      (Prod.ext (funext fun p => (h2 _ (hUU' (hSU (haS _))) _ (hSU' (hbS _))).symm) rfl)
  show (V ω ∈ annData (xiGamma γ) c C r) = (h ω ∈ annEvent (xiGamma γ) D c C r z)
  rw [eV]
  exact propext (mem_annEvent_iff hr hl (hsc _) (hav _) haS hbS haD hbD).symm

/-- **T:1476 at the centre `0`**: the events `E_ρ(z;C)`, as events of the translated normalized
field `h(· + z) − h_1(z)` on `𝔸_{(3ρ)/6, 5(3ρ)/6}(0)`, normalized at radius `3ρ` (the form of
`AnnulusIterHyp`, as in `GM.aeEventIn_goodAnnulus_translate`). -/
theorem annEvent_translate {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (C : ℝ) (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) :
    ∃ E : Set Ω, MeasurableSet[fieldSigma (fun ω =>
        addConst (addConst (affineComp 1 z (h ω)) (-circleAvg (affineComp 1 z (h ω)) 1 0))
          (-circleAvg (addConst (affineComp 1 z (h ω)) (-circleAvg (affineComp 1 z (h ω)) 1 0))
            (3 * ρ) 0)) (annulus 0 (1 / 6 * (3 * ρ)) (5 / 6 * (3 * ρ)))] E ∧
      E =ᵐ[P] h ⁻¹' annEvent (xiGamma γ) D c C ρ z := by
  obtain ⟨F, hF, hFae⟩ := aeEventIn_annEvent hD C z hρ P h hh
  have hUV : ∀ y : ℂ, y ∈ annulus 0 (1 / 6 * (3 * ρ)) (5 / 6 * (3 * ρ)) ↔
      (1 : ℝ) • y + z ∈ annulus z (ρ / 2) (5 / 2 * ρ) := fun y => by
    show 1 / 6 * (3 * ρ) < ‖y - 0‖ ∧ ‖y - 0‖ < 5 / 6 * (3 * ρ) ↔
      ρ / 2 < ‖(1 : ℝ) • y + z - z‖ ∧ ‖(1 : ℝ) • y + z - z‖ < 5 / 2 * ρ
    simp only [sub_zero, one_smul, add_sub_cancel_right]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hF2 := GM.fieldSigma_le_affineComp one_pos hUV _ F hF
  obtain ⟨B, hB, hBF⟩ := hF2
  refine ⟨_, ⟨B, hB, rfl⟩, ?_⟩
  have hz := hh.affineComp one_pos z
  refine EventuallyEq.trans ?_ hFae
  rw [← hBF]
  filter_upwards [CircleAvg.ae_circleAvg_addConst hz 0 (show (0 : ℝ) < 3 * ρ by positivity)]
    with ω hω
  simp only [mem_preimage]
  rw [GM.affineComp_addConst one_pos, hω, GM.Tight.circleAvg_affineComp_one,
    GM.Tight.circleAvg_affineComp_one, GFFLaw.addConst_addConst]
  congr! 3
  ring

end LQGMetric.DFGPS
