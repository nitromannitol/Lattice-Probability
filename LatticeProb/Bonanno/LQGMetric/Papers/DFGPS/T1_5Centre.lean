/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T1_5Centre at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5Trans
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Nodes
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightLaw
import LatticeProb.Bonanno.LQGMetric.Metric.InternalOps

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
DFGPS (arXiv:1905.00380, "T"), proof of Theorem 1.5, Step 1 (T:1662–1670): "By Proposition 3.1
and a union bound over all `z ∈ (𝕣𝕊) ∩ (δ𝕣ℤ²)` …". Proposition 3.1 is stated at the centre `0`;
DFGPS use it at the centres `z` through translation invariance (Axiom IV′ of a weak LQG metric,
GM l. 438, together with the translation invariance of the law of `h(· + z) - h_1(z)`). On the
canonical space `(DistC, μ, id)` we show that the event at the centre `z` for `g` coincides a.s.
with the event at `0` for the recentred translate `T_z g = g(· + z) - g_1(z)`
(`transField`), using the three a.s. identities
* `D_{T_z g} = e^{-ξ g_1(z)} D_g(· + z, · + z)` (Axiom IV′ + Axiom III with a constant, GM.S1.6
  `IsWeakLQGMetric.ae_dist_addConst`);
* `(T_z g)_𝕣(0) = g_𝕣(z) - g_1(z)`;
* internal distances scale and translate (`MetricGeometry.internalEDist_image_of_edist_eq`),
and conclude with `measure_preimage_transField_le`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

/-- internal distances of `D' = a·D(· + z, · + z)` -/
lemma internal_transl_smul {D D' : ContMetric} {a : ℝ} (ha : 0 < a) (z : ℂ)
    (h : ∀ u v, D'.1 (u, v) = a * D.1 (u + z, v + z)) (W : Set ℂ) (x y : ℂ) :
    D'.internal ((fun w => w - z) '' W) (x - z) (y - z) = ENNReal.ofReal a * D.internal W x y := by
  let e : D.Space ≃ D'.Space := (Equiv.subRight z : ℂ ≃ ℂ)
  have he : ∀ p q : D.Space, edist (e p) (e q) = ENNReal.ofReal a * edist p q := fun p q => by
    rw [edist_dist, edist_dist]
    show ENNReal.ofReal (D'.1 ((Equiv.subRight z : ℂ ≃ ℂ) p, (Equiv.subRight z : ℂ ≃ ℂ) q)) =
      ENNReal.ofReal a * ENNReal.ofReal (D.1 (p, q))
    rw [h]
    show ENNReal.ofReal (a * D.1 (((show ℂ from p) - z) + z, ((show ℂ from q) - z) + z)) = _
    rw [sub_add_cancel, sub_add_cancel, ENNReal.ofReal_mul ha.le]
  have := MetricGeometry.internalEDist_image_of_edist_eq e (ENNReal.ofReal_pos.2 ha).ne'
    ENNReal.ofReal_ne_top he (D.pt '' W) x y
  unfold ContMetric.internal
  convert this using 2
  all_goals first | rfl | (simp only [image_image]; rfl)

/-- `setDistIn` of `D' = a·D(· + z, · + z)` on translated sets -/
lemma setDistIn_transl_smul {D D' : ContMetric} {a : ℝ} (ha : 0 < a) (z : ℂ)
    (h : ∀ u v, D'.1 (u, v) = a * D.1 (u + z, v + z)) (A B W : Set ℂ) :
    setDistIn D' ((fun w => w - z) '' A) ((fun w => w - z) '' B) ((fun w => w - z) '' W) =
      ENNReal.ofReal a * setDistIn D A B W := by
  have h0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.2 ha).ne'
  unfold setDistIn
  simp only [iInf_image, internal_transl_smul ha z h]
  simp_rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]

lemma scaleSet_zero_eq_image (r : ℝ) (z : ℂ) (K : Set ℂ) :
    scaleSet r 0 K = (fun w => w - z) '' scaleSet r z K := by
  unfold scaleSet
  rw [image_image]
  simp

/-- `setDistIn` on `𝕣K` for `D' = a·D(· + z, · + z)` equals `a` times `setDistIn` on `𝕣K + z` -/
lemma setDistIn_scaleSet_transl {D D' : ContMetric} {a : ℝ} (ha : 0 < a) (z : ℂ)
    (h : ∀ u v, D'.1 (u, v) = a * D.1 (u + z, v + z)) (r : ℝ) (K₁ K₂ U : Set ℂ) :
    setDistIn D' (scaleSet r 0 K₁) (scaleSet r 0 K₂) (scaleSet r 0 U) =
      ENNReal.ofReal a * setDistIn D (scaleSet r z K₁) (scaleSet r z K₂) (scaleSet r z U) := by
  rw [scaleSet_zero_eq_image r z K₁, scaleSet_zero_eq_image r z K₂,
    scaleSet_zero_eq_image r z U]
  exact setDistIn_transl_smul ha z h _ _ _

/-- the two a.s. identities for the recentred translate on the canonical space -/
lemma ae_transField_ident {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {μ : Measure DistC} [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWPGFF id μ) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ g ∂μ, (∀ u v, (D (transField z g)).1 (u, v) =
        Real.exp (-(xiGamma γ * circleAvg g 1 z)) * (D g).1 (u + z, v + z)) ∧
      circleAvg (transField z g) r 0 = circleAvg g r z - circleAvg g 1 z := by
  have hw : IsWholePlaneGFF (fun g : DistC => affineComp 1 z g) μ := hμ.1.affineComp one_pos z
  filter_upwards [hD.translation μ id (GM.Tight.isGFFPlusCont_of_wp hμ.1) z,
    hD.ae_dist_addConst (GM.Tight.isGFFPlusCont_of_wp hw),
    CircleAvg.ae_circleAvg_addConst hw 0 hr] with g h1 h2 h3
  refine ⟨fun u v => ?_, ?_⟩
  · rw [transField, h2, mul_neg]
    exact congrArg _ (h1 u v)
  · rw [transField, h3, GM.Tight.circleAvg_affineComp_one, sub_eq_add_neg]

/-- **DFGPS Prop 3.1 at every centre**, constants uniform in the centre `z` (canonical space). -/
theorem prop3_1_centre (h31 : Prop3_1) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {U K₁ K₂ : Set ℂ}
    (hU : IsOpen U) (hUc : IsConnected U) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) (hc₁ : IsConnected K₁)
    (hc₂ : IsConnected K₂) (h₁ : K₁ ⊆ U) (h₂ : K₂ ⊆ U) (hd : Disjoint K₁ K₂)
    (hn₁ : ¬ K₁.Subsingleton) (hn₂ : ¬ K₂.Subsingleton)
    {μ : Measure DistC} [IsProbabilityMeasure μ] (hμ : IsNormalizedWPGFF id μ) :
    ∀ p : ℝ, 0 < p → ∃ C A₀ : ℝ, ∀ A, A₀ < A → ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ z : ℂ,
      μ {g | ENNReal.ofReal (A⁻¹ * scaleFac (xiGamma γ) c g 𝕣 z) ≤
            setDistIn (D g) (scaleSet 𝕣 z K₁) (scaleSet 𝕣 z K₂) (scaleSet 𝕣 z U) ∧
          setDistIn (D g) (scaleSet 𝕣 z K₁) (scaleSet 𝕣 z K₂) (scaleSet 𝕣 z U) ≤
            ENNReal.ofReal (A * scaleFac (xiGamma γ) c g 𝕣 z)}ᶜ ≤
        ENNReal.ofReal (C * A ^ (-p)) := by
  intro p hp
  obtain ⟨C, A₀, hCA⟩ := h31 γ hγ0 hγ2 D c hD U K₁ K₂ hU hUc hK₁ hK₂ hc₁ hc₂ h₁ h₂ hd hn₁ hn₂ μ id
    hμ p hp
  refine ⟨C, A₀, fun A hA r hr z => ?_⟩
  refine le_trans ?_ ((measure_preimage_transField_le hμ z _).trans (hCA A hA r hr))
  apply measure_mono_ae
  filter_upwards [ae_transField_ident hD hμ z hr] with g ⟨hd1, hd2⟩
  intro hg hE
  apply hg
  set a := Real.exp (-(xiGamma γ * circleAvg g 1 z)) with ha_def
  have ha : 0 < a := Real.exp_pos _
  have hS : scaleFac (xiGamma γ) c (transField z g) r 0 = a * scaleFac (xiGamma γ) c g r z := by
    unfold scaleFac
    rw [hd2, mul_sub, sub_eq_add_neg, Real.exp_add, ha_def]
    ring
  have hX := setDistIn_scaleSet_transl ha z hd1 r K₁ K₂ U
  simp only [mem_ofPred_eq, id] at hE
  rw [hS, hX] at hE
  have h0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.2 ha).ne'
  rw [mul_left_comm, ENNReal.ofReal_mul ha.le, mul_left_comm A, ENNReal.ofReal_mul ha.le,
    ENNReal.mul_le_mul_iff_right h0 ENNReal.ofReal_ne_top,
    ENNReal.mul_le_mul_iff_right h0 ENNReal.ofReal_ne_top] at hE
  exact hE

end LQGMetric.DFGPS
