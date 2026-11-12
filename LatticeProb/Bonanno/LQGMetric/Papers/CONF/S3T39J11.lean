/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39J11 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J5
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J9

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9 from the remaining node `CONFThm3_9RestCL` (D130, packet W-2)

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
Theorem 3.9 (C:1506–1509), proof C:1512–1744; decision D130 (decisions/DEC-130.md §3, §5).
The Blueprint `CONFThm3_9At` assumes, besides the stopping-time property, that `𝓑^•_τ` is a local
set of `h` modulo additive constants (`IsLocalSetDet0`, D130; CONF C:1431 via L2.1 with `h`
modulo constants, C:1154). The remaining node is `CONFThm3_9RestCL` (S3T39J9), which carries the
same hypothesis.

* **`confThm3_9IterC'_of_restCL`**: `CONFThm3_9IterC'` (S3T39J5) from Lemma 3.6, DFGPS Lemma 3.8
  and `CONFThm3_9RestCL`; copy of the former `confThm3_9IterC'_of_restC` (S3T39J5, removed by
  D130), itself a copy-and-adapt of `confThm3_9Iter'_of_rest` (S3T39I5).
* **`confThm3_9At_of_restCL`**: `CONFThm3_9At` by `confThm3_9AtC_of_iterAE` (S3T39J5) and the
  completion transfer `confThm3_9At_of_complete` (S3T39J4).

`H35 : CONFLem3_5At γ D c p` and `hη : 0 < p.η` are part of the D130 signatures (they are the
hypotheses of `confThm3_9RestCL_of_J6`, the producer of `CONFThm3_9RestCL`); they are not used
in these two assembly steps.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open LQGMetric.Blueprint LQGMetric.GM
open scoped ENNReal

namespace LQGMetric
namespace CONF

/-- **`CONFThm3_9IterC'` from Lemma 3.6, DFGPS Lemma 3.8 and `CONFThm3_9RestCL`** (D130); `N₁` of
the node is combined with `t39i_hN₀`'s by `max` -/
theorem confThm3_9IterC'_of_restCL (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams} {χ : ℝ} (hD : IsWeakLQGMetric γ D c)
    (_H35 : CONFLem3_5At γ D c p) (_hη : 0 < p.η) (H36 : CONFLem3_6AtAE0 γ D c p)
    (H : CONFThm3_9RestCL γ D c p χ) :
    CONFThm3_9IterC' γ D c p χ := by
  obtain ⟨α, C₀, hα, hC₀, hL⟩ := confLem3_7AtAE0_of_36 H36
  refine ⟨α, C₀, hα, by linarith, fun a ha => ?_⟩
  obtain ⟨N₁, HN⟩ := H a ha
  obtain ⟨N₂, hN₂⟩ := t39i_hN₀ ha.1
  refine ⟨max N₁ N₂, fun P _ _ h hh z₀ R hR τ hτst hloc0 hτI => ?_⟩
  have hgood := t39h_tau_ae h38 hγ hγ2 hD P h hh z₀ hR τ hτI
  obtain ⟨A, hsep, hdata⟩ := HN P h hh z₀ R hR τ hτst hloc0 hτI
  refine ⟨hgood.mono fun ω hω => ⟨hω.1, hω.2.2.2 _⟩, A, hsep, fun m => ?_⟩
  obtain ⟨s, n, x, Act, hI₀, hs0, hsucc, hn, hsnn, hsm, hst, hloc, hmono, hnm, hxm, hxf, hActm,
    hAct, hstar⟩ := hdata m
  exact t39j_iterData_of hL hD.measurable hh hR ha.1 (A m) τ s n x Act hI₀ hs0 hsucc hn hsnn hsm
    hst hloc hmono hnm hxm hxf hActm hAct
    (hstar.mono fun ω hω hωE k hk hN => hω hωE k hk ((le_max_left _ _).trans hN)) hgood
    (fun m' hm' => hN₂ m' ((le_max_right _ _).trans hm'))

/-- **CONF Theorem 3.9** (C:1506, Blueprint form with the D130 locality hypothesis on `τ`) from
Lemma 3.6, DFGPS Lemma 3.8 and `CONFThm3_9RestCL` (complete spaces), by the completion transfer
`confThm3_9At_of_complete` (S3T39J4) -/
theorem confThm3_9At_of_restCL (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams} {χ : ℝ} (hD : IsWeakLQGMetric γ D c)
    (hχ : 0 < χ) (H35 : CONFLem3_5At γ D c p) (hη : 0 < p.η) (H36 : CONFLem3_6AtAE0 γ D c p)
    (H : CONFThm3_9RestCL γ D c p χ) :
    CONFThm3_9At γ D c p χ :=
  confThm3_9At_of_complete (confThm3_9AtC_of_iterAE hχ hD.tightness.1
    (confThm3_9IterC'_of_restCL h38 hγ hγ2 hD H35 hη H36 H))

end CONF
end LQGMetric
