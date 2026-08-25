/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# The planar co-area formula — foundational lemmas

This is the first of three files building the sharp planar co-area (Eilenberg) inequality
`eilenberg_coarea_grad_le` (assembled in `Coarea.Assembly`); Mathlib has no co-area formula, so it
is built from scratch. This file collects the foundations:

* `measurable_slice_hausdorff_one` — measurability of `c ↦ μH[1] (u ⁻¹' {c} ∩ A)` for compact `A`
  (compact-image / countable-open-cover argument with `Metric.thickening`);
* `eilenberg_coarea_planar_metric` — the raw (Lipschitz-constant) metric Eilenberg inequality
  `∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) ≤ K · μH[2] A` on a compact set;
* `hausdorffMeasure_two_complex_smul_volume` — the normalization `μH[2] = c • volume` on `ℂ`
  (proportionality, not equality: the raw Hausdorff measure differs from `volume` by `4/π`);
* `coarea_linear_eq` — the exact affine co-area `∫⁻ c, μH[1] (L ⁻¹' {c} ∩ B) = ‖L‖ · volume B`;
* `hausdorffMeasure_one_image_le` — the fiber arc-length bound `μH[1] (γ '' I) ≤ ∫⁻ ‖γ'‖`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace NoWanderingDomains.Coarea

/-! ## Slice measurability — the gating crux of the co-area construction -/

/-- **Measurability of the level-set arc-length in the level parameter (gating crux).**

For a continuous `u : ℂ → ℝ` and a compact set `A ⊆ ℂ`, the map
`c ↦ μH[1] (u ⁻¹' {c} ∩ A)` (the `μH[1]`-measure of the level set `{u = c}` restricted to `A`) is
Borel measurable in `c`.

This is the single technical ingredient that lets the co-area set function
`A ↦ ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A)` be assembled into a genuine measure `ν` (via `lintegral_tsum`
for countable additivity) and is therefore the gate to the Besicovitch-differentiation localization
that proves the sharp co-area inequality `eilenberg_coarea_grad_le`. Mathlib's only parameter
measurability (`measurable_measure_prodMk_left`) covers *product* slices; the level sets of a
general continuous `u` are curves, not product fibers, so this is net-new.

## Truth and direction

Proof strategy (compact `A`, separable target): write
`μH[1] (S) = ⨆ n, μH[1]_{1/n} (S)` with `μH[1]_r` the Hausdorff premeasure
(`Measure.mkMetric'.pre`), and bound each premeasure by countable open covers. For a fixed countable
cover `{Tᵢ}` (open, `diam ≤ r`), the cover is *valid for `c`* (i.e. covers `u ⁻¹' {c} ∩ A`) iff
`c ∉ u '' (A ∩ (⋃ᵢ Tᵢ)ᶜ)`; with `A` compact and the `Tᵢ` open, `A ∩ (⋃ Tᵢ)ᶜ` is compact, so its
continuous image `u '' (…)` is **compact** (Borel), making `c ↦ [valid? ∑ diam : ∞]` measurable.
A countable infimum over such covers recovers `μH[1]_{1/n}` (separability), and a countable
supremum over `n` recovers `μH[1]`. The compactness of `A` (so that `u`-images of the complement
pieces are compact = Borel) is what avoids needing the universal measurability of analytic sets. -/
theorem measurable_slice_hausdorff_one {u : ℂ → ℝ} (hu : Continuous u)
    {A : Set ℂ} (hA : IsCompact A) :
    Measurable (fun c => μH[1] (u ⁻¹' {c} ∩ A)) := by
  classical
  -- A countable dense enumeration of `ℂ`, for rational-ball centres.
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℂ, DenseRange D :=
    ⟨TopologicalSpace.denseSeq ℂ, TopologicalSpace.denseRange_denseSeq ℂ⟩
  -- Rational balls, finite unions of them (`elem`), and finite collections of those (`scover`).
  set ball' : ℕ × ℚ → Set ℂ := fun p => Metric.ball (D p.1) (p.2 : ℝ) with hball'
  have hballopen : ∀ p, IsOpen (ball' p) := fun p => Metric.isOpen_ball
  set elem : Finset (ℕ × ℚ) → Set ℂ := fun s => ⋃ p ∈ s, ball' p with helem
  have helem_open : ∀ s, IsOpen (elem s) := fun s => isOpen_biUnion (fun p _ => hballopen p)
  set scover : Finset (Finset (ℕ × ℚ)) → Set ℂ := fun S => ⋃ s ∈ S, elem s with hscover
  have hscover_open : ∀ S, IsOpen (scover S) := fun S => isOpen_biUnion (fun s _ => helem_open s)
  set scost : Finset (Finset (ℕ × ℚ)) → ℝ≥0∞ :=
    fun S => ∑ s ∈ S, ⨆ _ : (elem s).Nonempty, Metric.ediam (elem s) ^ (1:ℝ) with hscost
  -- The rational-ball basis selector: any point of an open set sits in a small rational ball.
  have hsel : ∀ (z : ℂ) (O : Set ℂ), IsOpen O → z ∈ O →
      ∃ p : ℕ × ℚ, z ∈ ball' p ∧ ball' p ⊆ O := by
    intro z O hO hz
    rw [Metric.isOpen_iff] at hO
    obtain ⟨εO, hεO, hballO⟩ := hO z hz
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show εO/3 < εO/2 by linarith)
    have hqpos : (0:ℝ) < q := by linarith
    obtain ⟨i, hi⟩ := hD.exists_dist_lt z (show (0:ℝ) < εO/3 by linarith)
    refine ⟨(i, q), ?_, ?_⟩
    · rw [hball']; simp only; rw [Metric.mem_ball, dist_comm]
      have : dist z (D i) < (q:ℝ) := by linarith
      rwa [dist_comm] at this
    · rw [hball']; simp only
      intro w hw; rw [Metric.mem_ball] at hw
      apply hballO; rw [Metric.mem_ball]
      calc dist w z ≤ dist w (D i) + dist (D i) z := dist_triangle _ _ _
        _ < q + εO/3 := by rw [dist_comm (D i) z]; linarith
        _ < εO := by linarith
  -- Per-cover validity is Borel (continuous image of a compact set): the indicator is measurable.
  have hind : ∀ {A' : Set ℂ}, IsCompact A' → ∀ (S : Finset (Finset (ℕ × ℚ))) (r : ℝ≥0∞),
      Measurable (fun c : ℝ => if u ⁻¹' {c} ∩ A' ⊆ scover S then r else (∞ : ℝ≥0∞)) := by
    intro A' hA' S r
    have hborel : MeasurableSet (u '' (A' ∩ (scover S)ᶜ)) :=
      (hA'.inter_right (hscover_open S).isClosed_compl |>.image hu).measurableSet
    have hpred : ∀ c : ℝ, (u ⁻¹' {c} ∩ A' ⊆ scover S) ↔ c ∈ (u '' (A' ∩ (scover S)ᶜ))ᶜ := by
      intro c; rw [mem_compl_iff]
      exact ⟨fun hsub ⟨z, ⟨hzA, hzU⟩, hcz⟩ => hzU (hsub ⟨hcz, hzA⟩),
             fun hc z hz => by by_contra hzU; exact hc ⟨z, ⟨hz.2, hzU⟩, hz.1⟩⟩
    have heq : (fun c : ℝ => if u ⁻¹' {c} ∩ A' ⊆ scover S then r else (∞ : ℝ≥0∞))
        = fun c : ℝ => if c ∈ (u '' (A' ∩ (scover S)ᶜ))ᶜ then r else ∞ := by
      funext c; exact if_congr (hpred c) rfl rfl
    rw [heq]; exact Measurable.ite hborel.compl measurable_const measurable_const
  -- The scale-`(k+1)⁻¹` restricted Hausdorff content over countable rational covers.
  set Gterm : ℕ → Finset (Finset (ℕ × ℚ)) → ℝ → ℝ≥0∞ :=
    fun k S c => if (∀ s ∈ S, Metric.ediam (elem s) ≤ ((k:ℝ≥0∞)+1)⁻¹) ∧ u ⁻¹' {c} ∩ A ⊆ scover S
                 then scost S else ∞ with hGterm
  set G : ℕ → ℝ → ℝ≥0∞ := fun k c => ⨅ S, Gterm k S c with hG
  have hGmeas : ∀ k, Measurable (G k) := by
    intro k; apply Measurable.iInf; intro S
    change Measurable (fun c => Gterm k S c)
    by_cases hsmall : ∀ s ∈ S, Metric.ediam (elem s) ≤ ((k:ℝ≥0∞)+1)⁻¹
    · have he : (fun c => Gterm k S c)
          = fun c => if u ⁻¹' {c} ∩ A ⊆ scover S then scost S else ∞ := by
        funext c; exact if_congr (by tauto) rfl rfl
      rw [he]; exact hind hA S (scost S)
    · have he : (fun c => Gterm k S c) = fun _ => (∞ : ℝ≥0∞) := by
        funext c; simp only [hGterm]; rw [if_neg (by tauto)]
      rw [he]; exact measurable_const
  -- It now suffices to identify `μH[1] (u⁻¹{c} ∩ A)` with the measurable `⨆ k, G k c`.
  suffices hF : ∀ c, μH[(1:ℝ)] (u ⁻¹' {c} ∩ A) = ⨆ k, G k c by
    have heq : (fun c => μH[(1:ℝ)] (u ⁻¹' {c} ∩ A)) = fun c => ⨆ k, G k c := funext hF
    have hconv : (fun c => μH[1] (u ⁻¹' {c} ∩ A)) = fun c => ⨆ k, G k c := heq
    rw [hconv]; exact Measurable.iSup hGmeas
  intro c
  set K : Set ℂ := u ⁻¹' {c} ∩ A with hK_def
  have hK : IsCompact K := hA.inter_left (IsClosed.preimage hu isClosed_singleton)
  -- The unrestricted (arbitrary-cover) Hausdorff content at scale `r`.
  set content : ℝ≥0∞ → ℝ≥0∞ := fun r =>
    ⨅ (t : ℕ → Set ℂ) (_ : K ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
      ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ) with hcontent
  have hHA : μH[(1:ℝ)] K = ⨆ (r : ℝ≥0∞) (_ : 0 < r), content r := Measure.hausdorffMeasure_apply _ _
  have hcontent_anti : ∀ r r' : ℝ≥0∞, r ≤ r' → content r' ≤ content r := by
    intro r r' hrr'; rw [hcontent]
    refine iInf_mono fun t => iInf_mono fun hcov => le_iInf fun hsmall => ?_
    exact iInf_le_of_le (fun n => (hsmall n).trans hrr') le_rfl
  -- (A)  content at scale `(k+1)⁻¹` is below `G k c`.
  have hA_dir : ∀ k : ℕ, content ((k:ℝ≥0∞)+1)⁻¹ ≤ G k c := by
    intro k
    rw [hG]; simp only
    refine le_iInf fun S => ?_
    rw [hGterm]; simp only
    by_cases hvalid : (∀ s ∈ S, Metric.ediam (elem s) ≤ ((k:ℝ≥0∞)+1)⁻¹) ∧ K ⊆ scover S
    · rw [if_pos hvalid]
      -- content ≤ scost S, by exhibiting the padded cover `t = (S.toList.map elem).getD · ∅`.
      obtain ⟨hsmall, hcov⟩ := hvalid
      set l : List (Finset (ℕ × ℚ)) := S.toList with hl
      have hlmem : ∀ x, x ∈ l ↔ x ∈ S := fun x => Finset.mem_toList
      set t : ℕ → Set ℂ := fun n => ((l.map elem).getD n ∅) with ht
      have hlen : (l.map elem).length = l.length := List.length_map _
      have htmem : ∀ n, (∃ s ∈ S, t n = elem s) ∨ t n = ∅ := by
        intro n
        rcases lt_or_ge n l.length with hlt | hge
        · left; refine ⟨l[n], (hlmem _).1 (List.getElem_mem hlt), ?_⟩
          simp only [ht]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hlt),
              Option.getD_some, List.getElem_map]
        · right; simp only [ht]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlen]; exact hge),
              Option.getD_none]
      have htsmall : ∀ n, Metric.ediam (t n) ≤ ((k:ℝ≥0∞)+1)⁻¹ := by
        intro n; rcases htmem n with ⟨s, hs, hts⟩ | h0
        · rw [hts]; exact hsmall s hs
        · rw [h0]; simp
      have htcov : K ⊆ ⋃ n, t n := by
        refine hcov.trans ?_
        intro z hz; rw [hscover] at hz; simp only [mem_iUnion] at hz ⊢
        obtain ⟨s, hs, hzs⟩ := hz
        obtain ⟨i, hi⟩ := List.getElem_of_mem ((hlmem s).2 hs)
        refine ⟨i, ?_⟩
        have : t i = elem s := by
          simp only [ht]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hi.1),
              Option.getD_some, List.getElem_map, hi.2]
        rw [this]; exact hzs
      have hcosteq : (∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ)) = scost S := by
        set h : Finset (ℕ × ℚ) → ℝ≥0∞ :=
          fun s => ⨆ _ : (elem s).Nonempty, Metric.ediam (elem s) ^ (1:ℝ) with hh
        have hFn : ∀ n,
            (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ)) = (l.map h).getD n 0 := by
          intro n
          rcases lt_or_ge n l.length with hlt | hge
          · have htn : t n = elem (l[n]) := by
              simp only [ht]
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hlt),
                  Option.getD_some, List.getElem_map]
            have hhn : (l.map h).getD n 0 = h (l[n]) := by
              rw [List.getD_eq_getElem?_getD,
                  List.getElem?_eq_getElem (by rw [List.length_map]; exact hlt),
                  Option.getD_some, List.getElem_map]
            rw [htn, hhn, hh]
          · have htn : t n = ∅ := by
              simp only [ht]
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlen]; exact hge),
                  Option.getD_none]
            have hhn : (l.map h).getD n 0 = 0 := by
              rw [List.getD_eq_getElem?_getD,
                  List.getElem?_eq_none (by rw [List.length_map]; exact hge), Option.getD_none]
            rw [htn, hhn]; simp
        have htsum : (∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ)) = (l.map h).sum := by
          rw [show (fun n => ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ))
                = fun n => (l.map h).getD n 0 from funext hFn]
          rw [tsum_eq_sum (s := Finset.range (l.map h).length) ?_]
          · rw [← Fin.sum_univ_getElem (l.map h), Finset.sum_range fun n => (l.map h).getD n 0]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.2, Option.getD_some]
          · intro b hb; simp only [Finset.mem_range, not_lt] at hb
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hb, Option.getD_none]
        rw [htsum, hscost, hl, ← List.sum_toFinset h S.nodup_toList, Finset.toList_toFinset]
      rw [hcontent]
      calc (⨅ (t' : ℕ → Set ℂ) (_ : K ⊆ ⋃ n, t' n) (_ : ∀ n, Metric.ediam (t' n) ≤ ((k:ℝ≥0∞)+1)⁻¹),
              ∑' n, ⨆ _ : (t' n).Nonempty, Metric.ediam (t' n) ^ (1:ℝ))
          ≤ ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ) :=
            iInf_le_of_le t (iInf_le_of_le htcov (iInf_le_of_le htsmall le_rfl))
        _ = scost S := hcosteq
    · rw [if_neg hvalid]; exact le_top
  -- (B)  `G k c` is below the content at scale `(2(k+1))⁻¹`.
  have hB_dir : ∀ k : ℕ, G k c ≤ content (2*((k:ℝ≥0∞)+1))⁻¹ := by
    intro k
    rw [hcontent]
    refine le_iInf fun t => le_iInf fun htcov => le_iInf fun htsmall => ?_
    -- It suffices to dominate by the `t`-cost plus any `ε`.
    refine ENNReal.le_of_forall_pos_le_add ?_
    intro ε hεpos _
    set εE : ℝ≥0∞ := (ε : ℝ≥0∞) with hεE
    have hεEpos : 0 < εE := by rw [hεE]; exact_mod_cast hεpos
    have hεEtop : εE ≠ ∞ := by rw [hεE]; exact ENNReal.coe_ne_top
    -- BUILD the rational `(k+1)⁻¹`-cover from the `t`-cover (the thickening / grouping core).
    set e : ℝ := εE.toReal with he_def
    have he : 0 < e := by rw [he_def]; exact ENNReal.toReal_pos hεEpos.ne' hεEtop
    set δ : ℕ → ℝ := fun n => min (1/(4*((k:ℝ)+1))) (e * (1/2)^(n+2)) with hδ_def
    have hkR1 : (0:ℝ) < (k:ℝ)+1 := by positivity
    have hδpos : ∀ n, 0 < δ n := fun n => lt_min (by positivity) (by positivity)
    have hδle : ∀ n, δ n ≤ 1/(4*((k:ℝ)+1)) := fun n => min_le_left _ _
    have hδsum : (∑' n, ENNReal.ofReal (2 * δ n)) ≤ εE := by
      have hgeo : Summable (fun n : ℕ => ((1:ℝ)/2)^n) := summable_geometric_two
      have hsumm : Summable (fun n : ℕ => 2 * (e * (1/2)^(n+2))) := by
        have : (fun n : ℕ => 2 * (e * ((1:ℝ)/2)^(n+2)))
             = fun n => (2 * e * ((1:ℝ)/2)^2) * (1/2)^n := by funext n; rw [pow_add]; ring
        rw [this]; exact hgeo.mul_left _
      have hval : (∑' n : ℕ, 2 * (e * ((1:ℝ)/2)^(n+2))) = e := by
        have : (fun n : ℕ => 2 * (e * ((1:ℝ)/2)^(n+2)))
             = fun n => (2 * e * ((1:ℝ)/2)^2) * (1/2)^n := by funext n; rw [pow_add]; ring
        rw [this, tsum_mul_left, tsum_geometric_two]; ring
      calc (∑' n, ENNReal.ofReal (2 * δ n))
          ≤ ∑' n, ENNReal.ofReal (2 * (e * (1/2)^(n+2))) := by
            apply ENNReal.tsum_le_tsum; intro n; apply ENNReal.ofReal_le_ofReal
            have := min_le_right (1/(4*((k:ℝ)+1)):ℝ) (e * (1/2)^(n+2))
            rw [hδ_def]; simp only; linarith
        _ = ENNReal.ofReal (∑' n, 2 * (e * (1/2)^(n+2))) :=
            (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm).symm
        _ = ENNReal.ofReal e := by rw [hval]
        _ = εE := by rw [he_def, ENNReal.ofReal_toReal hεEtop]
    set W : ℕ → Set ℂ := fun n => Metric.thickening (δ n) (t n) with hW_def
    have hWopen : ∀ n, IsOpen (W n) := fun n => Metric.isOpen_thickening
    have htsubW : ∀ n, t n ⊆ W n := fun n => Metric.self_subset_thickening (hδpos n) (t n)
    have hKW : K ⊆ ⋃ n, W n := htcov.trans (iUnion_mono (fun n => htsubW n))
    set B : ℕ → ℝ≥0∞ := fun n => Metric.ediam (t n) + ENNReal.ofReal (2 * δ n) with hB_def
    have hWdiam : ∀ n, Metric.ediam (W n) ≤ B n := by
      intro n; apply Metric.ediam_le
      intro x hx y hy
      rw [hW_def] at hx hy; simp only [Metric.mem_thickening_iff] at hx hy
      obtain ⟨x', hx', hxx'⟩ := hx
      obtain ⟨y', hy', hyy'⟩ := hy
      have hstep : edist x y ≤ (edist x x' + edist x' y') + edist y' y := by
        refine (edist_triangle x y' y).trans ?_; gcongr; exact edist_triangle x x' y'
      refine hstep.trans ?_
      have h1 : edist x x' ≤ ENNReal.ofReal (δ n) := by
        rw [edist_dist]; exact ENNReal.ofReal_le_ofReal hxx'.le
      have h2 : edist x' y' ≤ Metric.ediam (t n) := Metric.edist_le_ediam_of_mem hx' hy'
      have h3 : edist y' y ≤ ENNReal.ofReal (δ n) := by
        rw [edist_dist, dist_comm]; exact ENNReal.ofReal_le_ofReal hyy'.le
      rw [hB_def]; simp only
      calc (edist x x' + edist x' y') + edist y' y
          ≤ (ENNReal.ofReal (δ n) + Metric.ediam (t n)) + ENNReal.ofReal (δ n) := by gcongr
        _ = Metric.ediam (t n) + (ENNReal.ofReal (δ n) + ENNReal.ofReal (δ n)) := by ring
        _ = Metric.ediam (t n) + ENNReal.ofReal (2 * δ n) := by
            rw [← ENNReal.ofReal_add (hδpos n).le (hδpos n).le]; ring_nf
    have hBsmall : ∀ n, B n ≤ ((k:ℝ≥0∞)+1)⁻¹ := by
      intro n; rw [hB_def]; simp only
      have hle1 : Metric.ediam (t n) ≤ (2*((k:ℝ≥0∞)+1))⁻¹ := htsmall n
      have hle2 : ENNReal.ofReal (2 * δ n) ≤ (2*((k:ℝ≥0∞)+1))⁻¹ := by
        have hd : (2 * δ n) ≤ 1/(2*((k:ℝ)+1)) := by
          have := hδle n; rw [le_div_iff₀ (by positivity)] at this ⊢; nlinarith
        refine (ENNReal.ofReal_le_ofReal hd).trans ?_
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
            ENNReal.ofReal_mul (by norm_num)]
        rw [show ENNReal.ofReal ((k:ℝ)+1) = (k:ℝ≥0∞)+1 by
              rw [ENNReal.ofReal_add (by positivity) (by norm_num)]; norm_num,
            show ENNReal.ofReal 2 = (2:ℝ≥0∞) by norm_num, one_div]
      calc Metric.ediam (t n) + ENNReal.ofReal (2 * δ n)
          ≤ (2*((k:ℝ≥0∞)+1))⁻¹ + (2*((k:ℝ≥0∞)+1))⁻¹ := by gcongr
        _ = ((k:ℝ≥0∞)+1)⁻¹ := by
            rw [← two_mul, ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
                ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    -- finite subcover + selection (rational balls assigned to thickenings)
    have hcovP : ∀ z ∈ K, ∃ p : ℕ × ℚ, z ∈ ball' p ∧ ∃ n, ball' p ⊆ W n := by
      intro z hz
      obtain ⟨n, hn⟩ : ∃ n, z ∈ W n := by have := hKW hz; rwa [mem_iUnion] at this
      obtain ⟨p, hzp, hpW⟩ := hsel z (W n) (hWopen n) hn
      exact ⟨p, hzp, n, hpW⟩
    choose! pp hzpp hnpp using hcovP
    obtain ⟨T, hTsub, hTfin, hTcov⟩ := hK.elim_finite_subcover_image
      (b := K) (c := fun z => ball' (pp z)) (fun z _ => hballopen (pp z))
      (by intro z hz; rw [mem_iUnion₂]; exact ⟨z, hz, hzpp z hz⟩)
    set Tf := hTfin.toFinset with hTf
    set P : Finset (ℕ × ℚ) := Tf.image pp with hP
    have hPprop : ∀ p ∈ P, ∃ n, ball' p ⊆ W n := by
      intro p hp; rw [hP, Finset.mem_image] at hp
      obtain ⟨z, hzT, rfl⟩ := hp
      exact hnpp z (hTsub (by rw [hTf, Set.Finite.mem_toFinset] at hzT; exact hzT))
    choose! ν hν using hPprop
    have hKcovP : K ⊆ ⋃ p ∈ P, ball' p := by
      intro z hz
      have := hTcov hz; rw [mem_iUnion₂] at this
      obtain ⟨w, hwT, hzw⟩ := this
      rw [mem_iUnion₂]; refine ⟨pp w, ?_, hzw⟩
      rw [hP, Finset.mem_image]; exact ⟨w, by rw [hTf, Set.Finite.mem_toFinset]; exact hwT, rfl⟩
    have hνW : ∀ p ∈ P, ball' p ⊆ W (ν p) := fun p hp => hν p hp
    -- grouping into `S`
    set grp : ℕ → Finset (ℕ × ℚ) := fun n => P.filter (fun p => ν p = n) with hgrp
    set S : Finset (Finset (ℕ × ℚ)) := (P.image ν).image grp with hS
    have hgrpW : ∀ n, elem (grp n) ⊆ W n := by
      intro n; rw [helem]; refine iUnion₂_subset ?_; intro p hp
      rw [hgrp, Finset.mem_filter] at hp; rw [← hp.2]; exact hνW p hp.1
    have hgrpdiam : ∀ n, Metric.ediam (elem (grp n)) ≤ B n := fun n =>
      (Metric.ediam_mono (hgrpW n)).trans (hWdiam n)
    -- `S` is a valid `(k+1)⁻¹`-cover, so `G k c ≤ scost S`.
    have hScover : K ⊆ scover S := by
      rw [hscover]
      refine hKcovP.trans ?_
      intro z hz; rw [mem_iUnion₂] at hz; obtain ⟨p, hp, hzp⟩ := hz
      rw [mem_iUnion₂]; refine ⟨grp (ν p), ?_, ?_⟩
      · rw [hS, Finset.mem_image]; exact ⟨ν p, Finset.mem_image_of_mem ν hp, rfl⟩
      · rw [helem, mem_iUnion₂]; exact ⟨p, by rw [hgrp, Finset.mem_filter]; exact ⟨hp, rfl⟩, hzp⟩
    have hSsmall : ∀ s ∈ S, Metric.ediam (elem s) ≤ ((k:ℝ≥0∞)+1)⁻¹ := by
      intro s hs; rw [hS, Finset.mem_image] at hs
      obtain ⟨n, hn, rfl⟩ := hs; exact (hgrpdiam n).trans (hBsmall n)
    have hGle : G k c ≤ scost S := by
      rw [hG]; simp only
      refine iInf_le_of_le S ?_
      rw [hGterm]; simp only; rw [if_pos ⟨hSsmall, hScover⟩]
    refine hGle.trans ?_
    -- cost of `S` ≤ `t`-cost + ε
    have himg : scost S
        ≤ ∑ n ∈ P.image ν,
            (⨆ _ : (elem (grp n)).Nonempty, Metric.ediam (elem (grp n)) ^ (1:ℝ)) := by
      rw [hscost, hS, ← Finset.sum_fiberwise_of_maps_to (g := grp) (t := (P.image ν).image grp)
            (fun n hn => Finset.mem_image_of_mem grp hn)]
      apply Finset.sum_le_sum; intro s hs
      obtain ⟨n0, hn0T, hn0⟩ := Finset.mem_image.1 hs
      have hmem : n0 ∈ (P.image ν).filter (fun n => grp n = s) := Finset.mem_filter.2 ⟨hn0T, hn0⟩
      calc (⨆ _ : (elem s).Nonempty, Metric.ediam (elem s) ^ (1:ℝ))
          = (⨆ _ : (elem (grp n0)).Nonempty, Metric.ediam (elem (grp n0)) ^ (1:ℝ)) := by rw [hn0]
        _ ≤ ∑ n ∈ (P.image ν).filter (fun n => grp n = s),
              (⨆ _ : (elem (grp n)).Nonempty, Metric.ediam (elem (grp n)) ^ (1:ℝ)) :=
            Finset.single_le_sum
              (f := fun n => ⨆ _ : (elem (grp n)).Nonempty, Metric.ediam (elem (grp n)) ^ (1:ℝ))
              (fun _ _ => zero_le) hmem
    have hstep2 :
        ∑ n ∈ P.image ν, (⨆ _ : (elem (grp n)).Nonempty, Metric.ediam (elem (grp n)) ^ (1:ℝ))
          ≤ ∑ n ∈ P.image ν, ((⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ))
              + ENNReal.ofReal (2 * δ n)) := by
      apply Finset.sum_le_sum; intro n _
      have hb : (⨆ _ : (elem (grp n)).Nonempty, Metric.ediam (elem (grp n)) ^ (1:ℝ)) ≤ B n := by
        refine iSup_le (fun _ => ?_); rw [ENNReal.rpow_one]; exact hgrpdiam n
      refine hb.trans ?_
      rw [hB_def]; simp only; gcongr
      by_cases h : (t n).Nonempty
      · rw [ciSup_pos h, ENNReal.rpow_one]
      · rw [not_nonempty_iff_eq_empty] at h; rw [h]; simp
    calc scost S
        ≤ ∑ n ∈ P.image ν, ((⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ))
            + ENNReal.ofReal (2 * δ n)) := himg.trans hstep2
      _ = (∑ n ∈ P.image ν, (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ)))
            + ∑ n ∈ P.image ν, ENNReal.ofReal (2 * δ n) := Finset.sum_add_distrib
      _ ≤ (∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ)) + εE :=
            add_le_add (ENNReal.sum_le_tsum _) ((ENNReal.sum_le_tsum _).trans hδsum)
  -- Assemble:  μH[1] K = ⨆ k, G k c.
  apply le_antisymm
  · rw [hHA]; refine iSup₂_le ?_; intro r hr
    obtain ⟨k, hkr⟩ : ∃ k : ℕ, ((k:ℝ≥0∞)+1)⁻¹ ≤ r := by
      rcases eq_or_ne r ∞ with rfl | hrtop
      · exact ⟨0, le_top⟩
      · obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt (a := r) hr.ne'
        exact ⟨k, (ENNReal.inv_le_inv.2 le_self_add).trans hk.le⟩
    calc content r ≤ content ((k:ℝ≥0∞)+1)⁻¹ := hcontent_anti _ _ hkr
      _ ≤ G k c := hA_dir k
      _ ≤ ⨆ k, G k c := le_iSup (fun k => G k c) k
  · refine iSup_le ?_; intro k
    calc G k c ≤ content (2*((k:ℝ≥0∞)+1))⁻¹ := hB_dir k
      _ ≤ μH[(1:ℝ)] K := by
          rw [hHA]; refine le_iSup₂_of_le (2*((k:ℝ≥0∞)+1))⁻¹ ?_ le_rfl
          rw [ENNReal.inv_pos]
          exact ENNReal.mul_ne_top (by norm_num)
            (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top k, by norm_num⟩)

/-- **Planar metric Eilenberg inequality on `ℂ` (unblocked by `measurable_slice_hausdorff_one`).**

For `u : ℂ → ℝ` that is `K`-Lipschitz on a compact set `A`, the integrated arc-length of the level
sets of `u` meeting `A` is bounded by `K` times the 2-dimensional Hausdorff measure of `A`:

`∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) ≤ (K : ℝ≥0∞) * μH[2] A`.

This is the **raw (un-normalized) metric Eilenberg inequality** specialized to the plane with the
level-arc-length weight. The constant is the (local) Lipschitz constant `K` — *not* the sharp
gradient — so on its own it carries the unavoidable `μH[2] = (4/π)·volume` mismatch; it is used in
the sharp-co-area localization only where that factor is multiplied by a vanishing quantity (the
`∇u = 0` set, where the local Lipschitz constant tends to `0`, and the `volume`-null remainder,
where `μH[2] = (4/π)·volume = 0`). The sharp leading term comes instead from `coarea_linear_eq`.

## Truth, direction, and proof

One-sided `≤`, constant exactly `K` (raw Hausdorff convention). Proof: write
`μH[1] (S) = ⨆ n, μH[1]_{1/n} (S)` via the Hausdorff premeasures and pass the supremum out of the
`c`-integral by monotone convergence — legitimate because each premeasure slice
`c ↦ μH[1]_{1/n} (u ⁻¹' {c} ∩ A)` is measurable by the same compact-image / countable-open-cover
argument as `measurable_slice_hausdorff_one`. For a fixed scale and a fixed cover `{Tᵢ}` of `A` with
`diam Tᵢ ≤ 1/n`, `μH[1]_{1/n} (u ⁻¹' {c} ∩ A) ≤ ∑_{i : c ∈ u '' (A ∩ Tᵢ)} diam Tᵢ`; integrating in
`c` (dominating `𝟙[c ∈ u '' (A ∩ Tᵢ)]` by `𝟙[c ∈ Icc (sInf) (sSup)]`, whose integral is the length
`≤ K · diam Tᵢ` by the Lipschitz oscillation bound) gives `∑ᵢ diam Tᵢ · K · diam Tᵢ = K ∑ᵢ diam²`;
infimum over covers yields `K · μH[2]_{1/n} (A) ≤ K · μH[2] A`. -/
theorem eilenberg_coarea_planar_metric {u : ℂ → ℝ} {K : ℝ≥0} {A : Set ℂ}
    (hu : LipschitzOnWith K u A) (hA : IsCompact A) :
    ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) ≤ (K : ℝ≥0∞) * μH[2] A := by
  classical
  -- Handle the degenerate `K = 0` case (then `u` is constant on `A`).
  rcases eq_or_ne K 0 with hK0 | hKne0
  · subst hK0
    rw [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero]
    rcases A.eq_empty_or_nonempty with hAe | ⟨z0, hz0⟩
    · subst hAe; simp
    · have hconst : ∀ x ∈ A, u x = u z0 := fun x hx =>
        (LipschitzOnWith.zero_iff u).1 hu x hx z0 hz0
      have hsupp : (fun c => μH[1] (u ⁻¹' {c} ∩ A))
          = Set.indicator {u z0} (fun _ => μH[1] A) := by
        funext c
        by_cases hc : c = u z0
        · subst hc
          rw [indicator_of_mem (by simp)]
          congr 1
          rw [Set.inter_eq_right]
          intro x hx
          simp only [mem_preimage, mem_singleton_iff]; exact hconst x hx
        · rw [indicator_of_notMem (by simp [hc])]
          have hemp : u ⁻¹' {c} ∩ A = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            rintro x ⟨hxc, hxA⟩
            simp only [mem_preimage, mem_singleton_iff] at hxc
            exact hc (by rw [← hxc, hconst x hxA])
          rw [hemp, measure_empty]
      rw [hsupp, lintegral_indicator (measurableSet_singleton _), setLIntegral_const,
        Real.volume_singleton, mul_zero]
  -- Main case: `K ≠ 0`.
  obtain ⟨g, hgLip, hgEq⟩ := hu.extend_real
  have hgcont : Continuous g := hgLip.continuous
  have hslice_eq : ∀ c : ℝ, u ⁻¹' {c} ∩ A = g ⁻¹' {c} ∩ A := by
    intro c; ext z
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hz, hzA⟩; exact ⟨by rw [← hgEq hzA]; exact hz, hzA⟩
    · rintro ⟨hz, hzA⟩; exact ⟨by rw [hgEq hzA]; exact hz, hzA⟩
  rw [show (∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A)) = ∫⁻ c, μH[1] (g ⁻¹' {c} ∩ A) by
        apply lintegral_congr; intro c; rw [hslice_eq c]]
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℂ, DenseRange D :=
    ⟨TopologicalSpace.denseSeq ℂ, TopologicalSpace.denseRange_denseSeq ℂ⟩
  set ball' : ℕ × ℚ → Set ℂ := fun p => Metric.ball (D p.1) (p.2 : ℝ) with hball'
  have hballopen : ∀ p, IsOpen (ball' p) := fun p => Metric.isOpen_ball
  set elem : Finset (ℕ × ℚ) → Set ℂ := fun s => ⋃ p ∈ s, ball' p with helem
  have helem_open : ∀ s, IsOpen (elem s) := fun s => isOpen_biUnion (fun p _ => hballopen p)
  set scover : Finset (Finset (ℕ × ℚ)) → Set ℂ := fun S => ⋃ s ∈ S, elem s with hscover
  have hscover_open : ∀ S, IsOpen (scover S) := fun S => isOpen_biUnion (fun s _ => helem_open s)
  set scost : Finset (Finset (ℕ × ℚ)) → ℝ≥0∞ :=
    fun S => ∑ s ∈ S, ⨆ _ : (elem s).Nonempty, Metric.ediam (elem s) ^ (1:ℝ) with hscost
  have hsel : ∀ (z : ℂ) (O : Set ℂ), IsOpen O → z ∈ O →
      ∃ p : ℕ × ℚ, z ∈ ball' p ∧ ball' p ⊆ O := by
    intro z O hO hz
    rw [Metric.isOpen_iff] at hO
    obtain ⟨εO, hεO, hballO⟩ := hO z hz
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show εO/3 < εO/2 by linarith)
    have hqpos : (0:ℝ) < q := by linarith
    obtain ⟨i, hi⟩ := hD.exists_dist_lt z (show (0:ℝ) < εO/3 by linarith)
    refine ⟨(i, q), ?_, ?_⟩
    · rw [hball']; simp only; rw [Metric.mem_ball, dist_comm]
      have : dist z (D i) < (q:ℝ) := by linarith
      rwa [dist_comm] at this
    · rw [hball']; simp only
      intro w hw; rw [Metric.mem_ball] at hw
      apply hballO; rw [Metric.mem_ball]
      calc dist w z ≤ dist w (D i) + dist (D i) z := dist_triangle _ _ _
        _ < q + εO/3 := by rw [dist_comm (D i) z]; linarith
        _ < εO := by linarith
  have hind : ∀ {A' : Set ℂ}, IsCompact A' → ∀ (S : Finset (Finset (ℕ × ℚ))) (r : ℝ≥0∞),
      Measurable (fun c : ℝ => if g ⁻¹' {c} ∩ A' ⊆ scover S then r else (∞ : ℝ≥0∞)) := by
    intro A' hA' S r
    have hborel : MeasurableSet (g '' (A' ∩ (scover S)ᶜ)) :=
      (hA'.inter_right (hscover_open S).isClosed_compl |>.image hgcont).measurableSet
    have hpred : ∀ c : ℝ, (g ⁻¹' {c} ∩ A' ⊆ scover S) ↔ c ∈ (g '' (A' ∩ (scover S)ᶜ))ᶜ := by
      intro c; rw [mem_compl_iff]
      exact ⟨fun hsub ⟨z, ⟨hzA, hzU⟩, hcz⟩ => hzU (hsub ⟨hcz, hzA⟩),
             fun hc z hz => by by_contra hzU; exact hc ⟨z, ⟨hz.2, hzU⟩, hz.1⟩⟩
    have heq : (fun c : ℝ => if g ⁻¹' {c} ∩ A' ⊆ scover S then r else (∞ : ℝ≥0∞))
        = fun c : ℝ => if c ∈ (g '' (A' ∩ (scover S)ᶜ))ᶜ then r else ∞ := by
      funext c; exact if_congr (hpred c) rfl rfl
    rw [heq]; exact Measurable.ite hborel.compl measurable_const measurable_const
  set Gterm : ℕ → Finset (Finset (ℕ × ℚ)) → ℝ → ℝ≥0∞ :=
    fun k S c => if (∀ s ∈ S, Metric.ediam (elem s) ≤ ((k:ℝ≥0∞)+1)⁻¹) ∧ g ⁻¹' {c} ∩ A ⊆ scover S
                 then scost S else ∞ with hGterm
  set G : ℕ → ℝ → ℝ≥0∞ := fun k c => ⨅ S, Gterm k S c with hG
  have hGmeas : ∀ k, Measurable (G k) := by
    intro k; apply Measurable.iInf; intro S
    change Measurable (fun c => Gterm k S c)
    by_cases hsmall : ∀ s ∈ S, Metric.ediam (elem s) ≤ ((k:ℝ≥0∞)+1)⁻¹
    · have he : (fun c => Gterm k S c)
          = fun c => if g ⁻¹' {c} ∩ A ⊆ scover S then scost S else ∞ := by
        funext c; exact if_congr (by tauto) rfl rfl
      rw [he]; exact hind hA S (scost S)
    · have he : (fun c => Gterm k S c) = fun _ => (∞ : ℝ≥0∞) := by
        funext c; simp only [hGterm]; rw [if_neg (by tauto)]
      rw [he]; exact measurable_const
  -- per-c content (dimension 1) of the slice
  set content : ℝ → ℝ≥0∞ → ℝ≥0∞ := fun c r =>
    ⨅ (t : ℕ → Set ℂ) (_ : (g ⁻¹' {c} ∩ A) ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
      ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ) with hcontent
  -- For each c: the supremum identity and the B-direction.
  have hkey : ∀ c : ℝ,
      μH[(1:ℝ)] (g ⁻¹' {c} ∩ A) = ⨆ k, G k c
      ∧ ∀ k : ℕ, G k c ≤ content c (2*((k:ℝ≥0∞)+1))⁻¹ := by
    intro c
    set Kc : Set ℂ := g ⁻¹' {c} ∩ A with hK_def
    have hKc : IsCompact Kc := hA.inter_left (IsClosed.preimage hgcont isClosed_singleton)
    have hHA : μH[(1:ℝ)] Kc = ⨆ (r : ℝ≥0∞) (_ : 0 < r), content c r :=
      Measure.hausdorffMeasure_apply _ _
    have hcontent_anti : ∀ r r' : ℝ≥0∞, r ≤ r' → content c r' ≤ content c r := by
      intro r r' hrr'; rw [hcontent]
      refine iInf_mono fun t => iInf_mono fun hcov => le_iInf fun hsmall => ?_
      exact iInf_le_of_le (fun n => (hsmall n).trans hrr') le_rfl
    -- (A) content at scale (k+1)⁻¹ ≤ G k c.
    have hA_dir : ∀ k : ℕ, content c ((k:ℝ≥0∞)+1)⁻¹ ≤ G k c := by
      intro k
      rw [hG]; simp only
      refine le_iInf fun S => ?_
      rw [hGterm]; simp only
      by_cases hvalid : (∀ s ∈ S, Metric.ediam (elem s) ≤ ((k:ℝ≥0∞)+1)⁻¹) ∧ Kc ⊆ scover S
      · rw [if_pos hvalid]
        obtain ⟨hsmall, hcov⟩ := hvalid
        set l : List (Finset (ℕ × ℚ)) := S.toList with hl
        have hlmem : ∀ x, x ∈ l ↔ x ∈ S := fun x => Finset.mem_toList
        set t : ℕ → Set ℂ := fun n => ((l.map elem).getD n ∅) with ht
        have hlen : (l.map elem).length = l.length := List.length_map _
        have htmem : ∀ n, (∃ s ∈ S, t n = elem s) ∨ t n = ∅ := by
          intro n
          rcases lt_or_ge n l.length with hlt | hge
          · left; refine ⟨l[n], (hlmem _).1 (List.getElem_mem hlt), ?_⟩
            simp only [ht]
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hlt),
                Option.getD_some, List.getElem_map]
          · right; simp only [ht]
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlen]; exact hge),
                Option.getD_none]
        have htsmall : ∀ n, Metric.ediam (t n) ≤ ((k:ℝ≥0∞)+1)⁻¹ := by
          intro n; rcases htmem n with ⟨s, hs, hts⟩ | h0
          · rw [hts]; exact hsmall s hs
          · rw [h0]; simp
        have htcov : Kc ⊆ ⋃ n, t n := by
          refine hcov.trans ?_
          intro z hz; rw [hscover] at hz; simp only [mem_iUnion] at hz ⊢
          obtain ⟨s, hs, hzs⟩ := hz
          obtain ⟨i, hi⟩ := List.getElem_of_mem ((hlmem s).2 hs)
          refine ⟨i, ?_⟩
          have : t i = elem s := by
            simp only [ht]
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hi.1),
                Option.getD_some, List.getElem_map, hi.2]
          rw [this]; exact hzs
        have hcosteq : (∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ)) = scost S := by
          set h : Finset (ℕ × ℚ) → ℝ≥0∞ :=
            fun s => ⨆ _ : (elem s).Nonempty, Metric.ediam (elem s) ^ (1:ℝ) with hh
          have hFn : ∀ n,
              (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ)) = (l.map h).getD n 0 := by
            intro n
            rcases lt_or_ge n l.length with hlt | hge
            · have htn : t n = elem (l[n]) := by
                simp only [ht]
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hlt),
                    Option.getD_some, List.getElem_map]
              have hhn : (l.map h).getD n 0 = h (l[n]) := by
                rw [List.getD_eq_getElem?_getD,
                    List.getElem?_eq_getElem (by rw [List.length_map]; exact hlt),
                    Option.getD_some, List.getElem_map]
              rw [htn, hhn, hh]
            · have htn : t n = ∅ := by
                simp only [ht]
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlen]; exact hge),
                    Option.getD_none]
              have hhn : (l.map h).getD n 0 = 0 := by
                rw [List.getD_eq_getElem?_getD,
                    List.getElem?_eq_none (by rw [List.length_map]; exact hge), Option.getD_none]
              rw [htn, hhn]; simp
          have htsum : (∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ))
              = (l.map h).sum := by
            rw [show (fun n => ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ))
                  = fun n => (l.map h).getD n 0 from funext hFn]
            rw [tsum_eq_sum (s := Finset.range (l.map h).length) ?_]
            · rw [← Fin.sum_univ_getElem (l.map h), Finset.sum_range fun n => (l.map h).getD n 0]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.2, Option.getD_some]
            · intro b hb; simp only [Finset.mem_range, not_lt] at hb
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hb, Option.getD_none]
          rw [htsum, hscost, hl, ← List.sum_toFinset h S.nodup_toList, Finset.toList_toFinset]
        rw [hcontent]
        calc (⨅ (t' : ℕ → Set ℂ) (_ : Kc ⊆ ⋃ n, t' n)
                  (_ : ∀ n, Metric.ediam (t' n) ≤ ((k:ℝ≥0∞)+1)⁻¹),
                ∑' n, ⨆ _ : (t' n).Nonempty, Metric.ediam (t' n) ^ (1:ℝ))
            ≤ ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ) :=
              iInf_le_of_le t (iInf_le_of_le htcov (iInf_le_of_le htsmall le_rfl))
          _ = scost S := hcosteq
      · rw [if_neg hvalid]; exact le_top
    -- (B) G k c ≤ content at scale (2(k+1))⁻¹.
    have hB_dir : ∀ k : ℕ, G k c ≤ content c (2*((k:ℝ≥0∞)+1))⁻¹ := by
      intro k
      rw [hcontent]
      refine le_iInf fun t => le_iInf fun htcov => le_iInf fun htsmall => ?_
      refine ENNReal.le_of_forall_pos_le_add ?_
      intro ε hεpos _
      set εE : ℝ≥0∞ := (ε : ℝ≥0∞) with hεE
      have hεEpos : 0 < εE := by rw [hεE]; exact_mod_cast hεpos
      have hεEtop : εE ≠ ∞ := by rw [hεE]; exact ENNReal.coe_ne_top
      set e : ℝ := εE.toReal with he_def
      have he : 0 < e := by rw [he_def]; exact ENNReal.toReal_pos hεEpos.ne' hεEtop
      set δ : ℕ → ℝ := fun n => min (1/(4*((k:ℝ)+1))) (e * (1/2)^(n+2)) with hδ_def
      have hkR1 : (0:ℝ) < (k:ℝ)+1 := by positivity
      have hδpos : ∀ n, 0 < δ n := fun n => lt_min (by positivity) (by positivity)
      have hδle : ∀ n, δ n ≤ 1/(4*((k:ℝ)+1)) := fun n => min_le_left _ _
      have hδsum : (∑' n, ENNReal.ofReal (2 * δ n)) ≤ εE := by
        have hgeo : Summable (fun n : ℕ => ((1:ℝ)/2)^n) := summable_geometric_two
        have hsumm : Summable (fun n : ℕ => 2 * (e * (1/2)^(n+2))) := by
          have : (fun n : ℕ => 2 * (e * ((1:ℝ)/2)^(n+2)))
               = fun n => (2 * e * ((1:ℝ)/2)^2) * (1/2)^n := by funext n; rw [pow_add]; ring
          rw [this]; exact hgeo.mul_left _
        have hval : (∑' n : ℕ, 2 * (e * ((1:ℝ)/2)^(n+2))) = e := by
          have : (fun n : ℕ => 2 * (e * ((1:ℝ)/2)^(n+2)))
               = fun n => (2 * e * ((1:ℝ)/2)^2) * (1/2)^n := by funext n; rw [pow_add]; ring
          rw [this, tsum_mul_left, tsum_geometric_two]; ring
        calc (∑' n, ENNReal.ofReal (2 * δ n))
            ≤ ∑' n, ENNReal.ofReal (2 * (e * (1/2)^(n+2))) := by
              apply ENNReal.tsum_le_tsum; intro n; apply ENNReal.ofReal_le_ofReal
              have := min_le_right (1/(4*((k:ℝ)+1)):ℝ) (e * (1/2)^(n+2))
              rw [hδ_def]; simp only; linarith
          _ = ENNReal.ofReal (∑' n, 2 * (e * (1/2)^(n+2))) :=
              (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm).symm
          _ = ENNReal.ofReal e := by rw [hval]
          _ = εE := by rw [he_def, ENNReal.ofReal_toReal hεEtop]
      set W : ℕ → Set ℂ := fun n => Metric.thickening (δ n) (t n) with hW_def
      have hWopen : ∀ n, IsOpen (W n) := fun n => Metric.isOpen_thickening
      have htsubW : ∀ n, t n ⊆ W n := fun n => Metric.self_subset_thickening (hδpos n) (t n)
      have hKW : Kc ⊆ ⋃ n, W n := htcov.trans (iUnion_mono (fun n => htsubW n))
      set B : ℕ → ℝ≥0∞ := fun n => Metric.ediam (t n) + ENNReal.ofReal (2 * δ n) with hB_def
      have hWdiam : ∀ n, Metric.ediam (W n) ≤ B n := by
        intro n; apply Metric.ediam_le
        intro x hx y hy
        rw [hW_def] at hx hy; simp only [Metric.mem_thickening_iff] at hx hy
        obtain ⟨x', hx', hxx'⟩ := hx
        obtain ⟨y', hy', hyy'⟩ := hy
        have hstep : edist x y ≤ (edist x x' + edist x' y') + edist y' y := by
          refine (edist_triangle x y' y).trans ?_; gcongr; exact edist_triangle x x' y'
        refine hstep.trans ?_
        have h1 : edist x x' ≤ ENNReal.ofReal (δ n) := by
          rw [edist_dist]; exact ENNReal.ofReal_le_ofReal hxx'.le
        have h2 : edist x' y' ≤ Metric.ediam (t n) := Metric.edist_le_ediam_of_mem hx' hy'
        have h3 : edist y' y ≤ ENNReal.ofReal (δ n) := by
          rw [edist_dist, dist_comm]; exact ENNReal.ofReal_le_ofReal hyy'.le
        rw [hB_def]; simp only
        calc (edist x x' + edist x' y') + edist y' y
            ≤ (ENNReal.ofReal (δ n) + Metric.ediam (t n)) + ENNReal.ofReal (δ n) := by gcongr
          _ = Metric.ediam (t n) + (ENNReal.ofReal (δ n) + ENNReal.ofReal (δ n)) := by ring
          _ = Metric.ediam (t n) + ENNReal.ofReal (2 * δ n) := by
              rw [← ENNReal.ofReal_add (hδpos n).le (hδpos n).le]; ring_nf
      have hBsmall : ∀ n, B n ≤ ((k:ℝ≥0∞)+1)⁻¹ := by
        intro n; rw [hB_def]; simp only
        have hle1 : Metric.ediam (t n) ≤ (2*((k:ℝ≥0∞)+1))⁻¹ := htsmall n
        have hle2 : ENNReal.ofReal (2 * δ n) ≤ (2*((k:ℝ≥0∞)+1))⁻¹ := by
          have hd : (2 * δ n) ≤ 1/(2*((k:ℝ)+1)) := by
            have := hδle n; rw [le_div_iff₀ (by positivity)] at this ⊢; nlinarith
          refine (ENNReal.ofReal_le_ofReal hd).trans ?_
          rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
              ENNReal.ofReal_mul (by norm_num)]
          rw [show ENNReal.ofReal ((k:ℝ)+1) = (k:ℝ≥0∞)+1 by
                rw [ENNReal.ofReal_add (by positivity) (by norm_num)]; norm_num,
              show ENNReal.ofReal 2 = (2:ℝ≥0∞) by norm_num, one_div]
        calc Metric.ediam (t n) + ENNReal.ofReal (2 * δ n)
            ≤ (2*((k:ℝ≥0∞)+1))⁻¹ + (2*((k:ℝ≥0∞)+1))⁻¹ := by gcongr
          _ = ((k:ℝ≥0∞)+1)⁻¹ := by
              rw [← two_mul, ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
                  ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      have hcovP : ∀ z ∈ Kc, ∃ p : ℕ × ℚ, z ∈ ball' p ∧ ∃ n, ball' p ⊆ W n := by
        intro z hz
        obtain ⟨n, hn⟩ : ∃ n, z ∈ W n := by have := hKW hz; rwa [mem_iUnion] at this
        obtain ⟨p, hzp, hpW⟩ := hsel z (W n) (hWopen n) hn
        exact ⟨p, hzp, n, hpW⟩
      choose! pp hzpp hnpp using hcovP
      obtain ⟨T, hTsub, hTfin, hTcov⟩ := hKc.elim_finite_subcover_image
        (b := Kc) (c := fun z => ball' (pp z)) (fun z _ => hballopen (pp z))
        (by intro z hz; rw [mem_iUnion₂]; exact ⟨z, hz, hzpp z hz⟩)
      set Tf := hTfin.toFinset with hTf
      set P : Finset (ℕ × ℚ) := Tf.image pp with hP
      have hPprop : ∀ p ∈ P, ∃ n, ball' p ⊆ W n := by
        intro p hp; rw [hP, Finset.mem_image] at hp
        obtain ⟨z, hzT, rfl⟩ := hp
        exact hnpp z (hTsub (by rw [hTf, Set.Finite.mem_toFinset] at hzT; exact hzT))
      choose! ν hν using hPprop
      have hKcovP : Kc ⊆ ⋃ p ∈ P, ball' p := by
        intro z hz
        have := hTcov hz; rw [mem_iUnion₂] at this
        obtain ⟨w, hwT, hzw⟩ := this
        rw [mem_iUnion₂]; refine ⟨pp w, ?_, hzw⟩
        rw [hP, Finset.mem_image]; exact ⟨w, by rw [hTf, Set.Finite.mem_toFinset]; exact hwT, rfl⟩
      have hνW : ∀ p ∈ P, ball' p ⊆ W (ν p) := fun p hp => hν p hp
      set grp : ℕ → Finset (ℕ × ℚ) := fun n => P.filter (fun p => ν p = n) with hgrp
      set S : Finset (Finset (ℕ × ℚ)) := (P.image ν).image grp with hS
      have hgrpW : ∀ n, elem (grp n) ⊆ W n := by
        intro n; rw [helem]; refine iUnion₂_subset ?_; intro p hp
        rw [hgrp, Finset.mem_filter] at hp; rw [← hp.2]; exact hνW p hp.1
      have hgrpdiam : ∀ n, Metric.ediam (elem (grp n)) ≤ B n := fun n =>
        (Metric.ediam_mono (hgrpW n)).trans (hWdiam n)
      have hScover : Kc ⊆ scover S := by
        rw [hscover]
        refine hKcovP.trans ?_
        intro z hz; rw [mem_iUnion₂] at hz; obtain ⟨p, hp, hzp⟩ := hz
        rw [mem_iUnion₂]; refine ⟨grp (ν p), ?_, ?_⟩
        · rw [hS, Finset.mem_image]; exact ⟨ν p, Finset.mem_image_of_mem ν hp, rfl⟩
        · rw [helem, mem_iUnion₂]; exact ⟨p, by rw [hgrp, Finset.mem_filter]; exact ⟨hp, rfl⟩, hzp⟩
      have hSsmall : ∀ s ∈ S, Metric.ediam (elem s) ≤ ((k:ℝ≥0∞)+1)⁻¹ := by
        intro s hs; rw [hS, Finset.mem_image] at hs
        obtain ⟨n, hn, rfl⟩ := hs; exact (hgrpdiam n).trans (hBsmall n)
      have hGle : G k c ≤ scost S := by
        rw [hG]; simp only
        refine iInf_le_of_le S ?_
        rw [hGterm]; simp only; rw [if_pos ⟨hSsmall, hScover⟩]
      refine hGle.trans ?_
      have himg : scost S
          ≤ ∑ n ∈ P.image ν,
              (⨆ _ : (elem (grp n)).Nonempty, Metric.ediam (elem (grp n)) ^ (1:ℝ)) := by
        rw [hscost, hS, ← Finset.sum_fiberwise_of_maps_to (g := grp) (t := (P.image ν).image grp)
              (fun n hn => Finset.mem_image_of_mem grp hn)]
        apply Finset.sum_le_sum; intro s hs
        obtain ⟨n0, hn0T, hn0⟩ := Finset.mem_image.1 hs
        have hmem : n0 ∈ (P.image ν).filter (fun n => grp n = s) := Finset.mem_filter.2 ⟨hn0T, hn0⟩
        calc (⨆ _ : (elem s).Nonempty, Metric.ediam (elem s) ^ (1:ℝ))
            = (⨆ _ : (elem (grp n0)).Nonempty, Metric.ediam (elem (grp n0)) ^ (1:ℝ)) := by rw [hn0]
          _ ≤ ∑ n ∈ (P.image ν).filter (fun n => grp n = s),
                (⨆ _ : (elem (grp n)).Nonempty, Metric.ediam (elem (grp n)) ^ (1:ℝ)) :=
              Finset.single_le_sum
                (f := fun n => ⨆ _ : (elem (grp n)).Nonempty, Metric.ediam (elem (grp n)) ^ (1:ℝ))
                (fun _ _ => zero_le) hmem
      have hstep2 :
          ∑ n ∈ P.image ν, (⨆ _ : (elem (grp n)).Nonempty, Metric.ediam (elem (grp n)) ^ (1:ℝ))
            ≤ ∑ n ∈ P.image ν, ((⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ))
                + ENNReal.ofReal (2 * δ n)) := by
        apply Finset.sum_le_sum; intro n _
        have hb : (⨆ _ : (elem (grp n)).Nonempty, Metric.ediam (elem (grp n)) ^ (1:ℝ)) ≤ B n := by
          refine iSup_le (fun _ => ?_); rw [ENNReal.rpow_one]; exact hgrpdiam n
        refine hb.trans ?_
        rw [hB_def]; simp only; gcongr
        by_cases h : (t n).Nonempty
        · rw [ciSup_pos h, ENNReal.rpow_one]
        · rw [not_nonempty_iff_eq_empty] at h; rw [h]; simp
      calc scost S
          ≤ ∑ n ∈ P.image ν, ((⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ))
              + ENNReal.ofReal (2 * δ n)) := himg.trans hstep2
        _ = (∑ n ∈ P.image ν, (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ)))
              + ∑ n ∈ P.image ν, ENNReal.ofReal (2 * δ n) := Finset.sum_add_distrib
        _ ≤ (∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ)) + εE :=
              add_le_add (ENNReal.sum_le_tsum _) ((ENNReal.sum_le_tsum _).trans hδsum)
    -- assemble identity
    refine ⟨le_antisymm ?_ ?_, hB_dir⟩
    · rw [hHA]; refine iSup₂_le ?_; intro r hr
      obtain ⟨k, hkr⟩ : ∃ k : ℕ, ((k:ℝ≥0∞)+1)⁻¹ ≤ r := by
        rcases eq_or_ne r ∞ with rfl | hrtop
        · exact ⟨0, le_top⟩
        · obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt (a := r) hr.ne'
          exact ⟨k, (ENNReal.inv_le_inv.2 le_self_add).trans hk.le⟩
      calc content c r ≤ content c ((k:ℝ≥0∞)+1)⁻¹ := hcontent_anti _ _ hkr
        _ ≤ G k c := hA_dir k
        _ ≤ ⨆ k, G k c := le_iSup (fun k => G k c) k
    · refine iSup_le ?_; intro k
      calc G k c ≤ content c (2*((k:ℝ≥0∞)+1))⁻¹ := hB_dir k
        _ ≤ μH[(1:ℝ)] Kc := by
            rw [hHA]; refine le_iSup₂_of_le (2*((k:ℝ≥0∞)+1))⁻¹ ?_ le_rfl
            rw [ENNReal.inv_pos]
            exact ENNReal.mul_ne_top (by norm_num)
              (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top k, by norm_num⟩)
  -- ============================================================
  -- MCT + per-scale covering bound.
  -- ============================================================
  have hGmono : Monotone G := by
    intro k k' hkk' c
    rw [hG]; simp only
    refine le_iInf fun S => ?_
    have hkey2 : Gterm k S c ≤ Gterm k' S c := by
      rw [hGterm]; simp only
      by_cases hv' : (∀ s ∈ S, Metric.ediam (elem s) ≤ ((k':ℝ≥0∞)+1)⁻¹)
          ∧ g ⁻¹' {c} ∩ A ⊆ scover S
      · have hv : (∀ s ∈ S, Metric.ediam (elem s) ≤ ((k:ℝ≥0∞)+1)⁻¹)
            ∧ g ⁻¹' {c} ∩ A ⊆ scover S := by
          refine ⟨fun s hs => (hv'.1 s hs).trans ?_, hv'.2⟩
          apply ENNReal.inv_le_inv.2
          gcongr
        rw [if_pos hv, if_pos hv']
      · rw [if_neg hv']; exact le_top
    exact (iInf_le _ S).trans hkey2
  rw [show (fun c => μH[(1:ℝ)] (g ⁻¹' {c} ∩ A)) = fun c => ⨆ k, G k c from
        funext (fun c => (hkey c).1)]
  rw [lintegral_iSup hGmeas hGmono]
  refine iSup_le (fun k => ?_)
  set r' : ℝ≥0∞ := (2*((k:ℝ≥0∞)+1))⁻¹ with hr'_def
  have hr'pos : 0 < r' := by
    rw [hr'_def, ENNReal.inv_pos]
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top k, by norm_num⟩)
  set content2f : ℝ≥0∞ → ℝ≥0∞ := fun r =>
    ⨅ t : ℕ → Set ℂ, if (A ⊆ ⋃ n, t n) ∧ (∀ n, Metric.ediam (t n) ≤ r)
      then ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (2:ℝ) else ⊤ with hcontent2f
  have hcontent2f_le : content2f r' ≤ μH[(2:ℝ)] A := by
    rw [Measure.hausdorffMeasure_apply]
    refine le_iSup₂_of_le r' hr'pos ?_
    refine le_iInf fun t => le_iInf fun htcov => le_iInf fun htsmall => ?_
    rw [hcontent2f]; simp only
    refine iInf_le_of_le t ?_
    rw [if_pos ⟨htcov, htsmall⟩]
  have hKne : (K : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hKzero : (K : ℝ≥0∞) ≠ 0 := by
    simpa only [ne_eq, ENNReal.coe_eq_zero] using hKne0
  have hbound : ∫⁻ c, G k c ≤ (K : ℝ≥0∞) * content2f r' := by
    rw [hcontent2f, ENNReal.mul_iInf_of_ne hKzero hKne]
    refine le_iInf fun t => ?_
    by_cases hcov : (A ⊆ ⋃ n, t n) ∧ (∀ n, Metric.ediam (t n) ≤ r')
    · rw [if_pos hcov]
      obtain ⟨htcov, htsmall⟩ := hcov
      set F : ℕ → ℝ → ℝ≥0∞ :=
        fun n c => (g '' (A ∩ closure (t n))).indicator (fun _ => Metric.ediam (t n)) c with hF_def
      have hAclos : ∀ n, IsCompact (A ∩ closure (t n)) := fun n => hA.inter_right isClosed_closure
      have hFimg_meas : ∀ n, MeasurableSet (g '' (A ∩ closure (t n))) :=
        fun n => ((hAclos n).image hgcont).measurableSet
      have hFmeas : ∀ n, Measurable (F n) := by
        intro n; rw [hF_def]; exact Measurable.indicator measurable_const (hFimg_meas n)
      have hptwise : ∀ c, G k c ≤ ∑' n, F n c := by
        intro c
        have hGle : G k c ≤ content c r' := (hkey c).2 k
        refine hGle.trans ?_
        rw [hcontent]
        set t'' : ℕ → Set ℂ :=
          fun n => if c ∈ g '' (A ∩ closure (t n)) then closure (t n) else ∅ with ht''_def
        have ht''cov : (g ⁻¹' {c} ∩ A) ⊆ ⋃ n, t'' n := by
          intro z hz
          obtain ⟨hzc, hzA⟩ := hz
          have hzU : z ∈ ⋃ n, t n := htcov hzA
          rw [mem_iUnion] at hzU; obtain ⟨n, hzn⟩ := hzU
          rw [mem_iUnion]; refine ⟨n, ?_⟩
          have hzclos : z ∈ closure (t n) := subset_closure hzn
          have hcimg : c ∈ g '' (A ∩ closure (t n)) := by
            refine ⟨z, ⟨hzA, hzclos⟩, ?_⟩
            simpa [mem_preimage, mem_singleton_iff] using hzc
          rw [ht''_def]; simp only; rw [if_pos hcimg]; exact hzclos
        have ht''small : ∀ n, Metric.ediam (t'' n) ≤ r' := by
          intro n; rw [ht''_def]; simp only
          by_cases hc : c ∈ g '' (A ∩ closure (t n))
          · rw [if_pos hc, Metric.ediam_closure]; exact htsmall n
          · rw [if_neg hc]; simp
        calc (⨅ (t' : ℕ → Set ℂ) (_ : (g ⁻¹' {c} ∩ A) ⊆ ⋃ n, t' n)
                  (_ : ∀ n, Metric.ediam (t' n) ≤ r'),
                ∑' n, ⨆ _ : (t' n).Nonempty, Metric.ediam (t' n) ^ (1:ℝ))
            ≤ ∑' n, ⨆ _ : (t'' n).Nonempty, Metric.ediam (t'' n) ^ (1:ℝ) :=
              iInf_le_of_le t'' (iInf_le_of_le ht''cov (iInf_le_of_le ht''small le_rfl))
          _ ≤ ∑' n, F n c := by
              apply ENNReal.tsum_le_tsum; intro n
              change (⨆ _ : (t'' n).Nonempty, Metric.ediam (t'' n) ^ (1:ℝ))
                ≤ (g '' (A ∩ closure (t n))).indicator (fun _ => Metric.ediam (t n)) c
              by_cases hc : c ∈ g '' (A ∩ closure (t n))
              · rw [indicator_of_mem hc]
                have htt : t'' n = closure (t n) := by
                  rw [ht''_def]; simp only; rw [if_pos hc]
                rw [htt, Metric.ediam_closure]
                refine iSup_le (fun _ => ?_); rw [ENNReal.rpow_one]
              · have htt : t'' n = ∅ := by
                  rw [ht''_def]; simp only; rw [if_neg hc]
                rw [htt]; simp
      calc ∫⁻ c, G k c
          ≤ ∫⁻ c, ∑' n, F n c := lintegral_mono hptwise
        _ = ∑' n, ∫⁻ c, F n c :=
            lintegral_tsum (fun n => (hFmeas n).aemeasurable)
        _ ≤ ∑' n, (K : ℝ≥0∞) * ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (2:ℝ) := by
            apply ENNReal.tsum_le_tsum; intro n
            change ∫⁻ c, (g '' (A ∩ closure (t n))).indicator (fun _ => Metric.ediam (t n)) c ≤ _
            rw [lintegral_indicator_const (hFimg_meas n)]
            have hvol : volume (g '' (A ∩ closure (t n))) ≤ (K : ℝ≥0∞) * Metric.ediam (t n) := by
              calc volume (g '' (A ∩ closure (t n)))
                  ≤ Metric.ediam (g '' (A ∩ closure (t n))) := Real.volume_le_diam _
                _ ≤ (K : ℝ≥0∞) * Metric.ediam (A ∩ closure (t n)) :=
                    hgLip.ediam_image_le _
                _ ≤ (K : ℝ≥0∞) * Metric.ediam (t n) := by
                    have hdle : Metric.ediam (A ∩ closure (t n)) ≤ Metric.ediam (t n) :=
                      (Metric.ediam_mono inter_subset_right).trans_eq (Metric.ediam_closure (t n))
                    gcongr
            by_cases hne : (t n).Nonempty
            · rw [ciSup_pos hne]
              calc Metric.ediam (t n) * volume (g '' (A ∩ closure (t n)))
                  ≤ Metric.ediam (t n) * ((K : ℝ≥0∞) * Metric.ediam (t n)) := by gcongr
                _ = (K : ℝ≥0∞) * (Metric.ediam (t n) * Metric.ediam (t n)) := by ring
                _ = (K : ℝ≥0∞) * Metric.ediam (t n) ^ (2:ℝ) := by
                    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, sq]
            · rw [not_nonempty_iff_eq_empty] at hne
              rw [hne]
              simp only [closure_empty, inter_empty, image_empty, measure_empty, mul_zero]
              exact zero_le
        _ = (K : ℝ≥0∞) * ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (2:ℝ) :=
            ENNReal.tsum_mul_left
    · rw [if_neg hcov, ENNReal.mul_top hKzero]; exact le_top
  calc ∫⁻ c, G k c
      ≤ (K : ℝ≥0∞) * content2f r' := hbound
    _ ≤ (K : ℝ≥0∞) * μH[(2:ℝ)] A := by gcongr

/-- **`μH[2]` is a positive multiple of `volume` on `ℂ` (normalization).**

The 2-dimensional Hausdorff measure on the complex plane (with its Euclidean / L2 metric) is a
strictly positive scalar multiple of the canonical planar Lebesgue measure `volume`:
`μH[2] = c • volume` for some `c : ℝ≥0`, `0 < c`.

## Truth and direction

Proportionality, NOT equality. Mathlib's `μH[d]` is the *raw* Hausdorff measure
(`diam ^ d`, with no normalizing constant). On `ℂ`'s Euclidean (L2) metric the raw `μH[2]` is
**not** `volume`: the exact factor is `4/π` (only the sup metric gives `μH[2] = volume`, cf.
`MeasureTheory.hausdorffMeasure_pi_real`). What *is* true and all that is needed downstream is the
**proportionality** `μH[2] = c • volume` with `c > 0`.

## Proof

`ℂ` is a 2-dimensional real inner product space (`Complex.finrank_real_complex`), and
`InnerProductSpace.euclideanHausdorffMeasure_eq_volume` gives `μHE[finrank ℝ ℂ] = volume`, i.e.
`μHE[2] = volume`. By `Measure.euclideanHausdorffMeasure_def`, `μHE[2] = k • μH[2]` where
`k := addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin 2))) μH[2]`, which is nonzero by
`Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero`. Hence `volume = k • μH[2]`, so
`μH[2] = k⁻¹ • volume`; take `c = k⁻¹ > 0`. The exact value `c = π/4` rests on a Mathlib
`proof_wanted` (`addHaarScalarFactor_hausdorffMeasure_eq`), so only proportionality is asserted. -/
theorem hausdorffMeasure_two_complex_smul_volume :
    ∃ c : ℝ≥0, 0 < c ∧ (μH[2] : Measure ℂ) = c • volume := by
  -- `μHE[finrank ℝ ℂ] = volume` on the inner product space `ℂ`.
  have hvol : (μHE[Module.finrank ℝ ℂ] : Measure ℂ) = volume :=
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume
  rw [Complex.finrank_real_complex] at hvol
  -- Unfold the definition `μHE[2] = k • μH[2]`.
  rw [Measure.euclideanHausdorffMeasure_def] at hvol
  set k : ℝ≥0 :=
    (volume : Measure (EuclideanSpace ℝ (Fin 2))).addHaarScalarFactor μH[(2 : ℕ)] with hk_def
  have hk0 : k ≠ 0 := Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero 2
  -- Reconcile the `ℕ`-cast index `μH[(↑2 : ℝ)]` with the statement's `μH[(2 : ℝ)]`.
  have hcast : (μH[((2 : ℕ) : ℝ)] : Measure ℂ) = (μH[(2 : ℝ)] : Measure ℂ) := by norm_num
  rw [hcast] at hvol
  -- Now `hvol : k • μH[2] = volume`; invert `k` to get `μH[2] = k⁻¹ • volume`.
  refine ⟨k⁻¹, inv_pos.mpr (pos_iff_ne_zero.mpr hk0), ?_⟩
  calc (μH[2] : Measure ℂ)
      = (1 : ℝ≥0) • (μH[2] : Measure ℂ) := (one_smul _ _).symm
    _ = (k⁻¹ * k) • (μH[2] : Measure ℂ) := by rw [inv_mul_cancel₀ hk0]
    _ = k⁻¹ • (k • (μH[2] : Measure ℂ)) := (smul_smul k⁻¹ k (μH[2] : Measure ℂ)).symm
    _ = k⁻¹ • volume := by rw [hvol]

/-- **Linear co-area equality on ℂ (the affine model for the sharp co-area inequality).**

For a continuous `ℝ`-linear functional `L : ℂ →L[ℝ] ℝ` and a measurable set `B ⊆ ℂ`, the integrated
arc-length (`μH[1]`) of the level lines of `L` meeting `B` equals `‖L‖` times the area of `B`:

`∫⁻ c, μH[1] (L ⁻¹' {c} ∩ B) ∂volume = (‖L‖₊ : ℝ≥0∞) * volume B`.

This is the **exact** co-area identity for the *affine* (here linear) case: the level sets
`L ⁻¹' {c}` are parallel lines, and Fubini in coordinates aligned with `L` evaluates the integral to
`‖L‖ · area`. It is the local model on which the sharp Lipschitz co-area inequality
`eilenberg_coarea_grad_le` is built by Rademacher/Besicovitch localization: on a small ball around a
point of differentiability, `u` is within `o(r)` of its linearization `L = fderiv ℝ u`, and this
identity supplies the leading term `‖L‖ · vol`.

## Truth and direction

Equality. For `L = 0` both sides are `0` (the left integrand is supported on the single
point `c = 0`, a `volume`-null set in `ℝ`). For `L ≠ 0`, rotate ℂ by a linear isometry sending the
unit normal of `L` to the real axis; isometries preserve `μH[1]`, `volume`, and `‖L‖`, reducing to
`L (x + i y) = ‖L‖ · x`, where `L ⁻¹' {c} ∩ B` is the vertical slice `{c/‖L‖} ×ℂ B_{c/‖L‖}`, whose
`μH[1]` is `volume` of the fiber (the vertical embedding `y ↦ ⟨c/‖L‖, y⟩` is an isometry,
`MeasureTheory.hausdorffMeasure_real`), and Fubini (`lintegral_lintegral` / `Measure.prod`) together
with the substitution `c = ‖L‖ · t` gives
`∫⁻ c, volume (fiber at c/‖L‖) = ‖L‖ · ∫⁻ t, volume (fiber at t) = ‖L‖ · volume B`. -/
theorem coarea_linear_eq (L : ℂ →L[ℝ] ℝ) {B : Set ℂ} (hB : MeasurableSet B) :
    ∫⁻ c, μH[1] (L ⁻¹' {c} ∩ B) = (‖L‖₊ : ℝ≥0∞) * volume B := by
  -- Case `L = 0`: the integrand is supported on the single point `c = 0`, a null set in `ℝ`.
  rcases eq_or_ne L 0 with hL0 | hL0
  · subst hL0
    rw [nnnorm_zero]
    simp only [ENNReal.coe_zero, zero_mul]
    have hint : (fun c : ℝ => μH[1] ((0 : ℂ →L[ℝ] ℝ) ⁻¹' {c} ∩ B))
        = Set.indicator {0} (fun _ => μH[1] B) := by
      ext c
      by_cases hc : c = 0
      · subst hc
        rw [indicator_of_mem (by simp)]
        congr 1
        rw [Set.inter_eq_right]
        intro z _
        simp
      · rw [indicator_of_notMem (by simp [hc])]
        have hempty : (0 : ℂ →L[ℝ] ℝ) ⁻¹' {c} = ∅ := by
          ext z; simp [eq_comm, hc]
        rw [hempty, Set.empty_inter, measure_empty]
    rw [hint, lintegral_indicator (measurableSet_singleton 0), setLIntegral_const,
      Real.volume_singleton, mul_zero]
  -- Case `L ≠ 0`: rotate so `L` becomes `‖L‖ • re`, then slice and apply Fubini.
  · -- Riesz vector `v` with `L w = ⟪v, w⟫` and `‖v‖ = ‖L‖`.
    set v := (InnerProductSpace.toDual ℝ ℂ).symm L with hv_def
    have hLnorm : ‖v‖ = ‖L‖ := LinearIsometryEquiv.norm_map _ _
    have hv : v ≠ 0 := by
      intro h
      apply hL0
      have hLeq : L = (InnerProductSpace.toDual ℝ ℂ) v := by
        rw [hv_def, LinearIsometryEquiv.apply_symm_apply]
      rw [hLeq, h, map_zero]
    have hLpos : 0 < ‖L‖ := by rw [← hLnorm]; positivity
    have hLne : ‖L‖ ≠ 0 := ne_of_gt hLpos
    have hriesz : ∀ z : ℂ, L z = inner ℝ v z := fun z => by
      rw [hv_def]; exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)).symm
    -- The rotation: multiplication by the unit `v / ‖v‖`.
    have hmem : v / (‖v‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, norm_norm,
        div_self (by rw [Ne, norm_eq_zero]; exact hv)]
    set a : Circle := ⟨v / (‖v‖ : ℂ), hmem⟩ with ha_def
    have hrot : ∀ w : ℂ, L (rotation a w) = ‖L‖ * w.re := by
      intro w
      rw [rotation_apply]
      change L (((⟨v / (‖v‖ : ℂ), hmem⟩ : Circle) : ℂ) * w) = ‖L‖ * w.re
      rw [hriesz, Complex.inner]
      have hvn : (‖v‖ : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero, norm_eq_zero]; exact hv
      have key : v * (starRingEnd ℂ) v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have heq : ((v / (‖v‖ : ℂ)) * w) * (starRingEnd ℂ) v = w * (‖v‖ : ℂ) := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hvn]
        rw [show v * w * (starRingEnd ℂ) v = w * (v * (starRingEnd ℂ) v) by ring, key]
        push_cast; ring
      change (((v / (‖v‖ : ℂ)) * w) * (starRingEnd ℂ) v).re = ‖L‖ * w.re
      rw [heq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hLnorm]
      ring
    -- Replace `B` by the rotated set `B'`.
    set B' : Set ℂ := rotation a ⁻¹' B with hB'_def
    have hB'meas : MeasurableSet B' := (rotation a).continuous.measurable hB
    have hvolB : volume B' = volume B := by
      have hmp : MeasurePreserving (rotation a) (volume : Measure ℂ) volume :=
        LinearIsometryEquiv.measurePreserving (rotation a)
      exact hmp.measure_preimage hB.nullMeasurableSet
    -- Reduce each level-set measure to the rotated slice.
    have stepA : ∀ c : ℝ,
        μH[(1:ℝ)] (L ⁻¹' {c} ∩ B) = μH[1] ({w : ℂ | ‖L‖ * w.re = c} ∩ B') := by
      intro c
      have hLmeas : MeasurableSet (L ⁻¹' {c} ∩ B) :=
        ((L.continuous.measurable (measurableSet_singleton c))).inter hB
      have hmp := IsometryEquiv.measurePreserving_hausdorffMeasure
        (rotation a).toIsometryEquiv (1:ℝ)
      rw [← hmp.measure_preimage hLmeas.nullMeasurableSet]
      congr 1
      ext w
      have hcoe : (rotation a).toIsometryEquiv w = rotation a w := rfl
      simp only [mem_preimage, mem_inter_iff, mem_singleton_iff, mem_ofPred_eq, hcoe, hB'_def]
      rw [hrot w]
    -- Each vertical slice's `μH[1]` is the fiber `volume`.
    have stepB : ∀ c : ℝ,
        μH[(1:ℝ)] ({w : ℂ | ‖L‖ * w.re = c} ∩ B')
          = volume {y : ℝ | Complex.mk (c / ‖L‖) y ∈ B'} := by
      intro c
      have hset : {w : ℂ | ‖L‖ * w.re = c} = {w : ℂ | w.re = c / ‖L‖} := by
        ext w; simp only [mem_ofPred_eq]; rw [eq_div_iff hLne, mul_comm]
      rw [hset]
      have hiso : Isometry (fun y : ℝ => Complex.mk (c / ‖L‖) y) := by
        intro y1 y2
        simp only [edist_dist, Complex.dist_eq, Real.dist_eq]
        congr 1
        rw [Complex.norm_eq_sqrt_sq_add_sq]
        simp only [Complex.sub_re, Complex.sub_im, sub_self]
        rw [zero_pow (by norm_num), zero_add, Real.sqrt_sq_eq_abs]
      have himgeq : {w : ℂ | w.re = c / ‖L‖} ∩ B'
          = (fun y : ℝ => Complex.mk (c / ‖L‖) y) ''
            {y | Complex.mk (c / ‖L‖) y ∈ B'} := by
        ext w
        simp only [mem_inter_iff, mem_ofPred_eq, mem_image]
        constructor
        · rintro ⟨hre, hBmem⟩
          refine ⟨w.im, ?_, ?_⟩
          · show Complex.mk (c / ‖L‖) w.im ∈ B'
            have hweq : Complex.mk (c / ‖L‖) w.im = w := by apply Complex.ext <;> simp [hre]
            rw [hweq]; exact hBmem
          · apply Complex.ext <;> simp [hre]
        · rintro ⟨y, hy, rfl⟩
          exact ⟨by simp, hy⟩
      rw [himgeq, hiso.hausdorffMeasure_image (Or.inl (by norm_num)),
        MeasureTheory.hausdorffMeasure_real]
    -- The fiber `volume` is measurable in the slice parameter.
    have hgmeas : Measurable (fun s : ℝ => volume {y : ℝ | Complex.mk s y ∈ B'}) := by
      have hSmeas : MeasurableSet (Complex.measurableEquivRealProd.symm ⁻¹' B') :=
        Complex.measurableEquivRealProd.symm.measurable hB'meas
      exact measurable_measure_prodMk_left (α := ℝ) (ν := (volume : Measure ℝ)) hSmeas
    -- Assemble: rewrite the integral, scale, then apply Fubini.
    calc ∫⁻ c, μH[1] (L ⁻¹' {c} ∩ B)
        = ∫⁻ c, volume {y : ℝ | Complex.mk (c / ‖L‖) y ∈ B'} := by
          apply lintegral_congr; intro c; rw [stepA c, stepB c]
      _ = ENNReal.ofReal ‖L‖ * ∫⁻ s, volume {y : ℝ | Complex.mk s y ∈ B'} := by
          set g : ℝ → ℝ≥0∞ := fun s => volume {y : ℝ | Complex.mk s y ∈ B'}
            with hg_def
          change ∫⁻ c, g (c / ‖L‖) ∂(volume : Measure ℝ)
              = ENNReal.ofReal ‖L‖ * ∫⁻ s, g s ∂volume
          have hg2 : Measurable (fun c => g (c / ‖L‖)) :=
            hgmeas.comp (measurable_id.div_const ‖L‖)
          have hmapint2 : ∫⁻ x, g (x / ‖L‖) ∂(Measure.map ((‖L‖ : ℝ) * ·) volume)
              = ∫⁻ y, g ((‖L‖ * y) / ‖L‖) ∂volume :=
            lintegral_map hg2 (measurable_const_mul ‖L‖)
          rw [Real.map_volume_mul_left hLne, lintegral_smul_measure,
            abs_of_pos (inv_pos.mpr hLpos)] at hmapint2
          have heq2 : (fun y => g ((‖L‖ * y) / ‖L‖)) = g := by
            ext y; rw [mul_comm (‖L‖) y, mul_div_assoc, div_self hLne, mul_one]
          rw [heq2, smul_eq_mul] at hmapint2
          rw [← hmapint2, ← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hLpos),
            mul_inv_cancel₀ hLne, ENNReal.ofReal_one, one_mul]
      _ = ENNReal.ofReal ‖L‖ * volume B' := by
          congr 1
          have hmp : MeasurePreserving Complex.measurableEquivRealProd
              (volume : Measure ℂ) volume :=
            Complex.volume_preserving_equiv_real_prod
          have hmps : MeasurePreserving Complex.measurableEquivRealProd.symm
              (volume : Measure (ℝ × ℝ)) volume := hmp.symm _
          have hSmeas : MeasurableSet (Complex.measurableEquivRealProd.symm ⁻¹' B') :=
            Complex.measurableEquivRealProd.symm.measurable hB'meas
          have hvolS : volume (Complex.measurableEquivRealProd.symm ⁻¹' B') = volume B' :=
            hmps.measure_preimage hB'meas.nullMeasurableSet
          rw [← hvolS, show (volume : Measure (ℝ × ℝ))
              = (volume : Measure ℝ).prod volume from Measure.volume_eq_prod ℝ ℝ,
            Measure.prod_apply hSmeas]
          apply lintegral_congr
          intro s
          congr 1
      _ = (‖L‖₊ : ℝ≥0∞) * volume B := by
          rw [hvolB]
          congr 1
          exact ((ENNReal.ofReal_coe_nnreal).symm.trans (by rw [coe_nnnorm])).symm

open scoped Pointwise in
/-- **Arc-length bound for a differentiable curve (the `≤` fiber length, area-formula route).**

For a curve `γ : ℝ → ℂ` that is differentiable on a measurable set `I` with derivative `γ'`, the
`1`-dimensional Hausdorff measure of its image is bounded by the integral of its speed:

`μH[1] (γ '' I) ≤ ∫⁻ t in I, ‖γ' t‖₊`.

This is the `≤` ("length `≤` `∫` speed") direction of the 1-D area formula — no injectivity needed.
It is the fiber-length ingredient of the area-formula proof of the sharp co-area inequality: applied
to the level-curve parametrization `γ_c = Φ⁻¹(c, ·)` of `Φ = (u, ℓ)` on an injective piece, it turns
`μH[1] (u ⁻¹' {c} ∩ S)` into a fiber integral that Fubini + the area formula
(`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) convert to `∫⁻ z in S, ‖∇u z‖`.

## Truth and proof

Standard: cover `I` by countably many small pieces on each of which `γ` is, up to
`o`, affine with slope `γ' t₀`, so `μH[1] (γ '' piece) ≤ (‖γ' t₀‖ + ε) · volume piece` (via
`LipschitzOnWith.hausdorffMeasure_image_le` with the local Lipschitz constant), and sum.
Equivalently `μH[1] (γ '' I) ≤ eVariationOn γ I ≤ ∫⁻ I ‖γ'‖` (image Hausdorff measure `≤` the
variation, which for a curve with derivative `γ'` is `≤ ∫ ‖γ'‖`). `γ'` is measurable as an a.e.
derivative of the continuous `γ`. -/
theorem hausdorffMeasure_one_image_le {γ γ' : ℝ → ℂ} {I : Set ℝ}
    (hI : MeasurableSet I) (hγ' : ∀ t ∈ I, HasDerivWithinAt γ (γ' t) I t) :
    μH[1] (γ '' I) ≤ ∫⁻ t in I, (‖γ' t‖₊ : ℝ≥0∞) := by
  classical
  -- The Frechet derivative associated to `deriv γ' x` is `smulRight 1 (γ' x)`, of norm `‖γ' x‖`;
  -- `HasDerivWithinAt` is definitionally `HasFDerivWithinAt` with this `f'`.
  set f' : ℝ → (ℝ →L[ℝ] ℂ) := fun x => (1 : ℝ →L[ℝ] ℝ).smulRight (γ' x) with hf'def
  have hfd : ∀ x ∈ I, HasFDerivWithinAt γ (f' x) I x := fun x hx => hγ' x hx
  have hnorm : ∀ x, ‖f' x‖₊ = ‖γ' x‖₊ := by
    intro x
    apply NNReal.coe_injective
    simp only [hf'def, coe_nnnorm, ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul]
  -- KEY 1: the analogue of `ApproximatesLinearOn.norm_fderiv_sub_le` for `A : ℝ →L[ℝ] ℂ`.
  -- Mathlib's lemma is stated only for square maps `E →L[ℝ] E`; its proof (Lebesgue density
  -- points + Besicovitch differentiation) is dimension-agnostic, so we replay it inline here.
  have nfsl : ∀ (A : ℝ →L[ℝ] ℂ) (δ : ℝ≥0) (s : Set ℝ),
      MeasurableSet s → ApproximatesLinearOn γ A s δ →
      (∀ x ∈ s, HasFDerivWithinAt γ (f' x) s x) →
      ∀ᵐ x ∂(volume : Measure ℝ).restrict s, ‖f' x - A‖₊ ≤ δ := by
    intro A δ s hs hf hfd_s
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div (volume : Measure ℝ) s,
      ae_restrict_mem hs]
    intro x hx xs
    apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
    suffices H : ∀ ε, 0 < ε → ‖(f' x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε by
      have hT : Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε) (𝓝[>] 0)
          (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖f' x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at hT
      apply le_of_tendsto_of_tendsto tendsto_const_nhds hT
      filter_upwards [self_mem_nhdsWithin]
      exact H
    intro ε εpos
    have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • Metric.closedBall z ε)).Nonempty :=
      Measure.eventually_nonempty_inter_smul_of_density_one (volume : Measure ℝ) s x hx _
        measurableSet_closedBall (Metric.measure_closedBall_pos (volume : Measure ℝ) z εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ :
        ∃ ρ > 0, Metric.ball x ρ ∩ s ⊆ {y : ℝ | ‖γ y - γ x - (f' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      Metric.mem_nhdsWithin_iff.1 (((hfd_s x xs).isLittleO).def εpos)
    have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • Metric.closedBall z ε ⊆ Metric.ball x ρ := by
      apply nhdsWithin_le_nhds
      exact eventually_singleton_add_smul_subset Metric.isBounded_closedBall
        (Metric.ball_mem_nhds x ρpos)
    obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ :
        ∃ r : ℝ, (s ∩ ({x} + r • Metric.closedBall z ε)).Nonempty ∧
          {x} + r • Metric.closedBall z ε ⊆ Metric.ball x ρ ∧ 0 < r :=
      (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, az, ya⟩ : ∃ a, a ∈ Metric.closedBall z ε ∧ y = x + r • a := by
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
      rcases hy with ⟨a, az, ha⟩
      exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
      calc ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
    have Iineq : r * ‖(f' x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
      calc r * ‖(f' x - A) a‖ = ‖(f' x - A) (r • a)‖ := by
            rw [map_smul, Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg rpos.le]
        _ = ‖γ y - γ x - A (y - x) - (γ y - γ x - (f' x) (y - x))‖ := by
            congr 1
            simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left,
              FunLike.coe_sub, Pi.sub_apply, map_smul]
            module
        _ ≤ ‖γ y - γ x - A (y - x)‖ + ‖γ y - γ x - (f' x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := (add_le_add (hf _ ys _ xs) (hρ ⟨rρ hy, ys⟩))
        _ = r * (δ + ε) * ‖a‖ := by
            simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
            ring
        _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
    calc ‖(f' x - A) z‖ = ‖(f' x - A) a + (f' x - A) (z - a)‖ := by
          congr 1
          simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
          abel
      _ ≤ ‖(f' x - A) a‖ + ‖(f' x - A) (z - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ‖z - a‖ := by
          apply add_le_add
          · rw [mul_assoc] at Iineq; exact (mul_le_mul_iff_right₀ rpos).1 Iineq
          · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε := by
          rw [mem_closedBall_iff_norm'] at az
          gcongr
  -- KEY 2: a map approximated by `A` up to `δ` is `(‖A‖ + δ)`-Lipschitz, expanding `μH[1]` by
  -- at most that factor (the `d = 1` case of `LipschitzOnWith.hausdorffMeasure_image_le`).
  have expand : ∀ (A : ℝ →L[ℝ] ℂ) (δ : ℝ≥0) (t : Set ℝ),
      ApproximatesLinearOn γ A t δ →
      μH[1] (γ '' t) ≤ ((‖A‖₊ + δ : ℝ≥0) : ℝ≥0∞) * μH[1] t := by
    intro A δ t htg
    have hlip : LipschitzOnWith (‖A‖₊ + δ) γ t := by
      rw [lipschitzOnWith_iff_restrict]; exact htg.lipschitz
    calc μH[1] (γ '' t) ≤ ((‖A‖₊ + δ : ℝ≥0) : ℝ≥0∞) ^ (1 : ℝ) * μH[1] t :=
          hlip.hausdorffMeasure_image_le (by norm_num)
      _ = ((‖A‖₊ + δ : ℝ≥0) : ℝ≥0∞) * μH[1] t := by rw [ENNReal.rpow_one]
  -- On the source `ℝ`, `μH[1] = volume`.
  have hHvol : (μH[1] : Measure ℝ) = volume := hausdorffMeasure_real
  -- AUX1: the finite-error estimate, via a measurable partition on which `γ` is well approximated
  -- by linear maps (`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`).
  have aux1 : ∀ {s : Set ℝ}, MeasurableSet s →
      (∀ x ∈ s, HasFDerivWithinAt γ (f' x) s x) → ∀ {ε : ℝ≥0}, 0 < ε →
      μH[1] (γ '' s) ≤ (∫⁻ x in s, (‖γ' x‖₊ : ℝ≥0∞)) + 2 * ε * (volume s) := by
    intro s hs hfds ε εpos
    obtain ⟨t, A, t_disj, t_meas, t_cover, ht, hAy⟩ :
        ∃ (t : ℕ → Set ℝ) (A : ℕ → (ℝ →L[ℝ] ℂ)),
          Pairwise (Function.onFun Disjoint t) ∧
            (∀ n : ℕ, MeasurableSet (t n)) ∧
              (s ⊆ ⋃ n : ℕ, t n) ∧
                (∀ n : ℕ, ApproximatesLinearOn γ (A n) (s ∩ t n) ε) ∧
                  (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt γ s f' hfds (fun _ => ε)
        (fun _ => εpos.ne')
    calc
      μH[1] (γ '' s) ≤ μH[1] (⋃ n, γ '' (s ∩ t n)) := by
        apply measure_mono
        rw [← image_iUnion, ← inter_iUnion]
        exact Set.image_mono (subset_inter Subset.rfl t_cover)
      _ ≤ ∑' n, μH[1] (γ '' (s ∩ t n)) := measure_iUnion_le _
      _ ≤ ∑' n, ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞) * μH[1] (s ∩ t n) := by
        apply ENNReal.tsum_le_tsum fun n => ?_
        exact expand (A n) ε (s ∩ t n) (ht n)
      _ = ∑' n, ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞) * volume (s ∩ t n) := by
        simp_rw [hHvol]
      _ = ∑' n, ∫⁻ _ in s ∩ t n, ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞) := by
        simp only [setLIntegral_const]
      _ ≤ ∑' n, ∫⁻ x in s ∩ t n, ((‖γ' x‖₊ : ℝ≥0∞) + 2 * ε) := by
        apply ENNReal.tsum_le_tsum fun n => ?_
        apply lintegral_mono_ae
        filter_upwards [nfsl (A n) ε (s ∩ t n) (hs.inter (t_meas n)) (ht n)
            (fun x hx => (hfds x hx.1).mono inter_subset_left)]
        intro x hx
        have hAle : (‖A n‖₊ : ℝ≥0) ≤ ‖γ' x‖₊ + ε := by
          calc (‖A n‖₊ : ℝ≥0) = ‖f' x - (f' x - A n)‖₊ := by rw [sub_sub_cancel]
            _ ≤ ‖f' x‖₊ + ‖f' x - A n‖₊ := nnnorm_sub_le _ _
            _ ≤ ‖f' x‖₊ + ε := by gcongr
            _ = ‖γ' x‖₊ + ε := by rw [hnorm]
        calc ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞) ≤ (((‖γ' x‖₊ + ε) + ε : ℝ≥0) : ℝ≥0∞) := by
              rw [ENNReal.coe_le_coe]; gcongr
          _ = (‖γ' x‖₊ : ℝ≥0∞) + 2 * ε := by push_cast; ring
      _ = ∫⁻ x in ⋃ n, s ∩ t n, ((‖γ' x‖₊ : ℝ≥0∞) + 2 * ε) := by
        rw [lintegral_iUnion (fun n => hs.inter (t_meas n))
          (pairwise_disjoint_mono t_disj fun n => inter_subset_right)]
      _ = ∫⁻ x in s, ((‖γ' x‖₊ : ℝ≥0∞) + 2 * ε) := by
        rw [← inter_iUnion, inter_eq_self_of_subset_left t_cover]
      _ = (∫⁻ x in s, (‖γ' x‖₊ : ℝ≥0∞)) + 2 * ε * (volume s) := by
        rw [lintegral_add_right' _ aemeasurable_const, setLIntegral_const]
  -- AUX2: let `ε → 0` for finite-measure sets.
  have aux2 : ∀ {s : Set ℝ}, MeasurableSet s → volume s ≠ ∞ →
      (∀ x ∈ s, HasFDerivWithinAt γ (f' x) s x) →
      μH[1] (γ '' s) ≤ ∫⁻ x in s, (‖γ' x‖₊ : ℝ≥0∞) := by
    intro s hs hsfin hfds
    have hlim : Tendsto (fun ε : ℝ≥0 =>
        (∫⁻ x in s, (‖γ' x‖₊ : ℝ≥0∞)) + 2 * (ε : ℝ≥0∞) * (volume s)) (𝓝[>] 0)
        (𝓝 ((∫⁻ x in s, (‖γ' x‖₊ : ℝ≥0∞)) + 2 * (0 : ℝ≥0) * (volume s))) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      refine tendsto_const_nhds.add ?_
      refine ENNReal.Tendsto.mul_const ?_ (Or.inr hsfin)
      exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 tendsto_id) (Or.inr ENNReal.coe_ne_top)
    simp only [ENNReal.coe_zero, mul_zero, zero_mul, add_zero] at hlim
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin]
    intro ε εpos
    rw [mem_Ioi] at εpos
    exact aux1 hs hfds εpos
  -- Reduce `I` to finite-measure disjoint pieces via the spanning sets of `volume`.
  set u : ℕ → Set ℝ := fun n => disjointed (spanningSets (volume : Measure ℝ)) n with hu_def
  have u_meas : ∀ n, MeasurableSet (u n) := fun n =>
    MeasurableSet.disjointed (fun i => measurableSet_spanningSets (volume : Measure ℝ) i) n
  have hIcover : I = ⋃ n, I ∩ u n := by
    rw [← inter_iUnion, iUnion_disjointed, iUnion_spanningSets, inter_univ]
  calc
    μH[1] (γ '' I) ≤ ∑' n, μH[1] (γ '' (I ∩ u n)) := by
      conv_lhs => rw [hIcover, image_iUnion]
      exact measure_iUnion_le _
    _ ≤ ∑' n, ∫⁻ x in I ∩ u n, (‖γ' x‖₊ : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply aux2 (hI.inter (u_meas n)) ?_ (fun x hx => (hfd x hx.1).mono inter_subset_left)
      have : volume (u n) < ∞ :=
        lt_of_le_of_lt (measure_mono (disjointed_subset _ _))
          (measure_spanningSets_lt_top (volume : Measure ℝ) n)
      exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_right) this)
    _ = ∫⁻ x in I, (‖γ' x‖₊ : ℝ≥0∞) := by
      rw [← lintegral_iUnion (fun n => hI.inter (u_meas n))
        (pairwise_disjoint_mono (disjoint_disjointed (spanningSets (volume : Measure ℝ)))
          (fun n => inter_subset_right)), ← hIcover]


end NoWanderingDomains.Coarea
