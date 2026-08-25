/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.Sobolev.Coarea.Foundations

/-!
# The planar co-area formula — the per-piece core

Second of three files for the sharp planar co-area inequality (see `Coarea.Foundations` for the
building blocks and `Coarea.Assembly` for the final result). This file proves:

* `coarea_null_le` — a `volume`-null set carries no integrated level-set length (the
  absolute-continuity ingredient);
* `eilenberg_coarea_planar_metric_meas` — the metric Eilenberg inequality for a measurable set
  (dropping the compactness hypothesis of `eilenberg_coarea_planar_metric`);
* `ae_uniqueDiffWithinAt_of_measurableSet` — almost every point of a measurable planar set is a
  point of unique differentiability (density-`1` ⟹ dense tangent cone);
* `coarea_piece_le` — the IFT-free per-piece core `∫⁻ c, μH[1] (u ⁻¹' {c} ∩ S) ≤ ∫⁻ z in S, ‖∇u‖`
  on a Lusin piece (bi-Lipschitz level curves via `ApproximatesLinearOn` + the area formula + the
  fiber arc-length bound). This is the genuine heart of the co-area formula.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace NoWanderingDomains.Coarea

/-- **Null sets carry no integrated level-set length (co-area absolute continuity).**

For a `K`-Lipschitz `u : ℂ → ℝ` and a `volume`-null measurable set `A`, the integrated arc-length of
the level sets meeting `A` vanishes:

`volume A = 0 → ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) = 0`.

This is the absolute-continuity ingredient of the co-area set function (`ν ≪ volume`). It is also
the "image of a null set is co-area-null" fact used to discard the non-differentiability set and to
handle the `{∇u = 0}` critical set in the area-formula proof.

## Truth and proof

Cover the null `A` by an open `U ⊇ A` of small area (`volume U < ε`, outer regularity).
Write `U = ⋃ₙ Kₙ` as an increasing union of compact sets (`U` is σ-compact in ℂ); then
`μH[1] (u ⁻¹' {c} ∩ Kₙ) ↑ μH[1] (u ⁻¹' {c} ∩ U)` (continuity from below) and, each `Kₙ` being
compact, `c ↦ μH[1] (u ⁻¹' {c} ∩ Kₙ)` is measurable (`measurable_slice_hausdorff_one`), so monotone
convergence gives `∫⁻ c, μH[1] (u ⁻¹' {c} ∩ U) = ⨆ₙ ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ Kₙ)`. Each term is
`≤ K · μH[2] Kₙ ≤ K · μH[2] U = K · c₀ · volume U < K · c₀ · ε` by `eilenberg_coarea_planar_metric`
and `hausdorffMeasure_two_complex_smul_volume`. Hence `∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) ≤ K c₀ ε` for all
`ε > 0`, so it is `0`. -/
theorem coarea_null_le {u : ℂ → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {A : Set ℂ} (hA : MeasurableSet A) (hA0 : volume A = 0) :
    ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) = 0 := by
  classical
  have _ := hA
  have hucont : Continuous u := hu.continuous
  -- The proportionality constant `μH[2] = c₀ • volume`.
  obtain ⟨c₀, hc₀pos, hc₀v⟩ := hausdorffMeasure_two_complex_smul_volume
  -- It suffices to bound the integral by `K * c₀ * ε` for every `ε > 0`.
  rw [← nonpos_iff_eq_zero]
  have key : ∀ ε : ℝ≥0∞, 0 < ε →
      ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) ≤ (K : ℝ≥0∞) * c₀ * ε := by
    intro ε εpos
    -- Outer regularity: open `U ⊇ A` with `volume U < ε`.
    obtain ⟨U, hAU, hUopen, hUvol⟩ :=
      Set.exists_isOpen_lt_of_lt A ε (by rw [hA0]; exact εpos)
    -- `U ≠ univ` since `volume U < ε < ∞` but `volume univ = ∞`.
    have hUne : U ≠ univ := by
      rintro rfl
      rw [measure_univ_of_isAddLeftInvariant] at hUvol
      exact (not_top_lt hUvol).elim
    have hUcompl_ne : (Uᶜ).Nonempty := by
      rw [nonempty_compl]; exact hUne
    -- Compact exhaustion of `U`:  Kₙ = closedBall 0 n ∩ {z | 1/(n+1) ≤ infDist z Uᶜ}.
    set Kset : ℕ → Set ℂ :=
      fun n => Metric.closedBall 0 n ∩ {z : ℂ | (1 : ℝ) / (n + 1) ≤ Metric.infDist z Uᶜ}
      with hKset_def
    have hKset_compact : ∀ n, IsCompact (Kset n) := by
      intro n
      apply (isCompact_closedBall (0 : ℂ) (n : ℝ)).of_isClosed_subset ?_ inter_subset_left
      refine (isCompact_closedBall (0 : ℂ) (n : ℝ)).isClosed.inter ?_
      exact isClosed_le continuous_const (Metric.continuous_infDist_pt Uᶜ)
    -- Each `Kₙ ⊆ U`.
    have hKset_subU : ∀ n, Kset n ⊆ U := by
      intro n z hz
      have hz2 : (1 : ℝ) / (n + 1) ≤ Metric.infDist z Uᶜ := hz.2
      by_contra hzU
      have hzc : z ∈ Uᶜ := hzU
      have h0 : Metric.infDist z Uᶜ = 0 := Metric.infDist_zero_of_mem hzc
      rw [h0] at hz2
      have : (0 : ℝ) < (1 : ℝ) / (n + 1) := by positivity
      linarith
    -- Monotone exhaustion.
    have hKset_mono : Monotone Kset := by
      intro m n hmn z hz
      refine ⟨?_, ?_⟩
      · exact Metric.closedBall_subset_closedBall (by exact_mod_cast hmn) hz.1
      · have hmn' : (1 : ℝ) / (n + 1) ≤ (1 : ℝ) / (m + 1) := by
          apply one_div_le_one_div_of_le
          · positivity
          · have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
            linarith
        exact le_trans hmn' hz.2
    -- `⋃ n, Kₙ = U`.
    have hKset_union : ⋃ n, Kset n = U := by
      apply subset_antisymm
      · exact iUnion_subset hKset_subU
      · intro z hzU
        have hUcl : IsClosed Uᶜ := hUopen.isClosed_compl
        have hzNotCompl : z ∉ Uᶜ := by simpa using hzU
        have hposdist : 0 < Metric.infDist z Uᶜ :=
          (hUcl.notMem_iff_infDist_pos hUcompl_ne).mp hzNotCompl
        -- Choose `n` with `dist z 0 ≤ n` and `1/(n+1) ≤ infDist z Uᶜ`.
        obtain ⟨n₁, hn₁⟩ := exists_nat_ge (dist z 0)
        obtain ⟨n₂, hn₂⟩ := exists_nat_gt ((1 : ℝ) / Metric.infDist z Uᶜ)
        refine mem_iUnion.mpr ⟨max n₁ n₂, ?_, ?_⟩
        · rw [Metric.mem_closedBall]
          exact le_trans hn₁ (by exact_mod_cast le_max_left n₁ n₂)
        · change (1 : ℝ) / ((max n₁ n₂ : ℕ) + 1) ≤ Metric.infDist z Uᶜ
          rw [div_le_iff₀ (by positivity)]
          rw [div_lt_iff₀ hposdist] at hn₂
          have hle : ((n₂ : ℝ)) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by exact_mod_cast le_max_right n₁ n₂
          nlinarith [Metric.infDist_nonneg (x := z) (s := Uᶜ)]
    -- Per-slice continuity from below for `μH[1]`.
    have hslice_sup : ∀ c : ℝ,
        μH[1] (u ⁻¹' {c} ∩ U) = ⨆ n, μH[1] (u ⁻¹' {c} ∩ Kset n) := by
      intro c
      have hmono : Monotone (fun n => u ⁻¹' {c} ∩ Kset n) := by
        intro m n hmn
        exact inter_subset_inter_right _ (hKset_mono hmn)
      have hunion : ⋃ n, u ⁻¹' {c} ∩ Kset n = u ⁻¹' {c} ∩ U := by
        rw [← inter_iUnion, hKset_union]
      rw [← hunion]
      exact hmono.measure_iUnion
    -- Each per-compact slice is measurable in `c`.
    have hmeas : ∀ n, Measurable (fun c => μH[1] (u ⁻¹' {c} ∩ Kset n)) :=
      fun n => measurable_slice_hausdorff_one hucont (hKset_compact n)
    -- Per-compact bound:  ∫ slice ≤ K * c₀ * ε.
    have hper : ∀ n, ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ Kset n) ≤ (K : ℝ≥0∞) * c₀ * ε := by
      intro n
      calc ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ Kset n)
          ≤ (K : ℝ≥0∞) * μH[2] (Kset n) :=
            eilenberg_coarea_planar_metric hu.lipschitzOnWith (hKset_compact n)
        _ ≤ (K : ℝ≥0∞) * μH[2] U := by
            gcongr (K : ℝ≥0∞) * ?_
            exact measure_mono (hKset_subU n)
        _ = (K : ℝ≥0∞) * c₀ * volume U := by
            rw [hc₀v]
            simp only [Measure.coe_nnreal_smul_apply]
            ring
        _ ≤ (K : ℝ≥0∞) * c₀ * ε := by gcongr
    -- Assemble: monotonicity to `U`, continuity from below, MCT, per-compact bound.
    calc ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A)
        ≤ ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ U) := by
          apply lintegral_mono
          intro c
          exact measure_mono (inter_subset_inter_right _ hAU)
      _ = ∫⁻ c, ⨆ n, μH[1] (u ⁻¹' {c} ∩ Kset n) := by
          simp_rw [hslice_sup]
      _ = ⨆ n, ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ Kset n) := by
          rw [lintegral_iSup hmeas]
          intro m n hmn c
          exact measure_mono (inter_subset_inter_right _ (hKset_mono hmn))
      _ ≤ (K : ℝ≥0∞) * c₀ * ε := iSup_le hper
  -- `≤ K c₀ ε` for all `ε > 0`  ⟹  `≤ 0`, by letting `ε → 0⁺`.
  have hlim : Tendsto (fun ε : ℝ≥0∞ => (K : ℝ≥0∞) * c₀ * ε) (𝓝[>] 0)
      (𝓝 ((K : ℝ≥0∞) * c₀ * 0)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact ENNReal.Tendsto.const_mul tendsto_id
      (Or.inr (by simp [ENNReal.mul_ne_top]))
  rw [mul_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε εpos
  rw [mem_Ioi] at εpos
  exact key ε εpos

/-- **Planar metric Eilenberg inequality for a measurable set (extends the compact-set version).**

For `u` that is `K`-Lipschitz on a measurable set `A ⊆ ℂ`,
`∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) ≤ (K : ℝ≥0∞) * μH[2] A`.

This drops the compactness hypothesis of `eilenberg_coarea_planar_metric`; it is the form the
area-formula assembly uses, where the Lusin pieces are measurable (not compact). It is the
absolute-continuity-style consequence of the compact version: by inner regularity write
`A = (⋃ₙ Kₙ) ∪ N` with `Kₙ` compact increasing and `volume N = 0`; the `N`-part contributes `0`
(`coarea_null_le`), and the `⋃ Kₙ` part is the monotone limit of the compact bounds
(`eilenberg_coarea_planar_metric` + `μH[2] (⋃ Kₙ) ≤ μH[2] A`). For `volume A = ∞` the right side is
`∞` (since `μH[2] = c₀ • volume` is infinite on a non-`volume`-finite set) and the bound is
trivial. -/
theorem eilenberg_coarea_planar_metric_meas {u : ℂ → ℝ} {K : ℝ≥0} {A : Set ℂ}
    (hu : LipschitzOnWith K u A) (hA : MeasurableSet A) :
    ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) ≤ (K : ℝ≥0∞) * μH[2] A := by
  classical
  -- Globalize: `g` is `K`-Lipschitz on all of `ℂ`, agreeing with `u` on `A`.
  obtain ⟨g, hgLip, hgEq⟩ := hu.extend_real
  have hgcont : Continuous g := hgLip.continuous
  -- On `A` the slices for `u` and `g` coincide, so we may work with `g`.
  have hslice_eq : ∀ c : ℝ, u ⁻¹' {c} ∩ A = g ⁻¹' {c} ∩ A := by
    intro c; ext z
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hz, hzA⟩; exact ⟨by rw [← hgEq hzA]; exact hz, hzA⟩
    · rintro ⟨hz, hzA⟩; exact ⟨by rw [hgEq hzA]; exact hz, hzA⟩
  rw [show (∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A)) = ∫⁻ c, μH[1] (g ⁻¹' {c} ∩ A) by
        apply lintegral_congr; intro c; rw [hslice_eq c]]
  -- The proportionality constant `μH[2] = c₀ • volume`.
  obtain ⟨c₀, hc₀pos, hc₀v⟩ := hausdorffMeasure_two_complex_smul_volume
  -- Case split on whether `A` has finite area.
  rcases eq_or_ne (volume A) ∞ with hAtop | hAfin
  · -- `volume A = ∞ ⟹ μH[2] A = c₀ • volume A = ∞`, RHS is `∞`, bound trivial.
    have hH2top : μH[2] A = ∞ := by
      rw [hc₀v, Measure.coe_nnreal_smul_apply, hAtop, ENNReal.mul_top]
      exact_mod_cast (pos_iff_ne_zero.mp hc₀pos)
    rw [hH2top]
    rcases eq_or_ne (K : ℝ≥0∞) 0 with hK0 | hKne
    · -- `K = 0`: then `g` is constant on `A`, and the integral is over a single point.
      rw [hK0, zero_mul]
      rw [ENNReal.coe_eq_zero] at hK0
      subst hK0
      rcases A.eq_empty_or_nonempty with hAe | ⟨z0, hz0⟩
      · simp [hAe]
      · have hconst : ∀ x ∈ A, u x = u z0 := fun x hx =>
          (LipschitzOnWith.zero_iff u).1 hu x hx z0 hz0
        have hsupp : (fun c => μH[1] (g ⁻¹' {c} ∩ A))
            = Set.indicator {u z0} (fun _ => μH[1] A) := by
          funext c
          by_cases hc : c = u z0
          · subst hc
            rw [indicator_of_mem (by simp)]
            congr 1
            rw [Set.inter_eq_right]
            intro x hx
            simp only [mem_preimage, mem_singleton_iff]
            rw [← hgEq hx]; exact hconst x hx
          · rw [indicator_of_notMem (by simp [hc])]
            have hemp : g ⁻¹' {c} ∩ A = ∅ := by
              rw [Set.eq_empty_iff_forall_notMem]
              rintro x ⟨hxc, hxA⟩
              simp only [mem_preimage, mem_singleton_iff] at hxc
              apply hc
              rw [← hxc, ← hgEq hxA, hconst x hxA]
            rw [hemp, measure_empty]
        rw [hsupp, lintegral_indicator (measurableSet_singleton _), setLIntegral_const,
          Real.volume_singleton, mul_zero]
    · rw [ENNReal.mul_top hKne]; exact le_top
  · -- Finite area: inner-regularity compact exhaustion.
    -- For each `n`, a compact `Kₙ ⊆ A` with `volume (A \ Kₙ) < 1/(n+1)`.
    have hAfin' : volume A ≠ ∞ := hAfin
    have hexc : ∀ n : ℕ, ∃ Q : Set ℂ, Q ⊆ A ∧ IsCompact Q ∧
        volume (A \ Q) < (1 : ℝ≥0∞) / (n + 1) := by
      intro n
      have hεne : ((1 : ℝ≥0∞) / (n + 1)) ≠ 0 := by
        rw [Ne, ENNReal.div_eq_zero_iff]
        rintro (h | h)
        · exact one_ne_zero h
        · exact (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩) h
      exact hA.exists_isCompact_sdiff_lt hAfin' hεne
    choose Q hQsub hQcomp hQdiff using hexc
    -- Monotone exhaustion `Kₙ := ⋃_{m ≤ n} Qₘ`.
    set Kset : ℕ → Set ℂ := fun n => ⋃ m ∈ Finset.range (n + 1), Q m with hKset_def
    have hKset_subA : ∀ n, Kset n ⊆ A := by
      intro n z hz
      simp only [hKset_def, mem_iUnion, Finset.mem_range] at hz
      obtain ⟨m, _, hzm⟩ := hz
      exact hQsub m hzm
    have hKset_compact : ∀ n, IsCompact (Kset n) := by
      intro n
      apply Finset.isCompact_biUnion
      intro m _; exact hQcomp m
    have hKset_mono : Monotone Kset := by
      intro p q hpq z hz
      simp only [hKset_def, mem_iUnion, Finset.mem_range] at hz ⊢
      obtain ⟨m, hm, hzm⟩ := hz
      exact ⟨m, lt_of_lt_of_le hm (by omega), hzm⟩
    -- `Qₙ ⊆ Kₙ`, so `A \ Kₙ ⊆ A \ Qₙ`.
    have hQsubK : ∀ n, Q n ⊆ Kset n := by
      intro n z hz
      simp only [hKset_def, mem_iUnion, Finset.mem_range]
      exact ⟨n, by omega, hz⟩
    set U : Set ℂ := ⋃ n, Kset n with hU_def
    have hUsubA : U ⊆ A := by
      rw [hU_def]; exact iUnion_subset hKset_subA
    have hUmeas : MeasurableSet U :=
      MeasurableSet.iUnion (fun n => (hKset_compact n).measurableSet)
    -- `N := A \ U` is measurable, `volume N = 0`, `N ⊆ A`.
    set N : Set ℂ := A \ U with hN_def
    have hNmeas : MeasurableSet N := hA.diff hUmeas
    have hNsubA : N ⊆ A := sdiff_subset
    have hN0 : volume N = 0 := by
      -- `volume N ≤ volume (A \ Kₙ) ≤ volume (A \ Qₙ) < 1/(n+1)` for all `n`.
      rw [← nonpos_iff_eq_zero]
      refine ENNReal.le_of_forall_pos_le_add ?_
      intro ε εpos _
      -- Choose `n` with `1/(n+1) ≤ ε`.
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (ε : ℝ))
      have hNle : volume N ≤ (1 : ℝ≥0∞) / (n + 1) := by
        have h1 : N ⊆ A \ Q n := by
          rw [hN_def]
          apply sdiff_subset_sdiff_right
          calc Q n ⊆ Kset n := hQsubK n
            _ ⊆ U := subset_iUnion Kset n
        calc volume N ≤ volume (A \ Q n) := measure_mono h1
          _ ≤ (1 : ℝ≥0∞) / (n + 1) := le_of_lt (hQdiff n)
      calc volume N ≤ (1 : ℝ≥0∞) / (n + 1) := hNle
        _ ≤ (ε : ℝ≥0∞) := by
            rw [ENNReal.div_le_iff (by simp) (by simp)]
            rw [div_lt_iff₀ (by exact_mod_cast εpos)] at hn
            rw [← ENNReal.coe_one, ← ENNReal.coe_natCast, ← ENNReal.coe_add, ← ENNReal.coe_mul,
              ENNReal.coe_le_coe]
            have : (1 : ℝ) < ε * (n + 1) := by nlinarith [εpos.le]
            exact_mod_cast this.le
        _ = 0 + (ε : ℝ≥0∞) := by rw [zero_add]
    -- `A ⊆ U ∪ N`.
    have hAsub : A ⊆ U ∪ N := by
      intro z hz
      by_cases hzU : z ∈ U
      · exact Or.inl hzU
      · exact Or.inr ⟨hz, hzU⟩
    -- Slice continuity from below for `μH[1]` on the monotone `Kₙ ↑ U`.
    have hslice_sup : ∀ c : ℝ,
        μH[1] (g ⁻¹' {c} ∩ U) = ⨆ n, μH[1] (g ⁻¹' {c} ∩ Kset n) := by
      intro c
      have hmono : Monotone (fun n => g ⁻¹' {c} ∩ Kset n) := by
        intro p q hpq
        exact inter_subset_inter_right _ (hKset_mono hpq)
      have hunion : ⋃ n, g ⁻¹' {c} ∩ Kset n = g ⁻¹' {c} ∩ U := by
        rw [← inter_iUnion, hU_def]
      rw [← hunion]
      exact hmono.measure_iUnion
    -- Each per-compact slice is measurable in `c`.
    have hmeas : ∀ n, Measurable (fun c => μH[1] (g ⁻¹' {c} ∩ Kset n)) :=
      fun n => measurable_slice_hausdorff_one hgcont (hKset_compact n)
    -- The `U`-slice function is measurable (monotone sup of measurables).
    have hUslice_meas : Measurable (fun c => μH[1] (g ⁻¹' {c} ∩ U)) := by
      have : (fun c => μH[1] (g ⁻¹' {c} ∩ U))
          = (fun c => ⨆ n, μH[1] (g ⁻¹' {c} ∩ Kset n)) := by
        funext c; exact hslice_sup c
      rw [this]
      exact Measurable.iSup hmeas
    -- `∫ over U`-part as the monotone sup of compact bounds.
    have hUbound : ∫⁻ c, μH[1] (g ⁻¹' {c} ∩ U) ≤ (K : ℝ≥0∞) * μH[2] A := by
      calc ∫⁻ c, μH[1] (g ⁻¹' {c} ∩ U)
          = ∫⁻ c, ⨆ n, μH[1] (g ⁻¹' {c} ∩ Kset n) := by
            simp_rw [hslice_sup]
        _ = ⨆ n, ∫⁻ c, μH[1] (g ⁻¹' {c} ∩ Kset n) := by
            rw [lintegral_iSup hmeas]
            intro p q hpq c
            exact measure_mono (inter_subset_inter_right _ (hKset_mono hpq))
        _ ≤ ⨆ n, (K : ℝ≥0∞) * μH[2] (Kset n) := by
            apply iSup_mono
            intro n
            exact eilenberg_coarea_planar_metric hgLip.lipschitzOnWith (hKset_compact n)
        _ = (K : ℝ≥0∞) * μH[2] U := by
            rw [← ENNReal.mul_iSup]
            congr 1
            rw [hU_def, hKset_mono.measure_iUnion]
        _ ≤ (K : ℝ≥0∞) * μH[2] A := by
            gcongr
    -- The `N`-part contributes `0`.
    have hNbound : ∫⁻ c, μH[1] (g ⁻¹' {c} ∩ N) = 0 :=
      coarea_null_le hgLip hNmeas hN0
    -- Combine: split `A ⊆ U ∪ N`.
    calc ∫⁻ c, μH[1] (g ⁻¹' {c} ∩ A)
        ≤ ∫⁻ c, (μH[1] (g ⁻¹' {c} ∩ U) + μH[1] (g ⁻¹' {c} ∩ N)) := by
          apply lintegral_mono
          intro c
          calc μH[1] (g ⁻¹' {c} ∩ A)
              ≤ μH[1] (g ⁻¹' {c} ∩ (U ∪ N)) := measure_mono (inter_subset_inter_right _ hAsub)
            _ = μH[1] ((g ⁻¹' {c} ∩ U) ∪ (g ⁻¹' {c} ∩ N)) := by rw [inter_union_distrib_left]
            _ ≤ μH[1] (g ⁻¹' {c} ∩ U) + μH[1] (g ⁻¹' {c} ∩ N) := measure_union_le _ _
      _ = (∫⁻ c, μH[1] (g ⁻¹' {c} ∩ U)) + ∫⁻ c, μH[1] (g ⁻¹' {c} ∩ N) := by
          rw [lintegral_add_left hUslice_meas]
      _ = ∫⁻ c, μH[1] (g ⁻¹' {c} ∩ U) := by rw [hNbound, add_zero]
      _ ≤ (K : ℝ≥0∞) * μH[2] A := hUbound

/-- **Almost every point of a measurable planar set is a point of unique differentiability.**

For a measurable `S ⊆ ℂ`, almost every `z ∈ S` satisfies `UniqueDiffWithinAt ℝ S z`.

This is the descriptive/measure-theoretic ingredient that lets a within-`S` derivative be identified
with the genuine `fderiv` a.e.: in `coarea_piece_le`, `u = Complex.re ∘ Ψ` holds only *on* `S`, so
the within-`S` derivative `Complex.reCLM ∘L Ψ'` equals the full `fderiv ℝ u` only at points of
unique differentiability of `S` — which, by this lemma, is a.e.

## Truth and proof

Almost every `z ∈ S` is a Lebesgue density-`1` point of `S`
(`Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet`).
At a density-`1` point the tangent cone `tangentConeAt ℝ S z` is all of `ℂ` (a positive-density set
approaches `z` from a dense set of directions), and `uniqueDiffWithinAt_iff` then gives
`UniqueDiffWithinAt ℝ S z`.

**Mathlib gap:** Mathlib has the density-`1` a.e. theorem and `uniqueDiffWithinAt_iff` (unique diff
`=` dense tangent-cone span), but **no bridge `density-1 ⟹ tangent-cone dense`** in dimension `≥ 2`
(the
existing density→`UniqueDiffWithinAt` route, `uniqueDiffWithinAt_iff_accPt`, is `1`-D
`NormedDivisionRing`-only). This bridge is the net-new content. -/
theorem ae_uniqueDiffWithinAt_of_measurableSet {S : Set ℂ} (hS : MeasurableSet S) :
    ∀ᵐ z ∂(volume.restrict S), UniqueDiffWithinAt ℝ S z := by
  classical
  -- Off-center Lebesgue density theorem with constant `K = 4`: a.e. point of `S`
  -- is a density point.
  have hdens := IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div
    (volume : Measure ℂ) S 4
  have hmemS : ∀ᵐ z ∂(volume.restrict S), z ∈ S := by
    rw [ae_restrict_iff' hS]; filter_upwards with z hz using hz
  filter_upwards [hdens, hmemS] with z hz hzS
  rw [uniqueDiffWithinAt_iff]
  refine ⟨?_, subset_closure hzS⟩
  -- Reduce dense-span to span = ⊤.
  suffices hspan : Submodule.span ℝ (tangentConeAt ℝ S z) = ⊤ by
    exact hspan ▸ (Submodule.top_coe (R := ℝ) (M := ℂ) ▸ dense_univ)
  -- KEY: for any unit direction `e`, the tangent cone contains a vector within `1/4` of `e`.
  have key : ∀ e : ℂ, ‖e‖ = 1 → ∃ y ∈ tangentConeAt ℝ S z, ‖y - e‖ ≤ 1/4 := by
    intro e he_norm
    -- Centres march toward `z` along `e` at distance `(n+1)⁻¹`; radii are `(n+1)⁻¹/4`.
    set w : ℕ → ℂ := fun n => z + ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * e with hw
    set δ : ℕ → ℝ := fun n => (((n : ℝ) + 1)⁻¹) / 4 with hδ
    have hδpos : ∀ n, 0 < δ n := by intro n; rw [hδ]; positivity
    have hδ0 : Tendsto δ atTop (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
          simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        simpa [hδ] using h1.div_const 4
      · filter_upwards with n using hδpos n
    have hdist : ∀ n, dist z (w n) = ((n : ℝ) + 1)⁻¹ := by
      intro n
      rw [hw, dist_eq_norm]
      have h0 : z - (z + (((((n : ℝ) + 1)⁻¹ : ℝ)) : ℂ) * e)
          = -((((((n : ℝ) + 1)⁻¹ : ℝ)) : ℂ) * e) := by ring
      rw [h0, norm_neg, norm_mul, Complex.norm_real, he_norm, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    -- `z` lies in the enlarged ball `closedBall (w n) (4 δ n)` since `dist z (w n) = 4 δ n`.
    have hzball : ∀ n, z ∈ Metric.closedBall (w n) (4 * δ n) := by
      intro n
      rw [Metric.mem_closedBall, hdist n, hδ]
      rw [show (4 : ℝ) * (((n : ℝ) + 1)⁻¹ / 4) = ((n : ℝ) + 1)⁻¹ by ring]
    have hratio := hz w δ hδ0 (Filter.Eventually.of_forall hzball)
    -- Density `→ 1` forces the intersection to be eventually nonempty.
    have hpos : ∀ᶠ n in atTop, (0 : ℝ≥0∞) <
        volume (S ∩ Metric.closedBall (w n) (δ n)) / volume (Metric.closedBall (w n) (δ n)) :=
      hratio.eventually (Ioi_mem_nhds (by norm_num))
    have hnonempty : ∀ᶠ n in atTop, (S ∩ Metric.closedBall (w n) (δ n)).Nonempty := by
      filter_upwards [hpos] with n hn
      apply nonempty_of_measure_ne_zero (μ := volume)
      intro hzero
      rw [hzero, ENNReal.zero_div] at hn
      exact lt_irrefl _ hn
    -- Pick a point `p n ∈ S` in the small ball (junk `z` off the eventual set).
    set p : ℕ → ℂ := fun n =>
      if h : (S ∩ Metric.closedBall (w n) (δ n)).Nonempty then h.choose else z with hp
    have hp_spec : ∀ᶠ n in atTop, p n ∈ S ∩ Metric.closedBall (w n) (δ n) := by
      filter_upwards [hnonempty] with n hn
      rw [hp]; simp only [hn, dif_pos]; exact hn.choose_spec
    set d : ℕ → ℂ := fun n => p n - z with hd
    have hp_specS : ∀ᶠ n in atTop, z + d n ∈ S := by
      filter_upwards [hp_spec] with n hn
      rw [hd]; simp only [add_sub_cancel]; exact hn.1
    -- The displacement `d n` is within `δ n` of `(n+1)⁻¹ e`.
    have hr_bound : ∀ᶠ n in atTop,
        ‖d n - ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * e‖ ≤ δ n := by
      filter_upwards [hp_spec] with n hn
      have hball : ‖p n - w n‖ ≤ δ n := by
        have := hn.2; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
      have heq : d n - ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * e = p n - w n := by rw [hd, hw]; ring
      rw [heq]; exact hball
    -- Rescale: `cseq n • d n` lives in `closedBall e (1/4)`, and `d n → 0`.
    set cseq : ℕ → ℝ := fun n => (n : ℝ) + 1 with hcseq
    set g : ℕ → ℂ := fun n => cseq n • d n with hg
    have hd0 : Tendsto d atTop (𝓝 0) := by
      have hbound : ∀ᶠ n in atTop, ‖d n‖ ≤ ((n : ℝ) + 1)⁻¹ + δ n := by
        filter_upwards [hr_bound] with n hn
        have htri : ‖d n‖ ≤ ‖d n - ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * e‖
            + ‖((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * e‖ := by
          have := norm_add_le (d n - ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * e)
            (((((n : ℝ) + 1)⁻¹ : ℝ)) * e)
          simpa using this
        have hnorm2 : ‖((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * e‖ = ((n : ℝ) + 1)⁻¹ := by
          rw [norm_mul, Complex.norm_real, he_norm, mul_one, Real.norm_eq_abs,
            abs_of_nonneg (by positivity)]
        rw [hnorm2] at htri; linarith [hn]
      have hto0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ + δ n) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
          simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        have h2 : Tendsto δ atTop (𝓝 0) := by rw [hδ]; simpa using h1.div_const 4
        simpa using h1.add h2
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _)) hbound hto0
    -- abstract algebraic bound: rescaling by `(n+1)` shrinks the `δ n`-error to `1/4`.
    have halg : ∀ (n : ℕ) (dn : ℂ),
        ‖dn - ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * e‖ ≤ δ n →
        ‖(((n : ℝ) + 1 : ℝ) : ℂ) * dn - e‖ ≤ 1/4 := by
      intro n dn hbnd
      have hfact : (((n : ℝ) + 1 : ℝ) : ℂ) * dn - e
          = (((n : ℝ) + 1 : ℝ) : ℂ) * (dn - ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * e) := by
        rw [mul_sub]; congr 1
        rw [← mul_assoc, ← Complex.ofReal_mul,
          mul_inv_cancel₀ (by positivity : ((n : ℝ) + 1) ≠ 0)]
        simp
      rw [hfact, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ((n : ℝ) + 1) * ‖dn - ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * e‖
          ≤ ((n : ℝ) + 1) * δ n := mul_le_mul_of_nonneg_left hbnd (by positivity)
        _ = 1/4 := by rw [hδ]; field_simp
    have hg_ball : ∀ᶠ n in atTop, g n ∈ Metric.closedBall e (1/4) := by
      filter_upwards [hr_bound] with n hn
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hgn : g n = (((n : ℝ) + 1 : ℝ) : ℂ) * d n := by
        rw [hg]; simp only [hcseq]; exact Complex.real_smul ..
      rw [hgn]
      exact halg n (d n) hn
    -- Bolzano-Weierstrass: extract a convergent subsequence of `g`.
    -- `g` lies in the compact ball `closedBall e (1/4)` for all `n ≥ N`; shift and extract.
    rw [eventually_atTop] at hg_ball
    obtain ⟨N, hN⟩ := hg_ball
    have hmemN : ∀ n, g (n + N) ∈ Metric.closedBall e (1/4) := fun n => hN (n + N) (by omega)
    obtain ⟨y, hy_ball, ψ, hψ_mono, hψ_tendsto⟩ :=
      (isCompact_closedBall e (1/4)).tendsto_subseq hmemN
    -- the composite index `ρ n = ψ n + N` is strictly monotone.
    set ρ : ℕ → ℕ := fun n => ψ n + N with hρ
    have hρ_mono : StrictMono ρ := fun a b hab => Nat.add_lt_add_right (hψ_mono hab) N
    refine ⟨y, ?_, ?_⟩
    · refine mem_tangentConeAt_of_seq atTop (cseq ∘ ρ) (d ∘ ρ) ?_ ?_ ?_
      · exact hd0.comp hρ_mono.tendsto_atTop
      · exact hρ_mono.tendsto_atTop.eventually hp_specS
      · have hgeq : (fun n => (cseq ∘ ρ) n • (d ∘ ρ) n) = fun n => g (ψ n + N) := by
          funext n; rw [hg]; rfl
        rw [hgeq]; exact hψ_tendsto
    · rw [Metric.mem_closedBall, dist_eq_norm] at hy_ball; exact hy_ball
  -- Apply `key` to directions `1` and `I`; the two near-orthogonal vectors span `ℂ` over `ℝ`.
  obtain ⟨y1, hy1, hb1⟩ := key 1 (by simp)
  obtain ⟨y2, hy2, hb2⟩ := key Complex.I (by simp)
  set T := tangentConeAt ℝ S z with hT
  -- coordinate bounds from the `1/4` norm estimates
  have hre1 : |y1.re - 1| ≤ 1/4 := by
    have : |(y1 - 1).re| ≤ ‖y1 - 1‖ := Complex.abs_re_le_norm _
    simpa using this.trans hb1
  have him1 : |y1.im| ≤ 1/4 := by
    have : |(y1 - 1).im| ≤ ‖y1 - 1‖ := Complex.abs_im_le_norm _
    simpa using this.trans hb1
  have hre2 : |y2.re| ≤ 1/4 := by
    have : |(y2 - Complex.I).re| ≤ ‖y2 - Complex.I‖ := Complex.abs_re_le_norm _
    simpa using this.trans hb2
  have him2 : |y2.im - 1| ≤ 1/4 := by
    have : |(y2 - Complex.I).im| ≤ ‖y2 - Complex.I‖ := Complex.abs_im_le_norm _
    simpa using this.trans hb2
  have hy1re : (3:ℝ)/4 ≤ y1.re := by rw [abs_le] at hre1; linarith [hre1.1]
  have hy2im : (3:ℝ)/4 ≤ y2.im := by rw [abs_le] at him2; linarith [him2.1]
  have hy1ne : y1 ≠ 0 := by
    intro h; rw [h] at hy1re; simp at hy1re; linarith
  -- linear independence of `![y1, y2]`
  have hli : LinearIndependent ℝ ![y1, y2] := by
    rw [LinearIndependent.pair_iff' hy1ne]
    intro a hcontra
    have h2 : (a : ℂ) * y1 = y2 := by rw [← Complex.real_smul]; exact hcontra
    have hre : a * y1.re = y2.re := by
      have h := congrArg Complex.re h2; simpa using h
    have him : a * y1.im = y2.im := by
      have h := congrArg Complex.im h2; simpa using h
    have ha_bound : |a| ≤ 1/3 := by
      have hare : |a| * y1.re = |y2.re| := by
        rw [← abs_of_pos (by linarith : (0:ℝ) < y1.re), ← abs_mul, hre]
      nlinarith [abs_nonneg a, hre2, hy1re, hare]
    have hkey : a * y1.im ≤ 1/12 := by
      have hbnd : |a * y1.im| ≤ 1/12 := by
        calc |a * y1.im| = |a| * |y1.im| := abs_mul a y1.im
          _ ≤ (1/3) * (1/4) := mul_le_mul ha_bound him1 (abs_nonneg _) (by norm_num)
          _ = 1/12 := by norm_num
      linarith [(abs_le.mp hbnd).2]
    rw [him] at hkey; linarith
  -- two independent vectors span the 2-dimensional `ℝ`-space `ℂ`.
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ ℂ := by
    rw [Complex.finrank_real_complex]; rfl
  have hsp := hli.span_eq_top_of_card_eq_finrank hcard
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty] at hsp
  apply top_unique
  rw [← hsp]
  apply Submodule.span_mono
  intro x hx
  simp only [Set.union_empty, Set.union_singleton, Set.mem_insert_iff] at hx
  rcases hx with h | h
  · rw [h]; exact hy2
  · simp only [Set.mem_singleton_iff] at h; rw [h]; exact hy1

/-- **Per-piece sharp co-area bound (the IFT-free area-formula core).**

On a Lusin piece `S` where the square map `Ψ : ℂ → ℂ` (with `Ψ.re = u`) is approximately the linear
isomorphism `A` (so `Ψ` is bi-Lipschitz and `Set.InjOn` on `S`), the integrated level-set length of
`u` over `S` is bounded by the gradient integral:

`∫⁻ c, μH[1] (u ⁻¹' {c} ∩ S) ≤ ∫⁻ z in S, ‖fderiv ℝ u z‖₊`.

This is the genuine core of the area-formula proof of the sharp co-area inequality. It is proved
**without the inverse function theorem** (which is unavailable for a merely differentiable `Ψ`):

* `ApproximatesLinearOn Ψ A S δ` with `δ < ‖A.symm‖₊⁻¹` makes `Ψ` `Set.InjOn S`
  (`ApproximatesLinearOn.injOn`) and **bi-Lipschitz** on `S`, so `Ψ⁻¹` is Lipschitz — so the level
  curve `u ⁻¹' {c} ∩ S = Ψ⁻¹ '' (Ψ '' S ∩ {w | w.re = c})` is a **Lipschitz** image of a segment,
  differentiable a.e. (Rademacher), with NO `C¹` / IFT hypothesis.
* The proven fiber-arc-length bound `hausdorffMeasure_one_image_le` (applied on the a.e.-diff subset
  of the segment; the Lipschitz image of the remaining null set is `μH[1]`-null) gives
  `μH[1] (u ⁻¹' {c} ∩ S) ≤ ∫⁻ s, ‖∂_im Ψ⁻¹ (c + s·I)‖`.
* Fubini in `(c, s)` over `Ψ '' S` and the area formula
  `lintegral_image_eq_lintegral_abs_det_fderiv_mul` for the InjOn differentiable `Ψ` convert this to
  `∫⁻ z in S, ‖(Ψ' z)⁻¹ · I‖ · |det (Ψ' z)|`, and the pointwise linear-algebra identity
  `‖(Ψ' z)⁻¹ · I‖ · |det (Ψ' z)| = ‖fderiv ℝ u z‖` (independent of the second coordinate `ℓ`;
  `fderiv ℝ u = Complex.re ∘ Ψ'`) finishes. -/
theorem coarea_piece_le {u : ℂ → ℝ} {Ψ : ℂ → ℂ} {Ψ' : ℂ → (ℂ →L[ℝ] ℂ)}
    {A : ℂ ≃L[ℝ] ℂ} {S : Set ℂ} {δ : ℝ≥0}
    (hS : MeasurableSet S) (_hSb : Bornology.IsBounded S)
    (hδ : δ < ‖(A.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹)
    (hALO : ApproximatesLinearOn Ψ (A : ℂ →L[ℝ] ℂ) S δ)
    (hΨ' : ∀ z ∈ S, HasFDerivWithinAt Ψ (Ψ' z) S z)
    (hre : ∀ z ∈ S, (Ψ z).re = u z)
    (hdiff : ∀ z ∈ S, DifferentiableAt ℝ u z) :
    ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ S) ≤ ∫⁻ z in S, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
  classical
  -- =================================================================
  -- (1)  Basic structure of `Ψ` and its inverse `g` on `T = Ψ '' S`.
  -- =================================================================
  have hinj : InjOn Ψ S := hALO.injOn (Or.inr hδ)
  set g : ℂ → ℂ := Function.invFunOn Ψ S with hg
  set T : Set ℂ := Ψ '' S with hT
  have hleft : ∀ z ∈ S, g (Ψ z) = z := fun z hz => hinj.leftInvOn_invFunOn hz
  have hright : ∀ w ∈ T, Ψ (g w) = w := by
    intro w hw; obtain ⟨z, hz, rfl⟩ := hw; rw [hleft z hz]
  have hgmem : ∀ w ∈ T, g w ∈ S := by
    intro w hw; obtain ⟨z, hz, rfl⟩ := hw; rw [hleft z hz]; exact hz
  have hgLip : LipschitzOnWith ((‖(A.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ - δ)⁻¹) g T := by
    rw [lipschitzOnWith_iff_restrict]
    exact (hALO.antilipschitz (Or.inr hδ)).to_rightInvOn'
      (fun w hw => hgmem w hw) (fun w hw => hright w hw)
  have hgCont : ContinuousOn g T := hgLip.continuousOn
  have hTmeas : MeasurableSet T := measurable_image_of_fderivWithin hS hΨ' hinj
  -- =================================================================
  -- (2)  `det (Ψ' z) ≠ 0` a.e. on `S` (small perturbation of `A`).
  -- =================================================================
  have hAne : ‖(A.symm : ℂ →L[ℝ] ℂ)‖₊ ≠ 0 := by
    intro h0; rw [h0, inv_zero] at hδ; exact absurd hδ (not_lt.mpr (zero_le))
  have hApos : (0 : ℝ≥0) < ‖(A.symm : ℂ →L[ℝ] ℂ)‖₊ := pos_of_ne_zero hAne
  -- the perturbation lemma: ‖T₀ - A‖ ≤ δ ⟹ T₀.det ≠ 0
  have hdet_of_close : ∀ T₀ : ℂ →L[ℝ] ℂ, ‖T₀ - (A : ℂ →L[ℝ] ℂ)‖₊ ≤ δ → T₀.det ≠ 0 := by
    intro T₀ hT₀
    have hinjT : Function.Injective (T₀ : ℂ →ₗ[ℝ] ℂ) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      by_contra hvne
      have hvpos : (0 : ℝ≥0) < ‖v‖₊ := by rwa [nnnorm_pos]
      have hAv : ‖(A.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ * ‖v‖₊ ≤ ‖(A : ℂ →L[ℝ] ℂ) v‖₊ := by
        have hb := (A : ℂ →L[ℝ] ℂ).bound_of_antilipschitz A.antilipschitz v
        rw [← NNReal.coe_le_coe]; push_cast
        rw [inv_mul_le_iff₀ (by exact_mod_cast hApos)]
        rw [coe_nnnorm] at hb; exact hb
      have hTAv : ‖(T₀ - (A : ℂ →L[ℝ] ℂ)) v‖₊ ≤ δ * ‖v‖₊ := by
        calc ‖(T₀ - (A : ℂ →L[ℝ] ℂ)) v‖₊ ≤ ‖T₀ - (A : ℂ →L[ℝ] ℂ)‖₊ * ‖v‖₊ :=
              (T₀ - (A : ℂ →L[ℝ] ℂ)).le_opNNNorm v
          _ ≤ δ * ‖v‖₊ := by gcongr
      have hTeq : T₀ v = (A : ℂ →L[ℝ] ℂ) v + (T₀ - (A : ℂ →L[ℝ] ℂ)) v := by
        rw [sub_apply]; ring
      have hTv0 : (A : ℂ →L[ℝ] ℂ) v + (T₀ - (A : ℂ →L[ℝ] ℂ)) v = 0 := by rw [← hTeq]; exact hv
      have hAvnorm : ‖(A : ℂ →L[ℝ] ℂ) v‖₊ = ‖(T₀ - (A : ℂ →L[ℝ] ℂ)) v‖₊ := by
        rw [eq_neg_of_add_eq_zero_left hTv0, nnnorm_neg]
      have hchain : ‖(A.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ * ‖v‖₊ ≤ δ * ‖v‖₊ :=
        le_trans hAv (le_trans (le_of_eq hAvnorm) hTAv)
      exact absurd (lt_of_le_of_lt (le_of_mul_le_mul_right hchain hvpos) hδ) (lt_irrefl _)
    intro hdet0
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet0) (LinearMap.ker_eq_bot.mpr hinjT)
  have hdet_ne : ∀ᵐ z ∂(volume.restrict S), (Ψ' z).det ≠ 0 := by
    filter_upwards [hALO.norm_fderiv_sub_le volume hS Ψ' hΨ'] with z hz
    exact hdet_of_close (Ψ' z) hz
  -- =================================================================
  -- (3)  The inverse derivative `Dg` and the weight `Φ`.
  -- =================================================================
  set Dg : ℂ → (ℂ →L[ℝ] ℂ) := fun w =>
    if h : (Ψ' (g w)).det ≠ 0 then
      (((Ψ' (g w)).toContinuousLinearEquivOfDetNeZero h).symm : ℂ →L[ℝ] ℂ) else 0 with hDg
  set Φ : ℂ → ℝ≥0∞ := fun w => (‖Dg w Complex.I‖₊ : ℝ≥0∞) with hΦ
  have hinvderiv : ∀ z ∈ S, (h : (Ψ' z).det ≠ 0) →
      HasFDerivWithinAt g
        (((Ψ' z).toContinuousLinearEquivOfDetNeZero h).symm : ℂ →L[ℝ] ℂ) T (Ψ z) := by
    intro z hz h
    have hgΨz : g (Ψ z) = z := hleft z hz
    have hfd : HasFDerivWithinAt Ψ
        (((Ψ' z).toContinuousLinearEquivOfDetNeZero h) : ℂ →L[ℝ] ℂ) S (g (Ψ z)) := by
      rw [hgΨz, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]; exact hΨ' z hz
    have htend : Filter.Tendsto g (𝓝[T] (Ψ z)) (𝓝[S] (g (Ψ z))) :=
      (hgCont _ ⟨z, hz, rfl⟩).tendsto_nhdsWithin (fun w hw => hgmem w hw)
    have hev : ∀ᶠ y in 𝓝[T] (Ψ z), Ψ (g y) = y := by
      filter_upwards [self_mem_nhdsWithin] with y hy using hright y hy
    exact HasFDerivWithinAt.of_local_left_inverse htend hfd ⟨z, hz, rfl⟩ hev
  -- =================================================================
  -- (4)  The pointwise linear-algebra identity (`LA identity`):
  --      `ofReal |T₀.det| * ‖(T₀)⁻¹ I‖ = ‖reCLM ∘ T₀‖`  for invertible `T₀`.
  -- =================================================================
  have hLA : ∀ (T₀ : ℂ →L[ℝ] ℂ) (h : T₀.det ≠ 0),
      ENNReal.ofReal |T₀.det| *
          (‖((T₀.toContinuousLinearEquivOfDetNeZero h).symm : ℂ →L[ℝ] ℂ) Complex.I‖₊ : ℝ≥0∞)
        = (‖Complex.reCLM.comp T₀‖₊ : ℝ≥0∞) := by
    intro T₀ h
    set Te := T₀.toContinuousLinearEquivOfDetNeZero h with hTe
    set w : ℂ := (Te.symm : ℂ →L[ℝ] ℂ) Complex.I with hw
    have hTw : T₀ w = Complex.I := by
      have : (Te : ℂ →L[ℝ] ℂ) w = Complex.I := by
        rw [hw]; exact Te.apply_symm_apply Complex.I
      rwa [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] at this
    set a := (T₀ 1).re with ha
    set b := (T₀ 1).im with hb
    set cc := (T₀ Complex.I).re with hcc
    set d := (T₀ Complex.I).im with hd
    have hdet : T₀.det = a * d - cc * b := by
      rw [show T₀.det = LinearMap.det (T₀ : ℂ →ₗ[ℝ] ℂ) from rfl,
        show LinearMap.det (T₀ : ℂ →ₗ[ℝ] ℂ)
          = Matrix.det (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
              (T₀ : ℂ →ₗ[ℝ] ℂ)) from (LinearMap.det_toMatrix Complex.basisOneI _).symm]
      rw [Matrix.det_fin_two]
      simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      rfl
    have hdecomp : T₀ w = w.re • (T₀ 1) + w.im • (T₀ Complex.I) := by
      have hwd : w = w.re • (1 : ℂ) + w.im • Complex.I := by
        apply Complex.ext <;> simp [Complex.real_smul]
      conv_lhs => rw [hwd]
      rw [map_add, map_smul, map_smul]
    have hre_eq : a * w.re + cc * w.im = 0 := by
      have h1 := congrArg Complex.re hTw
      rw [hdecomp] at h1
      simp only [Complex.add_re, Complex.smul_re, Complex.I_re, smul_eq_mul] at h1
      simp only [ha, hcc]; nlinarith [h1]
    have him_eq : b * w.re + d * w.im = 1 := by
      have h1 := congrArg Complex.im hTw
      rw [hdecomp] at h1
      simp only [Complex.add_im, Complex.smul_im, Complex.I_im, smul_eq_mul] at h1
      simp only [hb, hd]; nlinarith [h1]
    have hdetre : T₀.det * w.re = -cc := by
      rw [hdet]; linear_combination d * hre_eq - cc * him_eq
    have hdetim : T₀.det * w.im = a := by
      rw [hdet]; linear_combination (-b) * hre_eq + a * him_eq
    have hLval : ‖Complex.reCLM.comp T₀‖ = Real.sqrt (a ^ 2 + cc ^ 2) := by
      set L : ℂ →L[ℝ] ℝ := Complex.reCLM.comp T₀ with hL
      set v := (InnerProductSpace.toDual ℝ ℂ).symm L with hv
      have hLnorm : ‖v‖ = ‖L‖ := LinearIsometryEquiv.norm_map _ _
      have hriesz : ∀ z : ℂ, L z = inner ℝ v z := fun z => by
        rw [hv]; exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)).symm
      have hL1 : L 1 = a := by simp [hL, Complex.reCLM_apply, ha]
      have hLI : L Complex.I = cc := by simp [hL, Complex.reCLM_apply, hcc]
      have hvre : v.re = a := by
        have hh := (hriesz 1).symm; rw [hL1, Complex.inner] at hh; simpa using hh
      have hvim : v.im = cc := by
        have hh := (hriesz Complex.I).symm; rw [hLI, Complex.inner] at hh
        rw [Complex.mul_re] at hh; simp [Complex.conj_re, Complex.conj_im] at hh; linarith [hh]
      rw [← hLnorm, Complex.norm_eq_sqrt_sq_add_sq, hvre, hvim]
    have hprod : |T₀.det| * ‖w‖ = Real.sqrt (a ^ 2 + cc ^ 2) := by
      rw [Complex.norm_eq_sqrt_sq_add_sq w, ← Real.sqrt_sq (abs_nonneg T₀.det),
        ← Real.sqrt_mul (by positivity)]
      congr 1
      rw [sq_abs]
      have e1 : (T₀.det * w.re) ^ 2 = cc ^ 2 := by rw [hdetre, neg_pow, neg_one_sq, one_mul]
      have e2 : (T₀.det * w.im) ^ 2 = a ^ 2 := by rw [hdetim]
      nlinarith [e1, e2]
    have hwnn : ((‖(Te.symm : ℂ →L[ℝ] ℂ) Complex.I‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖w‖ := by
      rw [← hw, ← enorm_eq_nnnorm, ← ofReal_norm]
    have hLnn : ((‖Complex.reCLM.comp T₀‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖Complex.reCLM.comp T₀‖ := by
      rw [← enorm_eq_nnnorm, ← ofReal_norm]
    change ENNReal.ofReal |T₀.det| * ((‖(Te.symm : ℂ →L[ℝ] ℂ) Complex.I‖₊ : ℝ≥0∞))
        = ((‖Complex.reCLM.comp T₀‖₊ : ℝ≥0∞))
    rw [hwnn, hLnn, ← ENNReal.ofReal_mul (abs_nonneg _), hprod, hLval]
  -- =================================================================
  -- (5)  a.e. on `S`:  `fderiv ℝ u z = reCLM ∘ Ψ' z`  (unique-diff points).
  -- =================================================================
  have hfderiv_eq : ∀ᵐ z ∂(volume.restrict S), fderiv ℝ u z = Complex.reCLM.comp (Ψ' z) := by
    filter_upwards [ae_uniqueDiffWithinAt_of_measurableSet hS,
      (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall (fun z hz => hz))]
      with z hud hz
    have h1 : HasFDerivWithinAt (fun w => (Ψ w).re) (Complex.reCLM.comp (Ψ' z)) S z :=
      Complex.reCLM.hasFDerivAt.comp_hasFDerivWithinAt z (hΨ' z hz)
    have h2 : HasFDerivWithinAt u (Complex.reCLM.comp (Ψ' z)) S z :=
      h1.congr (fun w hw => (hre w hw).symm) (hre z hz).symm
    rw [← (hdiff z hz).fderivWithin hud, h2.fderivWithin hud]
  -- =================================================================
  -- (6)  AE-measurability of `Φ` on `T` (via the measurable embedding `Ψ|S`).
  -- =================================================================
  -- `Ψ'` is a.e.-measurable on `S`.
  have hΨ'meas : AEMeasurable Ψ' (volume.restrict S) := aemeasurable_fderivWithin volume hS hΨ'
  -- on `S`, a.e., `Φ (Ψ z) = ‖reCLM ∘ Ψ' z‖₊ / ofReal |det (Ψ' z)|`.
  have hΦΨ : ∀ᵐ z ∂(volume.restrict S),
      Φ (Ψ z) = (‖Complex.reCLM.comp (Ψ' z)‖₊ : ℝ≥0∞) / ENNReal.ofReal |(Ψ' z).det| := by
    filter_upwards [hdet_ne, (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall (fun z hz => hz))]
      with z hdetz hz
    have hgΨ : g (Ψ z) = z := hleft z hz
    have hDgΨ : Dg (Ψ z) =
        (((Ψ' z).toContinuousLinearEquivOfDetNeZero hdetz).symm : ℂ →L[ℝ] ℂ) := by
      rw [hDg]
      simp only [hgΨ]
      exact dif_pos hdetz
    have hΦval : Φ (Ψ z) =
        (‖(((Ψ' z).toContinuousLinearEquivOfDetNeZero hdetz).symm : ℂ →L[ℝ] ℂ)
            Complex.I‖₊ : ℝ≥0∞) := by
      rw [hΦ]; simp only [hDgΨ]
    rw [hΦval]
    have hdtop : ENNReal.ofReal |(Ψ' z).det| ≠ ⊤ := ENNReal.ofReal_ne_top
    have hd0 : ENNReal.ofReal |(Ψ' z).det| ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le, abs_pos]; exact hdetz
    rw [ENNReal.eq_div_iff hd0 hdtop]
    exact hLA (Ψ' z) hdetz
  -- `‖reCLM ∘ Ψ' ·‖₊ / ofReal |det Ψ' ·|` is a.e.-measurable on `S`.
  have hmeas_aux : AEMeasurable
      (fun z => (‖Complex.reCLM.comp (Ψ' z)‖₊ : ℝ≥0∞) / ENNReal.ofReal |(Ψ' z).det|)
      (volume.restrict S) := by
    have hcompcont : Continuous (fun M : ℂ →L[ℝ] ℂ => Complex.reCLM.comp M) := by
      have := (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.reCLM).continuous
      simpa only [ContinuousLinearMap.compL_apply] using! this
    have hc1 : AEMeasurable (fun z => (‖Complex.reCLM.comp (Ψ' z)‖₊ : ℝ≥0∞))
        (volume.restrict S) := by
      apply measurable_coe_nnreal_ennreal.comp_aemeasurable
      exact (continuous_nnnorm.comp hcompcont).measurable.comp_aemeasurable hΨ'meas
    have hc2 : AEMeasurable (fun z => ENNReal.ofReal |(Ψ' z).det|) (volume.restrict S) :=
      aemeasurable_ofReal_abs_det_fderivWithin volume hS hΨ'
    exact hc1.div hc2
  have hΦΨ_meas : AEMeasurable (fun z => Φ (Ψ z)) (volume.restrict S) :=
    hmeas_aux.congr (hΦΨ.mono (fun z hz => hz.symm))
  -- `Ψ` differentiable on `S`, hence images of null subsets are null.
  have hΨdiffOn : DifferentiableOn ℝ Ψ S := fun z hz => (hΨ' z hz).differentiableWithinAt
  -- `g` pushes `volume.restrict T` absolutely continuously onto `volume.restrict S`.
  have hgAC : (Measure.map g (volume.restrict T)) ≪ (volume.restrict S) := by
    have hgaem : AEMeasurable g (volume.restrict T) := hgCont.aemeasurable hTmeas
    refine Measure.AbsolutelyContinuous.mk fun N hN hN0 => ?_
    -- volume (N ∩ S) = 0 ⟹ map g (restrict T) N = 0
    rw [Measure.restrict_apply hN] at hN0
    rw [Measure.map_apply_of_aemeasurable hgaem hN]
    -- g ⁻¹' N ∩ T ⊆ Ψ '' (N ∩ S)
    have hsub : g ⁻¹' N ∩ T ⊆ Ψ '' (N ∩ S) := by
      rintro w ⟨hwN, hwT⟩
      exact ⟨g w, ⟨hwN, hgmem w hwT⟩, hright w hwT⟩
    have himg0 : volume (Ψ '' (N ∩ S)) = 0 :=
      addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
        (hΨdiffOn.mono inter_subset_right) hN0
    rw [Measure.restrict_apply' hTmeas]
    exact measure_mono_null hsub himg0
  -- transfer:  `Φ = (Φ ∘ Ψ) ∘ g` on `T`,  AEMeasurable via the change-of-variables.
  have hΦ_meas : AEMeasurable Φ (volume.restrict T) := by
    have hgaem : AEMeasurable g (volume.restrict T) := hgCont.aemeasurable hTmeas
    have hcomp : AEMeasurable (fun w => Φ (Ψ (g w))) (volume.restrict T) :=
      (hΦΨ_meas.mono' hgAC).comp_aemeasurable hgaem
    refine hcomp.congr ?_
    filter_upwards [(ae_restrict_iff' hTmeas).2 (Filter.Eventually.of_forall (fun w hw => hw))]
      with w hw
    rw [hright w hw]
  -- =================================================================
  -- (7)  STEP A:  `∫⁻ c, μH[1] (u⁻¹{c} ∩ S) ≤ ∫⁻ w in T, Φ w`.
  -- =================================================================
  -- A measurable null superset (within `S`) of the degenerate set, and its null image.
  obtain ⟨Z, hZsub, hZmeas, hZ0⟩ :
      ∃ Z : Set ℂ, ({z | ¬ (Ψ' z).det ≠ 0} ∩ S) ⊆ Z ∧ MeasurableSet Z ∧ volume Z = 0 := by
    have hh : volume.restrict S {z | ¬ (Ψ' z).det ≠ 0} = 0 := hdet_ne
    rw [Measure.restrict_apply₀' hS.nullMeasurableSet] at hh
    exact exists_measurable_superset_of_null hh
  -- `Ψ '' (Z ∩ S)` is `volume`-null.
  have hΨZ0 : volume (Ψ '' (Z ∩ S)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (hΨdiffOn.mono inter_subset_right)
      (measure_mono_null inter_subset_left hZ0)
  -- a.e. `c`, the slice `{s | mk c s ∈ Ψ '' (Z ∩ S)}` is `volume`-null.
  set W : Set ℂ := Ψ '' (Z ∩ S) with hW
  have hslicenull : ∀ᵐ c : ℝ, volume {s : ℝ | Complex.mk c s ∈ W} = 0 := by
    -- transport nullity to `ℝ × ℝ` via `measurableEquivRealProd.symm`.
    set P : Set (ℝ × ℝ) := Complex.measurableEquivRealProd.symm ⁻¹' W with hP
    have hpre : (volume : Measure (ℝ × ℝ)) P = 0 := by
      rw [hP, (Complex.volume_preserving_equiv_real_prod.symm _).measure_preimage
        (NullMeasurableSet.of_null hΨZ0)]
      exact hΨZ0
    have hprod0 : ((volume : Measure ℝ).prod (volume : Measure ℝ)) P = 0 := by
      rw [← Measure.volume_eq_prod]; exact hpre
    have hslice := MeasureTheory.Measure.measure_ae_null_of_prod_null hprod0
    filter_upwards [hslice] with c hc
    have hseteq : {s : ℝ | Complex.mk c s ∈ W} = Prod.mk c ⁻¹' P := by
      ext s
      simp only [hP, Set.mem_preimage, Complex.measurableEquivRealProd_symm_apply, mem_ofPred_eq]
    rw [hseteq]; exact hc
  -- The line map `s ↦ mk c s` and its derivative `I`.
  have hline : ∀ (c s : ℝ), HasDerivWithinAt (fun t : ℝ => Complex.mk c t) Complex.I
      {t : ℝ | Complex.mk c t ∈ T} s := by
    intro c s
    have hHA : HasDerivAt (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) Complex.I s := by
      have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) (1 * Complex.I) s :=
        (Complex.ofRealCLM.hasDerivAt).mul_const Complex.I
      have h3 := (h2.const_add (c : ℂ)); rwa [one_mul] at h3
    have hEq : (fun t : ℝ => Complex.mk c t)
        = (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) := by
      funext t; rw [Complex.mk_eq_add_mul_I]
    rw [hEq]; exact hHA.hasDerivWithinAt
  -- the fiber slice curve and its derivative at good points.
  have hslicederiv : ∀ (c s : ℝ), Complex.mk c s ∈ T →
      (Ψ' (g (Complex.mk c s))).det ≠ 0 →
      HasDerivWithinAt (fun t : ℝ => g (Complex.mk c t)) (Dg (Complex.mk c s) Complex.I)
        {t : ℝ | Complex.mk c t ∈ T} s := by
    intro c s hsT hdetne
    obtain ⟨z, hz, hzeq⟩ := hsT
    have hgw : g (Complex.mk c s) ∈ S := hgmem _ ⟨z, hz, hzeq⟩
    have hDgval : Dg (Complex.mk c s)
        = (((Ψ' (g (Complex.mk c s))).toContinuousLinearEquivOfDetNeZero hdetne).symm
            : ℂ →L[ℝ] ℂ) := by rw [hDg]; exact dif_pos hdetne
    have hgfd : HasFDerivWithinAt g (Dg (Complex.mk c s)) T (Complex.mk c s) := by
      rw [hDgval]
      have := hinvderiv (g (Complex.mk c s)) hgw hdetne
      rwa [hright _ ⟨z, hz, hzeq⟩] at this
    exact hgfd.comp_hasDerivWithinAt s (hline c s) (fun t ht => ht)
  -- the fiber slice curve is Lipschitz on `T_c`.
  have hlineLip : ∀ c : ℝ, LipschitzOnWith 1 (fun t : ℝ => Complex.mk c t)
      {t : ℝ | Complex.mk c t ∈ T} := by
    intro c
    apply LipschitzWith.lipschitzOnWith
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simp only [Complex.dist_eq, Complex.mk_eq_add_mul_I, NNReal.coe_one, one_mul]
    rw [show (c : ℂ) + (x : ℂ) * Complex.I - ((c : ℂ) + (y : ℂ) * Complex.I)
        = ((x : ℂ) - (y : ℂ)) * Complex.I by ring, norm_mul, Complex.norm_I, mul_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.dist_eq, Real.norm_eq_abs]
  have hsliceLip : ∀ c : ℝ, LipschitzOnWith ((‖(A.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ - δ)⁻¹)
      (fun t : ℝ => g (Complex.mk c t)) {t : ℝ | Complex.mk c t ∈ T} := by
    intro c
    have hcomp : LipschitzOnWith ((‖(A.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ - δ)⁻¹ * 1)
        (g ∘ (fun t : ℝ => Complex.mk c t)) {t : ℝ | Complex.mk c t ∈ T} :=
      hgLip.comp (hlineLip c) (fun t ht => ht)
    rw [mul_one] at hcomp
    exact hcomp
  -- ============================================================
  -- per-`c` slice bound (a.e. c):  μH[1](u⁻¹{c} ∩ S) ≤ ∫⁻ s in T_c, Φ(mk c s).
  -- ============================================================
  have hslicebound : ∀ᵐ c : ℝ, μH[1] (u ⁻¹' {c} ∩ S)
      ≤ ∫⁻ s in {t : ℝ | Complex.mk c t ∈ T}, Φ (Complex.mk c s) := by
    filter_upwards [hslicenull] with c hcnull
    set Tc : Set ℝ := {t : ℝ | Complex.mk c t ∈ T} with hTc
    have hmkcont : Continuous (fun t : ℝ => Complex.mk c t) := by
      have : (fun t : ℝ => Complex.mk c t)
          = (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) := by
        funext t; rw [Complex.mk_eq_add_mul_I]
      rw [this]; fun_prop
    have hTcmeas : MeasurableSet Tc := by
      rw [hTc]; exact hTmeas.preimage hmkcont.measurable
    -- a measurable null superset of the bad slice parameters.
    set B : Set ℝ := toMeasurable volume {s : ℝ | Complex.mk c s ∈ W} with hB
    have hBmeas : MeasurableSet B := measurableSet_toMeasurable _ _
    have hB0 : volume B = 0 := by rw [hB, measure_toMeasurable]; exact hcnull
    have hBsup : {s : ℝ | Complex.mk c s ∈ W} ⊆ B := subset_toMeasurable _ _
    set Tgood : Set ℝ := Tc \ B with hTgood
    set Tbad : Set ℝ := Tc ∩ B with hTbad
    have hTgood_meas : MeasurableSet Tgood := hTcmeas.diff hBmeas
    -- on `Tgood`, the determinant is nonzero.
    have hgood_det : ∀ t ∈ Tgood, (Ψ' (g (Complex.mk c t))).det ≠ 0 := by
      intro t ht
      obtain ⟨htT, htB⟩ := ht
      intro hdet0
      apply htB
      obtain ⟨z, hz, hzeq⟩ := htT
      have hgS : g (Complex.mk c t) ∈ S := hgmem _ ⟨z, hz, hzeq⟩
      have hgZ : g (Complex.mk c t) ∈ Z :=
        hZsub ⟨by simp only [mem_ofPred_eq, not_not]; exact hdet0, hgS⟩
      apply hBsup
      change Complex.mk c t ∈ W
      rw [hW, ← hright _ ⟨z, hz, hzeq⟩]
      exact ⟨g (Complex.mk c t), ⟨hgZ, hgS⟩, rfl⟩
    -- fiber set equality
    have hfiber : u ⁻¹' {c} ∩ S
        = (fun s : ℝ => g (Complex.mk c s)) '' Tc := by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_image, mem_ofPred_eq, hTc]
      constructor
      · rintro ⟨huc, hzS⟩
        have hΨze : Complex.mk c (Ψ z).im = Ψ z := by
          apply Complex.ext
          · simp [hre z hzS, huc]
          · simp
        exact ⟨(Ψ z).im, by rw [hΨze]; exact ⟨z, hzS, rfl⟩, by rw [hΨze, hleft z hzS]⟩
      · rintro ⟨s, hsT, rfl⟩
        have hgS : g (Complex.mk c s) ∈ S := hgmem _ hsT
        refine ⟨?_, hgS⟩
        rw [← hre _ hgS, hright _ hsT]
    -- image splits  (Tc = Tgood ∪ Tbad)
    have himgsplit : (fun s : ℝ => g (Complex.mk c s)) '' Tc
        = (fun s : ℝ => g (Complex.mk c s)) '' Tgood
          ∪ (fun s : ℝ => g (Complex.mk c s)) '' Tbad := by
      rw [← image_union]
      congr 1
      rw [hTgood, hTbad, sdiff_union_inter]
    -- good-part Hausdorff bound via arc-length
    have hgoodbound : μH[1] ((fun s : ℝ => g (Complex.mk c s)) '' Tgood)
        ≤ ∫⁻ s in Tc, Φ (Complex.mk c s) := by
      calc μH[1] ((fun s : ℝ => g (Complex.mk c s)) '' Tgood)
          ≤ ∫⁻ s in Tgood, (‖Dg (Complex.mk c s) Complex.I‖₊ : ℝ≥0∞) := by
            apply hausdorffMeasure_one_image_le hTgood_meas
            intro t ht
            have hdetne := hgood_det t ht
            have htT : Complex.mk c t ∈ T := ht.1
            exact (hslicederiv c t htT hdetne).mono (fun s hs => hs.1)
        _ = ∫⁻ s in Tgood, Φ (Complex.mk c s) := rfl
        _ ≤ ∫⁻ s in Tc, Φ (Complex.mk c s) :=
            lintegral_mono_set (fun t ht => ht.1)
    -- bad-part image is null
    have hbad_null : μH[1] ((fun s : ℝ => g (Complex.mk c s)) '' Tbad) = 0 := by
      have hHvol : (μH[(1:ℝ)] : Measure ℝ) = volume := hausdorffMeasure_real
      have hTbad_null : μH[1] Tbad = 0 := by
        rw [hHvol]; exact measure_mono_null inter_subset_right hB0
      have hsub : Tbad ⊆ {t : ℝ | Complex.mk c t ∈ T} := fun t ht => ht.1
      refine le_antisymm ?_ (zero_le)
      calc μH[1] ((fun s : ℝ => g (Complex.mk c s)) '' Tbad)
          ≤ ((‖(A.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ - δ)⁻¹ : ℝ≥0) ^ (1:ℝ) * μH[1] Tbad :=
            ((hsliceLip c).mono hsub).hausdorffMeasure_image_le (by norm_num)
        _ = 0 := by rw [hTbad_null, mul_zero]
    calc μH[1] (u ⁻¹' {c} ∩ S)
        = μH[1] ((fun s : ℝ => g (Complex.mk c s)) '' Tc) := by rw [hfiber]
      _ ≤ μH[1] ((fun s : ℝ => g (Complex.mk c s)) '' Tgood)
            + μH[1] ((fun s : ℝ => g (Complex.mk c s)) '' Tbad) := by
          rw [himgsplit]; exact measure_union_le _ _
      _ ≤ ∫⁻ s in Tc, Φ (Complex.mk c s) := by rw [hbad_null, add_zero]; exact hgoodbound
  -- ============================================================
  -- Fubini:  ∫⁻ c, ∫⁻ s in T_c, Φ(mk c s)  =  ∫⁻ w in T, Φ w.
  -- ============================================================
  have hmkmeas_all : ∀ c : ℝ, Measurable (fun t : ℝ => Complex.mk c t) := by
    intro c
    have hmcomp : Measurable (fun t : ℝ => Complex.measurableEquivRealProd.symm (c, t)) :=
      Complex.measurableEquivRealProd.symm.measurable.comp (by fun_prop)
    have he : (fun t : ℝ => Complex.mk c t)
        = (fun t : ℝ => Complex.measurableEquivRealProd.symm (c, t)) :=
      funext (fun t => (Complex.measurableEquivRealProd_symm_apply (c, t)).symm)
    exact he ▸ hmcomp
  have hFubini : ∫⁻ c : ℝ, ∫⁻ s in {t : ℝ | Complex.mk c t ∈ T}, Φ (Complex.mk c s)
      = ∫⁻ w in T, Φ w := by
    -- rewrite each slice as a full integral of an indicator.
    have hslice_eq : ∀ c : ℝ,
        ∫⁻ s in {t : ℝ | Complex.mk c t ∈ T}, Φ (Complex.mk c s)
          = ∫⁻ s : ℝ, (T.indicator Φ) (Complex.mk c s) := by
      intro c
      have hmkmeas : MeasurableSet {t : ℝ | Complex.mk c t ∈ T} :=
        hTmeas.preimage (hmkmeas_all c)
      rw [← lintegral_indicator hmkmeas]
      apply lintegral_congr
      intro s
      by_cases hmem : Complex.mk c s ∈ T
      · rw [indicator_of_mem hmem, indicator_of_mem (show s ∈ {t : ℝ | Complex.mk c t ∈ T}
          from hmem)]
      · rw [indicator_of_notMem hmem, indicator_of_notMem (show s ∉ {t : ℝ | Complex.mk c t ∈ T}
          from hmem)]
    simp_rw [hslice_eq]
    -- Tonelli through the volume-preserving equiv `ℂ ≃ᵐ ℝ × ℝ`.
    have hΦind_meas : AEMeasurable (T.indicator Φ) volume := by
      rw [aemeasurable_indicator_iff hTmeas]
      exact hΦ_meas
    have hsymm_mp : MeasurePreserving Complex.measurableEquivRealProd.symm
        (volume : Measure (ℝ × ℝ)) volume :=
      Complex.volume_preserving_equiv_real_prod.symm _
    have hcomp_meas : AEMeasurable
        (fun p : ℝ × ℝ => (T.indicator Φ) (Complex.measurableEquivRealProd.symm p))
        ((volume : Measure ℝ).prod volume) := by
      have : AEMeasurable
          (fun p : ℝ × ℝ => (T.indicator Φ) (Complex.measurableEquivRealProd.symm p))
          (volume : Measure (ℝ × ℝ)) := by
        apply AEMeasurable.comp_aemeasurable' _
          Complex.measurableEquivRealProd.symm.measurable.aemeasurable
        rw [hsymm_mp.map_eq]; exact hΦind_meas
      rwa [Measure.volume_eq_prod] at this
    calc ∫⁻ c : ℝ, ∫⁻ s : ℝ, (T.indicator Φ) (Complex.mk c s)
        = ∫⁻ p : ℝ × ℝ, (T.indicator Φ) (Complex.measurableEquivRealProd.symm p)
            ∂((volume : Measure ℝ).prod volume) := by
          rw [lintegral_prod _ hcomp_meas]
          apply lintegral_congr; intro c
          apply lintegral_congr; intro s
          rw [Complex.measurableEquivRealProd_symm_apply]
      _ = ∫⁻ w : ℂ, (T.indicator Φ) w := by
          rw [← Measure.volume_eq_prod]
          exact (Complex.volume_preserving_equiv_real_prod.symm _).lintegral_comp_emb
            Complex.measurableEquivRealProd.symm.measurableEmbedding _
      _ = ∫⁻ w in T, Φ w := lintegral_indicator hTmeas _
  -- ============================================================
  -- Area formula:  ∫⁻ w in T, Φ w  =  ∫⁻ z in S, ofReal |det Ψ'z| * Φ(Ψ z).
  -- ============================================================
  have hArea : ∫⁻ w in T, Φ w
      = ∫⁻ z in S, ENNReal.ofReal |(Ψ' z).det| * Φ (Ψ z) := by
    rw [hT]
    exact lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hΨ' hinj Φ
  -- a.e. on S, the integrand equals `‖fderiv ℝ u z‖₊`.
  have hAreaInt : ∫⁻ z in S, ENNReal.ofReal |(Ψ' z).det| * Φ (Ψ z)
      = ∫⁻ z in S, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
    apply lintegral_congr_ae
    filter_upwards [hdet_ne, hΦΨ, hfderiv_eq] with z hdetz hΦz hfz
    rw [hΦz, hfz]
    have hdtop : ENNReal.ofReal |(Ψ' z).det| ≠ ⊤ := ENNReal.ofReal_ne_top
    have hd0 : ENNReal.ofReal |(Ψ' z).det| ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le, abs_pos]; exact hdetz
    rw [ENNReal.mul_div_cancel hd0 hdtop]
  -- ============================================================
  -- Combine.
  -- ============================================================
  calc ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ S)
      ≤ ∫⁻ c : ℝ, ∫⁻ s in {t : ℝ | Complex.mk c t ∈ T}, Φ (Complex.mk c s) :=
        lintegral_mono_ae hslicebound
    _ = ∫⁻ w in T, Φ w := hFubini
    _ = ∫⁻ z in S, ENNReal.ofReal |(Ψ' z).det| * Φ (Ψ z) := hArea
    _ = ∫⁻ z in S, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := hAreaInt


end NoWanderingDomains.Coarea
