/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.Sobolev.Coarea.Assembly
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory

/-!
# Co-area slice assembly and the Vitali–Carathéodory envelope

Two bricks for the planar Loewner reciprocity assembly:

* `coarea_slice_assembly` — the co-area step: for a global Lipschitz potential `U`, a
  measurable weight `σ`, and a measurable majorant `G` of `‖fderiv U‖` a.e. on `Ω`, a
  slice lower bound `1 ≤ ∫_{U⁻¹(c) ∩ Ω} σ dμH¹` for a.e. `c ∈ (0, α)` integrates against
  the sharp Euclidean co-area inequality `eilenberg_coarea_grad_le`
  (`Analysis/Sobolev/Coarea/Assembly.lean`, with weight `σ · 𝟙_Ω`) to

    `ofReal α ≤ ∫_Ω σ · G`.

* `exists_lsc_sq_approx` — the Vitali–Carathéodory envelope: a measurable density `ρ` with
  cushion `c` admits a lower semicontinuous majorant `Φ ≥ max ρ c` whose squared energy on
  a finite-volume measurable set exceeds that of `max ρ c` by at most `ε`. Obtained by
  applying Mathlib's `exists_le_lowerSemicontinuous_lintegral_ge` to `(max ρ c)²` over
  `volume.restrict Ω` and taking the square root (`rpow (1/2)`), which preserves lower
  semicontinuity (continuous monotone post-composition) and the pointwise domination.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace NoWanderingDomains

/-- **The co-area slice assembly.** For a globally Lipschitz `U : ℂ → ℝ`, a measurable
weight `σ`, a measurable set `Ω`, a measurable `G` dominating `‖fderiv ℝ U ·‖₊` a.e. on
`Ω`, and a slice bound `1 ≤ ∫_{U⁻¹(c) ∩ Ω} σ dμH¹` for a.e. `c ∈ (0, α)`:

  `ENNReal.ofReal α ≤ ∫⁻ z in Ω, σ z * G z`.

Chain: `ofReal α ≤ ∫⁻ c in Ioo 0 α, (slice) ≤ ∫⁻ c, ∫_{U⁻¹(c)} σ·𝟙_Ω dμH¹ ≤
∫⁻ z, σ·𝟙_Ω·‖fderiv U‖ ≤ ∫_Ω σ·G` via `eilenberg_coarea_grad_le`. -/
theorem coarea_slice_assembly {U : ℂ → ℝ} {K : ℝ≥0} (hU : LipschitzWith K U)
    {σ : ℂ → ℝ≥0∞} (hσm : Measurable σ) {Ω : Set ℂ} (hΩ : MeasurableSet Ω)
    {G : ℂ → ℝ≥0∞} (hGm : Measurable G)
    (heik : ∀ᵐ z, z ∈ Ω → (‖fderiv ℝ U z‖₊ : ℝ≥0∞) ≤ G z)
    {α : ℝ} (hα : 0 < α)
    (hslice : ∀ᵐ c : ℝ, c ∈ Set.Ioo 0 α →
      1 ≤ ∫⁻ z in U ⁻¹' {c} ∩ Ω, σ z ∂(μH[1] : Measure ℂ)) :
    ENNReal.ofReal α ≤ ∫⁻ z in Ω, σ z * G z := by
  -- `hGm` and `hα` are part of the frozen interface; this route does not need them
  -- (`ofReal` and the a.e. comparison absorb them), so discard explicitly.
  have _ := hGm
  have _ := hα
  have hgm : Measurable (Ω.indicator σ) := hσm.indicator hΩ
  have hcoarea := Coarea.eilenberg_coarea_grad_le hU hgm
  calc ENNReal.ofReal α
      = ∫⁻ _ in Set.Ioo (0:ℝ) α, (1:ℝ≥0∞) := by
        rw [setLIntegral_one, Real.volume_Ioo, sub_zero]
    _ ≤ ∫⁻ c in Set.Ioo (0:ℝ) α,
          ∫⁻ z in U ⁻¹' {c} ∩ Ω, σ z ∂(μH[1] : Measure ℂ) :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2 hslice)
    _ = ∫⁻ c in Set.Ioo (0:ℝ) α,
          ∫⁻ z in U ⁻¹' {c}, Ω.indicator σ z ∂(μH[1] : Measure ℂ) := by
        refine lintegral_congr fun c => ?_
        rw [setLIntegral_indicator hΩ, Set.inter_comm]
    _ ≤ ∫⁻ c, ∫⁻ z in U ⁻¹' {c}, Ω.indicator σ z ∂(μH[1] : Measure ℂ) :=
        setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ z, Ω.indicator σ z * (‖fderiv ℝ U z‖₊ : ℝ≥0∞) ∂volume := hcoarea
    _ = ∫⁻ z in Ω, σ z * (‖fderiv ℝ U z‖₊ : ℝ≥0∞) ∂volume := by
        have hpt : ∀ z, Ω.indicator σ z * (‖fderiv ℝ U z‖₊ : ℝ≥0∞)
            = Ω.indicator (fun z => σ z * (‖fderiv ℝ U z‖₊ : ℝ≥0∞)) z := by
          intro z
          by_cases hz : z ∈ Ω <;> simp [hz]
        simp_rw [hpt]
        exact lintegral_indicator hΩ _
    _ ≤ ∫⁻ z in Ω, σ z * G z :=
        lintegral_mono_ae (((ae_restrict_iff' hΩ).2 heik).mono
          fun z hz => mul_le_mul_right hz _)

/-- **The Vitali–Carathéodory square-envelope.** For measurable `ρ`, a measurable set `Ω`
of finite volume, a cushion `c ∈ (0, ∞)`, and `ε ≠ 0`, there is a lower semicontinuous
`Φ : ℂ → ℝ≥0∞` with `max (ρ z) c ≤ Φ z` for all `z` and

  `∫_Ω Φ² ≤ ∫_Ω (max ρ c)² + ε`. -/
theorem exists_lsc_sq_approx {ρ : ℂ → ℝ≥0∞} (hρm : Measurable ρ) {Ω : Set ℂ}
    (hΩ : MeasurableSet Ω) (hvol : volume Ω ≠ ⊤) {ε : ℝ≥0∞} (hε : ε ≠ 0)
    {c : ℝ≥0∞} (hc : c ≠ 0) (hctop : c ≠ ⊤) :
    ∃ Φ : ℂ → ℝ≥0∞, LowerSemicontinuous Φ ∧ (∀ z, max (ρ z) c ≤ Φ z) ∧
      ∫⁻ z in Ω, (Φ z) ^ 2 ≤ (∫⁻ z in Ω, (max (ρ z) c) ^ 2) + ε := by
  -- `hΩ`/`hc`/`hctop` are part of the frozen interface (restriction and the cushion
  -- need no measurability or nondegeneracy here); discard explicitly.
  have _ := hΩ
  have _ := hc
  have _ := hctop
  -- `volume.restrict Ω` is a finite Borel measure on the metric space `ℂ`,
  -- hence weakly regular, so Mathlib's Vitali–Carathéodory envelope applies.
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.2 hvol
  have hfm : Measurable fun z => (max (ρ z) c) ^ 2 :=
    (hρm.max measurable_const).pow_const 2
  obtain ⟨g, hg_le, hg_lsc, hg_int⟩ :=
    exists_le_lowerSemicontinuous_lintegral_ge (volume.restrict Ω)
      (fun z => (max (ρ z) c) ^ 2) hfm hε
  -- `rpow` square/square-root arithmetic in `ℝ≥0∞` (unconditional).
  have hroot : ∀ x : ℝ≥0∞, (x ^ 2) ^ (2⁻¹ : ℝ) = x := by
    intro x
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul,
      (by norm_num : (2:ℝ) * 2⁻¹ = 1), ENNReal.rpow_one]
  have hsq : ∀ x : ℝ≥0∞, (x ^ (2⁻¹ : ℝ)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul,
      (by norm_num : (2:ℝ)⁻¹ * 2 = 1), ENNReal.rpow_one]
  refine ⟨fun z => g z ^ (2⁻¹ : ℝ), ?_, ?_, ?_⟩
  · -- lower semicontinuity: continuous monotone post-composition with `· ^ (1/2)`.
    exact ENNReal.continuous_rpow_const.comp_lowerSemicontinuous hg_lsc
      fun x y hxy => ENNReal.rpow_le_rpow hxy (by norm_num)
  · -- pointwise domination: take square roots in `(max ρ c)² ≤ g`.
    intro z
    have h := ENNReal.rpow_le_rpow (hg_le z) (by norm_num : (0:ℝ) ≤ 2⁻¹)
    rwa [hroot] at h
  · -- energy: `Φ² = g`, then the Vitali–Carathéodory integral bound.
    calc ∫⁻ z in Ω, (g z ^ (2⁻¹ : ℝ)) ^ 2
        = ∫⁻ z in Ω, g z := by simp_rw [hsq]
      _ ≤ (∫⁻ z in Ω, (max (ρ z) c) ^ 2) + ε := hg_int

end NoWanderingDomains
