/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.Regularity.Grotzsch
import NoWanderingDomains.QC.Equivalence
import NoWanderingDomains.QC.Regularity.MetricExtraction
import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Equicontinuity of quasiconformal families

This file derives the **regularity outputs** of the quasiconformal-modulus layer that the
normal-family compactness theorem (`QC/Calculus/Compactness.lean`) consumes:

* **Equicontinuity / normal family**: a uniformly `K`-quasiconformal, suitably normalized
  family `{fₙ}` and its inverses `{fₙ⁻¹}` are equicontinuous on every compact set, with a modulus
  of continuity depending only on `K` and the set.
* **Inverse stability**: the inverse of a geometric `K`-quasiconformal map is geometric
  `K`-quasiconformal (through the analytic equivalence layer).

Every statement is a true classical theorem and **fails for bare homeomorphisms** — the
`IsQCGeometric`/`uniformly K-qc` hypothesis is load-bearing throughout, and no statement
assumes any derivative control.

## Main statements

* `isQCGeometric_inv_of_isQCGeometric` — the inverse of a geometric `K`-qc map is geometric `K`-qc;
* `exists_uniform_modulus` / `exists_uniform_image_bound` — uniform ring-modulus distortion data
  and image bounds for a uniformly `K`-qc family;
* `equicontinuousOn_of_uniform_isQCGeometric` — a normalized uniformly `K`-qc family is
  equicontinuous on compacta;
* `equicontinuousOn_inv_of_uniform_isQCGeometric` — the inverses are equicontinuous on compacta.
-/

open MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology

namespace NoWanderingDomains

/-- **The inverse of a geometric `K`-quasiconformal map is geometric `K`-quasiconformal.** Since
`IsQCGeometric f K` is the symmetric modulus-distortion condition (the image-family modulus is used,
which for the homeomorphism `f⁻¹` recovers `M(f⁻¹(Q')) ≤ K · M(Q')` for every quadrilateral `Q'`),
the inverse homeomorphism `g = f⁻¹` is again geometric `K`-qc. Needed so that the equicontinuity of
the inverses `{fₙ⁻¹}` is an instance of the equicontinuity of a uniformly `K`-qc family. -/
theorem isQCGeometric_inv_of_isQCGeometric {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    IsQCGeometric (hf.2.1.isHomeomorph.homeomorph f).symm K := by
  -- Pass to the analytic layer: `f` is `IsQCAnalytic` with `b.normInf ≤ (K−1)/(K+1)`.
  obtain ⟨b, hbnd, hfa⟩ := isQCAnalytic_of_isQCGeometric hf.1 hf
  -- The analytic inverse is `IsQCAnalytic` with `b'.normInf ≤ b.normInf ≤ (K−1)/(K+1)`.
  obtain ⟨b', hb'le, hg⟩ := hfa.inverse_isQCAnalytic'
  have hb'bnd : b'.normInf ≤ (K - 1) / (K + 1) := le_trans hb'le hbnd
  -- Convert the analytic inverse back to the geometric side (same `K`).
  have hgeom : IsQCGeometric (⇑(hfa.1.1.homeomorph f).symm) K :=
    isQCGeometric_of_isQCAnalytic hf.1 hb'bnd hg
  -- The two homeomorphism-derived inverses agree as functions: both are the two-sided
  -- inverse of the same bijective `f`, so their `symm` coercions are equal by `funext`.
  have hbridge : ⇑(hfa.1.1.homeomorph f).symm = ⇑(hf.2.1.isHomeomorph.homeomorph f).symm := by
    funext w
    -- `f` is injective (from either homeomorph), and both sides map to a right-inverse of `f`.
    have hinj : Function.Injective f := (hfa.1.1.homeomorph f).injective
    -- For each derivation, `f (H.symm w) = w`: `f = ⇑(H.homeomorph f)` on the nose.
    have hL : f ((hfa.1.1.homeomorph f).symm w) = w := by
      rw [← IsHomeomorph.homeomorph_apply f hfa.1.1 ((hfa.1.1.homeomorph f).symm w)]
      exact (hfa.1.1.homeomorph f).apply_symm_apply w
    have hR : f ((hf.2.1.isHomeomorph.homeomorph f).symm w) = w := by
      rw [← IsHomeomorph.homeomorph_apply f hf.2.1.isHomeomorph
            ((hf.2.1.isHomeomorph.homeomorph f).symm w)]
      exact (hf.2.1.isHomeomorph.homeomorph f).apply_symm_apply w
    exact hinj (hL.trans hR.symm)
  rwa [hbridge] at hgeom

-- Metric-extraction chain (STAR gate/η-step/anchor chain) closing the inscription package.
noncomputable def starSup (f : ℂ → ℂ) (x₀ : ℂ) (a : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ ζ ∈ f '' Metric.closedBall x₀ a, r = dist ζ (f x₀)}

/-- Reparametrized form: sup of `dist (f (x₀ + a ζ)) (f x₀)` over the unit ball. -/
theorem starSup_eq_reparam (f : ℂ → ℂ) (x₀ : ℂ) {a : ℝ} (ha : 0 ≤ a) :
    starSup f x₀ a
      = sSup ((fun ζ => dist (f (x₀ + (a : ℂ) * ζ)) (f x₀)) '' Metric.closedBall (0 : ℂ) 1) := by
  unfold starSup
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨ζ, ⟨w, hw, rfl⟩, rfl⟩
    rcases eq_or_lt_of_le ha with rfl | hapos
    · simp only [Metric.mem_closedBall] at hw
      have hwx : w = x₀ := by rw [dist_le_zero] at hw; exact hw
      exact ⟨0, by simp, by simp [hwx]⟩
    · refine ⟨(w - x₀) / (a : ℂ), ?_, ?_⟩
      · simp only [Metric.mem_closedBall, dist_zero_right, norm_div, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hapos]
        rw [div_le_one hapos]
        simpa [dist_eq_norm] using hw
      · congr 2
        rw [mul_div_cancel₀ _ (by exact_mod_cast hapos.ne' : (a : ℂ) ≠ 0)]
        ring
  · rintro ⟨ζ, hζ, rfl⟩
    refine ⟨f (x₀ + (a : ℂ) * ζ), ⟨x₀ + (a : ℂ) * ζ, ?_, rfl⟩, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right] at hζ
    simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
    calc a * ‖ζ‖ ≤ a * 1 := by apply mul_le_mul_of_nonneg_left hζ ha
      _ = a := by ring

theorem continuousOn_starSup (f : ℂ → ℂ) (hf : Continuous f) (x₀ : ℂ) :
    ContinuousOn (fun a => starSup f x₀ a) (Set.Ici (0 : ℝ)) := by
  have hcont : Continuous fun a : ℝ =>
      sSup ((fun ζ => dist (f (x₀ + (a : ℂ) * ζ)) (f x₀)) '' Metric.closedBall (0 : ℂ) 1) := by
    apply IsCompact.continuous_sSup (isCompact_closedBall (0 : ℂ) 1)
    change Continuous fun p : ℝ × ℂ => dist (f (x₀ + (p.1 : ℂ) * p.2)) (f x₀)
    apply Continuous.dist _ continuous_const
    apply hf.comp
    apply Continuous.add continuous_const
    exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd
  apply ContinuousOn.congr hcont.continuousOn
  intro a ha
  exact starSup_eq_reparam f x₀ ha

/-- The defining set of `starSup` is bounded above (image of a compact set under a continuous
distance). -/
theorem starSup_bddAbove (f : ℂ → ℂ) (hf : Continuous f) (x₀ : ℂ) (a : ℝ) :
    BddAbove {r : ℝ | ∃ ζ ∈ f '' Metric.closedBall x₀ a, r = dist ζ (f x₀)} := by
  have hKcpt : IsCompact (f '' Metric.closedBall x₀ a) := (isCompact_closedBall x₀ a).image hf
  have hSimg : {r : ℝ | ∃ ζ ∈ f '' Metric.closedBall x₀ a, r = dist ζ (f x₀)}
      = (fun ζ => dist ζ (f x₀)) '' (f '' Metric.closedBall x₀ a) := by
    ext r; simp only [Set.mem_ofPred_eq, Set.mem_image]
    exact ⟨fun ⟨ζ, hζ, h⟩ => ⟨ζ, hζ, h.symm⟩, fun ⟨ζ, hζ, h⟩ => ⟨ζ, hζ, h.symm⟩⟩
  rw [hSimg]
  exact hKcpt.bddAbove_image (continuous_id.dist continuous_const).continuousOn

/-- Nonnegativity of `starSup` (`f x₀` itself is in the image of the closed ball, giving `0` in the
set). -/
theorem starSup_nonneg (f : ℂ → ℂ) (hf : Continuous f) (x₀ : ℂ) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ starSup f x₀ a := by
  apply le_csSup (starSup_bddAbove f hf x₀ a)
  exact ⟨f x₀, ⟨x₀, Metric.mem_closedBall_self ha, rfl⟩, (dist_self _).symm⟩

/-- **(H3).** The image of an inner point is within `starSup` of `f x₀`. -/
theorem dist_le_starSup (f : ℂ → ℂ) (hf : Continuous f) {x₀ w : ℂ} {a : ℝ}
    (hw : w ∈ Metric.closedBall x₀ a) : dist (f x₀) (f w) ≤ starSup f x₀ a := by
  rw [dist_comm]
  exact le_csSup (starSup_bddAbove f hf x₀ a) ⟨f w, ⟨w, hw, rfl⟩, rfl⟩

/-- **Monotonicity** of `starSup` in the radius. -/
theorem starSup_mono (f : ℂ → ℂ) (hf : Continuous f) (x₀ : ℂ) {a₁ a₂ : ℝ} (ha₁ : 0 ≤ a₁)
    (h : a₁ ≤ a₂) : starSup f x₀ a₁ ≤ starSup f x₀ a₂ := by
  apply csSup_le_csSup (starSup_bddAbove f hf x₀ a₂)
  · exact ⟨0, f x₀, ⟨x₀, Metric.mem_closedBall_self ha₁, rfl⟩, (dist_self _).symm⟩
  · rintro r ⟨ζ, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨f w, ⟨w, Metric.closedBall_subset_closedBall h hw, rfl⟩, rfl⟩

/-- `starSup f x₀ 0 = 0`: the closed ball of radius `0` is the singleton `{x₀}`. -/
theorem starSup_zero (f : ℂ → ℂ) (x₀ : ℂ) : starSup f x₀ 0 = 0 := by
  unfold starSup
  have : {r : ℝ | ∃ ζ ∈ f '' Metric.closedBall x₀ 0, r = dist ζ (f x₀)} = {0} := by
    ext r
    simp only [Metric.closedBall_zero, Set.image_singleton, Set.mem_ofPred_eq,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨ζ, rfl, rfl⟩; exact dist_self _
    · rintro rfl; exact ⟨f x₀, rfl, (dist_self _).symm⟩
  rw [this, csSup_singleton]

/-- **`starSup → 0` as the radius `→ 0⁺`.** -/
theorem starSup_tendsto_zero (f : ℂ → ℂ) (hf : Continuous f) (x₀ : ℂ) :
    Tendsto (fun a => starSup f x₀ a) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hcont : ContinuousWithinAt (fun a => starSup f x₀ a) (Set.Ici (0 : ℝ)) 0 :=
    (continuousOn_starSup f hf x₀) 0 (Set.self_mem_Ici)
  rw [ContinuousWithinAt, starSup_zero] at hcont
  exact hcont.mono_left (nhdsWithin_mono 0 (Set.Ioi_subset_Ici le_rfl))

/-- The image-side inner sphere distance `b'` of STAR. -/
noncomputable def starInf (f : ℂ → ℂ) (x₀ : ℂ) (b : ℝ) : ℝ :=
  Metric.infDist (f x₀) (f '' Metric.sphere x₀ b)

/-- Positivity of `starInf` for a homeomorphism and `b > 0`. -/
theorem starInf_pos {f : ℂ → ℂ} (hf : IsHomeomorph f) {x₀ : ℂ} {b : ℝ} (hb : 0 < b) :
    0 < starInf f x₀ b := by
  have hFcpt : IsCompact (f '' Metric.sphere x₀ b) := (isCompact_sphere x₀ b).image hf.continuous
  have hFne : (f '' Metric.sphere x₀ b).Nonempty := by
    obtain ⟨w, hw⟩ := (NormedSpace.sphere_nonempty (x := x₀) (r := b)).mpr hb.le
    exact ⟨f w, w, hw, rfl⟩
  have hcenter_off : f x₀ ∉ f '' Metric.sphere x₀ b := by
    rintro ⟨y, hy, hyeq⟩
    have hxy : x₀ = y := hf.injective hyeq.symm
    rw [← hxy, Metric.mem_sphere, dist_self] at hy
    exact hb.ne hy
  exact (hFcpt.isClosed.notMem_iff_infDist_pos hFne).mp hcenter_off

/-- **STEP A key bound.** `starSup f x₀ t < starInf f x₀ b / √2` for `t` below the `K`-threshold
`b · exp(-240 π K)`. The proof is a first-crossing argument: if `A t ≥ c := b'/√2`, the closed set
`Bad := {a ∈ [0,t] | A a ≥ c}` has a positive infimum `a*` with `A a* = c` (attained since `A a → 0`
as `a → 0`); on `(0, a*)` the gate holds, so STAR bounds `A a ≤ b'·√(120πK/log(b/a))`; the left
limit gives `c = A a* ≤ b'·√(120πK/log(b/a*))`, forcing `log(b/a*) ≤ 240πK`, i.e.
`a* ≥ b·exp(-240πK) > t`, contradicting `a* ≤ t`. -/
theorem starSup_lt_of_qc {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) {x₀ : ℂ} {b t : ℝ}
    (hb : 0 < b) (ht : 0 < t) (htb : t < b)
    (hthr : t < b * Real.exp (-(240 * Real.pi * K))) :
    starSup f x₀ t < starInf f x₀ b / Real.sqrt 2 := by
  classical
  have hK1 : (1 : ℝ) ≤ K := hf.1
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have hpi := Real.pi_pos
  have hcont : Continuous f := hf.2.1.isHomeomorph.continuous
  set b' : ℝ := starInf f x₀ b with hb'def
  have hb'pos : 0 < b' := starInf_pos hf.2.1.isHomeomorph hb
  set A : ℝ → ℝ := fun a => starSup f x₀ a with hAdef
  set c : ℝ := b' / Real.sqrt 2 with hcdef
  have hsqrt2_pos : 0 < Real.sqrt 2 := by positivity
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc_pos : 0 < c := by rw [hcdef]; positivity
  have hAcont : ContinuousOn A (Set.Ici (0 : ℝ)) := continuousOn_starSup f hcont x₀
  by_contra hle
  rw [not_lt] at hle  -- hle : c ≤ A t
  -- The "bad" radii in `[0,t]` where `A ≥ c`, as `Icc 0 t ∩ A⁻¹'(Ici c)`.
  set Bad : Set ℝ := Set.Icc (0 : ℝ) t ∩ A ⁻¹' Set.Ici c with hBaddef
  have hBad_closed : IsClosed Bad :=
    (hAcont.mono Set.Icc_subset_Ici_self).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have htBad : t ∈ Bad := ⟨⟨ht.le, le_refl _⟩, hle⟩
  have hBad_ne : Bad.Nonempty := ⟨t, htBad⟩
  have hBad_bdd : BddBelow Bad := ⟨0, fun a ha => ha.1.1⟩
  set as : ℝ := sInf Bad with hasdef
  have hasBad : as ∈ Bad := hBad_closed.csInf_mem hBad_ne hBad_bdd
  have hasIcc : as ∈ Set.Icc (0 : ℝ) t := hasBad.1
  have hasc : c ≤ A as := hasBad.2
  -- `as > 0`: `A 0 = 0 < c`.
  have hA0 : A 0 = 0 := starSup_zero f x₀
  have haspos : 0 < as := by
    rcases lt_or_eq_of_le hasIcc.1 with h | h
    · exact h
    · exact absurd (by rw [← h, hA0] at hasc; exact hasc) (not_le.mpr hc_pos)
  have hast : as ≤ t := hasIcc.2
  have hasb : as < b := lt_of_le_of_lt hast htb
  -- Below `as`, `A < c` (so the gate holds strictly).
  have hbelow : ∀ a ∈ Set.Ioo (0 : ℝ) as, A a < c := by
    intro a ha
    by_contra hge
    rw [not_lt] at hge
    have haBad : a ∈ Bad := ⟨⟨ha.1.le, le_trans ha.2.le hast⟩, hge⟩
    exact absurd (csInf_le hBad_bdd haBad) (not_le.mpr ha.2)
  -- The STAR bound at each `a ∈ (0, as)`: `A a ≤ b' · √(120πK/log(b/as))`.
  set B : ℝ := b' * Real.sqrt (120 * Real.pi * K / Real.log (b / as)) with hBdef
  have hlog_as : 0 < Real.log (b / as) := Real.log_pos ((one_lt_div haspos).mpr hasb)
  have hstar_bound : ∀ a ∈ Set.Ioo (0 : ℝ) as, A a ≤ B := by
    intro a ha
    have hapos := ha.1
    have hab : a < b := lt_trans ha.2 hasb
    have hAa_lt : A a < c := hbelow a ha
    have hAa_nn : 0 ≤ A a := starSup_nonneg f hcont x₀ hapos.le
    rcases eq_or_lt_of_le hAa_nn with hA0a | hApos
    · -- A a = 0 ≤ B.
      rw [← hA0a]; positivity
    · -- Gate holds: (A a / b')² < 1/2.
      have hgate : (A a / b') ^ 2 < 1 / 2 := by
        have hlt : A a < b' / Real.sqrt 2 := lt_of_lt_of_le hAa_lt (le_of_eq hcdef)
        have hb'sqrt : A a * Real.sqrt 2 < b' := by
          rw [lt_div_iff₀ hsqrt2_pos] at hlt; exact hlt
        have hsq : (A a * Real.sqrt 2) ^ 2 < b' ^ 2 := by
          apply sq_lt_sq' _ hb'sqrt
          nlinarith [hAa_nn, hsqrt2_pos, hb'pos]
        rw [mul_pow, hsqrt2_sq] at hsq
        rw [div_pow, div_lt_iff₀ (by positivity)]
        nlinarith [hsq]
      -- STAR at (a, b).
      have hstar := geometric_shellRatio_star hf hapos hab hApos hgate
      -- `hstar : (A a / b')² / 60 ≤ K · (2π/log(b/a))`.
      have hloga : 0 < Real.log (b / a) := Real.log_pos ((one_lt_div hapos).mpr hab)
      have hlog_mono : Real.log (b / as) ≤ Real.log (b / a) :=
        Real.log_le_log (by positivity) (by
          rw [div_le_div_iff_of_pos_left hb haspos hapos]; exact ha.2.le)
      -- (A a / b')² ≤ 120πK/log(b/a) ≤ 120πK/log(b/as).
      have hsq_le : (A a / b') ^ 2 ≤ 120 * Real.pi * K / Real.log (b / as) := by
        have h1 : (A a / b') ^ 2 ≤ 120 * Real.pi * K / Real.log (b / a) := by
          rw [div_le_iff₀ (by norm_num : (0:ℝ) < 60)] at hstar
          rw [div_eq_mul_inv (120 * Real.pi * K), ← div_eq_mul_inv]
          rw [le_div_iff₀ hloga]
          calc (A a / b') ^ 2 * Real.log (b / a)
              ≤ K * (2 * Real.pi / Real.log (b / a)) * 60 * Real.log (b / a) := by
                apply mul_le_mul_of_nonneg_right hstar hloga.le
            _ = 120 * Real.pi * K := by field_simp; ring
        calc (A a / b') ^ 2 ≤ 120 * Real.pi * K / Real.log (b / a) := h1
          _ ≤ 120 * Real.pi * K / Real.log (b / as) := by
              apply div_le_div_of_nonneg_left (by positivity) hlog_as hlog_mono
      -- Take square roots: A a / b' ≤ √(...), so A a ≤ B.
      have hAdivb'_nn : 0 ≤ A a / b' := by positivity
      have hrhs_nn : 0 ≤ 120 * Real.pi * K / Real.log (b / as) := by positivity
      have hsqrt := (Real.le_sqrt hAdivb'_nn hrhs_nn).mpr hsq_le
      rw [div_le_iff₀ hb'pos] at hsqrt
      rw [hBdef]
      linarith [hsqrt, mul_comm b' (Real.sqrt (120 * Real.pi * K / Real.log (b / as)))]
  -- Left limit: `A as ≤ B`.
  have hAas_le_B : A as ≤ B := by
    have hne : NeBot (𝓝[Set.Ioo (0 : ℝ) as] as) := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (ne_of_lt haspos)]
      exact ⟨haspos.le, le_refl _⟩
    have htend : Tendsto A (𝓝[Set.Ioo (0 : ℝ) as] as) (𝓝 (A as)) := by
      have hsub : Set.Ioo (0 : ℝ) as ⊆ Set.Ici (0 : ℝ) := fun x hx => Set.mem_Ici.mpr hx.1.le
      exact (hAcont as (Set.mem_Ici.mpr haspos.le)).tendsto.mono_left (nhdsWithin_mono as hsub)
    exact le_of_tendsto htend (eventually_nhdsWithin_of_forall hstar_bound)
  -- Combine: `c ≤ A as ≤ B = b'·√(120πK/log(b/as))`.
  have hc_le_B : c ≤ B := le_trans hasc hAas_le_B
  -- Divide by b': `1/√2 ≤ √(120πK/log(b/as))`, square: `1/2 ≤ 120πK/log(b/as)`.
  have hrhs_nn : 0 ≤ 120 * Real.pi * K / Real.log (b / as) := by positivity
  have hsqrt_ge : b' / Real.sqrt 2 ≤ b' * Real.sqrt (120 * Real.pi * K / Real.log (b / as)) := by
    rw [hcdef, hBdef] at hc_le_B; exact hc_le_B
  -- Square both sides of `b'/√2 ≤ b'·√(...)` (both nonneg) to get `b'²/2 ≤ b'²·(120πK/log(b/as))`.
  have hsq_ineq : b' ^ 2 / 2 ≤ b' ^ 2 * (120 * Real.pi * K / Real.log (b / as)) := by
    have hL : (0:ℝ) ≤ b' / Real.sqrt 2 := by positivity
    have := mul_le_mul hsqrt_ge hsqrt_ge hL (le_trans hL hsqrt_ge)
    rw [mul_mul_mul_comm, Real.mul_self_sqrt hrhs_nn] at this
    rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)] at this
    linarith [this]
  have hsq : 1 / 2 ≤ 120 * Real.pi * K / Real.log (b / as) := by
    have hb'2 : 0 < b' ^ 2 := by positivity
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)] at *
    nlinarith [hsq_ineq, hb'2]
  -- `log(b/as) ≤ 240πK`, so `as ≥ b·exp(-240πK) > t ≥ as`.
  have hlogle : Real.log (b / as) ≤ 240 * Real.pi * K := by
    rw [le_div_iff₀ hlog_as] at hsq
    nlinarith [hsq, hlog_as.le]
  -- `b/as ≤ exp(240πK)`, so `as ≥ b·exp(-240πK)`.
  have hbas : b / as ≤ Real.exp (240 * Real.pi * K) := by
    rw [← Real.exp_log (by positivity : (0:ℝ) < b / as)]
    exact Real.exp_le_exp.mpr hlogle
  have has_ge : b * Real.exp (-(240 * Real.pi * K)) ≤ as := by
    rw [div_le_iff₀ haspos] at hbas
    have hexp_pos := Real.exp_pos (240 * Real.pi * K)
    rw [Real.exp_neg, mul_comm, inv_mul_le_iff₀ hexp_pos]
    exact hbas
  linarith [has_ge, hthr, hast]

/-- **STEP B (the η-step).** For a geometric `K`-quasiconformal `f`, `0 < b`, and `0 < t < b` below
the threshold `b · exp(-240 π K)`, every image point of the inner disk stays within
`b' · √(120 π K / log(b/t))` of `f x₀`, where `b' := starInf f x₀ b`. Combines the gate
(`starSup_lt_of_qc`) with the shell-ratio bound (`geometric_shellRatio_star`) and `dist_le_starSup`.
-/
theorem dist_le_etaStep {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) {x₀ w : ℂ} {b t : ℝ}
    (hb : 0 < b) (ht : 0 < t) (htb : t < b)
    (hthr : t < b * Real.exp (-(240 * Real.pi * K))) (hw : w ∈ Metric.closedBall x₀ t) :
    dist (f x₀) (f w)
      ≤ starInf f x₀ b * Real.sqrt (120 * Real.pi * K / Real.log (b / t)) := by
  have hK1 : (1 : ℝ) ≤ K := hf.1
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have hpi := Real.pi_pos
  have hcont : Continuous f := hf.2.1.isHomeomorph.continuous
  set b' : ℝ := starInf f x₀ b with hb'def
  have hb'pos : 0 < b' := starInf_pos hf.2.1.isHomeomorph hb
  have hlogt : 0 < Real.log (b / t) := Real.log_pos ((one_lt_div ht).mpr htb)
  set A : ℝ := starSup f x₀ t with hAdef
  have hA_nn : 0 ≤ A := starSup_nonneg f hcont x₀ ht.le
  -- The gate holds at `(t, b)`.
  have hgate_lt : A < b' / Real.sqrt 2 := starSup_lt_of_qc hf hb ht htb hthr
  have hsqrt2_pos : 0 < Real.sqrt 2 := by positivity
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- First, `dist (f x₀) (f w) ≤ A`.
  have hdist_le_A : dist (f x₀) (f w) ≤ A := dist_le_starSup f hcont hw
  refine le_trans hdist_le_A ?_
  -- Now `A ≤ b' · √(120πK/log(b/t))`.
  rcases eq_or_lt_of_le hA_nn with hA0 | hApos
  · rw [← hA0]; positivity
  · -- Gate as squared inequality for STAR.
    have hgate : (A / b') ^ 2 < 1 / 2 := by
      have hb'sqrt : A * Real.sqrt 2 < b' := by
        rw [lt_div_iff₀ hsqrt2_pos] at hgate_lt; exact hgate_lt
      have hsq : (A * Real.sqrt 2) ^ 2 < b' ^ 2 := by
        apply sq_lt_sq' _ hb'sqrt; nlinarith [hA_nn, hsqrt2_pos, hb'pos]
      rw [mul_pow, hsqrt2_sq] at hsq
      rw [div_pow, div_lt_iff₀ (by positivity)]; nlinarith [hsq]
    have hstar := geometric_shellRatio_star hf ht htb hApos hgate
    have hsq_le : (A / b') ^ 2 ≤ 120 * Real.pi * K / Real.log (b / t) := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 60)] at hstar
      rw [le_div_iff₀ hlogt]
      calc (A / b') ^ 2 * Real.log (b / t)
          ≤ K * (2 * Real.pi / Real.log (b / t)) * 60 * Real.log (b / t) :=
            mul_le_mul_of_nonneg_right hstar hlogt.le
        _ = 120 * Real.pi * K := by field_simp; ring
    have hAdivb'_nn : 0 ≤ A / b' := by positivity
    have hrhs_nn : 0 ≤ 120 * Real.pi * K / Real.log (b / t) := by positivity
    have hsqrt := (Real.le_sqrt hAdivb'_nn hrhs_nn).mpr hsq_le
    rw [div_le_iff₀ hb'pos] at hsqrt
    linarith [hsqrt, mul_comm b' (Real.sqrt (120 * Real.pi * K / Real.log (b / t)))]

/-- The constant contraction factor of one chain step: `κ K := √(120πK/(240πK+log 2)) < 1`. -/
noncomputable def chainKappa (K : ℝ) : ℝ :=
  Real.sqrt (120 * Real.pi * K / (240 * Real.pi * K + Real.log 2))

theorem chainKappa_nonneg (K : ℝ) : 0 ≤ chainKappa K := Real.sqrt_nonneg _

theorem chainKappa_lt_one {K : ℝ} (hK : 1 ≤ K) : chainKappa K < 1 := by
  have hpi := Real.pi_pos
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [chainKappa, show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
  apply Real.sqrt_lt_sqrt (by positivity)
  rw [div_lt_one (by positivity)]
  linarith [hlog2, hpi, hK0, mul_pos (mul_pos (by norm_num : (0:ℝ) < 120) hpi) hK0]

/-- **Single chain step.** If `dist p q = r₀ > 0` and `z'` is within
`ρ₀ := (r₀/2)·exp(-240πK)/2` of `z`, then the image step is contracted by `chainKappa K` against the
larger of the two anchor image distances: `dist (f z) (f z') ≤ κ · max (dist (f z)(f p))
(dist (f z)(f q))`. The far anchor (at distance `≥ r₀/2` from `z`, one of `p, q` always is, by the
triangle inequality) sits on the sphere of radius `b := dist z (anchor)`, so `starInf ≤` that anchor
image distance (H2), and the fixed step ratio forces `log(b/step) ≥ 240πK + log 2`. -/
theorem dist_step_le {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) {p q z z' : ℂ} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hpq : dist p q = r₀)
    (hstep : dist z z' ≤ r₀ / 2 * Real.exp (-(240 * Real.pi * K)) / 2) :
    dist (f z) (f z')
      ≤ chainKappa K * max (dist (f z) (f p)) (dist (f z) (f q)) := by
  have hK1 : (1 : ℝ) ≤ K := hf.1
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have hpi := Real.pi_pos
  have hcont : Continuous f := hf.2.1.isHomeomorph.continuous
  have hexp_pos := Real.exp_pos (-(240 * Real.pi * K))
  set ρ₀ : ℝ := r₀ / 2 * Real.exp (-(240 * Real.pi * K)) / 2 with hρ₀def
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀def]; positivity
  -- The far anchor: one of p, q is at distance ≥ r₀/2 from z.
  have hfar : r₀ / 2 ≤ dist z p ∨ r₀ / 2 ≤ dist z q := by
    by_contra h
    rw [not_or, not_le, not_le] at h
    obtain ⟨h1, h2⟩ := h
    have := dist_triangle p z q
    rw [dist_comm p z] at this
    rw [hpq] at this; linarith [this, h1, h2]
  -- STEP B centered at z with anchor radius b := dist z anchor, applied to z'.
  -- Reduce to a uniform statement for a fixed anchor `w` with `r₀/2 ≤ dist z w`.
  have key : ∀ w : ℂ, r₀ / 2 ≤ dist z w →
      dist (f z) (f z') ≤ chainKappa K * dist (f z) (f w) := by
    intro w hw
    set b : ℝ := dist z w with hbdef
    have hb2 : r₀ / 2 ≤ b := hw
    have hbpos : 0 < b := lt_of_lt_of_le (by positivity) hb2
    have hstep' : dist z z' ≤ ρ₀ := hstep
    have hstep_pos_or : dist z z' = 0 ∨ 0 < dist z z' := by
      rcases eq_or_lt_of_le (dist_nonneg (x := z) (y := z')) with h | h
      · exact Or.inl h.symm
      · exact Or.inr h
    rcases hstep_pos_or with hz0 | hzpos
    · -- z = z': distance 0.
      rw [dist_eq_zero] at hz0
      rw [hz0, dist_self]
      apply mul_nonneg (chainKappa_nonneg K) dist_nonneg
    · set t : ℝ := dist z z' with htdef
      have htb : t < b := lt_of_le_of_lt hstep' (by
        rw [hρ₀def]; nlinarith [hb2, hexp_pos, Real.exp_le_one_iff.mpr
          (by nlinarith [hpi, hK0] : -(240 * Real.pi * K) ≤ 0), hr₀])
      have hthr : t < b * Real.exp (-(240 * Real.pi * K)) := by
        calc t ≤ ρ₀ := hstep'
          _ = r₀ / 2 * Real.exp (-(240 * Real.pi * K)) / 2 := hρ₀def
          _ < r₀ / 2 * Real.exp (-(240 * Real.pi * K)) := by nlinarith [hexp_pos, hr₀]
          _ ≤ b * Real.exp (-(240 * Real.pi * K)) := by
              apply mul_le_mul_of_nonneg_right hb2 hexp_pos.le
      -- STEP B: dist (f z)(f z') ≤ starInf f z b · √(120πK/log(b/t)).
      have hz'mem : z' ∈ Metric.closedBall z t := by
        rw [Metric.mem_closedBall, htdef, dist_comm]
      have hetaB := dist_le_etaStep hf hbpos hzpos htb hthr hz'mem
      -- starInf f z b ≤ dist (f z)(f w): w ∈ sphere z b.
      have hwsphere : w ∈ Metric.sphere z b := by rw [Metric.mem_sphere, hbdef, dist_comm]
      have hstarInf_le : starInf f z b ≤ dist (f z) (f w) :=
        Metric.infDist_le_dist_of_mem ⟨w, hwsphere, rfl⟩
      -- √(120πK/log(b/t)) ≤ chainKappa K.
      have hlogt : 0 < Real.log (b / t) := Real.log_pos ((one_lt_div hzpos).mpr htb)
      have hbt_ge : 2 * Real.exp (240 * Real.pi * K) ≤ b / t := by
        rw [le_div_iff₀ hzpos]
        calc 2 * Real.exp (240 * Real.pi * K) * t
            ≤ 2 * Real.exp (240 * Real.pi * K) * ρ₀ :=
              mul_le_mul_of_nonneg_left hstep' (by positivity)
          _ = r₀ / 2 * (Real.exp (240 * Real.pi * K) * Real.exp (-(240 * Real.pi * K))) := by
              rw [hρ₀def]; ring
          _ = r₀ / 2 := by rw [← Real.exp_add]; simp
          _ ≤ b := hb2
      have hlog_ge : 240 * Real.pi * K + Real.log 2 ≤ Real.log (b / t) := by
        calc 240 * Real.pi * K + Real.log 2
            = Real.log (Real.exp (240 * Real.pi * K)) + Real.log 2 := by rw [Real.log_exp]
          _ = Real.log (2 * Real.exp (240 * Real.pi * K)) := by
              rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', add_comm]
          _ ≤ Real.log (b / t) := Real.log_le_log (by positivity) hbt_ge
      have hsqrt_le : Real.sqrt (120 * Real.pi * K / Real.log (b / t)) ≤ chainKappa K := by
        rw [chainKappa]
        apply Real.sqrt_le_sqrt
        apply div_le_div_of_nonneg_left (by positivity) (by positivity) hlog_ge
      -- Chain: dist(fz)(fz') ≤ starInf·√ ≤ dist(fz)(fw)·κ.
      calc dist (f z) (f z')
          ≤ starInf f z b * Real.sqrt (120 * Real.pi * K / Real.log (b / t)) := hetaB
        _ ≤ dist (f z) (f w) * chainKappa K := by
            apply mul_le_mul hstarInf_le hsqrt_le (Real.sqrt_nonneg _) dist_nonneg
        _ = chainKappa K * dist (f z) (f w) := by ring
  rcases hfar with hp | hq
  · calc dist (f z) (f z') ≤ chainKappa K * dist (f z) (f p) := key p hp
      _ ≤ chainKappa K * max (dist (f z) (f p)) (dist (f z) (f q)) := by
          apply mul_le_mul_of_nonneg_left (le_max_left _ _) (chainKappa_nonneg K)
  · calc dist (f z) (f z') ≤ chainKappa K * dist (f z) (f q) := key q hq
      _ ≤ chainKappa K * max (dist (f z) (f p)) (dist (f z) (f q)) := by
          apply mul_le_mul_of_nonneg_left (le_max_right _ _) (chainKappa_nonneg K)

/-- **The anchor chain (STEP C).** For a geometric `K`-quasiconformal `f`, anchors `p, q` at
distance `r₀ > 0` with `dist (f p)(f q) ≤ M`, and any `z` with `dist z p ≤ R`, the image distance
`dist (f z)(f p)` is bounded by `(1 + κ)^m · M`, where `κ := chainKappa K < 1` and
`m := ⌈R / ρ₀⌉ + 1` (`ρ₀ := (r₀/2)·exp(-240πK)/2`) — a constant depending only on `K, r₀, R, M`. The
straight segment `p → z` is split into `m` steps of length `≤ ρ₀`; each step contracts the larger of
the two anchor image distances by `κ` (`dist_step_le`), so the maximum grows by at most `1 + κ`. -/
theorem chain_dist_le {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) {p q : ℂ} {r₀ M R : ℝ}
    (hr₀ : 0 < r₀) (hpq : dist p q = r₀) (hM : dist (f p) (f q) ≤ M) {z : ℂ}
    (hzR : dist z p ≤ R) :
    dist (f z) (f p)
      ≤ (1 + chainKappa K) ^ (⌈R / (r₀ / 2 * Real.exp (-(240 * Real.pi * K)) / 2)⌉₊ + 1) * M := by
  have hK1 : (1 : ℝ) ≤ K := hf.1
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have hpi := Real.pi_pos
  have hκnn : 0 ≤ chainKappa K := chainKappa_nonneg K
  have hM0 : 0 ≤ M := le_trans dist_nonneg hM
  set ρ₀ : ℝ := r₀ / 2 * Real.exp (-(240 * Real.pi * K)) / 2 with hρ₀def
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀def]; positivity
  set m : ℕ := ⌈R / ρ₀⌉₊ + 1 with hmdef
  have hmpos : 0 < m := Nat.succ_pos _
  have hMC : (m : ℂ) ≠ 0 := by exact_mod_cast hmpos.ne'
  -- Segment points.
  set y : ℕ → ℂ := fun k => p + ((k : ℂ) / (m : ℂ)) * (z - p) with hy
  have hy0 : y 0 = p := by simp [hy]
  have hym : y m = z := by simp only [hy]; rw [div_self hMC]; ring
  -- Consecutive step distances.
  have hstepdist : ∀ k : ℕ, dist (y k) (y (k + 1)) = (1 / m) * dist z p := by
    intro k
    simp only [hy, dist_eq_norm]
    have hcast : ((k + 1 : ℕ) : ℂ) = (k : ℂ) + 1 := by push_cast; ring
    rw [hcast, show (p + ((k : ℂ) / (m : ℂ)) * (z - p)) - (p + (((k : ℂ) + 1) / (m : ℂ)) * (z - p))
          = (-(1 : ℂ) / (m : ℂ)) * (z - p) from by field_simp; ring, norm_mul]
    rw [show (-(1 : ℂ) / (m : ℂ)) = -(1 / (m : ℂ)) from by ring, norm_neg, norm_div,
      norm_one, Complex.norm_natCast, ← dist_eq_norm]
  have hsteple : ∀ k : ℕ, dist (y k) (y (k + 1)) ≤ ρ₀ := by
    intro k
    rw [hstepdist k]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by exact_mod_cast hmpos)]
    -- dist z p ≤ R ≤ ⌈R/ρ₀⌉ ρ₀ ≤ m ρ₀
    have h1 : dist z p ≤ R := hzR
    have h2 : R ≤ (⌈R / ρ₀⌉₊ : ℝ) * ρ₀ := by
      rcases le_or_gt R 0 with hR0 | hR0
      · calc R ≤ 0 := hR0
          _ ≤ (⌈R / ρ₀⌉₊ : ℝ) * ρ₀ := by positivity
      · rw [← div_le_iff₀ hρ₀pos]; exact Nat.le_ceil _
    have h3 : (⌈R / ρ₀⌉₊ : ℝ) * ρ₀ ≤ (m : ℝ) * ρ₀ := by
      apply mul_le_mul_of_nonneg_right _ hρ₀pos.le
      rw [hmdef]; push_cast; linarith
    linarith [h1, h2, h3]
  -- The max anchor image distance E.
  set E : ℕ → ℝ := fun k => max (dist (f (y k)) (f p)) (dist (f (y k)) (f q)) with hE
  have hE0 : E 0 ≤ M := by
    simp only [hE, hy0, dist_self]
    exact max_le hM0 hM
  have hEstep : ∀ k : ℕ, E (k + 1) ≤ (1 + chainKappa K) * E k := by
    intro k
    have hstep := dist_step_le hf hr₀ hpq (z := y k) (z' := y (k + 1))
      (by rw [← hρ₀def]; exact hsteple k)
    -- dist (f (y (k+1))) (f p) ≤ dist(f(y(k+1)))(f(y k)) + dist(f(y k))(f p) ≤ κ E k + E k
    have hp' : dist (f (y (k + 1))) (f p) ≤ (1 + chainKappa K) * E k := by
      calc dist (f (y (k + 1))) (f p)
          ≤ dist (f (y (k + 1))) (f (y k)) + dist (f (y k)) (f p) := dist_triangle _ _ _
        _ = dist (f (y k)) (f (y (k + 1))) + dist (f (y k)) (f p) := by rw [dist_comm]
        _ ≤ chainKappa K * E k + E k := by
            apply add_le_add hstep (le_max_left _ _)
        _ = (1 + chainKappa K) * E k := by ring
    have hq' : dist (f (y (k + 1))) (f q) ≤ (1 + chainKappa K) * E k := by
      calc dist (f (y (k + 1))) (f q)
          ≤ dist (f (y (k + 1))) (f (y k)) + dist (f (y k)) (f q) := dist_triangle _ _ _
        _ = dist (f (y k)) (f (y (k + 1))) + dist (f (y k)) (f q) := by rw [dist_comm]
        _ ≤ chainKappa K * E k + E k := by
            apply add_le_add hstep (le_max_right _ _)
        _ = (1 + chainKappa K) * E k := by ring
    exact max_le hp' hq'
  -- Geometric bound: E m ≤ (1+κ)^m E 0.
  have hEgeo : ∀ k : ℕ, E k ≤ (1 + chainKappa K) ^ k * E 0 := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      calc E (n + 1) ≤ (1 + chainKappa K) * E n := hEstep n
        _ ≤ (1 + chainKappa K) * ((1 + chainKappa K) ^ n * E 0) := by
            apply mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (1 + chainKappa K) ^ (n + 1) * E 0 := by ring
  -- Conclude.
  calc dist (f z) (f p) ≤ E m := by rw [← hym]; exact le_max_left _ _
    _ ≤ (1 + chainKappa K) ^ m * E 0 := hEgeo m
    _ ≤ (1 + chainKappa K) ^ m * M := by
        apply mul_le_mul_of_nonneg_left hE0 (by positivity)

/-- Auxiliary for `exists_uniform_modulus` under `1 ≤ K` (equivalently, `Nonempty ι`). -/
theorem exists_uniform_modulus_aux {ι : Type*} [Nonempty ι] {f : ι → ℂ → ℂ} {K : ℝ}
    (hfK : ∀ i, IsQCGeometric (f i) K) {S : Set ℂ} (hS : IsCompact S)
    {p q : ℂ} (hp : p ∈ S) (_hq : q ∈ S) (hpq : p ≠ q) {M : ℝ}
    (hub : ∀ i, dist (f i p) (f i q) ≤ M) (hK1 : 1 ≤ K) :
    ∃ ω₀ : ℝ → ℝ, (∀ t, 0 ≤ ω₀ t) ∧ Tendsto ω₀ (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ (i : ι), ∀ x₀ ∈ S, ∀ x ∈ S, dist (f i x₀) (f i x) ≤ ω₀ (dist x₀ x) := by
  classical
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have hpi := Real.pi_pos
  -- Anchor separation.
  set r₀ : ℝ := dist p q with hr₀def
  have hr₀pos : 0 < r₀ := dist_pos.mpr hpq
  have hM0 : 0 ≤ M := le_trans dist_nonneg (hub (Classical.arbitrary _))
  -- Compact neighborhood radius.
  obtain ⟨RS, hRS⟩ := hS.isBounded.subset_closedBall p
  have hRS0 : 0 ≤ RS := le_trans dist_nonneg (by
    have := hRS hp; rw [Metric.mem_closedBall] at this; exact this)
  set R : ℝ := RS + r₀ / 2 with hRdef
  -- Chain constant.
  set ρ₀ : ℝ := r₀ / 2 * Real.exp (-(240 * Real.pi * K)) / 2 with hρ₀def
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀def]; positivity
  set m : ℕ := ⌈R / ρ₀⌉₊ + 1 with hmdef
  set Cstar : ℝ := (1 + chainKappa K) ^ m * M with hCstardef
  have hκnn := chainKappa_nonneg K
  have hCstar0 : 0 ≤ Cstar := by
    rw [hCstardef]; exact mul_nonneg (by positivity) hM0
  -- Fact 1: uniform chain bound `dist (f i z)(f i p) ≤ Cstar` for `dist z p ≤ R`.
  have hchain : ∀ i : ι, ∀ z : ℂ, dist z p ≤ R → dist (f i z) (f i p) ≤ Cstar := by
    intro i z hz
    have := chain_dist_le (hfK i) hr₀pos rfl (hub i) (R := R) (z := z) hz
    rwa [← hρ₀def, ← hmdef, ← hCstardef] at this
  -- Fact 2: `starInf (f i) x₀ (r₀/2) ≤ 2 Cstar` for `x₀ ∈ S`.
  have hstarInf_le : ∀ i : ι, ∀ x₀ ∈ S, starInf (f i) x₀ (r₀ / 2) ≤ 2 * Cstar := by
    intro i x₀ hx₀
    have hx₀R : dist x₀ p ≤ R := by
      have := hRS hx₀; rw [Metric.mem_closedBall] at this; rw [hRdef]; linarith [this]
    -- Choose a sphere point `w ∈ sphere x₀ (r₀/2)`.
    obtain ⟨w, hw⟩ := (NormedSpace.sphere_nonempty (x := x₀) (r := r₀ / 2)).mpr (by positivity)
    have hwmem : w ∈ Metric.sphere x₀ (r₀ / 2) := hw
    have hwR : dist w p ≤ R := by
      rw [Metric.mem_sphere] at hwmem
      have := hRS hx₀; rw [Metric.mem_closedBall] at this
      calc dist w p ≤ dist w x₀ + dist x₀ p := dist_triangle _ _ _
        _ = r₀ / 2 + dist x₀ p := by rw [hwmem]
        _ ≤ r₀ / 2 + RS := by linarith [this]
        _ = R := by rw [hRdef]; ring
    calc starInf (f i) x₀ (r₀ / 2) ≤ dist (f i x₀) (f i w) :=
          Metric.infDist_le_dist_of_mem ⟨w, hwmem, rfl⟩
      _ ≤ dist (f i x₀) (f i p) + dist (f i p) (f i w) := dist_triangle _ _ _
      _ ≤ Cstar + Cstar := by
          apply add_le_add (hchain i x₀ hx₀R)
          rw [dist_comm]; exact hchain i w hwR
      _ = 2 * Cstar := by ring
  -- Fact 3: `dist (f i x₀)(f i x) ≤ 2 Cstar` for `x₀, x ∈ S`.
  have hdiam : ∀ i : ι, ∀ x₀ ∈ S, ∀ x ∈ S, dist (f i x₀) (f i x) ≤ 2 * Cstar := by
    intro i x₀ hx₀ x hx
    have hx₀R : dist x₀ p ≤ R := by
      have := hRS hx₀; rw [Metric.mem_closedBall] at this; rw [hRdef]; linarith [this]
    have hxR : dist x p ≤ R := by
      have := hRS hx; rw [Metric.mem_closedBall] at this; rw [hRdef]; linarith [this]
    calc dist (f i x₀) (f i x) ≤ dist (f i x₀) (f i p) + dist (f i p) (f i x) := dist_triangle _ _ _
      _ ≤ Cstar + Cstar := by
          apply add_le_add (hchain i x₀ hx₀R); rw [dist_comm]; exact hchain i x hxR
      _ = 2 * Cstar := by ring
  -- The threshold and modulus function.
  set thr : ℝ := r₀ / 2 * Real.exp (-(240 * Real.pi * K)) with hthrdef
  have hthr_pos : 0 < thr := by rw [hthrdef]; positivity
  set ω₀ : ℝ → ℝ := fun t =>
    if t < thr then 2 * Cstar * Real.sqrt (120 * Real.pi * K / Real.log (r₀ / 2 / t))
    else 2 * Cstar with hω₀def
  refine ⟨ω₀, ?_, ?_, ?_⟩
  · -- Nonnegativity.
    intro t; rw [hω₀def]; dsimp only
    split_ifs with h
    · positivity
    · positivity
  · -- Tendsto 0.
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        ω₀ t = 2 * Cstar * Real.sqrt (120 * Real.pi * K / Real.log (r₀ / 2 / t)) := by
      filter_upwards [Ioo_mem_nhdsGT hthr_pos] with t ht
      rw [hω₀def]; dsimp only; rw [if_pos ht.2]
    rw [tendsto_congr' hev]
    -- 2 Cstar · √(120πK/log((r₀/2)/t)) → 0 as t → 0⁺.
    have hdiv : Tendsto (fun t : ℝ => r₀ / 2 / t) (𝓝[>] (0 : ℝ)) atTop := by
      have hmul : Tendsto (fun t : ℝ => (r₀ / 2) * t⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
        Tendsto.const_mul_atTop (by positivity) tendsto_inv_nhdsGT_zero
      refine hmul.congr (fun t => (div_eq_mul_inv (r₀ / 2) t).symm)
    have hlog : Tendsto (fun t : ℝ => Real.log (r₀ / 2 / t)) (𝓝[>] (0 : ℝ)) atTop :=
      Real.tendsto_log_atTop.comp hdiv
    have hratio : Tendsto (fun t : ℝ => 120 * Real.pi * K / Real.log (r₀ / 2 / t))
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds hlog
    have hsqrt : Tendsto (fun t : ℝ => Real.sqrt (120 * Real.pi * K / Real.log (r₀ / 2 / t)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hratio
      rwa [Real.sqrt_zero] at this
    have := hsqrt.const_mul (2 * Cstar)
    rwa [mul_zero] at this
  · -- Modulus bound.
    intro i x₀ hx₀ x hx
    set t : ℝ := dist x₀ x with htdef
    by_cases hlt : t < thr
    · rw [hω₀def]; dsimp only; rw [if_pos hlt]
      by_cases ht0 : t = 0
      · have hxx : x₀ = x := dist_eq_zero.mp (htdef ▸ ht0)
        rw [hxx, dist_self]; positivity
      · have htpos : 0 < t := lt_of_le_of_ne dist_nonneg (Ne.symm ht0)
        have htb : t < r₀ / 2 := lt_of_lt_of_le hlt (by
          rw [hthrdef]; nlinarith [Real.exp_le_one_iff.mpr
            (by nlinarith [hpi, hK0] : -(240 * Real.pi * K) ≤ 0), hr₀pos])
        have hthr' : t < r₀ / 2 * Real.exp (-(240 * Real.pi * K)) := by
          rw [← hthrdef]; exact hlt
        have hxmem : x ∈ Metric.closedBall x₀ t := by
          rw [Metric.mem_closedBall, htdef, dist_comm]
        have hetaB := dist_le_etaStep (hfK i) (b := r₀ / 2) (t := t)
          (by positivity) htpos htb hthr' hxmem
        calc dist (f i x₀) (f i x)
            ≤ starInf (f i) x₀ (r₀ / 2)
                * Real.sqrt (120 * Real.pi * K / Real.log (r₀ / 2 / t)) := hetaB
          _ ≤ 2 * Cstar * Real.sqrt (120 * Real.pi * K / Real.log (r₀ / 2 / t)) := by
              apply mul_le_mul_of_nonneg_right (hstarInf_le i x₀ hx₀) (Real.sqrt_nonneg _)
    · rw [hω₀def]; dsimp only; rw [if_neg hlt]
      exact hdiam i x₀ hx₀ x hx

/-- **The uniform modulus of continuity (STEP C + D).** A normalized uniformly `K`-quasiconformal
family on a compact set `S` (anchors `p ≠ q` of `S`, `dist (f i p)(f i q) ≤ M`) has a modulus
`ω₀ : ℝ → ℝ` with `ω₀ ≥ 0`, `ω₀ t → 0` as `t → 0⁺`, and `dist (f i x₀)(f i x) ≤ ω₀ (dist x₀ x)` for
all `i` and all `x₀, x ∈ S`. The uniform diameter bound `C*` on `f i '' N` (a compact neighborhood
of `S`) comes from the anchor chain (`chain_dist_le`); the vanishing modulus from the η-step
(`dist_le_etaStep`) at each `x₀ ∈ S` with anchor radius `r₀/2`. -/
theorem exists_uniform_modulus {ι : Type*} {f : ι → ℂ → ℂ} {K : ℝ}
    (hfK : ∀ i, IsQCGeometric (f i) K) {S : Set ℂ} (hS : IsCompact S)
    {p q : ℂ} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) {M : ℝ}
    (hub : ∀ i, dist (f i p) (f i q) ≤ M) :
    ∃ ω₀ : ℝ → ℝ, (∀ t, 0 ≤ ω₀ t) ∧ Tendsto ω₀ (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ (i : ι), ∀ x₀ ∈ S, ∀ x ∈ S, dist (f i x₀) (f i x) ≤ ω₀ (dist x₀ x) := by
  classical
  by_cases hne : Nonempty ι
  · obtain ⟨i₀⟩ := hne
    have hK1 : (1 : ℝ) ≤ K := (hfK i₀).1
    have : Nonempty ι := ⟨i₀⟩
    exact exists_uniform_modulus_aux hfK hS hp hq hpq hub hK1
  · exact ⟨fun _ => 0, fun _ => le_refl _, tendsto_const_nhds, fun i => absurd ⟨i⟩ hne⟩

/-- **Uniform image diameter bound.** A normalized uniformly `K`-quasiconformal family on a compact
set `S` (anchors `p ≠ q` of `S`, `dist (f i p)(f i q) ≤ M`) has its image restricted to `S` of
uniformly bounded diameter: there is a constant `C` with `dist (f i x₀)(f i x) ≤ C` for all `i` and
all `x₀, x ∈ S`. This is the uniform diameter bound `C* = (1 + κ)^m · M · 2` from the anchor chain
(`chain_dist_le`), independent of `i`. -/
theorem exists_uniform_image_bound {ι : Type*} {f : ι → ℂ → ℂ} {K : ℝ}
    (hfK : ∀ i, IsQCGeometric (f i) K) {S : Set ℂ} (hS : IsCompact S)
    {p q : ℂ} (_hp : p ∈ S) (_hq : q ∈ S) (hpq : p ≠ q) {M : ℝ}
    (hub : ∀ i, dist (f i p) (f i q) ≤ M) :
    ∃ C : ℝ, ∀ (i : ι), ∀ x₀ ∈ S, ∀ x ∈ S, dist (f i x₀) (f i x) ≤ C := by
  classical
  by_cases hne : Nonempty ι
  · obtain ⟨i₀⟩ := hne
    have hK1 : (1 : ℝ) ≤ K := (hfK i₀).1
    have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
    have hpi := Real.pi_pos
    set r₀ : ℝ := dist p q with hr₀def
    have hr₀pos : 0 < r₀ := dist_pos.mpr hpq
    obtain ⟨RS, hRS⟩ := hS.isBounded.subset_closedBall p
    set R : ℝ := RS + r₀ / 2 with hRdef
    set ρ₀ : ℝ := r₀ / 2 * Real.exp (-(240 * Real.pi * K)) / 2 with hρ₀def
    set m : ℕ := ⌈R / ρ₀⌉₊ + 1 with hmdef
    set Cstar : ℝ := (1 + chainKappa K) ^ m * M with hCstardef
    have hchain : ∀ i : ι, ∀ z : ℂ, dist z p ≤ R → dist (f i z) (f i p) ≤ Cstar := by
      intro i z hz
      have := chain_dist_le (hfK i) hr₀pos rfl (hub i) (R := R) (z := z) hz
      rwa [← hρ₀def, ← hmdef, ← hCstardef] at this
    refine ⟨2 * Cstar, fun i x₀ hx₀ x hx => ?_⟩
    have hx₀R : dist x₀ p ≤ R := by
      have := hRS hx₀; rw [Metric.mem_closedBall] at this; rw [hRdef]; linarith [this]
    have hxR : dist x p ≤ R := by
      have := hRS hx; rw [Metric.mem_closedBall] at this; rw [hRdef]; linarith [this]
    calc dist (f i x₀) (f i x)
        ≤ dist (f i x₀) (f i p) + dist (f i p) (f i x) := dist_triangle _ _ _
      _ ≤ Cstar + Cstar := by
          apply add_le_add (hchain i x₀ hx₀R); rw [dist_comm]; exact hchain i x hxR
      _ = 2 * Cstar := by ring
  · exact ⟨0, fun i => absurd ⟨i⟩ hne⟩

/-- **The inscription package from the uniform modulus.** A normalized uniformly `K`-quasiconformal
family satisfies `InscriptionModulusData f S`. From the uniform modulus `ω₀`
(`exists_uniform_modulus`), take the degenerate inscription `rᵢ := d + t`, `rₒ := d + 2t`, `M := ⊤`
(so `rₒ · exp(-2π/M.toReal) = rₒ`), with `d := dist (f i x₀)(f i x)` and `t := dist x₀ x > 0`; the
extracted bound `rₒ = d + 2t ≤ ω₀ t + 2t =: ω t` holds and `ω t → 0` as `t → 0⁺`. -/
theorem inscriptionModulusData_of_uniform {ι : Type*} {f : ι → ℂ → ℂ} {K : ℝ}
    (hfK : ∀ i, IsQCGeometric (f i) K) {S : Set ℂ} (hS : IsCompact S)
    {p q : ℂ} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) {M : ℝ}
    (hub : ∀ i, dist (f i p) (f i q) ≤ M) :
    InscriptionModulusData f S := by
  obtain ⟨ω₀, hω₀nn, hω₀lim, hω₀data⟩ := exists_uniform_modulus hfK hS hp hq hpq hub
  refine ⟨fun t => ω₀ t + 2 * |t|, ?_, ?_, ?_⟩
  · -- `ω t → 0`.
    have hlin : Tendsto (fun t : ℝ => 2 * |t|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => 2 * |t|) (𝓝 (0 : ℝ)) (𝓝 (2 * |(0 : ℝ)|)) :=
        (continuous_const.mul (continuous_abs)).tendsto 0
      rw [abs_zero, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have := hω₀lim.add hlin
    simpa using this
  · -- Nonnegativity.
    intro t; have := hω₀nn t; positivity
  · -- The per-configuration inscription data.
    intro i x₀ hx₀ x hx hne
    set t : ℝ := dist x₀ x with htdef
    have htpos : 0 < t := by rw [htdef]; exact dist_pos.mpr (fun h => hne h.symm)
    have htabs : |t| = t := abs_of_pos htpos
    set d : ℝ := dist (f i x₀) (f i x) with hddef
    have hd_nn : 0 ≤ d := dist_nonneg
    have hd_le : d ≤ ω₀ t := hω₀data i x₀ hx₀ x hx
    refine ⟨d + t, d + 2 * t, ⊤, by positivity, by linarith, ?_, le_top, ?_⟩
    · rw [hddef]; linarith
    · simp only [ENNReal.toReal_top, div_zero, Real.exp_zero, mul_one]
      rw [htabs]
      linarith [hd_le]

/-- **Equicontinuity of a normalized uniformly `K`-quasiconformal family.** Let `{fₙ}` be a
family of geometric `K`-quasiconformal maps that is *normalized* on a compact set `S`: there are
points `p ≠ q` of `S` and a constant `M` with `dist (fₙ p) (fₙ q) ≤ M` for all `n` (a two-point
normalization bounding the family's scale above). Then `{fₙ}` is equicontinuous on `S`, with a
modulus of continuity depending only on `K`, `S`, `M`.

Some normalization is unavoidable: without it `fₙ = n · id` is uniformly `1`-quasiconformal yet not
equicontinuous. Under the two-point normalization, the `K`-only quasisymmetric distortion control
of the ring-modulus layer converts the scale bound `dist (fₙ p) (fₙ q) ≤ M` into a uniform
Hölder/modulus-of-continuity estimate on `S`; no lower scale bound is needed (a family collapsing
towards a constant is all the more equicontinuous). False for bare homeomorphisms; no derivative
control assumed. -/
theorem equicontinuousOn_of_uniform_isQCGeometric {ι : Type*} {f : ι → ℂ → ℂ} {K : ℝ}
    (hfK : ∀ i, IsQCGeometric (f i) K) {S : Set ℂ} (hS : IsCompact S)
    {p q : ℂ} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q)
    {M : ℝ} (hub : ∀ i, dist (f i p) (f i q) ≤ M) :
    EquicontinuousOn f S :=
  equicontinuousOn_of_uniform_isQCGeometric_of_inscription
    (inscriptionModulusData_of_uniform hfK hS hp hq hpq hub)

/-- **Equicontinuity of the inverses of a uniformly `K`-quasiconformal family.** Under an
*image-side* covering hypothesis `hTU : T ⊆ f i '' U` for a fixed compact `U` (equivalently
`g i '' T ⊆ U`, uniformly in `i`), the inverse family `{fₙ⁻¹}` is equicontinuous on the compact set
`T`. The image-side hypothesis is essential: without a uniform bound on `g i '' T` the inverses may
expand `T` unboundedly (a scale jump across a fat annulus keeps `K` bounded while compressing a far
ball onto a fixed neighborhood of `T`), so the bare-`T` statement is false. Given `hTU`, the
inverses `g i` are geometric `K`-quasiconformal (`isQCGeometric_inv_of_isQCGeometric`) and
two-point–normalized on `T`: for two distinct anchors `u₀ ≠ v₀` of `T` the scale
`dist (g i u₀) (g i v₀)` is bounded by `diam U`, uniformly in `i`. Forward equicontinuity
`equicontinuousOn_of_uniform_isQCGeometric` applied to `g` then finishes. -/
theorem equicontinuousOn_inv_of_uniform_isQCGeometric {ι : Type*} {f : ι → ℂ → ℂ} {K : ℝ}
    (hfK : ∀ i, IsQCGeometric (f i) K)
    (g : ι → ℂ → ℂ)
    (hg : ∀ i, Function.LeftInverse (g i) (f i) ∧ Function.RightInverse (g i) (f i))
    {T U : Set ℂ} (hT : IsCompact T) (hU : IsCompact U) (hTU : ∀ i, T ⊆ f i '' U) :
    EquicontinuousOn g T := by
  classical
  -- Each inverse `g i` is geometrically `K`-quasiconformal.
  have hgK : ∀ i, IsQCGeometric (g i) K := by
    intro i
    have hinvK := isQCGeometric_inv_of_isQCGeometric (hfK i)
    have hbridge : ⇑((hfK i).2.1.isHomeomorph.homeomorph (f i)).symm = g i := by
      funext w
      have hfinj : Function.Injective (f i) := (hfK i).2.1.isHomeomorph.injective
      have hL : f i (((hfK i).2.1.isHomeomorph.homeomorph (f i)).symm w) = w := by
        rw [← IsHomeomorph.homeomorph_apply (f i) (hfK i).2.1.isHomeomorph
              (((hfK i).2.1.isHomeomorph.homeomorph (f i)).symm w)]
        exact ((hfK i).2.1.isHomeomorph.homeomorph (f i)).apply_symm_apply w
      have hR : f i (g i w) = w := (hg i).2 w
      exact hfinj (hL.trans hR.symm)
    rwa [hbridge] at hinvK
  -- `g i (T) ⊆ U`.
  have hgTU : ∀ i, ∀ z ∈ T, g i z ∈ U := by
    intro i z hz
    obtain ⟨w, hwU, hwz⟩ := hTU i hz
    have : g i z = w := by rw [← hwz]; exact (hg i).1 w
    rw [this]; exact hwU
  -- Subsingleton `T`: trivially equicontinuous.
  by_cases hTsub : T.Subsingleton
  · intro x₀ hx₀ V hV
    refine Filter.eventually_iff_exists_mem.mpr ⟨T, self_mem_nhdsWithin, ?_⟩
    intro x hx i
    rw [hTsub hx hx₀]
    exact refl_mem_uniformity hV
  · -- Two distinct anchors `u₀ ≠ v₀ ∈ T`.
    rw [Set.not_subsingleton_iff] at hTsub
    obtain ⟨u₀, hu₀, v₀, hv₀, huv⟩ := hTsub
    -- `diam U` bounds `dist (g i u₀) (g i v₀)` uniformly in `i`, since `g i '' T ⊆ U`.
    have hM'ub : ∀ i, dist (g i u₀) (g i v₀) ≤ Metric.diam U := fun i =>
      Metric.dist_le_diam_of_mem hU.isBounded (hgTU i u₀ hu₀) (hgTU i v₀ hv₀)
    -- Apply forward equicontinuity to `g` on `T`.
    exact equicontinuousOn_of_uniform_isQCGeometric hgK hT hu₀ hv₀ huv hM'ub

end NoWanderingDomains
