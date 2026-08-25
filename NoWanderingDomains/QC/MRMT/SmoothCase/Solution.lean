/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.MRMT.SmoothCase.Regularity

/-!
# The smooth-case principal solution

For smooth data the `Lᵖ` fixed point of `φ ↦ μ·Sφ + g` is continuous with
continuous Beurling image and satisfies the equation pointwise; for a smooth
compactly supported coefficient the principal solution is `C¹` with
everywhere-positive Jacobian and nonvanishing `∂f`.

* `exists_continuous_fixedPoint_beltrami_of_contDiff` — the smooth fixed point.
* `exists_contDiffOne_principalSolution` — the `C¹` principal solution.
-/

open MeasureTheory Complex Filter
open scoped ContDiff ENNReal NNReal Topology

namespace NoWanderingDomains

/-! ## The smooth fixed point -/

/-- **Regularity of the Beltrami fixed point for smooth data** (AIM
Lemma 5.2.1 / Theorem 5.2.2, the regularity content). For a smooth compactly
supported multiplier `μ` and datum `g`, and contraction data at an exponent
`p > 2`, the fixed-point equation `φ = μ·Sφ + g` has a solution `φ ∈ Lᵖ`,
vanishing outside the common support ball, which is **continuous with
continuous Beurling transform** and satisfies the equation **pointwise**.
Internally: the `Lᵖ` fixed point of the proved `exists_lp_fixedPoint_beltrami`
is `W^{1,p}` (differentiate the equation: `∂φ` solves the same-multiplier
equation with datum `∂μ·Sφ + ∂g`), hence Hölder continuous by the Morrey
embedding (`Analysis/Sobolev/Morrey/OscillationBound.lean`), and `S` preserves
the Hölder class of compactly supported fields; continuity of both sides
upgrades the a.e. equation to a pointwise one. -/
theorem exists_continuous_fixedPoint_beltrami_of_contDiff {μ g : ℂ → ℂ}
    {p : ℝ≥0∞} {C R : ℝ}
    (hp : 2 < p) (hp' : p ≠ ⊤)
    (hμs : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (hgs : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hCb : IsCalderonZygmundBound beurling p C)
    (hcontr : (eLpNormEssSup μ volume).toReal * C < 1)
    (hsupp : ∀ z : ℂ, R < ‖z‖ → μ z = 0 ∧ g z = 0) :
    ∃ φ : ℂ → ℂ, MemLp φ p volume ∧ (∀ z : ℂ, R < ‖z‖ → φ z = 0) ∧
      Continuous φ ∧ Continuous (beurling φ) ∧
      ∀ z : ℂ, φ z = μ z * beurling φ z + g z := by
  classical
  -- ===== Constants. =====
  set k : ℝ := (eLpNormEssSup μ volume).toReal with hkdef
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have hC0 : 0 ≤ C := hCb.1
  have hr0 : 0 ≤ k * C := mul_nonneg hk0 hC0
  have hr1 : k * C < 1 := hcontr
  set r' : ℝ := (k * C + 1) / 2 with hr'def
  have hr'0 : 0 < r' := by rw [hr'def]; linarith
  have hrr' : k * C < r' := by rw [hr'def]; linarith
  have hr'1 : r' < 1 := by rw [hr'def]; linarith
  set δ : ℝ := r' - k * C with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp.le
  have hp0 : p ≠ 0 := by
    intro h; rw [h] at hp; exact (not_lt_of_ge (zero_le)) hp
  -- ===== Differentiability shorthands. =====
  have hd1 : ∀ {u : ℂ → ℂ}, ContDiff ℝ ∞ u → Differentiable ℝ u := by
    intro u hu
    exact (hu.of_le (by exact_mod_cast le_top : ((1 : ℕ∞) : WithTop ℕ∞) ≤ _)).differentiable
      one_ne_zero
  -- ===== `dz`/`dzbar` of a smooth function are smooth. =====
  have hdz_sm : ∀ u : ℂ → ℂ, ContDiff ℝ ∞ u →
      ContDiff ℝ ∞ (fun ζ => dz u ζ) ∧ ContDiff ℝ ∞ (fun ζ => dzbar u ζ) := by
    intro u hu
    have hfderiv_cinf : ContDiff ℝ ∞ (fun ζ => fderiv ℝ u ζ) :=
      hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    constructor
    · have hcomp : (fun ζ => dz u ζ)
          = (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I))
            ∘ (fun ζ => fderiv ℝ u ζ) := by funext ζ; rfl
      have hΦ : ContDiff ℝ ∞
          (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I)) := by
        have hΦ_lin : (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I))
            = (fun D : ℂ →L[ℝ] ℂ =>
                (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) D
                  - Complex.I • ContinuousLinearMap.apply ℝ ℂ Complex.I D)) := by
          funext D; simp [ContinuousLinearMap.apply_apply, smul_eq_mul]
        rw [hΦ_lin]
        exact (((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).contDiff).sub
          ((ContinuousLinearMap.apply ℝ ℂ Complex.I).contDiff.const_smul Complex.I)).const_smul _
      rw [hcomp]; exact hΦ.comp hfderiv_cinf
    · have hcomp : (fun ζ => dzbar u ζ)
          = (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 + Complex.I * D Complex.I))
            ∘ (fun ζ => fderiv ℝ u ζ) := by funext ζ; rfl
      have hΦ : ContDiff ℝ ∞
          (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 + Complex.I * D Complex.I)) := by
        have hΦ_lin : (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 + Complex.I * D Complex.I))
            = (fun D : ℂ →L[ℝ] ℂ =>
                (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) D
                  + Complex.I • ContinuousLinearMap.apply ℝ ℂ Complex.I D)) := by
          funext D; simp [ContinuousLinearMap.apply_apply, smul_eq_mul]
        rw [hΦ_lin]
        exact (((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).contDiff).add
          ((ContinuousLinearMap.apply ℝ ℂ Complex.I).contDiff.const_smul Complex.I)).const_smul _
      rw [hcomp]; exact hΦ.comp hfderiv_cinf
  -- ===== `dz`/`dzbar` of a compactly supported function are compactly supported. =====
  have hdz_cs : ∀ u : ℂ → ℂ, HasCompactSupport u →
      HasCompactSupport (fun ζ => dz u ζ) ∧ HasCompactSupport (fun ζ => dzbar u ζ) := by
    intro u huc
    have hfderiv_cs : HasCompactSupport (fun ζ => fderiv ℝ u ζ) := huc.fderiv (𝕜 := ℝ)
    constructor
    · have hcomp : (fun ζ => dz u ζ)
          = (fun D : ℂ →L[ℝ] ℂ => (1/2 : ℂ) * (D 1 - I * D I)) ∘ (fun ζ => fderiv ℝ u ζ) := by
        funext ζ; rfl
      rw [hcomp]; exact hfderiv_cs.comp_left (by simp)
    · have hcomp : (fun ζ => dzbar u ζ)
          = (fun D : ℂ →L[ℝ] ℂ => (1/2 : ℂ) * (D 1 + I * D I)) ∘ (fun ζ => fderiv ℝ u ζ) := by
        funext ζ; rfl
      rw [hcomp]; exact hfderiv_cs.comp_left (by simp)
  -- ===== Derivatives vanish where the function vanishes on the outer region. =====
  have hvanish : ∀ (u : ℂ → ℂ), (∀ z, R < ‖z‖ → u z = 0) → ∀ z, R < ‖z‖ →
      dz u z = 0 ∧ dzbar u z = 0 := by
    intro u hu z hz
    have hopen : IsOpen {w : ℂ | R < ‖w‖} := isOpen_lt continuous_const continuous_norm
    have hev : u =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hz) (fun w hw => hu w hw)
    have hfd : fderiv ℝ u z = 0 := by
      rw [hev.fderiv_eq]; exact fderiv_const_apply 0
    constructor <;> simp [dz, dzbar, hfd]
  -- ===== The Neumann iterates. =====
  set T : (ℂ → ℂ) → (ℂ → ℂ) := fun w z => μ z * beurling w z with hTdef
  set v : ℕ → ℂ → ℂ := fun n => T^[n] g with hvdef
  have hvsucc : ∀ n, v (n + 1) = fun z => μ z * beurling (v n) z := by
    intro n
    simp only [hvdef]
    rw [Function.iterate_succ_apply']
  have hvprop : ∀ n, ContDiff ℝ ∞ (v n) ∧ HasCompactSupport (v n) ∧
      ∀ z, R < ‖z‖ → v n z = 0 := by
    intro n
    induction n with
    | zero => exact ⟨hgs, hgc, fun z hz => (hsupp z hz).2⟩
    | succ n ih =>
      obtain ⟨hsm, hcs, hvan⟩ := ih
      rw [hvsucc n]
      refine ⟨hμs.mul (contDiff_beurling hsm hcs), hμc.mul_right, ?_⟩
      intro z hz; simp only [(hsupp z hz).1, zero_mul]
  -- ===== Smooth identities: `S u = P (∂u)`, `∂(S u) = S (∂u)`, `∂̄(S u) = ∂u`. =====
  have hdzS : ∀ (u : ℂ → ℂ), ContDiff ℝ ∞ u → HasCompactSupport u → ∀ z,
      dz (fun w => beurling u w) z = beurling (fun ζ => dz u ζ) z ∧
      dzbar (fun w => beurling u w) z = dz u z := by
    intro u hu huc z
    have hdzu_sm : ContDiff ℝ ∞ (fun ζ => dz u ζ) := (hdz_sm u hu).1
    have hdzu_cs : HasCompactSupport (fun ζ => dz u ζ) := (hdz_cs u huc).1
    have hdzu1 : ContDiff ℝ 1 (fun ζ => dz u ζ) :=
      hdzu_sm.of_le (by exact_mod_cast le_top)
    have hfun : (fun w => beurling u w) = cauchyTransform (fun ζ => dz u ζ) := by
      funext w; exact beurling_eq_cauchyTransform_dz hu huc w
    rw [hfun]
    exact ⟨beurling_eq_dz_cauchyTransform hdzu1 hdzu_cs z,
      dzbar_cauchyTransform hdzu1 hdzu_cs z⟩
  -- ===== First-derivative recursion. =====
  have hrec : ∀ n z,
      dz (v (n + 1)) z
        = dz μ z * beurling (v n) z + μ z * beurling (fun ζ => dz (v n) ζ) z ∧
      dzbar (v (n + 1)) z
        = dzbar μ z * beurling (v n) z + μ z * dz (v n) z := by
    intro n z
    obtain ⟨hsm, hcs, _⟩ := hvprop n
    have hμd : DifferentiableAt ℝ μ z := hd1 hμs z
    have hSd : DifferentiableAt ℝ (fun w => beurling (v n) w) z :=
      hd1 (contDiff_beurling hsm hcs) z
    have hzz := hdzS (v n) hsm hcs z
    rw [hvsucc n]
    constructor
    · rw [dz_mul hμd hSd, hzz.1]; ring
    · rw [dzbar_mul hμd hSd, hzz.2]; ring
  -- ===== Second-derivative recursion. =====
  have hrec2 : ∀ n z,
      dz (fun ζ => dz (v (n + 1)) ζ) z
        = dz (fun ζ => dz μ ζ) z * beurling (v n) z
          + dz μ z * beurling (fun ζ => dz (v n) ζ) z
          + (dz μ z * beurling (fun ζ => dz (v n) ζ) z
            + μ z * beurling (fun ζ => dz (fun w => dz (v n) w) ζ) z) := by
    intro n z
    obtain ⟨hsm, hcs, _⟩ := hvprop n
    have hdzvn_sm : ContDiff ℝ ∞ (fun ζ => dz (v n) ζ) := (hdz_sm (v n) hsm).1
    have hdzvn_cs : HasCompactSupport (fun ζ => dz (v n) ζ) := (hdz_cs (v n) hcs).1
    have hfun : (fun ζ => dz (v (n + 1)) ζ)
        = fun ζ => dz μ ζ * beurling (v n) ζ + μ ζ * beurling (fun w => dz (v n) w) ζ := by
      funext ζ; exact (hrec n ζ).1
    rw [hfun]
    have hμd : DifferentiableAt ℝ (fun ζ => dz μ ζ) z := hd1 (hdz_sm μ hμs).1 z
    have hμd' : DifferentiableAt ℝ μ z := hd1 hμs z
    have hS1 : DifferentiableAt ℝ (fun w => beurling (v n) w) z :=
      hd1 (contDiff_beurling hsm hcs) z
    have hS2 : DifferentiableAt ℝ (fun w => beurling (fun ζ => dz (v n) ζ) w) z :=
      hd1 (contDiff_beurling hdzvn_sm hdzvn_cs) z
    have hprod1 : DifferentiableAt ℝ (fun ζ => dz μ ζ * beurling (v n) ζ) z :=
      hμd.mul hS1
    have hprod2 : DifferentiableAt ℝ
        (fun ζ => μ ζ * beurling (fun w => dz (v n) w) ζ) z := hμd'.mul hS2
    rw [dz_add hprod1 hprod2, dz_mul hμd hS1, dz_mul hμd' hS2,
      (hdzS (v n) hsm hcs z).1, (hdzS (fun ζ => dz (v n) ζ) hdzvn_sm hdzvn_cs z).1]
    ring
  -- ===== Sup-norm bounds for the fixed smooth data. =====
  obtain ⟨M₀, hM₀⟩ := hμs.continuous.bounded_above_of_compact_support hμc
  obtain ⟨M₁, hM₁⟩ :=
    (hdz_sm μ hμs).1.continuous.bounded_above_of_compact_support (hdz_cs μ hμc).1
  obtain ⟨M₂, hM₂⟩ := ((hdz_sm (fun ζ => dz μ ζ)
    (hdz_sm μ hμs).1).1).continuous.bounded_above_of_compact_support
    ((hdz_cs (fun ζ => dz μ ζ) (hdz_cs μ hμc).1).1)
  obtain ⟨M₃, hM₃⟩ :=
    (hdz_sm μ hμs).2.continuous.bounded_above_of_compact_support (hdz_cs μ hμc).2
  have hM₀0 : 0 ≤ M₀ := le_trans (norm_nonneg _) (hM₀ 0)
  have hM₁0 : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0)
  have hM₂0 : 0 ≤ M₂ := le_trans (norm_nonneg _) (hM₂ 0)
  have hM₃0 : 0 ≤ M₃ := le_trans (norm_nonneg _) (hM₃ 0)
  -- ===== `MemLp` for continuous compactly supported functions. =====
  have hmem : ∀ (u : ℂ → ℂ), Continuous u → HasCompactSupport u → MemLp u p volume :=
    fun u hu huc => hu.memLp_of_hasCompactSupport huc
  have hvmem : ∀ n, MemLp (v n) p volume := fun n =>
    hmem _ (hvprop n).1.continuous (hvprop n).2.1
  have hdzvmem : ∀ n, MemLp (fun ζ => dz (v n) ζ) p volume := fun n =>
    hmem _ ((hdz_sm _ (hvprop n).1).1).continuous ((hdz_cs _ (hvprop n).2.1).1)
  have hdz2vmem : ∀ n, MemLp (fun ζ => dz (fun w => dz (v n) w) ζ) p volume := fun n =>
    hmem _ ((hdz_sm _ ((hdz_sm _ (hvprop n).1).1)).1).continuous
      ((hdz_cs _ ((hdz_cs _ (hvprop n).2.1).1)).1)
  -- ===== a.e. bound `‖μ‖ ≤ k`. =====
  have hμ_ae : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k := by
    have h1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ₑ ≤ eLpNormEssSup μ volume :=
      ae_le_eLpNormEssSup
    have hfin : eLpNormEssSup μ volume ≠ ⊤ := by
      have h2 := (memLp_top_of_continuous_hasCompactSupport hμs.continuous hμc).2
      rw [eLpNorm_exponent_top] at h2
      exact h2.ne
    filter_upwards [h1] with z hz
    rw [← ofReal_norm] at hz
    have h3 := ENNReal.toReal_mono hfin hz
    rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at h3
  -- ===== `Lᵖ` multiplication bound by an a.e.-bounded factor. =====
  have hmul : ∀ (afn h : ℂ → ℂ) (M : ℝ), 0 ≤ M →
      (∀ᵐ z ∂(volume : Measure ℂ), ‖afn z‖ ≤ M) →
      eLpNorm (fun z => afn z * h z) p volume
        ≤ ENNReal.ofReal M * eLpNorm h p volume := by
    intro afn h M hM0 hb
    have hMnorm : ‖(M : ℂ)‖ = M := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM0]
    have hpt : ∀ᵐ z ∂(volume : Measure ℂ), ‖afn z * h z‖ ≤ ‖(M : ℂ) * h z‖ := by
      filter_upwards [hb] with z hz
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (hz.trans (le_of_eq hMnorm.symm)) (norm_nonneg _)
    calc eLpNorm (fun z => afn z * h z) p volume
        ≤ eLpNorm (fun z => (M : ℂ) * h z) p volume := eLpNorm_mono_ae hpt
      _ = ‖(M : ℂ)‖ₑ * eLpNorm h p volume := by
          have heq : (fun z => (M : ℂ) * h z) = (M : ℂ) • h := by
            funext z; rw [Pi.smul_apply, smul_eq_mul]
          rw [heq, eLpNorm_const_smul]
      _ = ENNReal.ofReal M * eLpNorm h p volume := by
          rw [← ofReal_norm, hMnorm]
  -- ===== The core term bound: `‖a·S u‖ₚ ≤ (M·C)·‖u‖ₚ`. =====
  have hterm : ∀ (M : ℝ) (afn u : ℂ → ℂ), 0 ≤ M →
      (∀ᵐ z ∂(volume : Measure ℂ), ‖afn z‖ ≤ M) → MemLp u p volume →
      eLpNorm (fun z => afn z * beurling u z) p volume
        ≤ ENNReal.ofReal (M * C) * eLpNorm u p volume := by
    intro M afn u hM0 hb hu
    calc eLpNorm (fun z => afn z * beurling u z) p volume
        ≤ ENNReal.ofReal M * eLpNorm (beurling u) p volume := hmul afn _ M hM0 hb
      _ ≤ ENNReal.ofReal M * (ENNReal.ofReal C * eLpNorm u p volume) :=
          mul_le_mul_right (hCb.2 u hu) _
      _ = ENNReal.ofReal (M * C) * eLpNorm u p volume := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hM0]
  -- ===== The real-valued `Lᵖ` norms of the cascade. =====
  set a : ℕ → ℝ := fun n => (eLpNorm (v n) p volume).toReal with hadef
  set b : ℕ → ℝ := fun n => (eLpNorm (fun ζ => dz (v n) ζ) p volume).toReal with hbdef
  set c : ℕ → ℝ :=
    fun n => (eLpNorm (fun ζ => dz (fun w => dz (v n) w) ζ) p volume).toReal with hcdef
  have haN : ∀ n, 0 ≤ a n := fun n => ENNReal.toReal_nonneg
  have hbN : ∀ n, 0 ≤ b n := fun n => ENNReal.toReal_nonneg
  have hcN : ∀ n, 0 ≤ c n := fun n => ENNReal.toReal_nonneg
  -- Level 0: `a (n+1) ≤ (k·C)·a n`.
  have hab : ∀ n, a (n + 1) ≤ (k * C) * a n := by
    intro n
    have h1 : eLpNorm (v (n + 1)) p volume
        ≤ ENNReal.ofReal (k * C) * eLpNorm (v n) p volume := by
      rw [hvsucc n]; exact hterm k μ (v n) hk0 hμ_ae (hvmem n)
    have h2 := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hvmem n).2.ne) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hr0] at h2
  -- Level 1: `b (n+1) ≤ M₁·C·a n + (k·C)·b n`.
  have hbb : ∀ n, b (n + 1) ≤ M₁ * C * a n + (k * C) * b n := by
    intro n
    obtain ⟨hsm, hcs, _⟩ := hvprop n
    have hfun : (fun ζ => dz (v (n + 1)) ζ)
        = fun ζ => dz μ ζ * beurling (v n) ζ
            + μ ζ * beurling (fun w => dz (v n) w) ζ := by
      funext ζ; exact (hrec n ζ).1
    have hcont1 : Continuous (fun ζ => dz μ ζ * beurling (v n) ζ) :=
      (hdz_sm μ hμs).1.continuous.mul (contDiff_beurling hsm hcs).continuous
    have hcont2 : Continuous (fun ζ => μ ζ * beurling (fun w => dz (v n) w) ζ) :=
      hμs.continuous.mul (contDiff_beurling (hdz_sm _ hsm).1 (hdz_cs _ hcs).1).continuous
    have hadd : eLpNorm (fun ζ => dz (v (n + 1)) ζ) p volume
        ≤ ENNReal.ofReal (M₁ * C) * eLpNorm (v n) p volume
          + ENNReal.ofReal (k * C) * eLpNorm (fun w => dz (v n) w) p volume := by
      rw [hfun]
      refine le_trans
        (eLpNorm_add_le hcont1.aestronglyMeasurable hcont2.aestronglyMeasurable hp1) ?_
      exact add_le_add
        (hterm M₁ _ _ hM₁0 (Filter.Eventually.of_forall hM₁) (hvmem n))
        (hterm k μ _ hk0 hμ_ae (hdzvmem n))
    have hne1 : ENNReal.ofReal (M₁ * C) * eLpNorm (v n) p volume ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hvmem n).2.ne
    have hne2 : ENNReal.ofReal (k * C) * eLpNorm (fun w => dz (v n) w) p volume ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hdzvmem n).2.ne
    have h2 := ENNReal.toReal_mono (by
      rw [ENNReal.add_ne_top]; exact ⟨hne1, hne2⟩) hadd
    rwa [ENNReal.toReal_add hne1 hne2, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (mul_nonneg hM₁0 hC0), ENNReal.toReal_ofReal hr0] at h2
  -- Level 2: `c (n+1) ≤ M₂·C·a n + M₁·C·b n + (M₁·C·b n + (k·C)·c n)`.
  have hcc : ∀ n, c (n + 1)
      ≤ (M₂ * C * a n + M₁ * C * b n) + (M₁ * C * b n + (k * C) * c n) := by
    intro n
    obtain ⟨hsm, hcs, _⟩ := hvprop n
    have hdzvn_sm : ContDiff ℝ ∞ (fun ζ => dz (v n) ζ) := (hdz_sm (v n) hsm).1
    have hdzvn_cs : HasCompactSupport (fun ζ => dz (v n) ζ) := (hdz_cs (v n) hcs).1
    have hfun : (fun ζ => dz (fun w => dz (v (n + 1)) w) ζ)
        = fun ζ => (dz (fun w => dz μ w) ζ * beurling (v n) ζ
            + dz μ ζ * beurling (fun w => dz (v n) w) ζ)
          + (dz μ ζ * beurling (fun w => dz (v n) w) ζ
            + μ ζ * beurling (fun w => dz (fun t => dz (v n) t) w) ζ) := by
      funext ζ
      exact hrec2 n ζ
    have hcA : Continuous (fun ζ => dz (fun w => dz μ w) ζ * beurling (v n) ζ) :=
      ((hdz_sm _ (hdz_sm μ hμs).1).1).continuous.mul
        (contDiff_beurling hsm hcs).continuous
    have hcB : Continuous (fun ζ => dz μ ζ * beurling (fun w => dz (v n) w) ζ) :=
      (hdz_sm μ hμs).1.continuous.mul
        (contDiff_beurling hdzvn_sm hdzvn_cs).continuous
    have hcC : Continuous
        (fun ζ => μ ζ * beurling (fun w => dz (fun t => dz (v n) t) w) ζ) :=
      hμs.continuous.mul (contDiff_beurling (hdz_sm _ hdzvn_sm).1
        (hdz_cs _ hdzvn_cs).1).continuous
    have htA : eLpNorm (fun ζ => dz (fun w => dz μ w) ζ * beurling (v n) ζ) p volume
        ≤ ENNReal.ofReal (M₂ * C) * eLpNorm (v n) p volume :=
      hterm M₂ _ _ hM₂0 (Filter.Eventually.of_forall hM₂) (hvmem n)
    have htB : eLpNorm (fun ζ => dz μ ζ * beurling (fun w => dz (v n) w) ζ) p volume
        ≤ ENNReal.ofReal (M₁ * C) * eLpNorm (fun w => dz (v n) w) p volume :=
      hterm M₁ _ _ hM₁0 (Filter.Eventually.of_forall hM₁) (hdzvmem n)
    have htC : eLpNorm
        (fun ζ => μ ζ * beurling (fun w => dz (fun t => dz (v n) t) w) ζ) p volume
        ≤ ENNReal.ofReal (k * C)
            * eLpNorm (fun w => dz (fun t => dz (v n) t) w) p volume :=
      hterm k μ _ hk0 hμ_ae (hdz2vmem n)
    have hadd : eLpNorm (fun ζ => dz (fun w => dz (v (n + 1)) w) ζ) p volume
        ≤ (ENNReal.ofReal (M₂ * C) * eLpNorm (v n) p volume
            + ENNReal.ofReal (M₁ * C) * eLpNorm (fun w => dz (v n) w) p volume)
          + (ENNReal.ofReal (M₁ * C) * eLpNorm (fun w => dz (v n) w) p volume
            + ENNReal.ofReal (k * C)
                * eLpNorm (fun w => dz (fun t => dz (v n) t) w) p volume) := by
      rw [hfun]
      refine le_trans (eLpNorm_add_le
        (hcA.add hcB).aestronglyMeasurable (hcB.add hcC).aestronglyMeasurable hp1) ?_
      refine add_le_add ?_ ?_
      · exact le_trans (eLpNorm_add_le hcA.aestronglyMeasurable
          hcB.aestronglyMeasurable hp1) (add_le_add htA htB)
      · exact le_trans (eLpNorm_add_le hcB.aestronglyMeasurable
          hcC.aestronglyMeasurable hp1) (add_le_add htB htC)
    have hneA : ENNReal.ofReal (M₂ * C) * eLpNorm (v n) p volume ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hvmem n).2.ne
    have hneB : ENNReal.ofReal (M₁ * C) * eLpNorm (fun w => dz (v n) w) p volume ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hdzvmem n).2.ne
    have hneC : ENNReal.ofReal (k * C)
        * eLpNorm (fun w => dz (fun t => dz (v n) t) w) p volume ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hdz2vmem n).2.ne
    have hneAB : ENNReal.ofReal (M₂ * C) * eLpNorm (v n) p volume
        + ENNReal.ofReal (M₁ * C) * eLpNorm (fun w => dz (v n) w) p volume ≠ ⊤ := by
      rw [ENNReal.add_ne_top]; exact ⟨hneA, hneB⟩
    have hneBC : ENNReal.ofReal (M₁ * C) * eLpNorm (fun w => dz (v n) w) p volume
        + ENNReal.ofReal (k * C)
            * eLpNorm (fun w => dz (fun t => dz (v n) t) w) p volume ≠ ⊤ := by
      rw [ENNReal.add_ne_top]; exact ⟨hneB, hneC⟩
    have h2 := ENNReal.toReal_mono (by
      rw [ENNReal.add_ne_top]; exact ⟨hneAB, hneBC⟩) hadd
    rwa [ENNReal.toReal_add hneAB hneBC, ENNReal.toReal_add hneA hneB,
      ENNReal.toReal_add hneB hneC, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hM₂0 hC0),
      ENNReal.toReal_ofReal (mul_nonneg hM₁0 hC0), ENNReal.toReal_ofReal hr0] at h2
  -- ===== Geometric decay with margin: `a n, b n, c n ≤ Dᵢ · r'^n`. =====
  have hr'pow : ∀ n : ℕ, (0 : ℝ) ≤ r' ^ n := fun n => pow_nonneg hr'0.le n
  set D₀ : ℝ := a 0 with hD₀def
  have hD₀0 : 0 ≤ D₀ := haN 0
  have haD : ∀ n, a n ≤ D₀ * r' ^ n := by
    intro n
    induction n with
    | zero => simp [hD₀def]
    | succ n ih =>
      calc a (n + 1) ≤ (k * C) * a n := hab n
        _ ≤ (k * C) * (D₀ * r' ^ n) := mul_le_mul_of_nonneg_left ih hr0
        _ ≤ r' * (D₀ * r' ^ n) :=
            mul_le_mul_of_nonneg_right hrr'.le (mul_nonneg hD₀0 (hr'pow n))
        _ = D₀ * r' ^ (n + 1) := by ring
  set D₁ : ℝ := b 0 + M₁ * C * D₀ / δ with hD₁def
  have hD₁0 : 0 ≤ D₁ :=
    add_nonneg (hbN 0) (div_nonneg (mul_nonneg (mul_nonneg hM₁0 hC0) hD₀0) hδ0.le)
  have hδD₁ : M₁ * C * D₀ ≤ δ * D₁ := by
    rw [hD₁def, mul_add, mul_div_cancel₀ _ hδ0.ne']
    nlinarith [mul_nonneg hδ0.le (hbN 0)]
  have hbD : ∀ n, b n ≤ D₁ * r' ^ n := by
    intro n
    induction n with
    | zero =>
      have h0 : 0 ≤ M₁ * C * D₀ / δ :=
        div_nonneg (mul_nonneg (mul_nonneg hM₁0 hC0) hD₀0) hδ0.le
      rw [pow_zero, mul_one, hD₁def]
      linarith
    | succ n ih =>
      calc b (n + 1) ≤ M₁ * C * a n + (k * C) * b n := hbb n
        _ ≤ M₁ * C * (D₀ * r' ^ n) + (k * C) * (D₁ * r' ^ n) :=
            add_le_add (mul_le_mul_of_nonneg_left (haD n) (mul_nonneg hM₁0 hC0))
              (mul_le_mul_of_nonneg_left ih hr0)
        _ = (M₁ * C * D₀ + (k * C) * D₁) * r' ^ n := by ring
        _ ≤ (δ * D₁ + (k * C) * D₁) * r' ^ n := by
            refine mul_le_mul_of_nonneg_right ?_ (hr'pow n)
            exact add_le_add hδD₁ le_rfl
        _ = D₁ * r' ^ (n + 1) := by rw [hδdef]; ring
  set D₂ : ℝ := c 0 + (M₂ * C * D₀ + 2 * (M₁ * C) * D₁) / δ with hD₂def
  have hnum2 : 0 ≤ M₂ * C * D₀ + 2 * (M₁ * C) * D₁ := by
    have h1 : 0 ≤ M₂ * C * D₀ := mul_nonneg (mul_nonneg hM₂0 hC0) hD₀0
    have h2 : 0 ≤ 2 * (M₁ * C) * D₁ :=
      mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hM₁0 hC0)) hD₁0
    linarith
  have hD₂0 : 0 ≤ D₂ := add_nonneg (hcN 0) (div_nonneg hnum2 hδ0.le)
  have hδD₂ : M₂ * C * D₀ + 2 * (M₁ * C) * D₁ ≤ δ * D₂ := by
    have hexp : δ * D₂ = δ * c 0 + (M₂ * C * D₀ + 2 * (M₁ * C) * D₁) := by
      rw [hD₂def, mul_add, mul_div_cancel₀ _ hδ0.ne']
    rw [hexp]
    have h0 : 0 ≤ δ * c 0 := mul_nonneg hδ0.le (hcN 0)
    linarith
  have hcD : ∀ n, c n ≤ D₂ * r' ^ n := by
    intro n
    induction n with
    | zero =>
      have h0 : 0 ≤ (M₂ * C * D₀ + 2 * (M₁ * C) * D₁) / δ := div_nonneg hnum2 hδ0.le
      rw [pow_zero, mul_one, hD₂def]
      linarith
    | succ n ih =>
      calc c (n + 1)
          ≤ (M₂ * C * a n + M₁ * C * b n) + (M₁ * C * b n + (k * C) * c n) := hcc n
        _ ≤ (M₂ * C * (D₀ * r' ^ n) + M₁ * C * (D₁ * r' ^ n))
              + (M₁ * C * (D₁ * r' ^ n) + (k * C) * (D₂ * r' ^ n)) := by
            refine add_le_add (add_le_add ?_ ?_) (add_le_add ?_ ?_)
            · exact mul_le_mul_of_nonneg_left (haD n) (mul_nonneg hM₂0 hC0)
            · exact mul_le_mul_of_nonneg_left (hbD n) (mul_nonneg hM₁0 hC0)
            · exact mul_le_mul_of_nonneg_left (hbD n) (mul_nonneg hM₁0 hC0)
            · exact mul_le_mul_of_nonneg_left ih hr0
        _ = (M₂ * C * D₀ + 2 * (M₁ * C) * D₁ + (k * C) * D₂) * r' ^ n := by ring
        _ ≤ (δ * D₂ + (k * C) * D₂) * r' ^ n := by
            refine mul_le_mul_of_nonneg_right ?_ (hr'pow n)
            nlinarith
        _ = D₂ * r' ^ (n + 1) := by rw [hδdef]; ring
  -- ===== The uniform sup bound for the Cauchy transform. =====
  obtain ⟨CR, hCR0, hCR⟩ := norm_cauchyTransform_le_of_memLp_support (R := R) hp hp'
  -- Vanishing of iterate derivatives outside the support ball.
  have hdzv_van : ∀ n, ∀ z, R < ‖z‖ → dz (v n) z = 0 := fun n z hz =>
    (hvanish (v n) (hvprop n).2.2 z hz).1
  have hdbv_van : ∀ n, ∀ z, R < ‖z‖ → dzbar (v n) z = 0 := fun n z hz =>
    (hvanish (v n) (hvprop n).2.2 z hz).2
  -- Sup bound for `S u` through the potential bound: `‖S u‖∞ ≤ CR·‖∂u‖ₚ`.
  have hSsup : ∀ (u : ℂ → ℂ), ContDiff ℝ ∞ u → HasCompactSupport u →
      (∀ z, R < ‖z‖ → u z = 0) → ∀ z,
      ‖beurling u z‖ ≤ CR * (eLpNorm (fun ζ => dz u ζ) p volume).toReal := by
    intro u hu huc huv z
    rw [beurling_eq_cauchyTransform_dz hu huc z]
    exact hCR _ (hmem _ ((hdz_sm u hu).1).continuous ((hdz_cs u huc).1))
      (fun w hw => (hvanish u huv w hw).1) z
  -- Sup decay of the transforms of the iterates.
  have hsupS : ∀ n z, ‖beurling (v n) z‖ ≤ CR * (D₁ * r' ^ n) := by
    intro n z
    refine le_trans (hSsup (v n) (hvprop n).1 (hvprop n).2.1 (hvprop n).2.2 z) ?_
    exact mul_le_mul_of_nonneg_left (hbD n) hCR0
  have hsupSdz : ∀ n z, ‖beurling (fun ζ => dz (v n) ζ) z‖ ≤ CR * (D₂ * r' ^ n) := by
    intro n z
    refine le_trans (hSsup (fun ζ => dz (v n) ζ) ((hdz_sm _ (hvprop n).1).1)
      ((hdz_cs _ (hvprop n).2.1).1) (hdzv_van n) z) ?_
    exact mul_le_mul_of_nonneg_left (hcD n) hCR0
  -- Sup bounds for the data `g`.
  obtain ⟨Mg, hMg⟩ := hgs.continuous.bounded_above_of_compact_support hgc
  obtain ⟨Mg₁, hMg₁⟩ :=
    ((hdz_sm g hgs).1).continuous.bounded_above_of_compact_support ((hdz_cs g hgc).1)
  obtain ⟨Mg₂, hMg₂⟩ :=
    ((hdz_sm g hgs).2).continuous.bounded_above_of_compact_support ((hdz_cs g hgc).2)
  have hMg0 : 0 ≤ Mg := le_trans (norm_nonneg _) (hMg 0)
  have hMg₁0 : 0 ≤ Mg₁ := le_trans (norm_nonneg _) (hMg₁ 0)
  have hMg₂0 : 0 ≤ Mg₂ := le_trans (norm_nonneg _) (hMg₂ 0)
  -- ===== Geometric sup decay of the iterates and their first derivatives. =====
  set Kv : ℝ := max Mg (M₀ * (CR * D₁) / r') with hKvdef
  have hKv0 : 0 ≤ Kv := le_trans hMg0 (le_max_left _ _)
  have hKv : ∀ n z, ‖v n z‖ ≤ Kv * r' ^ n := by
    intro n z
    cases n with
    | zero =>
      rw [pow_zero, mul_one]
      exact le_trans (hMg z) (le_max_left _ _)
    | succ n =>
      have h1 : v (n + 1) z = μ z * beurling (v n) z := congrFun (hvsucc n) z
      rw [h1, norm_mul]
      calc ‖μ z‖ * ‖beurling (v n) z‖
          ≤ M₀ * (CR * (D₁ * r' ^ n)) :=
            mul_le_mul (hM₀ z) (hsupS n z) (norm_nonneg _) hM₀0
        _ = (M₀ * (CR * D₁) / r') * r' ^ (n + 1) := by
            rw [pow_succ]; field_simp
        _ ≤ Kv * r' ^ (n + 1) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (hr'pow (n + 1))
  set Kdz : ℝ := max Mg₁ ((M₁ * (CR * D₁) + M₀ * (CR * D₂)) / r') with hKdzdef
  have hKdz0 : 0 ≤ Kdz := le_trans hMg₁0 (le_max_left _ _)
  have hKdz : ∀ n z, ‖dz (v n) z‖ ≤ Kdz * r' ^ n := by
    intro n z
    cases n with
    | zero =>
      rw [pow_zero, mul_one]
      exact le_trans (hMg₁ z) (le_max_left _ _)
    | succ n =>
      rw [(hrec n z).1]
      calc ‖dz μ z * beurling (v n) z + μ z * beurling (fun ζ => dz (v n) ζ) z‖
          ≤ ‖dz μ z * beurling (v n) z‖
            + ‖μ z * beurling (fun ζ => dz (v n) ζ) z‖ := norm_add_le _ _
        _ = ‖dz μ z‖ * ‖beurling (v n) z‖
            + ‖μ z‖ * ‖beurling (fun ζ => dz (v n) ζ) z‖ := by rw [norm_mul, norm_mul]
        _ ≤ M₁ * (CR * (D₁ * r' ^ n)) + M₀ * (CR * (D₂ * r' ^ n)) :=
            add_le_add (mul_le_mul (hM₁ z) (hsupS n z) (norm_nonneg _) hM₁0)
              (mul_le_mul (hM₀ z) (hsupSdz n z) (norm_nonneg _) hM₀0)
        _ = ((M₁ * (CR * D₁) + M₀ * (CR * D₂)) / r') * r' ^ (n + 1) := by
            rw [pow_succ]; field_simp
        _ ≤ Kdz * r' ^ (n + 1) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (hr'pow (n + 1))
  set Kdb : ℝ := max Mg₂ ((M₃ * (CR * D₁) + M₀ * Kdz) / r') with hKdbdef
  have hKdb0 : 0 ≤ Kdb := le_trans hMg₂0 (le_max_left _ _)
  have hKdb : ∀ n z, ‖dzbar (v n) z‖ ≤ Kdb * r' ^ n := by
    intro n z
    cases n with
    | zero =>
      rw [pow_zero, mul_one]
      exact le_trans (hMg₂ z) (le_max_left _ _)
    | succ n =>
      rw [(hrec n z).2]
      calc ‖dzbar μ z * beurling (v n) z + μ z * dz (v n) z‖
          ≤ ‖dzbar μ z * beurling (v n) z‖ + ‖μ z * dz (v n) z‖ := norm_add_le _ _
        _ = ‖dzbar μ z‖ * ‖beurling (v n) z‖ + ‖μ z‖ * ‖dz (v n) z‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ M₃ * (CR * (D₁ * r' ^ n)) + M₀ * (Kdz * r' ^ n) :=
            add_le_add (mul_le_mul (hM₃ z) (hsupS n z) (norm_nonneg _) hM₃0)
              (mul_le_mul (hM₀ z) (hKdz n z) (norm_nonneg _) hM₀0)
        _ = ((M₃ * (CR * D₁) + M₀ * Kdz) / r') * r' ^ (n + 1) := by
            rw [pow_succ]; field_simp
        _ ≤ Kdb * r' ^ (n + 1) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (hr'pow (n + 1))
  -- ===== Summability of the geometric envelopes. =====
  have hgeom : Summable (fun n : ℕ => r' ^ n) :=
    summable_geometric_of_lt_one hr'0.le hr'1
  have hsum_v : Summable (fun n => Kv * r' ^ n) := hgeom.mul_left Kv
  have hsum_dz : Summable (fun n => Kdz * r' ^ n) := hgeom.mul_left Kdz
  have hsum_db : Summable (fun n => Kdb * r' ^ n) := hgeom.mul_left Kdb
  -- ===== The limit functions. =====
  set φ : ℂ → ℂ := fun z => ∑' n, v n z with hφdef
  set u₁ : ℂ → ℂ := fun z => ∑' n, dz (v n) z with hu₁def
  set u₂ : ℂ → ℂ := fun z => ∑' n, dzbar (v n) z with hu₂def
  have hφcont : Continuous φ :=
    continuous_tsum (fun n => (hvprop n).1.continuous) hsum_v (fun n z => hKv n z)
  have hu₁cont : Continuous u₁ :=
    continuous_tsum (fun n => ((hdz_sm _ (hvprop n).1).1).continuous) hsum_dz
      (fun n z => hKdz n z)
  have hu₂cont : Continuous u₂ :=
    continuous_tsum (fun n => ((hdz_sm _ (hvprop n).1).2).continuous) hsum_db
      (fun n z => hKdb n z)
  have hφvan : ∀ z, R < ‖z‖ → φ z = 0 := by
    intro z hz
    have h0 : ∀ n, v n z = 0 := fun n => (hvprop n).2.2 z hz
    simp only [hφdef]
    rw [tsum_congr h0, tsum_zero]
  have hu₁van : ∀ z, R < ‖z‖ → u₁ z = 0 := by
    intro z hz
    have h0 : ∀ n, dz (v n) z = 0 := fun n => hdzv_van n z hz
    simp only [hu₁def]
    rw [tsum_congr h0, tsum_zero]
  have hu₂van : ∀ z, R < ‖z‖ → u₂ z = 0 := by
    intro z hz
    have h0 : ∀ n, dzbar (v n) z = 0 := fun n => hdbv_van n z hz
    simp only [hu₂def]
    rw [tsum_congr h0, tsum_zero]
  have hcs_of_van : ∀ (u : ℂ → ℂ), (∀ z, R < ‖z‖ → u z = 0) → HasCompactSupport u := by
    intro u huv
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R) ?_
    intro x hx
    refine huv x ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact hx
  have hφcs : HasCompactSupport φ := hcs_of_van φ hφvan
  have hu₁cs : HasCompactSupport u₁ := hcs_of_van u₁ hu₁van
  have hφmem : MemLp φ p volume := hmem φ hφcont hφcs
  -- ===== Partial sums and their Wirtinger derivatives. =====
  set s : ℕ → ℂ → ℂ := fun m z => ∑ n ∈ Finset.range m, v n z with hsdef
  set ds : ℕ → ℂ → ℂ := fun m z => ∑ n ∈ Finset.range m, dz (v n) z with hdsdef
  set db : ℕ → ℂ → ℂ := fun m z => ∑ n ∈ Finset.range m, dzbar (v n) z with hdbdef
  have hs_succ : ∀ m, s (m + 1) = fun z => s m z + v m z := by
    intro m; funext z; simp only [hsdef]; rw [Finset.sum_range_succ]
  have hds_succ : ∀ m z, ds (m + 1) z = ds m z + dz (v m) z := by
    intro m z; simp only [hdsdef]; rw [Finset.sum_range_succ]
  have hdb_succ : ∀ m z, db (m + 1) z = db m z + dzbar (v m) z := by
    intro m z; simp only [hdbdef]; rw [Finset.sum_range_succ]
  have hs_sm : ∀ m, ContDiff ℝ ∞ (s m) := by
    intro m
    induction m with
    | zero =>
      have h0 : s 0 = fun _ => (0 : ℂ) := by
        funext z; simp only [hsdef]; rw [Finset.range_zero, Finset.sum_empty]
      rw [h0]; exact contDiff_const
    | succ m ih =>
      rw [hs_succ m]; exact ih.add (hvprop m).1
  have hs_dz : ∀ m z, dz (s m) z = ds m z ∧ dzbar (s m) z = db m z := by
    intro m z
    induction m with
    | zero =>
      have h0 : s 0 = fun _ => (0 : ℂ) := by
        funext w; simp only [hsdef]; rw [Finset.range_zero, Finset.sum_empty]
      have hd0 : ds 0 z = 0 := by
        simp only [hdsdef]; rw [Finset.range_zero, Finset.sum_empty]
      have hb0 : db 0 z = 0 := by
        simp only [hdbdef]; rw [Finset.range_zero, Finset.sum_empty]
      rw [h0, hd0, hb0]
      have hfd : fderiv ℝ (fun _ : ℂ => (0 : ℂ)) z = 0 := fderiv_const_apply 0
      constructor <;> simp [dz, dzbar, hfd]
    | succ m ih =>
      rw [hs_succ m]
      have hd₁ : DifferentiableAt ℝ (s m) z := hd1 (hs_sm m) z
      have hd₂ : DifferentiableAt ℝ (v m) z := hd1 (hvprop m).1 z
      constructor
      · rw [dz_add hd₁ hd₂, ih.1, hds_succ m z]
      · rw [dzbar_add hd₁ hd₂, ih.2, hdb_succ m z]
  -- ===== CLM assembly toolkit. =====
  have hCLMext : ∀ T S : ℂ →L[ℝ] ℂ, T 1 = S 1 → T Complex.I = S Complex.I → T = S := by
    intro T S h1 hI
    ext w
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
      rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
    rw [hw]
    simp only [map_add, map_smul, h1, hI]
  have hA_apply : ∀ a b : ℂ,
      (Complex.reCLM.smulRight a + Complex.imCLM.smulRight b) (1 : ℂ) = a
      ∧ (Complex.reCLM.smulRight a + Complex.imCLM.smulRight b) Complex.I = b := by
    intro a b
    constructor
    · simp [ContinuousLinearMap.smulRight_apply]
    · simp [ContinuousLinearMap.smulRight_apply]
  have hopb : ∀ a b : ℂ,
      ‖Complex.reCLM.smulRight a + Complex.imCLM.smulRight b‖ ≤ ‖a‖ + ‖b‖ := by
    intro a b
    refine ContinuousLinearMap.opNorm_le_bound _
      (add_nonneg (norm_nonneg a) (norm_nonneg b)) (fun w => ?_)
    simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      Complex.reCLM_apply, Complex.imCLM_apply]
    calc ‖w.re • a + w.im • b‖
        ≤ ‖w.re • a‖ + ‖w.im • b‖ := norm_add_le _ _
      _ = |w.re| * ‖a‖ + |w.im| * ‖b‖ := by
          rw [Complex.real_smul, Complex.real_smul, norm_mul, norm_mul,
            Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖w‖ * ‖a‖ + ‖w‖ * ‖b‖ := by
          gcongr
          · exact Complex.abs_re_le_norm w
          · exact Complex.abs_im_le_norm w
      _ = (‖a‖ + ‖b‖) * ‖w‖ := by ring
  -- ===== The Wirtinger dictionary for the total derivative. =====
  have hdict : ∀ (f : ℂ → ℂ) (z : ℂ), (fderiv ℝ f z) 1 = dz f z + dzbar f z ∧
      (fderiv ℝ f z) Complex.I = Complex.I * (dz f z - dzbar f z) := by
    intro f z
    constructor
    · rw [dz, dzbar]; ring
    · rw [dz, dzbar]
      linear_combination ((fderiv ℝ f z) Complex.I) * Complex.I_mul_I
  -- ===== Each partial sum has the assembled derivative. =====
  have hsFD : ∀ m z, HasFDerivAt (s m)
      (Complex.reCLM.smulRight (ds m z + db m z)
        + Complex.imCLM.smulRight (Complex.I * (ds m z - db m z))) z := by
    intro m z
    have hd : DifferentiableAt ℝ (s m) z := hd1 (hs_sm m) z
    have hEq : fderiv ℝ (s m) z
        = Complex.reCLM.smulRight (ds m z + db m z)
          + Complex.imCLM.smulRight (Complex.I * (ds m z - db m z)) := by
      refine hCLMext _ _ ?_ ?_
      · rw [(hdict (s m) z).1, (hA_apply _ _).1, (hs_dz m z).1, (hs_dz m z).2]
      · rw [(hdict (s m) z).2, (hA_apply _ _).2, (hs_dz m z).1, (hs_dz m z).2]
    exact hEq ▸ hd.hasFDerivAt
  -- ===== Uniform convergence of the partial sums and their derivatives. =====
  have hsTU : TendstoUniformly (fun m z => s m z) φ atTop :=
    tendstoUniformly_tsum_nat hsum_v (fun n z => hKv n z)
  have hdsTU : TendstoUniformly (fun m z => ds m z) u₁ atTop :=
    tendstoUniformly_tsum_nat hsum_dz (fun n z => hKdz n z)
  have hdbTU : TendstoUniformly (fun m z => db m z) u₂ atTop :=
    tendstoUniformly_tsum_nat hsum_db (fun n z => hKdb n z)
  -- ===== Locally uniform convergence of the assembled derivatives. =====
  have hATLU : TendstoLocallyUniformlyOn
      (fun m z => Complex.reCLM.smulRight (ds m z + db m z)
        + Complex.imCLM.smulRight (Complex.I * (ds m z - db m z)))
      (fun z => Complex.reCLM.smulRight (u₁ z + u₂ z)
        + Complex.imCLM.smulRight (Complex.I * (u₁ z - u₂ z)))
      atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_univ]
    refine TendstoUniformly.tendstoLocallyUniformly ?_
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hε4 : (0 : ℝ) < ε / 4 := by positivity
    rw [Metric.tendstoUniformly_iff] at hdsTU hdbTU
    filter_upwards [hdsTU (ε / 4) hε4, hdbTU (ε / 4) hε4] with m hm₁ hm₂ z
    have h1 := hm₁ z
    have h2 := hm₂ z
    rw [dist_eq_norm] at h1 h2
    rw [dist_eq_norm]
    have hdiff : (Complex.reCLM.smulRight (u₁ z + u₂ z)
          + Complex.imCLM.smulRight (Complex.I * (u₁ z - u₂ z)))
        - (Complex.reCLM.smulRight (ds m z + db m z)
          + Complex.imCLM.smulRight (Complex.I * (ds m z - db m z)))
        = Complex.reCLM.smulRight ((u₁ z - ds m z) + (u₂ z - db m z))
          + Complex.imCLM.smulRight
              (Complex.I * ((u₁ z - ds m z) - (u₂ z - db m z))) := by
      refine hCLMext _ _ ?_ ?_
      · rw [sub_apply,
          (hA_apply (u₁ z + u₂ z) (Complex.I * (u₁ z - u₂ z))).1,
          (hA_apply (ds m z + db m z) (Complex.I * (ds m z - db m z))).1,
          (hA_apply ((u₁ z - ds m z) + (u₂ z - db m z))
            (Complex.I * ((u₁ z - ds m z) - (u₂ z - db m z)))).1]
        ring
      · rw [sub_apply,
          (hA_apply (u₁ z + u₂ z) (Complex.I * (u₁ z - u₂ z))).2,
          (hA_apply (ds m z + db m z) (Complex.I * (ds m z - db m z))).2,
          (hA_apply ((u₁ z - ds m z) + (u₂ z - db m z))
            (Complex.I * ((u₁ z - ds m z) - (u₂ z - db m z)))).2]
        ring
    rw [hdiff]
    refine lt_of_le_of_lt (hopb _ _) ?_
    have hb1 : ‖(u₁ z - ds m z) + (u₂ z - db m z)‖ < ε / 4 + ε / 4 :=
      lt_of_le_of_lt (norm_add_le _ _) (add_lt_add h1 h2)
    have hb2 : ‖Complex.I * ((u₁ z - ds m z) - (u₂ z - db m z))‖ < ε / 4 + ε / 4 := by
      rw [norm_mul, Complex.norm_I, one_mul]
      exact lt_of_le_of_lt (norm_sub_le _ _) (add_lt_add h1 h2)
    linarith
  -- ===== The limit: `φ` is differentiable with the assembled derivative. =====
  have hφFD : ∀ z, HasFDerivAt φ
      (Complex.reCLM.smulRight (u₁ z + u₂ z)
        + Complex.imCLM.smulRight (Complex.I * (u₁ z - u₂ z))) z := fun z =>
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ hATLU
      (fun m x _ => hsFD m x) (fun x _ => hsTU.tendsto_at x) (Set.mem_univ z)
  have hφfeq : ∀ z, fderiv ℝ φ z
      = Complex.reCLM.smulRight (u₁ z + u₂ z)
        + Complex.imCLM.smulRight (Complex.I * (u₁ z - u₂ z)) := fun z =>
    (hφFD z).fderiv
  have hφC1 : ContDiff ℝ 1 φ := by
    rw [contDiff_one_iff_fderiv]
    refine ⟨fun z => (hφFD z).differentiableAt, ?_⟩
    have heqf : fderiv ℝ φ = fun z =>
        Complex.reCLM.smulRight (u₁ z + u₂ z)
          + Complex.imCLM.smulRight (Complex.I * (u₁ z - u₂ z)) := funext hφfeq
    rw [heqf]
    have hc1 : Continuous (fun z => u₁ z + u₂ z) := hu₁cont.add hu₂cont
    have hc2 : Continuous (fun z => Complex.I * (u₁ z - u₂ z)) :=
      continuous_const.mul (hu₁cont.sub hu₂cont)
    exact (((ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.reCLM).continuous.comp hc1).add
      (((ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM).continuous.comp hc2)))
  -- ===== The Wirtinger derivatives of `φ` are the summed series. =====
  have hφdz : ∀ z, dz φ z = u₁ z ∧ dzbar φ z = u₂ z := by
    intro z
    have h1 : (fderiv ℝ φ z) 1 = u₁ z + u₂ z := by
      rw [hφfeq z]; exact (hA_apply _ _).1
    have hI : (fderiv ℝ φ z) Complex.I = Complex.I * (u₁ z - u₂ z) := by
      rw [hφfeq z]; exact (hA_apply _ _).2
    constructor
    · rw [dz, h1, hI]
      linear_combination (-(1 / 2 : ℂ) * (u₁ z - u₂ z)) * Complex.I_mul_I
    · rw [dzbar, h1, hI]
      linear_combination ((1 / 2 : ℂ) * (u₁ z - u₂ z)) * Complex.I_mul_I
  -- ===== `S φ = P (∂φ)` pointwise (`φ` is `C¹` with compact support). =====
  have hbeurφ : ∀ z, beurling φ z = cauchyTransform (fun ζ => dz φ ζ) z := by
    intro z
    rw [beurling, cauchyTransform]
    congr 1
    refine Filter.Tendsto.limUnder_eq ?_
    have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r φ z
        = czOperator beurlingKernel r φ z := fun r => rfl
    simpa only [hcz] using czOperator_beurling_tendsto_smooth hφC1 hφcs z
  have hdzφfun : (fun ζ => dz φ ζ) = u₁ := by funext ζ; exact (hφdz ζ).1
  have hbeurφ' : ∀ z, beurling φ z = cauchyTransform u₁ z := by
    intro z; rw [hbeurφ z, hdzφfun]
  have hSφcont : Continuous (beurling φ) := by
    have hfun : beurling φ = cauchyTransform u₁ := funext hbeurφ'
    rw [hfun]
    exact continuous_cauchyTransform_of_memLp_of_support hp hp'
      (hmem u₁ hu₁cont hu₁cs) hu₁van
  -- ===== Local integrability of the Cauchy kernel (polar coordinates). =====
  have hk_loc : LocallyIntegrable (fun w : ℂ => -w⁻¹) volume := by
    apply LocallyIntegrable.neg
    rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
    apply MeasureTheory.IntegrableOn.mono_set _ hR₀
    rw [IntegrableOn]
    refine ⟨measurable_inv.aestronglyMeasurable.restrict, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, ← lintegral_indicator measurableSet_closedBall,
      ← Complex.lintegral_comp_polarCoord_symm]
    set box : ℝ × ℝ → ENNReal :=
      (Set.Ioc (0 : ℝ) R₀ ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
        (fun _ => (1 : ENNReal)) with hbox
    have hbound : ∀ q ∈ polarCoord.target,
        ENNReal.ofReal q.1 • (Metric.closedBall (0 : ℂ) R₀).indicator
          (fun w : ℂ => ‖w⁻¹‖ₑ) (Complex.polarCoord.symm q) ≤ box q := by
      intro q hq
      simp only [hbox]
      rw [polarCoord_target, Set.mem_prod] at hq
      obtain ⟨hq1, hq2⟩ := hq
      simp only [Set.mem_Ioi] at hq1
      by_cases hmem' : Complex.polarCoord.symm q ∈ Metric.closedBall (0 : ℂ) R₀
      · rw [Set.indicator_of_mem hmem']
        have hnorm : ‖Complex.polarCoord.symm q‖ = q.1 := by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hq1]
        have hsymm_ne : Complex.polarCoord.symm q ≠ 0 := by
          rw [← norm_ne_zero_iff, hnorm]; exact ne_of_gt hq1
        rw [enorm_inv hsymm_ne]
        have henorm : ‖Complex.polarCoord.symm q‖ₑ = ENNReal.ofReal q.1 := by
          rw [← ofReal_norm, hnorm]
        rw [henorm, smul_eq_mul,
          ENNReal.mul_inv_cancel
            (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hq1)
            ENNReal.ofReal_lt_top.ne]
        have hqR : q.1 ≤ R₀ := by
          rw [Metric.mem_closedBall, dist_zero_right, hnorm] at hmem'; exact hmem'
        rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨hq1, hqR⟩, hq2⟩)]
      · rw [Set.indicator_of_notMem hmem']; simp
    calc
      ∫⁻ q in polarCoord.target, ENNReal.ofReal q.1 •
          (Metric.closedBall (0 : ℂ) R₀).indicator
            (fun w : ℂ => ‖w⁻¹‖ₑ) (Complex.polarCoord.symm q)
          ≤ ∫⁻ q in polarCoord.target, box q :=
            setLIntegral_mono (measurable_const.indicator
              (measurableSet_Ioc.prod measurableSet_Ioo)) hbound
      _ ≤ ∫⁻ q, box q := setLIntegral_le_lintegral _ _
      _ = volume (Set.Ioc (0 : ℝ) R₀ ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
            rw [hbox, lintegral_indicator (measurableSet_Ioc.prod measurableSet_Ioo)]
            simp
      _ < ⊤ := by
            rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioc,
              Real.volume_Ioo]
            exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  -- ===== Integrability of Cauchy integrands over continuous c.s. data. =====
  have hPint : ∀ (w : ℂ → ℂ), Continuous w → HasCompactSupport w → ∀ z : ℂ,
      Integrable (fun ζ => w ζ / (ζ - z)) volume := by
    intro w hw hwc z
    have h : Integrable (fun t =>
        (ContinuousLinearMap.mul ℝ ℂ) (w t) ((fun u : ℂ => -u⁻¹) (z - t))) volume :=
      (hwc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℂ) hw hk_loc) z
    have heq : (fun t =>
        (ContinuousLinearMap.mul ℝ ℂ) (w t) ((fun u : ℂ => -u⁻¹) (z - t)))
        = fun ζ => w ζ / (ζ - z) := by
      funext ζ
      rw [ContinuousLinearMap.mul_apply']
      change w ζ * -(z - ζ)⁻¹ = w ζ / (ζ - z)
      have hflip : -(z - ζ)⁻¹ = (ζ - z)⁻¹ := by rw [← neg_sub ζ z, inv_neg, neg_neg]
      rw [hflip, div_eq_mul_inv]
    rw [heq] at h
    exact h
  -- ===== Finite additivity of the Cauchy transform over the partial sums. =====
  have hds_cont : ∀ m, Continuous (fun ζ => ds m ζ) := by
    intro m
    have hc : ∀ n ∈ Finset.range m, Continuous (fun ζ => dz (v n) ζ) := fun n _ =>
      ((hdz_sm _ (hvprop n).1).1).continuous
    simpa only [hdsdef] using continuous_finsetSum _ hc
  have hds_van : ∀ m, ∀ ζ, R < ‖ζ‖ → ds m ζ = 0 := by
    intro m ζ hζ
    simp only [hdsdef]
    exact Finset.sum_eq_zero (fun n _ => hdzv_van n ζ hζ)
  have hPadd : ∀ m z, (∑ n ∈ Finset.range m,
      cauchyTransform (fun ζ => dz (v n) ζ) z) = cauchyTransform (fun ζ => ds m ζ) z := by
    intro m z
    have hint : ∀ n ∈ Finset.range m,
        Integrable (fun ζ => dz (v n) ζ / (ζ - z)) volume := fun n _ =>
      hPint _ ((hdz_sm _ (hvprop n).1).1).continuous ((hdz_cs _ (hvprop n).2.1).1) z
    simp only [cauchyTransform]
    rw [← Finset.mul_sum]
    congr 1
    rw [← MeasureTheory.integral_finsetSum _ hint]
    congr 1
    funext ζ
    simp only [hdsdef]
    rw [Finset.sum_div]
  -- ===== `eLpNorm` from a uniform bound on the support ball. =====
  have hpt0 : 0 < p.toReal := ENNReal.toReal_pos hp0 hp'
  have hVfin : volume (Metric.closedBall (0 : ℂ) R) ≠ ⊤ :=
    ((isCompact_closedBall (0 : ℂ) R).measure_lt_top).ne
  set Vp : ℝ := ((volume (Metric.closedBall (0 : ℂ) R)) ^ (1 / p.toReal)).toReal
    with hVpdef
  have help : ∀ (w : ℂ → ℂ) (t : ℝ), 0 ≤ t → (∀ ζ, ‖w ζ‖ ≤ t) →
      (∀ ζ, R < ‖ζ‖ → w ζ = 0) →
      (eLpNorm w p volume).toReal ≤ t * Vp := by
    intro w t ht hb hv
    have hmono : eLpNorm w p volume
        ≤ eLpNorm ((Metric.closedBall (0 : ℂ) R).indicator (fun _ => t)) p volume := by
      apply eLpNorm_mono
      intro ζ
      by_cases hζ : ζ ∈ Metric.closedBall (0 : ℂ) R
      · rw [Set.indicator_of_mem hζ, Real.norm_eq_abs, abs_of_nonneg ht]
        exact hb ζ
      · rw [Set.indicator_of_notMem hζ]
        have hout : R < ‖ζ‖ := by
          rwa [Metric.mem_closedBall, dist_zero_right, not_le] at hζ
        rw [hv ζ hout]
        simp
    rw [eLpNorm_indicator_const measurableSet_closedBall hp0 hp'] at hmono
    have hne : ‖t‖ₑ * volume (Metric.closedBall (0 : ℂ) R) ^ (1 / p.toReal) ≠ ⊤ := by
      refine ENNReal.mul_ne_top ?_ (ENNReal.rpow_lt_top_of_nonneg
        (div_nonneg zero_le_one hpt0.le) hVfin).ne
      rw [← ofReal_norm]; exact ENNReal.ofReal_ne_top
    have h2 := ENNReal.toReal_mono hne hmono
    rwa [ENNReal.toReal_mul, ← ofReal_norm,
      ENNReal.toReal_ofReal (norm_nonneg _), Real.norm_eq_abs, abs_of_nonneg ht] at h2
  -- ===== The pointwise fixed-point equation. =====
  have heqn : ∀ z : ℂ, φ z = μ z * beurling φ z + g z := by
    intro z
    -- The partial-sum recursion at `z`.
    have hids : ∀ m, s (m + 1) z
        = μ z * cauchyTransform (fun ζ => ds m ζ) z + g z := by
      intro m
      have hv0 : v 0 z = g z := by
        simp only [hvdef]; rw [Function.iterate_zero_apply]
      have h1 : s (m + 1) z = (∑ n ∈ Finset.range m, v (n + 1) z) + g z := by
        simp only [hsdef]
        rw [Finset.sum_range_succ', hv0]
      have h2 : ∀ n, v (n + 1) z
          = μ z * cauchyTransform (fun ζ => dz (v n) ζ) z := by
        intro n
        rw [congrFun (hvsucc n) z,
          beurling_eq_cauchyTransform_dz (hvprop n).1 (hvprop n).2.1 z]
      rw [h1, Finset.sum_congr rfl (fun n _ => h2 n), ← Finset.mul_sum, hPadd m z]
    -- LHS: the partial sums converge to `φ z`.
    have hsummz : Summable (fun n => v n z) :=
      Summable.of_norm_bounded hsum_v (fun n => hKv n z)
    have hφz : Tendsto (fun m => s m z) atTop (𝓝 (φ z)) :=
      hsummz.hasSum.tendsto_sum_nat
    have hL : Tendsto (fun m => s (m + 1) z) atTop (𝓝 (φ z)) :=
      hφz.comp (tendsto_add_atTop_nat 1)
    -- RHS: `P (ds m) z → P u₁ z` by the uniform tail bound.
    have hu₁intz : Integrable (fun ζ => u₁ ζ / (ζ - z)) volume :=
      hPint u₁ hu₁cont hu₁cs z
    have hPdiff : ∀ m, cauchyTransform (fun ζ => ds m ζ) z - cauchyTransform u₁ z
        = cauchyTransform (fun ζ => ds m ζ - u₁ ζ) z := by
      intro m
      simp only [cauchyTransform]
      rw [← mul_sub]
      congr 1
      rw [← MeasureTheory.integral_sub
        (hPint _ (hds_cont m) (hcs_of_van _ (hds_van m)) z) hu₁intz]
      congr 1
      funext ζ
      rw [← sub_div]
    have htail : ∀ m ζ, ‖ds m ζ - u₁ ζ‖ ≤ Kdz * (1 - r')⁻¹ * r' ^ m := by
      intro m ζ
      have hsummdzζ : Summable (fun n => dz (v n) ζ) :=
        Summable.of_norm_bounded hsum_dz (fun n => hKdz n ζ)
      have hsplit : ds m ζ + ∑' i, dz (v (i + m)) ζ = u₁ ζ := by
        simp only [hdsdef, hu₁def]
        exact hsummdzζ.sum_add_tsum_nat_add m
      have heqm : ds m ζ - u₁ ζ = -(∑' i, dz (v (i + m)) ζ) := by
        rw [← hsplit]; ring
      rw [heqm, norm_neg]
      have hb : ∀ i, ‖dz (v (i + m)) ζ‖ ≤ Kdz * r' ^ m * r' ^ i := by
        intro i
        calc ‖dz (v (i + m)) ζ‖ ≤ Kdz * r' ^ (i + m) := hKdz (i + m) ζ
          _ = Kdz * r' ^ m * r' ^ i := by rw [pow_add]; ring
      have hsum_geom : Summable (fun i : ℕ => Kdz * r' ^ m * r' ^ i) :=
        hgeom.mul_left _
      have hsumnorm : Summable (fun i => ‖dz (v (i + m)) ζ‖) :=
        Summable.of_nonneg_of_le (fun i => norm_nonneg _) hb hsum_geom
      calc ‖∑' i, dz (v (i + m)) ζ‖
          ≤ ∑' i, ‖dz (v (i + m)) ζ‖ := norm_tsum_le_tsum_norm hsumnorm
        _ ≤ ∑' i, Kdz * r' ^ m * r' ^ i := Summable.tsum_le_tsum hb hsumnorm hsum_geom
        _ = Kdz * r' ^ m * (1 - r')⁻¹ := by
            rw [tsum_mul_left, tsum_geometric_of_lt_one hr'0.le hr'1]
        _ = Kdz * (1 - r')⁻¹ * r' ^ m := by ring
    have hPtail : ∀ m, ‖cauchyTransform (fun ζ => ds m ζ - u₁ ζ) z‖
        ≤ CR * (Kdz * (1 - r')⁻¹ * r' ^ m * Vp) := by
      intro m
      have hcontm : Continuous (fun ζ => ds m ζ - u₁ ζ) := (hds_cont m).sub hu₁cont
      have hvanm : ∀ ζ, R < ‖ζ‖ → ds m ζ - u₁ ζ = 0 := by
        intro ζ hζ; rw [hds_van m ζ hζ, hu₁van ζ hζ, sub_zero]
      have ht0 : 0 ≤ Kdz * (1 - r')⁻¹ * r' ^ m :=
        mul_nonneg (mul_nonneg hKdz0 (inv_nonneg.mpr (by linarith))) (hr'pow m)
      have h1 := hCR _ (hmem _ hcontm (hcs_of_van _ hvanm)) hvanm z
      refine le_trans h1 ?_
      exact mul_le_mul_of_nonneg_left
        (help _ _ ht0 (fun ζ => htail m ζ) hvanm) hCR0
    have hto0 : Tendsto (fun m => CR * (Kdz * (1 - r')⁻¹ * r' ^ m * Vp)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun m : ℕ => r' ^ m) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hr'0.le hr'1
      have h2 : (fun m => CR * (Kdz * (1 - r')⁻¹ * r' ^ m * Vp))
          = fun m => (CR * (Kdz * (1 - r')⁻¹) * Vp) * r' ^ m := by
        funext m; ring
      rw [h2]
      simpa using h1.const_mul (CR * (Kdz * (1 - r')⁻¹) * Vp)
    have hPconv : Tendsto (fun m => cauchyTransform (fun ζ => ds m ζ) z) atTop
        (𝓝 (cauchyTransform u₁ z)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_) hto0
      rw [hPdiff m]
      exact hPtail m
    have hR : Tendsto (fun m => μ z * cauchyTransform (fun ζ => ds m ζ) z + g z)
        atTop (𝓝 (μ z * cauchyTransform u₁ z + g z)) :=
      (hPconv.const_mul (μ z)).add_const (g z)
    have hL' : Tendsto (fun m => s (m + 1) z) atTop
        (𝓝 (μ z * cauchyTransform u₁ z + g z)) := by
      have hfe : (fun m => s (m + 1) z)
          = fun m => μ z * cauchyTransform (fun ζ => ds m ζ) z + g z := funext hids
      rw [hfe]; exact hR
    have hkey : φ z = μ z * cauchyTransform u₁ z + g z := tendsto_nhds_unique hL hL'
    rw [hkey, hbeurφ' z]
  -- ===== Assemble the witness. =====
  exact ⟨φ, hφmem, hφvan, hφcont, hSφcont, heqn⟩

/-! ## The smooth principal solution -/

/-- **The smooth-case principal solution is a nondegenerate `C¹` map** (AIM
Theorem 5.2.3). For a Beltrami coefficient with smooth compactly supported `μ`
there is a principal solution `f` of class `C¹` whose Jacobian is positive at
**every** point and whose `∂`-derivative never vanishes. Exponential
representation: solve the auxiliary equation `ω = μ·Sω + ∂μ` (the fixed point
of `exists_continuous_fixedPoint_beltrami_of_contDiff` with datum `∂μ`), set
`σ = P ω` and `F = id + P(μ·e^σ)`; the identity `e^σ − 1 = S(μ·e^σ)` gives
`∂F = e^σ ≠ 0`, `∂̄F = μ·e^σ`, hence `J(z, F) = |e^σ|²·(1 − |μ|²) > 0`, and
`F` is itself a principal solution with field `h = μ·e^σ`. -/
theorem exists_contDiffOne_principalSolution (b : BeltramiCoeff)
    (hμs : ContDiff ℝ ∞ b.μ) (hμc : HasCompactSupport b.μ) :
    ∃ f : ℂ → ℂ, IsPrincipalSolution b f ∧ ContDiff ℝ 1 f ∧
      (∀ z : ℂ, 0 < (fderiv ℝ f z).det) ∧ ∀ z : ℂ, dz f z ≠ 0 := by
  classical
  -- ===== Constants and the pointwise coefficient bound. =====
  set k : ℝ := (eLpNormEssSup b.μ volume).toReal with hkdef
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have hkfin : eLpNormEssSup b.μ volume ≠ ⊤ := (b.bound.trans_le le_top).ne
  have hk1 : k < 1 := by
    rw [hkdef, show (1 : ℝ) = (1 : ℝ≥0∞).toReal by simp]
    exact (ENNReal.toReal_lt_toReal hkfin ENNReal.one_ne_top).2 b.bound
  have hμ_ae : ∀ᵐ z ∂(volume : Measure ℂ), ‖b.μ z‖ ≤ k := by
    have h1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖b.μ z‖ₑ ≤ eLpNormEssSup b.μ volume :=
      ae_le_eLpNormEssSup
    filter_upwards [h1] with z hz
    rw [← ofReal_norm] at hz
    have h3 := ENNReal.toReal_mono hkfin hz
    rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at h3
  have hμpt : ∀ z, ‖b.μ z‖ ≤ k := by
    by_contra hcon
    obtain ⟨z₀, hz₀⟩ := not_forall.mp hcon
    rw [not_le] at hz₀
    have hopen : IsOpen {z : ℂ | k < ‖b.μ z‖} :=
      isOpen_lt continuous_const hμs.continuous.norm
    have hnull : volume {z : ℂ | k < ‖b.μ z‖} = 0 := by
      have h2 := hμ_ae
      rw [MeasureTheory.ae_iff] at h2
      have hset : {z : ℂ | ¬ ‖b.μ z‖ ≤ k} = {z : ℂ | k < ‖b.μ z‖} := by
        ext z; simp [not_le]
      rwa [hset] at h2
    exact absurd hnull (hopen.measure_pos volume ⟨z₀, hz₀⟩).ne'
  -- ===== A support radius. =====
  obtain ⟨R, hR⟩ : ∃ R : ℝ, tsupport b.μ ⊆ Metric.closedBall 0 R :=
    (hμc.isCompact.isBounded).subset_closedBall 0
  have hμvan : ∀ z : ℂ, R < ‖z‖ → b.μ z = 0 := by
    intro z hz
    apply image_eq_zero_of_notMem_tsupport
    intro hmem'
    have h2 := hR hmem'
    rw [Metric.mem_closedBall, dist_zero_right] at h2
    exact absurd h2 (not_le.mpr hz)
  -- ===== Differentiability and Wirtinger toolkit. =====
  have hd1 : ∀ {u : ℂ → ℂ}, ContDiff ℝ ∞ u → Differentiable ℝ u := by
    intro u hu
    exact (hu.of_le (by exact_mod_cast le_top : ((1 : ℕ∞) : WithTop ℕ∞) ≤ _)).differentiable
      one_ne_zero
  have hdz_sm : ∀ u : ℂ → ℂ, ContDiff ℝ ∞ u →
      ContDiff ℝ ∞ (fun ζ => dz u ζ) := by
    intro u hu
    have hfderiv_cinf : ContDiff ℝ ∞ (fun ζ => fderiv ℝ u ζ) :=
      hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    have hcomp : (fun ζ => dz u ζ)
        = (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I))
          ∘ (fun ζ => fderiv ℝ u ζ) := by funext ζ; rfl
    have hΦ : ContDiff ℝ ∞
        (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I)) := by
      have hΦ_lin : (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I))
          = (fun D : ℂ →L[ℝ] ℂ =>
              (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) D
                - Complex.I • ContinuousLinearMap.apply ℝ ℂ Complex.I D)) := by
        funext D; simp [ContinuousLinearMap.apply_apply, smul_eq_mul]
      rw [hΦ_lin]
      exact (((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).contDiff).sub
        ((ContinuousLinearMap.apply ℝ ℂ Complex.I).contDiff.const_smul Complex.I)).const_smul _
    rw [hcomp]; exact hΦ.comp hfderiv_cinf
  have hdz_cs : ∀ u : ℂ → ℂ, HasCompactSupport u →
      HasCompactSupport (fun ζ => dz u ζ) := by
    intro u huc
    have hfderiv_cs : HasCompactSupport (fun ζ => fderiv ℝ u ζ) := huc.fderiv (𝕜 := ℝ)
    have hcomp : (fun ζ => dz u ζ)
        = (fun D : ℂ →L[ℝ] ℂ => (1/2 : ℂ) * (D 1 - I * D I)) ∘ (fun ζ => fderiv ℝ u ζ) := by
      funext ζ; rfl
    rw [hcomp]; exact hfderiv_cs.comp_left (by simp)
  have hvanish : ∀ (u : ℂ → ℂ), (∀ z, R < ‖z‖ → u z = 0) → ∀ z, R < ‖z‖ →
      dz u z = 0 := by
    intro u hu z hz
    have hopen : IsOpen {w : ℂ | R < ‖w‖} := isOpen_lt continuous_const continuous_norm
    have hev : u =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hz) (fun w hw => hu w hw)
    have hfd : fderiv ℝ u z = 0 := by
      rw [hev.fderiv_eq]; exact fderiv_const_apply 0
    simp [dz, hfd]
  have hcs_of_van : ∀ (u : ℂ → ℂ), (∀ z, R < ‖z‖ → u z = 0) → HasCompactSupport u := by
    intro u huv
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R) ?_
    intro x hx
    refine huv x ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact hx
  have hdict : ∀ (f : ℂ → ℂ) (z : ℂ), (fderiv ℝ f z) 1 = dz f z + dzbar f z ∧
      (fderiv ℝ f z) Complex.I = Complex.I * (dz f z - dzbar f z) := by
    intro f z
    constructor
    · rw [dz, dzbar]; ring
    · rw [dz, dzbar]
      linear_combination ((fderiv ℝ f z) Complex.I) * Complex.I_mul_I
  -- ===== The Weyl mollification lemma (continuous + vanishing weak `∂̄` ⇒ entire). =====
  have hweyl : ∀ (f gx gy : ℂ → ℂ), Continuous f →
      HasWeakDirDeriv 1 gx f Set.univ → HasWeakDirDeriv Complex.I gy f Set.univ →
      LocallyIntegrable gx → LocallyIntegrable gy →
      (∀ z, gx z + Complex.I * gy z = 0) →
      Differentiable ℂ f := by
    intro f gx gy hfcont hwgx hwgy hgxLI hgyLI hcombpt
    have hfloc : LocallyIntegrable f := hfcont.locallyIntegrable
    have hcomb : ∀ᵐ z ∂(volume : Measure ℂ), gx z + Complex.I * gy z = 0 :=
      Filter.Eventually.of_forall hcombpt
    set φb : ℕ → ContDiffBump (0 : ℂ) := fun n =>
      { rIn := 1 / (n + 2), rOut := 2 / (n + 2),
        rIn_pos := by positivity,
        rIn_lt_rOut := by
          rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num } with hφbdef
    have hφrout : Tendsto (fun n => (φb n).rOut) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        apply Tendsto.div_atTop tendsto_const_nhds
        exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      simpa [hφbdef] using h2
    set ρ : ℕ → ℂ → ℝ := fun n => (φb n).normed volume with hρdef
    set fn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution (ρ n) f
      (ContinuousLinearMap.lsmul ℝ ℝ) volume with hfndef
    have hρsm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
      (φb n).contDiff_normed (n := ⊤)
    have hρsupp : ∀ n, HasCompactSupport (ρ n) := fun n => (φb n).hasCompactSupport_normed
    have hρcont : ∀ n, Continuous (ρ n) := fun n => (hρsm n).continuous
    have hA1x : ∀ n z, (fderiv ℝ (fn n) z) (1 : ℂ)
        = MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z :=
      fun n z => fderiv_convolution_normed_apply_eq hwgx hfloc hgxLI (hρsm n) (hρsupp n) z
    have hA1y : ∀ n z, (fderiv ℝ (fn n) z) Complex.I
        = MeasureTheory.convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z :=
      fun n z => fderiv_convolution_normed_apply_eq hwgy hfloc hgyLI (hρsm n) (hρsupp n) z
    have hexx : ∀ n, MeasureTheory.ConvolutionExists (ρ n) gx
        (ContinuousLinearMap.lsmul ℝ ℝ) volume := fun n =>
      (hρsupp n).convolutionExists_left _ (hρcont n) hgxLI
    have hexy : ∀ n, MeasureTheory.ConvolutionExists (ρ n) gy
        (ContinuousLinearMap.lsmul ℝ ℝ) volume := fun n =>
      (hρsupp n).convolutionExists_left _ (hρcont n) hgyLI
    have hfn_holo : ∀ n, DifferentiableOn ℂ (fn n) Set.univ := by
      intro n
      have hfn_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fn n) :=
        (hρsupp n).contDiff_convolution_left _ (hρsm n) hfloc
      have hfn_diffR : ∀ z, DifferentiableAt ℝ (fn n) z := fun z =>
        (hfn_smooth.differentiable (by simp)).differentiableAt
      have hdzbar0 : ∀ z, dzbar (fn n) z = 0 := by
        intro z
        have hval : dzbar (fn n) z
            = (1 / 2 : ℂ) *
              (MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                + Complex.I * MeasureTheory.convolution (ρ n) gy
                  (ContinuousLinearMap.lsmul ℝ ℝ) volume z) := by
          rw [dzbar, hA1x n z, hA1y n z]
        have hzero : MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ)
              volume z
            + Complex.I * MeasureTheory.convolution (ρ n) gy
              (ContinuousLinearMap.lsmul ℝ ℝ) volume z = 0 := by
          set Fx : ℂ → ℂ := fun t => (ContinuousLinearMap.lsmul ℝ ℝ (ρ n t)) (gx (z - t))
            with hFx
          set Fy : ℂ → ℂ := fun t => (ContinuousLinearMap.lsmul ℝ ℝ (ρ n t)) (gy (z - t))
            with hFy
          have hcx : MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ)
              volume z = ∫ t, Fx t := rfl
          have hcy : MeasureTheory.convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ)
              volume z = ∫ t, Fy t := rfl
          rw [hcx, hcy]
          have hIint : Complex.I * ∫ t, Fy t = ∫ t, Complex.I * Fy t :=
            (MeasureTheory.integral_const_mul Complex.I Fy).symm
          rw [hIint]
          have hix : MeasureTheory.Integrable Fx volume := (hexx n z)
          have hiy : MeasureTheory.Integrable (fun t => Complex.I * Fy t) volume :=
            (hexy n z).const_mul Complex.I
          rw [← MeasureTheory.integral_add hix hiy]
          refine MeasureTheory.integral_eq_zero_of_ae ?_
          have hshift : ∀ᵐ t ∂(volume : Measure ℂ),
              gx (z - t) + Complex.I * gy (z - t) = 0 := by
            have hmp : MeasureTheory.MeasurePreserving (fun t : ℂ => z - t)
                (volume : Measure ℂ) volume :=
              (volume : Measure ℂ).measurePreserving_sub_left z
            exact hmp.quasiMeasurePreserving.ae hcomb
          filter_upwards [hshift] with t ht
          simp only [hFx, hFy, ContinuousLinearMap.lsmul_apply, Pi.zero_apply]
          rw [mul_smul_comm, ← smul_add, ht, smul_zero]
        rw [hval, hzero, mul_zero]
      refine (differentiableOn_iff_dzbar_eq_zero isOpen_univ ?_).mpr (fun z _ => hdzbar0 z)
      exact fun z _ => (hfn_diffR z).differentiableWithinAt
    have hTLU : TendstoLocallyUniformlyOn fn f atTop Set.univ := by
      rw [tendstoLocallyUniformlyOn_univ]
      refine tendstoLocallyUniformly_of_forall_exists_nhds (fun x => ?_)
      refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
      have hUC : UniformContinuousOn f (Metric.closedBall x 2) :=
        (isCompact_closedBall x 2).uniformContinuousOn_of_continuous hfcont.continuousOn
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have hε2 : (0 : ℝ) < ε / 2 := by positivity
      obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hUC (ε / 2) hε2
      have hev : ∀ᶠ n in atTop, (φb n).rOut < min δ 1 := by
        have := hφrout.eventually (eventually_lt_nhds (show (0 : ℝ) < min δ 1 by positivity))
        filter_upwards [this] with n hn using hn
      filter_upwards [hev] with n hn z hz
      have hrout_le_one : (φb n).rOut ≤ 1 := (lt_of_lt_of_le hn (min_le_right δ 1)).le
      have hrout_le_δ : (φb n).rOut ≤ δ := (lt_of_lt_of_le hn (min_le_left δ 1)).le
      have hsupp2 : Function.support (ρ n) ⊆ Metric.ball (0 : ℂ) (φb n).rOut := by
        rw [hρdef, (φb n).support_normed_eq]
      have hnf : ∀ y, 0 ≤ ρ n y := fun y => (φb n).nonneg_normed y
      have hintf : ∫ y, ρ n y ∂volume = 1 := (φb n).integral_normed
      have hclose : ∀ y ∈ Metric.ball z (φb n).rOut, dist (f y) (f z) ≤ ε / 2 := by
        intro y hy
        have hzmem : z ∈ Metric.closedBall x 2 :=
          Metric.closedBall_subset_closedBall (by norm_num) hz
        rw [Metric.mem_ball] at hy
        have hymem : y ∈ Metric.closedBall x 2 := by
          rw [Metric.mem_closedBall] at hz ⊢
          calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
            _ ≤ (φb n).rOut + 1 := by gcongr
            _ ≤ 1 + 1 := by gcongr
            _ = 2 := by norm_num
        exact (hδ y hymem z hzmem (hy.trans_le hrout_le_δ)).le
      calc dist (f z) (fn n z) = dist (fn n z) (f z) := dist_comm _ _
        _ ≤ ε / 2 := dist_convolution_le hε2.le hsupp2 hnf hintf
              hfcont.aestronglyMeasurable hclose
        _ < ε := by linarith
    have hdiffOn : DifferentiableOn ℂ f Set.univ :=
      hTLU.differentiableOn (Filter.Eventually.of_forall hfn_holo) isOpen_univ
    rw [← differentiableOn_univ]
    exact hdiffOn
  -- ===== Contraction data and the σ-equation. =====
  obtain ⟨p, hp, hp', C, hCb, hcontr⟩ :=
    exists_p_gt_two_beurling_contraction b.measurable b.bound
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp.le
  have hmem : ∀ (u : ℂ → ℂ), Continuous u → HasCompactSupport u → MemLp u p volume :=
    fun u hu huc => hu.memLp_of_hasCompactSupport huc
  have hsupp' : ∀ z : ℂ, R < ‖z‖ → b.μ z = 0 ∧ dz b.μ z = 0 := fun z hz =>
    ⟨hμvan z hz, hvanish b.μ hμvan z hz⟩
  obtain ⟨ν, hνmem, hνvan, hνcont, hSνcont, hνeq⟩ :=
    exists_continuous_fixedPoint_beltrami_of_contDiff hp hp' hμs hμc
      (hdz_sm b.μ hμs) (hdz_cs b.μ hμc) hCb hcontr hsupp'
  have hνeq' : ∀ z, ν z = b.μ z * beurling ν z + dz b.μ z := fun z => hνeq z
  -- ===== `σ = P ν` is C¹ with `∂σ = Sν`, `∂̄σ = ν`. =====
  set σ : ℂ → ℂ := cauchyTransform ν with hσdef
  have hσcont : Continuous σ :=
    continuous_cauchyTransform_of_memLp_of_support hp hp' hνmem hνvan
  have hσgrad := hasWeakGradient_cauchyTransform hp hp' hνmem hνvan
  have hσpkg := contDiffOne_of_continuous_hasWeakGradient hσcont hσgrad
    (hSνcont.add hνcont) (continuous_const.mul (hSνcont.sub hνcont))
  have hσC1 : ContDiff ℝ 1 σ := hσpkg.1
  have hσdiff : ∀ z, DifferentiableAt ℝ σ z :=
    fun z => (hσC1.differentiable one_ne_zero).differentiableAt
  have hσdz : ∀ z, dz σ z = beurling ν z ∧ dzbar σ z = ν z := by
    intro z
    have h1 : (fderiv ℝ σ z) 1 = beurling ν z + ν z := (hσpkg.2 z).1
    have hI : (fderiv ℝ σ z) Complex.I = Complex.I * (beurling ν z - ν z) := (hσpkg.2 z).2
    constructor
    · rw [dz, h1, hI]
      linear_combination (-(1 / 2 : ℂ) * (beurling ν z - ν z)) * Complex.I_mul_I
    · rw [dzbar, h1, hI]
      linear_combination ((1 / 2 : ℂ) * (beurling ν z - ν z)) * Complex.I_mul_I
  -- ===== The exponential `e^σ` and its Wirtinger derivatives. =====
  have hexpσC1 : ContDiff ℝ 1 (fun z => Complex.exp (σ z)) :=
    Complex.contDiff_exp.comp hσC1
  have hEdz : ∀ z, dz (fun w => Complex.exp (σ w)) z = Complex.exp (σ z) * beurling ν z
      ∧ dzbar (fun w => Complex.exp (σ w)) z = Complex.exp (σ z) * ν z := by
    intro z
    have hgd : DifferentiableAt ℂ Complex.exp (σ z) := Complex.differentiable_exp _
    have hgd' : DifferentiableAt ℝ Complex.exp (σ z) :=
      (Complex.contDiff_exp.differentiable one_ne_zero) (σ z)
    have hdzexp : dz Complex.exp (σ z) = Complex.exp (σ z) := by
      rw [dz_eq_deriv_of_differentiableAt hgd, Complex.deriv_exp]
    have hdzbarexp : dzbar Complex.exp (σ z) = 0 := dzbar_eq_zero_of_differentiableAt hgd
    constructor
    · rw [dz_comp (hσdiff z) hgd', hdzexp, hdzbarexp, (hσdz z).1]; ring
    · rw [dzbar_comp (hσdiff z) hgd', hdzexp, hdzbarexp, (hσdz z).2]; ring
  -- ===== The field `h = μ·e^σ`. =====
  set h : ℂ → ℂ := fun z => b.μ z * Complex.exp (σ z) with hhdef
  have hhC1 : ContDiff ℝ 1 h := (hμs.of_le (by exact_mod_cast le_top)).mul hexpσC1
  have hhcont : Continuous h := hhC1.continuous
  have hhcs : HasCompactSupport h := hμc.mul_right
  have hhvan : ∀ z, R < ‖z‖ → h z = 0 := by
    intro z hz; simp only [hhdef, hμvan z hz, zero_mul]
  have hhmem : MemLp h p volume := hmem h hhcont hhcs
  have hdzh : ∀ z, dz h z = Complex.exp (σ z) * ν z := by
    intro z
    have hμd : DifferentiableAt ℝ b.μ z := hd1 hμs z
    have hEd : DifferentiableAt ℝ (fun w => Complex.exp (σ w)) z :=
      (hexpσC1.differentiable one_ne_zero).differentiableAt
    calc dz h z
        = b.μ z * dz (fun w => Complex.exp (σ w)) z
          + Complex.exp (σ z) * dz b.μ z := by
          rw [hhdef]; exact dz_mul hμd hEd
      _ = b.μ z * (Complex.exp (σ z) * beurling ν z)
          + Complex.exp (σ z) * dz b.μ z := by rw [(hEdz z).1]
      _ = Complex.exp (σ z) * (b.μ z * beurling ν z + dz b.μ z) := by ring
      _ = Complex.exp (σ z) * ν z := by rw [← hνeq' z]
  -- ===== `S h = P (∂h)` pointwise, and continuity of `S h`. =====
  have hbeurh : ∀ z, beurling h z = cauchyTransform (fun ζ => dz h ζ) z := by
    intro z
    rw [beurling, cauchyTransform]
    congr 1
    refine Filter.Tendsto.limUnder_eq ?_
    have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r h z
        = czOperator beurlingKernel r h z := fun r => rfl
    simpa only [hcz] using czOperator_beurling_tendsto_smooth hhC1 hhcs z
  have hdzhfun : (fun ζ => dz h ζ) = fun ζ => Complex.exp (σ ζ) * ν ζ := by
    funext ζ; exact hdzh ζ
  have hdzhcont : Continuous (fun ζ => dz h ζ) := by
    rw [hdzhfun]; exact (Complex.continuous_exp.comp hσcont).mul hνcont
  have hdzhvan : ∀ ζ, R < ‖ζ‖ → dz h ζ = 0 := fun ζ hζ => hvanish h hhvan ζ hζ
  have hdzhcs : HasCompactSupport (fun ζ => dz h ζ) := hcs_of_van _ hdzhvan
  have hdzhmem : MemLp (fun ζ => dz h ζ) p volume := hmem _ hdzhcont hdzhcs
  have hShcont : Continuous (beurling h) := by
    have hfun : beurling h = cauchyTransform (fun ζ => dz h ζ) := funext hbeurh
    rw [hfun]
    exact continuous_cauchyTransform_of_memLp_of_support hp hp' hdzhmem hdzhvan
  -- ===== `P h` is C¹ with `∂(P h) = S h`, `∂̄(P h) = h`. =====
  have hPhcont : Continuous (cauchyTransform h) :=
    continuous_cauchyTransform_of_memLp_of_support hp hp' hhmem hhvan
  have hPhgrad := hasWeakGradient_cauchyTransform hp hp' hhmem hhvan
  have hPhpkg := contDiffOne_of_continuous_hasWeakGradient hPhcont hPhgrad
    (hShcont.add hhcont) (continuous_const.mul (hShcont.sub hhcont))
  have hPhC1 : ContDiff ℝ 1 (cauchyTransform h) := hPhpkg.1
  have hPhdz : ∀ z, dz (cauchyTransform h) z = beurling h z
      ∧ dzbar (cauchyTransform h) z = h z := by
    intro z
    have h1 : (fderiv ℝ (cauchyTransform h) z) 1 = beurling h z + h z := (hPhpkg.2 z).1
    have hI : (fderiv ℝ (cauchyTransform h) z) Complex.I
        = Complex.I * (beurling h z - h z) := (hPhpkg.2 z).2
    constructor
    · rw [dz, h1, hI]
      linear_combination (-(1 / 2 : ℂ) * (beurling h z - h z)) * Complex.I_mul_I
    · rw [dzbar, h1, hI]
      linear_combination ((1 / 2 : ℂ) * (beurling h z - h z)) * Complex.I_mul_I
  -- ===== The comparison function `u = (e^σ − 1) − P(∂h)` is entire and vanishes. =====
  set A : ℂ → ℂ := fun z => Complex.exp (σ z) - 1 with hAdef
  have hAC1 : ContDiff ℝ 1 A := hexpσC1.sub contDiff_const
  set B : ℂ → ℂ := cauchyTransform (fun ζ => dz h ζ) with hBdef
  have hBgrad := hasWeakGradient_cauchyTransform hp hp' hdzhmem hdzhvan
  have hBcont : Continuous B :=
    continuous_cauchyTransform_of_memLp_of_support hp hp' hdzhmem hdzhvan
  set u : ℂ → ℂ := fun z => A z - B z with hudef
  have hucont : Continuous u := hAC1.continuous.sub hBcont
  have hwAx : HasWeakDirDeriv 1 (fun z => (fderiv ℝ A z) 1) A Set.univ :=
    HasWeakDirDeriv.of_contDiffOn isOpen_univ hAC1.contDiffOn
  have hwAy : HasWeakDirDeriv Complex.I (fun z => (fderiv ℝ A z) Complex.I) A Set.univ :=
    HasWeakDirDeriv.of_contDiffOn isOpen_univ hAC1.contDiffOn
  have hfdA_cont : Continuous (fun z => fderiv ℝ A z) := (contDiff_one_iff_fderiv.mp hAC1).2
  have hgAx_cont : Continuous (fun z => (fderiv ℝ A z) 1) :=
    ((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous).comp hfdA_cont
  have hgAy_cont : Continuous (fun z => (fderiv ℝ A z) Complex.I) :=
    ((ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous).comp hfdA_cont
  have hSdzhmem : MemLp (beurling (fun ζ => dz h ζ)) p volume :=
    memLp_beurling_of_memLp hp hp' hdzhmem
  have hgxB_LI : LocallyIntegrable (fun z => beurling (fun ζ => dz h ζ) z + dz h z) :=
    (hSdzhmem.add hdzhmem).locallyIntegrable hp1
  have hgyB_LI : LocallyIntegrable
      (fun z => Complex.I * (beurling (fun ζ => dz h ζ) z - dz h z)) :=
    ((hSdzhmem.sub hdzhmem).const_mul Complex.I).locallyIntegrable hp1
  have hwux : HasWeakDirDeriv 1
      (fun z => (fderiv ℝ A z) 1 - (beurling (fun ζ => dz h ζ) z + dz h z)) u Set.univ :=
    HasWeakDirDeriv.sub hwAx hBgrad.1
      (locallyIntegrableOn_univ.mpr hAC1.continuous.locallyIntegrable)
      (locallyIntegrableOn_univ.mpr hBcont.locallyIntegrable)
      (locallyIntegrableOn_univ.mpr hgAx_cont.locallyIntegrable)
      (locallyIntegrableOn_univ.mpr hgxB_LI)
  have hwuy : HasWeakDirDeriv Complex.I
      (fun z => (fderiv ℝ A z) Complex.I
        - Complex.I * (beurling (fun ζ => dz h ζ) z - dz h z)) u Set.univ :=
    HasWeakDirDeriv.sub hwAy hBgrad.2
      (locallyIntegrableOn_univ.mpr hAC1.continuous.locallyIntegrable)
      (locallyIntegrableOn_univ.mpr hBcont.locallyIntegrable)
      (locallyIntegrableOn_univ.mpr hgAy_cont.locallyIntegrable)
      (locallyIntegrableOn_univ.mpr hgyB_LI)
  have hdzbarA : ∀ z, dzbar A z = Complex.exp (σ z) * ν z := by
    intro z
    have hfdA : fderiv ℝ A z = fderiv ℝ (fun w => Complex.exp (σ w)) z := by
      rw [hAdef]; exact fderiv_sub_const 1
    have h2 := (hEdz z).2
    rw [dzbar] at h2 ⊢
    rw [hfdA]
    exact h2
  have hcombpt : ∀ z,
      ((fderiv ℝ A z) 1 - (beurling (fun ζ => dz h ζ) z + dz h z))
        + Complex.I * ((fderiv ℝ A z) Complex.I
          - Complex.I * (beurling (fun ζ => dz h ζ) z - dz h z)) = 0 := by
    intro z
    rw [(hdict A z).1, (hdict A z).2, hdzbarA z, hdzh z]
    linear_combination (dz A z - beurling (fun ζ => dz h ζ) z) * Complex.I_mul_I
  have hu_ent : Differentiable ℂ u :=
    hweyl u _ _ hucont hwux hwuy
      (hgAx_cont.locallyIntegrable.sub hgxB_LI)
      (hgAy_cont.locallyIntegrable.sub hgyB_LI)
      hcombpt
  -- ===== `u → 0` cocompactly, hence `u ≡ 0` by Liouville. =====
  have hσ0 : Tendsto σ (Filter.cocompact ℂ) (𝓝 0) :=
    cauchyTransform_tendsto_cocompact hp hp' hνmem hνvan
  have hA0 : Tendsto A (Filter.cocompact ℂ) (𝓝 0) := by
    have h1 : Tendsto (fun z => Complex.exp (σ z)) (Filter.cocompact ℂ) (𝓝 1) := by
      have h2 := (Complex.continuous_exp.tendsto 0).comp hσ0
      simpa using! h2
    have h2 := h1.sub_const 1
    simpa [hAdef] using h2
  have hB0 : Tendsto B (Filter.cocompact ℂ) (𝓝 0) :=
    cauchyTransform_tendsto_cocompact hp hp' hdzhmem hdzhvan
  have hu0 : Tendsto u (Filter.cocompact ℂ) (𝓝 0) := by
    have h2 := hA0.sub hB0
    simpa [hudef] using h2
  have hubdd : Bornology.IsBounded (Set.range u) := by
    have h1 : ∀ᶠ z in Filter.cocompact ℂ, u z ∈ Metric.closedBall (0 : ℂ) 1 :=
      hu0 (Metric.closedBall_mem_nhds 0 one_pos)
    rw [Filter.eventually_iff, Filter.mem_cocompact] at h1
    obtain ⟨K, hKc, hKsub⟩ := h1
    have h2 : Set.range u ⊆ (u '' K) ∪ Metric.closedBall (0 : ℂ) 1 := by
      rintro _ ⟨z, rfl⟩
      by_cases hz : z ∈ K
      · exact Or.inl ⟨z, hz, rfl⟩
      · exact Or.inr (hKsub hz)
    exact (((hKc.image hucont).isBounded).union Metric.isBounded_closedBall).subset h2
  have hu_zero : ∀ z, u z = 0 := by
    intro z
    have hconst : ∀ w, u w = u z := fun w => hu_ent.apply_eq_apply_of_bounded hubdd w z
    have hc' : Tendsto u (Filter.cocompact ℂ) (𝓝 (u z)) := by
      have hfe : u = fun _ => u z := funext hconst
      rw [hfe]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hc' hu0
  -- ===== The key identity `e^σ = 1 + S h`. =====
  have hkey : ∀ z, Complex.exp (σ z) = 1 + beurling h z := by
    intro z
    have h0 : A z - B z = 0 := hu_zero z
    have h1 : Complex.exp (σ z) - 1 - cauchyTransform (fun ζ => dz h ζ) z = 0 := by
      simpa [hAdef, hBdef, sub_sub] using h0
    rw [hbeurh z]
    linear_combination h1
  -- ===== Assemble the principal solution `F = id + P h`. =====
  have hidd : ∀ z : ℂ, DifferentiableAt ℝ (fun w : ℂ => w) z :=
    fun z => differentiable_id.differentiableAt
  have hPd : ∀ z, DifferentiableAt ℝ (cauchyTransform h) z :=
    fun z => (hPhC1.differentiable one_ne_zero).differentiableAt
  have hdzid : ∀ z : ℂ, dz (fun w : ℂ => w) z = 1 ∧ dzbar (fun w : ℂ => w) z = 0 := by
    intro z
    have hfd : fderiv ℝ (fun w : ℂ => w) z = ContinuousLinearMap.id ℝ ℂ := fderiv_fun_id
    constructor
    · rw [dz, hfd]
      simp only [ContinuousLinearMap.id_apply]
      linear_combination (-(1 / 2 : ℂ)) * Complex.I_mul_I
    · rw [dzbar, hfd]
      simp only [ContinuousLinearMap.id_apply]
      linear_combination ((1 / 2 : ℂ)) * Complex.I_mul_I
  have hFdz : ∀ z, dz (fun w => w + cauchyTransform h w) z = Complex.exp (σ z)
      ∧ dzbar (fun w => w + cauchyTransform h w) z = h z := by
    intro z
    constructor
    · rw [dz_add (hidd z) (hPd z), (hdzid z).1, (hPhdz z).1, hkey z]
    · rw [dzbar_add (hidd z) (hPd z), (hdzid z).2, (hPhdz z).2, zero_add]
  refine ⟨fun w => w + cauchyTransform h w, ?_, ?_, ?_, ?_⟩
  · -- IsPrincipalSolution
    refine ⟨p, h, R, hp, hp', hhmem, hhvan, ?_, fun z => rfl⟩
    refine Filter.Eventually.of_forall (fun z => ?_)
    have h1 : h z = b.μ z * Complex.exp (σ z) := by rw [hhdef]
    rw [h1, hkey z]
    ring
  · -- C¹
    exact contDiff_id.add hPhC1
  · -- positive Jacobian
    intro z
    rw [det_fderiv_eq_wirtinger, (hFdz z).1, (hFdz z).2]
    have h1 : ‖h z‖ = ‖b.μ z‖ * ‖Complex.exp (σ z)‖ := by
      rw [hhdef]; exact norm_mul _ _
    have h2 : 0 < ‖Complex.exp (σ z)‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
    have h3 : ‖b.μ z‖ ≤ k := hμpt z
    have h4 : 0 ≤ ‖b.μ z‖ := norm_nonneg _
    rw [h1]
    have h5 : ‖b.μ z‖ * ‖b.μ z‖ ≤ k * k := mul_le_mul h3 h3 h4 hk0
    have h6 : k * k < 1 := by nlinarith
    have h7 : ‖b.μ z‖ * ‖b.μ z‖ < 1 := lt_of_le_of_lt h5 h6
    have h8 : 0 < ‖Complex.exp (σ z)‖ * ‖Complex.exp (σ z)‖ := mul_pos h2 h2
    nlinarith [mul_pos h8 (sub_pos.mpr h7)]
  · -- nonvanishing ∂F
    intro z
    rw [(hFdz z).1]
    exact Complex.exp_ne_zero _

end NoWanderingDomains
