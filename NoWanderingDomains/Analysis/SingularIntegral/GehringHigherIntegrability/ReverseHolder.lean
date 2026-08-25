/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.SingularIntegral.GehringHigherIntegrability.Caccioppoli

/-!
# Gehring self-improvement: the `f`-level reverse-Hölder inequality (S1)

The `f`-level reverse-Hölder inequality `reverseHolder_of_weakGradient`, derived from the
Caccioppoli (N3) and Sobolev–Poincaré (N1) nodes, with the `setLAverage` arithmetic for the
Wirtinger conversion.
-/

open MeasureTheory Complex Filter
open scoped ENNReal NNReal Topology Real Pointwise

namespace NoWanderingDomains

/-! ## S1 sub-stack — `setLAverage` arithmetic for the Wirtinger conversion

The corrected Sobolev–Poincaré node N1 carries the **full gradient** `‖Gx‖ + ‖Gy‖`, so the
reverse-Hölder node S1 must convert it back to the holomorphic gradient `‖G‖` (plus an `L²`
forcing). The Wirtinger identities give, a.e., `‖Gx z‖ + ‖Gy z‖ ≤ A'·‖G z‖ + 2·‖R z‖`; the
two small lemmas below turn the pointwise bound and the `L¹ ≤ L²` Jensen step into statements
about the lower-integral set averages `⨍⁻_s` over the doubled ball. -/

/-- **Aux: `setLAverage` monotone under an a.e. pointwise bound and a constant-multiple-plus
split.** For `s` with `0 < volume s` and `volume s < ⊤`, if a.e. on `s` we have
`f z ≤ ENNReal.ofReal c · g z + d z`, then `⨍⁻_s f ≤ ENNReal.ofReal c · ⨍⁻_s g + ⨍⁻_s d`. -/
private theorem setLAverage_le_const_mul_add {s : Set ℂ}
    {f g d : ℂ → ℝ≥0∞} {c : ℝ}
    (hd : AEMeasurable d (volume.restrict s))
    (hpt : ∀ᵐ z ∂(volume.restrict s), f z ≤ ENNReal.ofReal c * g z + d z) :
    (⨍⁻ z in s, f z ∂volume) ≤
      ENNReal.ofReal c * (⨍⁻ z in s, g z ∂volume) + (⨍⁻ z in s, d z ∂volume) := by
  rw [setLAverage_eq, setLAverage_eq, setLAverage_eq]
  -- Reduce to the `∫⁻`-level inequality, then divide by the common volume `V := volume s`.
  set V : ℝ≥0∞ := volume s with hV_def
  have hint : (∫⁻ z in s, f z ∂volume) ≤
      ENNReal.ofReal c * (∫⁻ z in s, g z ∂volume) + (∫⁻ z in s, d z ∂volume) := by
    calc (∫⁻ z in s, f z ∂volume)
        ≤ ∫⁻ z in s, (ENNReal.ofReal c * g z + d z) ∂volume := lintegral_mono_ae hpt
      _ = (∫⁻ z in s, ENNReal.ofReal c * g z ∂volume) + (∫⁻ z in s, d z ∂volume) :=
          lintegral_add_right' _ hd
      _ = ENNReal.ofReal c * (∫⁻ z in s, g z ∂volume) + (∫⁻ z in s, d z ∂volume) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc (∫⁻ z in s, f z ∂volume) / V
      ≤ (ENNReal.ofReal c * (∫⁻ z in s, g z ∂volume) + (∫⁻ z in s, d z ∂volume)) / V := by
        gcongr
    _ = ENNReal.ofReal c * ((∫⁻ z in s, g z ∂volume) / V) + (∫⁻ z in s, d z ∂volume) / V := by
        rw [ENNReal.add_div, mul_div_assoc]

/-- **Aux: Jensen `⨍⁻_s f ≤ (⨍⁻_s f²)^(1/2)`** for a finite, positive-measure set `s`. The
`L¹`-average is dominated by the `L²`-average; the proof is Cauchy–Schwarz `∫⁻ f·1 ≤
(∫⁻ f²)^½·(∫⁻ 1)^½ = (∫⁻ f²)^½·V^½` divided by `V`. -/
private theorem setLAverage_le_rpow_setLAverage_sq {s : Set ℂ}
    (hs0 : volume s ≠ 0) (hstop : volume s ≠ ⊤) {f : ℂ → ℝ≥0∞}
    (hf : AEMeasurable f (volume.restrict s)) :
    (⨍⁻ z in s, f z ∂volume) ≤
      (⨍⁻ z in s, f z ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) := by
  set V : ℝ≥0∞ := volume s with hV_def
  -- Cauchy–Schwarz: `∫⁻_s f = ∫⁻_s f·1 ≤ (∫⁻_s f²)^½·(∫⁻_s 1²)^½`.
  have hcs : (∫⁻ z in s, f z ∂volume) ≤
      (∫⁻ z in s, f z ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) * V ^ (1 / (2 : ℝ)) := by
    have hpq : (2 : ℝ).HolderConjugate 2 := by
      rw [Real.holderConjugate_iff]; constructor <;> norm_num
    have hmul := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict s) hpq
      (f := f) (g := fun _ => (1 : ℝ≥0∞)) hf aemeasurable_const
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul,
      Measure.restrict_apply_univ] at hmul
    -- `(∫⁻_s 1)^{1/2} = V^{1/2}`; `hmul` now is exactly the target.
    exact hmul
  rw [setLAverage_eq, setLAverage_eq]
  -- Divide by `V`: `(∫f)/V ≤ ((∫f²)^½·V^½)/V = ((∫f²)/V)^½`.
  have hVpow : V ^ (1 / (2 : ℝ)) ≠ 0 := by
    simp only [ne_eq, ENNReal.rpow_eq_zero_iff, not_or, not_and_or]
    exact ⟨Or.inl hs0, Or.inr (by norm_num)⟩
  have hVpowtop : V ^ (1 / (2 : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hstop
  -- `V^½·V^½ = V`.
  have hVsplit : V ^ (1 / (2 : ℝ)) * V ^ (1 / (2 : ℝ)) = V := by
    rw [← ENNReal.rpow_add_of_nonneg (1 / 2) (1 / 2) (by norm_num) (by norm_num)]
    norm_num
  -- `V^½/V = (V^½)⁻¹`, hence `(a·V^½)/V = a/V^½`.
  have hkey : ∀ a : ℝ≥0∞, a * V ^ (1 / (2 : ℝ)) / V = a / V ^ (1 / (2 : ℝ)) := by
    intro a
    rw [ENNReal.div_eq_div_iff hVpow hVpowtop hs0 hstop]
    -- `V^½ · (a · V^½) = V · a`, using `V^½ · V^½ = V`.
    calc V ^ (1 / (2 : ℝ)) * (a * V ^ (1 / (2 : ℝ)))
        = a * (V ^ (1 / (2 : ℝ)) * V ^ (1 / (2 : ℝ))) := by ring
      _ = a * V := by rw [hVsplit]
      _ = V * a := by ring
  calc (∫⁻ z in s, f z ∂volume) / V
      ≤ ((∫⁻ z in s, f z ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) * V ^ (1 / (2 : ℝ))) / V := by
        gcongr
    _ = (∫⁻ z in s, f z ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) / V ^ (1 / (2 : ℝ)) := hkey _
    _ = ((∫⁻ z in s, f z ^ (2 : ℝ) ∂volume) / V) ^ (1 / (2 : ℝ)) :=
        (ENNReal.div_rpow_of_nonneg (∫⁻ z in s, f z ^ (2 : ℝ) ∂volume) V
          (by norm_num : (0 : ℝ) ≤ 1 / 2)).symm

/-! ## S1 — the `f`-level reverse-Hölder inequality from the primitive -/

/-- **S1 (`reverseHolder_of_weakGradient`).** The **`f`-level reverse-Hölder / Caccioppoli
inequality** for an `L²` Beltrami fixed point `G = h + T(μ·G)` that is the weak holomorphic
gradient `G = ½(Gx − I·Gy)` of a primitive `F` (with weak partials `Gx, Gy`), carrying the
**antiholomorphic relation** `½(Gx + I·Gy) =ᵐ μ·G + R` (`R` an `L²` cutoff remainder).

There is a constant `A ≥ 0`, depending only on `‖μ‖∞` and the Beurling/dimensional
constants (hence **independent of the ball** `x, r`), such that for every centre `x` and
radius `r > 0` the `L²`-average of `‖G‖` over the ball `B = ball x r` is controlled by the
`L¹`-average of `‖G‖` over the doubled ball `2B = ball x (2r)` plus the `L²`-average of the
**combined forcing** `‖h‖ + ‖R‖`:
`(⨍⁻_{B} ‖G‖²)^(1/2) ≤ A · ⨍⁻_{2B} ‖G‖ + A · (⨍⁻_{2B} (‖h‖ + ‖R‖)²)^(1/2)`.

This is the hypothesis the general Gehring lemma `gehring_selfImprovement` consumes
(with `q = 2`, weight `w = ‖G‖`, lower-order term `b = ‖h‖ + ‖R‖`). The averages are the
`ℝ≥0∞`-valued lower-integral averages `⨍⁻ … = (vol B)⁻¹ ∫⁻ …`, which avoid any Bochner
integrability side-condition.

**Uniformity.** The constant `A` is quantified *outside* the fixed-point bundle
`(F, G, h, R)`: classically it depends only on the ellipticity `‖μ‖∞` and the
Beurling/dimensional constants, never on the particular solution. This uniformity is what
lets the downstream consumer upgrade *all* cutoff fixed points with a single exponent.

*Derivation (PROVEN modulo N1/N3).* Chain the `f`-level Caccioppoli inequality N3
(`caccioppoli_of_beltrami`, the `r⁻¹·(oscillation of F)` bound) with the corrected
Sobolev–Poincaré inequality N1 (`sobolevPoincare_ball`,
`(oscillation of F) ≤ r·⨍(‖Gx‖+‖Gy‖)`): the `r⁻¹` from Caccioppoli cancels the `r` from
Sobolev–Poincaré. The **full gradient** `‖Gx‖+‖Gy‖` is converted back to the holomorphic
gradient `‖G‖` (plus the `L²` forcing `‖R‖`) by the **Wirtinger identities**
`Gx = (1+μ)G + R`, `Gy = -I((1−μ)G − R)` (from `G = ½(Gx−I·Gy)` and the antiholomorphic
relation), so `‖Gx z‖ + ‖Gy z‖ ≤ 2(1+‖μ‖∞)·‖G z‖ + 2·‖R z‖` a.e. Averaging and a Jensen
`L¹ ≤ L²` step on `‖R‖` fold `‖R‖` together with the N3 inhomogeneity `‖h‖` into the single
`L²`-forcing `‖h‖ + ‖R‖`, giving a scale-invariant constant `A`. -/
theorem reverseHolder_of_weakGradient {μ : ℂ → ℂ}
    (hμmeas : Measurable μ) (hμfin : eLpNormEssSup μ volume ≠ ⊤)
    (hμbound : eLpNormEssSup μ volume < 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {F G Gx Gy h R : ℂ → ℂ},
      HasCompactSupport F → MemLp F 2 volume → MemLp G 2 volume → MemLp h 2 volume →
      MemLp Gx 2 volume → MemLp Gy 2 volume →
      HasWeakDirDeriv 1 Gx F Set.univ → HasWeakDirDeriv Complex.I Gy F Set.univ →
      (∀ z, G z = (1 / 2 : ℂ) * (Gx z - Complex.I * Gy z)) →
      G =ᵐ[volume] h + beurling (fun z => μ z * G z) →
      MemLp R 2 volume →
      (∀ᵐ z, (1 / 2 : ℂ) * (Gx z + Complex.I * Gy z) = μ z * G z + R z) →
        ∀ (x : ℂ) (r : ℝ), 0 < r →
          (⨍⁻ z in Metric.ball x r, (‖G z‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) ≤
            ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), (‖G z‖₊ : ℝ≥0∞) ∂volume) +
              ENNReal.ofReal A *
                (⨍⁻ z in Metric.ball x (4 * r),
                  ((‖h z‖₊ : ℝ≥0∞) + (‖R z‖₊ : ℝ≥0∞)) ^ (2 : ℝ) ∂volume)
                  ^ (1 / (2 : ℝ)) := by
  classical
  -- N3: the `f`-level Caccioppoli constant `A₃` (depending only on `μ`).
  obtain ⟨A₃, hA₃, hCacc⟩ := caccioppoli_of_beltrami hμmeas hμfin hμbound
  -- N1: the dimensional Sobolev–Poincaré constant `C₁`.
  obtain ⟨C₁, hC₁, hSob⟩ := sobolevPoincare_ball
  -- `M := ‖μ‖∞.toReal < 1`; the Wirtinger comparison constant `A' := 2(1 + M)`.
  set M : ℝ := (eLpNormEssSup μ volume).toReal with hM_def
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  set A' : ℝ := 2 * (1 + M) with hA'_def
  have hA'0 : 0 ≤ A' := by positivity
  -- `‖μ z‖ₑ ≤ ofReal M` a.e. (from `ae_le_eLpNormEssSup` and `‖μ‖∞ = ofReal M`).
  have hμessSup_eq : eLpNormEssSup μ volume = ENNReal.ofReal M := by
    rw [hM_def, ENNReal.ofReal_toReal hμfin]
  -- The combined reverse-Hölder constant. The `r⁻¹` of Caccioppoli cancels the `r` of the
  -- Sobolev–Poincaré applied at radius `2r` (giving the factor `2`), so the gradient
  -- coefficient is `2·A₃·C₁·A'`; the forcing absorbs the Wirtinger remainder `4·A₃·C₁·normB`
  -- (via Jensen) and the N3 inhomogeneity `2·A₃·normB` (after the `2B → 4B` ball-transfer).
  refine ⟨2 * (A₃ * C₁ * A') + 4 * (A₃ * C₁) + 2 * A₃, by positivity, ?_⟩
  intro F G Gx Gy h R hFcs hFmem hGmem hhmem hGxmem hGymem hGxweak hGyweak hGdef hGeq hRmem hRrel
    x r hr
  set Afin : ℝ := 2 * (A₃ * C₁ * A') + 4 * (A₃ * C₁) + 2 * A₃ with hAfin_def
  have hAfin0 : 0 ≤ Afin := by positivity
  -- Caccioppoli (N3): `(⨍_B ‖G‖²)^½ ≤ (A₃/r)·oscF + A₃·(⨍_{2B}‖h‖²)^½`.
  have hC := hCacc hFmem hGmem hRmem hGxmem hGymem hGxweak hGyweak hGdef hRrel x r hr
  -- Sobolev–Poincaré (N1, asymmetric) applied at radius `2r`: the oscillation of `F` over
  -- `2B = ball x (2r)` (centered at `⨍_{2B} F`) is bounded by the full-gradient `L¹`-average
  -- over the DOUBLED ball `4B = ball x (4r)`: `oscF ≤ (C₁·(2r))·⨍_{4B}(‖Gx‖+‖Gy‖)`.
  have h2r : (0 : ℝ) < 2 * r := by linarith
  have hS := hSob hFmem hGxmem hGymem hGxweak hGyweak x (2 * r) h2r
  -- ====================================================================
  -- The balls `2B`, `4B`, their volumes, and basic measurability.
  -- ====================================================================
  set B2 : Set ℂ := Metric.ball x (2 * r) with hB2_def
  set B4 : Set ℂ := Metric.ball x (4 * r) with hB4_def
  have h4r : (0 : ℝ) < 4 * r := by linarith
  have hB2meas : MeasurableSet B2 := measurableSet_ball
  have hB4meas : MeasurableSet B4 := measurableSet_ball
  have hVol2_0 : volume B2 ≠ 0 := (Metric.measure_ball_pos volume x h2r).ne'
  have hVol2top : volume B2 ≠ ⊤ := measure_ball_lt_top.ne
  have hVol0 : volume B4 ≠ 0 := (Metric.measure_ball_pos volume x h4r).ne'
  have hVoltop : volume B4 ≠ ⊤ := measure_ball_lt_top.ne
  -- `2B ⊆ 4B`, and the planar volume ratio `|4B| = 4·|2B|`.
  have hB2_sub_B4 : B2 ⊆ B4 := by
    intro z hz; rw [hB2_def, Metric.mem_ball] at hz; rw [hB4_def, Metric.mem_ball]; linarith
  have hvol_ratio : volume B4 = 4 * volume B2 := by
    rw [hB2_def, hB4_def, Complex.volume_ball, Complex.volume_ball,
      show (4 : ℝ) * r = 2 * (2 * r) from by ring, ENNReal.ofReal_mul (by norm_num), mul_pow,
      show ENNReal.ofReal 2 ^ 2 = (4 : ℝ≥0∞) from by
        rw [← ENNReal.ofReal_pow (by norm_num)]; norm_num]
    ring
  -- Abbreviations: `oscF` and N3's `normH` over `2B`; the Wirtinger/gradient averages over `4B`.
  set oscF : ℝ≥0∞ :=
    (⨍⁻ z in B2, (‖F z - (⨍ w in B2, F w)‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))
    with hoscF_def
  -- `normH` now holds the N3 forcing in its corrected `‖R‖`-form (the differential
  -- inhomogeneity `R = ∂̄F − μ·∂F`), still over `2B`.
  set normH : ℝ≥0∞ :=
    (⨍⁻ z in B2, (‖R z‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) with hnormH_def
  set avgG : ℝ≥0∞ := ⨍⁻ z in B4, (‖G z‖₊ : ℝ≥0∞) ∂volume with havgG_def
  set avgR : ℝ≥0∞ := ⨍⁻ z in B4, (‖R z‖₊ : ℝ≥0∞) ∂volume with havgR_def
  set normR : ℝ≥0∞ :=
    (⨍⁻ z in B4, (‖R z‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) with hnormR_def
  set normB : ℝ≥0∞ :=
    (⨍⁻ z in B4, ((‖h z‖₊ : ℝ≥0∞) + (‖R z‖₊ : ℝ≥0∞)) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))
    with hnormB_def
  set avgGxGy : ℝ≥0∞ := ⨍⁻ z in B4, ((‖Gx z‖₊ : ℝ≥0∞) + (‖Gy z‖₊ : ℝ≥0∞)) ∂volume
    with havgGxGy_def
  -- ====================================================================
  -- (W) The pointwise Wirtinger bound, a.e. on `4B`:
  --     `‖Gx z‖ₑ + ‖Gy z‖ₑ ≤ ofReal A' · ‖G z‖ₑ + 2·‖R z‖ₑ`.
  -- ====================================================================
  have hWirt : ∀ᵐ z ∂(volume.restrict B4),
      (‖Gx z‖₊ : ℝ≥0∞) + (‖Gy z‖₊ : ℝ≥0∞)
        ≤ ENNReal.ofReal A' * (‖G z‖₊ : ℝ≥0∞) + 2 * (‖R z‖₊ : ℝ≥0∞) := by
    have hμae : ∀ᵐ z ∂(volume : Measure ℂ), (‖μ z‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal M := by
      filter_upwards [ae_le_eLpNormEssSup (f := μ) (μ := volume)] with z hz
      rw [hμessSup_eq] at hz
      rwa [← enorm_eq_nnnorm]
    rw [ae_restrict_iff' hB4meas]
    filter_upwards [hRrel, hμae] with z hrelz hμz _
    -- Algebra: `Gx z = (1 + μ z)·G z + R z`, `Gy z = -I·((1 − μ z)·G z − R z)`.
    have hGxeq : Gx z = (1 + μ z) * G z + R z := by
      have hbar : (1 / 2 : ℂ) * (Gx z + Complex.I * Gy z) = μ z * G z + R z := hrelz
      have hg : G z = (1 / 2 : ℂ) * (Gx z - Complex.I * Gy z) := hGdef z
      -- `Gx = ½(Gx − I·Gy) + ½(Gx + I·Gy) = G + (μ·G + R)`.
      have : G z + (1 / 2 : ℂ) * (Gx z + Complex.I * Gy z) = Gx z := by rw [hg]; ring
      rw [hbar] at this; rw [← this]; ring
    have hGyeq : Complex.I * Gy z = (μ z - 1) * G z + R z := by
      have hbar : (1 / 2 : ℂ) * (Gx z + Complex.I * Gy z) = μ z * G z + R z := hrelz
      have hg : G z = (1 / 2 : ℂ) * (Gx z - Complex.I * Gy z) := hGdef z
      -- `I·Gy = ½(Gx + I·Gy) − ½(Gx − I·Gy) = (μ·G + R) − G`.
      have : (1 / 2 : ℂ) * (Gx z + Complex.I * Gy z) - G z = Complex.I * Gy z := by
        rw [hg]; ring
      rw [hbar] at this; rw [← this]; ring
    -- Enorm bounds. `‖1 + μ z‖ₑ ≤ ofReal(1 + M)` and `‖μ z − 1‖ₑ ≤ ofReal(1 + M)`.
    have hofReal1M : (1 : ℝ≥0∞) + ENNReal.ofReal M = ENNReal.ofReal (1 + M) := by
      rw [ENNReal.ofReal_add (by norm_num) hM0, ENNReal.ofReal_one]
    have hμze : ‖(μ z : ℂ)‖ₑ ≤ ENNReal.ofReal M := by rwa [enorm_eq_nnnorm]
    have hone : ‖(1 : ℂ)‖ₑ ≤ (1 : ℝ≥0∞) := by simp [enorm_eq_nnnorm]
    have hc1 : ‖(1 + μ z : ℂ)‖ₑ ≤ ENNReal.ofReal (1 + M) := by
      refine le_trans (enorm_add_le _ _) ?_
      rw [← hofReal1M]
      exact add_le_add hone hμze
    have hofRealM1 : ENNReal.ofReal M + 1 = ENNReal.ofReal (1 + M) := by
      rw [add_comm]; exact hofReal1M
    have hc2 : ‖(μ z - 1 : ℂ)‖ₑ ≤ ENNReal.ofReal (1 + M) := by
      refine le_trans enorm_sub_le ?_
      rw [← hofRealM1]
      exact add_le_add hμze hone
    -- `‖Gx z‖ₑ ≤ ofReal(1+M)·‖G z‖ₑ + ‖R z‖ₑ`.
    have hGxbd : (‖Gx z‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (1 + M) * (‖G z‖₊ : ℝ≥0∞)
        + (‖R z‖₊ : ℝ≥0∞) := by
      rw [← enorm_eq_nnnorm, hGxeq, ← enorm_eq_nnnorm, ← enorm_eq_nnnorm]
      refine le_trans (enorm_add_le _ _) ?_
      gcongr
      rw [enorm_mul]; gcongr
    -- `‖Gy z‖ₑ = ‖I·Gy z‖ₑ ≤ ofReal(1+M)·‖G z‖ₑ + ‖R z‖ₑ`.
    have hGybd : (‖Gy z‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (1 + M) * (‖G z‖₊ : ℝ≥0∞)
        + (‖R z‖₊ : ℝ≥0∞) := by
      have hI : (‖Gy z‖₊ : ℝ≥0∞) = ‖Complex.I * Gy z‖ₑ := by
        rw [enorm_mul]; simp [enorm_eq_nnnorm]
      rw [hI, hGyeq]
      refine le_trans (enorm_add_le _ _) ?_
      gcongr
      · rw [enorm_mul]; gcongr; rw [enorm_eq_nnnorm]
      · rw [enorm_eq_nnnorm]
    -- Sum and collect: coefficient `2·ofReal(1+M) = ofReal A'`, remainder `2·‖R‖ₑ`.
    calc (‖Gx z‖₊ : ℝ≥0∞) + (‖Gy z‖₊ : ℝ≥0∞)
        ≤ (ENNReal.ofReal (1 + M) * (‖G z‖₊ : ℝ≥0∞) + (‖R z‖₊ : ℝ≥0∞))
            + (ENNReal.ofReal (1 + M) * (‖G z‖₊ : ℝ≥0∞) + (‖R z‖₊ : ℝ≥0∞)) :=
          add_le_add hGxbd hGybd
      _ = ENNReal.ofReal A' * (‖G z‖₊ : ℝ≥0∞) + 2 * (‖R z‖₊ : ℝ≥0∞) := by
          have hA'split : ENNReal.ofReal A' = ENNReal.ofReal (1 + M) + ENNReal.ofReal (1 + M) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity), hA'_def]
            congr 1; ring
          rw [hA'split]
          ring
  -- ====================================================================
  -- (C) The averaged Wirtinger conversion:
  --     `avgGxGy ≤ ofReal A' · avgG + 2 · avgR`.
  -- ====================================================================
  have hGmeasR : AEMeasurable (fun z => (‖G z‖₊ : ℝ≥0∞)) (volume.restrict B4) := by
    refine (hGmem.1.enorm.restrict).congr ?_; filter_upwards with z; simp [enorm_eq_nnnorm]
  have hRmeasR : AEMeasurable (fun z => (‖R z‖₊ : ℝ≥0∞)) (volume.restrict B4) := by
    refine (hRmem.1.enorm.restrict).congr ?_; filter_upwards with z; simp [enorm_eq_nnnorm]
  have hConv : avgGxGy ≤ ENNReal.ofReal A' * avgG + 2 * avgR := by
    have hd : AEMeasurable (fun z => 2 * (‖R z‖₊ : ℝ≥0∞)) (volume.restrict B4) :=
      hRmeasR.const_mul _
    have := setLAverage_le_const_mul_add (s := B4) (c := A') (g := fun z => (‖G z‖₊ : ℝ≥0∞))
      (d := fun z => 2 * (‖R z‖₊ : ℝ≥0∞)) hd hWirt
    -- `⨍_{4B}(2·‖R‖) = 2·avgR`.
    have hlinR : (⨍⁻ z in B4, 2 * (‖R z‖₊ : ℝ≥0∞) ∂volume) = 2 * avgR := by
      rw [havgR_def, setLAverage_eq, setLAverage_eq, lintegral_const_mul' _ _ (by norm_num),
        ← mul_div_assoc]
    rwa [hlinR] at this
  -- ====================================================================
  -- (J) Jensen: `avgR ≤ normR` and the forcing comparisons `normH, normR ≤ normB`.
  -- ====================================================================
  have hRJensen : avgR ≤ normR :=
    setLAverage_le_rpow_setLAverage_sq hVol0 hVoltop hRmeasR
  -- `‖R‖ ≤ ‖h‖ + ‖R‖` pointwise (same ball `4B`), so `normR ≤ normB`.
  have hnormR_le : normR ≤ normB := by
    rw [hnormR_def, hnormB_def]; gcongr with z
    filter_upwards with z; gcongr; exact le_add_self
  -- Ball-transfer for nonnegative integrands: `⨍⁻_{2B} g ≤ 4·⨍⁻_{4B} g`, since
  -- `∫⁻_{2B} ≤ ∫⁻_{4B}` (subset) and `|4B| = 4·|2B|`.
  have htransfer : ∀ g : ℂ → ℝ≥0∞, (⨍⁻ z in B2, g z ∂volume) ≤ 4 * ⨍⁻ z in B4, g z ∂volume := by
    intro g
    rw [setLAverage_eq, setLAverage_eq, hvol_ratio, mul_div_assoc',
      ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]
    gcongr
  -- `normH ≤ 2·normB`: pointwise `‖R‖² ≤ (‖h‖+‖R‖)²` on `2B`, then transfer `2B → 4B`
  -- (factor `4` under the root becomes `2`).
  have hnormH_le2 : normH ≤ 2 * normB := by
    have hstep : normH ≤ (⨍⁻ z in B2, ((‖h z‖₊ : ℝ≥0∞) + (‖R z‖₊ : ℝ≥0∞)) ^ (2 : ℝ) ∂volume)
        ^ (1 / (2 : ℝ)) := by
      rw [hnormH_def]
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [setLAverage_eq, setLAverage_eq]
      gcongr
      exact le_add_self
    refine le_trans hstep ?_
    refine le_trans (ENNReal.rpow_le_rpow
      (htransfer (fun z => ((‖h z‖₊ : ℝ≥0∞) + (‖R z‖₊ : ℝ≥0∞)) ^ (2 : ℝ)))
      (by norm_num : (0:ℝ) ≤ 1/2)) ?_
    rw [hnormB_def, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
      show (4 : ℝ≥0∞) ^ (1 / (2:ℝ)) = 2 from by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 from by simp [ENNReal.ofReal_ofNat],
          ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num),
          show (4 : ℝ) ^ (1 / (2:ℝ)) = 2 from by
            rw [show (4:ℝ) = 2^(2:ℝ) from by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num]
        simp [ENNReal.ofReal_ofNat]]
  -- ====================================================================
  -- (Assemble) Substitute N1, the conversion, Jensen, and collect constants.
  -- ====================================================================
  -- `hS`'s gradient ball `ball x (2·(2r))` is `B4 = ball x (4r)`.
  rw [show (2 : ℝ) * (2 * r) = 4 * r from by ring, ← hB4_def, ← havgGxGy_def] at hS
  refine le_trans hC ?_
  have hrne : r ≠ 0 := hr.ne'
  -- `A₃/r · (C₁·2r) = 2·A₃·C₁` (the `r⁻¹` cancels the `r`, leaving the N1@2r factor `2`).
  have hreal : A₃ / r * (C₁ * (2 * r)) = 2 * (A₃ * C₁) := by
    field_simp
  have hofRealA'C :
      ENNReal.ofReal (2 * (A₃ * C₁)) * ENNReal.ofReal A' = ENNReal.ofReal (2 * (A₃ * C₁ * A')) := by
    rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  -- First term: `(A₃/r)·oscF ≤ ofReal(2·A₃·C₁·A')·avgG + ofReal(4·A₃·C₁)·normB`.
  have hterm1 : ENNReal.ofReal (A₃ / r) * oscF ≤
      ENNReal.ofReal (2 * (A₃ * C₁ * A')) * avgG + ENNReal.ofReal (4 * (A₃ * C₁)) * normB := by
    calc ENNReal.ofReal (A₃ / r) * oscF
        ≤ ENNReal.ofReal (A₃ / r) * (ENNReal.ofReal (C₁ * (2 * r)) * avgGxGy) := by
          gcongr
      _ = ENNReal.ofReal (2 * (A₃ * C₁)) * avgGxGy := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hreal]
      _ ≤ ENNReal.ofReal (2 * (A₃ * C₁)) * (ENNReal.ofReal A' * avgG + 2 * avgR) := by gcongr
      _ = ENNReal.ofReal (2 * (A₃ * C₁ * A')) * avgG + ENNReal.ofReal (4 * (A₃ * C₁)) * avgR := by
          have hgrad : ENNReal.ofReal (2 * (A₃ * C₁)) * (ENNReal.ofReal A' * avgG)
              = ENNReal.ofReal (2 * (A₃ * C₁ * A')) * avgG := by
            rw [← mul_assoc, hofRealA'C]
          have hforc : ENNReal.ofReal (2 * (A₃ * C₁)) * (2 * avgR)
              = ENNReal.ofReal (4 * (A₃ * C₁)) * avgR := by
            rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by simp [ENNReal.ofReal_ofNat],
              ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            congr 2; ring
          rw [mul_add, hgrad, hforc]
      _ ≤ ENNReal.ofReal (2 * (A₃ * C₁ * A')) * avgG + ENNReal.ofReal (4 * (A₃ * C₁)) * normB := by
          gcongr
          exact le_trans hRJensen hnormR_le
  -- Second term: `A₃·normH ≤ A₃·(2·normB) = ofReal(2·A₃)·normB` (via the `2B → 4B` transfer).
  have hterm2 : ENNReal.ofReal A₃ * normH ≤ ENNReal.ofReal (2 * A₃) * normB := by
    calc ENNReal.ofReal A₃ * normH
        ≤ ENNReal.ofReal A₃ * (2 * normB) := by gcongr
      _ = ENNReal.ofReal (2 * A₃) * normB := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by simp [ENNReal.ofReal_ofNat],
            ← mul_assoc, ← ENNReal.ofReal_mul hA₃, mul_comm A₃ 2]
  -- Combine: the two `normB` coefficients add to `4·A₃·C₁ + 2·A₃`; both they and the
  -- gradient coefficient `2·A₃·C₁·A'` are `≤ Afin`.
  have hAC0 : 0 ≤ A₃ * C₁ := mul_nonneg hA₃ hC₁
  have hACA'0 : 0 ≤ A₃ * C₁ * A' := mul_nonneg hAC0 hA'0
  have hAfin_grad : ENNReal.ofReal (2 * (A₃ * C₁ * A')) ≤ ENNReal.ofReal Afin :=
    ENNReal.ofReal_le_ofReal (by rw [hAfin_def]; nlinarith [hACA'0, hAC0, hA₃])
  have hAfin_forc :
      ENNReal.ofReal (4 * (A₃ * C₁)) + ENNReal.ofReal (2 * A₃) ≤ ENNReal.ofReal Afin := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by rw [hAfin_def]; nlinarith [hACA'0, hAC0, hA₃])
  calc ENNReal.ofReal (A₃ / r) * oscF + ENNReal.ofReal A₃ * normH
      ≤ (ENNReal.ofReal (2 * (A₃ * C₁ * A')) * avgG + ENNReal.ofReal (4 * (A₃ * C₁)) * normB)
          + ENNReal.ofReal (2 * A₃) * normB := add_le_add hterm1 hterm2
    _ = ENNReal.ofReal (2 * (A₃ * C₁ * A')) * avgG
          + (ENNReal.ofReal (4 * (A₃ * C₁)) + ENNReal.ofReal (2 * A₃)) * normB := by
        rw [add_assoc, add_mul]
    _ ≤ ENNReal.ofReal Afin * avgG + ENNReal.ofReal Afin * normB := by
        gcongr


end NoWanderingDomains
