/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.SingularIntegral.GehringHigherIntegrability.SelfImprovement

/-!
# Gehring self-improvement: the restated Beltrami higher-integrability residual (S3)

`beltrami_fixedPoint_memLpLocOn` — assembling S0 + S1 + S2 into the higher-integrability
conclusion for the `L²` Beltrami fixed point, the residual consumed by
`Beurling/Beltrami.lean`.
-/

open MeasureTheory Complex Filter
open scoped ENNReal NNReal Topology Real Pointwise

namespace NoWanderingDomains

/-! ## S3 — the restated Beltrami higher-integrability residual -/

/-- **Auxiliary: local-`L²` ⟹ local lintegral finiteness of `‖·‖²`.** From `MemLp F 2`
the squared `ℝ≥0∞`-enorm has finite lower integral on every compact set — the
loc-`Lᵠ` hypothesis (with `q = 2`) that the Gehring lemma S2 consumes. -/
private theorem lintegral_enorm_sq_lt_top_of_memLp {F : ℂ → ℂ} (hF : MemLp F 2 volume)
    (K : Set ℂ) : ∫⁻ z in K, (‖F z‖₊ : ℝ≥0∞) ^ (2 : ℝ) < ⊤ := by
  have hFK : MemLp F 2 (volume.restrict K) := hF.restrict K
  have h2ne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hlt := hFK.eLpNorm_lt_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2ne h2top] at hlt
  have htoReal : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [htoReal] at hlt
  have hbase : (∫⁻ z, ‖F z‖ₑ ^ (2 : ℝ) ∂volume.restrict K) < ⊤ := by
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    rw [htop] at hlt
    simp only [ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 1/2)] at hlt
    exact (lt_irrefl _ hlt)
  simpa only [enorm_eq_nnnorm] using hbase

/-- **Auxiliary: `MemLp F (ofReal s)` ⟹ local lintegral finiteness of `‖·‖^t` for
`0 < t ≤ s`.** From `MemLp F (ofReal s)`, on every compact `K` the `t`-th `ℝ≥0∞`-enorm
power has finite lower integral whenever `0 < t ≤ s`: restrict to `K` (a finite
measure on a compact set), drop the exponent to `ofReal t ≤ ofReal s` by
`MemLp.mono_exponent`, and unfold `eLpNorm`. This is the forcing-term finiteness the
corrected Gehring lemma S2 consumes at the higher integrability exponent `t = 2 + ε`,
supplied by the `δ = 1` datum `MemLp h 3` (`s = 3`). -/
private theorem lintegral_enorm_rpow_lt_top_of_memLp {F : ℂ → ℂ} {s t : ℝ}
    (ht0 : 0 < t) (hts : t ≤ s) (hF : MemLp F (ENNReal.ofReal s) volume)
    (K : Set ℂ) (hK : IsCompact K) : ∫⁻ z in K, (‖F z‖₊ : ℝ≥0∞) ^ t < ⊤ := by
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hFKs : MemLp F (ENNReal.ofReal s) (volume.restrict K) := hF.restrict K
  have hFKt : MemLp F (ENNReal.ofReal t) (volume.restrict K) :=
    hFKs.mono_exponent (ENNReal.ofReal_le_ofReal hts)
  have htne : ENNReal.ofReal t ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, ht0]
  have httop : ENNReal.ofReal t ≠ ⊤ := ENNReal.ofReal_ne_top
  have hlt := hFKt.eLpNorm_lt_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal htne httop] at hlt
  have htoReal : (ENNReal.ofReal t).toReal = t := ENNReal.toReal_ofReal ht0.le
  rw [htoReal] at hlt
  have hbase : (∫⁻ z, ‖F z‖ₑ ^ t ∂volume.restrict K) < ⊤ := by
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    rw [htop] at hlt
    simp only [ENNReal.top_rpow_of_pos (by positivity : (0:ℝ) < 1 / t)] at hlt
    exact (lt_irrefl _ hlt)
  simpa only [enorm_eq_nnnorm] using hbase

/-- **Auxiliary: local lintegral finiteness of `‖G‖^q` ⟹ `MemLpLocOn G (ofReal q)`.**
Repackages the Gehring conclusion (`∫⁻_K ‖G‖^q < ⊤` for every compact `K`) as
`MemLpLocOn`. -/
private theorem memLpLocOn_of_lintegral_lt_top {G : ℂ → ℂ} {q : ℝ} (hq0 : 0 < q)
    (hGae : AEStronglyMeasurable G volume)
    (hfin : ∀ K : Set ℂ, IsCompact K → ∫⁻ z in K, (‖G z‖₊ : ℝ≥0∞) ^ q < ⊤) :
    MemLpLocOn G (ENNReal.ofReal q) Set.univ := by
  intro K _ hK
  have hofReal_ne0 : ENNReal.ofReal q ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, hq0]
  have hofReal_ne_top : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨hGae.restrict, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hofReal_ne0 hofReal_ne_top]
  have htoReal : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hq0.le
  rw [htoReal]
  have hfinK : (∫⁻ z, ‖G z‖ₑ ^ q ∂volume.restrict K) < ⊤ := by
    have hgK := hfin K hK
    have heq : (∫⁻ z in K, (‖G z‖₊ : ℝ≥0∞) ^ q) = (∫⁻ z, ‖G z‖ₑ ^ q ∂volume.restrict K) := by
      simp [enorm_eq_nnnorm]
    rwa [heq] at hgK
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
  exact hfinK.ne

/-- **S3 (`beltrami_fixedPoint_memLpLocOn`).** The restated (decoupled) higher-
integrability residual, in **uniform-exponent** form. With `μ` fixed (`‖μ‖∞ < 1`), there
is a single exponent `q > 2` — depending only on `μ` — such that **every** `L²` Beltrami
fixed point `G = h + T(μ·G)` that is the weak holomorphic gradient `G = ½(Gx − I·Gy)` of a
compactly-supported `W^{1,2}` primitive `F` is locally `Lᵠ`, with no `Lᵖ` hypothesis on `h`.

The exponent is quantified *outside* the fixed-point bundle `(F, G, Gx, Gy, h)`: this
records the classical fact that Gehring's gain `ε` depends only on `‖μ‖∞` (via the
reverse-Hölder constant `A` from S1 and the dimension), not on the particular solution. The
downstream consumer L6 (`dz_memLpLocOn_of_beltrami`) needs exactly this uniformity, since it
applies the residual to a cutoff fixed point whose data varies with the compact set; L5
(`dz_cutoff_eq_beurling_repr`) supplies the primitive bundle for each such fixed point.

*Proof.* `reverseHolder_of_weakGradient` (S1) gives a reverse-Hölder constant `A` depending
only on `μ`; `gehring_selfImprovement` (S2) turns the pair `(q = 2, A)` into a uniform gain
`ε > 0`. Set `q := 2 + ε`. For each fixed point, the primitive bundle `(F, Gx, Gy)` feeds
S1's reverse-Hölder inequality for `(‖G‖, ‖h‖)`, the `MemLp _ 2` data supplies the loc-`L²`
hypotheses (`lintegral_enorm_sq_lt_top_of_memLp`), so S2 yields `∫⁻_K ‖G‖^{2+ε} < ⊤` on
every compact `K`, which `memLpLocOn_of_lintegral_lt_top` repackages as
`MemLpLocOn G (ofReal (2+ε)) univ`. -/
theorem beltrami_fixedPoint_memLpLocOn {μ : ℂ → ℂ}
    (hμmeas : Measurable μ) (hμfin : eLpNormEssSup μ volume ≠ ⊤)
    (hμbound : eLpNormEssSup μ volume < 1) :
    ∃ q : ℝ, 2 < q ∧ ∀ {F G Gx Gy h R : ℂ → ℂ},
      HasCompactSupport F → MemLp F 2 volume → MemLp G 2 volume →
      MemLp h 2 volume → MemLp h 3 volume →
      MemLp Gx 2 volume → MemLp Gy 2 volume →
      HasWeakDirDeriv 1 Gx F Set.univ → HasWeakDirDeriv Complex.I Gy F Set.univ →
      (∀ z, G z = (1 / 2 : ℂ) * (Gx z - Complex.I * Gy z)) →
      G =ᵐ[volume] h + beurling (fun z => μ z * G z) →
      MemLp R 2 volume → MemLp R 3 volume →
      (∀ᵐ z, (1 / 2 : ℂ) * (Gx z + Complex.I * Gy z) = μ z * G z + R z) →
        MemLpLocOn G (ENNReal.ofReal q) Set.univ := by
  classical
  -- S1: the uniform reverse-Hölder constant `A` (depending only on `μ`).
  obtain ⟨A, hA, hRH⟩ := reverseHolder_of_weakGradient hμmeas hμfin hμbound
  -- S2: the uniform exponent gain `ε₀` (depending only on `q = 2`
  -- and `A`). The gain is achievable at any `ε ≤ ε₀`; we take `ε := min ε₀ 1` so that the
  -- higher-integrability exponent `2 + ε ≤ 3` is supplied by the `δ = 1` datum `MemLp h 3`.
  obtain ⟨ε₀, hε₀, hgain⟩ := gehring_selfImprovement (q := 2) (A := A) (by norm_num) hA
  set ε : ℝ := min ε₀ 1 with hε_def
  have hεpos : 0 < ε := lt_min hε₀ (by norm_num)
  have hεle₀ : ε ≤ ε₀ := min_le_left _ _
  have hεle1 : ε ≤ 1 := min_le_right _ _
  refine ⟨2 + ε, by linarith, ?_⟩
  -- Fix an arbitrary `L²` Beltrami fixed point bundle `(F, G, Gx, Gy, h, R)`, now also
  -- equipped with the `δ = 1` higher integrability `MemLp h 3`, `MemLp R 3`, and the
  -- antiholomorphic relation `½(Gx + I·Gy) =ᵐ μ·G + R`.
  intro F G Gx Gy h R hFcs hFmem hGmem hhmem hhmem3 hGxmem hGymem hGxweak hGyweak hGdef hGeq
    hRmem hRmem3 hRrel
  have hq0 : (0 : ℝ) < 2 + ε := by linarith
  -- The weights for the abstract Gehring lemma. The forcing `b` is the **combined** `L²`/`L³`
  -- inhomogeneity `‖h‖ + ‖R‖`: S1 (the corrected reverse-Hölder) converts the full gradient
  -- `‖Gx‖ + ‖Gy‖` back to `‖G‖` plus a `‖R‖` term (Wirtinger), and folds it together with the
  -- N3 inhomogeneity `‖h‖` into this single forcing.
  set w : ℂ → ℝ≥0∞ := fun z => (‖G z‖₊ : ℝ≥0∞) with hw_def
  set b : ℂ → ℝ≥0∞ := fun z => (‖h z‖₊ : ℝ≥0∞) + (‖R z‖₊ : ℝ≥0∞) with hb_def
  have hGae : AEStronglyMeasurable G volume := hGmem.1
  have hhae : AEStronglyMeasurable h volume := hhmem.1
  have hRae : AEStronglyMeasurable R volume := hRmem.1
  have hwmeas : AEMeasurable w volume := by
    refine (hGae.enorm).congr ?_; filter_upwards with z; simp [hw_def, enorm_eq_nnnorm]
  have hbmeas : AEMeasurable b volume := by
    have hh' : AEMeasurable (fun z => (‖h z‖₊ : ℝ≥0∞)) volume := by
      refine (hhae.enorm).congr ?_; filter_upwards with z; simp [enorm_eq_nnnorm]
    have hR' : AEMeasurable (fun z => (‖R z‖₊ : ℝ≥0∞)) volume := by
      refine (hRae.enorm).congr ?_; filter_upwards with z; simp [enorm_eq_nnnorm]
    simpa only [hb_def] using! hh'.add hR'
  -- Loc-`L²` of `w = ‖G‖` (the weight at the base exponent `q = 2`).
  have hwloc : ∀ K : Set ℂ, IsCompact K → ∫⁻ z in K, w z ^ (2 : ℝ) < ⊤ :=
    fun K _ => by simpa only [hw_def] using lintegral_enorm_sq_lt_top_of_memLp hGmem K
  -- The forcing `b = ‖h‖ + ‖R‖` at the STRICTLY HIGHER exponent `2 + ε`: this is what the
  -- corrected Gehring lemma consumes. Supplied by `MemLp h 3` and `MemLp R 3` (`2 + ε ≤ 3`):
  -- `(‖h‖ + ‖R‖)^p ≤ 2^{p-1}(‖h‖^p + ‖R‖^p)` and both pieces have finite local lintegral.
  have hhmem3' : MemLp h (ENNReal.ofReal 3) volume := by
    rw [show (ENNReal.ofReal 3 : ℝ≥0∞) = 3 from by norm_num]; exact hhmem3
  have hRmem3' : MemLp R (ENNReal.ofReal 3) volume := by
    rw [show (ENNReal.ofReal 3 : ℝ≥0∞) = 3 from by norm_num]; exact hRmem3
  have hbloc : ∀ K : Set ℂ, IsCompact K → ∫⁻ z in K, b z ^ (2 + ε) < ⊤ := by
    intro K hK
    -- `b^{2+ε} ≤ 2^{1+ε}(‖h‖^{2+ε} + ‖R‖^{2+ε})` pointwise.
    have hpt : ∀ z, b z ^ (2 + ε) ≤ (2 : ℝ≥0∞) ^ (1 + ε) *
        ((‖h z‖₊ : ℝ≥0∞) ^ (2 + ε) + (‖R z‖₊ : ℝ≥0∞) ^ (2 + ε)) := by
      intro z
      have h2e : (2 + ε) - 1 = 1 + ε := by ring
      have hbnd := ENNReal.rpow_add_le_mul_rpow_add_rpow (‖h z‖₊ : ℝ≥0∞) (‖R z‖₊ : ℝ≥0∞)
        (p := 2 + ε) (by linarith)
      rw [h2e] at hbnd
      simpa only [hb_def] using hbnd
    -- Measurability of the first summand `z ↦ ‖h z‖ₑ^{2+ε}` (restricted to `K`).
    have hmeas_h : AEMeasurable (fun z => (‖h z‖₊ : ℝ≥0∞) ^ (2 + ε))
        (volume.restrict K) := by
      have : AEMeasurable (fun z => (‖h z‖₊ : ℝ≥0∞)) (volume.restrict K) := by
        refine (hhae.enorm.restrict).congr ?_; filter_upwards with z; simp [enorm_eq_nnnorm]
      exact this.pow_const _
    refine lt_of_le_of_lt (setLIntegral_mono' hK.measurableSet (fun z _ => hpt z)) ?_
    rw [lintegral_const_mul' _ _ (by
      exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (by norm_num)),
      lintegral_add_left' hmeas_h]
    refine ENNReal.mul_lt_top (by
      exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (by norm_num)) ?_
    exact ENNReal.add_lt_top.2
      ⟨lintegral_enorm_rpow_lt_top_of_memLp (by linarith) (by linarith) hhmem3' K hK,
       lintegral_enorm_rpow_lt_top_of_memLp (by linarith) (by linarith) hRmem3' K hK⟩
  -- The reverse-Hölder inequality for this fixed point, from S1 (fed the primitive bundle and
  -- the antiholomorphic relation): it now carries the COMBINED forcing `b² = (‖h‖ + ‖R‖)²`.
  have hRHGh :=
    hRH hFcs hFmem hGmem hhmem hGxmem hGymem hGxweak hGyweak hGdef hGeq hRmem hRrel
  -- S2's conclusion: `∫⁻_K ‖G‖^{2+ε} < ⊤` on every compact `K`.
  have hfin : ∀ K : Set ℂ, IsCompact K → ∫⁻ z in K, w z ^ (2 + ε) < ⊤ :=
    hgain hεpos hεle₀ hwmeas hbmeas hwloc hbloc hRHGh
  -- Repackage as `MemLpLocOn`.
  refine memLpLocOn_of_lintegral_lt_top hq0 hGae ?_
  intro K hK
  simpa only [hw_def] using hfin K hK


end NoWanderingDomains
