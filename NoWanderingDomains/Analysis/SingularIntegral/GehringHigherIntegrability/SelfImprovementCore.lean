/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.SingularIntegral.GehringHigherIntegrability.ReverseHolder

/-!
# Gehring self-improvement: the Calderón–Zygmund good-λ core (S2, part I)

The radius hole-filling iteration `giaquinta_iteration` and the Calderón–Zygmund stopping /
good-λ machinery that the abstract Gehring lemma runs over: the dyadic reverse-Hölder
transfer, the Vitali/Carleson density and engine bounds, the global dyadic cover, and the
honest exponent-1 good-λ integral `gehring_goodLambda_integral_core`.
-/

open MeasureTheory Complex Filter
open scoped ENNReal NNReal Topology Real Pointwise

namespace NoWanderingDomains

/-! ## S2 — the general Gehring self-improvement lemma -/

/-- **Giaquinta–Giusti iteration lemma.** A nonnegative function `Z` that is bounded
on `[r, R]` and satisfies the hole-filling inequality
`Z t ≤ θ · Z s + A / (s - t)^α + B` for every `r ≤ t < s ≤ R` (with `0 ≤ θ < 1`,
`α > 0`, `A, B ≥ 0`) is controlled at the inner endpoint by the data at scale `R - r`:
`Z r ≤ c(α, θ) · (A / (R - r)^α + B)`, with `c` depending only on `α` and `θ`.

This is the standard absorption device (Giusti, *Direct Methods in the Calculus of
Variations*, Lemma 6.1): the smallness `θ < 1` is iterated along a geometric chain of
radii `r = ρ₀ < ρ₁ < ⋯ → R` (with ratio `τ ∈ (θ^{1/α}, 1)`, so `θ·τ^{-α} < 1`), summing
the geometric series; the boundedness `Z ≤ M` makes the tail `θ^k · Z(ρ_k) → 0`.  It is
what closes the G2 layer-cake of `gehring_selfImprovement`, absorbing the reconstructed
`w^{q+ε}`-mass over the enlargement `16B₀` back onto the inner ball `4B₀`. -/
theorem giaquinta_iteration {α θ : ℝ} (hα : 0 < α) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ {Z : ℝ → ℝ} {r R A B M : ℝ}, r < R → 0 ≤ A → 0 ≤ B →
        (∀ t ∈ Set.Icc r R, 0 ≤ Z t) →
        (∀ t ∈ Set.Icc r R, Z t ≤ M) →
        (∀ t s, r ≤ t → t < s → s ≤ R → Z t ≤ θ * Z s + A / (s - t) ^ α + B) →
        Z r ≤ c * (A / (R - r) ^ α + B) := by
  -- STEP 1: choose the ratio τ.
  have hθα0 : (0:ℝ) ≤ θ ^ (1/α) := Real.rpow_nonneg hθ0 _
  have hinvα : (0:ℝ) < 1/α := by positivity
  have hθα1 : θ ^ (1/α) < 1 := Real.rpow_lt_one hθ0 hθ1 hinvα
  set τ : ℝ := (θ ^ (1/α) + 1) / 2 with hτdef
  have hτ_gt : θ ^ (1/α) < τ := by rw [hτdef]; linarith
  have hτ1 : τ < 1 := by rw [hτdef]; linarith
  have hτ0 : 0 < τ := by rw [hτdef]; linarith
  -- τ^α > θ
  have hτα_pos : 0 < τ ^ α := Real.rpow_pos_of_pos hτ0 α
  have hθlt : θ < τ ^ α := by
    have h := Real.rpow_lt_rpow hθα0 hτ_gt hα
    rwa [← Real.rpow_mul hθ0, one_div_mul_cancel hα.ne', Real.rpow_one] at h
  -- q₀ := θ / τ^α
  set q₀ : ℝ := θ / τ ^ α with hq0def
  have hq0_nonneg : 0 ≤ q₀ := by rw [hq0def]; positivity
  have hq0_lt : q₀ < 1 := by
    rw [hq0def, div_lt_one hτα_pos]; exact hθlt
  -- STEP 2: the constant.
  have h1τ : 0 < 1 - τ := by linarith
  have h1q0 : 0 < 1 - q₀ := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  have h1τα_pos : 0 < (1 - τ) ^ (-α) := Real.rpow_pos_of_pos h1τ _
  set c : ℝ := max ((1 - τ) ^ (-α) / (1 - q₀)) (1 / (1 - θ)) with hcdef
  have hc_nonneg : 0 ≤ c := by
    rw [hcdef]; apply le_max_of_le_right; positivity
  refine ⟨c, hc_nonneg, ?_⟩
  -- STEP 3: the ∀-body.
  intro Z r R A B M hrR hA hB hZpos hZbdd hstep
  have hRr : 0 < R - r := by linarith
  have hM0 : 0 ≤ M := le_trans (hZpos r ⟨le_refl r, hrR.le⟩) (hZbdd r ⟨le_refl r, hrR.le⟩)
  -- radius chain
  set ρ : ℕ → ℝ := fun i => r + (1 - τ ^ i) * (R - r) with hρdef
  have hρ0 : ρ 0 = r := by simp [hρdef]
  have hτi_nonneg : ∀ i, (0:ℝ) ≤ τ ^ i := fun i => pow_nonneg hτ0.le i
  have hτi_le_one : ∀ i, τ ^ i ≤ 1 := fun i => pow_le_one₀ hτ0.le hτ1.le
  have hρ_mem : ∀ i, ρ i ∈ Set.Icc r R := by
    intro i
    constructor
    · simp only [hρdef]; nlinarith [hτi_le_one i, hRr, hτi_nonneg i]
    · simp only [hρdef]; nlinarith [hτi_nonneg i, hRr, hτi_le_one i]
  have hρ_ge_r : ∀ i, r ≤ ρ i := fun i => (hρ_mem i).1
  have hρ_le_R : ∀ i, ρ i ≤ R := fun i => (hρ_mem i).2
  -- the gap
  have hgap : ∀ i, ρ (i+1) - ρ i = (τ ^ i) * (1 - τ) * (R - r) := by
    intro i
    simp only [hρdef, pow_succ]
    ring
  have hgap_pos : ∀ i, 0 < ρ (i+1) - ρ i := by
    intro i
    rw [hgap i]
    have : 0 < τ ^ i := pow_pos hτ0 i
    positivity
  have hρ_mono : ∀ i, ρ i < ρ (i+1) := fun i => by linarith [hgap_pos i]
  -- gap rpow
  have hgap_rpow : ∀ i, (ρ (i+1) - ρ i) ^ α = (τ ^ α) ^ i * (1 - τ) ^ α * (R - r) ^ α := by
    intro i
    rw [hgap i, Real.mul_rpow (by positivity) hRr.le, Real.mul_rpow (hτi_nonneg i) h1τ.le]
    congr 2
    rw [← Real.rpow_natCast τ i, ← Real.rpow_natCast (τ ^ α) i, ← Real.rpow_mul hτ0.le,
        ← Real.rpow_mul hτ0.le, mul_comm]
  -- D and Dstep
  set D : ℝ := A * (1 - τ) ^ (-α) * (R - r) ^ (-α) with hDdef
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  set Dstep : ℕ → ℝ := fun i => A / (ρ (i+1) - ρ i) ^ α with hDstepdef
  have hDstep_val : ∀ i, Dstep i = D * ((τ ^ α) ^ i)⁻¹ := by
    intro i
    simp only [hDstepdef, hgap_rpow i, hDdef]
    rw [Real.rpow_neg h1τ.le, Real.rpow_neg hRr.le]
    field_simp
  have hDstep_nonneg : ∀ i, 0 ≤ Dstep i := by
    intro i
    simp only [hDstepdef]
    exact div_nonneg hA (Real.rpow_nonneg (hgap_pos i).le α)
  -- per-step bound: θ^i * Dstep i = D * q₀^i
  have hstep_geom : ∀ i, θ ^ i * Dstep i = D * q₀ ^ i := by
    intro i
    rw [hDstep_val i, hq0def, div_pow]
    have : (τ ^ α) ^ i ≠ 0 := by positivity
    field_simp
  -- the per-step inequality from hstep
  have hper : ∀ i, Z (ρ i) ≤ θ * Z (ρ (i+1)) + Dstep i + B := by
    intro i
    have h := hstep (ρ i) (ρ (i+1)) (hρ_ge_r i) (hρ_mono i) (hρ_le_R (i+1))
    simpa only [hDstepdef] using h
  -- TELESCOPE
  have htele : ∀ k, Z (ρ 0) ≤ θ ^ k * Z (ρ k) + ∑ i ∈ Finset.range k, θ ^ i * (Dstep i + B) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hθk : (0:ℝ) ≤ θ ^ k := pow_nonneg hθ0 k
        have hstepk := hper k
        have hmul : θ ^ k * Z (ρ k) ≤ θ ^ k * (θ * Z (ρ (k+1)) + Dstep k + B) :=
          mul_le_mul_of_nonneg_left hstepk hθk
        have hexp : θ ^ k * (θ * Z (ρ (k+1)) + Dstep k + B)
            = θ ^ (k+1) * Z (ρ (k+1)) + θ ^ k * (Dstep k + B) := by
          rw [pow_succ]; ring
        rw [Finset.sum_range_succ]
        calc Z (ρ 0) ≤ θ ^ k * Z (ρ k) + ∑ i ∈ Finset.range k, θ ^ i * (Dstep i + B) := ih
          _ ≤ θ ^ k * (θ * Z (ρ (k+1)) + Dstep k + B)
                + ∑ i ∈ Finset.range k, θ ^ i * (Dstep i + B) := by linarith
          _ = θ ^ (k+1) * Z (ρ (k+1))
                + (∑ i ∈ Finset.range k, θ ^ i * (Dstep i + B) + θ ^ k * (Dstep k + B)) := by
              rw [hexp]; ring
  -- bound the sum uniformly
  -- geometric partial sums
  have hgeom_bound : ∀ (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ),
      ∑ i ∈ Finset.range k, x ^ i ≤ 1 / (1 - x) := by
    intro x hx0 hx1 k
    rw [geom_sum_eq (by linarith : x ≠ 1)]
    have hxk : (0:ℝ) ≤ x ^ k := pow_nonneg hx0 k
    have hh1x : (0:ℝ) < 1 - x := by linarith
    have heq : (x ^ k - 1) / (x - 1) = (1 - x ^ k) / (1 - x) := by
      rw [← neg_div_neg_eq]; congr 1 <;> ring
    rw [heq]; gcongr; linarith
  have hsum_bound : ∀ k, ∑ i ∈ Finset.range k, θ ^ i * (Dstep i + B)
      ≤ D / (1 - q₀) + B / (1 - θ) := by
    intro k
    have hsplit : ∑ i ∈ Finset.range k, θ ^ i * (Dstep i + B)
        = (∑ i ∈ Finset.range k, θ ^ i * Dstep i) + B * ∑ i ∈ Finset.range k, θ ^ i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _; ring
    rw [hsplit]
    have hA1 : (∑ i ∈ Finset.range k, θ ^ i * Dstep i)
        = D * ∑ i ∈ Finset.range k, q₀ ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _; exact hstep_geom i
    rw [hA1]
    have hb1 : D * ∑ i ∈ Finset.range k, q₀ ^ i ≤ D / (1 - q₀) := by
      rw [div_eq_mul_one_div]
      apply mul_le_mul_of_nonneg_left (hgeom_bound q₀ hq0_nonneg hq0_lt k) hD0
    have hb2 : B * ∑ i ∈ Finset.range k, θ ^ i ≤ B / (1 - θ) := by
      rw [div_eq_mul_one_div]
      apply mul_le_mul_of_nonneg_left (hgeom_bound θ hθ0 hθ1 k) hB
    linarith
  -- combine: ∀ k, Z r ≤ θ^k * Z(ρ k) + (D/(1-q₀) + B/(1-θ))
  set C : ℝ := D / (1 - q₀) + B / (1 - θ) with hCdef
  have hbound_k : ∀ k, Z r ≤ θ ^ k * Z (ρ k) + C := by
    intro k
    have h1 := htele k
    have h2 := hsum_bound k
    rw [hρ0] at h1
    linarith
  -- LIMIT k→∞
  have htend_left : Tendsto (fun k : ℕ => θ ^ k * Z (ρ k)) atTop (𝓝 0) := by
    apply squeeze_zero (g := fun k : ℕ => θ ^ k * M)
    · intro k
      have hZk := hZpos (ρ k) (hρ_mem k)
      have hθk : (0:ℝ) ≤ θ ^ k := pow_nonneg hθ0 k
      positivity
    · intro k
      have hZk := hZbdd (ρ k) (hρ_mem k)
      have hθk : (0:ℝ) ≤ θ ^ k := pow_nonneg hθ0 k
      exact mul_le_mul_of_nonneg_left hZk hθk
    · have : Tendsto (fun k : ℕ => θ ^ k * M) atTop (𝓝 (0 * M)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const M
      simpa using this
  have hZr_le_C : Z r ≤ C := by
    have htend_rhs : Tendsto (fun k : ℕ => θ ^ k * Z (ρ k) + C) atTop (𝓝 (0 + C)) :=
      htend_left.add_const C
    have htend_lhs : Tendsto (fun _ : ℕ => Z r) atTop (𝓝 (Z r)) := tendsto_const_nhds
    have := le_of_tendsto_of_tendsto' htend_lhs htend_rhs hbound_k
    simpa using this
  -- FINISH: C = (1-τ)^(-α)/(1-q₀) * (A/(R-r)^α) + (1/(1-θ)) * B ≤ c*(A/(R-r)^α + B)
  have hRrα_pos : 0 < (R - r) ^ α := Real.rpow_pos_of_pos hRr α
  have hAdiv_nonneg : 0 ≤ A / (R - r) ^ α := by positivity
  -- rewrite C
  have hCval : C = ((1 - τ) ^ (-α) / (1 - q₀)) * (A / (R - r) ^ α) + (1 / (1 - θ)) * B := by
    rw [hCdef, hDdef]
    rw [Real.rpow_neg hRr.le]
    field_simp
  rw [hCval] at hZr_le_C
  -- bound coefficients by c
  have hcoef1 : (1 - τ) ^ (-α) / (1 - q₀) ≤ c := by rw [hcdef]; exact le_max_left _ _
  have hcoef2 : 1 / (1 - θ) ≤ c := by rw [hcdef]; exact le_max_right _ _
  calc Z r ≤ ((1 - τ) ^ (-α) / (1 - q₀)) * (A / (R - r) ^ α) + (1 / (1 - θ)) * B := hZr_le_C
    _ ≤ c * (A / (R - r) ^ α) + c * B := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hcoef1 hAdiv_nonneg
        · exact mul_le_mul_of_nonneg_right hcoef2 hB
    _ = c * (A / (R - r) ^ α + B) := by ring

/-- **Dyadic reverse-Hölder transfer** (private copy for `gehring_selfImprovement`).  A
metric-ball reverse-Hölder inequality with the fixed enlargement factor `4` (the hypothesis
form consumed by `gehring_selfImprovement`) yields a reverse-Hölder inequality on every dyadic
square `R = dyadicSquare m k`, with the right-hand side over the comparable ball about the
square's centre of radius `4 · 2^m`.  Kept as a module-local copy; the standalone public
version was a superseded duplicate and has been removed. -/
theorem dyadic_reverseHolder' {q A : ℝ} (hq : 1 < q) (_hA : 0 ≤ A)
    {w b : ℂ → ℝ≥0∞}
    (hRH : ∀ (x : ℂ) (r : ℝ), 0 < r →
      (⨍⁻ z in Metric.ball x r, w z ^ q ∂volume) ^ (1 / q) ≤
        ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), w z ∂volume) +
          ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), b z ^ q ∂volume) ^ (1 / q))
    (m : ℤ) (k : ℤ × ℤ) :
    (⨍⁻ z in dyadicSquare m k, w z ^ q ∂volume) ^ (1 / q) ≤
      ENNReal.ofReal (Real.pi ^ (1 / q) * A) *
          (⨍⁻ z in Metric.ball (dyadicCenter m k) (4 * (2 : ℝ) ^ m), w z ∂volume) +
        ENNReal.ofReal (Real.pi ^ (1 / q) * A) *
          (⨍⁻ z in Metric.ball (dyadicCenter m k) (4 * (2 : ℝ) ^ m), b z ^ q ∂volume) ^
            (1 / q) := by
  set c := dyadicCenter m k with hc
  set s : ℝ := (2 : ℝ) ^ m with hs
  have hs0 : 0 < s := by rw [hs]; exact zpow_pos (by norm_num) m
  set R := dyadicSquare m k with hR
  set Bs := Metric.ball c s with hBs
  have hq0 : (0 : ℝ) ≤ 1 / q := by positivity
  have hvolR : volume R = ENNReal.ofReal (s ^ 2) := by
    rw [hR, volume_dyadicSquare]
  have hvolBs : volume Bs = ENNReal.ofReal (Real.pi * s ^ 2) := by
    rw [hBs, Complex.volume_ball]
    have hpi : (↑NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
      rw [← NNReal.coe_real_pi]; rw [ENNReal.ofReal_coe_nnreal]
    rw [hpi, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hs0.le, mul_comm]
  have hs2pos : (0 : ℝ) < s ^ 2 := by positivity
  have hvolR0 : volume R ≠ 0 := by
    rw [hvolR, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hs2pos
  have hvolRtop : volume R ≠ ⊤ := by rw [hvolR]; exact ENNReal.ofReal_ne_top
  have hvolBs0 : volume Bs ≠ 0 := by
    rw [hvolBs, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hvolBstop : volume Bs ≠ ⊤ := by rw [hvolBs]; exact ENNReal.ofReal_ne_top
  have hratio : volume Bs / volume R = ENNReal.ofReal Real.pi := by
    rw [hvolR, hvolBs, ENNReal.ofReal_mul Real.pi_pos.le, mul_div_assoc, ENNReal.div_self]
    · rw [mul_one]
    · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hs2pos
    · exact ENNReal.ofReal_ne_top
  have hsubset : R ⊆ Bs := by rw [hR, hBs]; exact dyadicSquare_subset_ball m k
  have hmono : ∫⁻ z in R, w z ^ q ≤ ∫⁻ z in Bs, w z ^ q := lintegral_mono_set hsubset
  have hStepA : (⨍⁻ z in R, w z ^ q ∂volume) ≤
      ENNReal.ofReal Real.pi * (⨍⁻ z in Bs, w z ^ q ∂volume) := by
    rw [setLAverage_eq, setLAverage_eq]
    calc (∫⁻ z in R, w z ^ q ∂volume) / volume R
        ≤ (∫⁻ z in Bs, w z ^ q ∂volume) / volume R := ENNReal.div_le_div_right hmono _
      _ = ((∫⁻ z in Bs, w z ^ q ∂volume) / volume Bs) * (volume Bs / volume R) := by
          rw [← mul_div_assoc, ENNReal.div_mul_cancel hvolBs0 hvolBstop]
      _ = (volume Bs / volume R) * ((∫⁻ z in Bs, w z ^ q ∂volume) / volume Bs) := by rw [mul_comm]
      _ = ENNReal.ofReal Real.pi * ((∫⁻ z in Bs, w z ^ q ∂volume) / volume Bs) := by rw [hratio]
  have hStepB : (⨍⁻ z in R, w z ^ q ∂volume) ^ (1 / q) ≤
      ENNReal.ofReal (Real.pi ^ (1 / q)) * (⨍⁻ z in Bs, w z ^ q ∂volume) ^ (1 / q) := by
    calc (⨍⁻ z in R, w z ^ q ∂volume) ^ (1 / q)
        ≤ (ENNReal.ofReal Real.pi * (⨍⁻ z in Bs, w z ^ q ∂volume)) ^ (1 / q) :=
          ENNReal.rpow_le_rpow hStepA hq0
      _ = ENNReal.ofReal (Real.pi ^ (1 / q)) * (⨍⁻ z in Bs, w z ^ q ∂volume) ^ (1 / q) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq0, ENNReal.ofReal_rpow_of_pos Real.pi_pos]
  have hStepC := hRH c s hs0
  have hpi0 : (0 : ℝ) ≤ Real.pi ^ (1 / q) := by positivity
  calc (⨍⁻ z in R, w z ^ q ∂volume) ^ (1 / q)
      ≤ ENNReal.ofReal (Real.pi ^ (1 / q)) * (⨍⁻ z in Bs, w z ^ q ∂volume) ^ (1 / q) := hStepB
    _ ≤ ENNReal.ofReal (Real.pi ^ (1 / q)) *
          (ENNReal.ofReal A * (⨍⁻ z in Metric.ball c (4 * s), w z ∂volume) +
           ENNReal.ofReal A * (⨍⁻ z in Metric.ball c (4 * s), b z ^ q ∂volume) ^ (1 / q)) :=
        mul_le_mul_right hStepC _
    _ = ENNReal.ofReal (Real.pi ^ (1 / q) * A) * (⨍⁻ z in Metric.ball c (4 * s), w z ∂volume) +
        ENNReal.ofReal (Real.pi ^ (1 / q) * A) *
          (⨍⁻ z in Metric.ball c (4 * s), b z ^ q ∂volume) ^ (1 / q) := by
        rw [mul_add, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hpi0]

/-- **Layer-cake (Cavalieri) for a truncated weight over a ball** (helper for the
hole-filling step of `gehring_selfImprovement`).  For the bounded truncation
`min w N` and any exponent `p > 0`, the `(p)`-mass over a ball is the Cavalieri
integral of the super-level measures of the real-valued truncation `(min w N).toReal`
against the radial weight `λ^{p-1}`.  This is `lintegral_rpow_eq_lintegral_meas_lt_mul`
transported from the real layer (`(min w N).toReal`) to the `ℝ≥0∞` weight, using that
`min w N ≤ N < ⊤` so that `min w N = ofReal ((min w N).toReal)` pointwise. -/
theorem holeFill_layerCake {p : ℝ} (hp : 0 < p) {w : ℂ → ℝ≥0∞}
    (hwmeas : AEMeasurable w volume) (N : ℕ) (x₀ : ℂ) (t : ℝ) :
    ∫⁻ z in Metric.ball x₀ t, (min (w z) (N : ℝ≥0∞)) ^ p
      = ENNReal.ofReal p * ∫⁻ lam in Set.Ioi (0 : ℝ),
          (volume.restrict (Metric.ball x₀ t)) {z | lam < (min (w z) (N : ℝ≥0∞)).toReal}
            * ENNReal.ofReal (lam ^ (p - 1)) := by
  set μ := volume.restrict (Metric.ball x₀ t) with hμ
  set f : ℂ → ℝ := fun z => (min (w z) (N : ℝ≥0∞)).toReal with hf
  have hfnn : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall (fun z => ENNReal.toReal_nonneg)
  have hfmeas : AEMeasurable f μ :=
    ((hwmeas.min aemeasurable_const).ennreal_toReal).restrict
  have key := lintegral_rpow_eq_lintegral_meas_lt_mul μ hfnn hfmeas hp
  rw [← key]
  have hpt : ∀ z, (min (w z) (N : ℝ≥0∞)) ^ p = ENNReal.ofReal (f z ^ p) := by
    intro z
    have hfin : min (w z) (N : ℝ≥0∞) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (min_le_right _ _)
    rw [hf, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le,
      ENNReal.ofReal_toReal hfin]
  calc ∫⁻ z in Metric.ball x₀ t, (min (w z) (N : ℝ≥0∞)) ^ p
      = ∫⁻ z, (min (w z) (N : ℝ≥0∞)) ^ p ∂μ := rfl
    _ = ∫⁻ z, ENNReal.ofReal (f z ^ p) ∂μ := by
        apply lintegral_congr; intro z; rw [hpt z]

/-- A closed ball in `ℂ` is `volume`-a.e. equal to the corresponding open ball (the sphere
is null). -/
private theorem closedBall_aeEq_ball' (c : ℂ) (ρ : ℝ) :
    Metric.closedBall c ρ =ᵐ[volume] Metric.ball c ρ := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · -- `closedBall \ ball ⊆ sphere`, null.
    refine measure_mono_null ?_ (Measure.addHaar_sphere volume c ρ)
    intro z hz
    rw [Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, not_lt] at hz
    rw [Metric.mem_sphere]; linarith [hz.1, hz.2]
  · -- `ball \ closedBall = ∅`.
    convert measure_empty (μ := (volume : Measure ℂ)) using 2
    rw [Set.sdiff_eq_empty]
    exact Metric.ball_subset_closedBall

/-- **Per-point density witness ball** (helper for the good-λ measure bound).  For a
`volume`-globally-integrable nonnegative weight `g : ℂ → ℝ≥0∞` (`∫⁻ g < ⊤`), at a.e. point
`c` the ball averages `(∫⁻_{ball c ρ} g)/vol(ball c ρ)` converge to `g c` as `ρ → 0⁺`;
consequently, for a.e. `c`, any height `Λ < g c`, and any cap `ρ₀ > 0`, there is a radius
`0 < ρ ≤ ρ₀` with `Λ < (∫⁻_{ball c ρ} g)/vol(ball c ρ)`.  Proven from Mathlib's Lebesgue
differentiation (`VitaliFamily.ae_tendsto_lintegral_div` on the uniformly-locally-doubling
Vitali family, transported to closed balls via `tendsto_closedBall_filterAt`) plus the planar
fact that closed and open balls have equal volume and integral. -/
theorem gehring_density_ball {g : ℂ → ℝ≥0∞}
    (hgmeas : AEMeasurable g volume) (hgfin : ∫⁻ z, g z < ⊤) :
    ∀ᵐ c ∂volume, ∀ Λ : ℝ≥0∞, Λ < g c → ∀ ρ₀ : ℝ, 0 < ρ₀ →
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧
        Λ < (∫⁻ z in Metric.ball c ρ, g z) / volume (Metric.ball c ρ) := by
  -- The uniformly-locally-doubling Vitali family for `volume` on `ℂ`.
  set v : VitaliFamily (volume : Measure ℂ) := IsUnifLocDoublingMeasure.vitaliFamily volume 1
    with hv
  -- Lebesgue differentiation: for a.e. `c`, `(∫⁻_a g)/vol a → g c` along `v.filterAt c`.
  filter_upwards [v.ae_tendsto_lintegral_div hgmeas hgfin.ne] with c hc
  intro Λ hΛ ρ₀ hρ₀
  -- A radius sequence `δ n = ρ₀ / (n+1) → 0⁺`.
  set δ : ℕ → ℝ := fun n => ρ₀ / (n + 1) with hδ
  have hδpos : ∀ n, 0 < δ n := fun n => div_pos hρ₀ (by positivity)
  have hδto : Tendsto δ atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall (fun n => hδpos n)⟩
    rw [hδ]
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := ρ₀)).div_atTop h1
  -- Convergence over the closed balls `closedBall c (δ n)`.
  have hclosed : Tendsto
      (fun n : ℕ => (∫⁻ z in Metric.closedBall c (δ n), g z) / volume (Metric.closedBall c (δ n)))
      atTop (𝓝 (g c)) := by
    have htf : Tendsto (fun n : ℕ => Metric.closedBall c (δ n)) atTop (v.filterAt c) := by
      refine IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt
        (μ := (volume : Measure ℂ)) (fun _ => c) δ hδto ?_
      exact Eventually.of_forall (fun n => by
        rw [one_mul]; exact Metric.mem_closedBall_self (hδpos n).le)
    exact hc.comp htf
  -- Switch closed balls to open balls (equal volume and integral in the plane).
  have hcb_eq : ∀ n,
      (∫⁻ z in Metric.closedBall c (δ n), g z) / volume (Metric.closedBall c (δ n))
        = (∫⁻ z in Metric.ball c (δ n), g z) / volume (Metric.ball c (δ n)) := by
    intro n
    have hae := closedBall_aeEq_ball' c (δ n)
    rw [setLIntegral_congr hae, measure_congr hae]
  rw [Filter.tendsto_congr hcb_eq] at hclosed
  -- Eventually the open-ball averages exceed `Λ`.
  have hev : ∀ᶠ n in atTop,
      Λ < (∫⁻ z in Metric.ball c (δ n), g z) / volume (Metric.ball c (δ n)) :=
    hclosed.eventually_const_lt hΛ
  -- Also `δ n ≤ ρ₀` (always).
  have hev2 : ∀ᶠ n in atTop, δ n ≤ ρ₀ := Eventually.of_forall (fun n => by
    rw [hδ, div_le_iff₀ (by positivity)]
    nlinarith [hρ₀.le, (Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  obtain ⟨n, hn1, hn2⟩ := (hev.and hev2).exists
  exact ⟨δ n, hδpos n, hn2, hn1⟩

/-- **Carleson covering bound** (helper for the good-λ measure bound).  Given a level
`l ≠ 0, ⊤`, a weight `u`, a (possibly uncountable) center set `T`, a radius function
`R : ℂ → ℝ` bounded by `Rbd`, with the per-ball averaging property
`l·vol(ball c (R c)) ≤ ∫_{ball c (R c)} u` on `T`, the union of the balls has
`l·vol(⋃_{c∈T} ball c (R c)) ≤ 16·∫⁻ u`.  Lindelöf (`isOpen_biUnion_countable`) extracts a
countable subfamily that preserves the union, then the Carleson Vitali engine
`measure_biUnion_le_lintegral` (planar doubling `A_dbl = 4`, `A_dbl² = 16`)
internalizes the overlap. -/
theorem gehring_engine_bound (l : ℝ≥0∞) (u : ℂ → ℝ≥0∞) (T : Set ℂ) (R : ℂ → ℝ)
    (Rbd : ℝ) (_hRbd : ∀ c ∈ T, R c ≤ Rbd)
    (h2u : ∀ c ∈ T, l * volume (Metric.ball c (R c)) ≤ ∫⁻ z in Metric.ball c (R c), u z) :
    l * volume (⋃ c ∈ T, Metric.ball c (R c)) ≤ (16 : ℝ≥0∞) * ∫⁻ z, u z := by
  have hdbl : (volume : Measure ℂ).IsDoubling (2 ^ Module.finrank ℝ ℂ) :=
    InnerProductSpace.IsDoubling
  -- Extract a countable subfamily preserving the union.
  obtain ⟨Tc, hTcsub, hTccount, hTcU⟩ :=
    TopologicalSpace.isOpen_biUnion_countable (ι := ℂ) T (fun c => Metric.ball c (R c))
      (fun c _ => Metric.isOpen_ball)
  rw [← hTcU]
  -- Engine on the countable family `Tc ⊆ T`.
  have hengine := measure_biUnion_le_lintegral (μ := (volume : Measure ℂ))
    (A := 2 ^ Module.finrank ℝ ℂ) (c := id) (r := R) Tc l u
    (fun c hc => h2u c (hTcsub hc))
  -- `A_dbl² = 16`.
  have hA2 : ((2 ^ Module.finrank ℝ ℂ : ℝ≥0) : ℝ≥0∞) ^ 2 = (16 : ℝ≥0∞) := by
    rw [Complex.finrank_real_complex]; norm_num
  simpa only [id, hA2] using hengine

/-- **Good-λ super-level measure bound** (the Calderón–Zygmund covering core of the
hole-filling step of `gehring_selfImprovement`).  For concentric radii
`4R₀ ≤ t < s ≤ 16R₀`, every truncation `N`, and every height `lam > 0`, the volume of the
super-level set of the truncation `min w N` inside `ball x₀ t` is controlled by a
`(1/lam)`-weighted `w`-mass plus a `(1/lam)^q`-weighted `bᵠ`-mass over the larger ball
`ball x₀ s`:
`vol {z ∈ ball x₀ t | lam < (min w N) z} ≤ ofReal(Cw/lam)·∫_{ball x₀ s} w
    + ofReal((Cb/lam)^q · 16)·∫_{ball x₀ s} bᵠ`
with `Cw = 2(A+1)·16`, `Cb = 2(A+1)`.  Construction: each super-level point has, by Lebesgue
differentiation (`gehring_density_ball`), a small ball `ball c ρ_c` (radius capped at
`(s-t)/8`) with `⨍_{ball c ρ_c} wᵠ > lamᵠ`; the per-ball reverse-Hölder hypothesis `hRH`
splits it into a `w`-dominated and a `b`-dominated alternative; the two subfamilies of
enlarged balls `ball c (4ρ_c) ⊆ ball x₀ s` are fed to the Carleson Vitali engine
`measure_biUnion_le_lintegral` (planar doubling constant `A_dbl = 2² = 4`,
`A_dbl² = 16`), which internalizes the bounded overlap.  This is `w,b`-uniform. -/
theorem gehring_goodLambda_measure {q A : ℝ} (hq : 1 < q) (hA : 0 ≤ A)
    {w b : ℂ → ℝ≥0∞} (hwmeas : AEMeasurable w volume) (_hbmeas : AEMeasurable b volume)
    (hRH : ∀ (x : ℂ) (r : ℝ), 0 < r →
      (⨍⁻ z in Metric.ball x r, w z ^ q ∂volume) ^ (1 / q) ≤
        ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), w z ∂volume) +
          ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), b z ^ q ∂volume) ^ (1 / q))
    (x₀ : ℂ) (R₀ : ℝ) (_hR₀ : 0 < R₀)
    (hWfin : ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q < ⊤)
    (N : ℕ) (t s : ℝ) (_ht : 4 * R₀ ≤ t) (hts : t < s) (hs : s ≤ 16 * R₀)
    (lam : ℝ) (hlam : 0 < lam) :
    volume {z : ℂ | z ∈ Metric.ball x₀ t ∧ lam < (min (w z) (N : ℝ≥0∞)).toReal}
      ≤ ENNReal.ofReal ((2 * (A + 1) / lam) * 16) * (∫⁻ z in Metric.ball x₀ s, w z)
        + ENNReal.ofReal ((2 * (A + 1) / lam) ^ q * 16) *
            (∫⁻ z in Metric.ball x₀ s, b z ^ q) := by
  classical
  -- The planar doubling instance (`A_dbl = 2^finrank ℝ ℂ = 4`) for the Carleson engine.
  have hdbl : (volume : Measure ℂ).IsDoubling (2 ^ Module.finrank ℝ ℂ) :=
    InnerProductSpace.IsDoubling
  have hAdbl : (2 ^ Module.finrank ℝ ℂ : ℝ≥0) = 4 := by
    rw [Complex.finrank_real_complex]; norm_num
  -- Notation.
  have hq0 : 0 < q := lt_trans one_pos hq
  set Ã : ℝ := A + 1 with hÃdef
  have hÃpos : 0 < Ã := by rw [hÃdef]; linarith
  have hÃ0 : 0 ≤ Ã := hÃpos.le
  -- `hRH` upgraded to the larger constant `Ã = A + 1` (RHS only grows).
  have hRHÃ : ∀ (x : ℂ) (r : ℝ), 0 < r →
      (⨍⁻ z in Metric.ball x r, w z ^ q ∂volume) ^ (1 / q) ≤
        ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball x (4 * r), w z ∂volume) +
          ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball x (4 * r), b z ^ q ∂volume) ^ (1 / q) := by
    intro x r hr
    refine le_trans (hRH x r hr) (add_le_add ?_ ?_) <;>
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by rw [hÃdef]; linarith)) _
  -- The localized weight `g = wᵠ · 1_{ball x₀ 16R₀}` (globally integrable).
  set B16 : Set ℂ := Metric.ball x₀ (16 * R₀) with hB16
  set g : ℂ → ℝ≥0∞ := B16.indicator (fun z => w z ^ q) with hgdef
  have hgmeas : AEMeasurable g volume :=
    (hwmeas.pow_const q).indicator measurableSet_ball
  have hgfin : ∫⁻ z, g z < ⊤ := by
    rw [hgdef, lintegral_indicator measurableSet_ball]; exact hWfin
  -- The super-level set.
  set S : Set ℂ := {z : ℂ | z ∈ Metric.ball x₀ t ∧ lam < (min (w z) (N : ℝ≥0∞)).toReal}
    with hSdef
  -- Heights for the density witness: `Λ = (ofReal lam)^q`.
  set Λ : ℝ≥0∞ := ENNReal.ofReal lam ^ q with hΛdef
  -- Capping radius and geometry.
  set ρ₀ : ℝ := (s - t) / 8 with hρ₀def
  have hst : 0 < s - t := by linarith
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀def]; positivity
  -- Step bound from `hWfin`: localize-to-`ball x₀ s` integrals are over a sub-ball of 16R₀.
  have hsubs16 : Metric.ball x₀ s ⊆ B16 := by
    rw [hB16]; exact Metric.ball_subset_ball (by linarith)
  -- =========================================================================
  -- PER-POINT WITNESS.  For a.e. `c ∈ S`, there is a capped ball `ball c ρ` with
  -- `⨍_{ball c ρ} wᵠ > lamᵠ`, and `hRH` yields the `w`/`b` dichotomy.
  -- =========================================================================
  -- The good set: the full-measure set on which the density witness holds.
  set Good : Set ℂ := {c : ℂ | ∀ Λ' : ℝ≥0∞, Λ' < g c → ∀ ρ₀' : ℝ, 0 < ρ₀' →
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀' ∧
        Λ' < (∫⁻ z in Metric.ball c ρ, g z) / volume (Metric.ball c ρ)} with hGooddef
  have hGoodae : volume (Goodᶜ) = 0 := by
    have hae := gehring_density_ball hgmeas hgfin
    rw [MeasureTheory.ae_iff] at hae
    exact hae
  have hDdens : ∀ c ∈ Good, ∀ Λ' : ℝ≥0∞, Λ' < g c → ∀ ρ₀' : ℝ, 0 < ρ₀' →
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀' ∧
        Λ' < (∫⁻ z in Metric.ball c ρ, g z) / volume (Metric.ball c ρ) := fun c hc => hc
  -- For `c ∈ S ∩ D` (a.e. all of `S`), the dichotomy: a capped enlarged ball that is
  -- either `w`-good or `b`-good.
  -- The two scalar levels.
  set lw : ℝ≥0∞ := ENNReal.ofReal (lam / (2 * Ã)) with hlwdef
  set lb : ℝ≥0∞ := ENNReal.ofReal ((lam / (2 * Ã)) ^ q) with hlbdef
  -- Per-point dichotomy.  For `c ∈ S ∩ Good`: a capped radius `ρ` whose enlarged ball
  -- `ball c (4ρ) ⊆ ball x₀ s` is either `w`-good (`lw·vol ≤ ∫ w`) or `b`-good
  -- (`lb·vol ≤ ∫ bᵠ`).
  have hdich : ∀ c ∈ S ∩ Good, ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball c (4 * ρ) ⊆ Metric.ball x₀ s ∧
      (lw * volume (Metric.ball c (4 * ρ)) ≤ ∫⁻ z in Metric.ball c (4 * ρ), w z ∨
       lb * volume (Metric.ball c (4 * ρ)) ≤ ∫⁻ z in Metric.ball c (4 * ρ), b z ^ q) ∧
      4 * ρ ≤ (s - t) / 2 := by
    rintro c ⟨hcS, hcGood⟩
    obtain ⟨hct, hclam⟩ := hcS
    -- `c ∈ B16`.
    have hcB16 : c ∈ B16 := hsubs16 (Metric.ball_subset_ball (by linarith) hct)
    -- `g c = w c ^ q`.
    have hgc : g c = w c ^ q := by rw [hgdef, Set.indicator_of_mem hcB16]
    -- `ofReal lam < w c`.
    have hlam_wc : ENNReal.ofReal lam < w c := by
      have h1 : ENNReal.ofReal lam < min (w c) (N : ℝ≥0∞) := by
        have hfin : min (w c) (N : ℝ≥0∞) ≠ ⊤ :=
          ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (min_le_right _ _)
        rw [← ENNReal.ofReal_toReal hfin]
        exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hlam.le |>.mpr hclam
      exact lt_of_lt_of_le h1 (min_le_left _ _)
    -- `Λ < g c`.
    have hΛlt : Λ < g c := by
      rw [hgc, hΛdef]; exact ENNReal.rpow_lt_rpow hlam_wc hq0
    -- Density witness ball.
    obtain ⟨ρ, hρpos, hρcap, hρavg⟩ := hDdens c hcGood Λ hΛlt ρ₀ hρ₀pos
    -- `ball c ρ ⊆ ball x₀ s` (capped).
    have hballρ_sub : Metric.ball c ρ ⊆ Metric.ball x₀ s := by
      intro z hz
      rw [Metric.mem_ball] at hz ⊢
      rw [Metric.mem_ball] at hct
      have : dist z x₀ ≤ dist z c + dist c x₀ := dist_triangle z c x₀
      have hρle : ρ ≤ (s - t) / 8 := hρcap
      nlinarith [this, hz, hct, hρle, hst]
    have hball4ρ_sub : Metric.ball c (4 * ρ) ⊆ Metric.ball x₀ s := by
      intro z hz
      rw [Metric.mem_ball] at hz ⊢
      rw [Metric.mem_ball] at hct
      have htri : dist z x₀ ≤ dist z c + dist c x₀ := dist_triangle z c x₀
      have hρle : ρ ≤ (s - t) / 8 := hρcap
      nlinarith [htri, hz, hct, hρle, hst]
    refine ⟨ρ, hρpos, hball4ρ_sub, ?_, by linarith [hρcap, hst]⟩
    -- On `ball c ρ ⊆ B16`, `g = wᵠ`, so the density average is the `wᵠ`-average.
    have hballρ_B16 : Metric.ball c ρ ⊆ B16 := hballρ_sub.trans hsubs16
    have hgint : ∫⁻ z in Metric.ball c ρ, g z = ∫⁻ z in Metric.ball c ρ, w z ^ q := by
      refine setLIntegral_congr_fun measurableSet_ball (fun z hz => ?_)
      rw [hgdef, Set.indicator_of_mem (hballρ_B16 hz)]
    rw [hgint] at hρavg
    -- `(ofReal lam)^q < ⨍⁻_{ball c ρ} wᵠ`.
    have hvolρ_pos : 0 < volume (Metric.ball c ρ) := Metric.measure_ball_pos _ _ hρpos
    have havg : Λ < ⨍⁻ z in Metric.ball c ρ, w z ^ q ∂volume := by
      rw [setLAverage_eq]; exact hρavg
    -- Take `^{1/q}`: `ofReal lam < (⨍⁻ wᵠ)^{1/q}`.
    have h1q : (0:ℝ) < 1 / q := by positivity
    have hroot : ENNReal.ofReal lam < (⨍⁻ z in Metric.ball c ρ, w z ^ q ∂volume) ^ (1 / q) := by
      rw [hΛdef] at havg
      have h := ENNReal.rpow_lt_rpow havg h1q
      have hid : (ENNReal.ofReal lam ^ q) ^ (1 / q) = ENNReal.ofReal lam := by
        rw [one_div, ENNReal.rpow_rpow_inv hq0.ne']
      rwa [hid] at h
    -- Reverse-Hölder dichotomy at `ball c ρ`.
    have hRHc := hRHÃ c ρ hρpos
    have hsum : ENNReal.ofReal lam <
        ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball c (4 * ρ), w z ∂volume) +
          ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball c (4 * ρ), b z ^ q ∂volume) ^ (1 / q) :=
      lt_of_lt_of_le hroot hRHc
    -- One of the two terms is `≥ ofReal lam / 2`.
    have hhalf : ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball c (4 * ρ), w z ∂volume)
          ≥ ENNReal.ofReal lam / 2 ∨
        ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball c (4 * ρ), b z ^ q ∂volume) ^ (1 / q)
          ≥ ENNReal.ofReal lam / 2 := by
      by_contra hcon
      rw [not_or] at hcon
      obtain ⟨h1, h2⟩ := hcon
      rw [not_le] at h1 h2
      have : ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball c (4 * ρ), w z ∂volume) +
          ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball c (4 * ρ), b z ^ q ∂volume) ^ (1 / q)
          < ENNReal.ofReal lam / 2 + ENNReal.ofReal lam / 2 := ENNReal.add_lt_add h1 h2
      rw [ENNReal.add_halves] at this
      exact absurd (lt_trans hsum this) (lt_irrefl _)
    -- Volume facts for `4ρ`-ball (positive, finite).
    have hvol4_pos : 0 < volume (Metric.ball c (4 * ρ)) :=
      Metric.measure_ball_pos _ _ (by positivity)
    have hvol4_ne : volume (Metric.ball c (4 * ρ)) ≠ 0 := hvol4_pos.ne'
    have hvol4_top : volume (Metric.ball c (4 * ρ)) ≠ ⊤ := measure_ball_lt_top.ne
    have hÃne : ENNReal.ofReal Ã ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hÃpos
    have hÃtop : ENNReal.ofReal Ã ≠ ⊤ := ENNReal.ofReal_ne_top
    -- The clean key: `lw * ofReal Ã = ofReal lam / 2` (and similarly for the `q`-power).
    have hlw_mul : lw * ENNReal.ofReal Ã = ENNReal.ofReal lam / 2 := by
      rw [hlwdef, ← ENNReal.ofReal_mul (by positivity)]
      have hreal : lam / (2 * Ã) * Ã = lam / 2 := by
        field_simp
      rw [hreal, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
      congr 1; norm_num
    rcases hhalf with hw | hb
    · -- `w`-good: `lw·vol(4B) ≤ ∫_{4B} w`.
      left
      -- `lw ≤ ⨍ w` by cancelling `ofReal Ã` from `lw·ofReal Ã = ofReal lam/2 ≤ ofReal Ã·⨍ w`.
      have hge : lw ≤ ⨍⁻ z in Metric.ball c (4 * ρ), w z ∂volume := by
        have hchain : lw * ENNReal.ofReal Ã
            ≤ (⨍⁻ z in Metric.ball c (4 * ρ), w z ∂volume) * ENNReal.ofReal Ã := by
          rw [hlw_mul, mul_comm]; exact hw
        exact (ENNReal.mul_le_mul_iff_left hÃne hÃtop).mp hchain
      rw [setLAverage_eq] at hge
      rwa [ENNReal.le_div_iff_mul_le (Or.inl hvol4_ne) (Or.inl hvol4_top)] at hge
    · -- `b`-good: `lb·vol(4B) ≤ ∫_{4B} bᵠ`.
      right
      -- `lb = lw^q`, and from `lw ≤ (⨍ bᵠ)^{1/q}` raise to `q`.
      have hlb_eq : lb = lw ^ q := by
        rw [hlbdef, hlwdef, ← ENNReal.ofReal_rpow_of_pos (by positivity)]
      have hgew : lw ≤ (⨍⁻ z in Metric.ball c (4 * ρ), b z ^ q ∂volume) ^ (1 / q) := by
        have hchain : lw * ENNReal.ofReal Ã
            ≤ (⨍⁻ z in Metric.ball c (4 * ρ), b z ^ q ∂volume) ^ (1 / q) * ENNReal.ofReal Ã := by
          rw [hlw_mul, mul_comm]; exact hb
        exact (ENNReal.mul_le_mul_iff_left hÃne hÃtop).mp hchain
      have hgeq : lb ≤ ⨍⁻ z in Metric.ball c (4 * ρ), b z ^ q ∂volume := by
        rw [hlb_eq]
        have hpow := ENNReal.rpow_le_rpow hgew hq0.le
        rwa [one_div, ENNReal.rpow_inv_rpow hq0.ne'] at hpow
      rw [setLAverage_eq] at hgeq
      rwa [ENNReal.le_div_iff_mul_le (Or.inl hvol4_ne) (Or.inl hvol4_top)] at hgeq
  -- =========================================================================
  -- ASSEMBLY.  Choose, for each `c ∈ S ∩ Good`, the enlarged radius `R c = 4ρ_c`;
  -- partition into `w`-good and `b`-good centers; feed each subfamily to the engine.
  -- =========================================================================
  -- Total enlarged-radius function (`0` off `S ∩ Good`).
  set Rfun : ℂ → ℝ := fun c => if h : c ∈ S ∩ Good then 4 * (hdich c h).choose else 0
    with hRfundef
  -- Spec of the choice on `S ∩ Good`.
  have hRspec : ∀ c (h : c ∈ S ∩ Good), 0 < Rfun c ∧
      Metric.ball c (Rfun c) ⊆ Metric.ball x₀ s ∧
      (lw * volume (Metric.ball c (Rfun c)) ≤ ∫⁻ z in Metric.ball c (Rfun c), w z ∨
       lb * volume (Metric.ball c (Rfun c)) ≤ ∫⁻ z in Metric.ball c (Rfun c), b z ^ q) ∧
      Rfun c ≤ (s - t) / 2 := by
    intro c h
    have hch := (hdich c h).choose_spec
    obtain ⟨hρpos, hsub, hdisj, hcap⟩ := hch
    have hRfval : Rfun c = 4 * (hdich c h).choose := by rw [hRfundef]; simp [h]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hRfval]; positivity
    · rw [hRfval]; exact hsub
    · rw [hRfval]; exact hdisj
    · rw [hRfval]; exact hcap
  -- The `w`-good and `b`-good center subsets.
  set Sw : Set ℂ := {c | ∃ h : c ∈ S ∩ Good,
      lw * volume (Metric.ball c (Rfun c)) ≤ ∫⁻ z in Metric.ball c (Rfun c), w z} with hSwdef
  set Sb : Set ℂ := {c | ∃ h : c ∈ S ∩ Good,
      lb * volume (Metric.ball c (Rfun c)) ≤ ∫⁻ z in Metric.ball c (Rfun c), b z ^ q} with hSbdef
  -- Every `c ∈ S ∩ Good` lies in `Sw ∪ Sb`, and inside its own ball.
  have hcover : S ∩ Good ⊆ (⋃ c ∈ Sw, Metric.ball c (Rfun c))
      ∪ (⋃ c ∈ Sb, Metric.ball c (Rfun c)) := by
    intro c hc
    obtain ⟨hRpos, _, hdisj, _⟩ := hRspec c hc
    have hcmem : c ∈ Metric.ball c (Rfun c) := Metric.mem_ball_self hRpos
    rcases hdisj with hw | hb
    · exact Or.inl (Set.mem_biUnion (⟨hc, hw⟩) hcmem)
    · exact Or.inr (Set.mem_biUnion (⟨hc, hb⟩) hcmem)
  -- Uniform radius bound and averaging hypotheses for the two engine calls.
  have hRbd_w : ∀ c ∈ Sw, Rfun c ≤ (s - t) / 2 := by
    rintro c ⟨h, _⟩; exact (hRspec c h).2.2.2
  have hRbd_b : ∀ c ∈ Sb, Rfun c ≤ (s - t) / 2 := by
    rintro c ⟨h, _⟩; exact (hRspec c h).2.2.2
  -- `u`-weights localized to `ball x₀ s`.
  have h2u_w : ∀ c ∈ Sw, lw * volume (Metric.ball c (Rfun c))
      ≤ ∫⁻ z in Metric.ball c (Rfun c), (Metric.ball x₀ s).indicator w z := by
    rintro c ⟨h, hle⟩
    have hsub : Metric.ball c (Rfun c) ⊆ Metric.ball x₀ s := (hRspec c h).2.1
    have heq : ∫⁻ z in Metric.ball c (Rfun c), (Metric.ball x₀ s).indicator w z
        = ∫⁻ z in Metric.ball c (Rfun c), w z := by
      refine setLIntegral_congr_fun measurableSet_ball (fun z hz => ?_)
      rw [Set.indicator_of_mem (hsub hz)]
    rw [heq]; exact hle
  have h2u_b : ∀ c ∈ Sb, lb * volume (Metric.ball c (Rfun c))
      ≤ ∫⁻ z in Metric.ball c (Rfun c), (Metric.ball x₀ s).indicator (fun z => b z ^ q) z := by
    rintro c ⟨h, hle⟩
    have hsub : Metric.ball c (Rfun c) ⊆ Metric.ball x₀ s := (hRspec c h).2.1
    have heq : ∫⁻ z in Metric.ball c (Rfun c), (Metric.ball x₀ s).indicator (fun z => b z ^ q) z
        = ∫⁻ z in Metric.ball c (Rfun c), b z ^ q := by
      refine setLIntegral_congr_fun measurableSet_ball (fun z hz => ?_)
      rw [Set.indicator_of_mem (hsub hz)]
    rw [heq]; exact hle
  -- Engine bounds.
  have hEw := gehring_engine_bound lw ((Metric.ball x₀ s).indicator w) Sw Rfun ((s - t) / 2)
    hRbd_w h2u_w
  have hEb := gehring_engine_bound lb ((Metric.ball x₀ s).indicator (fun z => b z ^ q)) Sb Rfun
    ((s - t) / 2) hRbd_b h2u_b
  -- The localized global integrals are the `ball x₀ s` integrals.
  have hIw : ∫⁻ z, (Metric.ball x₀ s).indicator w z = ∫⁻ z in Metric.ball x₀ s, w z := by
    rw [lintegral_indicator measurableSet_ball]
  have hIb : ∫⁻ z, (Metric.ball x₀ s).indicator (fun z => b z ^ q) z
      = ∫⁻ z in Metric.ball x₀ s, b z ^ q := by
    rw [lintegral_indicator measurableSet_ball]
  rw [hIw] at hEw
  rw [hIb] at hEb
  -- Positivity/finiteness of `lw, lb`.
  have hlw_pos : 0 < lw := by rw [hlwdef, ENNReal.ofReal_pos]; positivity
  have hlb_pos : 0 < lb := by rw [hlbdef, ENNReal.ofReal_pos]; positivity
  have hlw_ne : lw ≠ 0 := hlw_pos.ne'
  have hlb_ne : lb ≠ 0 := hlb_pos.ne'
  have hlw_top : lw ≠ ⊤ := by rw [hlwdef]; exact ENNReal.ofReal_ne_top
  have hlb_top : lb ≠ ⊤ := by rw [hlbdef]; exact ENNReal.ofReal_ne_top
  -- The coefficients and the key cancellation identities `coefw · lw = 16`, `coefb · lb = 16`.
  have h2Ãpos : 0 < 2 * Ã := by positivity
  set coefw : ℝ≥0∞ := ENNReal.ofReal ((2 * (A + 1) / lam) * 16) with hcoefwdef
  set coefb : ℝ≥0∞ := ENNReal.ofReal ((2 * (A + 1) / lam) ^ q * 16) with hcoefbdef
  have hcw_mul : coefw * lw = (16 : ℝ≥0∞) := by
    rw [hcoefwdef, hlwdef, ← ENNReal.ofReal_mul (by positivity), ← hÃdef]
    rw [show (2 * Ã / lam) * 16 * (lam / (2 * Ã)) = 16 by field_simp]
    rw [ENNReal.ofReal_ofNat]
  have hcb_mul : coefb * lb = (16 : ℝ≥0∞) := by
    rw [hcoefbdef, hlbdef, ← ENNReal.ofReal_mul (by positivity), ← hÃdef]
    rw [show (2 * Ã / lam) ^ q * 16 * (lam / (2 * Ã)) ^ q = 16 by
      rw [mul_right_comm, ← Real.mul_rpow (by positivity) (by positivity),
        show (2 * Ã / lam) * (lam / (2 * Ã)) = 1 by field_simp, Real.one_rpow, one_mul]]
    rw [ENNReal.ofReal_ofNat]
  -- Convert the engine bounds to volume bounds: `vol(⋃) ≤ coef·∫`.
  have hVw : volume (⋃ c ∈ Sw, Metric.ball c (Rfun c))
      ≤ coefw * (∫⁻ z in Metric.ball x₀ s, w z) := by
    have hcw_pos : 0 < coefw := by rw [hcoefwdef, ENNReal.ofReal_pos]; positivity
    have hkey : lw * volume (⋃ c ∈ Sw, Metric.ball c (Rfun c))
        ≤ lw * (coefw * (∫⁻ z in Metric.ball x₀ s, w z)) := by
      calc lw * volume (⋃ c ∈ Sw, Metric.ball c (Rfun c))
          ≤ (16 : ℝ≥0∞) * ∫⁻ z in Metric.ball x₀ s, w z := hEw
        _ = (coefw * lw) * ∫⁻ z in Metric.ball x₀ s, w z := by rw [hcw_mul]
        _ = lw * (coefw * (∫⁻ z in Metric.ball x₀ s, w z)) := by ring
    exact (ENNReal.mul_le_mul_iff_right hlw_ne hlw_top).mp hkey
  have hVb : volume (⋃ c ∈ Sb, Metric.ball c (Rfun c))
      ≤ coefb * (∫⁻ z in Metric.ball x₀ s, b z ^ q) := by
    have hkey : lb * volume (⋃ c ∈ Sb, Metric.ball c (Rfun c))
        ≤ lb * (coefb * (∫⁻ z in Metric.ball x₀ s, b z ^ q)) := by
      calc lb * volume (⋃ c ∈ Sb, Metric.ball c (Rfun c))
          ≤ (16 : ℝ≥0∞) * ∫⁻ z in Metric.ball x₀ s, b z ^ q := hEb
        _ = (coefb * lb) * ∫⁻ z in Metric.ball x₀ s, b z ^ q := by rw [hcb_mul]
        _ = lb * (coefb * (∫⁻ z in Metric.ball x₀ s, b z ^ q)) := by ring
    exact (ENNReal.mul_le_mul_iff_right hlb_ne hlb_top).mp hkey
  -- Final: `vol S = vol(S ∩ Good) ≤ vol(⋃Sw) + vol(⋃Sb)`.
  have hSeq : volume S = volume (S ∩ Good) := by
    refine le_antisymm ?_ (measure_mono Set.inter_subset_left)
    calc volume S ≤ volume ((S ∩ Good) ∪ Goodᶜ) := by
          refine measure_mono (fun z hz => ?_)
          by_cases hg : z ∈ Good
          · exact Or.inl ⟨hz, hg⟩
          · exact Or.inr hg
      _ ≤ volume (S ∩ Good) + volume (Goodᶜ) := measure_union_le _ _
      _ = volume (S ∩ Good) := by rw [hGoodae, add_zero]
  rw [hSdef] at hSeq ⊢
  rw [← hSdef, hSeq]
  calc volume (S ∩ Good)
      ≤ volume ((⋃ c ∈ Sw, Metric.ball c (Rfun c)) ∪ (⋃ c ∈ Sb, Metric.ball c (Rfun c))) :=
        measure_mono hcover
    _ ≤ volume (⋃ c ∈ Sw, Metric.ball c (Rfun c)) + volume (⋃ c ∈ Sb, Metric.ball c (Rfun c)) :=
        measure_union_le _ _
    _ ≤ coefw * (∫⁻ z in Metric.ball x₀ s, w z)
          + coefb * (∫⁻ z in Metric.ball x₀ s, b z ^ q) := add_le_add hVw hVb

/-- **Global dyadic Calderón–Zygmund cover** (helper for `gehring_goodLambda_integral_core`).
Run the two-sided dyadic stopping `exists_dyadic_CZ_stopping` simultaneously on the (countably
many) generation-`M` dyadic squares, applied to the localized weight `f = (ball x₀ s).indicator wᵠ`
at height `Λ = (ofReal lam)^q`.  When `2s ≤ 2^M` each generation-`M` square has area
`(2^M)² ≥ 4s² ≥ vol(ball x₀ s)` (since `4 > π`), so the ambient average of `f` over every such
square is `≤ ⨍_{ball s} wᵠ ≤ Λ`: the ambient square never stops.  The stopping cubes of the various
ambient squares assemble into a single countable, pairwise-disjoint family that a.e.-covers the
super-level set `{lam < w} ∩ ball x₀ t` (for any `t ≤ s`), with each cube nested in `ball x₀ s` and
satisfying the two-sided bound `Λ < ⨍_{Qᵢ} f ≤ 4Λ`, where the average is of the LOCALIZED `f`, so
`∫_{Qᵢ} f = ∫_{Qᵢ ∩ ball s} wᵠ ≤ ∫_{Qᵢ} wᵠ` and the lower bound forces `Qᵢ ∩ ball s ≠ ∅`. -/
theorem gehring_dyadic_global_cover {q : ℝ} (hq0 : 0 < q) {w : ℂ → ℝ≥0∞}
    (hwmeas : AEMeasurable w volume) (x₀ : ℂ) (s : ℝ) (hs : 0 < s)
    (M : ℤ) (hM : 2 * s ≤ (2 : ℝ) ^ M)
    (lam : ℝ) (hlam : 0 < lam)
    (hlam0cond : (⨍⁻ z in Metric.ball x₀ s, w z ^ q ∂volume) ≤ (ENNReal.ofReal lam) ^ q) :
    ∃ (B : Set (ℤ × (ℤ × ℤ))),
      B.Countable ∧
      (B.Pairwise (fun i j => Disjoint (dyadicSquare i.1 i.2) (dyadicSquare j.1 j.2))) ∧
      -- every cube has scale `≤ M` (so `2^{i.1} ≤ 2^M`) and meets `ball x₀ s`:
      (∀ i ∈ B, i.1 ≤ M) ∧
      (∀ i ∈ B, (dyadicSquare i.1 i.2 ∩ Metric.ball x₀ s).Nonempty) ∧
      -- a.e.-cover of `{lam < w} ∩ ball x₀ s`:
      (volume ((Metric.ball x₀ s ∩ {z : ℂ | lam < (w z).toReal}) \
        ⋃ i ∈ B, dyadicSquare i.1 i.2) = 0) ∧
      -- two-sided dyadic average bounds for the localized weight:
      (∀ i ∈ B,
        (∫⁻ z in dyadicSquare i.1 i.2 ∩ Metric.ball x₀ s, w z ^ q)
          ≤ ENNReal.ofReal (4 * lam ^ q) * volume (dyadicSquare i.1 i.2)) ∧
      (∀ i ∈ B, (ENNReal.ofReal lam) ^ q <
        (∫⁻ z in dyadicSquare i.1 i.2 ∩ Metric.ball x₀ s, w z ^ q) /
          volume (dyadicSquare i.1 i.2)) := by
  classical
  -- The localized weight `f = (ball x₀ s).indicator wᵠ`.
  set Bs : Set ℂ := Metric.ball x₀ s with hBsdef
  set f : ℂ → ℝ≥0∞ := Bs.indicator (fun z => w z ^ q) with hfdef
  have hfmeas : AEMeasurable f volume := (hwmeas.pow_const q).indicator measurableSet_ball
  -- The height `Λ = ofReal(lam^q) = (ofReal lam)^q`.
  set Λ : ℝ≥0∞ := ENNReal.ofReal (lam ^ q) with hΛdef
  have hΛeq : (ENNReal.ofReal lam) ^ q = Λ := by
    rw [hΛdef, ENNReal.ofReal_rpow_of_nonneg hlam.le hq0.le]
  have hΛfin : Λ ≠ ⊤ := by rw [hΛdef]; exact ENNReal.ofReal_ne_top
  have hΛpos : 0 < Λ := by rw [hΛdef, ENNReal.ofReal_pos]; positivity
  -- Volume facts.
  have h2Mpos : (0:ℝ) < (2:ℝ) ^ M := zpow_pos (by norm_num) M
  have hvolBs : volume Bs = ENNReal.ofReal (Real.pi * s ^ 2) := by
    rw [hBsdef, Complex.volume_ball]
    have hpi : (↑NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
      rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
    rw [hpi, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hs.le, mul_comm]
  -- `vol(ball s) < (2^M)^2 = vol(dyadicSquare M j)` (since `4 > π` and `2s ≤ 2^M`).
  have hvolBs_lt : volume Bs < ENNReal.ofReal (((2:ℝ) ^ M) ^ 2) := by
    rw [hvolBs]
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have h4s : 4 * s ^ 2 ≤ ((2:ℝ) ^ M) ^ 2 := by nlinarith [hM, hs.le, h2Mpos]
    nlinarith [Real.pi_lt_d2, hs, h4s]
  -- AMBIENT NON-STOP: for every gen-`M` index `j`, the localized average is `< Λ`.
  have hambient : ∀ j : ℤ × ℤ, (⨍⁻ z in dyadicSquare M j, f z ∂volume) < Λ := by
    intro j
    set Q : Set ℂ := dyadicSquare M j with hQdef
    have hvolQ : volume Q = ENNReal.ofReal (((2:ℝ) ^ M) ^ 2) := by
      rw [hQdef, volume_dyadicSquare]
    have hvolQ0 : volume Q ≠ 0 := by
      rw [hvolQ, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    have hvolQtop : volume Q ≠ ⊤ := by rw [hvolQ]; exact ENNReal.ofReal_ne_top
    -- `∫_Q f = ∫_{Q ∩ ball s} wᵠ ≤ ∫_{ball s} wᵠ`.
    have hintf : ∫⁻ z in Q, f z = ∫⁻ z in Q ∩ Bs, w z ^ q := by
      rw [hfdef, setLIntegral_indicator (measurableSet_ball), Set.inter_comm Bs Q]
    have hintf_le : ∫⁻ z in Q, f z ≤ ∫⁻ z in Bs, w z ^ q := by
      rw [hintf]; exact lintegral_mono_set Set.inter_subset_right
    -- The average over `Bs`.
    have hAvBs : ⨍⁻ z in Bs, w z ^ q ∂volume ≤ Λ := by rw [hΛeq] at hlam0cond; exact hlam0cond
    -- `∫_{Bs} wᵠ ≤ Λ · vol(Bs) < ⊤`.
    have hIfin : ∫⁻ z in Bs, w z ^ q ≠ ⊤ := by
      rw [setLAverage_eq] at hAvBs
      have hvolBstop : volume Bs ≠ ⊤ := by rw [hvolBs]; exact ENNReal.ofReal_ne_top
      have hvolBs0 : volume Bs ≠ 0 := by
        rw [hvolBs, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
      have := (ENNReal.div_le_iff_le_mul (Or.inl hvolBs0) (Or.inl hvolBstop)).mp hAvBs
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hΛfin hvolBstop) this
    -- `⨍_Q f = (∫_Q f)/vol Q ≤ (∫_{Bs} wᵠ)/vol Q < (∫_{Bs} wᵠ)/vol Bs = ⨍_{Bs} wᵠ ≤ Λ`,
    -- using `vol Q > vol Bs`.  Handle `∫_{Bs} wᵠ = 0` separately.
    rw [setLAverage_eq]
    rcases eq_or_ne (∫⁻ z in Bs, w z ^ q) 0 with hI0 | hIpos
    · -- numerator `0`: average `= 0 < Λ`.
      have : ∫⁻ z in Q, f z = 0 := le_antisymm (le_trans hintf_le (le_of_eq hI0)) (zero_le)
      rw [this, ENNReal.zero_div]; exact hΛpos
    · -- positive numerator: strict via `vol Q > vol Bs`.
      have hvolBs0 : volume Bs ≠ 0 := by
        rw [hvolBs, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
      have hvolBstop : volume Bs ≠ ⊤ := by rw [hvolBs]; exact ENNReal.ofReal_ne_top
      have hvolQgtBs : volume Bs < volume Q := by rw [hvolQ]; exact hvolBs_lt
      calc (∫⁻ z in Q, f z) / volume Q
          ≤ (∫⁻ z in Bs, w z ^ q) / volume Q := ENNReal.div_le_div_right hintf_le _
        _ < (∫⁻ z in Bs, w z ^ q) / volume Bs :=
            ENNReal.div_lt_div_left hIpos hIfin hvolQgtBs
        _ = ⨍⁻ z in Bs, w z ^ q ∂volume := by rw [setLAverage_eq]
        _ ≤ Λ := hAvBs
  -- Per-ambient stopping data, chosen via `Exists.choose`.
  have hstop : ∀ j : ℤ × ℤ, ∃ (ι : Type) (B : Set ι) (n : ι → ℤ) (k : ι → ℤ × ℤ),
      B.Countable ∧
      (∀ i ∈ B, dyadicSquare (n i) (k i) ⊆ dyadicSquare M j) ∧
      (Pairwise (fun i₁ i₂ => Disjoint (dyadicSquare (n i₁) (k i₁)) (dyadicSquare (n i₂) (k i₂)))) ∧
      (volume ({z ∈ dyadicSquare M j | Λ < f z} \
        ⋃ i ∈ B, dyadicSquare (n i) (k i)) = 0) ∧
      (∀ i ∈ B, Λ < ⨍⁻ z in dyadicSquare (n i) (k i), f z ∂volume ∧
        (⨍⁻ z in dyadicSquare (n i) (k i), f z ∂volume) ≤ 4 * Λ) :=
    fun j => exists_dyadic_CZ_stopping hfmeas M j (hambient j) hΛfin
  choose ιj Bj nj kj hBjct hBjsub hBjdisj hBjcov hBjavg using hstop
  -- The cube-identifier map for ambient `j`.
  set gj : (j : ℤ × ℤ) → ιj j → ℤ × (ℤ × ℤ) := fun j i => (nj j i, kj j i) with hgjdef
  -- The combined family of cube identifiers.
  set B : Set (ℤ × (ℤ × ℤ)) := ⋃ j : ℤ × ℤ, gj j '' (Bj j) with hBdef
  -- Membership unfolding: `p ∈ B ↔ ∃ j, ∃ i ∈ Bj j, gj j i = p`.
  have hBmem : ∀ p : ℤ × (ℤ × ℤ), p ∈ B ↔ ∃ j, ∃ i ∈ Bj j, gj j i = p := by
    intro p
    simp only [hBdef, Set.mem_iUnion, Set.mem_image]
  -- For `i' ∈ Bj j`, the cube identified by `gj j i'` equals `dyadicSquare (nj j i') (kj j i')`.
  have hcubeEq : ∀ (j : ℤ × ℤ) (i : ιj j),
      dyadicSquare (gj j i).1 (gj j i).2 = dyadicSquare (nj j i) (kj j i) := fun j i => rfl
  -- The localized-integral identity `∫_{cube} f = ∫_{cube ∩ ball s} wᵠ` for any dyadic cube.
  have hfint : ∀ (m : ℤ) (idx : ℤ × ℤ),
      ∫⁻ z in dyadicSquare m idx, f z
        = ∫⁻ z in dyadicSquare m idx ∩ Bs, w z ^ q := by
    intro m idx
    rw [hfdef, setLIntegral_indicator (measurableSet_ball), Set.inter_comm Bs _]
  -- Volume positivity/finiteness of any dyadic cube.
  have hvolcube : ∀ (m : ℤ) (idx : ℤ × ℤ),
      volume (dyadicSquare m idx) ≠ 0 ∧ volume (dyadicSquare m idx) ≠ ⊤ := by
    intro m idx
    rw [volume_dyadicSquare]
    refine ⟨?_, ENNReal.ofReal_ne_top⟩
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  refine ⟨B, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Countability.
    rw [hBdef]
    exact Set.countable_iUnion (fun j => (hBjct j).image _)
  · -- Pairwise disjointness on `B`.
    intro p hp p' hp' hpp'
    rw [hBmem] at hp hp'
    obtain ⟨j, i, hi, hgi⟩ := hp
    obtain ⟨j', i', hi', hgi'⟩ := hp'
    -- The cubes.
    have hcp : dyadicSquare p.1 p.2 = dyadicSquare (nj j i) (kj j i) := by rw [← hgi]
    have hcp' : dyadicSquare p'.1 p'.2 = dyadicSquare (nj j' i') (kj j' i') := by rw [← hgi']
    rw [hcp, hcp']
    by_cases hjj : j = j'
    · -- Same ambient: use per-ambient pairwise disjointness; `i ≠ i'`.
      subst hjj
      have hii : i ≠ i' := by
        rintro rfl
        exact hpp' (by rw [← hgi, ← hgi'])
      exact hBjdisj j hii
    · -- Different ambients: cubes nested in disjoint gen-`M` squares.
      have hsub1 : dyadicSquare (nj j i) (kj j i) ⊆ dyadicSquare M j := hBjsub j i hi
      have hsub2 : dyadicSquare (nj j' i') (kj j' i') ⊆ dyadicSquare M j' := hBjsub j' i' hi'
      have hQdisj : Disjoint (dyadicSquare M j) (dyadicSquare M j') :=
        dyadicSquare_pairwise_disjoint M hjj
      exact hQdisj.mono hsub1 hsub2
  · -- Scale bound `i.1 ≤ M`.
    intro p hp
    rw [hBmem] at hp
    obtain ⟨j, i, hi, hgi⟩ := hp
    have hsub : dyadicSquare (nj j i) (kj j i) ⊆ dyadicSquare M j := hBjsub j i hi
    have hp1 : p.1 = nj j i := by rw [← hgi, hgjdef]
    rw [hp1]
    -- volume monotonicity ⟹ `(2^{nj})² ≤ (2^M)²` ⟹ `nj ≤ M`.
    have hvmono : volume (dyadicSquare (nj j i) (kj j i)) ≤ volume (dyadicSquare M j) :=
      measure_mono hsub
    rw [volume_dyadicSquare, volume_dyadicSquare,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hvmono
    have h2n : (0:ℝ) < (2:ℝ) ^ (nj j i) := zpow_pos (by norm_num) _
    have h2M : (0:ℝ) < (2:ℝ) ^ M := zpow_pos (by norm_num) _
    have hle : (2:ℝ) ^ (nj j i) ≤ (2:ℝ) ^ M := by nlinarith [hvmono, h2n, h2M]
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp hle
  · -- Nonempty intersection with `ball s`.
    intro p hp
    rw [hBmem] at hp
    obtain ⟨j, i, hi, hgi⟩ := hp
    have hp12 : dyadicSquare p.1 p.2 = dyadicSquare (nj j i) (kj j i) := by rw [← hgi]
    rw [hp12]
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    -- `f = 0` on the cube ⟹ `⨍ f = 0`, contradicting `Λ < ⨍ f`.
    have havg := (hBjavg j i hi).1
    have hf0 : ∫⁻ z in dyadicSquare (nj j i) (kj j i), f z = 0 := by
      rw [hfint, hempty]; simp
    rw [setLAverage_eq, hf0, ENNReal.zero_div] at havg
    exact absurd havg (not_lt.mpr (zero_le))
  · -- a.e.-cover of `{lam < w.toReal} ∩ ball s`.
    have hbad_sub : (Metric.ball x₀ s ∩ {z : ℂ | lam < (w z).toReal}) \
        ⋃ i ∈ B, dyadicSquare i.1 i.2
        ⊆ ⋃ j : ℤ × ℤ, ({z ∈ dyadicSquare M j | Λ < f z} \
            ⋃ i ∈ Bj j, dyadicSquare (nj j i) (kj j i)) := by
      rintro z ⟨⟨hzs, hzlam⟩, hznotcov⟩
      simp only [Set.mem_ofPred_eq] at hzlam
      -- `z` lies in its gen-`M` ambient square.
      set j₀ : ℤ × ℤ := dyadicIndexAt M z with hj₀
      have hzj₀ : z ∈ dyadicSquare M j₀ := mem_dyadicSquare_dyadicIndexAt M z
      -- `f z > Λ`.
      have hwfin : w z ≠ ⊤ := by
        intro htop; rw [htop, ENNReal.toReal_top] at hzlam; linarith
      have hfz : f z = w z ^ q := by
        rw [hfdef, Set.indicator_of_mem (by rw [hBsdef]; exact hzs)]
      have hΛlt : Λ < f z := by
        rw [hfz, hΛdef, ← ENNReal.ofReal_rpow_of_nonneg hlam.le hq0.le]
        apply ENNReal.rpow_lt_rpow _ hq0
        rw [← ENNReal.ofReal_toReal hwfin]
        exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hlam.le |>.mpr hzlam
      refine Set.mem_iUnion.mpr ⟨j₀, ⟨hzj₀, hΛlt⟩, ?_⟩
      -- `z` not covered by `Bj j₀` cubes (else it would be in `⋃ B`).
      intro hzcov
      apply hznotcov
      rw [Set.mem_iUnion₂] at hzcov ⊢
      obtain ⟨i, hi, hzi⟩ := hzcov
      refine ⟨gj j₀ i, (hBmem _).mpr ⟨j₀, i, hi, rfl⟩, ?_⟩
      rw [hcubeEq j₀ i]; exact hzi
    refine measure_mono_null hbad_sub ?_
    rw [measure_iUnion_null_iff]
    exact fun j => hBjcov j
  · -- Upper average bound: `∫_{cube ∩ ball s} wᵠ ≤ ofReal(4 lam^q) · vol(cube)`.
    intro p hp
    rw [hBmem] at hp
    obtain ⟨j, i, hi, hgi⟩ := hp
    have hp12 : dyadicSquare p.1 p.2 = dyadicSquare (nj j i) (kj j i) := by rw [← hgi]
    rw [hp12]
    have havg := (hBjavg j i hi).2
    rw [setLAverage_eq, hfint] at havg
    obtain ⟨hv0, hvtop⟩ := hvolcube (nj j i) (kj j i)
    rw [ENNReal.div_le_iff_le_mul (Or.inl hv0) (Or.inl hvtop)] at havg
    refine le_trans havg ?_
    rw [show (4 : ℝ≥0∞) * Λ = ENNReal.ofReal (4 * lam ^ q) by
      rw [hΛdef, show (4:ℝ≥0∞) = ENNReal.ofReal 4 by rw [ENNReal.ofReal_ofNat],
        ← ENNReal.ofReal_mul (by norm_num)]]
  · -- Lower average bound: `(ofReal lam)^q < ∫_{cube ∩ ball s} wᵠ / vol(cube)`.
    intro p hp
    rw [hBmem] at hp
    obtain ⟨j, i, hi, hgi⟩ := hp
    have hp12 : dyadicSquare p.1 p.2 = dyadicSquare (nj j i) (kj j i) := by rw [← hgi]
    rw [hp12]
    have havg := (hBjavg j i hi).1
    rw [setLAverage_eq, hfint] at havg
    rw [hΛeq]; exact havg

/-- **Indexed Carleson covering bound** (helper for `gehring_goodLambda_integral_core`).  The
cube-identifier-indexed analogue of `gehring_engine_bound`: a countable family of balls
`ball (c i) (r i)` (`i ∈ 𝓑`), each with the per-ball averaging property
`l·vol ≤ ∫ u`, has `l·vol(⋃) ≤ 16·∫⁻ u` (planar doubling `A_dbl = 4`, `A_dbl² = 16`). -/
theorem gehring_engine_idx {ι : Type} (𝓑 : Set ι) (_hct : 𝓑.Countable)
    (c : ι → ℂ) (r : ι → ℝ) (l : ℝ≥0∞) (u : ℂ → ℝ≥0∞) (Rbd : ℝ)
    (_hRbd : ∀ i ∈ 𝓑, r i ≤ Rbd)
    (h2u : ∀ i ∈ 𝓑, l * volume (Metric.ball (c i) (r i)) ≤ ∫⁻ z in Metric.ball (c i) (r i), u z) :
    l * volume (⋃ i ∈ 𝓑, Metric.ball (c i) (r i)) ≤ (16 : ℝ≥0∞) * ∫⁻ z, u z := by
  have hdbl : (volume : Measure ℂ).IsDoubling (2 ^ Module.finrank ℝ ℂ) :=
    InnerProductSpace.IsDoubling
  have hengine := measure_biUnion_le_lintegral (μ := (volume : Measure ℂ))
    (A := 2 ^ Module.finrank ℝ ℂ) (c := c) (r := r) 𝓑 l u h2u
  have hA2 : ((2 ^ Module.finrank ℝ ℂ : ℝ≥0) : ℝ≥0∞) ^ 2 = (16 : ℝ≥0∞) := by
    rw [Complex.finrank_real_complex]; norm_num
  simpa only [hA2] using hengine

/-- **Honest exponent-1 good-λ in INTEGRAL (`w^q`-mass) form, on the HIGH range `λ ≥ λ₀`** — the
analytic core of STEP B of `gehring_selfImprovement`.
For concentric radii `4R₀ ≤ t < s ≤ 16R₀` and a height `lam > 0` on the HIGH range characterized by
`⨍⁻_{ball s} wᵠ ≤ (ofReal lam)^q` (i.e. `lam ≥ λ₀ := (⨍_{ball s} wᵠ)^{1/q}`), the FULL
(a-priori-integrable) `w^q`-mass over the super-level set `{w > lam} ∩ ball t` is controlled by the
`lam^{q-1}`-weighted FULL `w`-mass (exponent ONE) over the SUPER-LEVEL set `{w > β·lam} ∩ ball s`,
plus a super-level `bᵠ`-forcing:
`∫_{ball t ∩ {lam < w}} wᵠ  ≤  Cw·lam^{q-1}·∫_{ball s ∩ {β·lam < w}} w`
`  + Cb·∫_{ball s ∩ {β·lam < b}} bᵠ`
with (here) `β = 1/2`, `Cw = 4(2·π^{1/q}·A)ᵠ`, `Cb = 256(2·π^{1/q}·(A+1))ᵠ`.

The THRESHOLD-RESTRICTED hypothesis `hlam0cond` is what makes the statement hold: it is the
Giaquinta–Modica threshold split, consumed downstream in `gehring_assembly`/`gehring_holeFill`
ONLY on the high range `λ ≥ λ₀`, while `0 < λ < λ₀` is handled there by the trivial
`∫_{ball t ∩ {λ<w}} wᵠ ≤ ∫_{16B₀} wᵠ` bound folded into the `C₁·Wmaster/(s-t)²` collar.
The proof is the classical Calderón–Zygmund stopping-time / reverse-Hölder dichotomy core:
two-sided stopping of `g := 1_{ball s}·wᵠ` at height `lamᵠ`
(`exists_dyadic_CZ_stopping`: cubes `Qᵢ ⊆ Q` with `lamᵠ < ⨍_{Qᵢ}g ≤ 4lamᵠ`, the `≤ 4lamᵠ` from
doubling against the non-stopping parent; `λ ≥ λ₀` is what makes
`⨍_Q g ≤ ⨍_{ball s}wᵠ ≤ lamᵠ` so the ambient does not stop) bounding the LHS by `Σ 4lamᵠ·vol(Qᵢ)`;
per-cube reverse-Hölder dichotomy `dyadic_reverseHolder'` into `w`-good / `b`-good cubes
(`⨍_{Eᵢ}w > γ·lam` or `⨍_{Eᵢ}bᵠ > (γlam)ᵠ`, `γ = 1/(2π^{1/q}A)`, `Eᵢ = ball(centre,4·2^{mᵢ})`);
super-level concentration (`β < γ`: `∫_{Eᵢ}w ≤ βlam·vol(Eᵢ) + ∫_{Eᵢ∩{w>βλ}}w` ⟹
`lam·vol(Eᵢ) ≤ (γ-β)⁻¹∫_{Eᵢ∩{w>βλ}}w`); and the Carleson sum via `gehring_engine_bound` on
`u := 1_{ball s ∩ {w>βλ}}·w`.  The boundary-collar term handles the geometric capping
`Eᵢ ⊆ ball s` (the `4×` enlargement of the at-most-`vol(ball s)`-sized stopping cubes need not, in
general, fit inside `ball s`), via the metric capped covering shared with the companion
super-level MEASURE bound `gehring_goodLambda_measure`. -/
theorem gehring_goodLambda_integral_core {q A : ℝ} (hq : 1 < q) (hA : 0 ≤ A)
    {w b : ℂ → ℝ≥0∞} (hwmeas : AEMeasurable w volume) (hbmeas : AEMeasurable b volume)
    (hRH : ∀ (x : ℂ) (r : ℝ), 0 < r →
      (⨍⁻ z in Metric.ball x r, w z ^ q ∂volume) ^ (1 / q) ≤
        ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), w z ∂volume) +
          ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), b z ^ q ∂volume) ^ (1 / q))
    (x₀ : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hWfin : ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q < ⊤)
    (hBfin : ∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ q < ⊤)
    (t s : ℝ) (ht : 4 * R₀ ≤ t) (hts : t < s) (hs : s ≤ 16 * R₀)
    (lam : ℝ) (hlam : 0 < lam)
    (hlam0cond : (⨍⁻ z in Metric.ball x₀ s, w z ^ q ∂volume) ≤ (ENNReal.ofReal lam) ^ q) :
    ∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (w z).toReal}, w z ^ q
      ≤ ENNReal.ofReal (256 * (Real.pi ^ (1 / q) * A + 1) * lam ^ (q - 1))
          * (∫⁻ z in Metric.ball x₀ s ∩
              {z | 1 / (4 * (Real.pi ^ (1 / q) * A + 1)) * lam < (w z).toReal}, w z)
        + ENNReal.ofReal (64 * (4 * (Real.pi ^ (1 / q) * A + 1)) ^ q)
          * (∫⁻ z in Metric.ball x₀ s ∩
              {z | 1 / (4 * (Real.pi ^ (1 / q) * A + 1)) * lam < (b z).toReal}, b z ^ q)
        -- BOUNDARY COLLAR: the contribution of the (few, large) stopping cubes whose `4×`
        -- enlargement spills outside `ball x₀ s`; bounded by `4·lamᵠ·vol(ball s)`.  This term
        -- vanishes for `lam` above the structural threshold `λ₁` (any boundary cube would force
        -- `lamᵠ·((s-t)/10)² < ∫_{ball s}wᵠ ≤ Wmaster`), making its λ-integral finite; the
        -- consumer integrates this good-λ on `(λ₀, λ₁)` and uses the collar-free form above.
        + ENNReal.ofReal (4 * lam ^ q) * volume (Metric.ball x₀ s) := by
  classical
  have hq0 : 0 < q := lt_trans one_pos hq
  have hst : 0 < s - t := by linarith
  have hspos : 0 < s := by linarith
  -- Planar doubling instance for the Carleson engine.
  have hdbl : (volume : Measure ℂ).IsDoubling (2 ^ Module.finrank ℝ ℂ) :=
    InnerProductSpace.IsDoubling
  -- Abbreviation `Ã = π^{1/q}·A + 1 > 0` (the reverse-Hölder constant, padded by 1).
  set P : ℝ := Real.pi ^ (1 / q) with hPdef
  have hPpos : 0 < P := by rw [hPdef]; positivity
  set Ã : ℝ := P * A + 1 with hÃdef
  have hÃpos : 0 < Ã := by rw [hÃdef]; nlinarith [hPpos, hA]
  -- The collar/level constants: `β = 1/(4Ã)`, w-level `lw = ofReal(βlam)`,
  -- b-level `lb = ofReal((βlam)^q)`.
  set β : ℝ := 1 / (4 * Ã) with hβdef
  have hβpos : 0 < β := by rw [hβdef]; positivity
  set lw : ℝ≥0∞ := ENNReal.ofReal (β * lam) with hlwdef
  set lb : ℝ≥0∞ := ENNReal.ofReal ((β * lam) ^ q) with hlbdef
  -- Choose `M` minimal-ish with `2s ≤ 2^M` (any large enough `M` works for the cover).
  obtain ⟨M, hM⟩ : ∃ M : ℤ, 2 * s ≤ (2 : ℝ) ^ M := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * s) (by norm_num : (1:ℝ) < 2)
    exact ⟨(n : ℤ), by rw [zpow_natCast]; exact hn.le⟩
  -- Run the global dyadic cover.
  obtain ⟨B, hBct, hBdisj, hBscale, hBmeet, hBcov, hBup, hBlow⟩ :=
    gehring_dyadic_global_cover hq0 hwmeas x₀ s hspos M hM lam hlam hlam0cond
  -- Geometry of a cube `i ∈ B`: centre, scale, enlarged ball `Eᵢ = ball cᵢ (4·2^{nᵢ})`.
  set cI : ℤ × (ℤ × ℤ) → ℂ := fun i => dyadicCenter i.1 i.2 with hcIdef
  set ρI : ℤ × (ℤ × ℤ) → ℝ := fun i => (2 : ℝ) ^ i.1 with hρIdef
  have hρIpos : ∀ i, 0 < ρI i := fun i => by rw [hρIdef]; exact zpow_pos (by norm_num) _
  -- The cube is inside its circumscribed ball `ball cᵢ (2^{nᵢ})`.
  have hQsubball : ∀ i, dyadicSquare i.1 i.2 ⊆ Metric.ball (cI i) (ρI i) := by
    intro i; rw [hcIdef, hρIdef]; exact dyadicSquare_subset_ball i.1 i.2
  -- ============================================================================
  -- PER-CUBE REVERSE-HÖLDER DICHOTOMY (super-level concentrated).
  -- For `i ∈ B`: either `w`-good (`lw·vol(Eᵢ) ≤ ∫_{Eᵢ∩{w>βλ}} w`) or `b`-good
  -- (`lb·vol(Eᵢ) ≤ ∫_{Eᵢ∩{b>βλ}} bᵠ`), where `Eᵢ = ball cᵢ (4ρᵢ)`.
  -- ============================================================================
  set Esub : Set ℂ := {z : ℂ | β * lam < (w z).toReal} with hEsubdef
  set Fsub : Set ℂ := {z : ℂ | β * lam < (b z).toReal} with hFsubdef
  -- Full (un-restricted) reverse-Hölder levels `lwf = lam/(2Ã)`, `lbf = (lam/(2Ã))^q`.
  set lwf : ℝ≥0∞ := ENNReal.ofReal (lam / (2 * Ã)) with hlwfdef
  set lbf : ℝ≥0∞ := ENNReal.ofReal ((lam / (2 * Ã)) ^ q) with hlbfdef
  have hdich : ∀ i ∈ B,
      (lwf * volume (Metric.ball (cI i) (4 * ρI i))
        ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), w z) ∨
      (lbf * volume (Metric.ball (cI i) (4 * ρI i))
        ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q) := by
    intro i hi
    -- `lam < (⨍_{Qᵢ} wᵠ)^{1/q}`.
    have hQpos : 0 < volume (dyadicSquare i.1 i.2) := by
      rw [volume_dyadicSquare, ENNReal.ofReal_pos]; positivity
    have hQtop : volume (dyadicSquare i.1 i.2) ≠ ⊤ := by
      rw [volume_dyadicSquare]; exact ENNReal.ofReal_ne_top
    have hlowfull : (ENNReal.ofReal lam) ^ q < ⨍⁻ z in dyadicSquare i.1 i.2, w z ^ q ∂volume := by
      refine lt_of_lt_of_le (hBlow i hi) ?_
      rw [setLAverage_eq]
      exact ENNReal.div_le_div_right (lintegral_mono_set Set.inter_subset_left) _
    have h1q : (0:ℝ) < 1 / q := by positivity
    have hroot : ENNReal.ofReal lam <
        (⨍⁻ z in dyadicSquare i.1 i.2, w z ^ q ∂volume) ^ (1 / q) := by
      have h := ENNReal.rpow_lt_rpow hlowfull h1q
      have hid : (ENNReal.ofReal lam ^ q) ^ (1 / q) = ENNReal.ofReal lam := by
        rw [one_div, ENNReal.rpow_rpow_inv hq0.ne']
      rwa [hid] at h
    -- Reverse-Hölder on the cube, with constant `P·A ≤ Ã`.
    have hRHc := dyadic_reverseHolder' hq hA hRH i.1 i.2
    have hPA_le : ENNReal.ofReal (P * A) ≤ ENNReal.ofReal Ã :=
      ENNReal.ofReal_le_ofReal (by rw [hÃdef, hPdef]; nlinarith [hPpos, hA])
    have hRHc' : ENNReal.ofReal lam <
        ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), w z ∂volume) +
          ENNReal.ofReal Ã *
            (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume) ^ (1 / q) := by
      have hceq : Metric.ball (dyadicCenter i.1 i.2) (4 * (2:ℝ) ^ i.1)
          = Metric.ball (cI i) (4 * ρI i) := by rw [hcIdef, hρIdef]
      rw [hceq] at hRHc
      refine lt_of_lt_of_le hroot (le_trans hRHc (add_le_add ?_ ?_)) <;>
        exact mul_le_mul_left hPA_le _
    -- One of the two terms is `≥ ofReal lam / 2`.
    have hvol4_pos : 0 < volume (Metric.ball (cI i) (4 * ρI i)) :=
      Metric.measure_ball_pos _ _ (by positivity [hρIpos i])
    have hvol4_ne : volume (Metric.ball (cI i) (4 * ρI i)) ≠ 0 := hvol4_pos.ne'
    have hvol4_top : volume (Metric.ball (cI i) (4 * ρI i)) ≠ ⊤ := measure_ball_lt_top.ne
    have hÃne : ENNReal.ofReal Ã ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hÃpos
    have hÃtop : ENNReal.ofReal Ã ≠ ⊤ := ENNReal.ofReal_ne_top
    have hhalf : ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), w z ∂volume)
          ≥ ENNReal.ofReal lam / 2 ∨
        ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume) ^ (1 / q)
          ≥ ENNReal.ofReal lam / 2 := by
      by_contra hcon
      rw [not_or] at hcon
      obtain ⟨h1, h2⟩ := hcon
      rw [not_le] at h1 h2
      have hsum2 : ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), w z ∂volume) +
          ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume) ^ (1 / q)
          < ENNReal.ofReal lam / 2 + ENNReal.ofReal lam / 2 := ENNReal.add_lt_add h1 h2
      rw [ENNReal.add_halves] at hsum2
      exact absurd (lt_trans hRHc' hsum2) (lt_irrefl _)
    -- `lwf · ofReal Ã = ofReal lam / 2`.
    have hlwf_mul : lwf * ENNReal.ofReal Ã = ENNReal.ofReal lam / 2 := by
      rw [hlwfdef, ← ENNReal.ofReal_mul (by positivity)]
      have hreal : lam / (2 * Ã) * Ã = lam / 2 := by field_simp
      rw [hreal, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
      congr 1; norm_num
    rcases hhalf with hw | hb
    · left
      have hge : lwf ≤ ⨍⁻ z in Metric.ball (cI i) (4 * ρI i), w z ∂volume := by
        have hchain : lwf * ENNReal.ofReal Ã
            ≤ (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), w z ∂volume) * ENNReal.ofReal Ã := by
          rw [hlwf_mul, mul_comm]; exact hw
        exact (ENNReal.mul_le_mul_iff_left hÃne hÃtop).mp hchain
      rw [setLAverage_eq] at hge
      rwa [ENNReal.le_div_iff_mul_le (Or.inl hvol4_ne) (Or.inl hvol4_top)] at hge
    · right
      have hlbf_eq : lbf = lwf ^ q := by
        rw [hlbfdef, hlwfdef, ← ENNReal.ofReal_rpow_of_pos (by positivity)]
      have hgew : lwf ≤ (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume) ^ (1 / q) := by
        have hchain : lwf * ENNReal.ofReal Ã
            ≤ (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume) ^ (1 / q)
                * ENNReal.ofReal Ã := by
          rw [hlwf_mul, mul_comm]; exact hb
        exact (ENNReal.mul_le_mul_iff_left hÃne hÃtop).mp hchain
      have hgeq : lbf ≤ ⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume := by
        rw [hlbf_eq]
        have hpow := ENNReal.rpow_le_rpow hgew hq0.le
        rwa [one_div, ENNReal.rpow_inv_rpow hq0.ne'] at hpow
      rw [setLAverage_eq] at hgeq
      rwa [ENNReal.le_div_iff_mul_le (Or.inl hvol4_ne) (Or.inl hvol4_top)] at hgeq
  -- ============================================================================
  -- SETUP for the assembly: containments, a.e. finiteness, the inner predicate.
  -- ============================================================================
  have hssub16 : Metric.ball x₀ s ⊆ Metric.ball x₀ (16 * R₀) :=
    Metric.ball_subset_ball (by linarith)
  -- `w < ⊤` a.e. on `ball s`.
  have hwfin_ae : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ s)), w z ≠ ⊤ := by
    have h16 : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (16 * R₀))), w z ^ q ≠ ⊤ :=
      ae_lt_top' (hwmeas.pow_const q).restrict hWfin.ne |>.mono (fun z hz => hz.ne)
    have : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (16 * R₀))), w z ≠ ⊤ := by
      filter_upwards [h16] with z hz htop
      rw [htop, ENNReal.top_rpow_of_pos hq0] at hz; exact hz rfl
    exact (ae_mono (Measure.restrict_mono hssub16 le_rfl)) this
  -- `b < ⊤` a.e. on `ball s`.
  have hbfin_ae : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ s)), b z ≠ ⊤ := by
    have h16 : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (16 * R₀))), b z ^ q ≠ ⊤ :=
      ae_lt_top' (hbmeas.pow_const q).restrict hBfin.ne |>.mono (fun z hz => hz.ne)
    have : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (16 * R₀))), b z ≠ ⊤ := by
      filter_upwards [h16] with z hz htop
      rw [htop, ENNReal.top_rpow_of_pos hq0] at hz; exact hz rfl
    exact (ae_mono (Measure.restrict_mono hssub16 le_rfl)) this
  -- The inner predicate: the enlargement `Eᵢ ⊆ ball x₀ s` (engine-able cubes).
  set Inn : Set (ℤ × (ℤ × ℤ)) :=
    {i ∈ B | Metric.ball (cI i) (4 * ρI i) ⊆ Metric.ball x₀ s} with hInndef
  -- The w-good and b-good inner subfamilies.
  set Sw : Set (ℤ × (ℤ × ℤ)) := {i ∈ Inn |
      lwf * volume (Metric.ball (cI i) (4 * ρI i))
        ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), w z} with hSwdef
  set Sb : Set (ℤ × (ℤ × ℤ)) := {i ∈ Inn |
      lbf * volume (Metric.ball (cI i) (4 * ρI i))
        ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q} with hSbdef
  have hSwsub : Sw ⊆ B := fun i hi => hi.1.1
  have hSbsub : Sb ⊆ B := fun i hi => hi.1.1
  have hSwct : Sw.Countable := hBct.mono hSwsub
  have hSbct : Sb.Countable := hBct.mono hSbsub
  -- The localized `u`-weights.
  set uw : ℂ → ℝ≥0∞ := (Metric.ball x₀ s ∩ Esub).indicator w with huwdef
  set ub : ℂ → ℝ≥0∞ := (Metric.ball x₀ s ∩ Fsub).indicator (fun z => b z ^ q) with hubdef
  -- ============================================================================
  -- PER-CUBE ENGINE HYPOTHESES (super-level concentration on inner cubes).
  -- ============================================================================
  have hEsub_nm : NullMeasurableSet Esub volume :=
    nullMeasurableSet_lt aemeasurable_const hwmeas.ennreal_toReal
  have hFsub_nm : NullMeasurableSet Fsub volume :=
    nullMeasurableSet_lt aemeasurable_const hbmeas.ennreal_toReal
  -- w-good inner: `lw·vol(Eᵢ) ≤ ∫_{Eᵢ} uw`.
  have h2uw : ∀ i ∈ Sw, lw * volume (Metric.ball (cI i) (4 * ρI i))
      ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), uw z := by
    rintro i ⟨⟨hiB, hEsub⟩, hwg⟩
    set E : Set ℂ := Metric.ball (cI i) (4 * ρI i) with hEdef
    have hEsubs : E ⊆ Metric.ball x₀ s := hEsub
    have hvolE_top : volume E ≠ ⊤ := measure_ball_lt_top.ne
    -- `∫_E uw = ∫_{E ∩ Esub} w` (since `E ⊆ ball s`).
    have huwint : ∫⁻ z in E, uw z = ∫⁻ z in E ∩ Esub, w z := by
      have hpt : ∀ z ∈ E, uw z = Esub.indicator w z := by
        intro z hz
        rw [huwdef]
        by_cases hzE : z ∈ Esub
        · have hmem : z ∈ Metric.ball x₀ s ∩ Esub := ⟨hEsubs hz, hzE⟩
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hzE]
        · have hnmem : z ∉ Metric.ball x₀ s ∩ Esub := fun h => hzE h.2
          rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hzE]
      rw [setLIntegral_congr_fun measurableSet_ball hpt,
        setLIntegral_indicator₀ _
          (hEsub_nm.mono_ac (Measure.restrict_le_self.absolutelyContinuous)),
        Set.inter_comm]
    -- Pointwise a.e. on `E`: `w z ≤ Esub.indicator w z + ofReal(βlam)`.
    have hconc : ∫⁻ z in E, w z
        ≤ (∫⁻ z in E, Esub.indicator w z) + ENNReal.ofReal (β * lam) * volume E := by
      have hstep : ∫⁻ z in E, w z
          ≤ ∫⁻ z in E, (Esub.indicator w z + ENNReal.ofReal (β * lam)) := by
        apply lintegral_mono_ae
        have haef : ∀ᵐ z ∂(volume.restrict E), w z ≠ ⊤ :=
          ae_mono (Measure.restrict_mono hEsubs le_rfl) hwfin_ae
        filter_upwards [haef] with z hzfin
        by_cases hzE : z ∈ Esub
        · rw [Set.indicator_of_mem hzE]; exact le_add_right le_rfl
        · rw [Set.indicator_of_notMem hzE, zero_add]
          rw [hEsubdef, Set.mem_ofPred_eq, not_lt] at hzE
          rw [← ENNReal.ofReal_toReal hzfin]
          exact ENNReal.ofReal_le_ofReal hzE
      rwa [lintegral_add_right' _ aemeasurable_const, setLIntegral_const] at hstep
    have hindint : ∫⁻ z in E, Esub.indicator w z = ∫⁻ z in E ∩ Esub, w z := by
      rw [setLIntegral_indicator₀ _ (hEsub_nm.mono_ac
        (Measure.restrict_le_self.absolutelyContinuous)), Set.inter_comm]
    rw [hindint] at hconc
    -- Combine: `lwf·vol(E) ≤ ∫_E w`, and `lwf = lw + ofReal(βlam)`.
    have hlw_eq : lw + ENNReal.ofReal (β * lam) = lwf := by
      rw [hlwdef, hlwfdef, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      rw [hβdef]; field_simp; ring
    rw [huwint]
    have hkey : lwf * volume E
        ≤ (∫⁻ z in E ∩ Esub, w z) + ENNReal.ofReal (β * lam) * volume E := le_trans hwg hconc
    rw [← hlw_eq, add_mul] at hkey
    refine ENNReal.le_of_add_le_add_right ?_ hkey
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvolE_top
  -- b-good inner: `lb·vol(Eᵢ) ≤ ∫_{Eᵢ} ub`.
  have h2ub : ∀ i ∈ Sb, lb * volume (Metric.ball (cI i) (4 * ρI i))
      ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), ub z := by
    rintro i ⟨⟨hiB, hEsub⟩, hbg⟩
    set E : Set ℂ := Metric.ball (cI i) (4 * ρI i) with hEdef
    have hEsubs : E ⊆ Metric.ball x₀ s := hEsub
    have hvolE_top : volume E ≠ ⊤ := measure_ball_lt_top.ne
    have hubint : ∫⁻ z in E, ub z = ∫⁻ z in E ∩ Fsub, b z ^ q := by
      have hpt : ∀ z ∈ E, ub z = Fsub.indicator (fun z => b z ^ q) z := by
        intro z hz
        rw [hubdef]
        by_cases hzF : z ∈ Fsub
        · have hmem : z ∈ Metric.ball x₀ s ∩ Fsub := ⟨hEsubs hz, hzF⟩
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hzF]
        · have hnmem : z ∉ Metric.ball x₀ s ∩ Fsub := fun h => hzF h.2
          rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hzF]
      rw [setLIntegral_congr_fun measurableSet_ball hpt,
        setLIntegral_indicator₀ _
          (hFsub_nm.mono_ac (Measure.restrict_le_self.absolutelyContinuous)),
        Set.inter_comm]
    -- Super-level concentration: `bᵠ z ≤ Fsub.indicator bᵠ z + ofReal((βlam)^q)` a.e. on `E`.
    have hconc : ∫⁻ z in E, b z ^ q
        ≤ (∫⁻ z in E, Fsub.indicator (fun z => b z ^ q) z)
          + ENNReal.ofReal ((β * lam) ^ q) * volume E := by
      have hstep : ∫⁻ z in E, b z ^ q
          ≤ ∫⁻ z in E, (Fsub.indicator (fun z => b z ^ q) z + ENNReal.ofReal ((β * lam) ^ q)) := by
        apply lintegral_mono_ae
        have haef : ∀ᵐ z ∂(volume.restrict E), b z ≠ ⊤ :=
          ae_mono (Measure.restrict_mono hEsubs le_rfl) hbfin_ae
        filter_upwards [haef] with z hzfin
        by_cases hzF : z ∈ Fsub
        · rw [Set.indicator_of_mem hzF]; exact le_add_right le_rfl
        · rw [Set.indicator_of_notMem hzF, zero_add]
          rw [hFsubdef, Set.mem_ofPred_eq, not_lt] at hzF
          rw [← ENNReal.ofReal_toReal hzfin,
            ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq0.le]
          exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ENNReal.toReal_nonneg hzF hq0.le)
      rwa [lintegral_add_right' _ aemeasurable_const, setLIntegral_const] at hstep
    have hindint : ∫⁻ z in E, Fsub.indicator (fun z => b z ^ q) z = ∫⁻ z in E ∩ Fsub, b z ^ q := by
      rw [setLIntegral_indicator₀ _ (hFsub_nm.mono_ac
        (Measure.restrict_le_self.absolutelyContinuous)), Set.inter_comm]
    rw [hindint] at hconc
    -- `lb + ofReal((βlam)^q) ≤ lbf` (since `2 ≤ 2^q`).
    have hlb_le : lb + ENNReal.ofReal ((β * lam) ^ q) ≤ lbf := by
      rw [hlbdef, hlbfdef, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have h2q : (2:ℝ) ≤ 2 ^ q := by
        calc (2:ℝ) = 2 ^ (1:ℝ) := by rw [Real.rpow_one]
          _ ≤ 2 ^ q := Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt hq)
      have hβl : (0:ℝ) ≤ β * lam := by positivity
      have hkey : 2 * (β * lam) ^ q ≤ (lam / (2 * Ã)) ^ q := by
        have heq : lam / (2 * Ã) = 2 * (β * lam) := by rw [hβdef]; field_simp; ring
        rw [heq, Real.mul_rpow (by norm_num) hβl]
        nlinarith [Real.rpow_nonneg hβl q, h2q]
      linarith [hkey]
    rw [hubint]
    have hkey : lbf * volume E
        ≤ (∫⁻ z in E ∩ Fsub, b z ^ q) + ENNReal.ofReal ((β * lam) ^ q) * volume E :=
      le_trans hbg hconc
    have hlbstep : (lb + ENNReal.ofReal ((β * lam) ^ q)) * volume E
        ≤ (∫⁻ z in E ∩ Fsub, b z ^ q) + ENNReal.ofReal ((β * lam) ^ q) * volume E :=
      le_trans (mul_le_mul_left hlb_le _) hkey
    rw [add_mul] at hlbstep
    refine ENNReal.le_of_add_le_add_right ?_ hlbstep
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvolE_top
  -- ============================================================================
  -- ENGINE CALLS: bound `vol(⋃_{Sw} Eᵢ)`, `vol(⋃_{Sb} Eᵢ)` by super-level integrals.
  -- ============================================================================
  -- Radius bound: for inner cubes, `4·ρI i ≤ s` (since `Eᵢ ⊆ ball x₀ s`).
  have hRbd : ∀ i ∈ Inn, 4 * ρI i ≤ s := by
    rintro i ⟨hiB, hEsub⟩
    by_contra hgt
    push Not at hgt
    have hvle : volume (Metric.ball (cI i) (4 * ρI i)) ≤ volume (Metric.ball x₀ s) :=
      measure_mono hEsub
    rw [Complex.volume_ball, Complex.volume_ball] at hvle
    have h4ρpos : 0 < 4 * ρI i := by have := hρIpos i; linarith
    rw [ENNReal.mul_le_mul_iff_left (by simp [NNReal.pi_pos.ne']) (by simp)] at hvle
    rw [← ENNReal.ofReal_pow h4ρpos.le, ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ s),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hvle
    nlinarith [hvle, hgt, h4ρpos]
  have hRbdSw : ∀ i ∈ Sw, 4 * ρI i ≤ s := fun i hi => hRbd i hi.1
  have hRbdSb : ∀ i ∈ Sb, 4 * ρI i ≤ s := fun i hi => hRbd i hi.1
  have hEw := gehring_engine_idx Sw hSwct cI (fun i => 4 * ρI i) lw uw s hRbdSw h2uw
  have hEb := gehring_engine_idx Sb hSbct cI (fun i => 4 * ρI i) lb ub s hRbdSb h2ub
  -- The global integrals of `uw`, `ub` are the super-level masses over `ball x₀ s`.
  have hIuw : ∫⁻ z, uw z = ∫⁻ z in Metric.ball x₀ s ∩ Esub, w z := by
    rw [huwdef, lintegral_indicator₀ (measurableSet_ball.nullMeasurableSet.inter hEsub_nm)]
  have hIub : ∫⁻ z, ub z = ∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q := by
    rw [hubdef, lintegral_indicator₀ (measurableSet_ball.nullMeasurableSet.inter hFsub_nm)]
  rw [hIuw] at hEw
  rw [hIub] at hEb
  -- ============================================================================
  -- LHS BOUND and FINAL ASSEMBLY.
  -- ============================================================================
  set S : Set ℂ := Metric.ball x₀ t ∩ {z : ℂ | lam < (w z).toReal} with hSdef
  have htsub : Metric.ball x₀ t ⊆ Metric.ball x₀ s := Metric.ball_subset_ball hts.le
  -- The cube sets `Cᵢ := Qᵢ ∩ ball s` are measurable and pairwise disjoint on `B`.
  set Cset : ℤ × (ℤ × ℤ) → Set ℂ := fun i => dyadicSquare i.1 i.2 ∩ Metric.ball x₀ s with hCsetdef
  have hCmeas : ∀ i, MeasurableSet (Cset i) :=
    fun i => (measurableSet_dyadicSquare _ _).inter measurableSet_ball
  have hCdisj : B.PairwiseDisjoint Cset := by
    intro i hi j hj hij
    exact (hBdisj hi hj hij).mono Set.inter_subset_left Set.inter_subset_left
  -- `S` is a.e. covered by `⋃_{i∈B} Cset i`.
  have hScov : volume (S \ ⋃ i ∈ B, Cset i) = 0 := by
    refine measure_mono_null ?_ hBcov
    intro z hz
    obtain ⟨hzS, hznotcov⟩ := hz
    have hzs : z ∈ Metric.ball x₀ s ∩ {z : ℂ | lam < (w z).toReal} :=
      ⟨htsub hzS.1, hzS.2⟩
    refine ⟨hzs, ?_⟩
    intro hzcov
    apply hznotcov
    rw [Set.mem_iUnion₂] at hzcov ⊢
    obtain ⟨i, hi, hzi⟩ := hzcov
    exact ⟨i, hi, hzi, hzs.1⟩
  -- `∫_S wᵠ ≤ ∫_{⋃_{i∈B} Cset i} wᵠ`.
  set U : Set ℂ := ⋃ i ∈ B, Cset i with hUdef
  have hLHS1 : ∫⁻ z in S, w z ^ q ≤ ∫⁻ z in U, w z ^ q := by
    have h1 : (S \ (S \ U) : Set ℂ) =ᵐ[volume] S := sdiff_null_ae_eq_self hScov
    have h2 : S \ (S \ U) = S ∩ U := Set.sdiff_sdiff_right_self S U
    rw [h2] at h1
    rw [setLIntegral_congr h1.symm]
    exact lintegral_mono_set Set.inter_subset_right
  -- Split `⋃_{i∈B} Cset = (⋃_{Inn}) ∪ (⋃_{B\Inn})`, a disjoint union.
  have hInnsubB : Inn ⊆ B := fun i hi => hi.1
  have hUsplit : (⋃ i ∈ B, Cset i)
      = (⋃ i ∈ Inn, Cset i) ∪ (⋃ i ∈ B \ Inn, Cset i) := by
    rw [← Set.biUnion_union]
    congr 1
    rw [Set.union_sdiff_cancel hInnsubB]
  have hUdisj : Disjoint (⋃ i ∈ Inn, Cset i) (⋃ i ∈ B \ Inn, Cset i) := by
    rw [Set.disjoint_iff_forall_ne]
    rintro x hx y hy rfl
    rw [Set.mem_iUnion₂] at hx hy
    obtain ⟨i, hiI, hxi⟩ := hx
    obtain ⟨j, ⟨hjB, hjnI⟩, hxj⟩ := hy
    have hij : i ≠ j := fun h => hjnI (h ▸ hiI)
    exact (hCdisj (hInnsubB hiI) hjB hij).le_bot ⟨hxi, hxj⟩ |>.elim
  have hUmeasBd : MeasurableSet (⋃ i ∈ B \ Inn, Cset i) := by
    apply MeasurableSet.biUnion (hBct.mono (Set.sdiff_subset))
    exact fun i _ => hCmeas i
  -- `∫_{⋃_B} = ∫_{⋃_Inn} + ∫_{⋃_{B\Inn}}`.
  have hLHS2 : ∫⁻ z in ⋃ i ∈ B, Cset i, w z ^ q
      = (∫⁻ z in ⋃ i ∈ Inn, Cset i, w z ^ q) + ∫⁻ z in ⋃ i ∈ B \ Inn, Cset i, w z ^ q := by
    rw [hUsplit, lintegral_union hUmeasBd hUdisj]
  -- BOUNDARY BOUND: `∫_{⋃_{B\Inn} Cset} wᵠ ≤ ofReal(lamᵠ)·vol(ball s)`.
  have hUbdsubs : (⋃ i ∈ B \ Inn, Cset i) ⊆ Metric.ball x₀ s := by
    apply Set.iUnion₂_subset
    exact fun i _ => Set.inter_subset_right
  have hBoundary : ∫⁻ z in ⋃ i ∈ B \ Inn, Cset i, w z ^ q
      ≤ ENNReal.ofReal (lam ^ q) * volume (Metric.ball x₀ s) := by
    calc ∫⁻ z in ⋃ i ∈ B \ Inn, Cset i, w z ^ q
        ≤ ∫⁻ z in Metric.ball x₀ s, w z ^ q := lintegral_mono_set hUbdsubs
      _ ≤ ENNReal.ofReal (lam ^ q) * volume (Metric.ball x₀ s) := by
          have hav := hlam0cond
          rw [setLAverage_eq, ENNReal.ofReal_rpow_of_nonneg hlam.le hq0.le] at hav
          have hvol_ne : volume (Metric.ball x₀ s) ≠ 0 := (Metric.measure_ball_pos _ _ hspos).ne'
          have hvol_top : volume (Metric.ball x₀ s) ≠ ⊤ := measure_ball_lt_top.ne
          exact (ENNReal.div_le_iff_le_mul (Or.inl hvol_ne) (Or.inl hvol_top)).mp hav
  -- INNER BOUND: `∫_{⋃_{Inn} Cset} wᵠ ≤ ofReal(4lamᵠ)·(vol(⋃_{Sw}Eᵢ) + vol(⋃_{Sb}Eᵢ))`.
  -- Step (a): `∫_{⋃_{Inn} Cset} wᵠ = Σ_{i:Inn} ∫_{Cset i} wᵠ ≤ ofReal(4lamᵠ)·vol(⋃_{Inn} Qᵢ)`.
  have hInnct : Inn.Countable := hBct.mono hInnsubB
  have hInnerSum : ∫⁻ z in ⋃ i ∈ Inn, Cset i, w z ^ q
      ≤ ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Inn, dyadicSquare i.1 i.2) := by
    rw [lintegral_biUnion hInnct (fun i _ => hCmeas i)
      (hCdisj.subset hInnsubB)]
    calc ∑' i : Inn, ∫⁻ z in Cset i, w z ^ q
        ≤ ∑' i : Inn, ENNReal.ofReal (4 * lam ^ q)
            * volume (dyadicSquare (i : ℤ × (ℤ × ℤ)).1 (i : ℤ × (ℤ × ℤ)).2) := by
          apply ENNReal.tsum_le_tsum
          rintro ⟨i, hi⟩
          exact hBup i (hInnsubB hi)
      _ = ENNReal.ofReal (4 * lam ^ q)
            * ∑' i : Inn, volume (dyadicSquare (i : ℤ × (ℤ × ℤ)).1 (i : ℤ × (ℤ × ℤ)).2) :=
          ENNReal.tsum_mul_left
      _ = ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Inn, dyadicSquare i.1 i.2) := by
          rw [measure_biUnion hInnct (Set.Pairwise.mono hInnsubB hBdisj)
            (fun i _ => measurableSet_dyadicSquare _ _)]
  -- Step (b): `vol(⋃_{Inn} Qᵢ) ≤ vol(⋃_{Sw} Eᵢ) + vol(⋃_{Sb} Eᵢ)`.
  have hQcover : (⋃ i ∈ Inn, dyadicSquare i.1 i.2)
      ⊆ (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))
        ∪ (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)) := by
    apply Set.iUnion₂_subset
    intro i hi
    have hiB : i ∈ B := hInnsubB hi
    have hQE : dyadicSquare i.1 i.2 ⊆ Metric.ball (cI i) (4 * ρI i) := by
      refine (hQsubball i).trans (Metric.ball_subset_ball ?_)
      have := hρIpos i; linarith
    rcases hdich i hiB with hw | hb
    · have hiSw : i ∈ Sw := ⟨hi, hw⟩
      exact hQE.trans (Set.subset_union_of_subset_left
        (Set.subset_biUnion_of_mem (u := fun i => Metric.ball (cI i) (4 * ρI i)) hiSw) _)
    · have hiSb : i ∈ Sb := ⟨hi, hb⟩
      exact hQE.trans (Set.subset_union_of_subset_right
        (Set.subset_biUnion_of_mem (u := fun i => Metric.ball (cI i) (4 * ρI i)) hiSb) _)
  have hQvol : volume (⋃ i ∈ Inn, dyadicSquare i.1 i.2)
      ≤ volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))
        + volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)) :=
    le_trans (measure_mono hQcover) (measure_union_le _ _)
  -- ============================================================================
  -- COEFFICIENT TRANSFER.  `ofReal(4lamᵠ)·vol(⋃_{Sw}Eᵢ) ≤ ofReal(Cw)·∫_{ball s∩Esub}w`,
  -- and similarly for `Sb`.
  -- ============================================================================
  set Cw : ℝ := 256 * Ã * lam ^ (q - 1) with hCwdef
  set Cb : ℝ := 64 * (4 * Ã) ^ q with hCbdef
  have hlw_ne : lw ≠ 0 := by rw [hlwdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hlb_ne : lb ≠ 0 := by rw [hlbdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hlw_top : lw ≠ ⊤ := by rw [hlwdef]; exact ENNReal.ofReal_ne_top
  have hlb_top : lb ≠ ⊤ := by rw [hlbdef]; exact ENNReal.ofReal_ne_top
  -- Real identity: `lam^{q-1}·lam = lam^q`.
  have hlamq : lam ^ (q - 1) * lam = lam ^ q := by
    have h := (Real.rpow_add hlam (q - 1) 1).symm
    rw [Real.rpow_one] at h
    rw [h]; congr 1; ring
  -- `ofReal Cw · lw = 16 · ofReal(4lamᵠ)`.
  have hCw_mul : ENNReal.ofReal Cw * lw = 16 * ENNReal.ofReal (4 * lam ^ q) := by
    rw [hCwdef, hlwdef, ← ENNReal.ofReal_mul (by positivity),
      show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by rw [ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [hβdef]
    have : 256 * Ã * lam ^ (q - 1) * (1 / (4 * Ã) * lam) = 64 * (lam ^ (q - 1) * lam) := by
      field_simp; ring
    rw [this, hlamq]; ring
  -- `ofReal Cb · lb = 16 · ofReal(4lamᵠ)`.
  have hCb_mul : ENNReal.ofReal Cb * lb = 16 * ENNReal.ofReal (4 * lam ^ q) := by
    rw [hCbdef, hlbdef, ← ENNReal.ofReal_mul (by positivity),
      show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by rw [ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    -- `64·(4Ã)^q·(βlam)^q = 64·lamᵠ`, since `(4Ã)^q·(βlam)^q = (4Ã·βlam)^q = lamᵠ`.
    have hbase : (4 * Ã) * (β * lam) = lam := by rw [hβdef]; field_simp
    have hmr : (4 * Ã) ^ q * (β * lam) ^ q = lam ^ q := by
      rw [← Real.mul_rpow (by positivity) (by positivity [hβpos]), hbase]
    rw [show (64 * (4 * Ã) ^ q * (β * lam) ^ q : ℝ) = 64 * ((4 * Ã) ^ q * (β * lam) ^ q) by ring,
      hmr]; ring
  -- Transfer the engine bounds to coefficient form.
  have hsixteen_ne : (16 : ℝ≥0∞) ≠ 0 := by norm_num
  have hsixteen_top : (16 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hTransW : ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))
      ≤ ENNReal.ofReal Cw * ∫⁻ z in Metric.ball x₀ s ∩ Esub, w z := by
    apply (ENNReal.mul_le_mul_iff_right hsixteen_ne hsixteen_top).mp
    calc (16 : ℝ≥0∞) * (ENNReal.ofReal (4 * lam ^ q)
            * volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i)))
        = (ENNReal.ofReal Cw * lw) * volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i)) := by
          rw [hCw_mul]; ring
      _ = ENNReal.ofReal Cw * (lw * volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))) := by ring
      _ ≤ ENNReal.ofReal Cw * (16 * ∫⁻ z in Metric.ball x₀ s ∩ Esub, w z) :=
          mul_le_mul_right hEw _
      _ = 16 * (ENNReal.ofReal Cw * ∫⁻ z in Metric.ball x₀ s ∩ Esub, w z) := by ring
  have hTransB : ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i))
      ≤ ENNReal.ofReal Cb * ∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q := by
    apply (ENNReal.mul_le_mul_iff_right hsixteen_ne hsixteen_top).mp
    calc (16 : ℝ≥0∞) * (ENNReal.ofReal (4 * lam ^ q)
            * volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)))
        = (ENNReal.ofReal Cb * lb) * volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)) := by
          rw [hCb_mul]; ring
      _ = ENNReal.ofReal Cb * (lb * volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i))) := by ring
      _ ≤ ENNReal.ofReal Cb * (16 * ∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q) :=
          mul_le_mul_right hEb _
      _ = 16 * (ENNReal.ofReal Cb * ∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q) := by ring
  -- ============================================================================
  -- FINAL COMBINATION.
  -- ============================================================================
  -- The goal's super-level sets coincide with `Esub`, `Fsub` (`β = 1/(4(P·A+1))`).
  have hβeq : (1 : ℝ) / (4 * (Real.pi ^ (1 / q) * A + 1)) = β := by
    rw [hβdef, hÃdef, hPdef]
  have hCw_goal : (256 : ℝ) * (Real.pi ^ (1 / q) * A + 1) * lam ^ (q - 1) = Cw := by
    rw [hCwdef, hÃdef, hPdef]
  have hCb_goal : (64 : ℝ) * (4 * (Real.pi ^ (1 / q) * A + 1)) ^ q = Cb := by
    rw [hCbdef, hÃdef, hPdef]
  -- The goal coincides (definitionally + via `hβeq`/`hCw_goal`/`hCb_goal`) with the bound below.
  have hgoal : ∫⁻ z in S, w z ^ q
      ≤ (ENNReal.ofReal Cw * (∫⁻ z in Metric.ball x₀ s ∩ Esub, w z)
          + ENNReal.ofReal Cb * (∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q))
          + ENNReal.ofReal (4 * lam ^ q) * volume (Metric.ball x₀ s) :=
    calc ∫⁻ z in S, w z ^ q
        ≤ ∫⁻ z in ⋃ i ∈ B, Cset i, w z ^ q := hLHS1
      _ = (∫⁻ z in ⋃ i ∈ Inn, Cset i, w z ^ q) + ∫⁻ z in ⋃ i ∈ B \ Inn, Cset i, w z ^ q := hLHS2
      _ ≤ ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Inn, dyadicSquare i.1 i.2)
            + ENNReal.ofReal (lam ^ q) * volume (Metric.ball x₀ s) :=
          add_le_add hInnerSum hBoundary
      _ ≤ ENNReal.ofReal (4 * lam ^ q)
              * (volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))
                + volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)))
            + ENNReal.ofReal (4 * lam ^ q) * volume (Metric.ball x₀ s) := by
          apply add_le_add (mul_le_mul_right hQvol _)
          exact mul_le_mul_left
            (ENNReal.ofReal_le_ofReal (by nlinarith [Real.rpow_nonneg hlam.le q])) _
      _ = (ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))
            + ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)))
            + ENNReal.ofReal (4 * lam ^ q) * volume (Metric.ball x₀ s) := by rw [mul_add]
      _ ≤ (ENNReal.ofReal Cw * (∫⁻ z in Metric.ball x₀ s ∩ Esub, w z)
            + ENNReal.ofReal Cb * (∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q))
            + ENNReal.ofReal (4 * lam ^ q) * volume (Metric.ball x₀ s) :=
          add_le_add (add_le_add hTransW hTransB) le_rfl
  -- The goal is already (definitionally, via the `set`s) in `Cw, Cb, Esub, Fsub` form.
  exact hgoal


end NoWanderingDomains
