/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Dyadic squares on `ℂ` and the Calderón–Zygmund stopping foundation

This file develops the dyadic-square infrastructure on the plane `ℂ ≅ ℝ²` used by the
Calderón–Zygmund stopping-time proof of the Gehring self-improvement lemma
(`gehring_selfImprovement`).  Working with dyadic squares — rather than metric balls —
is what makes the Gehring layer-cake absorb on a *single* fixed square: a dyadic
decomposition keeps every stopping square nested inside the ambient square, so the
super-level mass on the left and the reconstructed mass on the right live over the same
domain (no enlargement leaks out, hence no maximal function and no radial iteration).

A generation-`n` dyadic square (side `2^n`, `n : ℤ`) with integer index `j : ℤ × ℤ` is the
half-open square `[2^n j.1, 2^n (j.1+1)) × [2^n j.2, 2^n (j.2+1))`, transported to `ℂ` along
`Complex.measurableEquivRealProd`.

## Main definitions and API

* `dyadicSquare n j` — the generation-`n`, index-`j` half-open dyadic square.
* `mem_dyadicSquare`, `measurableSet_dyadicSquare`, `volume_dyadicSquare` — the basic
  structural facts.
* `dyadicSquare_subset_or_disjoint` — the fundamental dyadic property: any two dyadic
  squares are nested or disjoint.
* `dyadicParent`, `dyadicSquare_subset_parent` — the unique one-generation-coarser
  parent and the nesting into it.
* `dyadicCenter`, `dyadicSquare_subset_ball`, `ball_subset_dyadicSquare` — the centre of a
  square and its inscribed/circumscribed ball comparability, the device transferring a
  metric-ball reverse-Hölder hypothesis to the dyadic squares.
* `dyadicIndexAt`, `mem_dyadicSquare_dyadicIndexAt` — the index of the generation-`m` square
  containing a point, and the membership witnessing it.

The analytic results built on this combinatorial foundation — the dyadic Lebesgue
differentiation theorem and the Calderón–Zygmund stopping-time decomposition — live in
`DyadicLebesgue.lean`.
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace NoWanderingDomains

/-- The generation-`n` dyadic square (side length `2 ^ n`, `n : ℤ`) with integer index
`j : ℤ × ℤ`: the half-open square
`[2^n j.1, 2^n (j.1+1)) × [2^n j.2, 2^n (j.2+1))` carried to `ℂ` along the
measure-preserving identification `ℂ ≃ᵐ ℝ × ℝ`. -/
def dyadicSquare (n : ℤ) (j : ℤ × ℤ) : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹'
    (Set.Ico ((2 : ℝ) ^ n * (j.1 : ℝ)) ((2 : ℝ) ^ n * ((j.1 : ℝ) + 1)) ×ˢ
      Set.Ico ((2 : ℝ) ^ n * (j.2 : ℝ)) ((2 : ℝ) ^ n * ((j.2 : ℝ) + 1)))

/-- Membership in a dyadic square in terms of the real and imaginary parts. -/
theorem mem_dyadicSquare {n : ℤ} {j : ℤ × ℤ} {z : ℂ} :
    z ∈ dyadicSquare n j ↔
      (2 : ℝ) ^ n * (j.1 : ℝ) ≤ z.re ∧ z.re < (2 : ℝ) ^ n * ((j.1 : ℝ) + 1) ∧
        (2 : ℝ) ^ n * (j.2 : ℝ) ≤ z.im ∧ z.im < (2 : ℝ) ^ n * ((j.2 : ℝ) + 1) := by
  simp only [dyadicSquare, Set.mem_preimage, Complex.measurableEquivRealProd_apply,
    Set.mem_prod, Set.mem_Ico]
  tauto

/-- Dyadic squares are measurable. -/
theorem measurableSet_dyadicSquare (n : ℤ) (j : ℤ × ℤ) :
    MeasurableSet (dyadicSquare n j) := by
  exact (MeasurableSet.prod measurableSet_Ico measurableSet_Ico).preimage
    Complex.measurableEquivRealProd.measurable

/-- The Lebesgue area of a generation-`n` dyadic square is `(2 ^ n) ^ 2`. -/
theorem volume_dyadicSquare (n : ℤ) (j : ℤ × ℤ) :
    volume (dyadicSquare n j) = ENNReal.ofReal (((2 : ℝ) ^ n) ^ 2) := by
  have hpos : (0:ℝ) < (2:ℝ) ^ n := zpow_pos (by norm_num) n
  have hms : MeasurableSet
      (Set.Ico ((2 : ℝ) ^ n * (j.1 : ℝ)) ((2 : ℝ) ^ n * ((j.1 : ℝ) + 1)) ×ˢ
        Set.Ico ((2 : ℝ) ^ n * (j.2 : ℝ)) ((2 : ℝ) ^ n * ((j.2 : ℝ) + 1))) :=
    MeasurableSet.prod measurableSet_Ico measurableSet_Ico
  rw [dyadicSquare,
    Complex.volume_preserving_equiv_real_prod.measure_preimage hms.nullMeasurableSet]
  have hprod : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) := rfl
  rw [hprod, Measure.prod_prod, Real.volume_Ico, Real.volume_Ico]
  have e1 : (2 : ℝ) ^ n * ((j.1 : ℝ) + 1) - (2 : ℝ) ^ n * (j.1 : ℝ) = (2:ℝ)^n := by ring
  have e2 : (2 : ℝ) ^ n * ((j.2 : ℝ) + 1) - (2 : ℝ) ^ n * (j.2 : ℝ) = (2:ℝ)^n := by ring
  rw [e1, e2, ← ENNReal.ofReal_mul (le_of_lt hpos)]
  congr 1
  rw [sq]

/-- **Fundamental dyadic property.** Any two dyadic squares are either nested or disjoint. -/
theorem dyadicSquare_subset_or_disjoint (n₁ : ℤ) (j₁ : ℤ × ℤ) (n₂ : ℤ) (j₂ : ℤ × ℤ) :
    dyadicSquare n₁ j₁ ⊆ dyadicSquare n₂ j₂ ∨ dyadicSquare n₂ j₂ ⊆ dyadicSquare n₁ j₁ ∨
      Disjoint (dyadicSquare n₁ j₁) (dyadicSquare n₂ j₂) := by
  have coord : ∀ (a b : ℤ), a ≤ b → ∀ (i k : ℤ),
      (∀ x : ℝ, (2:ℝ)^a * i ≤ x ∧ x < (2:ℝ)^a * (i+1) →
        (2:ℝ)^b * k ≤ x ∧ x < (2:ℝ)^b * (k+1)) ∨
      (∀ x : ℝ, ¬ ((2:ℝ)^a * i ≤ x ∧ x < (2:ℝ)^a * (i+1) ∧
        (2:ℝ)^b * k ≤ x ∧ x < (2:ℝ)^b * (k+1))) := by
    intro a b hab i k
    have hposa : (0:ℝ) < (2:ℝ) ^ a := zpow_pos (by norm_num) a
    have hba : (2:ℝ)^b = (2:ℝ)^a * (2:ℝ)^(b-a) := by
      rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]; ring_nf
    obtain ⟨m, hm, hmeq⟩ : ∃ m : ℕ, (2:ℝ)^(b-a) = (2:ℝ)^m ∧ b - a = (m : ℤ) := by
      refine ⟨(b-a).toNat, ?_, ?_⟩
      · rw [← zpow_natCast]; congr 1; rw [Int.toNat_of_nonneg (by omega)]
      · rw [Int.toNat_of_nonneg (by omega)]
    have hmpos : (0:ℝ) < (2^m:ℝ) := by positivity
    have hbm : (2:ℝ)^b = (2:ℝ)^a * (2^m:ℝ) := by rw [hba, hm]
    by_cases hin : (2:ℝ)^b * k ≤ (2:ℝ)^a * i ∧ (2:ℝ)^a * i < (2:ℝ)^b * (k+1)
    · left
      obtain ⟨hin1, hin2⟩ := hin
      have hupperint : i < (2^m : ℤ) * (k+1) := by
        have h : (2:ℝ)^a * (i:ℝ) < (2:ℝ)^a * ((2^m:ℝ)*((k:ℝ)+1)) := by
          rw [hbm] at hin2; nlinarith [hin2]
        have h' : (i:ℝ) < (2^m:ℝ) * ((k:ℝ)+1) := lt_of_mul_lt_mul_left h (le_of_lt hposa)
        have hcast : ((i:ℤ):ℝ) < (((2^m : ℤ) * (k+1) : ℤ):ℝ) := by push_cast; linarith
        exact_mod_cast hcast
      have hi1 : i + 1 ≤ (2^m : ℤ) * (k+1) := by omega
      rintro x ⟨hx1, hx2⟩
      refine ⟨by linarith [hin1], ?_⟩
      have hub : (2:ℝ)^a * ((i:ℝ)+1) ≤ (2:ℝ)^b * ((k:ℝ)+1) := by
        rw [hbm]
        have hcast : ((i:ℝ)+1) ≤ (2^m:ℝ)*((k:ℝ)+1) := by
          have : (((i+1:ℤ)):ℝ) ≤ (((2^m : ℤ) * (k+1):ℤ):ℝ) := by exact_mod_cast hi1
          push_cast at this; linarith
        nlinarith [hposa, hcast]
      linarith [hx2, hub]
    · right
      rintro x ⟨hx1, hx2, hx3, hx4⟩
      by_cases hcase : (2:ℝ)^b * k ≤ (2:ℝ)^a * i
      · have h1 : (2:ℝ)^b * (k+1) ≤ (2:ℝ)^a * i :=
          not_lt.mp (fun hc => hin ⟨hcase, hc⟩)
        linarith [hx1, hx4, h1]
      · have hcase : (2:ℝ)^a * i < (2:ℝ)^b * k := not_le.mp hcase
        have hii : i < (2^m:ℤ) * k := by
          have h : (2:ℝ)^a * (i:ℝ) < (2:ℝ)^a * ((2^m:ℝ)*(k:ℝ)) := by
            rw [hbm] at hcase; nlinarith [hcase]
          have h' : (i:ℝ) < (2^m:ℝ) * (k:ℝ) := lt_of_mul_lt_mul_left h (le_of_lt hposa)
          have hcast : ((i:ℤ):ℝ) < (((2^m:ℤ)*k:ℤ):ℝ) := by push_cast; linarith
          exact_mod_cast hcast
        have hi1 : i + 1 ≤ (2^m:ℤ) * k := by omega
        have hle : (2:ℝ)^a * ((i:ℝ)+1) ≤ (2:ℝ)^b * (k:ℝ) := by
          rw [hbm]
          have hcast : ((i:ℝ)+1) ≤ (2^m:ℝ)*(k:ℝ) := by
            have : (((i+1:ℤ)):ℝ) ≤ (((2^m:ℤ)*k:ℤ):ℝ) := by exact_mod_cast hi1
            push_cast at this; linarith
          nlinarith [hposa, hcast]
        linarith [hx2, hx3, hle]
  rcases le_total n₁ n₂ with hnle | hnle
  · rcases coord n₁ n₂ hnle j₁.1 j₂.1 with hx | hx <;>
    rcases coord n₁ n₂ hnle j₁.2 j₂.2 with hy | hy
    · left
      intro z hz
      rw [mem_dyadicSquare] at hz ⊢
      obtain ⟨h1, h2, h3, h4⟩ := hz
      obtain ⟨ha, hb⟩ := hx z.re ⟨h1, h2⟩
      obtain ⟨hc, hd⟩ := hy z.im ⟨h3, h4⟩
      exact ⟨ha, hb, hc, hd⟩
    · right; right
      rw [Set.disjoint_left]
      intro z hz hz'
      rw [mem_dyadicSquare] at hz hz'
      obtain ⟨h1, h2, h3, h4⟩ := hz
      obtain ⟨h1', h2', h3', h4'⟩ := hz'
      exact hy z.im ⟨h3, h4, h3', h4'⟩
    · right; right
      rw [Set.disjoint_left]
      intro z hz hz'
      rw [mem_dyadicSquare] at hz hz'
      obtain ⟨h1, h2, h3, h4⟩ := hz
      obtain ⟨h1', h2', h3', h4'⟩ := hz'
      exact hx z.re ⟨h1, h2, h1', h2'⟩
    · right; right
      rw [Set.disjoint_left]
      intro z hz hz'
      rw [mem_dyadicSquare] at hz hz'
      obtain ⟨h1, h2, h3, h4⟩ := hz
      obtain ⟨h1', h2', h3', h4'⟩ := hz'
      exact hx z.re ⟨h1, h2, h1', h2'⟩
  · rcases coord n₂ n₁ hnle j₂.1 j₁.1 with hx | hx <;>
    rcases coord n₂ n₁ hnle j₂.2 j₁.2 with hy | hy
    · right; left
      intro z hz
      rw [mem_dyadicSquare] at hz ⊢
      obtain ⟨h1, h2, h3, h4⟩ := hz
      obtain ⟨ha, hb⟩ := hx z.re ⟨h1, h2⟩
      obtain ⟨hc, hd⟩ := hy z.im ⟨h3, h4⟩
      exact ⟨ha, hb, hc, hd⟩
    · right; right
      rw [Set.disjoint_left]
      intro z hz hz'
      rw [mem_dyadicSquare] at hz hz'
      obtain ⟨h1, h2, h3, h4⟩ := hz
      obtain ⟨h1', h2', h3', h4'⟩ := hz'
      exact hy z.im ⟨h3', h4', h3, h4⟩
    · right; right
      rw [Set.disjoint_left]
      intro z hz hz'
      rw [mem_dyadicSquare] at hz hz'
      obtain ⟨h1, h2, h3, h4⟩ := hz
      obtain ⟨h1', h2', h3', h4'⟩ := hz'
      exact hx z.re ⟨h1', h2', h1, h2⟩
    · right; right
      rw [Set.disjoint_left]
      intro z hz hz'
      rw [mem_dyadicSquare] at hz hz'
      obtain ⟨h1, h2, h3, h4⟩ := hz
      obtain ⟨h1', h2', h3', h4'⟩ := hz'
      exact hx z.re ⟨h1', h2', h1, h2⟩

/-- The index of the unique generation-`(n+1)` dyadic square (the *parent*) containing the
generation-`n` square of index `j`. -/
def dyadicParent (j : ℤ × ℤ) : ℤ × ℤ :=
  (Int.fdiv j.1 2, Int.fdiv j.2 2)

/-- A dyadic square is contained in its parent (one generation coarser). -/
theorem dyadicSquare_subset_parent (n : ℤ) (j : ℤ × ℤ) :
    dyadicSquare n j ⊆ dyadicSquare (n + 1) (dyadicParent j) := by
  have hpos : (0:ℝ) < (2:ℝ) ^ n := zpow_pos (by norm_num) n
  have hstep : (2:ℝ)^(n+1) = (2:ℝ)^n * 2 := by
    rw [zpow_add_one₀ (by norm_num)]
  intro z hz
  rw [mem_dyadicSquare] at hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  rw [mem_dyadicSquare]
  simp only [dyadicParent]
  have coord : ∀ (a : ℤ) (x : ℝ), (2:ℝ)^n * a ≤ x → x < (2:ℝ)^n * (a+1) →
      (2:ℝ)^(n+1) * (Int.fdiv a 2 : ℝ) ≤ x ∧ x < (2:ℝ)^(n+1) * ((Int.fdiv a 2 : ℝ) + 1) := by
    intro a x hx1 hx2
    have hsplit : 2 * Int.fdiv a 2 + Int.fmod a 2 = a := Int.mul_fdiv_add_fmod a 2
    have hfmnn : 0 ≤ Int.fmod a 2 := Int.fmod_nonneg_of_pos a (by norm_num)
    have hfmlt : Int.fmod a 2 < 2 := Int.fmod_lt_of_pos a (by norm_num)
    have hle : 2 * Int.fdiv a 2 ≤ a := by omega
    have hlt : a < 2 * Int.fdiv a 2 + 2 := by omega
    constructor
    · have heq1 : (2:ℝ)^(n+1) * (Int.fdiv a 2 : ℝ) = (2:ℝ)^n * (2 * (Int.fdiv a 2 : ℝ)) := by
        rw [hstep]; ring
      rw [heq1]
      have hle' : (2:ℝ)^n * (2 * (Int.fdiv a 2 : ℝ)) ≤ (2:ℝ)^n * a := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hpos)
        have hc : (2 * (Int.fdiv a 2 : ℝ)) = ((2 * Int.fdiv a 2 : ℤ) : ℝ) := by push_cast; ring
        rw [hc]
        exact_mod_cast hle
      linarith
    · have heq2 : (2:ℝ)^(n+1) * ((Int.fdiv a 2 : ℝ) + 1)
          = (2:ℝ)^n * (2 * (Int.fdiv a 2 : ℝ) + 2) := by
        rw [hstep]; ring
      rw [heq2]
      have hle' : (2:ℝ)^n * ((a:ℝ)+1) ≤ (2:ℝ)^n * (2 * (Int.fdiv a 2 : ℝ) + 2) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hpos)
        have hc : (2 * (Int.fdiv a 2 : ℝ) + 2) = ((2 * Int.fdiv a 2 + 2 : ℤ) : ℝ) := by
          push_cast; ring
        rw [hc]
        have hac : ((a:ℝ)+1) = ((a + 1 : ℤ):ℝ) := by push_cast; ring
        rw [hac]
        have : a + 1 ≤ 2 * Int.fdiv a 2 + 2 := by omega
        exact_mod_cast this
      linarith
  obtain ⟨ha1, ha2⟩ := coord j.1 z.re h1 h2
  obtain ⟨hb1, hb2⟩ := coord j.2 z.im h3 h4
  exact ⟨ha1, ha2, hb1, hb2⟩

/-- For every generation `n`, the dyadic squares of that generation are pairwise disjoint. -/
theorem dyadicSquare_pairwise_disjoint (n : ℤ) :
    Pairwise (Function.onFun Disjoint (dyadicSquare n)) := by
  have hpos : (0:ℝ) < (2:ℝ) ^ n := zpow_pos (by norm_num) n
  intro j j' hjj'
  simp only [Function.onFun, Set.disjoint_left]
  intro z hz hz'
  rw [mem_dyadicSquare] at hz hz'
  obtain ⟨h1, h2, h3, h4⟩ := hz
  obtain ⟨h1', h2', h3', h4'⟩ := hz'
  have key : ∀ (a b : ℤ) (x : ℝ), a ≠ b →
      ¬ ((2:ℝ)^n * a ≤ x ∧ x < (2:ℝ)^n * (a+1) ∧
         (2:ℝ)^n * b ≤ x ∧ x < (2:ℝ)^n * (b+1)) := by
    intro a b x hab
    rintro ⟨ha1, ha2, hb1, hb2⟩
    rcases lt_or_gt_of_ne hab with h | h
    · have hb : a + 1 ≤ b := by omega
      have : (2:ℝ)^n * (a+1) ≤ (2:ℝ)^n * b := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hpos)
        exact_mod_cast hb
      linarith
    · have hb : b + 1 ≤ a := by omega
      have : (2:ℝ)^n * (b+1) ≤ (2:ℝ)^n * a := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hpos)
        exact_mod_cast hb
      linarith
  by_cases hc1 : j.1 = j'.1
  · have hc2 : j.2 ≠ j'.2 := by
      intro h; exact hjj' (Prod.ext hc1 h)
    exact key j.2 j'.2 z.im hc2 ⟨h3, h4, h3', h4'⟩
  · exact key j.1 j'.1 z.re hc1 ⟨h1, h2, h1', h2'⟩

/-- For every generation `n`, the dyadic squares of that generation cover `ℂ`. -/
theorem iUnion_dyadicSquare (n : ℤ) :
    ⋃ j : ℤ × ℤ, dyadicSquare n j = Set.univ := by
  have hpos : (0:ℝ) < (2:ℝ) ^ n := zpow_pos (by norm_num) n
  rw [Set.eq_univ_iff_forall]
  intro z
  rw [Set.mem_iUnion]
  refine ⟨(⌊z.re / (2:ℝ)^n⌋, ⌊z.im / (2:ℝ)^n⌋), ?_⟩
  rw [mem_dyadicSquare]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hfl := Int.floor_le (z.re / (2:ℝ)^n)
    rw [le_div_iff₀ hpos] at hfl
    calc (2:ℝ)^n * (⌊z.re / (2:ℝ)^n⌋ : ℝ) = (⌊z.re / (2:ℝ)^n⌋ : ℝ) * (2:ℝ)^n := by ring
    _ ≤ z.re := hfl
  · have hfl := Int.lt_floor_add_one (z.re / (2:ℝ)^n)
    rw [div_lt_iff₀ hpos] at hfl
    calc z.re < ((⌊z.re / (2:ℝ)^n⌋ : ℝ) + 1) * (2:ℝ)^n := hfl
    _ = (2:ℝ)^n * ((⌊z.re / (2:ℝ)^n⌋ : ℝ) + 1) := by ring
  · have hfl := Int.floor_le (z.im / (2:ℝ)^n)
    rw [le_div_iff₀ hpos] at hfl
    calc (2:ℝ)^n * (⌊z.im / (2:ℝ)^n⌋ : ℝ) = (⌊z.im / (2:ℝ)^n⌋ : ℝ) * (2:ℝ)^n := by ring
    _ ≤ z.im := hfl
  · have hfl := Int.lt_floor_add_one (z.im / (2:ℝ)^n)
    rw [div_lt_iff₀ hpos] at hfl
    calc z.im < ((⌊z.im / (2:ℝ)^n⌋ : ℝ) + 1) * (2:ℝ)^n := hfl
    _ = (2:ℝ)^n * ((⌊z.im / (2:ℝ)^n⌋ : ℝ) + 1) := by ring

/-- The Euclidean centre of the generation-`n`, index-`j` dyadic square. -/
noncomputable def dyadicCenter (n : ℤ) (j : ℤ × ℤ) : ℂ :=
  { re := (2 : ℝ) ^ n * (j.1 : ℝ) + (2 : ℝ) ^ n / 2
    im := (2 : ℝ) ^ n * (j.2 : ℝ) + (2 : ℝ) ^ n / 2 }

/-- A dyadic square sits inside the ball about its centre of radius its side length (the
circumscribed ball has radius `2^n/√2 < 2^n`).  Together with `ball_subset_dyadicSquare`
this is the square/ball comparability that transfers a metric-ball reverse-Hölder
hypothesis onto the dyadic squares.

*(Note: an arbitrary ball is **not** contained in a single dyadic square of comparable
size — a ball straddling a grid line meets several squares — so the transfer goes through
this centre-based comparability, not a ball-in-square sandwich.)* -/
theorem dyadicSquare_subset_ball (n : ℤ) (j : ℤ × ℤ) :
    dyadicSquare n j ⊆ Metric.ball (dyadicCenter n j) ((2 : ℝ) ^ n) := by
  have hpos : (0:ℝ) < (2:ℝ) ^ n := zpow_pos (by norm_num) n
  set s : ℝ := (2:ℝ) ^ n with hs
  intro z hz
  rw [mem_dyadicSquare] at hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  rw [Metric.mem_ball, Complex.dist_eq_re_im]
  -- centre coordinates reduce definitionally
  have hcre : (dyadicCenter n j).re = s * (j.1 : ℝ) + s / 2 := rfl
  have hcim : (dyadicCenter n j).im = s * (j.2 : ℝ) + s / 2 := rfl
  rw [hcre, hcim]
  -- per-coordinate two-sided bounds: |z.re - c.re| ≤ s/2 and |z.im - c.im| ≤ s/2
  have hre_lo : -(s / 2) ≤ z.re - (s * (j.1 : ℝ) + s / 2) := by linarith
  have hre_hi : z.re - (s * (j.1 : ℝ) + s / 2) ≤ s / 2 := by
    have : z.re < s * ((j.1 : ℝ) + 1) := h2
    nlinarith [this]
  have him_lo : -(s / 2) ≤ z.im - (s * (j.2 : ℝ) + s / 2) := by linarith
  have him_hi : z.im - (s * (j.2 : ℝ) + s / 2) ≤ s / 2 := by
    have : z.im < s * ((j.2 : ℝ) + 1) := h4
    nlinarith [this]
  -- each squared difference is ≤ (s/2)^2
  have hre_sq : (z.re - (s * (j.1 : ℝ) + s / 2)) ^ 2 ≤ (s / 2) ^ 2 := by
    have hh := abs_le.mpr ⟨hre_lo, hre_hi⟩
    nlinarith [hh, abs_nonneg (z.re - (s * (j.1 : ℝ) + s / 2)),
      sq_abs (z.re - (s * (j.1 : ℝ) + s / 2))]
  have him_sq : (z.im - (s * (j.2 : ℝ) + s / 2)) ^ 2 ≤ (s / 2) ^ 2 := by
    have hh := abs_le.mpr ⟨him_lo, him_hi⟩
    nlinarith [hh, abs_nonneg (z.im - (s * (j.2 : ℝ) + s / 2)),
      sq_abs (z.im - (s * (j.2 : ℝ) + s / 2))]
  rw [Real.sqrt_lt' hpos]
  -- sum of squares ≤ s^2/2 < s^2
  nlinarith [hre_sq, him_sq, hpos, sq_nonneg s]

/-- The ball about the centre of a dyadic square of radius half its side length (the
inscribed ball) is contained in the square. -/
theorem ball_subset_dyadicSquare (n : ℤ) (j : ℤ × ℤ) :
    Metric.ball (dyadicCenter n j) ((2 : ℝ) ^ n / 2) ⊆ dyadicSquare n j := by
  set s : ℝ := (2:ℝ) ^ n with hs
  intro z hz
  rw [Metric.mem_ball, Complex.dist_eq] at hz
  have hcre : (dyadicCenter n j).re = s * (j.1 : ℝ) + s / 2 := rfl
  have hcim : (dyadicCenter n j).im = s * (j.2 : ℝ) + s / 2 := rfl
  -- |z.re - c.re| ≤ ‖z - c‖ < s/2 and similarly for the imaginary part
  have hre : |z.re - (s * (j.1 : ℝ) + s / 2)| < s / 2 := by
    have h := Complex.abs_re_le_norm (z - dyadicCenter n j)
    rw [Complex.sub_re, hcre] at h
    exact lt_of_le_of_lt h hz
  have him : |z.im - (s * (j.2 : ℝ) + s / 2)| < s / 2 := by
    have h := Complex.abs_im_le_norm (z - dyadicCenter n j)
    rw [Complex.sub_im, hcim] at h
    exact lt_of_le_of_lt h hz
  rw [abs_lt] at hre him
  obtain ⟨hre1, hre2⟩ := hre
  obtain ⟨him1, him2⟩ := him
  rw [mem_dyadicSquare]
  refine ⟨by linarith, ?_, by linarith, ?_⟩
  · have : z.re < s * (j.1 : ℝ) + s := by linarith
    nlinarith [this]
  · have : z.im < s * (j.2 : ℝ) + s := by linarith
    nlinarith [this]

/-- The index `(⌊z.re / 2^m⌋, ⌊z.im / 2^m⌋)` of the unique generation-`m` dyadic square
containing `z`. -/
noncomputable def dyadicIndexAt (m : ℤ) (z : ℂ) : ℤ × ℤ :=
  (⌊z.re / (2 : ℝ) ^ m⌋, ⌊z.im / (2 : ℝ) ^ m⌋)

/-- `z` lies in the generation-`m` dyadic square selected by `dyadicIndexAt m z`. -/
theorem mem_dyadicSquare_dyadicIndexAt (m : ℤ) (z : ℂ) :
    z ∈ dyadicSquare m (dyadicIndexAt m z) := by
  have hpos : (0:ℝ) < (2:ℝ) ^ m := zpow_pos (by norm_num) m
  simp only [mem_dyadicSquare, dyadicIndexAt]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hfl := Int.floor_le (z.re / (2:ℝ)^m)
    rw [le_div_iff₀ hpos] at hfl
    calc (2:ℝ)^m * (⌊z.re / (2:ℝ)^m⌋ : ℝ) = (⌊z.re / (2:ℝ)^m⌋ : ℝ) * (2:ℝ)^m := by ring
    _ ≤ z.re := hfl
  · have hfl := Int.lt_floor_add_one (z.re / (2:ℝ)^m)
    rw [div_lt_iff₀ hpos] at hfl
    calc z.re < ((⌊z.re / (2:ℝ)^m⌋ : ℝ) + 1) * (2:ℝ)^m := hfl
    _ = (2:ℝ)^m * ((⌊z.re / (2:ℝ)^m⌋ : ℝ) + 1) := by ring
  · have hfl := Int.floor_le (z.im / (2:ℝ)^m)
    rw [le_div_iff₀ hpos] at hfl
    calc (2:ℝ)^m * (⌊z.im / (2:ℝ)^m⌋ : ℝ) = (⌊z.im / (2:ℝ)^m⌋ : ℝ) * (2:ℝ)^m := by ring
    _ ≤ z.im := hfl
  · have hfl := Int.lt_floor_add_one (z.im / (2:ℝ)^m)
    rw [div_lt_iff₀ hpos] at hfl
    calc z.im < ((⌊z.im / (2:ℝ)^m⌋ : ℝ) + 1) * (2:ℝ)^m := hfl
    _ = (2:ℝ)^m * ((⌊z.im / (2:ℝ)^m⌋ : ℝ) + 1) := by ring

end NoWanderingDomains
