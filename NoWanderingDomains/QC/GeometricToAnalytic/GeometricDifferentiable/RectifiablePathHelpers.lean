/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.GeometricToAnalytic.GeometricDifferentiable.PlaneSeparation

/-!
# Rectifiable-path helpers (Eilenberg-Harrold polygon and chain machinery)

The polygon / chain helpers underlying the Eilenberg-Harrold rectifiable-connectedness
construction.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal Real

namespace NoWanderingDomains

section RhoPotentialWitness

variable {f : ℂ → ℂ} {a b s t : ℝ} (hab : a < b) (hst : s < t) {ρ σ : ℂ → ℝ≥0∞}

section RectifiablePathHelpers

/-! ## Eilenberg-Harrold rectifiable-path construction (polygon + chain helpers, inlined) -/

/-- Clamp a real number into `[0,1]`. -/
noncomputable def clmp (τ : ℝ) : ℝ := max 0 (min 1 τ)

theorem clmp_mem (τ : ℝ) : clmp τ ∈ Icc (0 : ℝ) 1 := by
  unfold clmp
  refine ⟨le_max_left _ _, ?_⟩
  rw [max_le_iff]; exact ⟨by norm_num, min_le_left _ _⟩

theorem clmp_eq_self {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) : clmp τ = τ := by
  unfold clmp
  rw [min_eq_right hτ.2, max_eq_right hτ.1]

/-- Segment index for the parameter `τ` (with `n` segments): the index of the subinterval
`[k/n, (k+1)/n]` containing `clmp τ`, clamped to `{0, …, n-1}`. -/
noncomputable def polyIdx (n : ℕ) (τ : ℝ) : ℕ :=
  min (n - 1) ⌊(n : ℝ) * clmp τ⌋₊

theorem polyIdx_le_sub (n : ℕ) (τ : ℝ) : polyIdx n τ ≤ n - 1 := by
  unfold polyIdx; exact min_le_left _ _

theorem polyIdx_lt (n : ℕ) (hn : 1 ≤ n) (τ : ℝ) : polyIdx n τ < n := by
  have h := polyIdx_le_sub n τ; omega

/-- The polygonal path with `n` segments through the points `z 0, …, z n`. On the `i`-th
subinterval `[i/n, (i+1)/n]` it is the straight segment from `z i` to `z (i+1)`, and it is
clamped to be constant (`z 0` for `τ ≤ 0`, `z (last)` for `τ ≥ 1`) outside `[0,1]`. The successor
index is capped at `n` so that the definition typechecks unconditionally; for `n ≥ 1` (the only
case of interest) this cap is never active. -/
noncomputable def polyPath (n : ℕ) (z : Fin (n + 1) → ℂ) : ℝ → ℂ := fun τ =>
  AffineMap.lineMap (z ⟨polyIdx n τ, by
      have h := polyIdx_le_sub n τ; omega⟩)
    (z ⟨min n (polyIdx n τ + 1), by
      have h := polyIdx_le_sub n τ; omega⟩)
    ((n : ℝ) * clmp τ - (polyIdx n τ : ℝ))

/-- Generic congruence for `lineMap` on `ℂ`: equal endpoints (as `Fin`-values into `z`) and equal
scalar give equal value. This avoids dependent-`rw` motive issues. -/
theorem lineMap_z_congr {n : ℕ} (z : Fin (n + 1) → ℂ) {a b a' b' : ℕ}
    (ha : a < n + 1) (hb : b < n + 1) (ha' : a' < n + 1) (hb' : b' < n + 1)
    (haa : a = a') (hbb : b = b') {c c' : ℝ} (hc : c = c') :
    AffineMap.lineMap (z ⟨a, ha⟩) (z ⟨b, hb⟩) c
      = AffineMap.lineMap (z ⟨a', ha'⟩) (z ⟨b', hb'⟩) c' := by
  subst haa; subst hbb; subst hc; rfl

/-- On the `i`-th subinterval `[i/n, (i+1)/n]`, the polygonal path equals the straight segment
from `z i.castSucc` to `z i.succ`, reparametrized affinely. -/
theorem polyPath_eq_lineMap (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) (i : Fin n)
    {τ : ℝ} (hτ : τ ∈ Icc ((i : ℝ) / n) (((i : ℝ) + 1) / n)) :
    polyPath n z τ = AffineMap.lineMap (z i.castSucc) (z i.succ)
      ((n : ℝ) * τ - (i : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hτ1, hτ2⟩ := hτ
  have hiltn : (i : ℕ) < n := i.2
  have hi_le : (i : ℝ) + 1 ≤ n := by
    have : (i : ℕ) + 1 ≤ n := hiltn
    exact_mod_cast this
  have hτ01 : τ ∈ Icc (0 : ℝ) 1 := by
    refine ⟨le_trans ?_ hτ1, le_trans hτ2 ?_⟩
    · positivity
    · rw [div_le_one hnpos]; exact hi_le
  have hclmp : clmp τ = τ := clmp_eq_self hτ01
  have hlow : (i : ℝ) ≤ (n : ℝ) * τ := by
    have := (div_le_iff₀ hnpos).mp hτ1; linarith [this]
  have hhigh : (n : ℝ) * τ ≤ (i : ℝ) + 1 := by
    have := (le_div_iff₀ hnpos).mp hτ2; linarith [this]
  -- The two `Fin` endpoints of `z i.castSucc`, `z i.succ` as plain values:
  have hcs : (i.castSucc : ℕ) = (i : ℕ) := rfl
  have hsu : (i.succ : ℕ) = (i : ℕ) + 1 := rfl
  -- The target rewritten with explicit `Fin.mk` endpoints.
  have htarget : AffineMap.lineMap (z i.castSucc) (z i.succ) ((n : ℝ) * τ - (i : ℝ))
      = AffineMap.lineMap (z ⟨(i : ℕ), by omega⟩) (z ⟨(i : ℕ) + 1, by omega⟩)
          ((n : ℝ) * τ - (i : ℝ)) := by
    apply lineMap_z_congr <;> simp
  rw [htarget]
  by_cases hend : (n : ℝ) * τ = (i : ℝ) + 1
  · -- right endpoint
    have hfloor : ⌊(n : ℝ) * clmp τ⌋₊ = (i : ℕ) + 1 := by
      rw [hclmp, hend, show ((i : ℝ) + 1) = (((i : ℕ) + 1 : ℕ) : ℝ) by push_cast; ring]
      exact Nat.floor_natCast _
    have hidxval : polyIdx n τ = min (n - 1) ((i : ℕ) + 1) := by
      unfold polyIdx; rw [hfloor]
    change AffineMap.lineMap (z ⟨polyIdx n τ, _⟩) (z ⟨min n (polyIdx n τ + 1), _⟩)
          ((n : ℝ) * clmp τ - (polyIdx n τ : ℝ)) = _
    rcases Nat.lt_or_ge ((i : ℕ) + 1) n with hcase | hcase
    · -- i+1 < n : index = i+1, param 0; both equal z (i+1)
      have hidx : polyIdx n τ = (i : ℕ) + 1 := by rw [hidxval]; omega
      have hp0 : (n : ℝ) * clmp τ - (polyIdx n τ : ℝ) = 0 := by
        rw [hclmp, hidx, hend]; push_cast; ring
      have hp1 : (n : ℝ) * τ - (i : ℝ) = 1 := by rw [hend]; ring
      rw [hp1, AffineMap.lineMap_apply_one]
      rw [hp0, AffineMap.lineMap_apply_zero]
      exact congrArg z (Fin.ext (by simp [hidx]))
    · -- i is last: index = n-1 = i, param 1
      have hin : (i : ℕ) + 1 = n := by omega
      have hidx : polyIdx n τ = (i : ℕ) := by rw [hidxval]; omega
      have hp1 : (n : ℝ) * clmp τ - (polyIdx n τ : ℝ) = 1 := by
        rw [hclmp, hidx, hend]; ring
      have hp1' : (n : ℝ) * τ - (i : ℝ) = 1 := by rw [hend]; ring
      rw [hp1', AffineMap.lineMap_apply_one]
      rw [hp1, AffineMap.lineMap_apply_one]
      exact congrArg z (Fin.ext (by simp [hidx, hin]))
  · -- interior: n*τ < i+1, floor = i
    have hlt : (n : ℝ) * τ < (i : ℝ) + 1 := lt_of_le_of_ne hhigh hend
    have hfloor : ⌊(n : ℝ) * clmp τ⌋₊ = (i : ℕ) := by
      rw [hclmp, Nat.floor_eq_iff (le_trans (by positivity) hlow)]
      exact ⟨hlow, hlt⟩
    have hidx : polyIdx n τ = (i : ℕ) := by
      unfold polyIdx; rw [hfloor]; omega
    change AffineMap.lineMap (z ⟨polyIdx n τ, _⟩) (z ⟨min n (polyIdx n τ + 1), _⟩)
          ((n : ℝ) * clmp τ - (polyIdx n τ : ℝ)) = _
    apply lineMap_z_congr
    · exact hidx
    · rw [hidx]; omega
    · rw [hclmp, hidx]

/-- Continuity of the polygonal path on the `i`-th subinterval. -/
theorem polyPath_continuousOn_seg (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) (i : Fin n) :
    ContinuousOn (polyPath n z) (Icc ((i : ℝ) / n) (((i : ℝ) + 1) / n)) := by
  apply ContinuousOn.congr (f := fun τ => AffineMap.lineMap (z i.castSucc) (z i.succ)
      ((n : ℝ) * τ - (i : ℝ)))
  · apply Continuous.continuousOn
    exact (AffineMap.lineMap_continuous).comp (by fun_prop)
  · intro τ hτ
    exact polyPath_eq_lineMap n hn z i hτ

/-- Continuity of the polygonal path on `Icc 0 (m/n)`, by induction on `m ≤ n`. -/
theorem polyPath_continuousOn_initial (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) :
    ∀ m : ℕ, m ≤ n → ContinuousOn (polyPath n z) (Icc (0 : ℝ) ((m : ℝ) / n)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  intro m
  induction m with
  | zero =>
    intro _
    simp only [Nat.cast_zero, zero_div]
    exact (Set.subsingleton_Icc_of_ge le_rfl).continuousOn _
  | succ k ih =>
    intro hk
    have hk' : k ≤ n := by omega
    have hkn : (k : ℕ) < n := by omega
    have hsplit : Icc (0 : ℝ) (((k : ℝ) + 1) / n)
        = Icc (0 : ℝ) ((k : ℝ) / n) ∪ Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n) := by
      rw [Set.Icc_union_Icc_eq_Icc]
      · positivity
      · gcongr; linarith
    have hpush : ((↑(k + 1) : ℝ)) / n = ((k : ℝ) + 1) / n := by push_cast; ring
    rw [hpush, hsplit]
    refine ContinuousOn.union_of_isClosed (ih hk') ?_ isClosed_Icc isClosed_Icc
    -- second piece is segment i = k
    have := polyPath_continuousOn_seg n hn z ⟨k, hkn⟩
    simpa only [Fin.val_mk] using this

/-- The polygonal path is continuous on `Icc 0 1`. -/
theorem polyPath_continuousOn_unit (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) :
    ContinuousOn (polyPath n z) (Icc (0 : ℝ) 1) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have := polyPath_continuousOn_initial n hn z n le_rfl
  rwa [div_self (ne_of_gt hnpos)] at this

/-- For `τ ≤ 0` the polygonal path is the constant `z 0`. -/
theorem polyPath_of_nonpos (n : ℕ) (_hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) {τ : ℝ} (hτ : τ ≤ 0) :
    polyPath n z τ = z 0 := by
  have hclmp : clmp τ = 0 := by
    unfold clmp; rw [min_eq_right (by linarith), max_eq_left hτ]
  have hidx : polyIdx n τ = 0 := by
    unfold polyIdx; rw [hclmp, mul_zero, Nat.floor_zero, Nat.min_zero]
  change AffineMap.lineMap (z ⟨polyIdx n τ, _⟩) (z ⟨min n (polyIdx n τ + 1), _⟩)
      ((n : ℝ) * clmp τ - (polyIdx n τ : ℝ)) = z 0
  have hp0 : (n : ℝ) * clmp τ - (polyIdx n τ : ℝ) = 0 := by rw [hclmp, hidx]; simp
  rw [hp0, AffineMap.lineMap_apply_zero]
  exact congrArg z (Fin.ext (by simp [hidx]))

/-- For `τ ≥ 1` the polygonal path is the constant `z (Fin.last n)`. -/
theorem polyPath_of_one_le (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) {τ : ℝ} (hτ : 1 ≤ τ) :
    polyPath n z τ = z (Fin.last n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hclmp : clmp τ = 1 := by
    unfold clmp; rw [min_eq_left hτ, max_eq_right (by norm_num)]
  have hfloor : ⌊(n : ℝ) * clmp τ⌋₊ = n := by
    rw [hclmp, mul_one, Nat.floor_natCast]
  have hidx : polyIdx n τ = n - 1 := by
    unfold polyIdx; rw [hfloor]; omega
  change AffineMap.lineMap (z ⟨polyIdx n τ, _⟩) (z ⟨min n (polyIdx n τ + 1), _⟩)
      ((n : ℝ) * clmp τ - (polyIdx n τ : ℝ)) = z (Fin.last n)
  have hp1 : (n : ℝ) * clmp τ - (polyIdx n τ : ℝ) = 1 := by
    rw [hclmp, hidx, mul_one]
    have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; norm_num
    rw [this]; ring
  rw [hp1, AffineMap.lineMap_apply_one]
  exact congrArg z (Fin.ext (by simp only [Fin.val_last]; omega))

/-- `polyPath n z 0 = z 0`. -/
theorem polyPath_zero (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) :
    polyPath n z 0 = z 0 :=
  polyPath_of_nonpos n hn z le_rfl

/-- `polyPath n z 1 = z (Fin.last n)`. -/
theorem polyPath_one (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) :
    polyPath n z 1 = z (Fin.last n) :=
  polyPath_of_one_le n hn z le_rfl

/-- The polygonal path is continuous on all of `ℝ`. -/
theorem polyPath_continuous (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) :
    Continuous (polyPath n z) := by
  rw [← continuousOn_univ]
  have hcov : (univ : Set ℝ) = Iic 0 ∪ Icc (0 : ℝ) 1 ∪ Ici 1 := by
    ext x; simp only [mem_univ, mem_union, mem_Iic, mem_Icc, mem_Ici, true_iff]
    rcases le_or_gt x 0 with h | h
    · exact Or.inl (Or.inl h)
    · rcases le_or_gt x 1 with h1 | h1
      · exact Or.inl (Or.inr ⟨le_of_lt h, h1⟩)
      · exact Or.inr (le_of_lt h1)
  rw [hcov]
  refine ContinuousOn.union_of_isClosed (ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Iic
    isClosed_Icc) ?_ (isClosed_Iic.union isClosed_Icc) isClosed_Ici
  · -- on Iic 0 : constant z 0
    refine (continuousOn_const (c := z 0)).congr ?_
    intro x hx; exact polyPath_of_nonpos n hn z hx
  · exact polyPath_continuousOn_unit n hn z
  · -- on Ici 1 : constant z (last)
    refine (continuousOn_const (c := z (Fin.last n))).congr ?_
    intro x hx; exact polyPath_of_one_le n hn z hx

/-- The `eVariationOn` of a straight segment `lineMap a b` over `[0,1]` is exactly `edist a b`. -/
theorem eVariationOn_lineMap (a b : ℂ) :
    eVariationOn (AffineMap.lineMap a b : ℝ → ℂ) (Icc (0 : ℝ) 1) = edist a b := by
  apply le_antisymm
  · -- ≤ : lineMap is `nndist a b`-Lipschitz, variation of identity on [0,1] is `edist 0 1`.
    have hlip : LipschitzOnWith (nndist a b) (AffineMap.lineMap a b : ℝ → ℂ) (Icc (0 : ℝ) 1) :=
      (lipschitzWith_lineMap a b).lipschitzOnWith
    have hcomp : eVariationOn ((AffineMap.lineMap a b : ℝ → ℂ) ∘ (id : ℝ → ℝ)) (Icc (0 : ℝ) 1)
        ≤ (nndist a b : ℝ≥0∞) * eVariationOn (id : ℝ → ℝ) (Icc (0 : ℝ) 1) :=
      hlip.comp_eVariationOn_le (Set.mapsTo_id _)
    simp only [Function.comp_id] at hcomp
    refine hcomp.trans ?_
    -- eVariationOn id (Icc 0 1) = edist 0 1 = 1
    have hidvar : eVariationOn (id : ℝ → ℝ) (Icc (0 : ℝ) 1) = 1 := by
      -- `eVariationOn_id_Icc` : variation of `id` on `Icc 0 1` is `ofReal (1 - 0) = 1`.
      simp
    rw [hidvar, mul_one]
    rw [edist_nndist]
  · -- ≥ : edist of the two endpoints lineMap 0 = a, lineMap 1 = b is ≤ variation.
    have h := eVariationOn.edist_le (AffineMap.lineMap a b : ℝ → ℂ)
      (s := Icc (0:ℝ) 1) (x := 0) (y := 1) (by simp) (by simp)
    simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using h

/-- The variation of the polygonal path over the `i`-th subinterval equals the length of the
`i`-th edge. -/
theorem eVariationOn_polyPath_seg (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) (i : Fin n) :
    eVariationOn (polyPath n z) (Icc ((i : ℝ) / n) (((i : ℝ) + 1) / n))
      = edist (z i.castSucc) (z i.succ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set φ : ℝ → ℝ := fun τ => (n : ℝ) * τ - (i : ℝ) with hφdef
  -- polyPath = (lineMap (z cs) (z su)) ∘ φ on the subinterval.
  have hEq : EqOn (polyPath n z)
      ((AffineMap.lineMap (z i.castSucc) (z i.succ) : ℝ → ℂ) ∘ φ)
      (Icc ((i : ℝ) / n) (((i : ℝ) + 1) / n)) := by
    intro τ hτ
    simpa only [Function.comp_apply, hφdef] using polyPath_eq_lineMap n hn z i hτ
  rw [eVariationOn.congr hEq]
  -- φ is monotone on the subinterval.
  have hφmono : MonotoneOn φ (Icc ((i : ℝ) / n) (((i : ℝ) + 1) / n)) := by
    intro x _ y _ hxy
    simp only [hφdef]
    have := mul_le_mul_of_nonneg_left hxy (le_of_lt hnpos)
    linarith
  rw [eVariationOn.comp_eq_of_monotoneOn _ φ hφmono]
  -- image of φ over the subinterval is Icc 0 1.
  have hφcont : ContinuousOn φ (Icc ((i : ℝ) / n) (((i : ℝ) + 1) / n)) := by
    apply Continuous.continuousOn; simp only [hφdef]; fun_prop
  have hle : (i : ℝ) / n ≤ ((i : ℝ) + 1) / n := by gcongr; linarith
  have himg : φ '' Icc ((i : ℝ) / n) (((i : ℝ) + 1) / n) = Icc (0 : ℝ) 1 := by
    rw [hφcont.image_Icc_of_monotoneOn hle hφmono]
    have hndvd : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hl : φ ((i : ℝ) / n) = 0 := by
      simp only [hφdef]; field_simp; ring
    have hr : φ (((i : ℝ) + 1) / n) = 1 := by
      simp only [hφdef]; field_simp; ring
    rw [hl, hr]
  rw [himg, eVariationOn_lineMap]

/-- **The key variation bound.** The total variation of the polygonal path over `[0,1]` is
bounded by the sum of the lengths of its edges. -/
theorem eVariationOn_polyPath_le (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) :
    eVariationOn (polyPath n z) (Icc (0 : ℝ) 1)
      ≤ ∑ i : Fin n, edist (z i.castSucc) (z i.succ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set I : ℕ → ℝ := fun k => (k : ℝ) / n with hIdef
  have hImono : Monotone I := by
    intro a b hab
    simp only [hIdef]
    have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    gcongr
  -- `eVariationOn.sum'` : ∑ over subintervals = variation over [I 0, I n] = [0,1].
  have hsum := eVariationOn.sum' (polyPath n z) hImono (n := n)
  have hI0 : I 0 = 0 := by simp [hIdef]
  have hIn : I n = 1 := by simp only [hIdef]; rw [div_self (ne_of_gt hnpos)]
  rw [hI0, hIn] at hsum
  rw [← hsum]
  -- Each subinterval variation equals the corresponding edge length; reindex Fin n ↔ range n.
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => eVariationOn (polyPath n z) (Icc (I k) (I (k + 1))))]
  apply Finset.sum_le_sum
  intro i _
  have hIi : I (i : ℕ) = (i : ℝ) / n := rfl
  have hIi1 : I ((i : ℕ) + 1) = ((i : ℝ) + 1) / n := by
    simp only [hIdef]; push_cast; ring_nf
  rw [hIi, hIi1]
  exact le_of_eq (eVariationOn_polyPath_seg n hn z i)

/-- For `τ ∈ [0,1]`, the parameter lies in the subinterval indexed by `polyIdx n τ`. -/
theorem mem_seg_of_mem_unit (n : ℕ) (hn : 1 ≤ n) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    τ ∈ Icc ((polyIdx n τ : ℝ) / n) (((polyIdx n τ : ℝ) + 1) / n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hclmp : clmp τ = τ := clmp_eq_self hτ
  have hnτnn : (0 : ℝ) ≤ (n : ℝ) * τ := by
    have := hτ.1; positivity
  set k := polyIdx n τ with hk
  -- lower bound : k ≤ n·τ
  have hlow : (k : ℝ) ≤ (n : ℝ) * τ := by
    have hkle : k ≤ ⌊(n : ℝ) * τ⌋₊ := by
      rw [hk]; unfold polyIdx; rw [hclmp]; exact min_le_right _ _
    calc (k : ℝ) ≤ (⌊(n : ℝ) * τ⌋₊ : ℝ) := by exact_mod_cast hkle
      _ ≤ (n : ℝ) * τ := Nat.floor_le hnτnn
  -- upper bound (non-strict) : n·τ ≤ k+1
  have hhigh : (n : ℝ) * τ ≤ (k : ℝ) + 1 := by
    by_cases hcase : ⌊(n : ℝ) * τ⌋₊ ≤ n - 1
    · -- then k = ⌊n·τ⌋₊, use floor upper bound (strict, hence ≤)
      have hkeq : k = ⌊(n : ℝ) * τ⌋₊ := by
        rw [hk]; unfold polyIdx; rw [hclmp]; omega
      rw [hkeq]
      calc (n : ℝ) * τ ≤ (⌊(n : ℝ) * τ⌋₊ : ℝ) + 1 := le_of_lt (Nat.lt_floor_add_one _)
        _ = (⌊(n : ℝ) * τ⌋₊ : ℝ) + 1 := rfl
    · -- then k = n-1, and n·τ ≤ n = k+1 (since τ ≤ 1)
      have hkeq : k = n - 1 := by
        rw [hk]; unfold polyIdx; rw [hclmp]; omega
      have hk1 : (k : ℝ) + 1 = n := by
        rw [hkeq]
        have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; norm_num
        rw [this]; ring
      rw [hk1]
      nlinarith [hτ.2, hnpos]
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ hnpos]; linarith [hlow]
  · rw [le_div_iff₀ hnpos]; linarith [hhigh]

/-- The trace of the polygonal path lies on one of its edges: for `τ ∈ [0,1]` there is a segment
index `i : Fin n` with `polyPath n z τ ∈ segment ℝ (z i.castSucc) (z i.succ)`. -/
theorem polyPath_mem_segment (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) :
    ∃ i : Fin n, polyPath n z τ ∈ segment ℝ (z i.castSucc) (z i.succ) := by
  refine ⟨⟨polyIdx n τ, polyIdx_lt n hn τ⟩, ?_⟩
  have hmem := mem_seg_of_mem_unit n hn hτ
  rw [polyPath_eq_lineMap n hn z ⟨polyIdx n τ, polyIdx_lt n hn τ⟩ (by simpa using hmem)]
  -- the parameter lies in [0,1], so the point is on the segment.
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨h1, h2⟩ := hmem
  rw [div_le_iff₀ hnpos] at h1
  rw [le_div_iff₀ hnpos] at h2
  have hparam : (n : ℝ) * τ - ((⟨polyIdx n τ, polyIdx_lt n hn τ⟩ : Fin n) : ℝ)
      ∈ Icc (0 : ℝ) 1 := by
    rw [Set.mem_Icc, Fin.val_mk]; constructor <;> linarith
  rw [show segment ℝ (z (⟨polyIdx n τ, polyIdx_lt n hn τ⟩ : Fin n).castSucc)
        (z (⟨polyIdx n τ, polyIdx_lt n hn τ⟩ : Fin n).succ)
      = AffineMap.lineMap (z (⟨polyIdx n τ, polyIdx_lt n hn τ⟩ : Fin n).castSucc)
        (z (⟨polyIdx n τ, polyIdx_lt n hn τ⟩ : Fin n).succ) '' Icc (0 : ℝ) 1
      from segment_eq_image_lineMap ℝ _ _]
  exact mem_image_of_mem _ hparam

/-- **Distance to a vertex.** Given an upper bound `D` on all edge lengths, every point of the
polygon trace (for `τ ∈ [0,1]`) is within `D` of some vertex `z i`. -/
theorem polyPath_dist_vertex (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) {D : ℝ}
    (hD : ∀ i : Fin n, dist (z i.castSucc) (z i.succ) ≤ D) :
    ∀ τ ∈ Icc (0 : ℝ) 1, ∃ i : Fin (n + 1), dist (polyPath n z τ) (z i) ≤ D := by
  intro τ hτ
  refine ⟨(⟨polyIdx n τ, polyIdx_lt n hn τ⟩ : Fin n).castSucc, ?_⟩
  have hmem := mem_seg_of_mem_unit n hn hτ
  have hidxmem : τ ∈ Icc (((⟨polyIdx n τ, polyIdx_lt n hn τ⟩ : Fin n) : ℝ) / n)
      ((((⟨polyIdx n τ, polyIdx_lt n hn τ⟩ : Fin n) : ℝ) + 1) / n) := by simpa using hmem
  rw [polyPath_eq_lineMap n hn z ⟨polyIdx n τ, polyIdx_lt n hn τ⟩ hidxmem]
  -- distance from `lineMap a b t` to `a` is `‖t‖ * dist a b ≤ dist a b ≤ D`.
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨h1, h2⟩ := hmem
  rw [div_le_iff₀ hnpos] at h1
  rw [le_div_iff₀ hnpos] at h2
  set i : Fin n := ⟨polyIdx n τ, polyIdx_lt n hn τ⟩ with hi
  have ht0 : 0 ≤ (n : ℝ) * τ - ((i : ℕ) : ℝ) := by simp only [hi, Fin.val_mk]; linarith
  have ht1 : (n : ℝ) * τ - ((i : ℕ) : ℝ) ≤ 1 := by simp only [hi, Fin.val_mk]; linarith
  rw [dist_lineMap_left]
  have hnorm : ‖(n : ℝ) * τ - ((i : ℕ) : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht1
  calc ‖(n : ℝ) * τ - ((i : ℕ) : ℝ)‖ * dist (z i.castSucc) (z i.succ)
      ≤ 1 * dist (z i.castSucc) (z i.succ) :=
        mul_le_mul_of_nonneg_right hnorm dist_nonneg
    _ = dist (z i.castSucc) (z i.succ) := one_mul _
    _ ≤ D := hD i



/-- **ε-chain reachability from connectedness.**
`C` is a finite `ε`-cover of a preconnected `Γ` (every point of `Γ` within `ε` of some center),
with `C ⊆ Γ`. Then any two centers `a, b ∈ C` are joined by a chain of centers with consecutive
gaps `≤ 2ε` — i.e. they are related by the reflexive-transitive closure of the "edge" relation
`step z w := z ∈ C ∧ w ∈ C ∧ dist z w ≤ 2ε`. -/
theorem reachable_of_isCover_preconnected {Γ : Set ℂ} (hΓconn : IsPreconnected Γ)
    {ε : ℝ} (hε : 0 < ε) {C : Finset ℂ} (hCΓ : ↑C ⊆ Γ)
    (hcover : ∀ x ∈ Γ, ∃ z ∈ C, dist x z ≤ ε)
    {a b : ℂ} (ha : a ∈ C) (hb : b ∈ C) :
    Relation.ReflTransGen (fun z w => z ∈ C ∧ w ∈ C ∧ dist z w ≤ 2 * ε) a b := by
  classical
  set step : ℂ → ℂ → Prop := fun z w => z ∈ C ∧ w ∈ C ∧ dist z w ≤ 2 * ε with hstepdef
  -- Reachable set from `a` within `C`.
  set R : Finset ℂ := C.filter (fun w => Relation.ReflTransGen step a w) with hRdef
  -- `a ∈ R`.
  have haR : a ∈ R := by
    rw [hRdef, Finset.mem_filter]
    exact ⟨ha, Relation.ReflTransGen.refl⟩
  -- Reachable centers are in `C`.
  have hRsub : R ⊆ C := Finset.filter_subset _ _
  -- The two closed cover pieces.
  set t : Set ℂ := ⋃ z ∈ R, Metric.closedBall z ε with htdef
  set t' : Set ℂ := ⋃ z ∈ (C \ R), Metric.closedBall z ε with ht'def
  have htclosed : IsClosed t := by
    rw [htdef]
    exact Set.Finite.isClosed_biUnion R.finite_toSet (fun z _ => Metric.isClosed_closedBall)
  have ht'closed : IsClosed t' := by
    rw [ht'def]
    exact Set.Finite.isClosed_biUnion (C \ R).finite_toSet
      (fun z _ => Metric.isClosed_closedBall)
  -- Γ ⊆ t ∪ t'.
  have hcoveruni : Γ ⊆ t ∪ t' := by
    intro x hx
    obtain ⟨z, hzC, hxz⟩ := hcover x hx
    by_cases hzR : z ∈ R
    · left; rw [htdef]; simp only [Set.mem_iUnion]
      exact ⟨z, hzR, by rw [Metric.mem_closedBall]; exact hxz⟩
    · right; rw [ht'def]; simp only [Set.mem_iUnion]
      refine ⟨z, ?_, by rw [Metric.mem_closedBall]; exact hxz⟩
      rw [Finset.mem_sdiff]; exact ⟨hzC, hzR⟩
  -- Γ ∩ t nonempty (a ∈ Γ ∩ t).
  have hat : a ∈ Γ ∩ t := by
    refine ⟨hCΓ ha, ?_⟩
    rw [htdef]; simp only [Set.mem_iUnion]
    exact ⟨a, haR, by rw [Metric.mem_closedBall, dist_self]; exact le_of_lt hε⟩
  -- Main claim: `b ∈ R`.
  have hbR : b ∈ R := by
    by_contra hbR
    -- then `b ∈ Γ ∩ t'`.
    have hbt' : b ∈ Γ ∩ t' := by
      refine ⟨hCΓ hb, ?_⟩
      rw [ht'def]; simp only [Set.mem_iUnion]
      refine ⟨b, ?_, by rw [Metric.mem_closedBall, dist_self]; exact le_of_lt hε⟩
      rw [Finset.mem_sdiff]; exact ⟨hb, hbR⟩
    -- preconnectedness forces Γ ∩ (t ∩ t') nonempty.
    obtain ⟨x, hxΓ, hxt, hxt'⟩ :=
      (isPreconnected_closed_iff.mp hΓconn) t t' htclosed ht'closed hcoveruni ⟨a, hat⟩ ⟨b, hbt'⟩
    -- extract the two covering centers.
    rw [htdef] at hxt; simp only [Set.mem_iUnion] at hxt
    obtain ⟨z, hzR, hxz⟩ := hxt
    rw [ht'def] at hxt'; simp only [Set.mem_iUnion] at hxt'
    obtain ⟨w, hwCR, hxw⟩ := hxt'
    rw [Metric.mem_closedBall] at hxz hxw
    rw [Finset.mem_sdiff] at hwCR
    obtain ⟨hwC, hwR⟩ := hwCR
    -- `dist z w ≤ 2ε`, so there is an edge `z → w`, contradicting `w ∉ R`.
    have hzC : z ∈ C := hRsub hzR
    have hzw : dist z w ≤ 2 * ε := by
      calc dist z w ≤ dist z x + dist x w := dist_triangle z x w
        _ = dist x z + dist x w := by rw [dist_comm z x]
        _ ≤ ε + ε := add_le_add hxz hxw
        _ = 2 * ε := by ring
    -- `z ∈ R` means `ReflTransGen step a z`; extend by the edge to `w`.
    have hzreach : Relation.ReflTransGen step a z := by
      rw [hRdef, Finset.mem_filter] at hzR; exact hzR.2
    have hwreach : Relation.ReflTransGen step a w :=
      hzreach.tail ⟨hzC, hwC, hzw⟩
    have : w ∈ R := by rw [hRdef, Finset.mem_filter]; exact ⟨hwC, hwreach⟩
    exact hwR this
  rw [hRdef, Finset.mem_filter] at hbR
  exact hbR.2



/-- Loop-excision helper, phrased with a length bound `n` to enable strong induction.
Any `r`-chain `l` with `l.length ≤ n` can be replaced by a `Nodup` `r`-chain with the same
endpoints (head and last). Whenever the chain is not already duplicate-free, we excise a loop
`l[i] … l[j]` (with `i < j` and `l[i] = l[j]`), yielding a strictly shorter chain, and recurse. -/
theorem exists_nodup_isChain_of_isChain_aux {α : Type*}
    {r : α → α → Prop} :
    ∀ (n : ℕ) (l : List α) (hne : l ≠ []) (_hlen : l.length ≤ n) (_hc : l.IsChain r),
      ∃ l' : List α, ∃ (hne' : l' ≠ []),
        l'.head hne' = l.head hne ∧ l'.getLast hne' = l.getLast hne ∧
        l'.IsChain r ∧ l'.Nodup := by
  intro n
  induction n with
  | zero =>
    intro l hne hlen _hc
    exact absurd (Nat.le_zero.mp hlen) (by simpa [List.length_eq_zero_iff] using hne)
  | succ n ih =>
    intro l hne hlen hc
    by_cases hnodup : l.Nodup
    · exact ⟨l, hne, rfl, rfl, hc, hnodup⟩
    · -- extract a duplicate: indices `i < j`, `j < l.length`, `l[i] = l[j]`
      rw [List.nodup_iff_getElem?_ne_getElem?] at hnodup
      push Not at hnodup
      obtain ⟨i, j, hij, hjlen, hdup⟩ := hnodup
      have hilen : i < l.length := lt_trans hij hjlen
      -- turn the `getElem?` equality into a `getElem` equality
      have hdup' : l[i] = l[j] := by
        have := hdup
        rw [List.getElem?_eq_getElem hilen, List.getElem?_eq_getElem hjlen] at this
        exact Option.some.inj this
      -- the spliced list: keep `take (i+1)` then `drop (j+1)`
      set l' : List α := l.take (i + 1) ++ l.drop (j + 1) with hl'def
      -- `take (i+1)` is nonempty
      have htake_ne : l.take (i + 1) ≠ [] := by
        rw [← List.length_pos_iff_ne_nil, List.length_take]
        omega
      have hl'_ne : l' ≠ [] := by
        rw [hl'def]
        simp [htake_ne]
      -- `l'` is a chain via append-overlap at the duplicated element `l[i] = l[j]`
      have hchain' : l'.IsChain r := by
        have h1 : (l.take i ++ [l[i]]).IsChain r := by
          rw [← List.take_succ_eq_append_getElem hilen]
          exact hc.take (i + 1)
        have h2 : ([l[i]] ++ l.drop (j + 1)).IsChain r := by
          have : l.drop j = l[i] :: l.drop (j + 1) := by
            rw [List.drop_eq_getElem_cons hjlen, hdup']
          have hdj : (l.drop j).IsChain r := hc.drop j
          rw [this] at hdj
          simpa using hdj
        have hover := List.IsChain.append_overlap (l₁ := l.take i) (l₂ := [l[i]])
          (l₃ := l.drop (j + 1)) h1 h2 (by simp)
        rw [hl'def, List.take_succ_eq_append_getElem hilen]
        simpa using hover
      -- `l'` is strictly shorter than `l`
      have hlen' : l'.length < l.length := by
        rw [hl'def, List.length_append, List.length_take, List.length_drop]
        rw [Nat.min_eq_left (by omega)]
        omega
      have hlen'' : l'.length ≤ n := by omega
      -- head of `l'` equals head of `l`
      have hhead : l'.head hl'_ne = l.head hne := by
        have hstep : l'.head hl'_ne = (l.take (i + 1)).head htake_ne := by
          apply List.head_append_left
        rw [hstep, List.head_eq_getElem htake_ne, List.getElem_take, List.head_eq_getElem hne]
      -- getLast of `l'` equals getLast of `l`
      have hlast : l'.getLast hl'_ne = l.getLast hne := by
        by_cases hd : l.drop (j + 1) = []
        · -- drop is empty: `j + 1 = l.length`, so `l[j]` is the last element
          have hjlast : j + 1 = l.length := by
            have := List.drop_eq_nil_iff.mp hd
            omega
          have hstep : l'.getLast hl'_ne = (l.take (i + 1)).getLast htake_ne := by
            apply List.getLast_append_left (l' := l.drop (j + 1))
            exact hd
          -- the last element of `take (i+1) l` is `l[i] = l[j]`, which is `l.getLast`
          have htlen : (l.take (i + 1)).length = i + 1 := by
            rw [List.length_take]; omega
          rw [hstep, List.getLast_eq_getElem htake_ne, List.getElem_take,
            List.getLast_eq_getElem hne]
          have e1 : (l.take (i + 1)).length - 1 = i := by omega
          have e2 : l.length - 1 = j := by omega
          simp only [e1, e2]; exact hdup'
        · have hstep : l'.getLast hl'_ne = (l.drop (j + 1)).getLast hd := by
            apply List.getLast_append_of_ne_nil
          rw [hstep, List.getLast_drop, List.getLast_eq_getElem hne]
      -- recurse on the strictly shorter chain
      obtain ⟨l'', hne'', hh'', hl'', hc'', hnd''⟩ := ih l' hl'_ne hlen'' hchain'
      exact ⟨l'', hne'', by rw [hh'', hhead], by rw [hl'', hlast], hc'', hnd''⟩

/-- **Main theorem.** If `a` and `b` are related by the reflexive transitive closure of `r`,
then there is a *duplicate-free* `r`-chain from `a` to `b`. -/
theorem exists_nodup_isChain_of_reflTransGen {α : Type*}
    {r : α → α → Prop} {a b : α} (h : Relation.ReflTransGen r a b) :
    ∃ l : List α, ∃ (hl : l ≠ []), l.head hl = a ∧ l.getLast hl = b ∧
      l.IsChain r ∧ l.Nodup := by
  classical
  -- start from some (possibly looping) chain provided by Mathlib
  obtain ⟨l, hne, hc, hhead, hlast⟩ :=
    List.exists_isChain_ne_nil_of_relationReflTransGen h
  -- excise loops to obtain a `Nodup` chain with the same endpoints
  obtain ⟨l', hne', hh', hl', hc', hnd'⟩ :=
    exists_nodup_isChain_of_isChain_aux l.length l hne le_rfl hc
  exact ⟨l', hne', by rw [hh', hhead], by rw [hl', hlast], hc', hnd'⟩

/-- **Corollary.** If every `r`-step lands inside a finite set `C` containing `a` and `b`, and
`a` reaches `b` under `ReflTransGen r`, then there is a `Nodup`-free (hence length `≤ C.card`)
`r`-chain from `a` to `b` all of whose vertices lie in `C`. -/
theorem exists_nodup_isChain_subset_card {α : Type*}
    {r : α → α → Prop} {C : Finset α} {a b : α} (ha : a ∈ C) (_hb : b ∈ C)
    (hr : ∀ x y, r x y → y ∈ C)
    (h : Relation.ReflTransGen r a b) :
    ∃ l : List α, ∃ (hl : l ≠ []), l.head hl = a ∧ l.getLast hl = b ∧
      l.IsChain r ∧ (∀ x ∈ l, x ∈ C) ∧ l.length ≤ C.card := by
  classical
  obtain ⟨l, hl, hhead, hlast, hc, hnd⟩ := exists_nodup_isChain_of_reflTransGen h
  -- every element of `l` is in `C`: the head is `a ∈ C`, every other is an `r`-target
  have hmem : ∀ x ∈ l, x ∈ C := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · -- head element equals `a`
      subst hi0
      rw [List.head_eq_getElem hl] at hhead
      rw [hhead]; exact ha
    · -- `x = l[i]` with `i ≥ 1` is the `r`-target of `l[i-1]`
      have hidx : i - 1 + 1 = i := by omega
      have hstep : r l[i - 1] l[i] := by
        have h0 := hc.getElem (i - 1) (by omega)
        simp only [hidx] at h0
        exact h0
      exact hr _ _ hstep
  refine ⟨l, hl, hhead, hlast, hc, hmem, ?_⟩
  -- length bound: `Nodup` + all elements in `C` gives `l.toFinset ⊆ C`
  have hsub : l.toFinset ⊆ C := by
    intro x hx
    exact hmem x (List.mem_toFinset.mp hx)
  calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ C.card := Finset.card_le_card hsub

/-- **List → vertex sequence.** Given a nonempty list `L` of complex numbers that is a chain for
the relation `dist · · ≤ 2ε`, with all elements in `Γ`, with head `p` and last `q`, and with
length `≥ 2`, produce a `Fin (n+1) → ℂ` vertex sequence with all the bounds transferred. The number
of segments `n = L.length - 1`. -/
theorem exists_vertices_of_list {Γ : Set ℂ} {ε : ℝ} {p q : ℂ} (L : List ℂ)
    (hlen : 2 ≤ L.length)
    (hmem : ∀ x ∈ L, x ∈ Γ)
    (hchain : L.IsChain (fun z w => dist z w ≤ 2 * ε))
    (hhead : L.head? = some p)
    (hlast : L.getLast? = some q) :
    ∃ (n : ℕ) (z : Fin (n+1) → ℂ), 1 ≤ n ∧ n + 1 = L.length ∧ z 0 = p ∧ z (Fin.last n) = q ∧
      (∀ i : Fin (n+1), z i ∈ Γ) ∧
      (∀ i : Fin n, dist (z i.castSucc) (z i.succ) ≤ 2 * ε) := by
  -- `n := L.length - 1`, so `L.length = n + 1`.
  have hLne : L ≠ [] := by rintro rfl; simp at hlen
  set n : ℕ := L.length - 1 with hn
  have hLlen : L.length = n + 1 := by omega
  have hn1 : 1 ≤ n := by omega
  -- The vertex function: `z i := L[i]` (with the length cast).
  refine ⟨n, fun i => L[(i : ℕ)]'(by omega), hn1, by omega, ?_, ?_, ?_, ?_⟩
  · -- `z 0 = p`
    have : L[0]'(by omega) = p := by
      have hh : L.head? = some (L[0]'(by omega)) := by
        rw [List.head?_eq_getElem?]
        rw [List.getElem?_eq_getElem (by omega : 0 < L.length)]
      rw [hhead] at hh
      exact ((Option.some.injEq _ _).mp hh).symm
    simpa using this
  · -- `z (Fin.last n) = q`
    have : L[n]'(by omega) = q := by
      have hq' : L.getLast? = some (L[n]'(by omega)) := by
        rw [List.getLast?_eq_getLast_of_ne_nil hLne, List.getLast_eq_getElem hLne]
      rw [hlast] at hq'
      exact ((Option.some.injEq _ _).mp hq').symm
    simpa [Fin.val_last] using this
  · -- membership
    intro i
    exact hmem _ (List.getElem_mem _)
  · -- edge bound
    intro i
    have hbound : (fun j : Fin (n+1) => L[(j : ℕ)]'(by omega)) i.castSucc
        = L[(i : ℕ)]'(by omega) := by simp
    have hbound2 : (fun j : Fin (n+1) => L[(j : ℕ)]'(by omega)) i.succ
        = L[(i : ℕ) + 1]'(by omega) := by simp
    rw [hbound, hbound2]
    have hi1 : (i : ℕ) + 1 < L.length := by have := i.2; omega
    exact hchain.getElem (i : ℕ) hi1

theorem exists_polygon_in_thickening
    {Γ : Set ℂ} (hΓconn : IsPreconnected Γ) {ε : ℝ} (hε : 0 < ε)
    {C : Finset ℂ} (hCΓ : ↑C ⊆ Γ)
    (hcover : ∀ x ∈ Γ, ∃ z ∈ C, dist x z ≤ ε)
    {p q : ℂ} (hp : p ∈ Γ) (hq : q ∈ Γ)
    {zp zq : ℂ} (hzp : zp ∈ C) (hzq : zq ∈ C) (hpzp : dist p zp ≤ ε) (hqzq : dist q zq ≤ ε) :
    ∃ (n : ℕ) (z : Fin (n+1) → ℂ), 1 ≤ n ∧ n ≤ C.card + 1 ∧ z 0 = p ∧ z (Fin.last n) = q ∧
      (∀ i : Fin (n+1), z i ∈ Γ) ∧
      (∀ i : Fin n, dist (z i.castSucc) (z i.succ) ≤ 2 * ε) := by
  classical
  set step : ℂ → ℂ → Prop := fun z w => z ∈ C ∧ w ∈ C ∧ dist z w ≤ 2 * ε with hstepdef
  -- every `step` lands in `C`.
  have hstepC : ∀ x y, step x y → y ∈ C := fun x y h => h.2.1
  -- 1. reachability `zp ⇝ zq`.
  have hreach : Relation.ReflTransGen step zp zq :=
    reachable_of_isCover_preconnected hΓconn hε hCΓ hcover hzp hzq
  -- 2. extract a *Nodup* chain `mid` from `zp` to `zq`, with length `≤ C.card`.
  obtain ⟨mid, hmidne, hmidhead, hmidlast, hmidchain, hmidC, hmidcard⟩ :=
    exists_nodup_isChain_subset_card hzp hzq hstepC hreach
  -- The full vertex list.
  set vlist : List ℂ := p :: (mid ++ [q]) with hvdef
  have hvne : vlist ≠ [] := by simp [hvdef]
  -- length ≥ 2 and `vlist.length = mid.length + 2`.
  have hmidlenpos : 1 ≤ mid.length := List.length_pos_iff.mpr hmidne
  have hvlencalc : vlist.length = mid.length + 2 := by
    rw [hvdef]; simp
  have hvlen : 2 ≤ vlist.length := by omega
  -- membership : every element of `vlist` is in `Γ`.
  have hvmem : ∀ x ∈ vlist, x ∈ Γ := by
    intro x hx
    rw [hvdef, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hp
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hCΓ (hmidC x hx)
    · rw [List.mem_singleton] at hx; subst hx; exact hq
  -- chain for the metric relation `dist · · ≤ 2ε`.
  have hvchain : vlist.IsChain (fun z w => dist z w ≤ 2 * ε) := by
    -- chain on `mid` for the metric relation.
    have hmidmetric : mid.IsChain (fun z w => dist z w ≤ 2 * ε) :=
      hmidchain.imp (fun a b hab => hab.2.2)
    -- append `[q]` : need last of `mid` (= `zq`) within `2ε` of `q`.
    have happ : (mid ++ [q]).IsChain (fun z w => dist z w ≤ 2 * ε) := by
      rw [List.isChain_append]
      refine ⟨hmidmetric, List.isChain_singleton _, ?_⟩
      intro x hx y hy
      rw [List.getLast?_eq_getLast_of_ne_nil hmidne, Option.mem_some_iff] at hx
      rw [List.head?_singleton, Option.mem_some_iff] at hy
      rw [hmidlast] at hx
      subst hx; subst hy
      calc dist zq q = dist q zq := dist_comm zq q
        _ ≤ ε := hqzq
        _ ≤ 2 * ε := by linarith
    -- prepend `p` : `dist p zp ≤ ε ≤ 2ε`, head of `mid ++ [q]` is `zp`.
    refine happ.cons ?_
    intro y hy
    rw [List.head?_append_of_ne_nil _ hmidne] at hy
    rw [List.head?_eq_some_head hmidne, hmidhead, Option.mem_some_iff] at hy
    subst hy
    calc dist p zp ≤ ε := hpzp
      _ ≤ 2 * ε := by linarith
  -- head of `vlist` is `p`.
  have hvhead : vlist.head? = some p := by rw [hvdef, List.head?_cons]
  -- last of `vlist` is `q`.
  have hvlast : vlist.getLast? = some q := by
    rw [hvdef, List.getLast?_cons, List.getLast?_append_cons]
    rfl
  obtain ⟨n, z, hn1, hnlen, hz0, hzlast, hzmem, hzedge⟩ :=
    exists_vertices_of_list (Γ := Γ) (ε := ε) (p := p) (q := q) vlist
      hvlen hvmem hvchain hvhead hvlast
  refine ⟨n, z, hn1, ?_, hz0, hzlast, hzmem, hzedge⟩
  -- `n + 1 = vlist.length = mid.length + 2 ≤ C.card + 2`, so `n ≤ C.card + 1`.
  omega


end RectifiablePathHelpers

end RhoPotentialWitness

end NoWanderingDomains
