/-
Copyright (c) 2025 Francesco Nishanil Chotuck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck
-/
import ForMathlib.Besicovitch.Fibre
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Thin covers

Körner's *thin cover* condition (Lemma 2.4): a set has a thin cover at height `v` and
thickness `ε` if finitely many open boxes cover its part in the band `|height - v| ≤ ε`
while having small total cross-sectional volume at every height of the band.  The condition
is open in the Hausdorff metric, and it bounds the volume of every cross-sectional slice
through the band.

## Main definitions

* `HasThinCover P v ε` : the thin-cover condition.
* `thinCoverSet v ε` : the members of `kornerCompacts` with a thin cover at `(v, ε)`.

## Main results

* `isOpen_thinCoverSet` : the thin-cover condition is open.
* `HasThinCover.toReal_volume_hSlice_le` : a thin cover bounds slice volumes by
  `100 * 4 ^ n * ε`.

## References

* T. W. Körner, *Besicovitch via Baire*, Studia Math. 158 (2003), no. 1, 65–78.
-/

open Set Topology Metric Bornology TopologicalSpace MeasureTheory NNReal Filter

namespace Besicovitch

variable {n : ℕ}

/-! ## Open boxes and thin covers -/

/-- An open axis-parallel box in `Fin (n+1) → ℝ`: the cross-section coordinates `i` lie in
`Ioo (lo i) (hi i)`, and the height coordinate lies in `Ioo c d`.  Realised as the product
`Set.univ.pi` of the `Fin.snoc` family of intervals so that the ambient `IsOpen`,
`MeasurableSet` and volume API applies directly. -/
def openBox (lo hi : Fin n → ℝ) (c d : ℝ) : Set (Fin (n + 1) → ℝ) :=
  Set.univ.pi (Fin.snoc (fun i => Ioo (lo i) (hi i)) (Ioo c d))

/-- Characterisation of membership in an `openBox`. -/
@[simp] lemma mem_openBox {lo hi : Fin n → ℝ} {c d : ℝ} {p : Fin (n + 1) → ℝ} :
    p ∈ openBox lo hi c d ↔
      (∀ i, p i.castSucc ∈ Ioo (lo i) (hi i)) ∧ p (Fin.last n) ∈ Ioo c d := by
  simp only [openBox, Set.mem_univ_pi]
  refine ⟨fun hp => ⟨fun i => by simpa using hp i.castSucc, by simpa using hp (Fin.last n)⟩, ?_⟩
  rintro ⟨h1, h2⟩ j
  induction j using Fin.lastCases with
  | last => simpa using h2
  | cast i => simpa using h1 i

/-- An open box is open. -/
lemma isOpen_openBox {lo hi : Fin n → ℝ} {c d : ℝ} : IsOpen (openBox lo hi c d) := by
  refine isOpen_set_pi Set.finite_univ fun i _ => ?_
  induction i using Fin.lastCases <;> simp [isOpen_Ioo]

/-- An open box is measurable. -/
@[measurability] lemma measurableSet_openBox {lo hi : Fin n → ℝ} {c d : ℝ} :
    MeasurableSet (openBox lo hi c d) := by
  refine MeasurableSet.univ_pi fun i => ?_
  induction i using Fin.lastCases <;> simp [measurableSet_Ioo]

/-- The cross-sectional slice of an `openBox` at height `u`: the open cross-section box
if `u ∈ Ioo c d`, else empty. -/
lemma hSlice_openBox (lo hi : Fin n → ℝ) (c d u : ℝ) :
    hSlice (openBox lo hi c d) u =
      if u ∈ Ioo c d then {x | ∀ i, x i ∈ Ioo (lo i) (hi i)} else ∅ := by
  ext x
  simp only [mem_hSlice, mem_openBox, stripPoint_castSucc, stripPoint_last]
  split_ifs with hu
  · exact and_iff_left hu
  · exact iff_of_false (fun h => hu h.2) (notMem_empty x)

/-- Körner's **thin cover** condition at height `v`, thickness `ε` (Lemma 2.4, `n`-dimensional
form): finitely many open boxes cover the part of `P` in the band `|height - v| ≤ ε`, and at
every height of the band the boxes present there have total cross-sectional volume less than
`100 ε`. -/
def HasThinCover (P : Set (Fin (n + 1) → ℝ)) (v ε : ℝ) : Prop :=
  ∃ (N : ℕ) (lo hi : Fin N → Fin n → ℝ) (c d : Fin N → ℝ),
    (∀ j i, lo j i ≤ hi j i) ∧
    (∀ p ∈ P, |p (Fin.last n) - v| ≤ ε → ∃ j, p ∈ openBox (lo j) (hi j) (c j) (d j)) ∧
    (∀ y : ℝ, |y - v| ≤ ε →
      ∑ j, (Ioo (c j) (d j)).indicator (fun _ => ∏ i, (hi j i - lo j i)) y < 100 * 4 ^ n * ε)

/-- `𝒫(v, ε)` as a subset of `kornerCompacts`. -/
def thinCoverSet (v ε : ℝ) : Set (kornerCompacts (n := n)) :=
  {P | HasThinCover (P : Set (Fin (n + 1) → ℝ)) v ε}

/-- Membership in `thinCoverSet v ε` is having a thin cover at `(v, ε)`. -/
@[simp] lemma mem_thinCoverSet {v ε : ℝ} {P : kornerCompacts (n := n)} :
    P ∈ thinCoverSet v ε ↔ HasThinCover (P : Set (Fin (n + 1) → ℝ)) v ε := Iff.rfl

/-- The thin-cover condition is open in the Hausdorff metric. -/
private lemma isOpen_setOf_hasThinCover (v ε : ℝ) :
    IsOpen {K : NonemptyCompacts (Fin (n + 1) → ℝ) |
      HasThinCover (K : Set (Fin (n + 1) → ℝ)) v ε} := by
  rw [Metric.isOpen_iff]
  rintro K ⟨N, lo, hi, c, d, hab, hcov, hthin⟩
  set W : Set (Fin (n + 1) → ℝ) :=
    (⋃ j, openBox (lo j) (hi j) (c j) (d j)) ∪ {p | ε < |p (Fin.last n) - v|}
  have hWopen : IsOpen W :=
    (isOpen_iUnion fun _ => isOpen_openBox).union
      (isOpen_lt continuous_const (((continuous_apply _).sub continuous_const).abs))
  have hKW : (K : Set (Fin (n + 1) → ℝ)) ⊆ W := fun p hp =>
    (le_or_gt _ _).imp (fun hpv => mem_iUnion.2 (hcov p hp hpv)) id
  obtain ⟨δ, hδ, hsub⟩ := K.isCompact.exists_thickening_subset_open hWopen hKW
  refine ⟨δ, hδ, fun K' hK' => ?_⟩
  have hlt : hausdorffDist (K' : Set (Fin (n + 1) → ℝ)) (K : Set (Fin (n + 1) → ℝ)) < δ := by
    rw [← NonemptyCompacts.dist_eq]
    exact Metric.mem_ball.1 hK'
  have hK'W : (K' : Set (Fin (n + 1) → ℝ)) ⊆ W := by
    refine subset_trans (fun x hx => ?_) hsub
    rw [mem_thickening_iff_infDist_lt K.nonempty]
    have hfin : hausdorffEDist (K' : Set (Fin (n + 1) → ℝ)) (K : Set (Fin (n + 1) → ℝ)) ≠ ⊤ :=
      hausdorffEDist_ne_top_of_nonempty_of_bounded K'.nonempty K.nonempty
        K'.isCompact.isBounded K.isCompact.isBounded
    exact lt_of_le_of_lt (infDist_le_hausdorffDist_of_mem hx hfin) hlt
  refine ⟨N, lo, hi, c, d, hab, fun p hp hpv => ?_, hthin⟩
  rcases hK'W hp with h | h
  · exact mem_iUnion.1 h
  · exact absurd hpv (not_le.2 h)

/-- The set `thinCoverSet v ε` is open in `kornerCompacts`. -/
theorem isOpen_thinCoverSet (v ε : ℝ) : IsOpen (thinCoverSet (n := n) v ε) :=
  (isOpen_setOf_hasThinCover v ε).preimage continuous_subtype_val

/-- If `P` has a thin cover at `(v, ε)`, then every height slice within `ε` of `v` has
cross-sectional volume at most `100 * 4 ^ n * ε`. -/
lemma HasThinCover.toReal_volume_hSlice_le {P : Set (Fin (n+1) → ℝ)} {v ε u : ℝ}
    (h : HasThinCover P v ε) (hu : |u - v| ≤ ε) :
    (volume (hSlice P u)).toReal ≤ 100 * 4 ^ n * ε := by
  obtain ⟨N, lo, hi, c, d, hab, hcov, hthin⟩ := h
  -- Nonnegativity of each indicator term.
  have hind : ∀ j : Fin N,
      (0 : ℝ) ≤ (Ioo (c j) (d j)).indicator (fun _ ↦ ∏ i, (hi j i - lo j i)) u :=
    fun j ↦ Set.indicator_nonneg
      (fun _ _ ↦ Finset.prod_nonneg fun i _ ↦ sub_nonneg.2 (hab j i)) _
  -- The slice at height `u` is covered by the slices of the boxes.
  have hsub : hSlice P u ⊆
      ⋃ j, hSlice (openBox (lo j) (hi j) (c j) (d j)) u := fun x hx =>
    mem_iUnion.2 (hcov (stripPoint x u) hx (by rwa [stripPoint_last]))
  -- Volume of each slice bounded by its indicator ofReal.
  have hvol_each : ∀ j : Fin N,
      volume (hSlice (openBox (lo j) (hi j) (c j) (d j)) u)
        ≤ ENNReal.ofReal ((Ioo (c j) (d j)).indicator (fun _ ↦ ∏ i, (hi j i - lo j i)) u) := by
    intro j
    rw [hSlice_openBox]
    by_cases hj : u ∈ Ioo (c j) (d j)
    · rw [if_pos hj, Set.indicator_of_mem hj]
      have hset : {x : Fin n → ℝ | ∀ i, x i ∈ Ioo (lo j i) (hi j i)}
          = Set.univ.pi (fun i => Ioo (lo j i) (hi j i)) :=
        Set.ext fun _ => Set.mem_univ_pi.symm
      rw [hset, Real.volume_pi_Ioo,
        ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ sub_nonneg.2 (hab j i))]
    · rw [if_neg hj, Set.indicator_of_notMem hj, measure_empty, ENNReal.ofReal_zero]
  -- Aggregate the bound.
  have hbound : volume (hSlice P u)
      ≤ ENNReal.ofReal
          (∑ j, (Ioo (c j) (d j)).indicator (fun _ ↦ ∏ i, (hi j i - lo j i)) u) := by
    calc volume (hSlice P u)
        ≤ volume (⋃ j, hSlice (openBox (lo j) (hi j) (c j) (d j)) u) := measure_mono hsub
      _ ≤ ∑ j, volume (hSlice (openBox (lo j) (hi j) (c j) (d j)) u) :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ j, ENNReal.ofReal
            ((Ioo (c j) (d j)).indicator (fun _ ↦ ∏ i, (hi j i - lo j i)) u) :=
          Finset.sum_le_sum fun j _ ↦ hvol_each j
      _ = ENNReal.ofReal
            (∑ j, (Ioo (c j) (d j)).indicator (fun _ ↦ ∏ i, (hi j i - lo j i)) u) :=
          (ENNReal.ofReal_sum_of_nonneg fun j _ ↦ hind j).symm
  have h0 : (0 : ℝ) ≤ ∑ j, (Ioo (c j) (d j)).indicator (fun _ ↦ ∏ i, (hi j i - lo j i)) u :=
    Finset.sum_nonneg fun j _ ↦ hind j
  exact (ENNReal.toReal_le_of_le_ofReal h0 hbound).trans (hthin u hu).le

end Besicovitch
