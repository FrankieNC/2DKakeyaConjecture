/-
Copyright (c) 2025 Francesco Nishanil Chotuck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck, Bhavik Mehta
-/

import BesicovitchSet.KakeyaSet
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Kakeya in one and two dimensions

This file collects basic results and conjectural statements about Kakeya sets
in low dimensions.


## Main statements

* In one dimension, any Kakeya set has full Hausdorff dimension:
  `dimH K = 1`. (Section `Kakeya1D`.)

* We also formalise a key technical result required for the proof:
  `exists_Gδ_of_dimH`, which shows that any subset of `ℝⁿ` can be thickened to a
  `Gδ` set of the same Hausdorff dimension.

## References

TO DO
-/

open Set Topology Real NNReal MeasureTheory Measure Filter

namespace Kakeya1D

/-- Any Kakeya set in `ℝ` contains a closed unit‐length interval. -/
lemma kakeya_contains_unit_Icc {K : Set ℝ} (hK : IsKakeya K) :
    ∃ x₀, Icc x₀ (x₀ + 1) ⊆ K := by
  have := hK 1 (by simp)
  rcases this with ⟨x₀, hseg⟩
  exact ⟨x₀, by simpa using hseg⟩

/-- Any closed interval of length 1 has Hausdorff dimension 1. -/
lemma dimH_Icc_length_one (a : ℝ) :
    dimH (Icc a (a + 1)) = 1 := by
  have h : (interior (Icc a (a + 1))).Nonempty := by simp [interior_Icc]
  calc
    dimH (Icc a (a + 1)) = Module.finrank ℝ ℝ := Real.dimH_of_nonempty_interior h
    _ = 1 := by simp

/-- If a set contains some unit interval, then its `dimH ≥ 1`. -/
lemma dimH_of_contains_Icc {K : Set ℝ} {x₀} (h : Icc x₀ (x₀ + 1) ⊆ K) :
    1 ≤ dimH K := by
  calc
    1 = dimH (Icc x₀ (x₀ + 1)) := (dimH_Icc_length_one x₀).symm
    _ ≤ dimH K := dimH_mono h

/-- Any subset of `ℝ` has `dimH ≤ 1`. -/
lemma dimH_le_one_univ : ∀ (K : Set ℝ), dimH K ≤ 1 := fun K ↦ by
  calc
    dimH K ≤ dimH (univ : Set ℝ) := dimH_mono (subset_univ _)
    _ = Module.finrank ℝ ℝ := by simp [dimH_univ]
    _ = 1 := by simp

/-- Any Kakeya set in `ℝ` has full Hausdorff dimension. -/
theorem isKakeya.dimH_eq_one (K : Set ℝ) (hK : IsKakeya K) :
    dimH K = 1 := by
  rcases kakeya_contains_unit_Icc hK with ⟨x₀, hsub⟩
  exact le_antisymm (dimH_le_one_univ K) (dimH_of_contains_Icc hsub)

end Kakeya1D

namespace Kakeya2D

-- This result has been formalised by Bhavik Mehta in a private repository,
-- and will soon be added to Mathlib

/-- For any set `E` and any non-negative `s : ℝ`, there exists a `Gδ` set `G` containing `E`
with the same `s`-dimensional Hausdorff measure. -/
theorem exists_Gδ_superset_hausdorffMeasure_eq
    {X : Type*}
    [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {s : ℝ} (hs : 0 ≤ s) (E : Set X) :
    ∃ G : Set X, IsGδ G ∧ E ⊆ G ∧ μH[s] G = μH[s] E := by
  sorry

/-- A subset of `ℝⁿ` has finite Hausdorff dimension. -/
theorem dimH_lt_top {n : ℕ} {A : Set (Fin n → ℝ)} :
    dimH A < ⊤ := by
  calc
    dimH A ≤ dimH (Set.univ : Set (Fin n → ℝ)) := dimH_mono (by simp)
    _ = n := dimH_univ_pi_fin n
    _ < ⊤ := by simp

theorem dimH_ne_top {n : ℕ} {A : Set (Fin n → ℝ)} : dimH A ≠ ⊤ := by
  simpa using (lt_top_iff_ne_top).1 dimH_lt_top

/-- For any subset `A` of `ℝⁿ` there is a `Gδ`‐set `G` with `A ⊆ G` and `dimH G = dimH A`. -/
theorem exists_Gδ_of_dimH {n : ℕ} (A : Set (Fin n → ℝ)) :
    ∃ G : Set (Fin n → ℝ), IsGδ G ∧ A ⊆ G ∧ dimH G = dimH A := by
  generalize hA : dimH A = DA
  have : DA ≠ ⊤ := Ne.symm (ne_of_ne_of_eq (id (Ne.symm dimH_ne_top)) hA)
  lift DA to ℝ≥0 using this
  obtain ⟨φ, h₁φ, h₂φ, h₃φ⟩ := exists_seq_strictAnti_tendsto' (show (0 : ℝ≥0) < 1 by norm_num)
  have h₄φ : Tendsto φ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_mono_right (Set.range_subset_iff.2 (by simp_all)) (tendsto_nhdsWithin_range.2 h₃φ)
  choose G' hG'_Gδ subG' meas_eq' using
    fun k : ℕ ↦ exists_Gδ_superset_hausdorffMeasure_eq (coe_nonneg (DA + φ k)) A
  let G := ⋂ k, G' k
  have iGδ : IsGδ G := IsGδ.iInter fun k ↦ hG'_Gδ k
  have Asub : A ⊆ G := subset_iInter fun k ↦ subG' k
  have hge : dimH A ≤ dimH G := dimH_mono Asub
  have hle : dimH G ≤ dimH A := by
    apply dimH_le
    intro d' hd'
    by_contra! hgt
    have hd_pos : 0 < (d' : ℝ≥0) - DA := by aesop
    rw [Metric.tendsto_atTop] at h₃φ
    rcases h₃φ _ hd_pos with ⟨k, hφk_lt⟩
    generalize hD : DA + φ k = D
    specialize h₂φ k
    simp only [mem_Ioo] at h₂φ
    cases' h₂φ with hφk_gt_0 hφk_lt_1
    have hlt : DA < D := by
      linear_combination hD + hφk_gt_0
    have hμA : μH[D] A = 0 := by
      apply hausdorffMeasure_of_dimH_lt
      rw [hA]
      norm_cast
    have hμGk : μH[D] (G' k) = 0 := by
      rw [← hD, meas_eq', hD, hμA]
    have hmono : μH[d'] G ≤ μH[D] (G' k) := by
      calc
        μH[d'] G ≤ μH[d'] (G' k) := by
          apply measure_mono
          exact iInter_subset_of_subset k fun ⦃a⦄ a ↦ a
        _ ≤ μH[D] (G' k) := by
          apply hausdorffMeasure_mono
          apply le_of_lt
          rw [← hD]
          simp only [NNReal.coe_add]
          specialize hφk_lt k
          norm_cast
          simp only [ge_iff_le, le_refl, val_eq_coe, dist_lt_coe, nndist_zero_eq_val',
            forall_const] at hφk_lt
          rw [lt_tsub_iff_left] at hφk_lt
          exact hφk_lt
    have h0 : μH[d'] G = 0 := by
      have hbot : μH[d'] G ≤ 0 := by
        apply hmono.trans_eq
        exact hμGk
      exact le_bot_iff.1 hbot
    simp [h0] at hd'
  rw [← hA]
  exact ⟨G, iGδ, Asub, le_antisymm hle hge⟩

/-- If `A ⊆ ℝⁿ` has finite `s`-dimensional Hausdorff measure,
    then for any `k ≤ s` and any `k`-plane `W`, the slices
    `A ∩ (Wᗮ + x)` have finite `(s - k)`-measure for `μH[k]`-almost all `x ∈ W`. -/
theorem hausdorffMeasure_slicing
  (n : ℕ)
  (A : Set (EuclideanSpace ℝ (Fin n))) (hA : MeasurableSet A)
  (s : ℝ) (hs : μH[s] A < ⊤)
  (k : ℕ) (hks : (k : ℝ) ≤ s)
  (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hW : Module.finrank ℝ W = k)
  (direction : W) (x : W) :
  ∀ᵐ x ∂ (μH[(k : ℝ)]).restrict (W : Set (EuclideanSpace ℝ (Fin n))),
    μH[s - k] (A ∩ (AffineSubspace.mk' x W.orthogonal : Set _)) < ⊤ := by
  sorry

end Kakeya2D
