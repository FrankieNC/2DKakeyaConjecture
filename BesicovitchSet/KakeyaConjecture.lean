/-
Copyright (c) 2025 Francesco Nishanil Chotuck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck, Bhavik Mehta
-/

import BesicovitchSet.KakeyaSet
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Order.CompletePartialOrder

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

-/

open Set Topology Real NNReal ENNReal MeasureTheory Measure Filter EMetric MetricSpace Metric

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

-- The following lemmas were formalised by Bhavik Mehta as part of the proof of
-- `exists_Gδ_superset_hausdorffMeasure_eq`. At the time of writing they are not
-- yet included in Mathlib.

lemma le_of_forall_mul_le {a b : ℝ≥0∞} (h : ∀ ε : ℝ≥0, 1 < ε → a ≤ b * ε) : a ≤ b := by
  obtain rfl | ha := eq_or_ne a ⊤
  · have : b * 2 = ⊤ := by
      specialize h 2
      norm_num at h
      assumption
    by_contra! hb
    exact ENNReal.mul_ne_top hb.ne (by simp) this
  apply le_of_forall_pos_nnreal_lt
  intro r hr hra
  generalize hε : a / r = ε
  have hε' : ε ≠ ⊤ := by
    rw [← hε]
    exact (ENNReal.div_lt_top ha (by positivity)).ne
  lift ε to ℝ≥0 using hε'
  have hε' : 1 < ε := by
    suffices (1 : ℝ≥0∞) < ε by simpa
    rwa [← hε, ENNReal.lt_div_iff_mul_lt (by simp) (by simp), one_mul]
  have : a / ε = r := by
    rw [← hε, ENNReal.div_div_cancel _ ha]
    exact (hra.trans_le' (by simp)).ne'
  rw [← this]
  apply ENNReal.div_le_of_le_mul
  exact h ε hε'

variable {X : Type*} [EMetricSpace X]

/-- The infimum of `∑ diam (t n) ^ d` over all countable
covers `(t n)` of `S` by sets in `p` with `diam (t n) ≤ r`.-/
noncomputable def deltaHausdorffWith (p : Set (Set X)) (d : ℝ) (r : ℝ≥0∞) (S : Set X) : ℝ≥0∞ :=
  ⨅ (t : ℕ → Set X) (_ : S ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r) (_ : ∀ n, t n ∈ p),
    ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ d

lemma deltaHausdorffWith_antitone_prop {r : ℝ≥0∞} {d : ℝ} {S : Set X} :
    Antitone (deltaHausdorffWith · d r S) :=
  fun _ _ hp ↦ iInf₂_mono fun _ _ ↦ iInf₂_mono' fun hU' hU'' ↦ ⟨hU', fun n ↦ hp (hU'' n), le_rfl⟩

lemma deltaHausdorffWith_antitone {p : Set (Set X)} {d : ℝ} {S : Set X} :
    Antitone (deltaHausdorffWith p d · S) :=
  fun _ _ hr ↦ iInf₂_mono fun _ _ ↦ iInf₂_mono' fun hU' hU'' ↦
    ⟨fun n ↦ (hU' n).trans hr, hU'', le_rfl⟩

lemma iSup₂_nnreal_deltaHausdorffWith (p : Set (Set X)) (d : ℝ) (S : Set X) :
    ⨆ (r : ℝ≥0) (_ : 0 < r), deltaHausdorffWith p d r S =
      ⨆ (r : ℝ≥0∞) (_ : 0 < r), deltaHausdorffWith p d r S := by
  refine le_antisymm (iSup₂_mono' ?_) (iSup₂_mono' ?_)
  · intro r hr
    exact ⟨r, by simpa⟩
  · intro r hr
    obtain rfl | hr' := eq_or_ne r ⊤
    · refine ⟨1, by simp, ?_⟩
      apply deltaHausdorffWith_antitone
      simp
    lift r to ℝ≥0 using hr'
    exact ⟨r, by simpa using hr⟩

lemma exists_isOpen_diam {E : Set X} (hE : E.Nontrivial) {δ : ℝ≥0} (hδ : 1 < δ) :
    ∃ U, E ⊆ U ∧ IsOpen U ∧ ediam U ≤ δ * ediam E := by
  have hδ₀ : δ ≠ 0 := by positivity
  obtain hE | hne := eq_or_ne (ediam E) ⊤
  · use Set.univ
    simp [hE, hδ₀]
  lift ediam E to ℝ≥0 using hne with dE hdE
  have hdE' : 0 < dE := by rwa [← ediam_pos_iff, ← hdE, ENNReal.coe_pos] at hE
  let ε : ℝ≥0 := (δ - 1) / 2 * dE
  have hε : 0 < ε := by
    have : 0 < δ - 1 := by simpa
    positivity
  refine ⟨Metric.thickening ε E, Metric.self_subset_thickening (by simpa) _,
    Metric.isOpen_thickening, ?_⟩
  calc ediam (Metric.thickening ε E) ≤ ediam E + 2 * ε := Metric.ediam_thickening_le _
    _ = dE + 2 * ε := by rw [hdE]
    _ = dE + 2 * ↑((δ - 1) / 2 * dE) := rfl
  norm_cast
  rw [← mul_assoc, ← one_add_mul, mul_div_cancel₀ _ (by simp), add_tsub_cancel_of_le hδ.le]

lemma deltaHausdorffWith_isOpen (S : Set X) (d : ℝ) (r : ℝ≥0) (ε : ℝ≥0)
    (hr : 0 < r) (hε : 1 < ε) (hd : 0 ≤ d) :
    deltaHausdorffWith {U | IsOpen U} d (ε * r) S ≤ ε ^ d * deltaHausdorffWith Set.univ d r S := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ν hν h
  have hε₀ : ε ≠ 0 := by positivity
  simp only [deltaHausdorffWith, mul_iInf_of_ne (a := ε ^ d) (by simp [hε₀]) (by simp [hε₀]),
    iInf_add, ← ENNReal.tsum_mul_left, ENNReal.mul_iSup]
  refine iInf₂_mono' fun U hU ↦ ?_
  obtain ⟨ν', hν', h'ν'⟩ := ENNReal.exists_pos_sum_of_countable (ε := ν) (by simp [hν.ne']) ℕ
  have U' (n : ℕ) : ∃ V, U n ⊆ V ∧ IsOpen V ∧ (V.Nonempty → (U n).Nonempty) ∧
      (ediam V ≤ ε * ediam (U n) ∨ ediam (U n) = 0 ∧ ediam V ≤ min (ε * r) (ν' n ^ d⁻¹)) := by
    obtain h' | h' := (U n).eq_empty_or_nonempty
    · use ∅
      simp [h']
    obtain ⟨x, hx⟩ | h' := h'.exists_eq_singleton_or_nontrivial
    · refine ⟨eball x (min (ε * r) (ν' n ^ d⁻¹) / 2), ?_, ?_, by simp [hx], Or.inr ?_⟩
      · rw [hx, Set.singleton_subset_iff]
        apply mem_eball_self
        have : 0 < ν' n ^ d⁻¹ := NNReal.rpow_pos (hν' n)
        refine ENNReal.div_pos ?_ (by simp)
        positivity
      · exact isOpen_eball
      · simp only [hx, ediam_singleton, true_and]
        refine ediam_eball_le.trans_eq ?_
        rw [ENNReal.mul_div_cancel (by simp) (by simp)]
    obtain ⟨V, hV, hV', hV''⟩ := exists_isOpen_diam h' hε
    exact ⟨V, hV, hV', by simp [h'.nonempty], Or.inl hV''⟩
  choose V hUV hVopen hVne hVdiam using U'
  use V, hU.trans (Set.iUnion_mono hUV)
  refine iInf₂_mono' fun h'U h''U ↦ ?_
  have hVdiam_r (n : ℕ) : ediam (V n) ≤ ε * r := by
    obtain h | h := hVdiam n
    · exact h.trans (mul_le_mul_right (h'U n) ε)
    · exact h.2.trans (by simp)
  use hVdiam_r, hVopen
  have h₁ : ∑' (i : ℕ), ((⨆ (_ : (U i).Nonempty), ε ^ d * ediam (U i) ^ d) + ν' i) ≤
      (∑' (i : ℕ), ⨆ (_ : (U i).Nonempty), ε ^ d * ediam (U i) ^ d) + ν := by
    rw [ENNReal.tsum_add]
    gcongr
  refine h₁.trans' <| ENNReal.tsum_le_tsum fun n ↦ ?_
  simp only [iSup_le_iff]
  intro hn
  simp only [hVne _ hn, iSup_pos]
  obtain h | ⟨h, h'⟩ := hVdiam n
  · calc ediam (V n) ^ d ≤ (ε * ediam (U n)) ^ d := by gcongr
      _ = ε ^ d * ediam (U n) ^ d := by rw [ENNReal.mul_rpow_of_nonneg _ _ hd]
      _ ≤ _ := le_self_add
  · obtain rfl | hd := hd.eq_or_lt
    · simp
    calc ediam (V n) ^ d ≤ (min (ε * r) (ν' n ^ d⁻¹)) ^ d := by gcongr
      _ ≤ (ν' n ^ d⁻¹ : ℝ≥0) ^ d := by gcongr; exact min_le_right _ _
      _ = ν' n := by
        rw [ENNReal.coe_rpow_of_nonneg, ENNReal.rpow_inv_rpow hd.ne']
        positivity
      _ ≤ _ := le_add_self

variable [MeasurableSpace X] [BorelSpace X]

lemma hausdorffMeasure_eq_iSup₂_deltaHausdorffWith {d : ℝ} {S : Set X} :
    μH[d] S = ⨆ (r : ℝ≥0∞) (_ : 0 < r), deltaHausdorffWith Set.univ d r S := by
  simp only [hausdorffMeasure_apply, deltaHausdorffWith, Set.mem_univ, implies_true, iInf_pos]

lemma hausdorffMeasure_eq_iSup₂_deltaHausdorffWith_isOpen {d : ℝ} {S : Set X} (hd : 0 ≤ d) :
    μH[d] S = ⨆ (r : ℝ≥0∞) (_ : 0 < r), deltaHausdorffWith {U | IsOpen U} d r S := by
  rw [hausdorffMeasure_eq_iSup₂_deltaHausdorffWith,
    ← iSup₂_nnreal_deltaHausdorffWith, ← iSup₂_nnreal_deltaHausdorffWith]
  refine le_antisymm (iSup₂_mono fun r hr ↦ deltaHausdorffWith_antitone_prop (by simp)) ?_
  obtain rfl | hd := hd.eq_or_lt
  · refine iSup₂_mono' fun r hr ↦ ?_
    refine ⟨r / 2, by positivity, ?_⟩
    convert deltaHausdorffWith_isOpen S 0 (r / 2) 2 (by positivity) (by simp) le_rfl using 2
    · norm_cast
      rw [mul_div_cancel₀ _ (by simp)]
    simp
  apply le_of_forall_mul_le
  intro ε hε
  rw [mul_comm]
  simp only [ENNReal.mul_iSup]
  refine iSup₂_mono' fun r hr ↦ ?_
  have h₂ : 0 < ε ^ (-d⁻¹) * r := mul_pos (NNReal.rpow_pos (by positivity)) hr
  use ε ^ (-d⁻¹) * r, h₂
  convert deltaHausdorffWith_isOpen S d _ (ε ^ d⁻¹) h₂ (NNReal.one_lt_rpow hε (by positivity)) hd.le
  · norm_cast
    rw [← mul_assoc, ← NNReal.rpow_add (by positivity)]
    simp
  · rw [ENNReal.coe_rpow_of_nonneg _ (by positivity), ENNReal.rpow_inv_rpow hd.ne']

lemma tendsto_deltaHausdorffWith_isOpen_hausdorffMeasure {d : ℝ} {S : Set X} (hd : 0 ≤ d) :
    Tendsto (deltaHausdorffWith {U | IsOpen U} d · S) (𝓝[>] 0) (𝓝 (μH[d] S)) := by
  rw [hausdorffMeasure_eq_iSup₂_deltaHausdorffWith_isOpen hd]
  convert deltaHausdorffWith_antitone.tendsto_nhdsGT 0
  rw [sSup_image]
  simp

/-- For any set `E` and any non-negative `s : ℝ`, there exists a `Gδ` set `G` containing `E`
with the same `s`-dimensional Hausdorff measure. -/
theorem exists_Gδ_superset_hausdorffMeasure_eq
    {X : Type*}
    [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {s : ℝ} (hs : 0 ≤ s) (E : Set X) :
    ∃ G : Set X, IsGδ G ∧ E ⊆ G ∧ μH[s] G = μH[s] E := by
  have h₁ : μH[s] E = ⊤ ∨ μH[s] E < ⊤ := by rw [← le_iff_eq_or_lt]; simp
  obtain h₁ | h₁ := h₁
  · exact ⟨Set.univ, by simp, by simp, le_antisymm (by rw [h₁]; simp) (measure_mono (by simp))⟩
  obtain ⟨φ, h₁φ, h₂φ, h₃φ⟩ := exists_seq_strictAnti_tendsto' (show (0 : ℝ≥0∞) < 1 by norm_num)
  have h₄φ : Tendsto φ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_mono_right
      (Set.range_subset_iff.2 (by simp_all)) (tendsto_nhdsWithin_range.2 h₃φ)
  have hc (i : ℕ) : ∃ (U : ℕ → Set X) (hU : E ⊆ ⋃ j, U j)
      (hU' : ∀ j, ediam (U j) ≤ φ i) (hU'' : ∀ j, IsOpen (U j)),
      ∑' j, ⨆ (_ : (U j).Nonempty), ediam (U j) ^ s <
        deltaHausdorffWith {U | IsOpen U} s (φ i) E + φ i := by
    have h₂ :
        deltaHausdorffWith {U | IsOpen U} s (φ i) E <
          deltaHausdorffWith {U | IsOpen U} s (φ i) E + φ i := by
      apply ENNReal.lt_add_right _ _
      · rw [← lt_top_iff_ne_top]
        refine h₁.trans_le' ?_
        rw [hausdorffMeasure_eq_iSup₂_deltaHausdorffWith_isOpen hs]
        exact le_iSup₂ (α := ℝ≥0∞) _ (by simp_all)
      · simp only [ne_eq, (h₂φ i).1.ne', not_false_eq_true]
    conv_lhs at h₂ =>
      simp only [deltaHausdorffWith]
    simp only [iInf_lt_iff, Set.mem_setOf_eq] at h₂
    exact h₂
  choose U hCov hDiam hOpen hU using hc
  let G : Set _ := ⋂ i, ⋃ j, U i j
  have hEG : E ⊆ G := Set.subset_iInter hCov
  have h₁ (i : ℕ) : deltaHausdorffWith {U | IsOpen U} s (φ i) G <
      deltaHausdorffWith {U | IsOpen U} s (φ i) E + φ i := by
    rw [deltaHausdorffWith]
    simp only [iInf_lt_iff]
    exact ⟨U i, Set.iInter_subset _ _, hDiam i, hOpen i, hU i⟩
  refine ⟨G, ?_, hEG, ?_⟩
  · apply IsGδ.iInter_of_isOpen
    intro i
    apply isOpen_iUnion
    intro j
    exact hOpen i j
  refine le_antisymm ?_ (measure_mono hEG)
  simpa using le_of_tendsto_of_tendsto'
    ((tendsto_deltaHausdorffWith_isOpen_hausdorffMeasure hs).comp h₄φ)
    (((tendsto_deltaHausdorffWith_isOpen_hausdorffMeasure hs).comp h₄φ).add h₃φ) (fun i ↦ (h₁ i).le)

-- What follows is the contribution of Francesco Chotuck.

theorem dimH_eq_of_Gδ_superset {n : ℕ} (A : Set (Fin n → ℝ)) (DA : ℝ≥0) (hA : dimH A = ↑DA)
    (φ : ℕ → ℝ≥0) (h₂φ : ∀ (n : ℕ), φ n ∈ Ioo 0 1) (h₃φ : Tendsto φ atTop (𝓝 0))
    (G' : ℕ → Set (Fin n → ℝ)) (meas_eq' : ∀ (k : ℕ), μH[↑(DA + φ k)] (G' k) = μH[↑(DA + φ k)] A) :
    let G := ⋂ k, G' k;
    IsGδ G → A ⊆ G → dimH A ≤ dimH G → dimH G ≤ dimH A := by
  intro G hG _ _
  apply dimH_le
  intro d' hd'
  by_contra! hgt
  have hd_pos : 0 < (d' : ℝ≥0) - DA := by aesop
  rw [Metric.tendsto_atTop] at h₃φ
  rcases h₃φ _ hd_pos with ⟨k, hφk_lt⟩
  generalize hD : DA + φ k = D
  specialize h₂φ k
  simp only [mem_Ioo] at h₂φ
  rcases h₂φ with ⟨hφk_gt_0, hφk_lt_1⟩
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

/-- For any subset `A` of `ℝⁿ` there is a `Gδ`‐set `G` with `A ⊆ G` and `dimH G = dimH A`. -/
theorem exists_Gδ_of_dimH {n : ℕ} (A : Set (Fin n → ℝ)) :
    ∃ G : Set (Fin n → ℝ), IsGδ G ∧ A ⊆ G ∧ dimH G = dimH A := by
  generalize hA : dimH A = DA
  have : DA ≠ ⊤ := Ne.symm (ne_of_ne_of_eq (id (Ne.symm (by apply dimH_ne_top))) hA)
  lift DA to ℝ≥0 using this
  obtain ⟨φ, h₁φ, h₂φ, h₃φ⟩ := exists_seq_strictAnti_tendsto' (show (0 : ℝ≥0) < 1 by norm_num)
  have h₄φ : Tendsto φ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_mono_right
      (Set.range_subset_iff.2 (by simp_all)) (tendsto_nhdsWithin_range.2 h₃φ)
  choose G' hG'_Gδ subG' meas_eq' using
    fun k : ℕ ↦ exists_Gδ_superset_hausdorffMeasure_eq (coe_nonneg (DA + φ k)) A
  let G := ⋂ k, G' k
  have iGδ : IsGδ G := IsGδ.iInter fun k ↦ hG'_Gδ k
  have Asub : A ⊆ G := subset_iInter fun k ↦ subG' k
  have hge : dimH A ≤ dimH G := dimH_mono Asub
  have hle : dimH G ≤ dimH A := by
    exact dimH_eq_of_Gδ_superset
      (A:=A) (DA:=DA) (φ:=φ) (G':=G') hA h₂φ h₃φ meas_eq' iGδ Asub hge
  rw [← hA]
  exact ⟨G, iGδ, Asub, le_antisymm hle hge⟩

-- If `A ⊆ ℝⁿ` has finite `s`-dimensional Hausdorff measure,
    -- then for any `k ≤ s` and any `k`-plane `W`, the slices
    -- `A ∩ (Wᗮ + x)` have finite `(s - k)`-measure for `μH[k]`-almost all `x ∈ W`. -
-- theorem hausdorffMeasure_slicing
--   (n : ℕ)
--   (A : Set (EuclideanSpace ℝ (Fin n))) (hA : MeasurableSet A)
--   (s : ℝ) (hs : μH[s] A < ⊤)
--   (k : ℕ) (hks : (k : ℝ) ≤ s)
--   (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hW : Module.finrank ℝ W = k)
--   (direction : W) (x : W) :
--   ∀ᵐ x ∂ (μH[(k : ℝ)]).restrict (W : Set (EuclideanSpace ℝ (Fin n))),
--     μH[s - k] (A ∩ (AffineSubspace.mk' x W.orthogonal : Set _)) < ⊤ := by
--   sorry

end Kakeya2D

#lint
