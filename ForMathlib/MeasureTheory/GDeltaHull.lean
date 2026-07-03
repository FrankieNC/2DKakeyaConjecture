/-
Copyright (c) 2026 Francesco Nishanil Chotuck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck
-/
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Gδ hulls for Hausdorff measure and dimension

Every set of `d`-dimensional Hausdorff measure zero is contained in a `Gδ` set of measure
zero (obtained by fattening efficient covers into open covers), and consequently every set
is contained in a `Gδ` set of the same Hausdorff dimension.

## Main results

* `MeasureTheory.exists_isGδ_superset_hausdorffMeasure_zero` : a set of `μH[d]`-measure zero
  is contained in a `Gδ` set of `μH[d]`-measure zero.
* `MeasureTheory.exists_isGδ_superset_dimH_eq` : every set is contained in a `Gδ` set of the
  same Hausdorff dimension.

## References

* K. J. Falconer, *The geometry of fractal sets*, p. 8–9.
* J. Fox, *Besicovitch sets, Kakeya sets, and their properties*, Prop. 3.2 and Prop. 3.4.
-/

open Set Metric Filter ENNReal
open scoped Topology NNReal

namespace MeasureTheory

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Subadditivity-type bound for `rpow` on `ℝ≥0∞`: `(a + b) ^ d ≤ 2 ^ d * (a ^ d + b ^ d)`. -/
private lemma rpow_add_le_two_rpow_mul {a b : ℝ≥0∞} {d : ℝ} (hd : 0 ≤ d) :
    (a + b) ^ d ≤ 2 ^ d * (a ^ d + b ^ d) := by
  calc (a + b) ^ d ≤ (2 * max a b) ^ d := by
        refine ENNReal.rpow_le_rpow ?_ hd
        rw [two_mul]
        exact add_le_add (le_max_left a b) (le_max_right a b)
    _ = 2 ^ d * max a b ^ d := ENNReal.mul_rpow_of_nonneg _ _ hd
    _ ≤ 2 ^ d * (a ^ d + b ^ d) := by
        gcongr
        rcases max_cases a b with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
        · exact self_le_add_right _ _
        · exact self_le_add_left _ _

/-- From `μH[d] A = 0`, extract for each bound `ε > 0` an *open* cover of `A` by sets of
diameter at most `2 * ε` whose `d`-power diameter sum is at most `2 ^ d * (ε + ε)`. -/
private lemma exists_open_cover_of_hausdorffMeasure_zero {d : ℝ} (hd : 0 < d) {A : Set X}
    (h : μH[d] A = 0) {ε : ℝ≥0∞} (hε0 : 0 < ε) (hεtop : ε ≠ ∞) :
    ∃ U : ℕ → Set X, (∀ n, IsOpen (U n)) ∧ A ⊆ ⋃ n, U n ∧
      (∀ n, ediam (U n) ≤ 2 * ε) ∧
      ∑' n, ediam (U n) ^ d ≤ 2 ^ d * (ε + ε) := by
  -- extract an efficient cover from the definition of Hausdorff measure
  obtain ⟨t, htA, htdiam, htsum⟩ : ∃ t : ℕ → Set X, A ⊆ ⋃ n, t n ∧
      (∀ n, ediam (t n) ≤ ε) ∧
      ∑' n, (⨆ _ : (t n).Nonempty, ediam (t n) ^ d) < ε := by
    have happ := Measure.hausdorffMeasure_apply d A
    rw [h] at happ
    have hin : (⨅ (t : ℕ → Set X) (_ : A ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ ε),
        ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ d) = 0 := by
      refine le_antisymm ?_ zero_le
      calc (⨅ (t : ℕ → Set X) (_ : A ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ ε),
            ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ d)
          ≤ ⨆ (r : ℝ≥0∞) (_ : 0 < r),
              ⨅ (t : ℕ → Set X) (_ : A ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r),
                ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ d :=
            le_iSup₂ (f := fun r _ =>
              ⨅ (t : ℕ → Set X) (_ : A ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r),
                ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ d) ε hε0
        _ = 0 := happ.symm
    have hlt : (⨅ (t : ℕ → Set X) (_ : A ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ ε),
        ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ d) < ε := hin ▸ hε0
    obtain ⟨t, ht⟩ := iInf_lt_iff.mp hlt
    obtain ⟨h1, ht⟩ := iInf_lt_iff.mp ht
    obtain ⟨h2, ht⟩ := iInf_lt_iff.mp ht
    exact ⟨t, h1, h2, ht⟩
  -- fattening radii
  obtain ⟨δ, hδ0, hδε, hδd⟩ : ∃ δ : ℕ → ℝ≥0, (∀ n, 0 < δ n) ∧
      (∀ n, (δ n : ℝ≥0∞) ≤ ε / 2) ∧
      (∀ n, (2 * δ n : ℝ≥0∞) ^ d ≤ ε * 2⁻¹ ^ (n + 1)) := by
    have key : ∀ n : ℕ, ∃ δ : ℝ≥0, 0 < δ ∧ (δ : ℝ≥0∞) ≤ ε / 2 ∧
        (2 * δ : ℝ≥0∞) ^ d ≤ ε * 2⁻¹ ^ (n + 1) := by
      intro n
      have hτ0 : (0 : ℝ≥0∞) < ε * 2⁻¹ ^ (n + 1) :=
        ENNReal.mul_pos hε0.ne' (by simp)
      have hτtop : ε * 2⁻¹ ^ (n + 1) ≠ ∞ :=
        ENNReal.mul_ne_top hεtop (by simp)
      set c : ℝ≥0∞ := min (ε / 2) ((ε * 2⁻¹ ^ (n + 1)) ^ d⁻¹ / 2) with hc
      have hc0 : 0 < c := by
        refine lt_min (ENNReal.div_pos hε0.ne' (by norm_num)) ?_
        exact ENNReal.div_pos (ENNReal.rpow_pos hτ0 hτtop).ne' (by norm_num)
      have hctop : c ≠ ∞ :=
        ((min_le_left _ _).trans_lt (ENNReal.div_lt_top hεtop (by norm_num))).ne
      refine ⟨c.toNNReal, ENNReal.toNNReal_pos hc0.ne' hctop, ?_, ?_⟩
      · rw [ENNReal.coe_toNNReal hctop]
        exact min_le_left _ _
      · rw [ENNReal.coe_toNNReal hctop]
        calc (2 * c) ^ d ≤ (2 * ((ε * 2⁻¹ ^ (n + 1)) ^ d⁻¹ / 2)) ^ d := by
              gcongr
              exact min_le_right _ _
          _ = ((ε * 2⁻¹ ^ (n + 1)) ^ d⁻¹) ^ d := by
              rw [ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
          _ = ε * 2⁻¹ ^ (n + 1) := ENNReal.rpow_inv_rpow hd.ne' _
    choose δ h1 h2 h3 using key
    exact ⟨δ, h1, h2, h3⟩
  -- the fattened cover
  refine ⟨fun n => thickening (δ n : ℝ) (t n), fun n => isOpen_thickening,
    htA.trans (iUnion_mono fun n =>
      self_subset_thickening (by exact_mod_cast hδ0 n) (t n)), ?_, ?_⟩
  · intro n
    calc ediam (thickening (δ n : ℝ) (t n))
        ≤ ediam (t n) + 2 * δ n := ediam_thickening_le _
      _ ≤ ε + 2 * (ε / 2) := by
          gcongr
          exacts [htdiam n, hδε n]
      _ ≤ 2 * ε := by
          rw [ENNReal.mul_div_cancel' (by norm_num) (by norm_num), two_mul]
  · have hbound : ∀ n, ediam (thickening (δ n : ℝ) (t n)) ^ d
        ≤ 2 ^ d * ((⨆ _ : (t n).Nonempty, ediam (t n) ^ d) + ε * 2⁻¹ ^ (n + 1)) := by
      intro n
      rcases eq_empty_or_nonempty (t n) with hne | hne
      · simp [hne, thickening_empty, ediam_empty,
          ENNReal.zero_rpow_of_pos hd]
      · calc ediam (thickening (δ n : ℝ) (t n)) ^ d
            ≤ (ediam (t n) + 2 * δ n) ^ d :=
              ENNReal.rpow_le_rpow (ediam_thickening_le _) hd.le
          _ ≤ 2 ^ d * (ediam (t n) ^ d + (2 * δ n : ℝ≥0∞) ^ d) :=
              rpow_add_le_two_rpow_mul hd.le
          _ ≤ 2 ^ d * ((⨆ _ : (t n).Nonempty, ediam (t n) ^ d) + ε * 2⁻¹ ^ (n + 1)) := by
              gcongr
              · rw [iSup_pos hne]
              · exact hδd n
    calc ∑' n, ediam (thickening (δ n : ℝ) (t n)) ^ d
        ≤ ∑' n, 2 ^ d * ((⨆ _ : (t n).Nonempty, ediam (t n) ^ d) + ε * 2⁻¹ ^ (n + 1)) :=
          ENNReal.tsum_le_tsum hbound
      _ = 2 ^ d * ((∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ d)
            + ∑' n, ε * 2⁻¹ ^ (n + 1)) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
      _ ≤ 2 ^ d * (ε + ε) := by
          have hgeom : ∑' n : ℕ, ε * 2⁻¹ ^ (n + 1) = ε := by
            calc ∑' n : ℕ, ε * 2⁻¹ ^ (n + 1) = ε * (2⁻¹ * ∑' n : ℕ, 2⁻¹ ^ n) := by
                  rw [ENNReal.tsum_mul_left]
                  congr 1
                  rw [← ENNReal.tsum_mul_left]
                  exact tsum_congr fun n => by rw [pow_succ, mul_comm]
              _ = ε := by
                  rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
                    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
          rw [hgeom]
          exact mul_le_mul' le_rfl (add_le_add htsum.le le_rfl)

/-- A set of `d`-dimensional Hausdorff measure zero is contained in a `Gδ` set of
`d`-dimensional Hausdorff measure zero. -/
theorem exists_isGδ_superset_hausdorffMeasure_zero {d : ℝ} (hd : 0 < d) {A : Set X}
    (h : μH[d] A = 0) : ∃ G, IsGδ G ∧ A ⊆ G ∧ μH[d] G = 0 := by
  have key : ∀ i : ℕ, ∃ U : ℕ → Set X, (∀ n, IsOpen (U n)) ∧ A ⊆ ⋃ n, U n ∧
      (∀ n, ediam (U n) ≤ 2 * 2⁻¹ ^ i) ∧
      ∑' n, ediam (U n) ^ d ≤ 2 ^ d * (2⁻¹ ^ i + 2⁻¹ ^ i) := fun i =>
    exists_open_cover_of_hausdorffMeasure_zero hd h
      (ENNReal.pow_pos (by norm_num) i) (ENNReal.pow_ne_top (by norm_num))
  choose U hUopen hUA hUdiam hUsum using key
  refine ⟨⋂ i, ⋃ n, U i n, IsGδ.iInter fun i => (isOpen_iUnion (hUopen i)).isGδ,
    subset_iInter hUA, le_antisymm ?_ zero_le⟩
  have hr0 : Tendsto (fun i : ℕ => 2 * (2⁻¹ : ℝ≥0∞) ^ i) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (2⁻¹ : ℝ≥0∞) < 1)) (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ∞))
    simpa using this
  have hle := Measure.hausdorffMeasure_le_liminf_tsum d (⋂ i, ⋃ n, U i n)
    (fun i : ℕ => 2 * (2⁻¹ : ℝ≥0∞) ^ i) hr0 U
    (Eventually.of_forall fun i => hUdiam i)
    (Eventually.of_forall fun i => iInter_subset _ i)
  refine hle.trans ?_
  have h0 : Tendsto (fun i : ℕ => (2 : ℝ≥0∞) ^ d * (2⁻¹ ^ i + 2⁻¹ ^ i)) atTop (𝓝 0) := by
    have hsum : Tendsto (fun i : ℕ => (2⁻¹ : ℝ≥0∞) ^ i + 2⁻¹ ^ i) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (2⁻¹ : ℝ≥0∞) < 1))
      simpa using this.add this
    have := ENNReal.Tendsto.const_mul hsum
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg hd.le (by norm_num) : (2 : ℝ≥0∞) ^ d ≠ ∞))
    simpa using this
  calc liminf (fun i => ∑' n, ediam (U i n) ^ d) atTop
      ≤ liminf (fun i : ℕ => (2 : ℝ≥0∞) ^ d * (2⁻¹ ^ i + 2⁻¹ ^ i)) atTop :=
        liminf_le_liminf (Eventually.of_forall hUsum)
    _ = 0 := h0.liminf_eq

/-- **Gδ hulls of the same Hausdorff dimension**: every set is contained in a `Gδ` set with
the same Hausdorff dimension. -/
theorem exists_isGδ_superset_dimH_eq [SecondCountableTopology X] (A : Set X) :
    ∃ G, IsGδ G ∧ A ⊆ G ∧ dimH G = dimH A := by
  rcases eq_or_ne (dimH A) ∞ with htop | htop
  · refine ⟨univ, IsGδ.univ, subset_univ A, le_antisymm ?_ (dimH_mono (subset_univ A))⟩
    rw [htop]
    exact le_top
  · -- exponents approaching `dimH A` from above
    set s : ℝ≥0 := (dimH A).toNNReal with hs
    have hd : ∀ i : ℕ, μH[(s + ((i : ℝ≥0) + 1)⁻¹ : ℝ≥0)] A = 0 := by
      intro i
      refine hausdorffMeasure_of_dimH_lt ?_
      rw [ENNReal.coe_add, hs, ENNReal.coe_toNNReal htop]
      exact ENNReal.lt_add_right htop (by positivity)
    have hpos : ∀ i : ℕ, (0 : ℝ) < ((s + ((i : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ) := by
      intro i
      have : (0 : ℝ≥0) < s + ((i : ℝ≥0) + 1)⁻¹ := by positivity
      exact_mod_cast this
    choose G hGδ hGA hG0 using fun i =>
      exists_isGδ_superset_hausdorffMeasure_zero (hpos i) (hd i)
    refine ⟨⋂ i, G i, IsGδ.iInter hGδ, subset_iInter hGA,
      le_antisymm ?_ (dimH_mono (subset_iInter hGA))⟩
    -- upper bound for the dimension of the hull
    have hle : ∀ i : ℕ, dimH (⋂ j, G j) ≤ ↑(s + ((i : ℝ≥0) + 1)⁻¹) := by
      intro i
      by_contra hlt
      push Not at hlt
      have htop' := hausdorffMeasure_of_lt_dimH hlt
      have hmono : μH[((s + ((i : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ)] (⋂ j, G j)
          ≤ μH[((s + ((i : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ)] (G i) :=
        measure_mono (iInter_subset _ i)
      rw [htop', hG0 i] at hmono
      simp at hmono
    have hinf : dimH (⋂ j, G j) ≤ ⨅ i : ℕ, (↑(s + ((i : ℝ≥0) + 1)⁻¹) : ℝ≥0∞) := le_iInf hle
    refine hinf.trans ?_
    have hcalc : (⨅ i : ℕ, (↑(s + ((i : ℝ≥0) + 1)⁻¹) : ℝ≥0∞))
        = (s : ℝ≥0∞) + ⨅ i : ℕ, (↑(((i : ℝ≥0) + 1)⁻¹) : ℝ≥0∞) := by
      simp_rw [ENNReal.coe_add]
      rw [ENNReal.add_iInf]
    have hzero : (⨅ i : ℕ, (↑(((i : ℝ≥0) + 1)⁻¹) : ℝ≥0∞)) = 0 := by
      refine le_antisymm ?_ zero_le
      refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt
        (show ((ε : ℝ≥0∞)) ≠ 0 from ENNReal.coe_ne_zero.2 hε.ne')
      rw [zero_add]
      refine (iInf_le _ n).trans ?_
      calc (↑(((n : ℝ≥0) + 1)⁻¹) : ℝ≥0∞) = ((n : ℝ≥0∞) + 1)⁻¹ := by
            rw [ENNReal.coe_inv (by positivity)]
            push_cast
            rfl
        _ ≤ (n : ℝ≥0∞)⁻¹ := by
            gcongr
            exact le_self_add
        _ ≤ ε := hn.le
    rw [hcalc, hzero, add_zero, hs, ENNReal.coe_toNNReal htop]
