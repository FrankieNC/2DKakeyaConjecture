/-
Copyright (c) 2026 Francesco Nishanil Chotuck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck
-/
import ForMathlib.Kakeya.Defs
import ForMathlib.Kakeya.Marstrand
import ForMathlib.MeasureTheory.GdeltaHull

/-!
# Besicovitch sets have Hausdorff dimension two

Any subset of the plane containing a unit line segment in every direction — in particular
any Besicovitch set — has Hausdorff dimension `2`.  This is Theorem 3.8 of [Fox], following
Mattila.

The proof is by duality.  After replacing the set `B` by a `Gδ` hull of the same dimension
(`MeasureTheory.exists_isGδ_superset_dimH_eq`), one considers for each rational `q` the dual
set `Eq` of parameters `(a, b)` with `a ∈ (0,1)` whose associated segment
`{(q + t, a t + b) : t ∈ [0, 1/2]}` is contained in `B`.  These sets are `Gδ`; since every
slope `a ∈ (0,1)` is realised, a projection argument shows some `E_{q₀}` has
`dimH E_{q₀} ≥ 1`.  Marstrand's projection theorem (`dimH_image_slope_ae_eq_one`) then makes
almost every vertical section of `B` one-dimensional, and the slicing theorem
(`ae_hausdorffMeasure_vertical_slice_lt_top`) forces `μH[α] B = ∞` for all `α < 2`.

## Main results

* `IsKakeya.dimH_eq_two` : a plane set containing a unit segment in every direction has
  Hausdorff dimension `2`.
* `IsBesicovitch.dimH_eq_two` : **Besicovitch sets have Hausdorff dimension equal to 2**
  (Fox, Theorem 3.8).

## References

* J. Fox, *Besicovitch sets, Kakeya sets, and their properties*, Theorem 3.8.
* P. Mattila, *Fourier analysis and Hausdorff dimension*, p. 144.
-/

open Set Metric MeasureTheory Filter Module
open scoped ENNReal NNReal Topology

namespace Besicovitch

/-- The point `(x, y)` of the Euclidean plane. -/
private noncomputable def pt (x y : ℝ) : EuclideanSpace ℝ (Fin 2) := !₂[x, y]

private lemma pt_zero (x y : ℝ) : pt x y 0 = x := rfl

private lemma pt_one (x y : ℝ) : pt x y 1 = y := rfl

/-- Coordinates of points in the Euclidean plane are `1`-Lipschitz. -/
private lemma lipschitzWith_coord (i : Fin 2) :
    LipschitzWith 1 (fun p : EuclideanSpace ℝ (Fin 2) => p i) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, EuclideanSpace.dist_eq]
  calc dist (x i) (y i) = √(dist (x i) (y i) ^ 2) := (Real.sqrt_sq dist_nonneg).symm
    _ ≤ √(∑ j, dist (x j) (y j) ^ 2) := by
        gcongr
        exact Finset.single_le_sum (f := fun j => dist (x j) (y j) ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-- The vertical embedding `y ↦ (c, y)` of `ℝ` into the plane is an isometry. -/
private lemma isometry_pt_snd (c : ℝ) : Isometry fun y : ℝ => pt c y := by
  refine Isometry.of_dist_eq fun y y' => ?_
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, pt_zero, pt_zero, pt_one, pt_one,
    dist_self]
  rw [Real.dist_eq]
  rw [show (0 : ℝ) ^ 2 + |y - y'| ^ 2 = |y - y'| ^ 2 by ring, Real.sqrt_sq (abs_nonneg _)]

/-- The **dual set** at `q` of a plane set `G`: parameters `(a, b)` with slope `a ∈ (0, 1)`
whose segment `{(q + t, a t + b) : t ∈ [0, 1/2]}` is contained in `G`. -/
private def dualSet (G : Set (EuclideanSpace ℝ (Fin 2))) (q : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | p 0 ∈ Ioo (0 : ℝ) 1 ∧ ∀ t ∈ Icc (0 : ℝ) (1 / 2 : ℝ), pt (q + t) (p 0 * t + p 1) ∈ G}

private lemma dualSet_mono {G G' : Set (EuclideanSpace ℝ (Fin 2))} (h : G ⊆ G') (q : ℝ) :
    dualSet G q ⊆ dualSet G' q := fun _ hp => ⟨hp.1, fun t ht => h (hp.2 t ht)⟩

/-- Tube lemma: containment of the compact dual segment in an open set is an open condition
on the parameters. -/
private lemma isOpen_setOf_segment_subset {U : Set (EuclideanSpace ℝ (Fin 2))}
    (hU : IsOpen U) (q : ℝ) :
    IsOpen {p : EuclideanSpace ℝ (Fin 2) |
      ∀ t ∈ Icc (0 : ℝ) (1 / 2 : ℝ), pt (q + t) (p 0 * t + p 1) ∈ U} := by
  rw [Metric.isOpen_iff]
  intro p₀ hp₀
  -- the dual segment of `p₀` is a compact subset of `U`
  have hcont : Continuous fun t : ℝ => pt (q + t) (p₀ 0 * t + p₀ 1) := by
    have hpi : Continuous fun t : ℝ => (![q + t, p₀ 0 * t + p₀ 1] : Fin 2 → ℝ) := by
      refine continuous_pi fun i => ?_
      fin_cases i <;> simp <;> fun_prop
    exact Continuous.comp (PiLp.continuous_toLp 2 fun _ : Fin 2 => ℝ) hpi
  have hKU : (fun t : ℝ => pt (q + t) (p₀ 0 * t + p₀ 1)) '' Icc 0 (1 / 2 : ℝ) ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    exact hp₀ t ht
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_Icc.image hcont).exists_thickening_subset_open hU hKU
  refine ⟨δ / 2, by positivity, fun p hp => fun t ht => ?_⟩
  apply hsub
  rw [Metric.mem_thickening_iff]
  refine ⟨pt (q + t) (p₀ 0 * t + p₀ 1), mem_image_of_mem _ ht, ?_⟩
  rw [(isometry_pt_snd (q + t)).dist_eq, Real.dist_eq]
  have h0 : |p 0 - p₀ 0| ≤ dist p p₀ := by
    have h := (lipschitzWith_coord 0).dist_le_mul p p₀
    rwa [NNReal.coe_one, one_mul, Real.dist_eq] at h
  have h1 : |p 1 - p₀ 1| ≤ dist p p₀ := by
    have h := (lipschitzWith_coord 1).dist_le_mul p p₀
    rwa [NNReal.coe_one, one_mul, Real.dist_eq] at h
  have hpd : dist p p₀ < δ / 2 := Metric.mem_ball.1 hp
  have ht2 : |t| ≤ 1 / 2 := by
    rw [abs_of_nonneg ht.1]
    exact ht.2
  calc |p 0 * t + p 1 - (p₀ 0 * t + p₀ 1)| = |(p 0 - p₀ 0) * t + (p 1 - p₀ 1)| := by
        ring_nf
    _ ≤ |(p 0 - p₀ 0) * t| + |p 1 - p₀ 1| := abs_add_le _ _
    _ = |p 0 - p₀ 0| * |t| + |p 1 - p₀ 1| := by rw [abs_mul]
    _ ≤ dist p p₀ * (1 / 2) + dist p p₀ := by gcongr
    _ < δ := by linarith [hpd, hδ]

/-- The dual sets of a `Gδ` set are `Gδ`. -/
private lemma isGδ_dualSet {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : IsGδ G) (q : ℝ) :
    IsGδ (dualSet G q) := by
  obtain ⟨T, hTopen, hTcount, rfl⟩ := hG
  have hset : dualSet (⋂₀ T) q =
      ((fun p : EuclideanSpace ℝ (Fin 2) => p 0) ⁻¹' Ioo (0 : ℝ) 1) ∩
        ⋂ U ∈ T, {p : EuclideanSpace ℝ (Fin 2) |
          ∀ t ∈ Icc (0 : ℝ) (1 / 2 : ℝ), pt (q + t) (p 0 * t + p 1) ∈ U} := by
    ext p
    simp only [dualSet, mem_setOf_eq, mem_inter_iff, mem_iInter, mem_preimage, mem_sInter]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun U hU t ht => h2 t ht U hU⟩,
      fun ⟨h1, h2⟩ => ⟨h1, fun t ht U hU => h2 U hU t ht⟩⟩
  rw [hset]
  exact ((isOpen_Ioo.preimage (lipschitzWith_coord 0).continuous).isGδ).inter
    (IsGδ.biInter hTcount fun U hU => (isOpen_setOf_segment_subset (hTopen U hU) q).isGδ)

/-- Every slope `a ∈ (0, 1)` is realised in some dual set of a Kakeya set, with rational
left endpoint. -/
private lemma exists_mem_dualSet {B : Set (EuclideanSpace ℝ (Fin 2))} (hB : IsKakeya B)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) : ∃ q : ℚ, ∃ b : ℝ, pt a b ∈ dualSet B (q : ℝ) := by
  obtain ⟨ha0, ha1⟩ := ha
  -- the (non-normalised) direction of slope `a`
  have hw0 : pt 1 a ≠ 0 := by
    intro h
    have h1 : pt 1 a 0 = (0 : EuclideanSpace ℝ (Fin 2)) 0 := by rw [h]
    rw [pt_zero] at h1
    exact one_ne_zero h1
  set r : ℝ := ‖pt 1 a‖ with hr
  have hr_pos : 0 < r := norm_pos_iff.2 hw0
  have hr2 : r ^ 2 = 1 + a ^ 2 := by
    rw [hr, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, pt_zero, pt_one]
    ring
  have hr_lt2 : r < 2 := by nlinarith
  have hrinv : 1 / 2 < r⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hr_pos]
    linarith
  -- the Kakeya set contains a unit segment in this direction
  obtain ⟨x, hx⟩ := hB (r⁻¹ • pt 1 a) (norm_smul_inv_norm hw0)
  -- pick a rational left endpoint inside the segment's shadow
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x 0 < x 0 + (r⁻¹ - 1 / 2) by linarith)
  refine ⟨q, x 1 + ((q : ℝ) - x 0) * a, ?_, fun t ht => ?_⟩
  · rw [pt_zero]
    exact ⟨ha0, ha1⟩
  · rw [pt_zero, pt_one]
    apply hx
    rw [segment_eq_image']
    refine ⟨((q : ℝ) + t - x 0) * r, ⟨?_, ?_⟩, ?_⟩
    · have : (0 : ℝ) ≤ (q : ℝ) + t - x 0 := by linarith [ht.1]
      positivity
    · have hle : (q : ℝ) + t - x 0 ≤ r⁻¹ := by linarith [ht.2]
      calc ((q : ℝ) + t - x 0) * r ≤ r⁻¹ * r := by gcongr
        _ = 1 := inv_mul_cancel₀ hr_pos.ne'
    · simp only [add_sub_cancel_left, smul_smul]
      have hcanc : ((q : ℝ) + t - x 0) * r * r⁻¹ = (q : ℝ) + t - x 0 := by
        rw [mul_assoc, mul_inv_cancel₀ hr_pos.ne', mul_one]
      apply PiLp.ext
      intro i
      fin_cases i
      · simp only [Fin.mk_zero, PiLp.add_apply, PiLp.smul_apply, pt_zero, smul_eq_mul, hcanc]
        ring
      · simp only [Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, pt_one, smul_eq_mul, hcanc]
        ring

/-- Some dual set has positive one-dimensional Hausdorff measure.

If all dual sets were `μH[1]`-null, so would be their countable union over `q : ℚ`, and
hence its `1`-Lipschitz projection `p ↦ p 0`.  But that projection covers `(0, 1)`, which
has positive length. -/
private lemma exists_dualSet_hausdorffMeasure_ne_zero {B G : Set (EuclideanSpace ℝ (Fin 2))}
    (hB : IsKakeya B) (hBG : B ⊆ G) :
    ∃ q : ℚ, μH[(1 : ℝ)] (dualSet G (q : ℝ)) ≠ 0 := by
  by_contra hall
  push Not at hall
  have hUnull : μH[(1 : ℝ)] (⋃ q : ℚ, dualSet G (q : ℝ)) = 0 := measure_iUnion_null hall
  have himg : μH[(1 : ℝ)]
      ((fun p : EuclideanSpace ℝ (Fin 2) => p 0) '' ⋃ q : ℚ, dualSet G (q : ℝ)) = 0 := by
    have hle := (lipschitzWith_coord 0).hausdorffMeasure_image_le
      (by norm_num : (0 : ℝ) ≤ 1) (⋃ q : ℚ, dualSet G (q : ℝ))
    simpa [hUnull] using hle
  have hproj : Ioo (0 : ℝ) 1 ⊆
      (fun p : EuclideanSpace ℝ (Fin 2) => p 0) '' ⋃ q : ℚ, dualSet G (q : ℝ) := by
    intro a ha
    obtain ⟨q, b, hmem⟩ := exists_mem_dualSet hB ha
    exact ⟨pt a b, mem_iUnion.2 ⟨q, dualSet_mono hBG _ hmem⟩, pt_zero a b⟩
  have h0 : μH[(1 : ℝ)] (Ioo (0 : ℝ) 1) = 0 := measure_mono_null hproj himg
  rw [hausdorffMeasure_real] at h0
  simp [Real.volume_Ioo] at h0

/-- Core estimate: a `Gδ` superset of a Kakeya set has infinite `α`-dimensional Hausdorff
measure for every `1 ≤ α < 2`. -/
private lemma hausdorffMeasure_eq_top_of_isGδ {B G : Set (EuclideanSpace ℝ (Fin 2))}
    (hB : IsKakeya B) (hBG : B ⊆ G) (hG : IsGδ G) {α : ℝ≥0} (hα1 : 1 ≤ α)
    (hα2 : (α : ℝ≥0∞) < 2) : μH[(α : ℝ)] G = ∞ := by
  by_contra hfin
  -- some dual set is at least one-dimensional
  obtain ⟨q₀, hq₀⟩ := exists_dualSet_hausdorffMeasure_ne_zero hB hBG
  have hdimE : 1 ≤ dimH (dualSet G (q₀ : ℝ)) := by
    have := le_dimH_of_hausdorffMeasure_ne_zero (d := 1) (by exact_mod_cast hq₀)
    simpa using this
  -- Marstrand: almost every slope has a one-dimensional projection
  have hmars := dimH_image_slope_ae_eq_one ((isGδ_dualSet hG _).measurableSet) hdimE
  -- slicing: almost every vertical section of `G` has finite `μH[α-1]`-measure
  have h1s : (1 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα1
  have hslice := ae_hausdorffMeasure_vertical_slice_lt_top h1s (lt_top_iff_ne_top.2 hfin)
  -- shift the sections by `q₀`
  have hshift : ∀ᵐ t : ℝ, μH[(α : ℝ) - 1] (G ∩ {p | p 0 = (q₀ : ℝ) + t}) < ∞ := by
    rw [ae_iff] at hslice ⊢
    obtain ⟨N, hN, hNmeas, hNnull⟩ := exists_measurable_superset_of_null hslice
    have hsub : {t : ℝ | ¬ μH[(α : ℝ) - 1] (G ∩ {p | p 0 = (q₀ : ℝ) + t}) < ∞} ⊆
        (fun t : ℝ => (q₀ : ℝ) + t) ⁻¹' N := fun t ht => hN ht
    refine measure_mono_null hsub ?_
    rw [(measurePreserving_add_left volume (q₀ : ℝ)).measure_preimage
      hNmeas.nullMeasurableSet]
    exact hNnull
  -- pick a single good parameter `t ∈ [0, 1/2]`
  obtain ⟨t, htIcc, hgood, hfin'⟩ :
      ∃ t, t ∈ Icc (0 : ℝ) (1 / 2 : ℝ) ∧
        dimH ((fun p => t * p 0 + p 1) '' dualSet G (q₀ : ℝ)) = 1 ∧
        μH[(α : ℝ) - 1] (G ∩ {p | p 0 = (q₀ : ℝ) + t}) < ∞ := by
    by_contra hno
    push Not at hno
    have hsub : Icc (0 : ℝ) (1 / 2 : ℝ) ⊆
        {t | ¬ (dimH ((fun p => t * p 0 + p 1) '' dualSet G (q₀ : ℝ)) = 1 ∧
          μH[(α : ℝ) - 1] (G ∩ {p | p 0 = (q₀ : ℝ) + t}) < ∞)} := by
      intro t ht hPQ
      exact hPQ.2.ne (top_le_iff.1 (hno t ht hPQ.1))
    have hIcc0 : volume (Icc (0 : ℝ) (1 / 2 : ℝ)) = 0 :=
      measure_mono_null hsub (ae_iff.1 (hmars.and hshift))
    simp [Real.volume_Icc] at hIcc0
  -- the vertical section at `q₀ + t` contains an isometric copy of the slope projection
  have hsec : 1 ≤ dimH (G ∩ {p : EuclideanSpace ℝ (Fin 2) | p 0 = (q₀ : ℝ) + t}) := by
    have hsub2 : (fun y : ℝ => pt ((q₀ : ℝ) + t) y) ''
        ((fun p => t * p 0 + p 1) '' dualSet G (q₀ : ℝ)) ⊆
        G ∩ {p | p 0 = (q₀ : ℝ) + t} := by
      rintro _ ⟨y, ⟨p, hp, rfl⟩, rfl⟩
      have h2 := hp.2 t htIcc
      rw [mul_comm (p 0) t] at h2
      exact ⟨h2, pt_zero _ _⟩
    calc (1 : ℝ≥0∞) = dimH ((fun p => t * p 0 + p 1) '' dualSet G (q₀ : ℝ)) := hgood.symm
      _ = dimH ((fun y : ℝ => pt ((q₀ : ℝ) + t) y) ''
            ((fun p => t * p 0 + p 1) '' dualSet G (q₀ : ℝ))) :=
          ((isometry_pt_snd _).dimH_image _).symm
      _ ≤ _ := dimH_mono hsub2
  -- contradiction: the section has infinite `μH[α-1]`-measure
  have hα2' : α < 2 := by exact_mod_cast hα2
  have hlt1 : ((α - 1 : ℝ≥0) : ℝ≥0∞) < dimH (G ∩ {p | p 0 = (q₀ : ℝ) + t}) := by
    refine lt_of_lt_of_le ?_ hsec
    exact_mod_cast (tsub_lt_iff_right hα1).2 (by rw [one_add_one_eq_two]; exact hα2')
  have htop := hausdorffMeasure_of_lt_dimH hlt1
  rw [NNReal.coe_sub hα1, NNReal.coe_one] at htop
  exact absurd htop hfin'.ne

/-- A plane set containing a unit line segment in every direction has Hausdorff
dimension `2`. -/
theorem _root_.IsKakeya.dimH_eq_two {B : Set (EuclideanSpace ℝ (Fin 2))} (hB : IsKakeya B) :
    dimH B = 2 := by
  -- upper bound: a subset of the plane has dimension at most `2`
  have hle : dimH B ≤ 2 := by
    have h2 : dimH (univ : Set (EuclideanSpace ℝ (Fin 2))) = 2 := by
      rw [Real.dimH_univ_eq_finrank (EuclideanSpace ℝ (Fin 2)), finrank_euclideanSpace_fin]
      norm_num
    exact (dimH_mono (subset_univ B)).trans h2.le
  -- pass to a `Gδ` hull of the same dimension
  obtain ⟨G, hGδ, hBG, hdimG⟩ := MeasureTheory.exists_isGδ_superset_dimH_eq B
  refine le_antisymm hle ?_
  rw [← hdimG]
  by_contra hlt
  push Not at hlt
  obtain ⟨α, hα₁, hα₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp
    (max_lt hlt (by norm_num : (1 : ℝ≥0∞) < 2))
  have h1α : 1 ≤ α := by
    have h := (le_max_right (dimH G) 1).trans_lt hα₁
    exact_mod_cast h.le
  have htop := hausdorffMeasure_eq_top_of_isGδ hB hBG hGδ h1α hα₂
  exact absurd (le_dimH_of_hausdorffMeasure_eq_top htop)
    (not_le.2 ((le_max_left (dimH G) 1).trans_lt hα₁))

/-- **Besicovitch sets have Hausdorff dimension equal to 2** (Fox, Theorem 3.8). -/
theorem _root_.IsBesicovitch.dimH_eq_two {B : Set (EuclideanSpace ℝ (Fin 2))}
    (hB : IsBesicovitch B) : dimH B = 2 :=
  hB.1.dimH_eq_two

end Besicovitch
