/-
Copyright (c) 2026 Francesco Nishanil Chotuck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Marstrand's projection theorem and Hausdorff-measure slicing (statements)

This file states two classical theorems of geometric measure theory, following Mattila.
The proofs are substantial (energy/Fourier-analytic methods for the projection theorem, and
a Fatou-type argument for slicing) and are deferred: the statements below are interfaces
(proofs currently `sorry`) consumed by `ForMathlib.Kakeya.DimensionTwo`, to be proved in
future work.

Directions of lines through the origin in `ℝⁿ⁺¹` are parametrised by unit vectors
`e ∈ Sⁿ`, and "almost all directions" is with respect to the `n`-dimensional Hausdorff
measure `μH[n]` restricted to the unit sphere (a constant multiple of the surface measure).
The orthogonal projection onto the line `{t • e}` is identified with `fun x => ⟪x, e⟫_ℝ`,
via the isometry `t • e ↦ t`.

## Main statements

* `dimH_image_inner_ae_eq` : (Marstrand, dimension part) if `A` is Borel with `dimH A ≤ 1`,
  then for almost every direction `e`, the projection of `A` to the line spanned by `e` has
  the same Hausdorff dimension as `A`.
* `hausdorffMeasure_image_inner_ae_pos` : (Marstrand, measure part) if `A` is Borel with
  `dimH A > 1`, then for almost every direction `e` the projection of `A` has positive
  one-dimensional Hausdorff measure.
* `dimH_image_slope_ae_eq_one` : the planar corollary, with lines parametrised by slope: if
  `A ⊆ ℝ²` is Borel with `dimH A ≥ 1` then for (Lebesgue) almost every `t : ℝ` the image
  of `A` under `p ↦ t * p 0 + p 1` has Hausdorff dimension `1`.
* `ae_hausdorffMeasure_slice_lt_top` : (slicing) if `μH[s] A < ∞` and `W` is a
  `k`-dimensional subspace with `k ≤ s`, then for `μH[k]`-almost every `x ∈ W` the slice
  `A ∩ (x +ᵥ Wᗮ)` has finite `μH[s - k]`-measure.
* `ae_hausdorffMeasure_vertical_slice_lt_top` : the planar corollary for vertical lines.

## References

* P. Mattila, *Fourier analysis and Hausdorff dimension*, Theorem 4.1 (p. 56) and
  Chapter 6 (p. 94).
* J. Fox, *Besicovitch sets, Kakeya sets, and their properties*, Prop. 3.6 and Prop. 3.7.
-/

open Set Metric MeasureTheory Module
open scoped ENNReal NNReal RealInnerProductSpace Pointwise

/-- **Marstrand's projection theorem**, dimension part (Fox, Prop. 3.6; Mattila, Thm 4.1):
if `A ⊆ ℝⁿ⁺¹` is Borel with `dimH A ≤ 1`, then for `μH[n]`-almost every unit vector `e`
the orthogonal projection of `A` onto the line spanned by `e` has Hausdorff dimension
`dimH A`. -/
theorem dimH_image_inner_ae_eq {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hA : MeasurableSet A) (hdim : dimH A ≤ 1) :
    ∀ᵐ e ∂(μH[(n : ℝ)].restrict (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)),
      dimH ((fun x => ⟪x, e⟫) '' A) = dimH A := by
  sorry

/-- **Marstrand's projection theorem**, measure part (Fox, Prop. 3.6; Mattila, Thm 4.1):
if `A ⊆ ℝⁿ⁺¹` is Borel with `dimH A > 1`, then for `μH[n]`-almost every unit vector `e`
the orthogonal projection of `A` onto the line spanned by `e` has positive one-dimensional
Hausdorff measure. -/
theorem hausdorffMeasure_image_inner_ae_pos {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hA : MeasurableSet A) (hdim : 1 < dimH A) :
    ∀ᵐ e ∂(μH[(n : ℝ)].restrict (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)),
      0 < μH[1] ((fun x => ⟪x, e⟫) '' A) := by
  sorry

/-- **Marstrand's projection theorem in the plane, slope form**: if `A ⊆ ℝ²` is Borel with
`dimH A ≥ 1`, then for (Lebesgue) almost every `t : ℝ` the image of `A` under the
projection `p ↦ t * p 0 + p 1` has Hausdorff dimension `1`.

This is the form of Prop. 3.6 used in the proof of Theorem 3.8.  It follows from
`dimH_image_inner_ae_eq` and `hausdorffMeasure_image_inner_ae_pos` by parametrising the
(non-horizontal) directions of `S¹` by slope, a locally bi-Lipschitz change of variables;
this derivation is deferred together with the proofs of the general statements. -/
theorem dimH_image_slope_ae_eq_one {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : MeasurableSet A) (hdim : 1 ≤ dimH A) :
    ∀ᵐ t : ℝ, dimH ((fun p => t * p 0 + p 1) '' A) = 1 := by
  sorry

/-- **Hausdorff-measure slicing** (Fox, Prop. 3.7; Mattila, Ch. 6): if `A ⊆ ℝⁿ` satisfies
`μH[s] A < ∞` and `W` is a `k`-dimensional subspace with `k ≤ s`, then for `μH[k]`-almost
every `x ∈ W` the slice of `A` by the affine subspace `x +ᵥ Wᗮ` has finite
`(s - k)`-dimensional Hausdorff measure.  (The degenerate instances `k = 0` and `k = n` are
trivially true, so no `0 < k` or `k ≤ n` side conditions are needed.) -/
theorem ae_hausdorffMeasure_slice_lt_top {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))} {s : ℝ}
    (hs : μH[s] A < ∞) {k : ℕ} (hk : (k : ℝ) ≤ s) {W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    (hW : finrank ℝ W = k) :
    ∀ᵐ x ∂(μH[(k : ℝ)].restrict (W : Set (EuclideanSpace ℝ (Fin n)))),
      μH[s - k] (A ∩ (x +ᵥ (Wᗮ : Set (EuclideanSpace ℝ (Fin n))))) < ∞ := by
  sorry

/-- **Slicing by vertical lines in the plane**: if `A ⊆ ℝ²` satisfies `μH[s] A < ∞` with
`s ≥ 1`, then for (Lebesgue) almost every `c : ℝ` the vertical slice `A ∩ {p | p 0 = c}`
has finite `(s - 1)`-dimensional Hausdorff measure.  This is the instance of
`ae_hausdorffMeasure_slice_lt_top` used in the proof of Theorem 3.8. -/
theorem ae_hausdorffMeasure_vertical_slice_lt_top {A : Set (EuclideanSpace ℝ (Fin 2))}
    {s : ℝ} (h1 : 1 ≤ s) (hs : μH[s] A < ∞) :
    ∀ᵐ c : ℝ, μH[s - 1] (A ∩ {p | p 0 = c}) < ∞ := by
  set e₀ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1 with he₀def
  have hn : ‖e₀‖ = 1 := by rw [he₀def, PiLp.norm_single]; norm_num
  have he₀ne : e₀ ≠ 0 := by
    rw [← norm_ne_zero_iff, hn]
    exact one_ne_zero
  have he₀0 : e₀ 0 = 1 := by rw [he₀def, PiLp.single_apply]; simp
  have hWrank : finrank ℝ (ℝ ∙ e₀) = 1 := finrank_span_singleton he₀ne
  have hk1 : ((1 : ℕ) : ℝ) ≤ s := by exact_mod_cast h1
  have hae := ae_hausdorffMeasure_slice_lt_top hs hk1 hWrank
  rw [Nat.cast_one] at hae
  -- membership in the orthogonal complement is vanishing of the first coordinate
  have horth : ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ ((ℝ ∙ e₀)ᗮ : Set (EuclideanSpace ℝ (Fin 2)))
      ↔ p 0 = 0 := by
    intro p
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, he₀def,
      EuclideanSpace.inner_single_left]
    simp
  -- the coset `(c • e₀) +ᵥ (ℝ ∙ e₀)ᗮ` is the vertical line at `c`
  have hcoset : ∀ c : ℝ,
      ((c • e₀) +ᵥ ((ℝ ∙ e₀)ᗮ : Set (EuclideanSpace ℝ (Fin 2))))
        = {p : EuclideanSpace ℝ (Fin 2) | p 0 = c} := by
    intro c
    ext y
    rw [Set.mem_vadd_set, mem_setOf_eq]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, he₀0, smul_eq_mul, mul_one,
        (horth p).1 hp, add_zero]
    · intro hy
      exact ⟨y - c • e₀, (horth _).2 (by rw [PiLp.sub_apply, PiLp.smul_apply, he₀0,
        smul_eq_mul, mul_one, hy, sub_self]), by rw [vadd_eq_add, add_sub_cancel]⟩
  -- the isometric parametrisation of the axis
  have hfiso : Isometry fun c : ℝ => c • e₀ := by
    refine Isometry.of_dist_eq fun c c' => ?_
    rw [dist_eq_norm, ← sub_smul, norm_smul, hn, mul_one, Real.norm_eq_abs, Real.dist_eq]
  -- transfer the a.e. statement along the parametrisation
  rw [ae_iff]
  refine le_antisymm ?_ zero_le
  have hbad := ae_iff.1 hae
  rw [Measure.restrict_apply' (Submodule.closed_of_finiteDimensional _).measurableSet] at hbad
  have hmap : (fun c : ℝ => c • e₀) '' {c : ℝ | ¬ μH[s - 1] (A ∩ {p | p 0 = c}) < ∞}
      ⊆ {x | ¬ μH[s - 1] (A ∩ (x +ᵥ ((ℝ ∙ e₀)ᗮ : Set (EuclideanSpace ℝ (Fin 2))))) < ∞}
        ∩ ((ℝ ∙ e₀) : Set (EuclideanSpace ℝ (Fin 2))) := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨?_, Submodule.mem_span_singleton.2 ⟨c, rfl⟩⟩
    rw [mem_setOf_eq, hcoset c]
    exact hc
  calc volume {c : ℝ | ¬ μH[s - 1] (A ∩ {p | p 0 = c}) < ∞}
      = μH[(1 : ℝ)] {c : ℝ | ¬ μH[s - 1] (A ∩ {p | p 0 = c}) < ∞} := by
        rw [hausdorffMeasure_real]
    _ = μH[(1 : ℝ)] ((fun c : ℝ => c • e₀) ''
          {c : ℝ | ¬ μH[s - 1] (A ∩ {p | p 0 = c}) < ∞}) :=
        (hfiso.hausdorffMeasure_image (Or.inl zero_le_one) _).symm
    _ ≤ μH[(1 : ℝ)] ({x | ¬ μH[s - 1]
          (A ∩ (x +ᵥ ((ℝ ∙ e₀)ᗮ : Set (EuclideanSpace ℝ (Fin 2))))) < ∞}
        ∩ ((ℝ ∙ e₀) : Set (EuclideanSpace ℝ (Fin 2)))) := measure_mono hmap
    _ = 0 := hbad
