/-
Copyright (c) 2025 Francesco Nishanil Chotuck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck
-/
import ForMathlib.Kakeya.Defs
import Mathlib.LinearAlgebra.Pi

/-!
# Covering the sup-norm sphere by images of a slope cone

The `ℝⁿ` Besicovitch construction produces a set containing, for every `v : Fin (n-1) → ℝ`
with `‖v‖ ≤ 1/2`, a segment in the direction `(v, 1) : Fin n → ℝ` (last coordinate `1`).
To turn such a set into a Kakeya set one needs the images of this **slope cone** under
finitely many invertible linear maps to cover every direction of `Fin n → ℝ`.

Working with the supremum norm on `Fin n → ℝ`, this file proves the key combinatorial fact:
every unit vector is, up to a scalar of absolute value at most one, the image of some `(v, 1)`
with `‖v‖ ≤ 1/2` under one of `2n` explicit signed, scaled coordinate permutations.

## Main results

* `exists_norm_eq_pi_norm` : on a nonempty finite product of seminormed groups some
  coordinate attains the supremum norm.
* `exists_reflectScale_smul_slopeVector` : for `w` of sup-norm `1`, there are a coordinate `i`,
  a slope `v` with `‖v‖ ≤ 1/2` and a scalar `t` with `|t| ≤ 1` such that
  `w = t • reflectScale i (slopeVector v)`.

## References

* T. W. Körner, *Besicovitch via Baire*, Studia Math. 158 (2003), no. 1, 65–78.
-/

variable {n : ℕ}

namespace Besicovitch

/-- The "slope vector" `(v, 1) : Fin (n+1) → ℝ` built from `v : Fin n → ℝ` by appending `1`
in the last coordinate. -/
def slopeVector (v : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.snoc v 1

/-- The cross-section coordinates of `slopeVector v` recover `v`. -/
@[simp] lemma slopeVector_castSucc (v : Fin n → ℝ) (i : Fin n) :
    slopeVector v i.castSucc = v i := by simp [slopeVector]

/-- The last coordinate of `slopeVector v` is `1`. -/
@[simp] lemma slopeVector_last (v : Fin n → ℝ) :
    slopeVector v (Fin.last n) = 1 := by simp [slopeVector]

/-- On a nonempty finite product of seminormed groups, some coordinate attains the
supremum norm. -/
theorem exists_norm_eq_pi_norm {ι : Type*} [Fintype ι] [Nonempty ι] {E : ι → Type*}
    [∀ i, SeminormedAddCommGroup (E i)] (w : ∀ i, E i) : ∃ i, ‖w i‖ = ‖w‖ := by
  obtain ⟨i, hi⟩ := Finite.exists_max fun i => ‖w i‖
  exact ⟨i, le_antisymm (norm_le_pi_norm w i) ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 hi)⟩

/-- Some coordinate of a vector in `Fin (m + 1) → ℝ` attains its supremum norm. -/
lemma exists_abs_eq_norm {m : ℕ} (w : Fin (m + 1) → ℝ) : ∃ i, |w i| = ‖w‖ := by
  simpa only [Real.norm_eq_abs] using exists_norm_eq_pi_norm w

/-- A unit vector (supremum norm) has a coordinate of absolute value `1`, all others `≤ 1`. -/
lemma exists_dominant_coord {w : Fin (n + 1) → ℝ} (hw : ‖w‖ = 1) :
    ∃ i : Fin (n + 1), |w i| = 1 ∧ ∀ k, |w k| ≤ 1 := by
  obtain ⟨i, hi⟩ := exists_abs_eq_norm w
  exact ⟨i, hi.trans hw, fun k => hw ▸ norm_le_pi_norm w k⟩

/-- The coordinate rearrangement sending the last coordinate into slot `i` and doubling
the remaining coordinates (rerouted through `Equiv.swap i (Fin.last n)`).  Scaling its image
of a slope vector by a suitable `t` with `|t| ≤ 1` produces any prescribed direction.
Because it is linear it maps null sets to null sets, which is all the Besicovitch
construction requires — no invertibility or determinant is needed. -/
def reflectScale (i : Fin (n + 1)) : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
  LinearMap.pi fun j =>
    if j = i then LinearMap.proj (Fin.last n)
    else (2 : ℝ) • LinearMap.proj (Equiv.swap i (Fin.last n) j)

/-- Coordinatewise value of `reflectScale`. -/
@[simp] lemma reflectScale_apply (i : Fin (n + 1)) (u : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    reflectScale i u j =
      if j = i then u (Fin.last n) else 2 * u (Equiv.swap i (Fin.last n) j) := by
  rw [reflectScale, LinearMap.pi_apply]
  split_ifs <;> simp

/-- **Direction cover.**  Every unit vector `w` of `Fin (n+1) → ℝ` (supremum norm) is, up to a
scalar `t` with `|t| ≤ 1`, the image under `reflectScale i` of a slope vector `slopeVector v`
with `‖v‖ ≤ 1/2`, for a suitable dominant coordinate `i`.  This lets a set containing
segments in every slope direction cover, after finitely many linear images and rescalings,
segments in every direction. -/
theorem exists_reflectScale_smul_slopeVector {w : Fin (n + 1) → ℝ} (hw : ‖w‖ = 1) :
    ∃ (i : Fin (n + 1)) (v : Fin n → ℝ) (t : ℝ),
      ‖v‖ ≤ 1 / 2 ∧ |t| ≤ 1 ∧ w = t • reflectScale i (slopeVector v) := by
  obtain ⟨i, hi, hle⟩ := exists_dominant_coord hw
  have hs2 : w i * w i = 1 := by rw [← abs_mul_abs_self, hi, mul_one]
  -- the slope: `v k = (w i / 2) * w (swap i last (castSucc k))`
  refine ⟨i, fun k => (w i / 2) * w (Equiv.swap i (Fin.last n) k.castSucc), w i, ?_, hi.le, ?_⟩
  · -- ‖v‖ ≤ 1/2
    rw [pi_norm_le_iff_of_nonneg one_half_pos.le]
    intro k
    rw [Real.norm_eq_abs, abs_mul, abs_div, hi, abs_two]
    linarith [hle (Equiv.swap i (Fin.last n) k.castSucc)]
  · -- the covering identity
    funext j
    rw [Pi.smul_apply, reflectScale_apply, smul_eq_mul]
    by_cases hj : j = i
    · rw [if_pos hj, slopeVector_last, mul_one, hj]
    · rw [if_neg hj]
      set p : Fin (n + 1) := Equiv.swap i (Fin.last n) j with hp
      have hpne : p ≠ Fin.last n := by
        simp [hp, Equiv.swap_apply_eq_iff, hj]
      rw [← Fin.castSucc_castPred p hpne, slopeVector_castSucc]
      simp only [Fin.castSucc_castPred, hp, Equiv.swap_apply_self]
      linear_combination (-(w j)) * hs2

end Besicovitch
