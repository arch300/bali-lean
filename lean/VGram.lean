import P699.EvenNorm
import P699.OddB

/-!
# Even `n`: the skew Gram of `V` in the basis `1, (y/4) p_a` (Bali lab, 2026-11-02)
Inner block `= Q^B/16`, and the border `⟨1,(y/4)p_j⟩_V = ⟨1,p_j⟩_B/(4n)` for `j ≥ 1`.
-/

open Finset Polynomial

namespace Bali.VG
open Bali.EvenPsi Bali.Chr Bali.Skew

variable (K : ℕ)

/-- the `V`-row of `(y/4) p`: it vanishes at the centre. -/
noncomputable def rowE (p : ℚ[X]) : Fin (K + 1 + 1) → ℚ := extZ K (fun k => rowB K p k / 4)

lemma extZ_eq_ext (φ : Fin (K + 1) → ℚ) : extZ K φ = Bali.OddB.ext φ := rfl

lemma skew_div4 {N : ℕ} (f g : Fin (N + 1) → ℚ) :
    skew (fun k => f k / 4) (fun k => g k / 4) = skew f g / 16 := by
  unfold skew
  rw [sum_div]
  refine sum_congr rfl fun k _ => ?_
  simp only [← sum_div]
  ring

/-- **inner block.** -/
theorem skew_rowE (p q : ℚ[X]) : skew (rowE K p) (rowE K q) = skew (rowB K p) (rowB K q) / 16 := by
  simp only [rowE, extZ_eq_ext]
  rw [Bali.OddB.skew_ext_ext]
  exact skew_div4 _ _

/-- the row of the constant `1` over the shells below the centre is `2C(n,k) y_k`. -/
lemma rowB_one (k : Fin (K + 1)) :
    rowB K 1 k = 2 * ((2 * K + 1 + 1).choose k : ℚ) * yv K k := by
  simp only [rowB, mul_one, Ylam, yv, add_comp, C_comp, mul_comp, X_comp, Bali.Even.lam, eval_add, eval_C,
    eval_mul, eval_X, eval_sub]
  rw [nQ_eq]
  push_cast
  ring

/-- **general border identity.** -/
theorem border (p : ℚ[X]) :
    skew (nuV K) (rowE K p)
      = skew (rowB K 1) (rowB K p) / (4 * ((2 * K + 1 + 1 : ℕ) : ℚ))
        - (((2 * K + 1 + 1 : ℕ) : ℚ) - 1) / ((2 * K + 1 + 1 : ℕ) : ℚ) * ipW K p 1 := by
  have h := L2pt K (fun k => ((Ylam K * p).comp (Bali.Even.lam (nQ K))).eval ((k : ℕ) : ℚ))
  have e1 : (fun k : Fin (K + 1) => 2 * ((2 * K + 1 + 1).choose k : ℚ) *
      ((Ylam K * p).comp (Bali.Even.lam (nQ K))).eval ((k : ℕ) : ℚ) / 4) = fun k => rowB K p k / 4 := rfl
  have e2 : (fun k : Fin (K + 1) => 2 * ((2 * K + 1 + 1).choose k : ℚ) * yv K k) = rowB K 1 :=
    funext fun k => (rowB_one K k).symm
  have e3 : (fun k : Fin (K + 1) => 2 * ((2 * K + 1 + 1).choose k : ℚ) *
      ((Ylam K * p).comp (Bali.Even.lam (nQ K))).eval ((k : ℕ) : ℚ)) = rowB K p := rfl
  rw [e1, e2, e3] at h
  have e4 : ∑ k : Fin (K + 1), ((2 * K + 1 + 1).choose k : ℚ) ^ 2 * (((2 * K + 1 + 1 : ℕ) : ℚ) - 2 * ((k : ℕ) : ℚ)) *
      ((Ylam K * p).comp (Bali.Even.lam (nQ K))).eval ((k : ℕ) : ℚ) = ipW K p 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => ((2 * K + 1 + 1).choose k : ℚ) ^ 2 * (((2 * K + 1 + 1 : ℕ) : ℚ) - 2 * (k : ℚ)) *
      ((Ylam K * p).comp (Bali.Even.lam (nQ K))).eval (k : ℚ)) (K + 1)]
    unfold ipW
    refine sum_congr rfl fun k _ => ?_
    simp only [eval_one, mul_one, nQ]
    push_cast; ring
  rw [e4] at h
  have e5 : rowE K p = extZ K (fun k => rowB K p k / 4) := rfl
  rw [e5]
  linarith

/-- **(L2) for the family.**  For `j ≥ 1` the border is proportional to `⟨1,p_j⟩_B`. -/
theorem border_pF (j : ℕ) (hj : 1 ≤ j) :
    skew (nuV K) (rowE K (pF K j))
      = skew (rowB K 1) (rowB K (pF K j)) / (4 * ((2 * K + 1 + 1 : ℕ) : ℚ)) := by
  rw [border, pF_orth K j 1 (by simp; omega)]
  ring

end Bali.VG

#print axioms Bali.VG.skew_rowE
#print axioms Bali.VG.border_pF
