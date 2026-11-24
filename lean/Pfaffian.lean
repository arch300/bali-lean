import Mathlib

/-!
# Pfaffian, stage 1 (Bali lab, 2026-11-01)

Mathlib has no Pfaffian.  We define it for `2n × 2n` matrices by expansion along the first row:
`Pf A = Σ_{j} (-1)^j A 0 (j+1) Pf (A without rows/cols 0, j+1)`.
Checks: the `2×2` and `4×4` closed forms.  (Stages 2–6: block lemma, de Bruijn, basis change, assembly.)
-/

open Finset

namespace Bali.Pf

variable {R : Type*} [CommRing R]

/-- Pfaffian of a `2n × 2n` matrix (no skew-symmetry assumed; only the upper triangle is used). -/
def pf : (n : ℕ) → Matrix (Fin (2 * n)) (Fin (2 * n)) R → R
  | 0, _ => 1
  | n + 1, A => ∑ j : Fin (2 * n + 1), (-1) ^ (j : ℕ) * A 0 j.succ *
      pf n (A.submatrix (fun i => (j.succAbove i).succ) (fun i => (j.succAbove i).succ))

theorem pf_two (A : Matrix (Fin 2) (Fin 2) R) : pf 1 A = A 0 1 := by
  simp [pf]

theorem pf_four (A : Matrix (Fin 4) (Fin 4) R) :
    pf 2 A = A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2 := by
  simp [pf, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Homogeneity: `Pf (c • A) = c^n Pf A`. -/
theorem pf_smul (c : R) : ∀ (n : ℕ) (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R), pf n (c • A) = c ^ n * pf n A
  | 0, _ => by simp [pf]
  | n + 1, A => by
    simp only [pf]
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [show (c • A).submatrix (fun i => (j.succAbove i).succ) (fun i => (j.succAbove i).succ)
        = c • A.submatrix (fun i => (j.succAbove i).succ) (fun i => (j.succAbove i).succ) from rfl,
      pf_smul c n]
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring

/-- Stage 2: if the first row vanishes beyond column 1, the expansion has one term. -/
theorem pf_first_row (n : ℕ) (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) R)
    (h : ∀ j : Fin (2 * n + 1), j ≠ 0 → A 0 j.succ = 0) :
    pf (n + 1) A = A 0 1 * pf n (A.submatrix (fun i => i.succ.succ) (fun i => i.succ.succ)) := by
  simp only [pf]
  rw [Fintype.sum_eq_single 0 (fun j hj => by rw [h j hj]; ring)]
  simp [Fin.succAbove_zero]

/-- Stage 2: a "Pfaffian-triangular" matrix (row `2i` vanishes beyond column `2i+1`) has
`Pf = ∏ A (2i) (2i+1)`.  Stated for matrices given by a function `g : ℕ → ℕ → R`. -/
theorem pf_triangular (g : ℕ → ℕ → R) :
    ∀ n : ℕ, (∀ i k, i < n → 2 * i + 1 < k → k < 2 * n → g (2 * i) k = 0) →
      pf n (Matrix.of fun i j : Fin (2 * n) => g i j) = ∏ i ∈ range n, g (2 * i) (2 * i + 1)
  | 0, _ => by simp [pf]
  | n + 1, h => by
    rw [pf_first_row]
    · have ih := pf_triangular (fun i j => g (i + 2) (j + 2)) n (by
        intro i k hi hk hk2
        have := h (i + 1) (k + 2) (by omega) (by omega) (by omega)
        simpa [show 2 * (i + 1) = 2 * i + 2 by ring] using this)
      have hsub : (Matrix.of fun i j : Fin (2 * (n + 1)) => g i j).submatrix (fun i => i.succ.succ) (fun i => i.succ.succ)
          = Matrix.of fun i j : Fin (2 * n) => g (i + 2) (j + 2) := by
        ext i j; simp [Fin.val_succ]
      rw [hsub, ih, prod_range_succ']
      simp
      rw [Nat.mod_eq_of_lt (by omega)]
      ring
    · intro j hj
      have hj' : (j : ℕ) ≠ 0 := fun e => hj (Fin.ext e)
      simpa using h 0 (j + 1) (by omega) (by omega) (by have := j.isLt; omega)

end Bali.Pf

#print axioms Bali.Pf.pf_four
#print axioms Bali.Pf.pf_triangular
#print axioms Bali.Pf.pf_smul
