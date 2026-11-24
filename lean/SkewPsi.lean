import P699.PfaffianPerm
import P699.Gosper

/-!
# Lemma ψ in skew-product form, step (a) (Bali lab, 2026-11-01)

The Gram matrix of de Bruijn's formula, `G = M · signM · Mᵀ`, is the skew product
`⟨f, g⟩ = Σ_k f_k (Σ_{l>k} g_l - Σ_{l<k} g_l)` of its rows.
-/

open Finset Matrix

namespace Bali.Skew
open Bali.PfP

variable {K : Type*} [Field K]

/-- skew product of two functions on the shells `Fin (N+1)`. -/
def skew {N : ℕ} (f g : Fin (N + 1) → K) : K :=
  ∑ k, f k * (∑ l ∈ Ioi k, g l - ∑ l ∈ Iio k, g l)

lemma row_signM {N : ℕ} (g : Fin (N + 1) → K) (k : Fin (N + 1)) :
    ∑ l, g l * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) K) k l = ∑ l ∈ Ioi k, g l - ∑ l ∈ Iio k, g l := by
  classical
  have e1 : Ioi k = univ.filter (fun l => k < l) := by ext; simp
  have e2 : Iio k = univ.filter (fun l => l < k) := by ext; simp
  rw [e1, e2, sum_filter, sum_filter, ← sum_sub_distrib]
  refine sum_congr rfl fun l _ => ?_
  rcases lt_trichotomy k l with h | rfl | h
  · simp [signM, h, not_lt_of_gt h]
  · simp [signM]
  · simp [signM, h, not_lt_of_gt h]

/-- **(a)** entries of the de Bruijn Gram matrix are skew products of the rows. -/
theorem gram_eq_skew {m N : ℕ} (M : Matrix (Fin m × Fin 2) (Fin (N + 1)) K) (a b : Fin m × Fin 2) :
    (M * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) K) * Mᵀ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) K) a b
      = skew (M a) (M b) := by
  rw [entry_rect]
  unfold skew
  refine sum_congr rfl fun k _ => ?_
  rw [← row_signM (M b) k, mul_sum]
  refine sum_congr rfl fun l _ => by ring

/-- with `T g = Σ g = 0` the bracket is `-(G_{≤k} + G_{<k})`. -/
lemma skew_of_total_zero {N : ℕ} (f g : Fin (N + 1) → K) (hT : ∑ l, g l = 0) :
    skew f g = -∑ k, f k * (∑ l ∈ Iic k, g l + ∑ l ∈ Iio k, g l) := by
  classical
  unfold skew
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun k _ => ?_
  have hsplit : ∑ l ∈ Ioi k, g l + ∑ l ∈ Iic k, g l = 0 := by
    rw [← hT, ← sum_union (disjoint_left.2 fun l h1 h2 => by
      simp only [mem_Ioi, mem_Iic] at h1 h2; exact absurd h1 (not_lt_of_ge h2))]
    congr 1; ext l
    simp only [mem_union, mem_Ioi, mem_Iic, mem_univ, iff_true]
    exact lt_or_ge k l
  linear_combination f k * hsplit

end Bali.Skew

namespace Bali.Skew
open Bali.PfP
/-! ## Step (b): the bracket through the Gosper quotient -/

section Bracket

/-- `x`-partial sums `P k = Σ_{x ≤ k} C(n,x) g(x)`. -/
def Psum (n : ℕ) (g : ℕ → ℚ) (k : ℕ) : ℚ := ∑ x ∈ range (k + 1), (n.choose x : ℚ) * g x

/-- the Gosper quotient `q k = P k / C(n-1,k)` (`n = m+1`). -/
noncomputable def qG (m : ℕ) (g : ℕ → ℚ) (k : ℕ) : ℚ := Psum (m + 1) g k / (m.choose k : ℚ)

/-- **(b2)**  `P k + P (k-1) = (C(n,k)/n) · (2(n-k) q k - n g k)` for `1 ≤ k ≤ m`, `n = m+1`. -/
theorem bracket_eq (m : ℕ) (g : ℕ → ℚ) (k : ℕ) (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    Psum (m + 1) g k + Psum (m + 1) g (k - 1)
      = ((m + 1).choose k : ℚ) / ((m : ℚ) + 1) * (2 * ((m : ℚ) + 1 - k) * qG m g k - ((m : ℚ) + 1) * g k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hP : Psum (m + 1) g (j + 1) = Psum (m + 1) g j + ((m + 1).choose (j + 1) : ℚ) * g (j + 1) := by
    simp [Psum, sum_range_succ]
  have hc : (m.choose (j + 1) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  -- C(m+1,j+1)(m-j) = (m+1) C(m,j+1)
  have a := Bali.choose_succ_mul_sub m j
  have hq : qG m g (j + 1) * (m.choose (j + 1) : ℚ) = Psum (m + 1) g (j + 1) := by
    simp only [qG]; field_simp
  rw [hP] at hq ⊢
  push_cast
  field_simp
  linear_combination (-2 * ((m : ℚ) + 1)) * hq + (-2 * qG m g (j + 1)) * a
end Bracket

end Bali.Skew

#print axioms Bali.Skew.gram_eq_skew
#print axioms Bali.Skew.skew_of_total_zero
#print axioms Bali.Skew.bracket_eq
