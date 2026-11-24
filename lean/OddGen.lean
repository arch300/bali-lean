import P699.EvenConjB

/-!
# Generic odd assembly (Bali lab, 2026-11-02)
Rows `r_p = ν · G_p(t)` (`deg G_p ≤ p`, `p ≤ 2k`), augmented by `δ_∞`:
`(∏ coeff) · sgn · V_{2k+1} = det Y` whenever the augmented Gram satisfies de Bruijn's hypotheses.
-/

open Finset Polynomial Matrix

namespace Bali.OG
open Bali.Skew Bali.PfP Bali.VB Bali.OddB

variable {N k : ℕ}

/-- coefficient matrix of `2k+1` polynomials. -/
noncomputable def Bc (G : ℕ → ℚ[X]) : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) ℚ :=
  fun p q => (G p).coeff q

lemma det_Bc (G : ℕ → ℚ[X]) (hdeg : ∀ p, (G p).natDegree ≤ p) :
    det (Bc (k := k) G) = ∏ p : Fin (2 * k + 1), (G p).coeff p := by
  rw [det_of_lowerTriangular]
  · rfl
  · intro p q hpq
    have hlt : p < q := OrderDual.toDual_lt_toDual.1 hpq
    simp only [Bc]
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg p) hlt)

lemma det_rowsG (G : ℕ → ℚ[X]) (hdeg : ∀ p, (G p).natDegree ≤ p) (t ν : Fin (N + 1) → ℚ)
    (S : Finset (Fin (N + 1))) :
    det (Matrix.of fun p q : Fin (2 * k + 1) => ν (Go S q) * (G p).eval (t (Go S q)))
      = det (Bc (k := k) G) * ((∏ q : Fin (2 * k + 1), ν (Go S q)) *
          ∏ i : Fin (2 * k + 1), ∏ j ∈ Ioi i, (t (Go S j) - t (Go S i))) := by
  have : (Matrix.of fun p q : Fin (2 * k + 1) => ν (Go S q) * (G p).eval (t (Go S q)))
      = Bc (k := k) G * ((vandermonde (fun q => t (Go S q)))ᵀ * diagonal (fun q => ν (Go S q))) := by
    ext p q
    rw [of_apply, Matrix.mul_apply]
    have hd : (G p).natDegree < 2 * k + 1 := lt_of_le_of_lt (hdeg p) p.isLt
    rw [eval_eq_sum_range' hd, ← Fin.sum_univ_eq_sum_range (fun i => (G p).coeff i * t (Go S q) ^ i), mul_sum]
    refine sum_congr rfl fun r _ => ?_
    rw [Matrix.mul_diagonal, transpose_apply, vandermonde_apply]
    simp only [Bc]
    ring
  rw [this, det_mul, det_mul, det_transpose, det_diagonal, det_vandermonde]
  ring

lemma sum_rowsG (G : ℕ → ℚ[X]) (hdeg : ∀ p, (G p).natDegree ≤ p) (t ν : Fin (N + 1) → ℚ) (ht : StrictAnti t) :
    ∑ S ∈ (univ : Finset (Fin (N + 1))).powersetCard (2 * k + 1),
        det (Matrix.of fun p q : Fin (2 * k + 1) => ν (Go S q) * (G p).eval (t (Go S q)))
      = det (Bc (k := k) G) * (sgnPairs (2 * k + 1) * VBvol t ν (2 * k + 1)) := by
  unfold VBvol sgnPairs
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun S hS => ?_
  have h : S.card = 2 * k + 1 := (mem_powersetCard.1 hS).2
  rw [det_rowsG G hdeg t ν S, dif_pos h]
  have hGo : ∀ q, Go S q = S.orderEmbOfFin h q := fun q => by simp [Go, h]
  simp only [hGo]
  have hneg : ∀ i : Fin (2 * k + 1), ∀ j ∈ Ioi i,
      t (S.orderEmbOfFin h j) - t (S.orderEmbOfFin h i)
        = (-1) * |t (S.orderEmbOfFin h j) - t (S.orderEmbOfFin h i)| := by
    intro i j hj
    have hij : i < j := mem_Ioi.1 hj
    have : t (S.orderEmbOfFin h j) < t (S.orderEmbOfFin h i) := ht ((S.orderEmbOfFin h).strictMono hij)
    rw [abs_of_neg (sub_neg.2 this)]; ring
  rw [prod_congr rfl fun i _ => prod_congr rfl (hneg i)]
  simp only [prod_mul_distrib]
  ring

/-- **generic odd assembly.** -/
theorem odd_assemble (G : ℕ → ℚ[X]) (hdeg : ∀ p, (G p).natDegree ≤ p) (t ν : Fin (N + 1) → ℚ) (ht : StrictAnti t)
    (hOO : ∀ i j, (Ma (m := k) (fun p h => ν h * (G p).eval (t h)) * (signM (N + 1) : Matrix _ _ ℚ) *
      (Ma (m := k) (fun p h => ν h * (G p).eval (t h)))ᵀ : Matrix (Fin (k + 1) × Fin 2) (Fin (k + 1) × Fin 2) ℚ) (i, 1) (j, 1) = 0)
    (hY : IsUnit (det (fun i j => (Ma (m := k) (fun p h => ν h * (G p).eval (t h)) * (signM (N + 1) : Matrix _ _ ℚ) *
      (Ma (m := k) (fun p h => ν h * (G p).eval (t h)))ᵀ : Matrix (Fin (k + 1) × Fin 2) (Fin (k + 1) × Fin 2) ℚ) (i, 0) (j, 1)
        : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ))) :
    (∏ p : Fin (2 * k + 1), (G p).coeff p) * (sgnPairs (2 * k + 1) * VBvol t ν (2 * k + 1))
      = det (fun i j => (Ma (m := k) (fun p h => ν h * (G p).eval (t h)) * (signM (N + 1) : Matrix _ _ ℚ) *
          (Ma (m := k) (fun p h => ν h * (G p).eval (t h)))ᵀ : Matrix (Fin (k + 1) × Fin 2) (Fin (k + 1) × Fin 2) ℚ) (i, 0) (j, 1)
            : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) := by
  have key := sum_minors_eq_det _ hOO hY
  rw [sum_aug] at key
  rw [← det_Bc G hdeg, ← sum_rowsG G hdeg t ν ht, ← key]

end Bali.OG

#print axioms Bali.OG.odd_assemble
