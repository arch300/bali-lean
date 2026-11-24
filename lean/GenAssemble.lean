import P699.TNonzero

/-!
# A generic assembly for semiseparable skew Gram matrices (Bali lab, 2026-11-02)
If `⟨e_s, e_t⟩ = τ_s w_t` for `s < t` (except possibly `(s,t) = (0,1)`), then with
`g_j = e_{2j+1} - (τ_{2j+1}/τ_{2j}) e_{2j}` the rows `e_{2i}, g_j` satisfy the hypotheses of de Bruijn:
`⟨g_i,g_j⟩ = 0`, and `⟨e_{2i},g_j⟩` is upper triangular with diagonal `⟨e_{2i},e_{2i+1}⟩`.
-/

open Finset Polynomial Matrix

namespace Bali.GA
open Bali.Skew Bali.EvenPsi Bali.PfP Bali.VB

variable {N : ℕ} (e : ℕ → Fin (N + 1) → ℚ) (τ w : ℕ → ℚ)

/-- the odd-slot rows. -/
def gO (j : ℕ) : Fin (N + 1) → ℚ := fun h => 1 * e (2 * j + 1) h - (τ (2 * j + 1) / τ (2 * j)) * e (2 * j) h

lemma skew_lin1 (f g h : Fin (N + 1) → ℚ) (a b : ℚ) :
    skew (fun l => a * f l - b * g l) h = a * skew f h - b * skew g h := by
  rw [Bali.OddB.skew_anti, skew_lin2, Bali.OddB.skew_anti h f, Bali.OddB.skew_anti h g]
  ring

variable (hK : ∀ s t, s < t → ¬(s = 0 ∧ t = 1) → skew (e s) (e t) = τ s * w t)

include hK in
lemma gO_e (i t : ℕ) (hi : τ (2 * i) ≠ 0) (ht : 2 * i + 1 < t) : skew (gO e τ i) (e t) = 0 := by
  unfold gO
  rw [skew_lin1, hK _ t ht (by omega), hK _ t (by omega) (by omega)]
  field_simp
  ring

include hK in
lemma gO_gO_lt (i j : ℕ) (hi : τ (2 * i) ≠ 0) (hij : i < j) : skew (gO e τ i) (gO e τ j) = 0 := by
  have e1 := gO_e e τ w hK i (2 * j + 1) hi (by omega)
  have e2 := gO_e e τ w hK i (2 * j) hi (by omega)
  have := skew_lin2 (gO e τ i) (e (2 * j + 1)) (e (2 * j)) 1 (τ (2 * j + 1) / τ (2 * j))
  rw [e1, e2, mul_zero, mul_zero, sub_zero] at this
  exact this

include hK in
lemma gO_gO (i j : ℕ) (hi : τ (2 * i) ≠ 0) (hj : τ (2 * j) ≠ 0) : skew (gO e τ i) (gO e τ j) = 0 := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact gO_gO_lt e τ w hK i j hi h
  · exact skew_self _
  · rw [Bali.OddB.skew_anti, gO_gO_lt e τ w hK j i hj h, neg_zero]

include hK in
lemma Y_low (i j : ℕ) (hj : τ (2 * j) ≠ 0) (hji : j < i) : skew (e (2 * i)) (gO e τ j) = 0 := by
  rw [Bali.OddB.skew_anti, gO_e e τ w hK j (2 * i) hj (by omega), neg_zero]

lemma Y_diag (i : ℕ) : skew (e (2 * i)) (gO e τ i) = skew (e (2 * i)) (e (2 * i + 1)) := by
  have := skew_lin2 (e (2 * i)) (e (2 * i + 1)) (e (2 * i)) 1 (τ (2 * i + 1) / τ (2 * i))
  rw [skew_self, mul_zero, sub_zero, one_mul] at this
  exact this

/-! ## the basis matrix -/

/-- coefficient matrix of polynomials `G a` (in `t`). -/
noncomputable def Bm {k : ℕ} (G : Fin k × Fin 2 → ℚ[X]) : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ :=
  fun a q => (G a).coeff (eι k q : ℕ)

lemma Bm_mul {k : ℕ} (G : Fin k × Fin 2 → ℚ[X]) (hdeg : ∀ a, (G a).natDegree ≤ (eι k a : ℕ))
    (t ν : Fin (N + 1) → ℚ) (a : Fin k × Fin 2) (h : Fin (N + 1)) :
    (Bm G * Mpow (m := k) t ν) a h = ν h * (G a).eval (t h) := by
  have hd : (G a).natDegree < 2 * k := lt_of_le_of_lt (hdeg a) (eι k a).isLt
  simp only [Matrix.mul_apply, Bm, Mpow]
  rw [show ∑ p : Fin k × Fin 2, (G a).coeff (eι k p : ℕ) * (ν h * t h ^ ((eι k p : Fin (2 * k)) : ℕ))
      = ν h * ∑ q : Fin (2 * k), (G a).coeff (q : ℕ) * t h ^ (q : ℕ) from by
    rw [mul_sum]
    rw [← Fintype.sum_equiv (eι k) (fun p => (G a).coeff (eι k p : ℕ) * (ν h * t h ^ ((eι k p : Fin (2 * k)) : ℕ)))
      (fun q => ν h * ((G a).coeff (q : ℕ) * t h ^ (q : ℕ))) (fun p => by ring)]]
  rw [Fin.sum_univ_eq_sum_range (fun q => (G a).coeff q * t h ^ q) (2 * k), ← eval_eq_sum_range' hd]

lemma det_Bm {k : ℕ} (G : Fin k × Fin 2 → ℚ[X]) (hdeg : ∀ a, (G a).natDegree ≤ (eι k a : ℕ)) :
    det (Bm G) = ∏ a, (G a).coeff (eι k a : ℕ) := by
  rw [← det_reindex_self (eι k), det_of_lowerTriangular]
  · rw [← (eι k).prod_comp]
    refine prod_congr rfl fun a _ => ?_
    simp [Bm]
  · intro p q hpq
    have hlt : p < q := OrderDual.toDual_lt_toDual.1 hpq
    simp only [reindex_apply, submatrix_apply, Bm, Equiv.apply_symm_apply]
    apply coeff_eq_zero_of_natDegree_lt
    refine lt_of_le_of_lt (hdeg _) ?_
    simpa using hlt

include hK in
/-- **The assembly.** -/
theorem assemble {k : ℕ} (t ν : Fin (N + 1) → ℚ) (ht : StrictAnti t) (G : Fin k × Fin 2 → ℚ[X])
    (hdeg : ∀ a, (G a).natDegree ≤ (eι k a : ℕ))
    (hG0 : ∀ (i : Fin k) h, ν h * (G (i, 0)).eval (t h) = e (2 * (i : ℕ)) h)
    (hG1 : ∀ (i : Fin k) h, ν h * (G (i, 1)).eval (t h) = gO e τ i h)
    (hτ : ∀ i : Fin k, τ (2 * (i : ℕ)) ≠ 0)
    (hd : ∀ i : Fin k, skew (e (2 * (i : ℕ))) (e (2 * (i : ℕ) + 1)) ≠ 0) :
    (∏ a, (G a).coeff (eι k a : ℕ)) * (sgnPairs (2 * k) * VBvol t ν (2 * k))
      = ∏ i : Fin k, skew (e (2 * (i : ℕ))) (e (2 * (i : ℕ) + 1)) := by
  set M := Bm G * Mpow (m := k) t ν with hM
  have r0 : ∀ i : Fin k, M (i, 0) = e (2 * (i : ℕ)) := fun i => funext fun h => by
    rw [hM, Bm_mul G hdeg, hG0]
  have r1 : ∀ i : Fin k, M (i, 1) = gO e τ i := fun i => funext fun h => by
    rw [hM, Bm_mul G hdeg, hG1]
  have hOO : ∀ i j, (M * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ) * Mᵀ : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) (i, 1) (j, 1) = 0 := by
    intro i j
    rw [gram_eq_skew, r1, r1]
    exact gO_gO e τ w hK _ _ (hτ i) (hτ j)
  set Y : Matrix (Fin k) (Fin k) ℚ := fun i j =>
    (M * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ) * Mᵀ : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) (i, 0) (j, 1) with hY
  have hYe : ∀ i j, Y i j = skew (e (2 * (i : ℕ))) (gO e τ j) := by
    intro i j
    simp only [hY]
    rw [gram_eq_skew, r0, r1]
  have hdet : det Y = ∏ i : Fin k, skew (e (2 * (i : ℕ))) (e (2 * (i : ℕ) + 1)) := by
    rw [det_of_upperTriangular]
    · exact prod_congr rfl fun i _ => by rw [hYe, Y_diag]
    · intro i j hji
      rw [hYe]
      exact Y_low e τ w hK _ _ (hτ j) hji
  have hU : IsUnit (det Y) := isUnit_iff_ne_zero.2 (by
    rw [hdet]; exact prod_ne_zero_iff.2 fun i _ => hd i)
  have key := VB_eq_detY (K := ℚ) t ν ht (Bm G) hOO hU
  rw [det_Bm G hdeg] at key
  rw [key]
  exact hdet

end Bali.GA

#print axioms Bali.GA.assemble
