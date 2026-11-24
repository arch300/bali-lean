import P699.BplusSkew
import P699.Christoffel

/-!
# Type B⁺: the Gram matrix of Racah polynomials is rank one below the diagonal (Bali lab, 2026-11-02)
`skew(ν' R_a, ν' R_b) = T'_a T'_b` for `b < a`, with `ν'_k = 2 C(n,k)(n-2k)` and `T'_a = Σ_k ν'_k R_a(k)`.
-/

open Finset Polynomial

namespace Bali.BP
open Bali Bali.Skew

/-! ## odd `n = 2H+1` -/

/-- `T'_a` for odd `n`. -/
def TpO (H a : ℕ) : ℚ :=
  ∑ k ∈ range (H + 1), 2 * ((2 * H + 1).choose k : ℚ) * ((2 * (H : ℚ) + 1 - 2 * k) * Bali.Racah.Rq (2 * H + 1) a k)

theorem gram_odd (H a b : ℕ) (hab : b < a) (ha : a ≤ H) :
    skew (fun k : Fin (H + 1) => 2 * ((2 * H + 1).choose k : ℚ) * ((2 * (H : ℚ) + 1 - 2 * (k : ℕ)) * Bali.Racah.Rq (2 * H + 1) a (k : ℕ)))
         (fun k : Fin (H + 1) => 2 * ((2 * H + 1).choose k : ℚ) * ((2 * (H : ℚ) + 1 - 2 * (k : ℕ)) * Bali.Racah.Rq (2 * H + 1) b (k : ℕ)))
      = TpO H a * TpO H b := by
  have hdeg : (Bali.Racah.RP (2 * H + 1) b).natDegree ≤ b := (Bali.Racah.RP_natDegree H b (by omega)).le
  obtain ⟨M, hMdeg, hM⟩ := skew_rank1 (2 * H) H b (by omega) (by omega) _ hdeg
    (fun k => (2 * (H : ℚ) + 1 - 2 * k) * Bali.Racah.Rq (2 * H + 1) a k)
  have hc : (((2 * H : ℕ) : ℚ) + 1) = 2 * (H : ℚ) + 1 := by push_cast; ring
  have hev : ∀ k : ℕ, (phiO (((2 * H : ℕ) : ℚ) + 1) (Bali.Racah.RP (2 * H + 1) b)).eval (k : ℚ)
      = (2 * (H : ℚ) + 1 - 2 * k) * Bali.Racah.Rq (2 * H + 1) b k := by
    intro k
    rw [hc, ← Bali.Racah.RP_eval]
    simp only [phiO, Bali.Even.lam, eval_mul, eval_sub, eval_C, eval_X, eval_comp]
  have e2 : (fun k : Fin (H + 1) => 2 * ((2 * H + 1).choose k : ℚ) * ((2 * (H : ℚ) + 1 - 2 * (k : ℕ)) * Bali.Racah.Rq (2 * H + 1) b (k : ℕ)))
      = (fun k : Fin (H + 1) => 2 * ((2 * H + 1).choose k : ℚ) *
          (phiO (((2 * H : ℕ) : ℚ) + 1) (Bali.Racah.RP (2 * H + 1) b)).eval ((k : ℕ) : ℚ)) :=
    funext fun k => by rw [hev]
  rw [e2]
  refine hM.trans ?_
  have hT : ∑ k ∈ range (H + 1), 2 * ((2 * H + 1).choose k : ℚ) *
      (phiO (((2 * H : ℕ) : ℚ) + 1) (Bali.Racah.RP (2 * H + 1) b)).eval (k : ℚ) = TpO H b :=
    sum_congr rfl fun k _ => by rw [hev]
  have ho := Bali.Racah.orth_poly H a ha M.natDegree M rfl (by omega)
  have hz : ∑ k ∈ range (H + 1), ((2 * H + 1).choose k : ℚ) ^ 2 *
      ((2 * (H : ℚ) + 1 - 2 * k) * Bali.Racah.Rq (2 * H + 1) a k) *
        M.eval ((k : ℚ) * ((k : ℚ) - (((2 * H : ℕ) : ℚ) + 1))) = 0 := by
    rw [← ho]; refine sum_congr rfl fun x _ => ?_
    rw [hc]; simp only [Bali.Racah.w]; ring
  rw [hT, hz, mul_zero, sub_zero]
  rfl

/-! ## even `n = 2(M+1)`: shells `k ≤ M` (the centre has weight `0`) -/

/-- `T'_a` for even `n`. -/
def TpE (M a : ℕ) : ℚ :=
  ∑ k ∈ range (M + 1), 2 * ((2 * (M + 1)).choose k : ℚ) * ((2 * ((M + 1 : ℕ) : ℚ) - 2 * k) * Bali.RE.RE (M + 1) a k)

theorem gram_even (M a b : ℕ) (hab : b < a) (ha : a ≤ M) :
    skew (fun k : Fin (M + 1) => 2 * ((2 * (M + 1)).choose k : ℚ) * ((2 * ((M + 1 : ℕ) : ℚ) - 2 * (k : ℕ)) * Bali.RE.RE (M + 1) a (k : ℕ)))
         (fun k : Fin (M + 1) => 2 * ((2 * (M + 1)).choose k : ℚ) * ((2 * ((M + 1 : ℕ) : ℚ) - 2 * (k : ℕ)) * Bali.RE.RE (M + 1) b (k : ℕ)))
      = TpE M a * TpE M b := by
  have hdeg : (Bali.Chr.RPE (M + 1) b).natDegree ≤ b := Bali.Chr.RPE_le (M + 1) b
  have hm : 2 * (M + 1) = 2 * M + 1 + 1 := by ring
  obtain ⟨Q, hQdeg, hQ⟩ := skew_rank1 (2 * M + 1) M b (by omega) (by omega) _ hdeg
    (fun k => (2 * ((M + 1 : ℕ) : ℚ) - 2 * k) * Bali.RE.RE (M + 1) a k)
  have hc : (((2 * M + 1 : ℕ) : ℚ) + 1) = 2 * ((M + 1 : ℕ) : ℚ) := by push_cast; ring
  have hev : ∀ k : ℕ, (phiO (((2 * M + 1 : ℕ) : ℚ) + 1) (Bali.Chr.RPE (M + 1) b)).eval (k : ℚ)
      = (2 * ((M + 1 : ℕ) : ℚ) - 2 * k) * Bali.RE.RE (M + 1) b k := by
    intro k
    rw [hc, ← Bali.Chr.RPE_eval]
    simp only [phiO, Bali.Even.lam, eval_mul, eval_sub, eval_C, eval_X, eval_comp]
  have e2 : (fun k : Fin (M + 1) => 2 * ((2 * (M + 1)).choose k : ℚ) * ((2 * ((M + 1 : ℕ) : ℚ) - 2 * (k : ℕ)) * Bali.RE.RE (M + 1) b (k : ℕ)))
      = (fun k : Fin (M + 1) => 2 * ((2 * M + 1 + 1).choose k : ℚ) *
          (phiO (((2 * M + 1 : ℕ) : ℚ) + 1) (Bali.Chr.RPE (M + 1) b)).eval ((k : ℕ) : ℚ)) :=
    funext fun k => by rw [hev, hm]
  have e1 : (fun k : Fin (M + 1) => 2 * ((2 * (M + 1)).choose k : ℚ) * ((2 * ((M + 1 : ℕ) : ℚ) - 2 * (k : ℕ)) * Bali.RE.RE (M + 1) a (k : ℕ)))
      = (fun k : Fin (M + 1) => 2 * ((2 * M + 1 + 1).choose k : ℚ) *
          ((2 * ((M + 1 : ℕ) : ℚ) - 2 * (k : ℕ)) * Bali.RE.RE (M + 1) a (k : ℕ))) :=
    funext fun k => by rw [hm]
  rw [e1, e2]
  refine hQ.trans ?_
  have hT : ∑ k ∈ range (M + 1), 2 * ((2 * M + 1 + 1).choose k : ℚ) *
      (phiO (((2 * M + 1 : ℕ) : ℚ) + 1) (Bali.Chr.RPE (M + 1) b)).eval (k : ℚ) = TpE M b :=
    sum_congr rfl fun k _ => by rw [hev, hm]
  have hTa : ∑ k ∈ range (M + 1), 2 * ((2 * M + 1 + 1).choose k : ℚ) *
      ((2 * ((M + 1 : ℕ) : ℚ) - 2 * k) * Bali.RE.RE (M + 1) a k) = TpE M a :=
    sum_congr rfl fun k _ => by rw [hm]
  have ho := Bali.Chr.orth_polyE M a (by omega) Q.natDegree Q rfl (by omega)
  have hz : ∑ k ∈ range (M + 1), ((2 * M + 1 + 1).choose k : ℚ) ^ 2 *
      ((2 * ((M + 1 : ℕ) : ℚ) - 2 * k) * Bali.RE.RE (M + 1) a k) *
        Q.eval ((k : ℚ) * ((k : ℚ) - (((2 * M + 1 : ℕ) : ℚ) + 1))) = 0 := by
    rw [← ho]; refine sum_congr rfl fun x _ => ?_
    rw [hc, ← hm]; simp only [Bali.REO.wE]; push_cast; ring
  rw [hT, hTa, hz, mul_zero, sub_zero]

end Bali.BP

#print axioms Bali.BP.gram_odd
#print axioms Bali.BP.gram_even
