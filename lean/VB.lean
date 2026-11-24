import P699.PfaffianPerm

/-!
# Step 1: the type-B volume `V^B` and the power-basis minors (Bali lab, 2026-11-01)

Shells `h = 0..H` (`n = 2H+1`), points `t_h = (n-2h)^2`, weights `ν_h = 2 C(n,h)`.
`VB H d = Σ_{|S|=d} ∏_{h∈S} ν_h ∏_{h<h' ∈ S} |t_{h'} - t_h|`.
In the power basis `M (i,b) h = ν_h t_h^(2i+b)` each maximal minor is `∏ ν · Vandermonde`.
-/

open Finset Matrix

namespace Bali.VB
open Bali.PfP

variable {K : Type*} [Field K]

/-- power-basis matrix: row `a` is the power `eι a`, column `h` a shell. -/
def Mpow {m N : ℕ} (t ν : Fin (N + 1) → K) : Matrix (Fin m × Fin 2) (Fin (N + 1)) K :=
  fun a h => ν h * t h ^ ((eι m a : Fin (2 * m)) : ℕ)

lemma det_Mpow_S {m N : ℕ} (t ν : Fin (N + 1) → K) (S : Finset (Fin (N + 1))) (hS : S.card = 2 * m) :
    det ((Mpow (m := m) t ν).submatrix id (GS S hS))
      = (∏ q : Fin (2 * m), ν (S.orderEmbOfFin hS q)) *
        ∏ i : Fin (2 * m), ∏ j ∈ Ioi i, (t (S.orderEmbOfFin hS j) - t (S.orderEmbOfFin hS i)) := by
  classical
  set g := S.orderEmbOfFin hS
  rw [← det_reindex_self (eι m)]
  have : reindex (eι m) (eι m) ((Mpow (m := m) t ν).submatrix id (GS S hS))
      = (vandermonde (fun q => t (g q)))ᵀ * diagonal (fun q => ν (g q)) := by
    ext p q
    simp [Mpow, GS, g, vandermonde, Matrix.mul_diagonal, mul_comm]
  rw [this, det_mul, det_transpose, det_diagonal, det_vandermonde, mul_comm]

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- the type-B volume over `d`-subsets of shells (points listed in increasing shell order). -/
noncomputable def VBvol {N : ℕ} (t ν : Fin (N + 1) → K) (d : ℕ) : K :=
  ∑ S ∈ (univ : Finset (Fin (N + 1))).powersetCard d,
    if h : S.card = d then (∏ q : Fin d, ν (S.orderEmbOfFin h q)) *
      ∏ i : Fin d, ∏ j ∈ Ioi i, |t (S.orderEmbOfFin h j) - t (S.orderEmbOfFin h i)| else 0

/-- the constant sign `(-1)^{C(d,2)}`, kept as a product. -/
def sgnPairs (d : ℕ) : K := ∏ i : Fin d, ∏ _j ∈ Ioi i, (-1 : K)

/-- **Step 1.**  For strictly decreasing points, the sum of the maximal power-basis minors is
`sgnPairs (2m) · V^B_{2m}`. -/
theorem sum_minors_eq_VB {m N : ℕ} (t ν : Fin (N + 1) → K) (ht : StrictAnti t) :
    ∑ S ∈ (univ : Finset (Fin (N + 1))).powersetCard (2 * m),
        det ((Mpow (m := m) t ν).submatrix id (G' (m := m) S))
      = sgnPairs (2 * m) * VBvol t ν (2 * m) := by
  classical
  unfold VBvol sgnPairs
  rw [mul_sum]
  refine sum_congr rfl fun S hS => ?_
  have h : S.card = 2 * m := (mem_powersetCard.1 hS).2
  have hG : G' (m := m) S = GS S h := by simp [G', h]
  rw [hG, det_Mpow_S t ν S h, dif_pos h]
  have hneg : ∀ i : Fin (2 * m), ∀ j ∈ Ioi i,
      t (S.orderEmbOfFin h j) - t (S.orderEmbOfFin h i)
        = (-1) * |t (S.orderEmbOfFin h j) - t (S.orderEmbOfFin h i)| := by
    intro i j hj
    have hij : i < j := mem_Ioi.1 hj
    have : t (S.orderEmbOfFin h j) < t (S.orderEmbOfFin h i) := ht ((S.orderEmbOfFin h).strictMono hij)
    rw [abs_of_neg (sub_neg.2 this)]; ring
  rw [prod_congr rfl fun i _ => prod_congr rfl (hneg i), ]
  simp only [prod_mul_distrib]
  ring

/-- basis change: the minors of `B * M` are `det B` times those of `M`. -/
lemma sum_minors_basis_change {m N : ℕ} (B : Matrix (Fin m × Fin 2) (Fin m × Fin 2) K)
    (M : Matrix (Fin m × Fin 2) (Fin (N + 1)) K) :
    ∑ S ∈ (univ : Finset (Fin (N + 1))).powersetCard (2 * m), det ((B * M).submatrix id (G' (m := m) S))
      = det B * ∑ S ∈ (univ : Finset (Fin (N + 1))).powersetCard (2 * m), det (M.submatrix id (G' (m := m) S)) := by
  rw [mul_sum]
  refine sum_congr rfl fun S _ => ?_
  rw [show (B * M).submatrix id (G' (m := m) S) = B * M.submatrix id (G' (m := m) S) by
    ext a c; simp [Matrix.mul_apply], det_mul]

/-- **Steps 1 + de Bruijn, combined.**  If the basis `B · (powers)` has a Gram matrix with zero odd–odd block and
invertible even–odd block `Y`, then `det B · sgn · V^B_{2m} = det Y`. -/
theorem VB_eq_detY [CharZero K] {m N : ℕ} (t ν : Fin (N + 1) → K) (ht : StrictAnti t)
    (B : Matrix (Fin m × Fin 2) (Fin m × Fin 2) K)
    (hOO : ∀ i j, ((B * Mpow (m := m) t ν) * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) K) *
        (B * Mpow (m := m) t ν)ᵀ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) K) (i, 1) (j, 1) = 0)
    (hY : IsUnit (det (fun i j => ((B * Mpow (m := m) t ν) * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) K) *
        (B * Mpow (m := m) t ν)ᵀ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) K) (i, 0) (j, 1) : Matrix (Fin m) (Fin m) K))) :
    det B * (sgnPairs (2 * m) * VBvol t ν (2 * m))
      = det (fun i j => ((B * Mpow (m := m) t ν) * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) K) *
          (B * Mpow (m := m) t ν)ᵀ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) K) (i, 0) (j, 1) : Matrix (Fin m) (Fin m) K) := by
  rw [← sum_minors_eq_VB t ν ht, ← sum_minors_basis_change]
  exact sum_minors_eq_det _ hOO hY

end Bali.VB

#print axioms Bali.VB.det_Mpow_S
#print axioms Bali.VB.sum_minors_eq_VB
#print axioms Bali.VB.VB_eq_detY
