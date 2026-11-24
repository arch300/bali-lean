import P699.VOdd
import P699.BplusT

/-!
# Type B⁺: generic assembly for a rank-one Gram matrix (Bali lab, 2026-11-02)
If `⟨e_s,e_r⟩ = -τ_s τ_r` for `s < r` with `τ_s = Σ e_s` (no exception), then
`(∏_{p<d} |ℓ_p|) V_d = ∏_{p<d} |τ_p|` for every `d`.
-/

open Finset Polynomial Matrix

namespace Bali.BP
open Bali.Skew Bali.EvenPsi Bali.PfP Bali.VB Bali.GA Bali.OddB Bali.OG

variable {N : ℕ} (t ν : Fin (N + 1) → ℚ) (G : ℕ → ℚ[X])

def Er (s : ℕ) : Fin (N + 1) → ℚ := fun h => ν h * (G s).eval (t h)
def Tt (s : ℕ) : ℚ := ∑ h, Er t ν G s h

noncomputable def Gr (p : ℕ) : ℚ[X] :=
  if p % 2 = 0 then G p else G p - C (Tt t ν G p / Tt t ν G (p - 1)) * G (p - 1)

variable {t ν G}

lemma Gr_deg (hdeg : ∀ p, (G p).natDegree ≤ p) (p : ℕ) : (Gr t ν G p).natDegree ≤ p := by
  unfold Gr
  split_ifs
  · exact hdeg p
  · exact (natDegree_sub_le _ _).trans (max_le (hdeg p) ((natDegree_C_mul_le _ _).trans ((hdeg _).trans (by omega))))

lemma Gr_coeff (hdeg : ∀ p, (G p).natDegree ≤ p) (p : ℕ) : (Gr t ν G p).coeff p = (G p).coeff p := by
  unfold Gr
  split_ifs with h
  · rfl
  · have hp : 1 ≤ p := by omega
    rw [coeff_sub, coeff_C_mul, coeff_eq_zero_of_natDegree_lt (p := G (p - 1)) (by have := hdeg (p - 1); omega),
      mul_zero, sub_zero]

lemma Gr_even (i : ℕ) (h : Fin (N + 1)) : ν h * (Gr t ν G (2 * i)).eval (t h) = Er t ν G (2 * i) h := by
  simp [Gr, Er]

lemma Gr_odd (i : ℕ) (h : Fin (N + 1)) :
    ν h * (Gr t ν G (2 * i + 1)).eval (t h) = gO (Er t ν G) (Tt t ν G) i h := by
  simp only [Gr, show (2 * i + 1) % 2 = 1 by omega, one_ne_zero, if_false, eval_sub, eval_mul, eval_C, gO, Er,
    Nat.add_sub_cancel]
  ring

lemma prod_pairs (f : ℕ → ℚ) : ∀ k, ∏ i ∈ range k, (f (2 * i) * f (2 * i + 1)) = ∏ p ∈ range (2 * k), f p
  | 0 => by simp
  | k + 1 => by
    rw [prod_range_succ, prod_pairs f k, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, prod_range_succ, prod_range_succ]
    ring

section total
variable (hK : ∀ s r, s < r → skew (Er t ν G s) (Er t ν G r) = Tt t ν G s * (-Tt t ν G r))

include hK in
theorem V_e (ht : StrictAnti t) (hdeg : ∀ p, (G p).natDegree ≤ p) (k : ℕ) (hτ : ∀ p, p < 2 * k → Tt t ν G p ≠ 0) :
    (∏ p ∈ range (2 * k), (G p).coeff p) * (sgnPairs (2 * k) * VBvol t ν (2 * k))
      = ∏ i ∈ range k, (Tt t ν G (2 * i) * (-Tt t ν G (2 * i + 1))) := by
  have hv : ∀ (i : Fin k) (x : Fin 2), ((eι k (i, x) : Fin (2 * k)) : ℕ) = 2 * (i : ℕ) + x := fun i x => eι_val k (i, x)
  have key := assemble (Er t ν G) (Tt t ν G) (fun r => -Tt t ν G r) (fun s r h _ => hK s r h) t ν ht
    (fun a => Gr t ν G (eι k a : ℕ)) (fun a => Gr_deg hdeg _)
    (fun i h => by rw [hv]; exact Gr_even _ h)
    (fun i h => by rw [hv]; exact Gr_odd _ h)
    (fun i => hτ _ (by have := i.isLt; omega))
    (fun i => by
      rw [hK _ _ (by omega)]
      have := i.isLt
      exact mul_ne_zero (hτ _ (by omega)) (neg_ne_zero.2 (hτ _ (by omega))))
  have e1 : ∏ a, (Gr t ν G (eι k a : ℕ)).coeff (eι k a : ℕ) = ∏ p ∈ range (2 * k), (G p).coeff p := by
    rw [← Fin.prod_univ_eq_prod_range (fun p => (G p).coeff p),
      Fintype.prod_equiv (eι k) (fun a => (Gr t ν G (eι k a : ℕ)).coeff (eι k a : ℕ))
        (fun q : Fin (2 * k) => (G q).coeff q) (fun a => Gr_coeff hdeg _)]
  rw [e1] at key
  rw [key, Fin.prod_univ_eq_prod_range (fun i => skew (Er t ν G (2 * i)) (Er t ν G (2 * i + 1))) k]
  exact prod_congr rfl fun i _ => hK _ _ (by omega)

include hK in
theorem V_o (ht : StrictAnti t) (hdeg : ∀ p, (G p).natDegree ≤ p) (k : ℕ) (hτ : ∀ p, p < 2 * k + 1 → Tt t ν G p ≠ 0) :
    (∏ p ∈ range (2 * k + 1), (G p).coeff p) * (sgnPairs (2 * k + 1) * VBvol t ν (2 * k + 1))
      = (∏ i ∈ range k, (Tt t ν G (2 * i) * (-Tt t ν G (2 * i + 1)))) * Tt t ν G (2 * k) := by
  set r : Fin (2 * k + 1) → Fin (N + 1) → ℚ := fun p h => ν h * (Gr t ν G p).eval (t h) with hr
  have hsl : ∀ i : Fin (k + 1), ∀ x : Fin 2, sl (m := k) (i, x) = 2 * (i : ℕ) + x := fun i x => eι_val (k + 1) (i, x)
  have row0 : ∀ i : Fin (k + 1), Ma r (i, 0) = Bali.OddB.ext (Er t ν G (2 * (i : ℕ))) := by
    intro i
    have hi := i.isLt
    have h0 : sl (m := k) (i, 0) < 2 * k + 1 := by rw [hsl]; simp; omega
    simp only [Ma, dif_pos h0]
    congr 1; funext h
    simp only [hr]
    rw [hsl]; simp only [Fin.val_zero, add_zero]
    exact Gr_even _ h
  have row1 : ∀ i : Fin (k + 1), (i : ℕ) < k → Ma r (i, 1) = Bali.OddB.ext (gO (Er t ν G) (Tt t ν G) i) := by
    intro i hik
    have h1 : sl (m := k) (i, 1) < 2 * k + 1 := by rw [hsl]; simp; omega
    simp only [Ma, dif_pos h1]
    congr 1; funext h
    simp only [hr]
    rw [hsl]; simp only [Fin.val_one]
    exact Gr_odd _ h
  have rowL : Ma r (Fin.last k, 1) = dI := by
    have h1 : ¬ sl (m := k) (Fin.last k, 1) < 2 * k + 1 := by rw [hsl]; simp
    simp only [Ma, dif_neg h1]
  have hK' : ∀ s r, s < r → ¬(s = 0 ∧ r = 1) →
      skew (Er t ν G s) (Er t ν G r) = Tt t ν G s * (fun r => -Tt t ν G r) r := fun s r h _ => hK s r h
  have hτ' : ∀ i : ℕ, i ≤ k → Tt t ν G (2 * i) ≠ 0 := fun i hi => hτ _ (by omega)
  have sum_g : ∀ i : ℕ, i < k → ∑ h, gO (Er t ν G) (Tt t ν G) i h = 0 := by
    intro i hi
    simp only [gO, sum_sub_distrib, ← mul_sum, one_mul]
    change Tt t ν G (2 * i + 1) - _ * Tt t ν G (2 * i) = 0
    have := hτ' i hi.le
    field_simp
    ring
  have gg : ∀ i j : ℕ, i < k → j < k → skew (gO (Er t ν G) (Tt t ν G) i) (gO (Er t ν G) (Tt t ν G) j) = 0 :=
    fun i j hi hj => gO_gO (Er t ν G) (Tt t ν G) _ hK' i j (hτ' i hi.le) (hτ' j hj.le)
  have hOO : ∀ i j : Fin (k + 1), (Ma r * (signM (N + 1) : Matrix _ _ ℚ) * (Ma r)ᵀ :
      Matrix (Fin (k + 1) × Fin 2) (Fin (k + 1) × Fin 2) ℚ) (i, 1) (j, 1) = 0 := by
    intro i j
    rw [gram_eq_skew]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · rw [row1 _ (by simp), row1 _ (by simp), skew_ext_ext]; exact gg _ _ (by simp) (by simp)
    · rw [row1 _ (by simp), rowL, skew_ext_dI]; exact sum_g _ (by simp)
    · rw [rowL, row1 _ (by simp), skew_dI_ext, sum_g _ (by simp), neg_zero]
    · rw [rowL, skew_dI_dI]
  set Y : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ := fun i j => (Ma r * (signM (N + 1) : Matrix _ _ ℚ) * (Ma r)ᵀ :
      Matrix (Fin (k + 1) × Fin 2) (Fin (k + 1) × Fin 2) ℚ) (i, 0) (j, 1) with hYd
  have hYc : ∀ i j : Fin (k + 1), (j : ℕ) < k → Y i j = skew (Er t ν G (2 * (i : ℕ))) (gO (Er t ν G) (Tt t ν G) j) := by
    intro i j hj
    simp only [hYd]; rw [gram_eq_skew, row0, row1 j hj, skew_ext_ext]
  have hYL : ∀ i : Fin (k + 1), Y i (Fin.last k) = Tt t ν G (2 * (i : ℕ)) := by
    intro i
    simp only [hYd]; rw [gram_eq_skew, row0, rowL, skew_ext_dI]; rfl
  have hdet : det Y = (∏ i ∈ range k, (Tt t ν G (2 * i) * (-Tt t ν G (2 * i + 1)))) * Tt t ν G (2 * k) := by
    rw [det_of_upperTriangular, Fin.prod_univ_castSucc,
      ← Fin.prod_univ_eq_prod_range (fun i => Tt t ν G (2 * i) * (-Tt t ν G (2 * i + 1))) k]
    · congr 1
      · refine prod_congr rfl fun i _ => ?_
        rw [hYc _ _ (by simp), Fin.val_castSucc, Y_diag, hK _ _ (by omega)]
      · rw [hYL, Fin.val_last]
    · intro i j hji
      have hj : (j : ℕ) < k := by have := i.isLt; have : (j : ℕ) < i := hji; omega
      rw [hYc _ _ hj]
      exact Y_low (Er t ν G) (Tt t ν G) _ hK' _ _ (hτ' _ hj.le) hji
  have hU : IsUnit (det Y) := by
    rw [isUnit_iff_ne_zero, hdet]
    refine mul_ne_zero (prod_ne_zero_iff.2 fun i hi => ?_) (hτ' k le_rfl)
    have := mem_range.1 hi
    exact mul_ne_zero (hτ _ (by omega)) (neg_ne_zero.2 (hτ _ (by omega)))
  have key : (∏ p : Fin (2 * k + 1), (Gr t ν G p).coeff p) * (sgnPairs (2 * k + 1) * VBvol t ν (2 * k + 1)) = det Y :=
    odd_assemble (k := k) (Gr t ν G) (Gr_deg hdeg) t ν ht hOO hU
  rw [hdet] at key
  rw [← key, ← Fin.prod_univ_eq_prod_range (fun p => (G p).coeff p)]
  congr 1
  exact prod_congr rfl fun p _ => (Gr_coeff hdeg _).symm

lemma abs_sgn (d : ℕ) : |(sgnPairs d : ℚ)| = 1 := by
  unfold sgnPairs
  simp [Finset.abs_prod]

lemma VBvol_nonneg (hν : ∀ h, 0 ≤ ν h) (d : ℕ) : 0 ≤ VBvol t ν d := by
  unfold VBvol
  refine sum_nonneg fun S _ => ?_
  split_ifs
  · exact mul_nonneg (prod_nonneg fun _ _ => hν _) (prod_nonneg fun _ _ => prod_nonneg fun _ _ => abs_nonneg _)
  · exact le_rfl

include hK in
theorem V_abs_total (ht : StrictAnti t) (hν : ∀ h, 0 ≤ ν h) (hdeg : ∀ p, (G p).natDegree ≤ p) (d : ℕ)
    (hτ : ∀ p, p < d → Tt t ν G p ≠ 0) :
    (∏ p ∈ range d, |(G p).coeff p|) * VBvol t ν d = ∏ p ∈ range d, |Tt t ν G p| := by
  rcases Nat.even_or_odd' d with ⟨k, rfl | rfl⟩
  · have h := congrArg abs (V_e hK ht hdeg k hτ)
    rw [abs_mul, abs_mul, abs_sgn, one_mul, abs_of_nonneg (VBvol_nonneg hν _), Finset.abs_prod, Finset.abs_prod] at h
    rw [h, ← prod_pairs (fun p => |Tt t ν G p|)]
    exact prod_congr rfl fun i _ => by rw [abs_mul, abs_neg]
  · have h := congrArg abs (V_o hK ht hdeg k hτ)
    rw [abs_mul, abs_mul, abs_mul, abs_sgn, one_mul, abs_of_nonneg (VBvol_nonneg hν _), Finset.abs_prod, Finset.abs_prod] at h
    rw [h, prod_range_succ, ← prod_pairs (fun p => |Tt t ν G p|)]
    congr 1
    exact prod_congr rfl fun i _ => by rw [abs_mul, abs_neg]

end total

/-- **truncated form.** Only `s < r ≤ N` are needed. -/
theorem V_abs (ht : StrictAnti t) (hν : ∀ h, 0 ≤ ν h) (hdeg : ∀ p, p ≤ N → (G p).natDegree ≤ p)
    (hK : ∀ s r, s < r → r ≤ N → skew (Er t ν G s) (Er t ν G r) = Tt t ν G s * (-Tt t ν G r))
    (d : ℕ) (hd : d ≤ N + 1) (hτ : ∀ p, p < d → Tt t ν G p ≠ 0) :
    (∏ p ∈ range d, |(G p).coeff p|) * VBvol t ν d = ∏ p ∈ range d, |Tt t ν G p| := by
  classical
  set H : ℕ → ℚ[X] := fun s => if s ≤ N then G s else 0 with hH
  have hEr : ∀ s, s ≤ N → Er t ν H s = Er t ν G s := fun s hs => by funext h; simp [Er, hH, hs]
  have hTt : ∀ s, s ≤ N → Tt t ν H s = Tt t ν G s := fun s hs => by simp only [Tt, hEr s hs]
  have hE0 : ∀ s, N < s → Er t ν H s = 0 := fun s hs => by
    funext h; simp [Er, hH, not_le.2 hs]
  have hT0 : ∀ s, N < s → Tt t ν H s = 0 := fun s hs => by simp [Tt, hE0 s hs]
  have hK' : ∀ s r, s < r → skew (Er t ν H s) (Er t ν H r) = Tt t ν H s * (-Tt t ν H r) := by
    intro s r hsr
    rcases le_or_gt r N with hr | hr
    · rw [hEr s (by omega), hEr r hr, hTt s (by omega), hTt r hr]; exact hK s r hsr hr
    · rw [hE0 r hr, hT0 r hr]; simp [skew]
  have hdeg' : ∀ p, (H p).natDegree ≤ p := fun p => by
    simp only [hH]; split_ifs with h
    · exact hdeg p h
    · simp
  have := V_abs_total hK' ht hν hdeg' d (fun p hp => by rw [hTt p (by omega)]; exact hτ p hp)
  have e1 : ∏ p ∈ range d, |(H p).coeff p| = ∏ p ∈ range d, |(G p).coeff p| :=
    prod_congr rfl fun p hp => by
      rw [show H p = G p by simp [hH, show p ≤ N by have := mem_range.1 hp; omega]]
  have e2 : ∏ p ∈ range d, |Tt t ν H p| = ∏ p ∈ range d, |Tt t ν G p| :=
    prod_congr rfl fun p hp => by rw [hTt p (by have := mem_range.1 hp; omega)]
  rw [e1, e2] at this
  exact this

end Bali.BP

#print axioms Bali.BP.V_abs
