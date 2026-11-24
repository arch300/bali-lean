import P699.ZonoK
import P699.BplusAssemble

/-!
# Main theorem `V_d(n)`: de Bruijn with the Krawtchouk rows (Bali lab, 2026-11-02)
Odd rows `K_{2j+1}`, even rows `Q_i = Σ_l κ_{i,l} K_{2l}`; the Gram block is triangular by `Ss_zero`.
-/

open Finset Polynomial Matrix

namespace Bali.ZV
open Bali.Skew Bali.EvenPsi Bali.PfP Bali.VB Bali.GA Bali.OddB Bali.OG Bali.BP Bali.ZK Bali.ZS

/-! ## generic triangular assembly -/

section Gen
variable {N : ℕ} {t ν : Fin (N + 1) → ℚ} {G : ℕ → ℚ[X]}

theorem tri_e (ht : StrictAnti t) (hdeg : ∀ p, (G p).natDegree ≤ p) (k : ℕ)
    (hOO : ∀ i j, i < k → j < k → skew (Er t ν G (2 * i + 1)) (Er t ν G (2 * j + 1)) = 0)
    (hY : ∀ i j, i < k → j < i → skew (Er t ν G (2 * i)) (Er t ν G (2 * j + 1)) = 0)
    (hd : ∀ i, i < k → skew (Er t ν G (2 * i)) (Er t ν G (2 * i + 1)) ≠ 0) :
    (∏ p ∈ range (2 * k), (G p).coeff p) * (sgnPairs (2 * k) * VBvol t ν (2 * k))
      = ∏ i ∈ range k, skew (Er t ν G (2 * i)) (Er t ν G (2 * i + 1)) := by
  have hv : ∀ (i : Fin k) (x : Fin 2), ((eι k (i, x) : Fin (2 * k)) : ℕ) = 2 * (i : ℕ) + x := fun i x => eι_val k (i, x)
  set G' : Fin k × Fin 2 → ℚ[X] := fun a => G (eι k a : ℕ) with hG'
  have hdeg' : ∀ a, (G' a).natDegree ≤ (eι k a : ℕ) := fun a => hdeg _
  set M := Bm G' * Mpow (m := k) t ν with hM
  have rw0 : ∀ a, M a = Er t ν G (eι k a : ℕ) := fun a => funext fun h => by
    rw [hM, Bm_mul G' hdeg']; rfl
  have r0 : ∀ i : Fin k, M (i, 0) = Er t ν G (2 * (i : ℕ)) := fun i => by rw [rw0, hv]; rfl
  have r1 : ∀ i : Fin k, M (i, 1) = Er t ν G (2 * (i : ℕ) + 1) := fun i => by rw [rw0, hv]; rfl
  have hOO' : ∀ i j, (M * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ) * Mᵀ : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) (i, 1) (j, 1) = 0 := by
    intro i j
    rw [gram_eq_skew, r1, r1]
    exact hOO _ _ i.isLt j.isLt
  set Y : Matrix (Fin k) (Fin k) ℚ := fun i j =>
    (M * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ) * Mᵀ : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) (i, 0) (j, 1) with hYd
  have hYe : ∀ i j, Y i j = skew (Er t ν G (2 * (i : ℕ))) (Er t ν G (2 * (j : ℕ) + 1)) := by
    intro i j
    simp only [hYd]
    rw [gram_eq_skew, r0, r1]
  have hdet : det Y = ∏ i ∈ range k, skew (Er t ν G (2 * i)) (Er t ν G (2 * i + 1)) := by
    rw [det_of_upperTriangular, ← Fin.prod_univ_eq_prod_range (fun i => skew (Er t ν G (2 * i)) (Er t ν G (2 * i + 1))) k]
    · exact prod_congr rfl fun i _ => hYe i i
    · intro i j hji
      rw [hYe]
      exact hY _ _ i.isLt hji
  have hU : IsUnit (det Y) := isUnit_iff_ne_zero.2 (by
    rw [hdet]; exact prod_ne_zero_iff.2 fun i hi => hd i (mem_range.1 hi))
  have key := VB_eq_detY (K := ℚ) t ν ht (Bm G') hOO' hU
  rw [det_Bm G' hdeg'] at key
  have e1 : ∏ a, (G' a).coeff (eι k a : ℕ) = ∏ p ∈ range (2 * k), (G p).coeff p := by
    rw [← Fin.prod_univ_eq_prod_range (fun p => (G p).coeff p),
      Fintype.prod_equiv (eι k) (fun a => (G' a).coeff (eι k a : ℕ))
        (fun q : Fin (2 * k) => (G q).coeff q) (fun a => rfl)]
  rw [e1] at key
  rw [key, hdet]

theorem tri_o (ht : StrictAnti t) (hdeg : ∀ p, (G p).natDegree ≤ p) (k : ℕ)
    (hOO : ∀ i j, i < k → j < k → skew (Er t ν G (2 * i + 1)) (Er t ν G (2 * j + 1)) = 0)
    (hY : ∀ i j, i ≤ k → j < i → skew (Er t ν G (2 * i)) (Er t ν G (2 * j + 1)) = 0)
    (hS : ∀ j, j < k → Tt t ν G (2 * j + 1) = 0)
    (hd : ∀ i, i < k → skew (Er t ν G (2 * i)) (Er t ν G (2 * i + 1)) ≠ 0)
    (hB : Tt t ν G (2 * k) ≠ 0) :
    (∏ p ∈ range (2 * k + 1), (G p).coeff p) * (sgnPairs (2 * k + 1) * VBvol t ν (2 * k + 1))
      = (∏ i ∈ range k, skew (Er t ν G (2 * i)) (Er t ν G (2 * i + 1))) * Tt t ν G (2 * k) := by
  set r : Fin (2 * k + 1) → Fin (N + 1) → ℚ := fun p h => ν h * (G p).eval (t h) with hr
  have hsl : ∀ i : Fin (k + 1), ∀ x : Fin 2, sl (m := k) (i, x) = 2 * (i : ℕ) + x := fun i x => eι_val (k + 1) (i, x)
  have row0 : ∀ i : Fin (k + 1), Ma r (i, 0) = Bali.OddB.ext (Er t ν G (2 * (i : ℕ))) := by
    intro i
    have hi := i.isLt
    have h0 : sl (m := k) (i, 0) < 2 * k + 1 := by rw [hsl]; simp; omega
    simp only [Ma, dif_pos h0]
    congr 1; funext h
    simp only [hr]
    rw [hsl]; simp only [Fin.val_zero, add_zero]
    rfl
  have row1 : ∀ i : Fin (k + 1), (i : ℕ) < k → Ma r (i, 1) = Bali.OddB.ext (Er t ν G (2 * (i : ℕ) + 1)) := by
    intro i hik
    have h1 : sl (m := k) (i, 1) < 2 * k + 1 := by rw [hsl]; simp; omega
    simp only [Ma, dif_pos h1]
    congr 1; funext h
    simp only [hr]
    rw [hsl]; simp only [Fin.val_one]
    rfl
  have rowL : Ma r (Fin.last k, 1) = dI := by
    have h1 : ¬ sl (m := k) (Fin.last k, 1) < 2 * k + 1 := by rw [hsl]; simp
    simp only [Ma, dif_neg h1]
  have hOO' : ∀ i j : Fin (k + 1), (Ma r * (signM (N + 1) : Matrix _ _ ℚ) * (Ma r)ᵀ :
      Matrix (Fin (k + 1) × Fin 2) (Fin (k + 1) × Fin 2) ℚ) (i, 1) (j, 1) = 0 := by
    intro i j
    rw [gram_eq_skew]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · rw [row1 _ (by simp), row1 _ (by simp), skew_ext_ext]; exact hOO _ _ (by simp) (by simp)
    · rw [row1 _ (by simp), rowL, skew_ext_dI]; exact hS _ (by simp)
    · rw [rowL, row1 _ (by simp), skew_dI_ext]
      have := hS (j' : ℕ) (by simp)
      rw [Fin.val_castSucc]
      change -(Tt t ν G (2 * (j' : ℕ) + 1)) = 0
      rw [this, neg_zero]
    · rw [rowL, skew_dI_dI]
  set Y : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ := fun i j => (Ma r * (signM (N + 1) : Matrix _ _ ℚ) * (Ma r)ᵀ :
      Matrix (Fin (k + 1) × Fin 2) (Fin (k + 1) × Fin 2) ℚ) (i, 0) (j, 1) with hYd
  have hYc : ∀ i j : Fin (k + 1), (j : ℕ) < k → Y i j = skew (Er t ν G (2 * (i : ℕ))) (Er t ν G (2 * (j : ℕ) + 1)) := by
    intro i j hj
    simp only [hYd]; rw [gram_eq_skew, row0, row1 j hj, skew_ext_ext]
  have hYL : ∀ i : Fin (k + 1), Y i (Fin.last k) = Tt t ν G (2 * (i : ℕ)) := by
    intro i
    simp only [hYd]; rw [gram_eq_skew, row0, rowL, skew_ext_dI]; rfl
  have hdet : det Y = (∏ i ∈ range k, skew (Er t ν G (2 * i)) (Er t ν G (2 * i + 1))) * Tt t ν G (2 * k) := by
    rw [det_of_upperTriangular, Fin.prod_univ_castSucc,
      ← Fin.prod_univ_eq_prod_range (fun i => skew (Er t ν G (2 * i)) (Er t ν G (2 * i + 1))) k]
    · congr 1
      · refine prod_congr rfl fun i _ => ?_
        rw [hYc _ _ (by simp), Fin.val_castSucc]
      · rw [hYL, Fin.val_last]
    · intro i j hji
      have hj : (j : ℕ) < k := by have := i.isLt; have : (j : ℕ) < i := hji; omega
      rw [hYc _ _ hj]
      exact hY _ _ (by have := i.isLt; omega) hji
  have hU : IsUnit (det Y) := by
    rw [isUnit_iff_ne_zero, hdet]
    exact mul_ne_zero (prod_ne_zero_iff.2 fun i hi => hd i (mem_range.1 hi)) hB
  have key : (∏ p : Fin (2 * k + 1), (G p).coeff p) * (sgnPairs (2 * k + 1) * VBvol t ν (2 * k + 1)) = det Y :=
    odd_assemble (k := k) G hdeg t ν ht hOO' hU
  rw [hdet] at key
  rw [← key, ← Fin.prod_univ_eq_prod_range (fun p => (G p).coeff p)]

end Gen

/-! ## polynomials in `-x` -/

lemma coeff_neg (H : ℚ[X]) (k : ℕ) : (H.comp (-X)).coeff k = (-1) ^ k * H.coeff k := by
  rw [show (-X : ℚ[X]) = C (-1) * X by simp, comp_C_mul_X_coeff]; ring

lemma deg_neg (H : ℚ[X]) (p : ℕ) (h : H.natDegree ≤ p) : (H.comp (-X)).natDegree ≤ p := by
  refine natDegree_comp_le.trans ?_
  rw [natDegree_neg, natDegree_X, mul_one]; exact h

/-! ## the rows -/

def tZ (n : ℕ) : Fin (n + 1) → ℚ := fun x => -((x : ℕ) : ℚ)
def nuZ (n : ℕ) : Fin (n + 1) → ℚ := fun x => (n.choose (x : ℕ) : ℚ)

lemma tZ_anti (n : ℕ) : StrictAnti (tZ n) := by
  intro a b hab
  have : ((a : ℕ) : ℚ) < (b : ℕ) := by exact_mod_cast hab
  simp only [tZ]; linarith

noncomputable def kap (n i l : ℕ) : ℚ := a n i l * (-1) ^ l / (n.choose (2 * l) : ℚ)

noncomputable def Q (n i : ℕ) : ℚ[X] := ∑ l ∈ range (i + 1), C (kap n i l) * Pk n (2 * l)

noncomputable def Gz (n p : ℕ) : ℚ[X] :=
  if p % 2 = 0 then (Q n (p / 2)).comp (-X) else (Pk n p).comp (-X)

lemma Q_deg (n i : ℕ) : (Q n i).natDegree ≤ 2 * i :=
  natDegree_sum_le_of_forall_le _ _ fun l hl =>
    (natDegree_C_mul_le _ _).trans ((Pk_deg n _).trans (by have := mem_range.1 hl; omega))

lemma Gz_deg (n p : ℕ) : (Gz n p).natDegree ≤ p := by
  unfold Gz
  split_ifs
  · exact deg_neg _ _ ((Q_deg n _).trans (by omega))
  · exact deg_neg _ _ (Pk_deg n p)

lemma Q_coeff (n i : ℕ) : (Q n i).coeff (2 * i) = kap n i i * ((-2) ^ (2 * i) / ((2 * i).factorial : ℚ)) := by
  rw [Q, finsetSum_coeff, sum_range_succ, coeff_C_mul, Pk_lead, sum_eq_zero, zero_add]
  intro l hl
  rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by have := Pk_deg n (2 * l); have := mem_range.1 hl; omega), mul_zero]

lemma Er_odd (n j : ℕ) : Er (tZ n) (nuZ n) (Gz n) (2 * j + 1) = Kr n (2 * j + 1) := by
  funext x
  simp [Er, Gz, tZ, nuZ, Kr, eval_comp, show (2 * j + 1) % 2 = 1 by omega]

lemma Er_even (n i : ℕ) : Er (tZ n) (nuZ n) (Gz n) (2 * i)
    = fun x => ∑ l ∈ range (i + 1), kap n i l * Kr n (2 * l) x := by
  funext x
  simp only [Er, Gz, show (2 * i) % 2 = 0 by omega, if_true, show 2 * i / 2 = i by omega, eval_comp, tZ, nuZ, Kr,
    eval_neg, eval_X, neg_neg, Q, eval_finsetSum, eval_mul, eval_C, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

lemma skew_sum_left {N : ℕ} (s : Finset ℕ) (c : ℕ → ℚ) (f : ℕ → Fin (N + 1) → ℚ) (g : Fin (N + 1) → ℚ) :
    skew (fun x => ∑ l ∈ s, c l * f l x) g = ∑ l ∈ s, c l * skew (f l) g := by
  unfold skew
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun l _ => sum_congr rfl fun k _ => ?_
  ring

/-- the even row against an odd row. -/
theorem skQ (n i j : ℕ) (hi : 2 * i ≤ n) (hj : 2 * j + 1 ≤ n) :
    skew (Er (tZ n) (nuZ n) (Gz n) (2 * i)) (Kr n (2 * j + 1))
      = -((-1) ^ j * (n.choose (2 * j + 1) : ℚ) * ((2 * n).choose n : ℚ) * Ss n i j) := by
  rw [Er_even, skew_sum_left, Ss, mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun l hl => ?_
  have hl' : l ≤ i := by have := mem_range.1 hl; omega
  have hc : (n.choose (2 * l) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  rw [gram_K n (2 * l) (2 * j + 1) (by omega) (by omega) hj,
    show 2 * l + (2 * j + 1) - 1 = 2 * (l + j) by omega, m_closed n (l + j) (by omega), kap]
  have e1 : (-1 : ℚ) ^ (2 * j + 1) = -1 := by rw [pow_succ, pow_mul]; simp
  have e2 : (-1 : ℚ) ^ l * (-1) ^ l = 1 := by rw [← mul_pow]; simp
  rw [e1, pow_add, div_mul_eq_mul_div, div_eq_iff hc]
  linear_combination (-(a n i l) * (n.choose (2 * j + 1) : ℚ) * ((2 * n).choose n : ℚ) * (-1) ^ j * mu n (l + j) * (n.choose (2 * l) : ℚ)) * e2

lemma mu_ne (n : ℕ) : ∀ r, mu n r ≠ 0
  | 0 => by simp [mu]
  | r + 1 => by
    rw [mu]
    have : 2 * (r : ℚ) + 1 ≠ 0 := by positivity
    exact mul_ne_zero (mu_ne n r) (div_ne_zero this (oddne n r))

lemma a_ne (n i : ℕ) : ∀ l, l ≤ i → a n i l ≠ 0
  | 0, _ => by simp [a]
  | l + 1, h => by
    rw [a]
    have d1 : (l : ℚ) + 1 ≠ 0 := by positivity
    have d2 : 2 * (l : ℚ) + 1 ≠ 0 := by positivity
    have d3 : (i : ℚ) - l ≠ 0 := by
      have : (l : ℚ) + 1 ≤ i := by exact_mod_cast h
      intro e; linarith
    exact mul_ne_zero (a_ne n i l (by omega))
      (div_ne_zero (neg_ne_zero.2 (mul_ne_zero d3 (odd1 n i l))) (mul_ne_zero d1 d2))

lemma Ss_ne (n i : ℕ) (h : 2 * i + 1 ≤ n) : Ss n i i ≠ 0 := by
  rw [Ss_closed]
  refine mul_ne_zero (mu_ne n i) (prod_ne_zero_iff.2 fun t ht => ?_)
  have ht' := mem_range.1 ht
  have h1 : (t : ℚ) < i := by exact_mod_cast ht'
  have h2 : (t : ℚ) < n := by exact_mod_cast (by omega : t < n)
  have d1 : (t : ℚ) - i ≠ 0 := by intro e; linarith
  have d2 : (n : ℚ) - t ≠ 0 := by intro e; linarith
  have d3 : 2 * (t : ℚ) + 1 ≠ 0 := by positivity
  unfold rho
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) d1) d2) (mul_ne_zero d3 (odd2 n t i))

lemma Tt_even (n k : ℕ) (hk : 2 * k ≤ n) : Tt (tZ n) (nuZ n) (Gz n) (2 * k) = 2 ^ n := by
  rw [Tt, Er_even]
  simp only
  rw [sum_comm, sum_range_succ']
  have hz : ∀ l ∈ range k, ∑ x, kap n k (l + 1) * Kr n (2 * (l + 1)) x = 0 := by
    intro l hl
    rw [← mul_sum, total_K n _ (by omega) (by have := mem_range.1 hl; omega), mul_zero]
  rw [sum_eq_zero hz, zero_add, ← mul_sum, show 2 * 0 = 0 from rfl, total_K0]
  simp [kap, a]

/-! ## the values -/

/-- the leading coefficient of an even row. -/
noncomputable def cfE (n i : ℕ) : ℚ := |a n i i| / (n.choose (2 * i) : ℚ) * 4 ^ i / ((2 * i).factorial : ℚ)
noncomputable def cfO (i : ℕ) : ℚ := 2 ^ (2 * i + 1) / ((2 * i + 1).factorial : ℚ)
noncomputable def rr (n i : ℕ) : ℚ := (n.choose (2 * i + 1) : ℚ) * ((2 * n).choose n : ℚ) * |Ss n i i|

lemma cf_even (n i : ℕ) : |(Gz n (2 * i)).coeff (2 * i)| = cfE n i := by
  simp only [Gz, show (2 * i) % 2 = 0 by omega, if_true, show 2 * i / 2 = i by omega]
  rw [coeff_neg, Q_coeff, kap, cfE, show (-1 : ℚ) ^ (2 * i) = 1 by rw [pow_mul]; simp, one_mul,
    show (-2 : ℚ) ^ (2 * i) = 4 ^ i by rw [pow_mul]; norm_num]
  rw [abs_mul, abs_div, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one, Nat.abs_cast, Nat.abs_cast,
    abs_of_pos (by positivity : (0 : ℚ) < 4 ^ i)]
  ring

lemma cf_odd (n i : ℕ) : |(Gz n (2 * i + 1)).coeff (2 * i + 1)| = cfO i := by
  simp only [Gz, show (2 * i + 1) % 2 = 1 by omega, one_ne_zero, if_false]
  rw [coeff_neg, Pk_lead, cfO, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_div, abs_pow, abs_neg,
    Nat.abs_cast, abs_two]

lemma cfE_pos (n i : ℕ) (h : 2 * i ≤ n) : 0 < cfE n i := by
  have h1 : 0 < |a n i i| := abs_pos.2 (a_ne n i i le_rfl)
  have h2 : (0 : ℚ) < (n.choose (2 * i) : ℚ) := by exact_mod_cast Nat.choose_pos h
  unfold cfE; positivity

lemma cfO_pos (i : ℕ) : 0 < cfO i := by unfold cfO; positivity

lemma skew_diag (n i : ℕ) (h : 2 * i + 1 ≤ n) :
    |skew (Er (tZ n) (nuZ n) (Gz n) (2 * i)) (Er (tZ n) (nuZ n) (Gz n) (2 * i + 1))| = rr n i := by
  rw [Er_odd, skQ n i i (by omega) h, abs_neg, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    Nat.abs_cast, Nat.abs_cast, rr]

lemma hOOz (n i j : ℕ) (hi : 2 * i + 1 ≤ n) (hj : 2 * j + 1 ≤ n) :
    skew (Er (tZ n) (nuZ n) (Gz n) (2 * i + 1)) (Er (tZ n) (nuZ n) (Gz n) (2 * j + 1)) = 0 := by
  rw [Er_odd, Er_odd, gram_K n _ _ hi (by omega) hj, show 2 * i + 1 + (2 * j + 1) - 1 = 2 * (i + j) + 1 by omega,
    m_odd n (i + j) (by omega)]
  ring

lemma hYz (n i j : ℕ) (hi : 2 * i ≤ n) (hj : j < i) :
    skew (Er (tZ n) (nuZ n) (Gz n) (2 * i)) (Er (tZ n) (nuZ n) (Gz n) (2 * j + 1)) = 0 := by
  rw [Er_odd, skQ n i j hi (by omega), Ss_zero n i j hj]; ring

lemma prod_cf (n k : ℕ) :
    ∏ p ∈ range (2 * k), |(Gz n p).coeff p| = ∏ i ∈ range k, (cfE n i * cfO i) := by
  rw [← prod_pairs (fun p => |(Gz n p).coeff p|)]
  exact prod_congr rfl fun i _ => by rw [cf_even, cf_odd]

lemma diag_ne (n i : ℕ) (h : 2 * i + 1 ≤ n) :
    skew (Er (tZ n) (nuZ n) (Gz n) (2 * i)) (Er (tZ n) (nuZ n) (Gz n) (2 * i + 1)) ≠ 0 := by
  rw [Er_odd, skQ n i i (by omega) h]
  have c1 : (n.choose (2 * i + 1) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos h).ne'
  have c2 : ((2 * n).choose n : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) c1) c2) (Ss_ne n i h))

/-- **even `d`.** -/
theorem Vz_e (n k : ℕ) (hk : 2 * k ≤ n + 1) :
    VBvol (tZ n) (nuZ n) (2 * k) = ∏ i ∈ range k, (rr n i / (cfE n i * cfO i)) := by
  have h := congrArg abs (tri_e (t := tZ n) (ν := nuZ n) (G := Gz n) (tZ_anti n) (Gz_deg n) k
    (fun i j hi hj => hOOz n i j (by omega) (by omega))
    (fun i j hi hj => hYz n i j (by omega) hj) (fun i hi => diag_ne n i (by omega)))
  have hν : ∀ h, 0 ≤ nuZ n h := fun h => by simp [nuZ]
  rw [abs_mul, abs_mul, abs_sgn, one_mul, abs_of_nonneg (VBvol_nonneg hν _), Finset.abs_prod, Finset.abs_prod, prod_cf n k,
    prod_congr rfl (fun i hi => skew_diag n i (by have := mem_range.1 hi; omega))] at h
  have hpos : ∏ i ∈ range k, (cfE n i * cfO i) ≠ 0 := prod_ne_zero_iff.2 fun i hi =>
    (mul_pos (cfE_pos n i (by have := mem_range.1 hi; omega)) (cfO_pos i)).ne'
  rw [prod_div_distrib, eq_div_iff hpos, mul_comm]
  exact h

/-- **odd `d`.** -/
theorem Vz_o (n k : ℕ) (hk : 2 * k ≤ n) :
    VBvol (tZ n) (nuZ n) (2 * k + 1) = VBvol (tZ n) (nuZ n) (2 * k) * (2 ^ n / cfE n k) := by
  have h := congrArg abs (tri_o (t := tZ n) (ν := nuZ n) (G := Gz n) (tZ_anti n) (Gz_deg n) k
    (fun i j hi hj => hOOz n i j (by omega) (by omega))
    (fun i j hi hj => hYz n i j (by omega) hj)
    (fun j hj => by
      rw [Tt, Er_odd]; exact total_K n _ (by omega) (by omega)) (fun i hi => diag_ne n i (by omega))
    (by rw [Tt_even n k hk]; positivity))
  have hν : ∀ h, 0 ≤ nuZ n h := fun h => by simp [nuZ]
  rw [abs_mul, abs_mul, abs_mul, abs_sgn, one_mul, abs_of_nonneg (VBvol_nonneg hν _), Finset.abs_prod, Finset.abs_prod,
    prod_range_succ, prod_cf n k, Tt_even n k hk, cf_even,
    prod_congr rfl (fun i hi => skew_diag n i (by have := mem_range.1 hi; omega))] at h
  rw [abs_of_pos (by positivity : (0 : ℚ) < 2 ^ n)] at h
  rw [Vz_e n k (by omega)]
  have hpos : ∏ i ∈ range k, (cfE n i * cfO i) ≠ 0 := prod_ne_zero_iff.2 fun i hi =>
    (mul_pos (cfE_pos n i (by have := mem_range.1 hi; omega)) (cfO_pos i)).ne'
  have hc := (cfE_pos n k hk).ne'
  rw [prod_div_distrib]
  field_simp
  linear_combination h

end Bali.ZV

#print axioms Bali.ZV.Vz_e
#print axioms Bali.ZV.Vz_o
