import P699.PsiAssemble

/-!
# Even `n`: Lemma ψ and the semiseparable structure of the centre part B (Bali lab, 2026-11-02)
`n = 2K+2`, shells `h = 0..K` (the centre `h = K+1` is a single point with `y = 0`).
(1) `shell_total_even`, `psi_skew_even`: Lemma ψ for even `n`, for `g` vanishing at the centre.
(2) **(L1)** for any family `p_a` orthogonal for `W = C(n,h)²(n-2h)³`:
    `⟨p_a, p_b⟩_B · T(p_0) = T(p_b) · ⟨p_a, p_0⟩_B` for `a > b`  (i.e. `Q^B_ab = -ρ_a u_b`).
-/

open Finset Polynomial

namespace Bali.EvenPsi
open Bali Bali.Skew Bali.Psi Bali.Even Bali.PsiA

lemma shell_total_even (K : ℕ) (g : ℕ → ℚ) (hsym : ∀ x, x ≤ 2 * K + 1 + 1 → g x = g (2 * K + 1 + 1 - x))
    (hc : g (K + 1) = 0) :
    ∑ h ∈ range (K + 1), 2 * ((2 * K + 1 + 1).choose h : ℚ) * g h
      = ∑ x ∈ range (2 * K + 1 + 1 + 1), ((2 * K + 1 + 1).choose x : ℚ) * g x := by
  rw [show 2 * K + 1 + 1 + 1 = (K + 1 + 1) + (K + 1) by ring,
    sum_range_add (fun x => ((2 * K + 1 + 1).choose x : ℚ) * g x) (K + 1 + 1) (K + 1),
    sum_range_succ (fun x => ((2 * K + 1 + 1).choose x : ℚ) * g x) (K + 1)]
  have hmid : ((2 * K + 1 + 1).choose (K + 1) : ℚ) * g (K + 1) = 0 := by rw [hc, mul_zero]
  have hrefl : ∑ x ∈ range (K + 1), ((2 * K + 1 + 1).choose (K + 1 + 1 + x) : ℚ) * g (K + 1 + 1 + x)
      = ∑ x ∈ range (K + 1), ((2 * K + 1 + 1).choose x : ℚ) * g x := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun x hx => ?_
    have hx' := mem_range.1 hx
    have e : K + 1 + 1 + (K + 1 - 1 - x) = 2 * K + 1 + 1 - x := by omega
    rw [e, Nat.choose_symm (by omega), hsym x (by omega)]
  rw [hmid, add_zero, hrefl, ← sum_add_distrib]
  exact sum_congr rfl fun x _ => by ring

/-- **Lemma ψ, even `n = 2K+2`**, for `g = G(λ)` vanishing at the centre. -/
theorem psi_skew_even (K d : ℕ) (hd1 : 1 ≤ d) (hdK : d ≤ K) (G : ℚ[X]) (hG : G.natDegree ≤ d)
    (htot : totL (2 * K + 1 + 1) (G.comp (lam (((2 * K + 1 : ℕ) : ℚ) + 1))) = 0)
    (hc : (G.comp (lam (((2 * K + 1 : ℕ) : ℚ) + 1))).eval ((K : ℚ) + 1) = 0) (f : ℕ → ℚ) :
    ∃ Q : ℚ[X], Q.natDegree ≤ d - 1 ∧
      skew (fun k : Fin (K + 1) => 2 * ((2 * K + 1 + 1).choose k : ℚ) * f k)
           (fun k : Fin (K + 1) => 2 * ((2 * K + 1 + 1).choose k : ℚ) *
              (G.comp (lam (((2 * K + 1 : ℕ) : ℚ) + 1))).eval (k : ℚ))
        = -4 * ∑ k ∈ range (K + 1), ((2 * K + 1 + 1).choose k : ℚ) ^ 2 *
            ((((2 * K + 1 : ℕ) : ℚ) + 1) - 2 * k) * f k *
            Q.eval ((k : ℚ) * ((k : ℚ) - (((2 * K + 1 : ℕ) : ℚ) + 1))) := by
  set m := 2 * K + 1 with hm
  set g := G.comp (lam ((m : ℚ) + 1)) with hgdef
  obtain ⟨q, hphi, -, -, Q, hQdeg, hN⟩ := psi_poly m d hd1 (by omega) G hG htot
  refine ⟨Q, hQdeg, ?_⟩
  have hgsym : ∀ x, x ≤ m + 1 → g.eval (x : ℚ) = g.eval ((m + 1 - x : ℕ) : ℚ) := by
    intro x hx
    have := congrArg (eval (x : ℚ)) (show g.comp (C ((m : ℚ) + 1) - X) = g by rw [hgdef, comp_assoc, lam_symm])
    rw [eval_comp] at this; simp only [eval_sub, eval_C, eval_X] at this
    rw [Nat.cast_sub hx]; push_cast; rw [← this]
  have htotal : ∑ l : Fin (K + 1), 2 * ((m + 1).choose l : ℚ) * g.eval (l : ℚ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun l => 2 * ((m + 1).choose l : ℚ) * g.eval (l : ℚ)) (K + 1),
      shell_total_even K (fun x => g.eval (x : ℚ)) (by intro x hx; exact hgsym x (by omega))
        (by simpa using hc)]
    rw [totL_apply] at htot
    simpa using htot
  rw [skew_of_total_zero _ _ htotal]
  have hk : ∀ k : Fin (K + 1),
      2 * ((m + 1).choose (k : ℕ) : ℚ) * f k *
        (∑ l ∈ Iic k, 2 * ((m + 1).choose (l : ℕ) : ℚ) * g.eval ((l : ℕ) : ℚ) +
         ∑ l ∈ Iio k, 2 * ((m + 1).choose (l : ℕ) : ℚ) * g.eval ((l : ℕ) : ℚ))
      = 4 * (((m + 1).choose (k : ℕ) : ℚ) ^ 2 * (((m : ℚ) + 1) - 2 * (k : ℕ)) * f k *
          Q.eval (((k : ℕ) : ℚ) * (((k : ℕ) : ℚ) - ((m : ℚ) + 1)))) := by
    intro k
    have hkm : (k : ℕ) ≤ m := by have := k.isLt; omega
    rw [sum_Iic_fin (fun x => 2 * ((m + 1).choose x : ℚ) * g.eval (x : ℚ)) k,
      sum_Iio_fin (fun x => 2 * ((m + 1).choose x : ℚ) * g.eval (x : ℚ)) k]
    have hP : ∑ x ∈ range ((k : ℕ) + 1), 2 * ((m + 1).choose x : ℚ) * g.eval (x : ℚ)
        = 2 * Psum (m + 1) (fun x => g.eval (x : ℚ)) k := by
      rw [Psum, mul_sum]; exact sum_congr rfl fun x _ => by ring
    have hP' : ∑ x ∈ range (k : ℕ), 2 * ((m + 1).choose x : ℚ) * g.eval (x : ℚ)
        = 2 * (if (k : ℕ) = 0 then 0 else Psum (m + 1) (fun x => g.eval (x : ℚ)) ((k : ℕ) - 1)) := by
      split_ifs with h0
      · rw [h0]; simp
      · obtain ⟨j, hj⟩ : ∃ j, (k : ℕ) = j + 1 := ⟨(k : ℕ) - 1, by omega⟩
        rw [hj, Nat.add_sub_cancel, Psum, mul_sum]; exact sum_congr rfl fun x _ => by ring
    rw [hP, hP', ← mul_add, bracket_Q m g q Q hphi hN k hkm]
    ring
  rw [sum_congr rfl fun k _ => hk k, ← mul_sum,
    Fin.sum_univ_eq_sum_range (fun k => ((m + 1).choose k : ℚ) ^ 2 * (((m : ℚ) + 1) - 2 * k) * f k *
      Q.eval ((k : ℚ) * ((k : ℚ) - ((m : ℚ) + 1)))) (K + 1)]
  ring

/-! ## (L1) the semiseparable structure -/

variable (K : ℕ)

/-- `n` as a rational. -/
abbrev nQ : ℚ := ((2 * K + 1 : ℕ) : ℚ) + 1
/-- `y = n² + 4λ` as a polynomial in `λ`. -/
noncomputable def Ylam : ℚ[X] := C (nQ K ^ 2) + C 4 * X
/-- the B-row of `p`: shell `k ↦ 2C(n,k) · (y p)(λ(k))`. -/
noncomputable def rowB (p : ℚ[X]) : Fin (K + 1) → ℚ :=
  fun k => 2 * ((2 * K + 1 + 1).choose k : ℚ) * ((Ylam K * p).comp (lam (nQ K))).eval (k : ℚ)
/-- `T(p) = Σ_x C(n,x) y_x p(λ_x)`. -/
noncomputable def TB (p : ℚ[X]) : ℚ := totL (2 * K + 1 + 1) ((Ylam K * p).comp (lam (nQ K)))
/-- the orthogonality pairing for `W = C(n,h)²(n-2h)·y`. -/
noncomputable def ipW (p Q : ℚ[X]) : ℚ :=
  ∑ k ∈ range (K + 1), ((2 * K + 1 + 1).choose k : ℚ) ^ 2 * (nQ K - 2 * k) *
    ((Ylam K * p).comp (lam (nQ K))).eval (k : ℚ) * Q.eval ((k : ℚ) * ((k : ℚ) - nQ K))

lemma skew_lin2 {N : ℕ} (f g h : Fin (N + 1) → ℚ) (a b : ℚ) :
    skew f (fun l => a * g l - b * h l) = a * skew f g - b * skew f h := by
  unfold skew
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  simp only [sum_sub_distrib, ← mul_sum]
  ring

lemma Ylam_centre : ((Ylam K).comp (lam (nQ K))).eval ((K : ℚ) + 1) = 0 := by
  simp only [Ylam, lam, add_comp, C_comp, mul_comp, X_comp, eval_add, eval_C, eval_mul, eval_X, eval_sub, nQ]
  push_cast; ring

/-- **(L1)**  For a family orthogonal for `W`, `⟨p_a,p_b⟩_B T(p_0) = T(p_b) ⟨p_a,p_0⟩_B` whenever `a > b`, `b+1 ≤ K`. -/
theorem L1 (p : ℕ → ℚ[X]) (hdeg : ∀ a, (p a).natDegree ≤ a)
    (horth : ∀ a (Q : ℚ[X]), Q.natDegree < a → ipW K (p a) Q = 0)
    (a b : ℕ) (hab : b < a) (hbK : b + 1 ≤ K) :
    skew (rowB K (p a)) (rowB K (p b)) * TB K (p 0) = TB K (p b) * skew (rowB K (p a)) (rowB K (p 0)) := by
  set gt : ℚ[X] := C (TB K (p 0)) * p b - C (TB K (p b)) * p 0 with hgt
  have hdeg_gt : (Ylam K * gt).natDegree ≤ b + 1 := by
    have h1 : (Ylam K).natDegree ≤ 1 := by
      unfold Ylam; compute_degree!
    have h2 : gt.natDegree ≤ b := by
      rw [hgt]
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_C_mul_le _ _).trans (hdeg b)
      · exact (natDegree_C_mul_le _ _).trans ((hdeg 0).trans (Nat.zero_le _))
    calc (Ylam K * gt).natDegree ≤ (Ylam K).natDegree + gt.natDegree := natDegree_mul_le
      _ ≤ b + 1 := by omega
  have htot : totL (2 * K + 1 + 1) ((Ylam K * gt).comp (lam (((2 * K + 1 : ℕ) : ℚ) + 1))) = 0 := by
    rw [hgt]
    simp only [mul_sub, sub_comp, mul_comp, C_comp, map_sub]
    have e1 : ∀ c (r : ℚ[X]), totL (2 * K + 1 + 1) ((Ylam K).comp (lam (nQ K)) * (C c * r.comp (lam (nQ K))))
        = c * TB K r := by
      intro c r
      rw [TB, mul_comp, show (Ylam K).comp (lam (nQ K)) * (C c * r.comp (lam (nQ K)))
        = C c * ((Ylam K).comp (lam (nQ K)) * r.comp (lam (nQ K))) by ring, ← smul_eq_C_mul, map_smul, smul_eq_mul]
    rw [e1, e1]; ring
  have hc : ((Ylam K * gt).comp (lam (((2 * K + 1 : ℕ) : ℚ) + 1))).eval ((K : ℚ) + 1) = 0 := by
    rw [mul_comp, eval_mul]
    have := Ylam_centre K
    simp only [nQ] at this
    rw [this, zero_mul]
  obtain ⟨Q, hQ, hpsi⟩ := psi_skew_even K (b + 1) (by omega) hbK (Ylam K * gt) hdeg_gt htot hc
    (fun k => ((Ylam K * p a).comp (lam (nQ K))).eval (k : ℚ))
  have hlhs : skew (rowB K (p a)) (fun k : Fin (K + 1) => 2 * ((2 * K + 1 + 1).choose k : ℚ) *
      ((Ylam K * gt).comp (lam (((2 * K + 1 : ℕ) : ℚ) + 1))).eval (k : ℚ))
      = TB K (p 0) * skew (rowB K (p a)) (rowB K (p b)) - TB K (p b) * skew (rowB K (p a)) (rowB K (p 0)) := by
    rw [← skew_lin2]
    congr 1
    funext l
    simp only [rowB, hgt, mul_sub, sub_comp, mul_comp, C_comp, eval_sub, eval_mul, eval_C, nQ]
    ring
  have hzero : ipW K (p a) Q = 0 := horth a Q (by omega)
  unfold ipW at hzero
  have := hpsi
  rw [show (fun k : Fin (K + 1) => 2 * ((2 * K + 1 + 1).choose k : ℚ) *
      ((Ylam K * p a).comp (lam (nQ K))).eval (k : ℚ)) = rowB K (p a) from rfl] at this
  rw [hlhs, hzero, mul_zero] at this
  linear_combination this

/-! ## (L2) ingredient: the telescoping identity behind the border -/

/-- `Σ_{x<h} C(n,x)(n - (n-2x)²) = -h(n+1-2h) C(n,h)`. -/
theorem tel_border (n : ℕ) : ∀ h : ℕ,
    ∑ x ∈ range h, (n.choose x : ℚ) * ((n : ℚ) - ((n : ℚ) - 2 * x) ^ 2)
      = -(h : ℚ) * ((n : ℚ) + 1 - 2 * h) * (n.choose h : ℚ)
  | 0 => by simp
  | h + 1 => by
    rw [sum_range_succ, tel_border n h]
    have key : ((n.choose (h + 1) : ℕ) : ℚ) * ((h : ℚ) + 1) = (n.choose h : ℚ) * (((n - h : ℕ) : ℚ)) := by
      exact_mod_cast Nat.choose_succ_right_eq n h
    rcases le_or_gt h n with hh | hh
    · rw [Nat.cast_sub hh] at key
      push_cast
      linear_combination ((n : ℚ) - 1 - 2 * h) * key
    · rw [Nat.choose_eq_zero_of_lt hh, Nat.choose_eq_zero_of_lt (by omega)]
      simp
/-! ## (L2) in Lean: the border identity, pointwise for any `φ` -/

lemma skew_col {N : ℕ} (f g : Fin (N + 1) → ℚ) :
    skew f g = ∑ l, g l * (∑ k ∈ Iio l, f k - ∑ k ∈ Ioi l, f k) := by
  have hIoi : ∀ (k : Fin (N + 1)) (h : Fin (N + 1) → ℚ), ∑ l ∈ Ioi k, h l = ∑ l, if k < l then h l else 0 := by
    intro k h; rw [← sum_filter]; congr 1; ext; simp
  have hIio : ∀ (k : Fin (N + 1)) (h : Fin (N + 1) → ℚ), ∑ l ∈ Iio k, h l = ∑ l, if l < k then h l else 0 := by
    intro k h; rw [← sum_filter]; congr 1; ext; simp
  have A : ∑ k, f k * ∑ l ∈ Ioi k, g l = ∑ l, g l * ∑ k ∈ Iio l, f k := by
    simp only [hIoi, hIio, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun l _ => sum_congr rfl fun k _ => by split_ifs <;> ring
  have B : ∑ k, f k * ∑ l ∈ Iio k, g l = ∑ l, g l * ∑ k ∈ Ioi l, f k := by
    simp only [hIoi, hIio, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun l _ => sum_congr rfl fun k _ => by split_ifs <;> ring
  unfold skew
  simp only [mul_sub, sum_sub_distrib]
  rw [A, B]

lemma sum_Ioi_eq {N : ℕ} (h : Fin (N + 1) → ℚ) (c : Fin (N + 1)) :
    ∑ k ∈ Ioi c, h k = ∑ k, h k - ∑ k ∈ Iic c, h k := by
  rw [eq_sub_iff_add_eq, ← sum_filter_add_sum_filter_not univ (fun x => c < x)]
  congr 1 <;> congr 1 <;> ext <;> simp [not_lt]

/-- the fold with the centre counted once. -/
lemma fold_even (g : ℕ → ℚ) (hsym : ∀ x, x ≤ 2 * K + 1 + 1 → g x = g (2 * K + 1 + 1 - x)) :
    ∑ h ∈ range (K + 1), 2 * ((2 * K + 1 + 1).choose h : ℚ) * g h + ((2 * K + 1 + 1).choose (K + 1) : ℚ) * g (K + 1)
      = ∑ x ∈ range (2 * K + 1 + 1 + 1), ((2 * K + 1 + 1).choose x : ℚ) * g x := by
  rw [show 2 * K + 1 + 1 + 1 = (K + 1 + 1) + (K + 1) by ring,
    sum_range_add (fun x => ((2 * K + 1 + 1).choose x : ℚ) * g x) (K + 1 + 1) (K + 1),
    sum_range_succ (fun x => ((2 * K + 1 + 1).choose x : ℚ) * g x) (K + 1)]
  have hrefl : ∑ x ∈ range (K + 1), ((2 * K + 1 + 1).choose (K + 1 + 1 + x) : ℚ) * g (K + 1 + 1 + x)
      = ∑ x ∈ range (K + 1), ((2 * K + 1 + 1).choose x : ℚ) * g x := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun x hx => ?_
    have hx' := mem_range.1 hx
    have e : K + 1 + 1 + (K + 1 - 1 - x) = 2 * K + 1 + 1 - x := by omega
    rw [e, Nat.choose_symm (by omega), hsym x (by omega)]
  rw [hrefl]
  have h2 : ∑ h ∈ range (K + 1), 2 * ((2 * K + 1 + 1).choose h : ℚ) * g h
      = ∑ x ∈ range (K + 1), ((2 * K + 1 + 1).choose x : ℚ) * g x + ∑ x ∈ range (K + 1), ((2 * K + 1 + 1).choose x : ℚ) * g x := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun x _ => by ring
  rw [h2]; ring

/-- shell weights of `V` (centre = last shell, single point). -/
def FV (x : ℕ) : ℚ := if x < K + 1 then 2 * ((2 * K + 1 + 1).choose x : ℚ) else ((2 * K + 1 + 1).choose x : ℚ)
def nuV : Fin (K + 1 + 1) → ℚ := fun x => FV K (x : ℕ)
/-- extend by `0` at the centre. -/
def extZ (φ : Fin (K + 1) → ℚ) : Fin (K + 1 + 1) → ℚ := fun x => if h : (x : ℕ) < K + 1 then φ ⟨x, h⟩ else 0
/-- `y_x = (n - 2x)²`. -/
def yv (x : ℕ) : ℚ := (((2 * K + 1 + 1 : ℕ) : ℚ) - 2 * x) ^ 2

lemma tot1 : ∑ x ∈ range (K + 1 + 1), FV K x = 2 ^ (2 * K + 1 + 1) := by
  rw [sum_range_succ, show FV K (K + 1) = ((2 * K + 1 + 1).choose (K + 1) : ℚ) by simp [FV]]
  rw [show ∑ x ∈ range (K + 1), FV K x = ∑ x ∈ range (K + 1), 2 * ((2 * K + 1 + 1).choose x : ℚ) * 1 from
    sum_congr rfl fun x hx => by simp [FV, mem_range.1 hx]]
  have := fold_even K (fun _ => (1 : ℚ)) (fun _ _ => rfl)
  simp only [mul_one] at this ⊢
  rw [this]
  exact_mod_cast Nat.sum_range_choose (2 * K + 1 + 1)

lemma tot2 : ∑ x ∈ range (K + 1), 2 * ((2 * K + 1 + 1).choose x : ℚ) * yv K x
    = ((2 * K + 1 + 1 : ℕ) : ℚ) * 2 ^ (2 * K + 1 + 1) := by
  have hf := fold_even K (yv K) (by intro x hx; simp only [yv]; rw [Nat.cast_sub hx]; ring)
  rw [show yv K (K + 1) = 0 by simp only [yv]; push_cast; ring, mul_zero, add_zero] at hf
  rw [hf]
  have ht := tel_border (2 * K + 1 + 1) (2 * K + 1 + 1 + 1)
  rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero] at ht
  have hs : ∑ x ∈ range (2 * K + 1 + 1 + 1), ((2 * K + 1 + 1).choose x : ℚ) = 2 ^ (2 * K + 1 + 1) := by
    exact_mod_cast Nat.sum_range_choose (2 * K + 1 + 1)
  simp only [mul_sub, sum_sub_distrib, ← sum_mul] at ht
  simp only [yv]
  rw [hs] at ht
  linear_combination -ht

@[simp] lemma extZ_cs (φ : Fin (K + 1) → ℚ) (k : Fin (K + 1)) : extZ K φ k.castSucc = φ k := by
  unfold extZ; rw [dif_pos (show (k.castSucc : ℕ) < K + 1 from k.isLt)]; rfl
@[simp] lemma extZ_last (φ : Fin (K + 1) → ℚ) : extZ K φ (Fin.last (K + 1)) = 0 := by simp [extZ]

/-- **(L2), pointwise:** for any `φ` on the shells `h < m`,
`⟨ν, ν φ/4⟩_V - ⟨ν y, ν φ⟩_B/(4n) = -((n-1)/n) Σ C(n,h)²(n-2h) φ_h`. -/
theorem L2pt (φ : Fin (K + 1) → ℚ) :
    skew (nuV K) (extZ K (fun k => 2 * ((2 * K + 1 + 1).choose k : ℚ) * φ k / 4))
      - skew (fun k : Fin (K + 1) => 2 * ((2 * K + 1 + 1).choose k : ℚ) * yv K k)
          (fun k => 2 * ((2 * K + 1 + 1).choose k : ℚ) * φ k) / (4 * ((2 * K + 1 + 1 : ℕ) : ℚ))
      = -((((2 * K + 1 + 1 : ℕ) : ℚ) - 1) / ((2 * K + 1 + 1 : ℕ) : ℚ)) *
          ∑ k : Fin (K + 1), ((2 * K + 1 + 1).choose k : ℚ) ^ 2 * (((2 * K + 1 + 1 : ℕ) : ℚ) - 2 * k) * φ k := by
  set n : ℚ := ((2 * K + 1 + 1 : ℕ) : ℚ) with hn
  have hn0 : n ≠ 0 := by rw [hn]; positivity
  rw [skew_col, skew_col, Fin.sum_univ_castSucc]
  simp only [extZ_cs, extZ_last, zero_mul, add_zero]
  rw [sum_div, ← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  have hl := l.isLt
  -- V-part sums
  have v1 : ∑ k ∈ Iio l.castSucc, nuV K k = ∑ x ∈ range l, 2 * ((2 * K + 1 + 1).choose x : ℚ) := by
    rw [show (∑ k ∈ Iio l.castSucc, nuV K k) = ∑ k ∈ Iio l.castSucc, FV K (k : ℕ) from rfl,
      sum_Iio_fin (FV K) l.castSucc, Fin.coe_castSucc]
    exact sum_congr rfl fun x hx => by simp [FV, show x < K + 1 by have := mem_range.1 hx; omega]
  have v2 : ∑ k ∈ Ioi l.castSucc, nuV K k
      = 2 ^ (2 * K + 1 + 1) - (∑ x ∈ range l, 2 * ((2 * K + 1 + 1).choose x : ℚ) + 2 * ((2 * K + 1 + 1).choose l : ℚ)) := by
    rw [sum_Ioi_eq, show (∑ k, nuV K k) = ∑ k : Fin (K + 1 + 1), FV K (k : ℕ) from rfl,
      Fin.sum_univ_eq_sum_range (FV K) (K + 1 + 1), tot1,
      show (∑ k ∈ Iic l.castSucc, nuV K k) = ∑ k ∈ Iic l.castSucc, FV K (k : ℕ) from rfl,
      sum_Iic_fin (FV K) l.castSucc, Fin.coe_castSucc, sum_range_succ]
    congr 2
    · exact sum_congr rfl fun x hx => by simp [FV, show x < K + 1 by have := mem_range.1 hx; omega]
    · simp [FV, hl]
  -- B-part sums
  have b1 : ∑ k ∈ Iio l, 2 * ((2 * K + 1 + 1).choose k : ℚ) * yv K k
      = ∑ x ∈ range l, 2 * ((2 * K + 1 + 1).choose x : ℚ) * yv K x :=
    sum_Iio_fin (fun x => 2 * ((2 * K + 1 + 1).choose x : ℚ) * yv K x) l
  have b2 : ∑ k ∈ Ioi l, 2 * ((2 * K + 1 + 1).choose k : ℚ) * yv K k
      = n * 2 ^ (2 * K + 1 + 1) - (∑ x ∈ range l, 2 * ((2 * K + 1 + 1).choose x : ℚ) * yv K x
          + 2 * ((2 * K + 1 + 1).choose l : ℚ) * yv K l) := by
    rw [sum_Ioi_eq, Fin.sum_univ_eq_sum_range (fun x => 2 * ((2 * K + 1 + 1).choose x : ℚ) * yv K x) (K + 1), tot2,
      sum_Iic_fin (fun x => 2 * ((2 * K + 1 + 1).choose x : ℚ) * yv K x) l, sum_range_succ]
  rw [v1, v2, b1, b2]
  have e1 : ∑ x ∈ range (l : ℕ), 2 * ((2 * K + 1 + 1).choose x : ℚ) = 2 * ∑ x ∈ range (l : ℕ), ((2 * K + 1 + 1).choose x : ℚ) := by
    rw [mul_sum]
  have e2 : ∑ x ∈ range (l : ℕ), 2 * ((2 * K + 1 + 1).choose x : ℚ) * yv K x
      = 2 * ∑ x ∈ range (l : ℕ), ((2 * K + 1 + 1).choose x : ℚ) * yv K x := by
    rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
  have ht := tel_border (2 * K + 1 + 1) l
  have e3 : ∑ x ∈ range (l : ℕ), ((2 * K + 1 + 1).choose x : ℚ) * (((2 * K + 1 + 1 : ℕ) : ℚ) - (((2 * K + 1 + 1 : ℕ) : ℚ) - 2 * x) ^ 2)
      = n * ∑ x ∈ range (l : ℕ), ((2 * K + 1 + 1).choose x : ℚ) - ∑ x ∈ range (l : ℕ), ((2 * K + 1 + 1).choose x : ℚ) * yv K x := by
    rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun x _ => by simp only [yv, hn]; ring
  rw [e3] at ht
  have hP' : ∑ x ∈ range (l : ℕ), ((2 * K + 1 + 1).choose x : ℚ) * yv K x
      = n * ∑ x ∈ range (l : ℕ), ((2 * K + 1 + 1).choose x : ℚ) + (l : ℚ) * (n + 1 - 2 * l) * ((2 * K + 1 + 1).choose (l : ℕ) : ℚ) := by
    rw [← hn] at ht; linarith
  have ey : yv K l = (n - 2 * l) ^ 2 := by simp only [yv, hn]
  rw [e1, e2, hP', ey]
  field_simp
  ring
end Bali.EvenPsi

#print axioms Bali.EvenPsi.psi_skew_even
#print axioms Bali.EvenPsi.L1
#print axioms Bali.EvenPsi.tel_border
#print axioms Bali.EvenPsi.L2pt
