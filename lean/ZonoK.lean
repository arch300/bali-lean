import P699.ZonoS
import P699.PsiAssemble

/-!
# Main theorem `V_d(n)`: Krawtchouk polynomials and their skew products (Bali lab, 2026-11-02)
`K_a(x) = [t^a](1+t)^{n-x}(1-t)^x`.  Self-duality, and
`⟨C K_a, C K_b⟩ = C(n,a) C(n,b) (-1)^b m(a+b-1)` with `m(s) = [z^n](1+z)^{2n-s}(1-z)^s`.
-/

open Finset Polynomial

namespace Bali.ZK
open Bali.Skew Bali.PsiA

/-- `(1+X)^p (1-X)^q`. -/
noncomputable def Fp (p q : ℕ) : ℚ[X] := (1 + X) ^ p * (1 - X) ^ q

lemma Fp_succ_left (p q : ℕ) : Fp (p + 1) q = (1 + X) * Fp p q := by unfold Fp; ring
lemma Fp_succ_right (p q : ℕ) : Fp p (q + 1) = (1 - X) * Fp p q := by unfold Fp; ring

lemma coeff_one_add (G : ℚ[X]) (k : ℕ) : ((1 + X) * G).coeff (k + 1) = G.coeff (k + 1) + G.coeff k := by
  rw [add_mul, one_mul, coeff_add, coeff_X_mul]

lemma coeff_one_sub (G : ℚ[X]) (k : ℕ) : ((1 - X) * G).coeff (k + 1) = G.coeff (k + 1) - G.coeff k := by
  rw [sub_mul, one_mul, coeff_sub, coeff_X_mul]

lemma coeff_one_add0 (G : ℚ[X]) : ((1 + X) * G).coeff 0 = G.coeff 0 := by
  rw [add_mul, one_mul, coeff_add, coeff_X_mul_zero, add_zero]

lemma coeff_one_sub0 (G : ℚ[X]) : ((1 - X) * G).coeff 0 = G.coeff 0 := by
  rw [sub_mul, one_mul, coeff_sub, coeff_X_mul_zero, sub_zero]

lemma Fp_coeff0 (p q : ℕ) : (Fp p q).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero]; simp [Fp]

lemma Fp_deg (p q : ℕ) : (Fp p q).natDegree ≤ p + q := by
  unfold Fp
  refine natDegree_mul_le.trans (add_le_add ?_ ?_)
  · refine natDegree_pow_le.trans ?_
    have : (1 + X : ℚ[X]).natDegree ≤ 1 := by compute_degree
    nlinarith
  · refine natDegree_pow_le.trans ?_
    have : (1 - X : ℚ[X]).natDegree ≤ 1 := by compute_degree
    nlinarith

/-- the differential equation. -/
lemma ode (p q : ℕ) : (1 - X ^ 2) * derivative (Fp p q)
    = (C ((p : ℚ) - q) - C ((p : ℚ) + q) * X) * Fp p q := by
  induction p with
  | succ p ih =>
    rw [Fp_succ_left, derivative_mul]
    simp only [derivative_add, derivative_one, derivative_X, zero_add, one_mul]
    have e1 : (C (((p + 1 : ℕ) : ℚ) - q) : ℚ[X]) = C ((p : ℚ) - q) + 1 := by
      push_cast; rw [show (p : ℚ) + 1 - q = ((p : ℚ) - q) + 1 by ring, C_add, C_1]
    have e2 : (C (((p + 1 : ℕ) : ℚ) + q) : ℚ[X]) = C ((p : ℚ) + q) + 1 := by
      push_cast; rw [show (p : ℚ) + 1 + q = ((p : ℚ) + q) + 1 by ring, C_add, C_1]
    rw [e1, e2]
    linear_combination (1 + X) * ih
  | zero =>
    induction q with
    | zero => simp [Fp]
    | succ q ih =>
      rw [Fp_succ_right, derivative_mul]
      simp only [derivative_sub, derivative_one, derivative_X, zero_sub]
      have e1 : (C (((0 : ℕ) : ℚ) - ((q + 1 : ℕ) : ℚ)) : ℚ[X]) = C (((0 : ℕ) : ℚ) - q) - 1 := by
        push_cast; rw [show (0 : ℚ) - ((q : ℚ) + 1) = ((0 : ℚ) - q) - 1 by ring, C_sub, C_1]
      have e2 : (C (((0 : ℕ) : ℚ) + ((q + 1 : ℕ) : ℚ)) : ℚ[X]) = C (((0 : ℕ) : ℚ) + q) + 1 := by
        push_cast; rw [show (0 : ℚ) + ((q : ℚ) + 1) = ((0 : ℚ) + q) + 1 by ring, C_add, C_1]
      rw [e1, e2]
      linear_combination (1 - X) * ih

lemma rhs_coeff (u v : ℚ) (G : ℚ[X]) (k : ℕ) :
    ((C u - C v * X) * G).coeff (k + 1) = u * G.coeff (k + 1) - v * G.coeff k := by
  rw [sub_mul, mul_assoc, coeff_sub, coeff_C_mul, coeff_C_mul, coeff_X_mul]

/-- `(a+2) c_{a+2} = (p-q) c_{a+1} - (p+q-a) c_a`. -/
lemma ode_coeff (p q a : ℕ) : ((a : ℚ) + 2) * (Fp p q).coeff (a + 2)
    = ((p : ℚ) - q) * (Fp p q).coeff (a + 1) - ((p : ℚ) + q - a) * (Fp p q).coeff a := by
  have h : ((1 - X ^ 2) * derivative (Fp p q)).coeff (a + 1)
      = ((C ((p : ℚ) - q) - C ((p : ℚ) + q) * X) * Fp p q).coeff (a + 1) := by rw [ode]
  rw [rhs_coeff] at h
  have hl : ((1 - X ^ 2) * derivative (Fp p q)).coeff (a + 1)
      = ((a : ℚ) + 2) * (Fp p q).coeff (a + 2) - (a : ℚ) * (Fp p q).coeff a := by
    rw [sub_mul, one_mul, coeff_sub, coeff_derivative, mul_comm (X ^ 2), coeff_mul_X_pow']
    rcases a with _ | b
    · simp; ring
    · rw [if_pos (by omega), show b + 1 + 1 - 2 = b by omega, coeff_derivative]
      push_cast; ring
  rw [hl] at h
  linear_combination h

lemma coeff1 (p q : ℕ) : (Fp p q).coeff 1 = (p : ℚ) - q := by
  have h : ((1 - X ^ 2) * derivative (Fp p q)).coeff 0
      = ((C ((p : ℚ) - q) - C ((p : ℚ) + q) * X) * Fp p q).coeff 0 := by rw [ode]
  have hl : ((1 - X ^ 2) * derivative (Fp p q)).coeff 0 = (Fp p q).coeff 1 := by
    rw [sub_mul, one_mul, coeff_sub, coeff_derivative, mul_comm (X ^ 2), coeff_mul_X_pow']
    simp
  have hr : ((C ((p : ℚ) - q) - C ((p : ℚ) + q) * X) * Fp p q).coeff 0 = (p : ℚ) - q := by
    rw [sub_mul, mul_assoc, coeff_sub, coeff_C_mul, coeff_C_mul, coeff_X_mul_zero, Fp_coeff0]; ring
  rw [hl, hr] at h
  exact h

/-! ## the polynomials -/

noncomputable def Pk (n : ℕ) : ℕ → ℚ[X]
  | 0 => 1
  | 1 => C (n : ℚ) - C 2 * X
  | a + 2 => C (1 / ((a : ℚ) + 2)) * ((C (n : ℚ) - C 2 * X) * Pk n (a + 1) - C ((n : ℚ) - a) * Pk n a)

theorem Pk_eval (n x : ℕ) (hx : x ≤ n) : ∀ a, (Pk n a).eval (x : ℚ) = (Fp (n - x) x).coeff a
  | 0 => by simp [Pk, Fp_coeff0]
  | 1 => by
    rw [coeff1, Nat.cast_sub hx]
    simp [Pk]; ring
  | a + 2 => by
    have i1 := Pk_eval n x hx (a + 1)
    have i0 := Pk_eval n x hx a
    have h := ode_coeff (n - x) x a
    rw [Nat.cast_sub hx] at h
    simp only [Pk, eval_mul, eval_C, eval_sub, eval_X, i1, i0]
    have d : (a : ℚ) + 2 ≠ 0 := by positivity
    field_simp
    linear_combination -h

lemma Pk_deg (n : ℕ) : ∀ a, (Pk n a).natDegree ≤ a
  | 0 => by simp [Pk]
  | 1 => by simp only [Pk]; compute_degree
  | a + 2 => by
    simp only [Pk]
    have i1 := Pk_deg n (a + 1)
    have i0 := Pk_deg n a
    refine (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans (max_le ?_ ?_))
    · refine natDegree_mul_le.trans ?_
      have : (C (n : ℚ) - C 2 * X : ℚ[X]).natDegree ≤ 1 := by compute_degree
      omega
    · exact (natDegree_C_mul_le _ _).trans (by omega)

/-- the leading coefficient. -/
lemma Pk_lead (n : ℕ) : ∀ a, (Pk n a).coeff a = (-2) ^ a / (a.factorial : ℚ)
  | 0 => by simp [Pk]
  | 1 => by simp [Pk, coeff_X, coeff_C]
  | a + 2 => by
    have i1 := Pk_lead n (a + 1)
    have hz1 : (Pk n (a + 1)).coeff (a + 2) = 0 := coeff_eq_zero_of_natDegree_lt (by have := Pk_deg n (a + 1); omega)
    have hz0 : (Pk n a).coeff (a + 2) = 0 := coeff_eq_zero_of_natDegree_lt (by have := Pk_deg n a; omega)
    simp only [Pk]
    rw [coeff_C_mul, coeff_sub, coeff_C_mul, hz0, sub_mul, mul_assoc, coeff_sub, coeff_C_mul, coeff_C_mul,
      show a + 2 = (a + 1) + 1 by ring, coeff_X_mul, hz1, i1, Nat.factorial_succ (a + 1)]
    have d : (a : ℚ) + 2 ≠ 0 := by positivity
    have d' : ((a + 1).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-! ## self-duality -/

noncomputable def W (n a x : ℕ) : ℚ := (n.choose x : ℚ) * (Fp (n - x) x).coeff a

lemma W_left (n a x : ℕ) : (n.choose x : ℚ) * (Fp (n + 1 - x) x).coeff a
    = (n.choose x : ℚ) * ((1 + X) * Fp (n - x) x).coeff a := by
  rcases le_or_gt x n with h | h
  · rw [show n + 1 - x = (n - x) + 1 by omega, Fp_succ_left]
  · rw [Nat.choose_eq_zero_of_lt h]; simp

lemma W_zero (n a : ℕ) : W (n + 1) a 0 = (n.choose 0 : ℚ) * ((1 + X) * Fp (n - 0) 0).coeff a := by
  unfold W
  rw [show (n + 1).choose 0 = n.choose 0 by simp, W_left]

lemma W_succ (n a x : ℕ) : W (n + 1) a (x + 1)
    = (n.choose (x + 1) : ℚ) * ((1 + X) * Fp (n - (x + 1)) (x + 1)).coeff a
      + (n.choose x : ℚ) * ((1 - X) * Fp (n - x) x).coeff a := by
  unfold W
  rw [Nat.choose_succ_succ, ← W_left, show n + 1 - (x + 1) = n - x by omega, Fp_succ_right]
  simp only [Nat.succ_eq_add_one]
  push_cast
  ring

theorem W_symm (n : ℕ) : ∀ a x, W n a x = W n x a := by
  induction n with
  | zero =>
    intro a x
    rcases a with _ | a <;> rcases x with _ | x
    · rfl
    · simp [W, Fp, coeff_one]
    · simp [W, Fp, coeff_one]
    · simp [W]
  | succ n ih =>
    intro a x
    rcases a with _ | a <;> rcases x with _ | x
    · rfl
    · rw [W_succ, W_zero]
      simp only [coeff_one_add0, coeff_one_sub0, coeff_one_add, Fp_coeff0, mul_one]
      have e1 := ih 0 (x + 1)
      have e2 := ih 0 x
      simp only [W, Fp_coeff0, mul_one] at e1 e2
      linear_combination e1 + e2
    · rw [W_succ, W_zero]
      simp only [coeff_one_add0, coeff_one_sub0, coeff_one_add, Fp_coeff0, mul_one]
      have e1 := ih 0 (a + 1)
      have e2 := ih 0 a
      simp only [W, Fp_coeff0, mul_one] at e1 e2
      linear_combination -e1 - e2
    · rw [W_succ, W_succ, coeff_one_add, coeff_one_sub, coeff_one_add, coeff_one_sub]
      have e1 := ih (a + 1) (x + 1)
      have e2 := ih a (x + 1)
      have e3 := ih (a + 1) x
      have e4 := ih a x
      simp only [W] at e1 e2 e3 e4
      linear_combination e1 + e2 + e3 - e4

/-! ## reversal -/

lemma Fp_swap (p q m : ℕ) : (Fp q p).coeff m = (-1) ^ m * (Fp p q).coeff m := by
  induction p generalizing m with
  | succ p ih =>
    rw [Fp_succ_right, Fp_succ_left]
    rcases m with _ | m
    · simp [coeff_one_add0, coeff_one_sub0, Fp_coeff0]
    · rw [coeff_one_sub, coeff_one_add, ih, ih, pow_succ]; ring
  | zero =>
    induction q generalizing m with
    | zero => rcases m with _ | m <;> simp [Fp, coeff_one]
    | succ q ih =>
      rw [Fp_succ_left, Fp_succ_right]
      rcases m with _ | m
      · simp [coeff_one_add0, coeff_one_sub0, Fp_coeff0]
      · rw [coeff_one_add, coeff_one_sub, ih, ih, pow_succ]; ring

theorem Fp_rev (p q k : ℕ) (hk : k ≤ p + q) :
    (Fp p q).coeff k = (-1) ^ q * (Fp p q).coeff (p + q - k) := by
  have h1 := W_symm (p + q) q k
  have h2 := W_symm (p + q) q (p + q - k)
  simp only [W] at h1 h2
  rw [show p + q - q = p by omega] at h1 h2
  rw [show p + q - (p + q - k) = k by omega, Nat.choose_symm hk, Fp_swap (p + q - k) k q] at h2
  have hc : ((p + q).choose q : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  apply mul_left_cancel₀ hc
  have hs : ((-1 : ℚ) ^ q) * (-1) ^ q = 1 := by rw [← mul_pow]; simp
  linear_combination -h1 + (-1 : ℚ) ^ q * h2
    - (((p + q).choose k : ℚ) * (Fp (p + q - k) k).coeff q) * hs

/-! ## the middle coefficient -/

noncomputable def m (n s : ℕ) : ℚ := (Fp (2 * n - s) s).coeff n

lemma m_odd (n r : ℕ) (h : 2 * r + 1 ≤ 2 * n) : m n (2 * r + 1) = 0 := by
  have := Fp_rev (2 * n - (2 * r + 1)) (2 * r + 1) n (by omega)
  rw [show 2 * n - (2 * r + 1) + (2 * r + 1) - n = n by omega, pow_succ, pow_mul] at this
  norm_num at this
  unfold m
  linarith

lemma m_step (n r : ℕ) (h : 2 * r + 2 ≤ 2 * n) :
    (2 * (n : ℚ) - 2 * r - 1) * m n (2 * r + 2) = -(2 * (r : ℚ) + 1) * m n (2 * r) := by
  obtain ⟨A, hA⟩ : ∃ A, 2 * n = A + 2 * r + 2 := ⟨2 * n - 2 * r - 2, by omega⟩
  unfold m
  rw [show 2 * n - (2 * r + 2) = A by omega, show 2 * n - 2 * r = A + 1 + 1 by omega,
    show 2 * r + 2 = (2 * r + 1) + 1 by ring, Fp_succ_right, Fp_succ_right, Fp_succ_left, Fp_succ_left]
  rcases n with _ | _ | l
  · omega
  · obtain rfl : r = 0 := by omega
    obtain rfl : A = 0 := by omega
    have c0 : (Fp 0 0).coeff 1 = 0 := by rw [coeff1]; simp
    have a1 : ((1 - X) * ((1 - X) * Fp 0 0)).coeff (0 + 1) = -2 := by
      rw [coeff_one_sub, coeff_one_sub0, coeff_one_sub, c0, Fp_coeff0]; norm_num
    have a2 : ((1 + X) * ((1 + X) * Fp 0 0)).coeff (0 + 1) = 2 := by
      rw [coeff_one_add, coeff_one_add0, coeff_one_add, c0, Fp_coeff0]; norm_num
    simp only [mul_zero]
    rw [a1, a2]
    norm_num
  · rw [coeff_one_add, coeff_one_sub, coeff_one_add, coeff_one_sub,
      show l + 1 = (l + 0) + 1 by ring, coeff_one_add, coeff_one_sub]
    simp only [add_zero]
    have hr := Fp_rev A (2 * r) l (by omega)
    rw [show A + 2 * r - l = l + 2 by omega, pow_mul] at hr
    norm_num at hr
    have ho := ode_coeff A (2 * r) l
    have hq : (A : ℚ) = 2 * (l : ℚ) + 2 - 2 * r := by
      have : (A : ℚ) + 2 * r + 2 = 2 * ((l : ℚ) + 1 + 1) := by exact_mod_cast hA.symm
      linarith
    rw [hq] at ho
    push_cast
    push_cast at ho
    rw [hr] at ho ⊢
    linear_combination (2 : ℚ) * ho

lemma m_zero (n : ℕ) : m n 0 = ((2 * n).choose n : ℚ) := by
  simp [m, Fp, coeff_one_add_X_pow]

/-- **the closed form.** -/
theorem m_closed (n : ℕ) : ∀ r, r ≤ n → m n (2 * r) = (-1) ^ r * ((2 * n).choose n : ℚ) * Bali.ZS.mu n r
  | 0, _ => by simp [m_zero, Bali.ZS.mu]
  | r + 1, h => by
    have ih := m_closed n r (by omega)
    have hs := m_step n r (by omega)
    have d := Bali.ZS.oddne n r
    rw [show 2 * (r + 1) = 2 * r + 2 by ring]
    apply mul_left_cancel₀ d
    rw [hs, ih, Bali.ZS.mu, pow_succ]
    generalize 2 * (n : ℚ) - 2 * r - 1 = D at d ⊢
    field_simp

/-! ## the skew products -/

noncomputable def fa (n a : ℕ) : Fin (n + 1) → ℚ := fun x => (Fp (n - a) a).coeff (x : ℕ)

lemma pre (H : ℚ[X]) : ∀ k, ∑ y ∈ range (k + 1), ((1 - X) * H).coeff y = H.coeff k
  | 0 => by simp [coeff_one_sub0]
  | k + 1 => by rw [sum_range_succ, pre H k, coeff_one_sub]; ring

lemma pre_Iic {n : ℕ} (H : ℚ[X]) (k : Fin (n + 1)) :
    ∑ l ∈ Iic k, ((1 - X) * H).coeff (l : ℕ) = H.coeff (k : ℕ) :=
  (sum_Iic_fin (fun y : ℕ => ((1 - X) * H).coeff y) k).trans (pre H k)

lemma pre_Iio {n : ℕ} (H : ℚ[X]) (k : Fin (n + 1)) :
    ∑ l ∈ Iio k, ((1 - X) * H).coeff (l : ℕ) = if (k : ℕ) = 0 then 0 else H.coeff ((k : ℕ) - 1) := by
  refine (sum_Iio_fin (fun y : ℕ => ((1 - X) * H).coeff y) k).trans ?_
  split_ifs with h0
  · rw [h0]; simp
  · obtain ⟨j, hj⟩ : ∃ j, (k : ℕ) = j + 1 := ⟨(k : ℕ) - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel]; exact pre H j

lemma pre_univ (n : ℕ) (H : ℚ[X]) : ∑ l : Fin (n + 1), ((1 - X) * H).coeff (l : ℕ) = H.coeff n :=
  (Fin.sum_univ_eq_sum_range (fun y : ℕ => ((1 - X) * H).coeff y) (n + 1)).trans (pre H n)

theorem skew_fa (n a c : ℕ) (hc : c + 1 ≤ n) :
    skew (fa n a) (fa n (c + 1)) = -∑ k ∈ range (n + 1), (Fp (n - a) a).coeff k * (Fp (n - c) c).coeff k := by
  set H := Fp (n - (c + 1)) c with hH
  have hb : Fp (n - (c + 1)) (c + 1) = (1 - X) * H := Fp_succ_right _ _
  have hc' : Fp (n - c) c = (1 + X) * H := by
    rw [show n - c = (n - (c + 1)) + 1 by omega]; exact Fp_succ_left _ _
  have htot : ∑ l, fa n (c + 1) l = 0 := by
    unfold fa
    rw [hb, pre_univ]
    exact coeff_eq_zero_of_natDegree_lt (by have := Fp_deg (n - (c + 1)) c; rw [hH]; omega)
  rw [skew_of_total_zero _ _ htot, ← Fin.sum_univ_eq_sum_range
    (fun k => (Fp (n - a) a).coeff k * (Fp (n - c) c).coeff k) (n + 1)]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  have e1 : ∑ l ∈ Iic k, fa n (c + 1) l = H.coeff (k : ℕ) := by
    unfold fa; rw [hb]; exact pre_Iic H k
  have e2 : ∑ l ∈ Iio k, fa n (c + 1) l = if (k : ℕ) = 0 then 0 else H.coeff ((k : ℕ) - 1) := by
    unfold fa; rw [hb]; exact pre_Iio H k
  rw [e1, e2, hc']
  simp only [fa]
  congr 1
  rcases hk : (k : ℕ) with _ | j
  · simp [coeff_one_add0]
  · rw [coeff_one_add]; simp

/-- reversal for `n`-th row. -/
lemma dot_eq (n a c : ℕ) (ha : a ≤ n) (hc : c ≤ n) :
    ∑ k ∈ range (n + 1), (Fp (n - a) a).coeff k * (Fp (n - c) c).coeff k = (-1) ^ c * m n (a + c) := by
  have hprod : Fp (2 * n - (a + c)) (a + c) = Fp (n - a) a * Fp (n - c) c := by
    unfold Fp
    rw [show 2 * n - (a + c) = (n - a) + (n - c) by omega, pow_add, pow_add]; ring
  unfold m
  rw [hprod, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by have := mem_range.1 hk; omega
  have h := Fp_rev (n - c) c k (by omega)
  rw [show n - c + c - k = n - k by omega] at h
  simp only
  rw [h]
  ring

/-- the rows `C(n,x) K_a(x)`. -/
noncomputable def Kr (n a : ℕ) : Fin (n + 1) → ℚ := fun x => (n.choose (x : ℕ) : ℚ) * (Pk n a).eval ((x : ℕ) : ℚ)

lemma Kr_eq (n a : ℕ) : Kr n a = fun x => (n.choose a : ℚ) * fa n a x := by
  funext x
  have hx : (x : ℕ) ≤ n := by have := x.isLt; omega
  have := W_symm n a x
  simp only [Kr, fa, W] at this ⊢
  rw [Pk_eval n x hx]
  exact this

lemma skew_smul (n : ℕ) (u v : ℚ) (f g : Fin (n + 1) → ℚ) :
    skew (fun x => u * f x) (fun x => v * g x) = u * v * skew f g := by
  unfold skew
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  simp only [← mul_sum]
  ring

/-- **The Gram matrix.** -/
theorem gram_K (n a b : ℕ) (ha : a ≤ n) (hb : 1 ≤ b) (hbn : b ≤ n) :
    skew (Kr n a) (Kr n b) = (n.choose a : ℚ) * (n.choose b : ℚ) * ((-1) ^ b * m n (a + b - 1)) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  rw [Kr_eq, Kr_eq, skew_smul, skew_fa n a c hbn, dot_eq n a c ha (by omega),
    show a + (c + 1) - 1 = a + c by omega, pow_succ]
  ring

theorem total_K (n a : ℕ) (ha : 1 ≤ a) (han : a ≤ n) : ∑ x, Kr n a x = 0 := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  rw [Kr_eq, ← mul_sum]
  unfold fa
  rw [Fp_succ_right, pre_univ,
    coeff_eq_zero_of_natDegree_lt (by have := Fp_deg (n - (c + 1)) c; omega), mul_zero]

theorem total_K0 (n : ℕ) : ∑ x, Kr n 0 x = 2 ^ n := by
  simp only [Kr, Pk, eval_one, mul_one]
  rw [Fin.sum_univ_eq_sum_range (fun x => (n.choose x : ℚ)) (n + 1)]
  exact_mod_cast Nat.sum_range_choose n

end Bali.ZK

#print axioms Bali.ZK.gram_K
#print axioms Bali.ZK.m_closed
#print axioms Bali.ZK.total_K
#print axioms Bali.ZK.Pk_lead
