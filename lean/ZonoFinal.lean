import P699.ZonoV
import P699.ShellX

/-!
# The main theorem: `V_d(n)` for all `d ≥ 2`, `n ≥ d - 1` (Bali lab, 2026-11-02)
`V_d(n) = κ_d 2^{dn} ∏_i (n-i)^{max(0,d-2-2i)} ∏_{i=d-1-m}^{d-2} (n-i) C(2(n-i),n-i) / 4^{n-i}`, `m = ⌊d/2⌋`.
-/

open Finset

namespace Bali.ZF
open Bali.ZS Bali.ZV Bali.VB Bali.ShellX

/-! ## the right-hand side -/

/-- `(2k-1)!!`. -/
def dfk (k : ℕ) : ℚ := ((2 * k - 1).doubleFactorial : ℚ)

def Kd (d : ℕ) : ℚ :=
  (1 / 2) * (∏ k ∈ Icc 2 (d / 2), (((k - 1).factorial : ℚ) / (2 * 4 ^ (k - 1))))
    * ∏ k ∈ Icc 1 ((d - 1) / 2), (dfk k / 8 ^ k)

def Zp (n d : ℕ) : ℚ := ∏ i ∈ range d, ((n : ℚ) - i) ^ (d - 2 - 2 * i)

def Tc (n i : ℕ) : ℚ := ((n - i : ℕ) : ℚ) * ((2 * (n - i)).choose (n - i) : ℚ) / 4 ^ (n - i)

def Wn (n d : ℕ) : ℚ := ∏ i ∈ Ico (d - 1 - d / 2) (d - 1), Tc n i

def RHS (n d : ℕ) : ℚ := Kd d * 2 ^ (d * n) * Zp n d * Wn n d

/-! ## auxiliary products -/

def OPr (n i : ℕ) : ℚ := ∏ s ∈ range i, (2 * (n : ℚ) - 2 * s - 1)

def dn (n i : ℕ) : ℚ := (n.descFactorial i : ℚ)

lemma OPr_ne (n i : ℕ) : OPr n i ≠ 0 := prod_ne_zero_iff.2 fun s _ => oddne n s

lemma dn_succ (n i : ℕ) (h : i < n) : dn n (i + 1) = dn n i * ((n : ℚ) - i) := by
  unfold dn
  rw [Nat.descFactorial_succ]
  push_cast [Nat.cast_sub h.le]
  ring

lemma dn_prod (n : ℕ) : ∀ i, i ≤ n → ∏ s ∈ range i, ((n : ℚ) - s) = dn n i
  | 0, _ => by simp [dn]
  | i + 1, h => by rw [prod_range_succ, dn_prod n i (by omega), dn_succ n i (by omega)]

lemma dn_ne (n i : ℕ) (h : i ≤ n) : dn n i ≠ 0 := by
  unfold dn
  exact_mod_cast (Nat.descFactorial_pos.2 h).ne'

lemma dfk_succ (k : ℕ) : dfk (k + 1) = dfk k * (2 * (k : ℚ) + 1) := by
  unfold dfk
  rcases k with _ | k
  · simp [Nat.doubleFactorial]
  · rw [show 2 * (k + 1 + 1) - 1 = (2 * k + 1) + 1 + 1 by omega, show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
      Nat.doubleFactorial_add_two]
    push_cast; ring

lemma dfk_prod : ∀ k, ∏ t ∈ range k, (2 * (t : ℚ) + 1) = dfk k
  | 0 => by simp [dfk]
  | k + 1 => by rw [prod_range_succ, dfk_prod k, dfk_succ]

lemma dfk_ne (k : ℕ) : dfk k ≠ 0 := by
  unfold dfk
  exact_mod_cast (Nat.doubleFactorial_pos _).ne'

lemma mu_OP (n : ℕ) : ∀ k, mu n k * OPr n k = dfk k
  | 0 => by simp [mu, OPr, dfk]
  | k + 1 => by
    have ih := mu_OP n k
    have d := oddne n k
    rw [mu, OPr, prod_range_succ, dfk_succ, ← ih]
    change _ * (OPr n k * _) = _
    generalize 2 * (n : ℚ) - 2 * (k : ℚ) - 1 = D at d ⊢
    field_simp

lemma fall_fact : ∀ k : ℕ, ∏ t ∈ range k, ((k : ℚ) - t) = (k.factorial : ℚ) := by
  intro k
  have h := prod_range_reflect (fun t : ℕ => ((t : ℚ) + 1)) k
  have h2 : ∏ t ∈ range k, ((t : ℚ) + 1) = (k.factorial : ℚ) := by
    have := Finset.prod_range_add_one_eq_factorial k
    rw [← this]; push_cast; rfl
  rw [← h2, ← h]
  refine prod_congr rfl fun t ht => ?_
  have ht' := mem_range.1 ht
  rw [show k - 1 - t = k - (t + 1) by omega, Nat.cast_sub (by omega)]
  push_cast; ring

lemma succ_fact (k : ℕ) : ∏ t ∈ range k, ((t : ℚ) + 1) = (k.factorial : ℚ) := by
  have := Finset.prod_range_add_one_eq_factorial k
  rw [← this]; push_cast; rfl

/-- `|Ss k k|`. -/
lemma Ss_abs (n k : ℕ) (h : 2 * k + 1 ≤ n) :
    |Ss n k k| * OPr n (2 * k) = 4 ^ k * (k.factorial : ℚ) * dn n k := by
  rw [Ss_closed, abs_mul, Finset.abs_prod]
  have hmu : 0 < mu n k := by
    have : ∀ r, r ≤ n → 0 < mu n r := by
      intro r
      induction r with
      | zero => intro _; simp [mu]
      | succ r ih =>
        intro hr
        rw [mu]
        have h1 := ih (by omega)
        have h2 : (r : ℚ) + 1 ≤ n := by exact_mod_cast hr
        have h3 : 0 < 2 * (n : ℚ) - 2 * r - 1 := by linarith
        positivity
    exact this k (by omega)
  have hrho : ∀ t ∈ range k, |rho n t k|
      = (4 * ((k : ℚ) - t) * ((n : ℚ) - t)) / ((2 * (t : ℚ) + 1) * (2 * (n : ℚ) - 2 * ((k + t : ℕ) : ℚ) - 1)) := by
    intro t ht
    have ht' : t < k := mem_range.1 ht
    have h1 : (t : ℚ) + 1 ≤ k := by exact_mod_cast ht'
    have h2 : 2 * (k : ℚ) + 1 ≤ n := by exact_mod_cast h
    have h0 : (0 : ℚ) ≤ t := by positivity
    have e : rho n t k = -((4 * ((k : ℚ) - t) * ((n : ℚ) - t)) / ((2 * (t : ℚ) + 1) * (2 * (n : ℚ) - 2 * ((k + t : ℕ) : ℚ) - 1))) := by
      unfold rho
      push_cast
      rw [show 2 * (n : ℚ) - 2 * ((k : ℚ) + t) - 1 = 2 * (n : ℚ) - 2 * t - 2 * k - 1 by ring, ← neg_div]
      congr 1; ring
    rw [e, abs_neg, abs_of_pos]
    have p1 : 0 < (k : ℚ) - t := by linarith
    have p2 : 0 < (n : ℚ) - t := by linarith
    have p3 : 0 < 2 * (n : ℚ) - 2 * ((k + t : ℕ) : ℚ) - 1 := by push_cast; linarith
    positivity
  rw [prod_congr rfl hrho, abs_of_pos hmu, prod_div_distrib, prod_mul_distrib, prod_mul_distrib, prod_mul_distrib,
    prod_const, card_range, fall_fact, dn_prod n k (by omega), dfk_prod]
  have hsplit : OPr n (2 * k) = OPr n k * ∏ t ∈ range k, (2 * (n : ℚ) - 2 * ((k + t : ℕ) : ℚ) - 1) := by
    unfold OPr
    rw [two_mul, prod_range_add]
  have hne : ∏ t ∈ range k, (2 * (n : ℚ) - 2 * ((k + t : ℕ) : ℚ) - 1) ≠ 0 :=
    prod_ne_zero_iff.2 fun t _ => oddne n (k + t)
  have hO := OPr_ne n k
  have hd := dfk_ne k
  have hm := mu_OP n k
  rw [hsplit]
  generalize (∏ t ∈ range k, (2 * (n : ℚ) - 2 * ((k + t : ℕ) : ℚ) - 1)) = E at hne ⊢
  rw [show mu n k = dfk k / OPr n k by rw [eq_div_iff hO]; exact hm]
  field_simp

lemma a_prod (n i : ℕ) : ∀ l, a n i l = ∏ t ∈ range l,
    (-(((i : ℚ) - t) * (2 * (n : ℚ) - 2 * i + 1 - 2 * t)) / (((t : ℚ) + 1) * (2 * (t : ℚ) + 1)))
  | 0 => by simp [a]
  | l + 1 => by rw [prod_range_succ, ← a_prod n i l, a]

/-- `|a_{k,k}|`, `k = j+1`. -/
lemma a_abs (n j : ℕ) (h : 2 * (j + 1) ≤ n + 1) :
    |a n (j + 1) (j + 1)| * dfk (j + 1) * OPr n j = OPr n (2 * j + 1) := by
  rw [a_prod, Finset.abs_prod]
  have hq : 2 * ((j : ℚ) + 1) ≤ (n : ℚ) + 1 := by exact_mod_cast h
  have ht : ∀ t ∈ range (j + 1), |(-((((j + 1 : ℕ) : ℚ) - t) * (2 * (n : ℚ) - 2 * ((j + 1 : ℕ) : ℚ) + 1 - 2 * t))
        / (((t : ℚ) + 1) * (2 * (t : ℚ) + 1)))|
      = (((j + 1 : ℕ) : ℚ) - t) * (2 * (n : ℚ) - 2 * ((j + t : ℕ) : ℚ) - 1) / (((t : ℚ) + 1) * (2 * (t : ℚ) + 1)) := by
    intro t ht
    have ht' : (t : ℚ) ≤ j := by exact_mod_cast (by have := mem_range.1 ht; omega : t ≤ j)
    have h0 : (0 : ℚ) ≤ t := by positivity
    rw [abs_div, abs_neg, abs_mul, abs_of_pos (by push_cast; linarith : (0 : ℚ) < ((j + 1 : ℕ) : ℚ) - t),
      abs_of_pos (by push_cast; linarith : (0 : ℚ) < 2 * (n : ℚ) - 2 * ((j + 1 : ℕ) : ℚ) + 1 - 2 * t),
      abs_of_pos (by positivity : (0 : ℚ) < ((t : ℚ) + 1) * (2 * (t : ℚ) + 1))]
    push_cast; ring_nf
  rw [prod_congr rfl ht, prod_div_distrib, prod_mul_distrib, prod_mul_distrib, fall_fact, succ_fact, dfk_prod]
  have hsplit : OPr n (2 * j + 1) = OPr n j * ∏ t ∈ range (j + 1), (2 * (n : ℚ) - 2 * ((j + t : ℕ) : ℚ) - 1) := by
    unfold OPr
    rw [show 2 * j + 1 = j + (j + 1) by ring, prod_range_add]
  rw [hsplit]
  have hf : (((j + 1).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have hd := dfk_ne (j + 1)
  field_simp

/-- `Tc`, closed. -/
lemma Tc_closed (n : ℕ) : ∀ i, i < n →
    Tc n i * OPr n i = ((2 * n).choose n : ℚ) / 4 ^ n * 2 ^ i * dn n (i + 1)
  | 0, h => by
    simp only [Tc, OPr, dn, Nat.sub_zero, range_zero, prod_empty, mul_one, pow_zero, zero_add, Nat.descFactorial_one]
    ring
  | i + 1, h => by
    have ih := Tc_closed n i (by omega)
    obtain ⟨M, hM⟩ : ∃ M, n - i = M + 1 := ⟨n - i - 1, by omega⟩
    have hM2 : n - (i + 1) = M := by omega
    have hc := Nat.succ_mul_centralBinom_succ M
    rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at hc
    have hcq : ((M : ℚ) + 1) * ((2 * (M + 1)).choose (M + 1) : ℚ) = 2 * (2 * (M : ℚ) + 1) * ((2 * M).choose M : ℚ) := by
      exact_mod_cast hc
    have hnq : (n : ℚ) = (M : ℚ) + 1 + i := by exact_mod_cast (by omega : n = M + 1 + i)
    have hT : Tc n (i + 1) * (2 * (n : ℚ) - 2 * i - 1) = 2 * ((n : ℚ) - i - 1) * Tc n i := by
      unfold Tc
      rw [hM, hM2, pow_succ]
      push_cast
      rw [hnq]
      field_simp
      linear_combination (-2 * (M : ℚ)) * hcq
    have hO : OPr n (i + 1) = OPr n i * (2 * (n : ℚ) - 2 * i - 1) := by
      unfold OPr; rw [prod_range_succ]
    rw [hO, dn_succ n (i + 1) (by omega)]
    push_cast
    calc Tc n (i + 1) * (OPr n i * (2 * (n : ℚ) - 2 * i - 1))
        = (Tc n (i + 1) * (2 * (n : ℚ) - 2 * i - 1)) * OPr n i := by ring
      _ = _ := by
        rw [hT]
        linear_combination (2 * ((n : ℚ) - i - 1)) * ih + 0 * hnq


/-! ## the algebra of one step -/

lemma algE (C1 Cc F F1 c2 S X A O1 O2 O3 T1 T2 T3 Fk Dk d2 d3 P u : ℚ)
    (hF : F ≠ 0) (hF1 : F1 ≠ 0) (hA : A ≠ 0) (hO1 : O1 ≠ 0) (hO2 : O2 ≠ 0) (hO3 : O3 ≠ 0) (hP : P ≠ 0) (hu : u ≠ 0)
    (hc2 : c2 ≠ 0) (hDk : Dk ≠ 0) (hd2 : d2 ≠ 0) (hd3 : d3 ≠ 0)
    (hC1 : C1 * F1 = d3) (hCc : Cc * F = d2) (hX : X * A * O1 = O2) (hS : S * O3 = 4 * u ^ 2 * Fk * Dk)
    (hT1 : T1 * O2 = c2 / P * (2 * u ^ 2) * d2) (hT2 : T2 * O3 = c2 / P * (4 * u ^ 2) * d3)
    (hT3 : T3 * O1 = c2 / P * u * Dk) :
    (C1 * c2 * S) / ((X / Cc * (4 * u ^ 2) / F) * (8 * u ^ 2 / F1))
      = Fk / (2 * (4 * u ^ 2)) * (A / (8 * u ^ 3)) * P * Dk ^ 2 * (T1 * T2 / T3) := by
  obtain rfl : C1 = d3 / F1 := by rw [eq_div_iff hF1]; exact hC1
  obtain rfl : Cc = d2 / F := by rw [eq_div_iff hF]; exact hCc
  obtain rfl : X = O2 / (A * O1) := by rw [eq_div_iff (mul_ne_zero hA hO1)]; linear_combination hX
  obtain rfl : S = 4 * u ^ 2 * Fk * Dk / O3 := by rw [eq_div_iff hO3]; exact hS
  obtain rfl : T1 = c2 / P * (2 * u ^ 2) * d2 / O2 := by rw [eq_div_iff hO2]; exact hT1
  obtain rfl : T2 = c2 / P * (4 * u ^ 2) * d3 / O3 := by rw [eq_div_iff hO3]; exact hT2
  obtain rfl : T3 = c2 / P * u * Dk / O1 := by rw [eq_div_iff hO1]; exact hT3
  field_simp

lemma algO (Cc F c2 X A O1 O2 T1 T3 Dk d2 P Q u : ℚ)
    (hF : F ≠ 0) (hA : A ≠ 0) (hO1 : O1 ≠ 0) (hO2 : O2 ≠ 0) (hP : P ≠ 0) (hu : u ≠ 0)
    (hc2 : c2 ≠ 0) (hDk : Dk ≠ 0) (hd2 : d2 ≠ 0)
    (hCc : Cc * F = d2) (hX : X * A * O1 = O2)
    (hT1 : T1 * O2 = c2 / P * (2 * u ^ 2) * d2) (hT3 : T3 * O1 = c2 / P * u * Dk) :
    Q / (X / Cc * (4 * u ^ 2) / F) = A / (8 * u ^ 3) * Q * Dk * (T1 / T3) := by
  obtain rfl : Cc = d2 / F := by rw [eq_div_iff hF]; exact hCc
  obtain rfl : X = O2 / (A * O1) := by rw [eq_div_iff (mul_ne_zero hA hO1)]; linear_combination hX
  obtain rfl : T1 = c2 / P * (2 * u ^ 2) * d2 / O2 := by rw [eq_div_iff hO2]; exact hT1
  obtain rfl : T3 = c2 / P * u * Dk / O1 := by rw [eq_div_iff hO1]; exact hT3
  field_simp
  ring

/-! ## the steps of the left side -/

noncomputable def RR (n i : ℕ) : ℚ := rr n i / (cfE n i * cfO i)

lemma RR_val (n j : ℕ) (h : 2 * j + 3 ≤ n) :
    RR n (j + 1) = ((j + 1).factorial : ℚ) / (2 * 4 ^ (j + 1)) * (dfk (j + 1) / 8 ^ (j + 1)) * 4 ^ n * dn n (j + 1) ^ 2
      * (Tc n (2 * j + 1) * Tc n (2 * j + 2) / Tc n j) := by
  have hC1 : ((n.choose (2 * j + 3) : ℕ) : ℚ) * ((2 * j + 3).factorial : ℚ) = dn n (2 * j + 3) := by
    unfold dn; rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring
  have hCc : ((n.choose (2 * j + 2) : ℕ) : ℚ) * ((2 * j + 2).factorial : ℚ) = dn n (2 * j + 2) := by
    unfold dn; rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring
  have hS := Ss_abs n (j + 1) (by omega)
  have hX := a_abs n j (by omega)
  have hT1 := Tc_closed n (2 * j + 1) (by omega)
  have hT2 := Tc_closed n (2 * j + 2) (by omega)
  have hT3 := Tc_closed n j (by omega)
  have p1 : (4 : ℚ) ^ (j + 1) = 4 * ((2 : ℚ) ^ j) ^ 2 := by
    rw [pow_succ, show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring
  have p2 : (8 : ℚ) ^ (j + 1) = 8 * ((2 : ℚ) ^ j) ^ 3 := by
    rw [pow_succ, show (8 : ℚ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul]; ring
  have p3 : (2 : ℚ) ^ (2 * j + 1) = 2 * ((2 : ℚ) ^ j) ^ 2 := by ring
  have p4 : (2 : ℚ) ^ (2 * j + 2) = 4 * ((2 : ℚ) ^ j) ^ 2 := by ring
  have p5 : (2 : ℚ) ^ (2 * (j + 1) + 1) = 8 * ((2 : ℚ) ^ j) ^ 2 := by ring
  rw [p1] at hS
  rw [p3] at hT1
  rw [p4] at hT2
  rw [show 2 * (j + 1) = 2 * j + 2 by ring] at hS
  unfold RR rr cfE cfO
  rw [p5, p1, p2, show 2 * (j + 1) + 1 = 2 * j + 3 by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
  exact algE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by positivity) (by positivity) (dfk_ne _) (OPr_ne _ _) (OPr_ne _ _) (OPr_ne _ _) (by positivity) (by positivity)
    (by exact_mod_cast (Nat.choose_pos (by omega)).ne')
    (dn_ne _ _ (by omega)) (dn_ne _ _ (by omega)) (dn_ne _ _ (by omega))
    hC1 hCc hX hS hT1 hT2 hT3

lemma BO_val (n j : ℕ) (h : 2 * j + 2 ≤ n) :
    2 ^ n / cfE n (j + 1) = dfk (j + 1) / 8 ^ (j + 1) * 2 ^ n * dn n (j + 1) * (Tc n (2 * j + 1) / Tc n j) := by
  have hCc : ((n.choose (2 * j + 2) : ℕ) : ℚ) * ((2 * j + 2).factorial : ℚ) = dn n (2 * j + 2) := by
    unfold dn; rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring
  have hX := a_abs n j (by omega)
  have hT1 := Tc_closed n (2 * j + 1) (by omega)
  have hT3 := Tc_closed n j (by omega)
  have p1 : (4 : ℚ) ^ (j + 1) = 4 * ((2 : ℚ) ^ j) ^ 2 := by
    rw [pow_succ, show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring
  have p2 : (8 : ℚ) ^ (j + 1) = 8 * ((2 : ℚ) ^ j) ^ 3 := by
    rw [pow_succ, show (8 : ℚ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul]; ring
  have p3 : (2 : ℚ) ^ (2 * j + 1) = 2 * ((2 : ℚ) ^ j) ^ 2 := by ring
  rw [p3] at hT1
  unfold cfE
  rw [p1, p2, show 2 * (j + 1) = 2 * j + 2 by ring]
  exact algO _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by positivity) (dfk_ne _) (OPr_ne _ _) (OPr_ne _ _) (by positivity) (by positivity)
    (by exact_mod_cast (Nat.choose_pos (by omega)).ne')
    (dn_ne _ _ (by omega)) (dn_ne _ _ (by omega)) hCc hX hT1 hT3

/-! ## the steps of the right side -/

lemma Kd_E (j : ℕ) : Kd (2 * j + 4) = Kd (2 * j + 2) * (((j + 1).factorial : ℚ) / (2 * 4 ^ (j + 1)))
    * (dfk (j + 1) / 8 ^ (j + 1)) := by
  unfold Kd
  rw [show (2 * j + 4) / 2 = j + 1 + 1 by omega, show (2 * j + 4 - 1) / 2 = j + 1 by omega,
    show (2 * j + 2) / 2 = j + 1 by omega, show (2 * j + 2 - 1) / 2 = j by omega,
    prod_Icc_succ_top (show 2 ≤ j + 1 + 1 by omega), prod_Icc_succ_top (show 1 ≤ j + 1 by omega),
    show j + 1 + 1 - 1 = j + 1 by omega]
  ring

lemma Kd_O (j : ℕ) : Kd (2 * j + 3) = Kd (2 * j + 2) * (dfk (j + 1) / 8 ^ (j + 1)) := by
  unfold Kd
  rw [show (2 * j + 3) / 2 = j + 1 by omega, show (2 * j + 3 - 1) / 2 = j + 1 by omega,
    show (2 * j + 2) / 2 = j + 1 by omega, show (2 * j + 2 - 1) / 2 = j by omega,
    prod_Icc_succ_top (show 1 ≤ j + 1 by omega)]
  ring

lemma Zp_cut (n d k : ℕ) (hk : k ≤ d) (h : d ≤ 2 * k + 2) :
    Zp n d = ∏ i ∈ range k, ((n : ℚ) - i) ^ (d - 2 - 2 * i) := by
  unfold Zp
  symm
  refine prod_subset (range_subset_range.2 hk) fun x _ hx => ?_
  have : k ≤ x := by simpa using hx
  rw [show d - 2 - 2 * x = 0 by omega, pow_zero]

lemma Zp_E (n j : ℕ) (h : j + 1 ≤ n) : Zp n (2 * j + 4) = Zp n (2 * j + 2) * dn n (j + 1) ^ 2 := by
  rw [Zp_cut n (2 * j + 4) (j + 1) (by omega) (by omega), Zp_cut n (2 * j + 2) (j + 1) (by omega) (by omega),
    ← dn_prod n (j + 1) h, ← prod_pow, ← prod_mul_distrib]
  refine prod_congr rfl fun i hi => ?_
  have := mem_range.1 hi
  rw [show 2 * j + 4 - 2 - 2 * i = (2 * j + 2 - 2 - 2 * i) + 2 by omega, pow_add]

lemma Zp_O (n j : ℕ) (h : j + 1 ≤ n) : Zp n (2 * j + 3) = Zp n (2 * j + 2) * dn n (j + 1) := by
  rw [Zp_cut n (2 * j + 3) (j + 1) (by omega) (by omega), Zp_cut n (2 * j + 2) (j + 1) (by omega) (by omega),
    ← dn_prod n (j + 1) h, ← prod_mul_distrib]
  refine prod_congr rfl fun i hi => ?_
  have := mem_range.1 hi
  rw [show 2 * j + 3 - 2 - 2 * i = (2 * j + 2 - 2 - 2 * i) + 1 by omega, pow_succ]

lemma Tc_ne (n i : ℕ) (h : i < n) : Tc n i ≠ 0 := by
  unfold Tc
  have h1 : ((n - i : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : n - i ≠ 0)
  have h2 : ((2 * (n - i)).choose (n - i) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  positivity

lemma Wn_E (n j : ℕ) (h : j < n) :
    Wn n (2 * j + 4) = Wn n (2 * j + 2) * (Tc n (2 * j + 1) * Tc n (2 * j + 2) / Tc n j) := by
  unfold Wn
  rw [show 2 * j + 4 - 1 - (2 * j + 4) / 2 = j + 1 by omega, show 2 * j + 4 - 1 = 2 * j + 2 + 1 by omega,
    show 2 * j + 2 - 1 - (2 * j + 2) / 2 = j by omega, show 2 * j + 2 - 1 = 2 * j + 1 by omega,
    prod_Ico_succ_top (by omega), prod_Ico_succ_top (by omega), prod_eq_prod_Ico_succ_bot (by omega : j < 2 * j + 1)]
  have := Tc_ne n j h
  field_simp

lemma Wn_O (n j : ℕ) (h : j < n) :
    Wn n (2 * j + 3) = Wn n (2 * j + 2) * (Tc n (2 * j + 1) / Tc n j) := by
  unfold Wn
  rw [show 2 * j + 3 - 1 - (2 * j + 3) / 2 = j + 1 by omega, show 2 * j + 3 - 1 = 2 * j + 1 + 1 by omega,
    show 2 * j + 2 - 1 - (2 * j + 2) / 2 = j by omega, show 2 * j + 2 - 1 = 2 * j + 1 by omega,
    prod_Ico_succ_top (by omega), prod_eq_prod_Ico_succ_bot (by omega : j < 2 * j + 1)]
  have := Tc_ne n j h
  field_simp

lemma RHS_E (n j : ℕ) (h : 2 * j + 3 ≤ n) : RHS n (2 * j + 4) = RHS n (2 * j + 2) * RR n (j + 1) := by
  rw [RR_val n j h]
  unfold RHS
  rw [Kd_E, Zp_E n j (by omega), Wn_E n j (by omega),
    show (2 * j + 4) * n = (2 * j + 2) * n + 2 * n by ring, pow_add (2 : ℚ) _ (2 * n), pow_mul (2 : ℚ) 2 n]
  norm_num
  ring

lemma RHS_O (n j : ℕ) (h : 2 * j + 2 ≤ n) : RHS n (2 * j + 3) = RHS n (2 * j + 2) * (2 ^ n / cfE n (j + 1)) := by
  rw [BO_val n j h]
  unfold RHS
  rw [Kd_O, Zp_O n j (by omega), Wn_O n j (by omega),
    show (2 * j + 3) * n = (2 * j + 2) * n + n by ring, pow_add (2 : ℚ) _ n]
  ring

lemma RHS_two (n : ℕ) (h : 1 ≤ n) : RHS n 2 = RR n 0 := by
  have hS : Ss n 0 0 = 1 := by simp [Ss, a, mu]
  unfold RHS RR rr cfE cfO
  simp only [Kd, Zp, Wn, Tc, hS]
  norm_num [a, pow_mul]
  have : ((4 : ℚ) ^ n) ≠ 0 := by positivity
  field_simp

lemma prod_RR (n : ℕ) : ∀ j, 2 * j + 1 ≤ n → ∏ i ∈ range (j + 1), RR n i = RHS n (2 * j + 2)
  | 0, h => by rw [prod_range_one]; exact (RHS_two n (by omega)).symm
  | j + 1, h => by
    rw [prod_range_succ, prod_RR n j (by omega), show 2 * (j + 1) + 2 = 2 * j + 4 by ring, RHS_E n j (by omega)]

/-- **The main theorem** (zonotope form). -/
theorem main_V (n d : ℕ) (hd2 : 2 ≤ d) (hdn : d ≤ n + 1) : VBvol (tZ n) (nuZ n) d = RHS n d := by
  rcases Nat.even_or_odd' d with ⟨k, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Vz_e n (j + 1) hdn, show 2 * (j + 1) = 2 * j + 2 by ring, ← prod_RR n j (by omega)]
    rfl
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Vz_o n (j + 1) (by omega), Vz_e n (j + 1) (by omega), show 2 * (j + 1) + 1 = 2 * j + 3 by ring,
      RHS_O n j (by omega), ← prod_RR n j (by omega)]
    rfl

/-- **Theorem (eq:main).** `V_d(n)` as the sum over `d`-subsets `X` of `{0,…,n}`:
`Σ_X ∏_{x∈X} C(n,x) ∏_{a<b in X} |b-a|`. -/
theorem main_theorem (n d : ℕ) (hd2 : 2 ≤ d) (hdn : d ≤ n + 1) :
    VBs (fun x : Fin (n + 1) => ((x : ℕ) : ℚ)) (fun x => (n.choose (x : ℕ) : ℚ)) d = RHS n d := by
  rw [← main_V n d hd2 hdn, VBvol_eq_VBs]
  unfold VBs
  refine sum_congr rfl fun X _ => ?_
  congr 1
  unfold Pp
  refine prod_congr rfl fun a _ => prod_congr rfl fun b _ => ?_
  simp only [tZ]
  rw [abs_sub_comm]
  congr 1
  ring

end Bali.ZF

#print axioms Bali.ZF.main_theorem
