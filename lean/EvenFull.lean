import P699.EvenEdge

/-!
# Even `n = 2m`, `d = m + 1` (all shells) (Bali lab, 2026-11-02)
Lagrange: `V_m = V_{m+1} Σ_h 1/(ν_h ∏_{k≠h}|t_k - t_h|)`, and every summand is `1/(4^m (2m)!)`,
so `V_{m+1} = V_m · 4^m (2m)!/(m+1)`.
-/

open Finset

namespace Bali.EF
open Bali.ShellX

/-! ## Lagrange, generic -/

section Lag
variable {N : ℕ} (f w : Fin (N + 1) → ℚ)

lemma Qd_insert (i : Fin (N + 1)) (S : Finset (Fin (N + 1))) (hi : i ∉ S) :
    Qd f (insert i S) = Qd f S * (∏ k ∈ S, |f k - f i|) ^ 2 := by
  unfold Qd
  rw [prod_insert hi]
  have e1 : ∏ b ∈ insert i S, (if i ≠ b then |f b - f i| else 1) = ∏ k ∈ S, |f k - f i| := by
    rw [prod_insert hi, if_neg (by simp), one_mul]
    exact prod_congr rfl fun b hb => by rw [if_pos (fun h : i = b => hi (h ▸ hb))]
  have e2 : ∀ a ∈ S, ∏ b ∈ insert i S, (if a ≠ b then |f b - f a| else 1)
      = |f i - f a| * ∏ b ∈ S, (if a ≠ b then |f b - f a| else 1) := by
    intro a ha
    rw [prod_insert hi, if_pos (fun h : a = i => hi (h ▸ ha))]
  rw [e1, prod_congr rfl e2, prod_mul_distrib]
  have e3 : ∏ a ∈ S, |f i - f a| = ∏ k ∈ S, |f k - f i| := prod_congr rfl fun a _ => abs_sub_comm _ _
  rw [e3]; ring

lemma Pp_insert (i : Fin (N + 1)) (S : Finset (Fin (N + 1))) (hi : i ∉ S) :
    Pp f (insert i S) = Pp f S * ∏ k ∈ S, |f k - f i| :=
  (pow_left_inj₀ (Pp_nonneg _ _) (mul_nonneg (Pp_nonneg _ _) (prod_nonneg fun _ _ => abs_nonneg _)) two_ne_zero).1
    (by rw [Pp_sq, mul_pow, Pp_sq, Qd_insert f i S hi])

lemma pc_full : (univ : Finset (Fin (N + 1))).powersetCard (N + 1) = {univ} := by
  have := powersetCard_self (univ : Finset (Fin (N + 1)))
  rwa [card_univ, Fintype.card_fin] at this

lemma pc_erase : (univ : Finset (Fin (N + 1))).powersetCard N
    = univ.map ⟨fun i => univ.erase i, fun a b h => by
        simp only at h
        by_contra hab
        have hm : a ∈ univ.erase b := mem_erase.2 ⟨hab, mem_univ _⟩
        rw [← h] at hm
        simp at hm⟩ := by
  symm
  apply eq_of_subset_of_card_le
  · intro X hX
    obtain ⟨i, -, rfl⟩ := mem_map.1 hX
    exact mem_powersetCard.2 ⟨subset_univ _, by
      show (univ.erase i).card = N
      rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; rfl⟩
  · rw [card_powersetCard, card_univ, Fintype.card_fin, card_map, card_univ, Fintype.card_fin, Nat.choose_succ_self_right]

/-- **Lagrange relation.** -/
theorem lagrange (hw : ∀ i, w i ≠ 0) (hf : Function.Injective f) :
    VBs f w N = VBs f w (N + 1) * ∑ i, 1 / (w i * ∏ k ∈ univ.erase i, |f k - f i|) := by
  have hP : ∀ i, ∏ k ∈ univ.erase i, |f k - f i| ≠ 0 := fun i =>
    prod_ne_zero_iff.2 fun k hk => abs_ne_zero.2 (sub_ne_zero.2 fun h => (ne_of_mem_erase hk) (hf h))
  unfold VBs
  rw [pc_full, sum_singleton, pc_erase, sum_map, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  have hfull := Pp_insert f i (univ.erase i) (by simp)
  rw [insert_erase (mem_univ i)] at hfull
  have hw' : ∏ x, w x = w i * ∏ x ∈ univ.erase i, w x := (mul_prod_erase _ _ (mem_univ i)).symm
  rw [hfull, hw']
  field_simp [hw i, hP i]
  rfl

end Lag

/-! ## the shells: every summand is `1/(4^m (2m)!)` -/

open Bali.EvenPsi

lemma prod_split (m h : ℕ) (hh : h ≤ m) (g : ℕ → ℚ) :
    ∏ k ∈ (range (m + 1)).erase h, g k = (∏ k ∈ range h, g k) * ∏ j ∈ range (m - h), g (h + 1 + j) := by
  set G : ℕ → ℚ := fun k => if k = h then 1 else g k with hG
  have e1 : ∏ k ∈ (range (m + 1)).erase h, g k = ∏ k ∈ range (m + 1), G k := by
    rw [← mul_prod_erase _ G (mem_range.2 (by omega : h < m + 1))]
    simp only [hG, if_pos rfl, one_mul]
    exact prod_congr rfl fun k hk => by rw [if_neg (ne_of_mem_erase hk)]
  rw [e1, show m + 1 = (h + 1) + (m - h) by omega, prod_range_add, prod_range_succ]
  simp only [hG, if_pos rfl, mul_one]
  congr 1
  · exact prod_congr rfl fun k hk => by rw [if_neg (by have := mem_range.1 hk; omega)]
  · exact prod_congr rfl fun j _ => by rw [if_neg (by omega)]

lemma fin_erase (K : ℕ) (h : Fin (K + 2)) (F : ℕ → ℚ) :
    ∏ k ∈ univ.erase h, F (k : ℕ) = ∏ k ∈ (range (K + 2)).erase (h : ℕ), F k := by
  set G : ℕ → ℚ := fun k => if k = (h : ℕ) then 1 else F k with hG
  have e1 : ∏ k ∈ univ.erase h, F (k : ℕ) = ∏ k : Fin (K + 2), G k := by
    rw [← mul_prod_erase _ (fun k : Fin (K + 2) => G k) (mem_univ h)]
    simp only [hG, if_pos rfl, one_mul]
    exact prod_congr rfl fun k hk => by rw [if_neg (fun e => ne_of_mem_erase hk (Fin.ext e))]
  have e2 : ∏ k ∈ (range (K + 2)).erase (h : ℕ), F k = ∏ k ∈ range (K + 2), G k := by
    rw [← mul_prod_erase _ G (mem_range.2 h.isLt)]
    simp only [hG, if_pos rfl, one_mul]
    exact prod_congr rfl fun k hk => by rw [if_neg (ne_of_mem_erase hk)]
  rw [e1, e2, Fin.prod_univ_eq_prod_range]

/-- `∏_{k<a} ((c+a) - k) · c! = (c+a)!`. -/
lemma desc (c : ℕ) : ∀ a : ℕ, (∏ k ∈ range a, (((c + a : ℕ) : ℚ) - k)) * (c.factorial : ℚ) = ((c + a).factorial : ℚ)
  | 0 => by simp
  | a + 1 => by
    rw [prod_range_succ', show c + (a + 1) = (c + a) + 1 by ring]
    have ih := desc c a
    have e : ∏ k ∈ range a, (((c + a + 1 : ℕ) : ℚ) - ((k + 1 : ℕ) : ℚ)) = ∏ k ∈ range a, (((c + a : ℕ) : ℚ) - k) :=
      prod_congr rfl fun k _ => by push_cast; ring
    rw [e, Nat.factorial_succ]
    push_cast at ih ⊢
    linear_combination ((c : ℚ) + a + 1) * ih

/-- **every summand is the same**: `ν_h ∏_{k≠h}|t_k - t_h| = 4^m (2m)!`, `m = K+1`. -/
theorem term_const (K : ℕ) (h : Fin (K + 2)) :
    nuV K h * ∏ k ∈ univ.erase h, |yv K (k : ℕ) - yv K (h : ℕ)| = 4 ^ (K + 1) * ((2 * (K + 1)).factorial : ℚ) := by
  have hh := h.isLt
  have hfe := fin_erase K h (fun k => |yv K k - yv K (h : ℕ)|)
  rw [hfe, show range (K + 2) = range (K + 1 + 1) from rfl, prod_split (K + 1) (h : ℕ) (by omega)]
  rcases Nat.lt_or_ge (h : ℕ) (K + 1) with hlt | hge
  · obtain ⟨r, hr⟩ : ∃ r, K = (h : ℕ) + r := ⟨K - h, by omega⟩
    have hnu : nuV K h = 2 * ((2 * K + 1 + 1).choose (h : ℕ) : ℚ) := by simp [nuV, FV, hlt]
    rw [hnu]
    generalize ha : (h : ℕ) = a at *
    subst hr
    rw [show a + r + 1 - a = r + 1 by omega]
    have p1 : ∏ k ∈ range a, |yv (a + r) k - yv (a + r) a|
        = ∏ k ∈ range a, (4 * ((((0 + a : ℕ) : ℚ) - k) * ((((2 * r + 2) + a : ℕ) : ℚ) - k))) := by
      refine prod_congr rfl fun k hk => ?_
      have h1 : (k : ℚ) < a := by exact_mod_cast mem_range.1 hk
      have h0 : (0 : ℚ) ≤ r := by positivity
      rw [abs_of_nonneg]
      · simp only [yv]; push_cast; ring
      · simp only [yv]; push_cast; nlinarith
    have p2 : ∏ j ∈ range (r + 1), |yv (a + r) (a + 1 + j) - yv (a + r) a|
        = ∏ j ∈ range (r + 1), (4 * (((j : ℚ) + 1) * (((r + (r + 1) : ℕ) : ℚ) - j))) := by
      refine prod_congr rfl fun j hj => ?_
      have h1 : (j : ℚ) ≤ r := by exact_mod_cast (by have := mem_range.1 hj; omega : j ≤ r)
      have h0 : (0 : ℚ) ≤ j := by positivity
      rw [abs_of_nonpos]
      · simp only [yv]; push_cast; ring
      · simp only [yv]; push_cast; nlinarith
    rw [p1, p2, prod_mul_distrib, prod_mul_distrib, prod_mul_distrib, prod_mul_distrib, prod_const, prod_const,
      card_range, card_range]
    have d1 := desc 0 a
    have d2 := desc (2 * r + 2) a
    have d3 := desc r (r + 1)
    have d4 : ∏ j ∈ range (r + 1), ((j : ℚ) + 1) = ((r + 1).factorial : ℚ) := by
      exact_mod_cast prod_range_add_one_eq_factorial (r + 1)
    have hC := Nat.choose_mul_factorial_mul_factorial (show a ≤ 2 * (a + r) + 1 + 1 by omega)
    rw [show 2 * (a + r) + 1 + 1 - a = (2 * r + 2) + a by omega] at hC
    have hCq : ((2 * (a + r) + 1 + 1).choose a : ℚ) * (a.factorial : ℚ) * (((2 * r + 2) + a).factorial : ℚ)
        = ((2 * (a + r) + 1 + 1).factorial : ℚ) := by exact_mod_cast hC
    simp only [Nat.factorial_zero, Nat.cast_one, mul_one] at d1
    rw [d1, d4]
    simp only [zero_add]
    set P2 := ∏ x ∈ range a, ((((2 * r + 2) + a : ℕ) : ℚ) - x)
    set P3 := ∏ x ∈ range (r + 1), (((r + (r + 1) : ℕ) : ℚ) - x)
    rw [show 2 * (a + r + 1) = 2 * (a + r) + 1 + 1 by ring]
    rw [show 2 * r + 2 = (2 * r + 1) + 1 by ring, Nat.factorial_succ] at d2
    rw [Nat.factorial_succ r] at d4 ⊢
    rw [show r + (r + 1) = 2 * r + 1 by ring] at d3
    have f1 : ((2 * r + 1).factorial : ℚ) ≠ 0 := by positivity
    have f2 : (r.factorial : ℚ) ≠ 0 := by positivity
    have f3 : (a.factorial : ℚ) ≠ 0 := by positivity
    have hpow : (4 : ℚ) ^ a * 4 ^ (r + 1) = 4 ^ (a + r + 1) := by rw [← pow_add, show a + (r + 1) = a + r + 1 by ring]
    have eC : ((2 * (a + r) + 1 + 1).choose a : ℚ) = ((2 * (a + r) + 1 + 1).factorial : ℚ)
        / ((a.factorial : ℚ) * (((2 * r + 1 + 1) + a).factorial : ℚ)) := by
      rw [eq_div_iff (by positivity)]; linear_combination hCq
    have eP2 : P2 = (((2 * r + 1 + 1) + a).factorial : ℚ) / ((((2 * r + 1 + 1 : ℕ) : ℚ)) * ((2 * r + 1).factorial : ℚ)) := by
      rw [eq_div_iff (by positivity)]; push_cast at d2 ⊢; linear_combination d2
    have eP3 : P3 = ((2 * r + 1).factorial : ℚ) / (r.factorial : ℚ) := by
      rw [eq_div_iff f2]; linear_combination d3
    rw [eC, eP2, eP3, ← hpow]
    push_cast
    field_simp
    ring
  · have hae : (h : ℕ) = K + 1 := by omega
    have hnu : nuV K h = ((2 * K + 1 + 1).choose (h : ℕ) : ℚ) := by simp [nuV, FV, hae]
    rw [hnu]
    generalize ha : (h : ℕ) = a at *
    subst hae
    rw [Nat.sub_self, prod_range_zero, mul_one]
    have p1 : ∏ k ∈ range (K + 1), |yv K k - yv K (K + 1)|
        = ∏ k ∈ range (K + 1), (4 * ((((0 + (K + 1) : ℕ) : ℚ) - k) * (((0 + (K + 1) : ℕ) : ℚ) - k))) := by
      refine prod_congr rfl fun k hk => ?_
      rw [abs_of_nonneg]
      · simp only [yv]; push_cast; ring
      · simp only [yv]; push_cast; nlinarith [sq_nonneg ((2 * (K : ℚ) + 1 + 1) - 2 * (k : ℚ))]
    rw [p1, prod_mul_distrib, prod_mul_distrib, prod_const, card_range]
    have d1 := desc 0 (K + 1)
    simp only [Nat.factorial_zero, Nat.cast_one, mul_one] at d1
    rw [d1]
    have hC := Nat.choose_mul_factorial_mul_factorial (show K + 1 ≤ 2 * K + 1 + 1 by omega)
    rw [show 2 * K + 1 + 1 - (K + 1) = K + 1 by omega] at hC
    have hCq : ((2 * K + 1 + 1).choose (K + 1) : ℚ) * ((K + 1).factorial : ℚ) * ((K + 1).factorial : ℚ)
        = ((2 * K + 1 + 1).factorial : ℚ) := by exact_mod_cast hC
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, zero_add, ← hCq]
    ring

/-- **the full-shell step**: `(m+1) V_{m+1} = 4^m (2m)! V_m`, `m = K+1`. -/
theorem V_full (K : ℕ) :
    ((K + 1 : ℕ) + 1 : ℚ) * Bali.VB.VBvol (fun h : Fin (K + 1 + 1) => yv K (h : ℕ)) (nuV K) (K + 1 + 1)
      = 4 ^ (K + 1) * ((2 * (K + 1)).factorial : ℚ)
          * Bali.VB.VBvol (fun h : Fin (K + 1 + 1) => yv K (h : ℕ)) (nuV K) (K + 1) := by
  rw [Bali.ShellX.VBvol_eq_VBs, Bali.ShellX.VBvol_eq_VBs]
  have hw : ∀ i : Fin (K + 1 + 1), nuV K i ≠ 0 := by
    intro i; have hi := i.isLt; unfold nuV FV; split_ifs
    · exact mul_ne_zero two_ne_zero (by exact_mod_cast (Nat.choose_pos (by omega)).ne')
    · exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hinj : Function.Injective (fun h : Fin (K + 1 + 1) => yv K (h : ℕ)) := Bali.VE.yv_anti.injective
  rw [lagrange _ _ hw hinj]
  have hs : ∑ i : Fin (K + 1 + 1), 1 / (nuV K i * ∏ k ∈ univ.erase i, |yv K (k : ℕ) - yv K (i : ℕ)|)
      = ((K + 1 : ℕ) + 1 : ℚ) / (4 ^ (K + 1) * ((2 * (K + 1)).factorial : ℚ)) := by
    simp only [term_const, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  rw [hs]
  have : (4 : ℚ) ^ (K + 1) * ((2 * (K + 1)).factorial : ℚ) ≠ 0 := by positivity
  field_simp

/-! ## the Γ side -/

/-- the diagonal ratio `ρ_m = 4^m (2m)!/(m+1)`. -/
theorem crE_diag (m : ℕ) : Bali.VE.crE m m (Bali.VE.Kc m) = 4 ^ m * ((2 * m).factorial : ℝ) / ((m : ℝ) + 1) := by
  have hs : (0 : ℝ) < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have G0 : Real.Gamma ((m : ℝ) - (m : ℝ) + 3 / 2) = √Real.pi / 2 := by
    rw [show (m : ℝ) - (m : ℝ) + 3 / 2 = ((1 : ℕ) : ℝ) + 1 / 2 by ring, Bali.ConjB.Gamma_half]
    norm_num [Nat.factorial]; ring
  have G1 : Real.Gamma ((m : ℝ) - (m : ℝ) + 1) = 1 := by rw [show (m : ℝ) - (m : ℝ) + 1 = 1 by ring, Real.Gamma_one]
  unfold Bali.VE.crE
  rw [G0, G1]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · rw [Bali.VE.Kc_even]
    unfold Bali.ConjB.Ke
    rw [show (2 * ((2 * k : ℕ) : ℝ) - ((2 * k : ℕ) : ℝ) + 1) / 2 = ((k : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      show (2 * ((2 * k : ℕ) : ℝ) - ((2 * k : ℕ) : ℝ) + 3) / 2 = ((k + 1 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half, Bali.ConjB.Gamma_half, show 2 * (k + 1) = (2 * k + 1) + 1 by ring,
      Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (2 * k), Nat.factorial_succ k]
    have := hs.ne'
    push_cast
    field_simp
    ring
  · rw [Bali.VE.Kc_odd]
    unfold Bali.ConjB.Ko
    rw [show (2 * ((2 * k + 1 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) + 1) / 2 = ((k + 1 : ℕ) : ℝ) by push_cast; ring,
      show (2 * ((2 * k + 1 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) + 3) / 2 = ((k + 1 : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial, show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring, Real.Gamma_nat_eq_factorial,
      Nat.factorial_succ k]
    have := hs.ne'
    push_cast
    field_simp
    ring

/-- beyond all shells the Γ product vanishes (`Γ(0) = 0`). -/
lemma crE_beyond (m : ℕ) (K : ℝ) : Bali.VE.crE m (m + 1) K = 0 := by
  unfold Bali.VE.crE
  rw [show (m : ℝ) - ((m + 1 : ℕ) : ℝ) + 1 = 0 by push_cast; ring, Real.Gamma_zero]
  simp

/-- **Conjecture B for even `n = 2m` (`m ≥ 3`), shell form, for every `d`** (both sides vanish for `d > m+1`). -/
theorem conjB_evenN_all (s d : ℕ) :
    ((Bali.VB.VBvol (fun h : Fin (s + 2 + 1 + 1) => yv (s + 2) (h : ℕ)) (nuV (s + 2)) d : ℚ) : ℝ)
      = ∏ j ∈ range d, Bali.VE.crE (s + 3) j (Bali.VE.Kc j) := by
  rcases Nat.lt_or_ge d (s + 4) with h | h
  · exact Bali.VE.conjB_evenN_full s d (by omega)
  · rcases Nat.lt_or_ge d (s + 5) with h' | h'
    · obtain rfl : d = s + 4 := by omega
      have hv := V_full (s + 2)
      have hprev := Bali.VE.conjB_evenN_full s (s + 3) le_rfl
      rw [prod_range_succ, ← hprev, crE_diag]
      have hn : ((s + 2 + 1 : ℕ) + 1 : ℚ) ≠ 0 := by positivity
      have hv' : Bali.VB.VBvol (fun h : Fin (s + 2 + 1 + 1) => yv (s + 2) (h : ℕ)) (nuV (s + 2)) (s + 4)
          = 4 ^ (s + 3) * ((2 * (s + 3)).factorial : ℚ)
            * Bali.VB.VBvol (fun h : Fin (s + 2 + 1 + 1) => yv (s + 2) (h : ℕ)) (nuV (s + 2)) (s + 3)
            / ((s + 2 + 1 : ℕ) + 1 : ℚ) := by
        rw [eq_div_iff hn]; linear_combination hv
      rw [hv']
      push_cast
      ring
    · have hz : Bali.VB.VBvol (fun h : Fin (s + 2 + 1 + 1) => yv (s + 2) (h : ℕ)) (nuV (s + 2)) d = 0 := by
        unfold Bali.VB.VBvol
        rw [powersetCard_eq_empty.2 (by rw [card_univ, Fintype.card_fin]; omega), sum_empty]
      rw [hz, Rat.cast_zero, eq_comm]
      exact prod_eq_zero (mem_range.2 (show s + 3 + 1 < d by omega)) (crE_beyond (s + 3) _)

/-- **the same in the point form**, every `d`. -/
theorem conjB_evenN_x_all (s d : ℕ) :
    ((VBs (fun x : Fin (2 * (s + 2) + 3) => (2 * (x : ℚ) - (2 * (s + 2) + 2)) ^ 2)
        (fun x => ((2 * (s + 2) + 2).choose (x : ℕ) : ℚ)) d : ℚ) : ℝ)
      = ∏ j ∈ range d, Bali.VE.crE (s + 3) j (Bali.VE.Kc j) := by
  have h := Bali.ShellXE.VBx_eq_even (s + 2) d
  push_cast at h
  rw [h, conjB_evenN_all]

end Bali.EF

#print axioms Bali.EF.conjB_evenN_x_all
#print axioms Bali.EF.term_const
#print axioms Bali.EF.V_full