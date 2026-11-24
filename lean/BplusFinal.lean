import P699.BplusAssemble
import P699.ShellXE

/-!
# Theorem B⁺ (`a = +1/2`) for every `n ≥ 1` and every `d` (Bali lab, 2026-11-02)
`V'_d = Σ ∏ C(n,x_i)|2x_i-n| ∏ |(2x_j-n)²-(2x_i-n)²|`, with the Γ ratios of the paper.
-/

open Finset Polynomial

namespace Bali.BP
open Bali.Skew Bali.VB Bali.ShellX Bali.ShellXE Bali.Final

/-! ## duplication -/

lemma dup (D : ℕ) : Real.Gamma (((D : ℝ) + 1) / 2) * Real.Gamma (((D : ℝ) + 2) / 2)
    = (D.factorial : ℝ) * √Real.pi / 2 ^ D := by
  have h := Real.Gamma_mul_Gamma_add_half (((D : ℝ) + 1) / 2)
  rw [show ((D : ℝ) + 1) / 2 + 1 / 2 = ((D : ℝ) + 2) / 2 by ring,
    show 2 * (((D : ℝ) + 1) / 2) = (D : ℝ) + 1 by ring, Real.Gamma_nat_eq_factorial,
    show 1 - ((D : ℝ) + 1) = -(D : ℝ) by ring, Real.rpow_neg (by norm_num), Real.rpow_natCast] at h
  rw [h]; field_simp

/-! ## odd `n = 2H+1` -/

def nuPO (H : ℕ) : Fin (H + 1) → ℚ :=
  fun h => 2 * ((2 * H + 1).choose (h : ℕ) : ℚ) * (2 * (H : ℚ) + 1 - 2 * (h : ℕ))

lemma TpO_pos (H a : ℕ) (ha : a ≤ H) : 0 < TpO H a := by
  have h := TpO_closed H a ha
  have hc : (0 : ℚ) < ((2 * H + 1).choose a : ℚ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hr : (0 : ℚ) < 2 * (2 * (H : ℚ) + 1) * ((2 * H).choose H : ℚ) := by
    have : (0 : ℚ) < ((2 * H).choose H : ℚ) := by exact_mod_cast Nat.choose_pos (by omega)
    positivity
  rw [← h] at hr
  exact (pos_iff_pos_of_mul_pos hr).1 hc

theorem VpO (H d : ℕ) (hd : d ≤ H + 1) :
    VBvol (tS H) (nuPO H) d = ∏ p ∈ range d,
      (TpO H p / ((Bali.Racah.RP (2 * H + 1) p).leadingCoeff * (1 / 4) ^ p)) := by
  have hEr : ∀ s, Er (tS H) (nuPO H) (Pa (2 * H + 1)) s = fun k : Fin (H + 1) =>
      2 * ((2 * H + 1).choose k : ℚ) * ((2 * (H : ℚ) + 1 - 2 * (k : ℕ)) * Bali.Racah.Rq (2 * H + 1) s (k : ℕ)) := by
    intro s; funext k
    simp only [Er, tS, nuPO, Pa_eval_shell]; ring
  have hTt : ∀ s, Tt (tS H) (nuPO H) (Pa (2 * H + 1)) s = TpO H s := by
    intro s
    rw [Tt, hEr, TpO]
    exact Fin.sum_univ_eq_sum_range (fun k => 2 * ((2 * H + 1).choose k : ℚ) *
      ((2 * (H : ℚ) + 1 - 2 * k) * Bali.Racah.Rq (2 * H + 1) s k)) (H + 1)
  have hν : ∀ h, 0 ≤ nuPO H h := by
    intro h
    have hh : ((h : ℕ) : ℚ) ≤ H := by exact_mod_cast (by have := h.isLt; omega : (h : ℕ) ≤ H)
    have : (0 : ℚ) ≤ 2 * (H : ℚ) + 1 - 2 * (h : ℕ) := by linarith
    simp only [nuPO]; positivity
  have hco : ∀ p, p ≤ H → ((Pa (2 * H + 1) p).coeff p)
      = (Bali.Racah.RP (2 * H + 1) p).leadingCoeff * (1 / 4) ^ p := by
    intro p hp
    rw [← Pa_leading H p hp, Polynomial.leadingCoeff, Pa_natDegree H p hp]
  have hcpos : ∀ p, p ≤ H → 0 < (Bali.Racah.RP (2 * H + 1) p).leadingCoeff * (1 / 4 : ℚ) ^ p :=
    fun p hp => mul_pos (Bali.ConjB.ell_pos H p hp) (by positivity)
  have key := V_abs (t := tS H) (ν := nuPO H) (G := Pa (2 * H + 1)) (tS_anti H) hν
    (fun p hp => (Pa_natDegree H p hp).le)
    (fun s r hsr hr => by
      rw [hEr, hEr, hTt, hTt, Bali.OddB.skew_anti, gram_odd H r s hsr hr]; ring)
    d hd (fun p hp => by rw [hTt]; exact (TpO_pos H p (by omega)).ne')
  have e1 : ∏ p ∈ range d, |(Pa (2 * H + 1) p).coeff p|
      = ∏ p ∈ range d, ((Bali.Racah.RP (2 * H + 1) p).leadingCoeff * (1 / 4) ^ p) :=
    prod_congr rfl fun p hp => by
      have hp' : p ≤ H := by have := mem_range.1 hp; omega
      rw [hco p hp', abs_of_pos (hcpos p hp')]
  have e2 : ∏ p ∈ range d, |Tt (tS H) (nuPO H) (Pa (2 * H + 1)) p| = ∏ p ∈ range d, TpO H p :=
    prod_congr rfl fun p hp => by
      rw [hTt, abs_of_pos (TpO_pos H p (by have := mem_range.1 hp; omega))]
  rw [e1, e2] at key
  have hne : ∏ p ∈ range d, ((Bali.Racah.RP (2 * H + 1) p).leadingCoeff * (1 / 4 : ℚ) ^ p) ≠ 0 :=
    prod_ne_zero_iff.2 fun p hp => (hcpos p (by have := mem_range.1 hp; omega)).ne'
  rw [prod_div_distrib, eq_div_iff hne, mul_comm]
  exact key

theorem VpO_x (H d : ℕ) :
    VBs (fun x : Fin (2 * H + 2) => (2 * (x : ℚ) - (2 * H + 1)) ^ 2)
        (fun x => ((2 * H + 1).choose (x : ℕ) : ℚ) * |2 * (x : ℚ) - (2 * H + 1)|) d
      = VBvol (tS H) (nuPO H) d := by
  have ht : (fun x : Fin (2 * H + 2) => (2 * (x : ℚ) - (2 * H + 1)) ^ 2) = tS H ∘ shF H := by
    funext x
    have hx := x.2
    simp only [Function.comp_apply, tS, shF]
    split_ifs with h
    · ring
    · rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hν : nuPO H = fun h =>
      (fun x : Fin (2 * H + 2) => ((2 * H + 1).choose (x : ℕ) : ℚ) * |2 * (x : ℚ) - (2 * H + 1)|) (loF H h)
        + (fun x : Fin (2 * H + 2) => ((2 * H + 1).choose (x : ℕ) : ℚ) * |2 * (x : ℚ) - (2 * H + 1)|) (hiF H h) := by
    funext h
    have hh := h.2
    have hle : ((h : ℕ) : ℚ) ≤ H := by exact_mod_cast (by omega : (h : ℕ) ≤ H)
    simp only [nuPO, loF, hiF]
    rw [Nat.choose_symm (by omega), Nat.cast_sub (by omega), abs_of_nonpos (by linarith),
      abs_of_nonneg (by push_cast; linarith)]
    push_cast; ring
  rw [ht, VBs_shell (shF H) (loF H) (hiF H) (shF_fib H) (loF_ne_hiF H), VBvol_eq_VBs, hν]

lemma facO (H d : ℕ) (hd : d ≤ H) :
    TpO H d / ((Bali.Racah.RP (2 * H + 1) d).leadingCoeff * (1 / 4) ^ d)
      = 2 * ((2 * H + 1).factorial : ℚ) * (d.factorial : ℚ) * 4 ^ d * ((2 * H + 1 - 2 * d).factorial : ℚ)
        / (((2 * H + 1 - d).factorial : ℚ) * ((H - d).factorial : ℚ) ^ 2) := by
  have hC := TpO_closed H d hd
  rw [Nat.cast_choose ℚ (show d ≤ 2 * H + 1 by omega), Nat.cast_choose ℚ (show H ≤ 2 * H by omega),
    show 2 * H - H = H by omega] at hC
  rw [Bali.ConjB.ell_closed H d hd]
  have hF : ((2 * H + 1).factorial : ℚ) = (2 * (H : ℚ) + 1) * ((2 * H).factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h1 : ((2 * H + 1 - d).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((H - d).factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((2 * H + 1 - 2 * d).factorial : ℚ) ≠ 0 := by positivity
  have h4 : (d.factorial : ℚ) ≠ 0 := by positivity
  have h5 : (H.factorial : ℚ) ≠ 0 := by positivity
  have h6 : ((2 * H + 1).factorial : ℚ) ≠ 0 := by positivity
  have h7 : ((2 * H).factorial : ℚ) ≠ 0 := by positivity
  have hT : TpO H d = 2 * (2 * (H : ℚ) + 1) * ((2 * H).factorial : ℚ) / ((H.factorial : ℚ) * H.factorial)
      * ((d.factorial : ℚ) * ((2 * H + 1 - d).factorial : ℚ)) / ((2 * H + 1).factorial : ℚ) := by
    field_simp at hC ⊢
    linear_combination hC
  rw [hT, hF]
  field_simp
  rw [← mul_pow]; norm_num

/-- the ratio of the paper, `n = 2H+1`. -/
noncomputable def crPo (H d : ℕ) : ℝ :=
  2 ^ (d + 1) * (d.factorial : ℝ) * ((2 * H + 1).factorial : ℝ)
    / (Real.Gamma ((2 * (H : ℝ) + 1 - d + 1) / 2) * Real.Gamma ((2 * (H : ℝ) + 1 - d + 2) / 2))
    * (Real.Gamma ((2 * (H : ℝ) + 1) / 2 - d + 1) / Real.Gamma ((2 * (H : ℝ) + 1) / 2 - d + 1 / 2))

lemma crPo_val (H d : ℕ) (hd : d ≤ H) :
    crPo H d = ((2 * ((2 * H + 1).factorial : ℚ) * (d.factorial : ℚ) * 4 ^ d * ((2 * H + 1 - 2 * d).factorial : ℚ)
        / (((2 * H + 1 - d).factorial : ℚ) * ((H - d).factorial : ℚ) ^ 2) : ℚ) : ℝ) := by
  obtain ⟨r, rfl⟩ : ∃ r, H = d + r := ⟨H - d, by omega⟩
  unfold crPo
  rw [show 2 * (d + r) + 1 - 2 * d = 2 * r + 1 by omega, show 2 * (d + r) + 1 - d = d + 2 * r + 1 by omega,
    show d + r - d = r by omega,
    show (2 * ((d + r : ℕ) : ℝ) + 1 - d + 1) / 2 = (((d + 2 * r + 1 : ℕ) : ℝ) + 1) / 2 by push_cast; ring,
    show (2 * ((d + r : ℕ) : ℝ) + 1 - d + 2) / 2 = (((d + 2 * r + 1 : ℕ) : ℝ) + 2) / 2 by push_cast; ring,
    show (2 * ((d + r : ℕ) : ℝ) + 1) / 2 - d + 1 = ((r + 1 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
    show (2 * ((d + r : ℕ) : ℝ) + 1) / 2 - d + 1 / 2 = (r : ℝ) + 1 by push_cast; ring,
    dup, Bali.ConjB.Gamma_half, Real.Gamma_nat_eq_factorial,
    show 2 * (r + 1) = (2 * r + 1) + 1 by ring, Nat.factorial_succ (2 * r + 1), Nat.factorial_succ r]
  have hs : √Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have p1 : (2 : ℝ) ^ (d + 2 * r + 1) = 2 ^ d * ((2 : ℝ) ^ r) ^ 2 * 2 := by ring
  have p2 : (4 : ℝ) ^ (r + 1) = 4 * ((2 : ℝ) ^ r) ^ 2 := by
    rw [pow_succ, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring
  have p3 : (4 : ℝ) ^ d = ((2 : ℝ) ^ d) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  push_cast
  rw [p1, p2, p3, pow_succ (2 : ℝ) d]
  have a1 : (((d + 2 * r + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have a2 : ((r.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have a3 : (r : ℝ) + 1 ≠ 0 := by positivity
  have a4 : ((2 : ℝ) ^ r) ≠ 0 := by positivity
  field_simp
  ring

lemma crPo_beyond (H : ℕ) : crPo H (H + 1) = 0 := by
  unfold crPo
  rw [show (2 * (H : ℝ) + 1) / 2 - ((H + 1 : ℕ) : ℝ) + 1 / 2 = 0 by push_cast; ring, Real.Gamma_zero]
  simp

/-- **Theorem B⁺, odd `n`, every `d`.** -/
theorem Bplus_odd (H d : ℕ) :
    ((VBs (fun x : Fin (2 * H + 2) => (2 * (x : ℚ) - (2 * H + 1)) ^ 2)
        (fun x => ((2 * H + 1).choose (x : ℕ) : ℚ) * |2 * (x : ℚ) - (2 * H + 1)|) d : ℚ) : ℝ)
      = ∏ p ∈ range d, crPo H p := by
  rw [VpO_x]
  rcases Nat.lt_or_ge d (H + 2) with h | h
  · rw [VpO H d (by omega)]
    push_cast [← Rat.cast_prod]
    rw [Rat.cast_prod]
    refine prod_congr rfl fun p hp => ?_
    have hp' : p ≤ H := by have := mem_range.1 hp; omega
    rw [crPo_val H p hp', facO H p hp']
  · have hz : VBvol (tS H) (nuPO H) d = 0 := by
      unfold VBvol
      rw [powersetCard_eq_empty.2 (by rw [card_univ, Fintype.card_fin]; omega), sum_empty]
    rw [hz, Rat.cast_zero, eq_comm]
    exact prod_eq_zero (mem_range.2 (show H + 1 < d by omega)) (crPo_beyond H)

/-! ## dropping a point of weight zero -/

lemma VBs_drop {M : ℕ} (f w : Fin (M + 1 + 1) → ℚ) (h0 : w (Fin.last _) = 0) (d : ℕ) :
    VBs f w d = VBs (f ∘ Fin.castSucc) (w ∘ Fin.castSucc) d := by
  classical
  unfold VBs
  have hinj : Function.Injective (Fin.castSucc : Fin (M + 1) → Fin (M + 1 + 1)) := Fin.castSucc_injective _
  have hterm : ∀ S : Finset (Fin (M + 1)), (∏ x ∈ S, (w ∘ Fin.castSucc) x) * Pp (f ∘ Fin.castSucc) S
      = (∏ x ∈ S.image Fin.castSucc, w x) * Pp f (S.image Fin.castSucc) := by
    intro S
    rw [prod_image (fun a _ b _ h => hinj h), Pp_image f Fin.castSucc S hinj.injOn]
    rfl
  rw [sum_congr rfl fun S _ => hterm S,
    ← sum_image (f := fun X => (∏ x ∈ X, w x) * Pp f X) (g := fun S => S.image Fin.castSucc)
      (s := (univ : Finset (Fin (M + 1))).powersetCard d) (fun a _ b _ h => image_injective hinj h)]
  symm
  refine sum_subset ?_ ?_
  · intro X hX
    obtain ⟨S, hS, rfl⟩ := mem_image.1 hX
    exact mem_powersetCard.2 ⟨subset_univ _, by
      rw [card_image_of_injective _ hinj]; exact (mem_powersetCard.1 hS).2⟩
  · intro X hX hn
    have hlast : Fin.last _ ∈ X := by
      by_contra hl
      apply hn
      refine mem_image.2 ⟨univ.filter (fun i => Fin.castSucc i ∈ X), ?_, ?_⟩
      · have him : (univ.filter (fun i => Fin.castSucc i ∈ X)).image Fin.castSucc = X := by
          ext y
          simp only [mem_image, mem_filter, mem_univ, true_and]
          constructor
          · rintro ⟨a, ha, rfl⟩; exact ha
          · intro hy
            rcases Fin.eq_castSucc_or_eq_last y with ⟨a, rfl⟩ | rfl
            · exact ⟨a, hy, rfl⟩
            · exact absurd hy hl
        refine mem_powersetCard.2 ⟨subset_univ _, ?_⟩
        rw [← card_image_of_injective _ hinj, him]
        exact (mem_powersetCard.1 hX).2
      · ext y
        simp only [mem_image, mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨a, ha, rfl⟩; exact ha
        · intro hy
          rcases Fin.eq_castSucc_or_eq_last y with ⟨a, rfl⟩ | rfl
          · exact ⟨a, hy, rfl⟩
          · exact absurd hy hl
    rw [prod_eq_zero hlast h0, zero_mul]

/-! ## even `n = 2M+2` -/

def tPE (M : ℕ) : Fin (M + 1) → ℚ := fun h => Bali.EvenPsi.yv M (h : ℕ)

def nuPE (M : ℕ) : Fin (M + 1) → ℚ :=
  fun h => 2 * ((2 * (M + 1)).choose (h : ℕ) : ℚ) * (2 * ((M + 1 : ℕ) : ℚ) - 2 * (h : ℕ))

noncomputable def GPE (M s : ℕ) : ℚ[X] := (Bali.Chr.RPE (M + 1) s).comp (Bali.VE.Lt M)

lemma TpE_pos (M a : ℕ) (ha : a ≤ M) : 0 < TpE M a := by
  have h := TpE_closed M a ha
  have hc : (0 : ℚ) < ((2 * M + 2).choose a : ℚ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hr : (0 : ℚ) < 2 * (2 * (M : ℚ) + 2) * ((2 * M + 1).choose M : ℚ) := by
    have : (0 : ℚ) < ((2 * M + 1).choose M : ℚ) := by exact_mod_cast Nat.choose_pos (by omega)
    positivity
  rw [← h] at hr
  exact (pos_iff_pos_of_mul_pos hr).1 hc

lemma ellE_pos (M a : ℕ) (ha : a ≤ M) : 0 < (Bali.Chr.RPE (M + 1) a).coeff a := by
  rw [Bali.Chr.ell_closedE M a ha]; positivity

lemma ErE (M s : ℕ) : Er (tPE M) (nuPE M) (GPE M) s = fun k : Fin (M + 1) =>
    2 * ((2 * (M + 1)).choose k : ℚ) * ((2 * ((M + 1 : ℕ) : ℚ) - 2 * (k : ℕ)) * Bali.RE.RE (M + 1) s (k : ℕ)) := by
  funext k
  have h1 : (GPE M s).eval (tPE M k) = Bali.RE.RE (M + 1) s (k : ℕ) := by
    rw [GPE, eval_comp, show tPE M k = Bali.EvenPsi.yv M (k : ℕ) from rfl, Bali.VE.Lt_eval, Bali.VE.lamS,
      Bali.Chr.RPE_eval]
  rw [Er, h1, nuPE]
  ring

lemma TtE (M s : ℕ) : Tt (tPE M) (nuPE M) (GPE M) s = TpE M s := by
  rw [Tt, ErE, TpE]
  exact Fin.sum_univ_eq_sum_range (fun k => 2 * ((2 * (M + 1)).choose k : ℚ) *
    ((2 * ((M + 1 : ℕ) : ℚ) - 2 * k) * Bali.RE.RE (M + 1) s k)) (M + 1)

lemma nuPE_nonneg (M : ℕ) (h : Fin (M + 1)) : 0 ≤ nuPE M h := by
  have hh : ((h : ℕ) : ℚ) ≤ M := by exact_mod_cast (by have := h.isLt; omega : (h : ℕ) ≤ M)
  have : (0 : ℚ) ≤ 2 * ((M + 1 : ℕ) : ℚ) - 2 * (h : ℕ) := by push_cast; linarith
  simp only [nuPE]; positivity

lemma tPE_anti (M : ℕ) : StrictAnti (tPE M) := by
  intro a b hab
  have hab' : ((a : ℕ) : ℚ) < (b : ℕ) := by exact_mod_cast hab
  have hb : ((b : ℕ) : ℚ) ≤ M := by exact_mod_cast (by have := b.isLt; omega : (b : ℕ) ≤ M)
  simp only [tPE, Bali.EvenPsi.yv]
  push_cast
  have h0 : (0 : ℚ) ≤ (a : ℕ) := by positivity
  nlinarith

lemma coE (M p : ℕ) : (GPE M p).coeff p = (Bali.Chr.RPE (M + 1) p).coeff p * (1 / 4) ^ p :=
  Bali.VE.coeff_comp_Lt _ _ (Bali.Chr.RPE_le _ _)

lemma skE (M s r : ℕ) (hsr : s < r) (hr : r ≤ M) :
    skew (Er (tPE M) (nuPE M) (GPE M) s) (Er (tPE M) (nuPE M) (GPE M) r)
      = Tt (tPE M) (nuPE M) (GPE M) s * (-Tt (tPE M) (nuPE M) (GPE M) r) := by
  rw [ErE, ErE, TtE, TtE, Bali.OddB.skew_anti, gram_even M r s hsr hr]; ring

theorem VpE (M d : ℕ) (hd : d ≤ M + 1) :
    VBvol (tPE M) (nuPE M) d = ∏ p ∈ range d,
      (TpE M p / ((Bali.Chr.RPE (M + 1) p).coeff p * (1 / 4) ^ p)) := by
  have hcpos : ∀ p, p ≤ M → 0 < (Bali.Chr.RPE (M + 1) p).coeff p * (1 / 4 : ℚ) ^ p :=
    fun p hp => mul_pos (ellE_pos M p hp) (by positivity)
  have key := V_abs (t := tPE M) (ν := nuPE M) (G := GPE M) (tPE_anti M) (nuPE_nonneg M)
    (fun p _ => Bali.VE.comp_le _ _ (Bali.Chr.RPE_le _ _))
    (skE M) d hd (fun p hp => by rw [TtE]; exact (TpE_pos M p (by omega)).ne')
  have e1 : ∏ p ∈ range d, |(GPE M p).coeff p|
      = ∏ p ∈ range d, ((Bali.Chr.RPE (M + 1) p).coeff p * (1 / 4) ^ p) :=
    prod_congr rfl fun p hp => by
      have hp' : p ≤ M := by have := mem_range.1 hp; omega
      rw [coE, abs_of_pos (hcpos p hp')]
  have e2 : ∏ p ∈ range d, |Tt (tPE M) (nuPE M) (GPE M) p| = ∏ p ∈ range d, TpE M p :=
    prod_congr rfl fun p hp => by
      rw [TtE, abs_of_pos (TpE_pos M p (by have := mem_range.1 hp; omega))]
  rw [e1, e2] at key
  have hne : ∏ p ∈ range d, ((Bali.Chr.RPE (M + 1) p).coeff p * (1 / 4 : ℚ) ^ p) ≠ 0 :=
    prod_ne_zero_iff.2 fun p hp => (hcpos p (by have := mem_range.1 hp; omega)).ne'
  rw [prod_div_distrib, eq_div_iff hne, mul_comm]
  exact key

theorem VpE_x (M d : ℕ) :
    VBs (fun x : Fin (2 * M + 3) => (2 * (x : ℚ) - (2 * M + 2)) ^ 2)
        (fun x => ((2 * M + 2).choose (x : ℕ) : ℚ) * |2 * (x : ℚ) - (2 * M + 2)|) d
      = VBvol (tPE M) (nuPE M) d := by
  have ht : (fun x : Fin (2 * M + 3) => (2 * (x : ℚ) - (2 * M + 2)) ^ 2)
      = (fun h : Fin (M + 2) => Bali.EvenPsi.yv M (h : ℕ)) ∘ shE M := by
    funext x
    have hx := x.2
    simp only [Function.comp_apply, Bali.EvenPsi.yv, shE]
    split_ifs with h
    · push_cast; ring
    · rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [ht, VBs_shellF (shE M) (FE M) (shE_fib M), VBs_drop _ _ (by
      simp only [FE, Fin.val_last, if_true, sum_singleton]
      push_cast; simp; right; ring), VBvol_eq_VBs]
  congr 1
  funext h
  have hh := h.2
  have hle : ((h : ℕ) : ℚ) ≤ M := by exact_mod_cast (by omega : (h : ℕ) ≤ M)
  simp only [Function.comp_apply, FE, Fin.val_castSucc, nuPE]
  rw [if_neg (by omega), sum_pair (by simp [Fin.ext_iff]; omega)]
  simp only
  rw [Nat.choose_symm (by omega), Nat.cast_sub (by omega), abs_of_nonpos (by linarith),
    abs_of_nonneg (by push_cast; linarith), show 2 * (M + 1) = 2 * M + 2 by ring]
  push_cast; ring

lemma facE (M d : ℕ) (hd : d ≤ M) :
    TpE M d / ((Bali.Chr.RPE (M + 1) d).coeff d * (1 / 4) ^ d)
      = 2 * ((2 * M + 2).factorial : ℚ) * (d.factorial : ℚ) * 4 ^ d * ((2 * M + 2 - 2 * d).factorial : ℚ)
        / (((2 * M + 2 - d).factorial : ℚ) * ((M - d).factorial : ℚ) * ((M + 1 - d).factorial : ℚ)) := by
  have hC := TpE_closed M d hd
  rw [Nat.cast_choose ℚ (show d ≤ 2 * M + 2 by omega), Nat.cast_choose ℚ (show M ≤ 2 * M + 1 by omega),
    show 2 * M + 1 - M = M + 1 by omega] at hC
  rw [Bali.Chr.ell_closedE M d hd, show 2 * (M + 1) = 2 * M + 2 by ring]
  have hF : ((2 * M + 2).factorial : ℚ) = (2 * (M : ℚ) + 2) * ((2 * M + 1).factorial : ℚ) := by
    rw [show 2 * M + 2 = (2 * M + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
  have h1 : ((2 * M + 2 - d).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((M - d).factorial : ℚ) ≠ 0 := by positivity
  have h2' : ((M + 1 - d).factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((2 * M + 2 - 2 * d).factorial : ℚ) ≠ 0 := by positivity
  have h4 : (d.factorial : ℚ) ≠ 0 := by positivity
  have h5 : (M.factorial : ℚ) ≠ 0 := by positivity
  have h5' : ((M + 1).factorial : ℚ) ≠ 0 := by positivity
  have h6 : ((2 * M + 2).factorial : ℚ) ≠ 0 := by positivity
  have h7 : ((2 * M + 1).factorial : ℚ) ≠ 0 := by positivity
  have hT : TpE M d = 2 * (2 * (M : ℚ) + 2) * ((2 * M + 1).factorial : ℚ) / ((M.factorial : ℚ) * (M + 1).factorial)
      * ((d.factorial : ℚ) * ((2 * M + 2 - d).factorial : ℚ)) / ((2 * M + 2).factorial : ℚ) := by
    field_simp at hC ⊢
    linear_combination hC
  rw [hT, hF]
  field_simp
  rw [← mul_pow]; norm_num

/-- the ratio of the paper, `n = 2M+2`. -/
noncomputable def crPe (M d : ℕ) : ℝ :=
  2 ^ (d + 1) * (d.factorial : ℝ) * ((2 * M + 2).factorial : ℝ)
    / (Real.Gamma ((2 * (M : ℝ) + 2 - d + 1) / 2) * Real.Gamma ((2 * (M : ℝ) + 2 - d + 2) / 2))
    * (Real.Gamma ((2 * (M : ℝ) + 2) / 2 - d + 1 / 2) / Real.Gamma ((2 * (M : ℝ) + 2) / 2 - d))

lemma crPe_val (M d : ℕ) (hd : d ≤ M) :
    crPe M d = ((2 * ((2 * M + 2).factorial : ℚ) * (d.factorial : ℚ) * 4 ^ d * ((2 * M + 2 - 2 * d).factorial : ℚ)
        / (((2 * M + 2 - d).factorial : ℚ) * ((M - d).factorial : ℚ) * ((M + 1 - d).factorial : ℚ)) : ℚ) : ℝ) := by
  obtain ⟨r, rfl⟩ : ∃ r, M = d + r := ⟨M - d, by omega⟩
  unfold crPe
  rw [show 2 * (d + r) + 2 - 2 * d = 2 * (r + 1) by omega, show 2 * (d + r) + 2 - d = d + 2 * r + 2 by omega,
    show d + r - d = r by omega, show d + r + 1 - d = r + 1 by omega,
    show (2 * ((d + r : ℕ) : ℝ) + 2 - d + 1) / 2 = (((d + 2 * r + 2 : ℕ) : ℝ) + 1) / 2 by push_cast; ring,
    show (2 * ((d + r : ℕ) : ℝ) + 2 - d + 2) / 2 = (((d + 2 * r + 2 : ℕ) : ℝ) + 2) / 2 by push_cast; ring,
    show (2 * ((d + r : ℕ) : ℝ) + 2) / 2 - d + 1 / 2 = ((r + 1 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
    show (2 * ((d + r : ℕ) : ℝ) + 2) / 2 - d = (r : ℝ) + 1 by push_cast; ring,
    dup, Bali.ConjB.Gamma_half, Real.Gamma_nat_eq_factorial]
  have hs : √Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have p1 : (2 : ℝ) ^ (d + 2 * r + 2) = 2 ^ d * ((2 : ℝ) ^ r) ^ 2 * 4 := by ring
  have p2 : (4 : ℝ) ^ (r + 1) = 4 * ((2 : ℝ) ^ r) ^ 2 := by
    rw [pow_succ, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring
  have p3 : (4 : ℝ) ^ d = ((2 : ℝ) ^ d) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  push_cast
  rw [p1, p2, p3, pow_succ (2 : ℝ) d]
  have a1 : (((d + 2 * r + 2).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have a2 : ((r.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have a3 : (((r + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have a4 : ((2 : ℝ) ^ r) ≠ 0 := by positivity
  field_simp

lemma crPe_beyond (M : ℕ) : crPe M (M + 1) = 0 := by
  unfold crPe
  rw [show (2 * (M : ℝ) + 2) / 2 - ((M + 1 : ℕ) : ℝ) = 0 by push_cast; ring, Real.Gamma_zero]
  simp

/-- **Theorem B⁺, even `n ≥ 2`, every `d`.** -/
theorem Bplus_even (M d : ℕ) :
    ((VBs (fun x : Fin (2 * M + 3) => (2 * (x : ℚ) - (2 * M + 2)) ^ 2)
        (fun x => ((2 * M + 2).choose (x : ℕ) : ℚ) * |2 * (x : ℚ) - (2 * M + 2)|) d : ℚ) : ℝ)
      = ∏ p ∈ range d, crPe M p := by
  rw [VpE_x]
  rcases Nat.lt_or_ge d (M + 2) with h | h
  · rw [VpE M d (by omega), Rat.cast_prod]
    refine prod_congr rfl fun p hp => ?_
    have hp' : p ≤ M := by have := mem_range.1 hp; omega
    rw [crPe_val M p hp', facE M p hp']
  · have hz : VBvol (tPE M) (nuPE M) d = 0 := by
      unfold VBvol
      rw [powersetCard_eq_empty.2 (by rw [card_univ, Fintype.card_fin]; omega), sum_empty]
    rw [hz, Rat.cast_zero, eq_comm]
    exact prod_eq_zero (mem_range.2 (show M + 1 < d by omega)) (crPe_beyond M)

end Bali.BP

#print axioms Bali.BP.Bplus_odd
#print axioms Bali.BP.Bplus_even
