import P699.ShellX
import P699.EvenAll

/-!
# Point form of `V^B` for even `n` (centre shell with a single point) (Bali lab, 2026-11-02)
Generalises `ShellX.VBs_shell` to arbitrary fibres `F h`.
-/

open Finset Polynomial

namespace Bali.ShellXE
open Bali.ShellX

section Gen
variable {β γ : Type*} [LinearOrder β] [LinearOrder γ] [Fintype β] [Fintype γ] (sh : β → γ) (F : γ → Finset β)
  (hfib : ∀ x h, sh x = h ↔ x ∈ F h)

include hfib in
lemma Fib_insertF (h : γ) (S : Finset γ) (hS : h ∉ S) :
    Fib sh (insert h S) = (Fib sh S ×ˢ F h).image (fun p => insert p.2 p.1) := by
  ext Y
  simp only [Fib, mem_filter, mem_univ, true_and, mem_image, mem_product, Prod.exists]
  constructor
  · rintro ⟨hY, hc⟩
    have hhY : h ∈ Y.image sh := by rw [hY]; exact mem_insert_self h S
    obtain ⟨x, hx, hxh⟩ := mem_image.1 hhY
    have hcard : (Y.image sh).card = Y.card := by rw [hY, hc]
    have hinj : Set.InjOn sh Y := card_image_iff.1 hcard
    have hsub : (Y.erase x).image sh ⊆ S := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := mem_image.1 hz
      have hu' := mem_of_mem_erase hu
      have : sh u ∈ insert h S := by rw [← hY]; exact mem_image_of_mem sh hu'
      rcases mem_insert.1 this with h1 | h1
      · exact absurd (hinj hu' hx (h1.trans hxh.symm)) (ne_of_mem_erase hu)
      · exact h1
    have hcE : (Y.erase x).card = S.card := by
      rw [card_erase_of_mem hx, hc, card_insert_of_notMem hS]; rfl
    refine ⟨Y.erase x, x, ⟨⟨?_, hcE⟩, (hfib x h).1 hxh⟩, insert_erase hx⟩
    apply eq_of_subset_of_card_le hsub
    rw [card_image_of_injOn (hinj.mono fun z hz => mem_of_mem_erase hz), hcE]
  · rintro ⟨X, x, ⟨⟨hX, hc⟩, hx⟩, rfl⟩
    have hxh : sh x = h := (hfib x h).2 hx
    have hxX : x ∉ X := fun hm => hS (by rw [← hxh, ← hX]; exact mem_image_of_mem sh hm)
    refine ⟨by rw [image_insert, hX, hxh], ?_⟩
    rw [card_insert_of_notMem hxX, card_insert_of_notMem hS, hc]

include hfib in
lemma sum_FibF (w : β → ℚ) (S : Finset γ) :
    ∑ X ∈ Fib sh S, ∏ x ∈ X, w x = ∏ h ∈ S, ∑ x ∈ F h, w x := by
  induction S using Finset.induction_on with
  | empty =>
    have : Fib sh (∅ : Finset γ) = {∅} := by ext X; simp [Fib]
    simp [this]
  | insert h S hS ih =>
    have hxX : ∀ X ∈ Fib sh S, ∀ x, sh x = h → x ∉ X := fun X hX x hxh hm =>
      hS (by rw [← hxh, ← (mem_filter.1 hX).2.1]; exact mem_image_of_mem sh hm)
    rw [Fib_insertF sh F hfib h S hS, sum_image, sum_product, prod_insert hS, ← ih, mul_sum]
    · refine sum_congr rfl fun X hX => ?_
      rw [sum_mul]
      refine sum_congr rfl fun x hx => ?_
      rw [prod_insert (hxX X hX x ((hfib x h).2 hx))]
    · rintro ⟨X, x⟩ hp ⟨X', x'⟩ hq hpq
      simp only [coe_product, Set.mem_prod, mem_coe] at hp hq hpq
      have hx : sh x = h := (hfib x h).2 hp.2
      have hx' : sh x' = h := (hfib x' h).2 hq.2
      have hnX := hxX X hp.1 x hx
      have hnX' := hxX X' hq.1 x' hx'
      have hxx : x = x' := by
        have : x ∈ insert x' X' := hpq ▸ mem_insert_self x X
        rcases mem_insert.1 this with h1 | h1
        · exact h1
        · exact absurd h1 (hxX X' hq.1 x hx)
      subst hxx
      rw [← erase_insert hnX, hpq, erase_insert hnX']

include hfib in
theorem VBs_shellF (t : γ → ℚ) (w : β → ℚ) (d : ℕ) :
    VBs (t ∘ sh) w d = VBs t (fun h => ∑ x ∈ F h, w x) d := by
  unfold VBs
  have step1 : ∑ X ∈ (univ : Finset β).powersetCard d, (∏ x ∈ X, w x) * Pp (t ∘ sh) X
      = ∑ X ∈ ((univ : Finset β).powersetCard d).filter (fun X => (X.image sh).card = X.card),
          (∏ x ∈ X, w x) * Pp t (X.image sh) := by
    rw [sum_filter]
    refine sum_congr rfl fun X _ => ?_
    split_ifs with hX
    · rw [Pp_image t sh X (card_image_iff.1 hX)]
    · rw [Pp_zero t sh X (fun hi => hX (card_image_of_injOn hi)), mul_zero]
  rw [step1, ← sum_fiberwise_of_maps_to (g := fun X : Finset β => X.image sh)
    (t := (univ : Finset γ).powersetCard d)]
  · refine sum_congr rfl fun S hS => ?_
    have hSd := (mem_powersetCard.1 hS).2
    have hset : (((univ : Finset β).powersetCard d).filter (fun X => (X.image sh).card = X.card)).filter
        (fun X => X.image sh = S) = Fib sh S := by
      ext X
      simp only [Fib, mem_filter, mem_powersetCard, subset_univ, true_and, mem_univ]
      constructor
      · rintro ⟨⟨_, hi⟩, him⟩; exact ⟨him, by rw [← him, hi]⟩
      · rintro ⟨him, hc⟩; exact ⟨⟨by rw [hc, hSd], by rw [him, hc]⟩, him⟩
    rw [hset]
    beta_reduce
    rw [← sum_FibF sh F hfib w S, sum_mul]
    refine sum_congr rfl fun X hX => ?_
    rw [(mem_filter.1 hX).2.1]
  · intro X hX
    have h := mem_filter.1 hX
    exact mem_powersetCard.2 ⟨subset_univ _, by rw [h.2, (mem_powersetCard.1 h.1).2]⟩

end Gen

/-! ## even `n = 2K+2`: points `x = 0..n`, shells `h = 0..K+1` -/

def shE (K : ℕ) (x : Fin (2 * K + 3)) : Fin (K + 2) :=
  if hx : (x : ℕ) ≤ K + 1 then ⟨x, by omega⟩ else ⟨2 * K + 2 - x, by omega⟩

/-- the fibre of a shell. -/
def FE (K : ℕ) (h : Fin (K + 2)) : Finset (Fin (2 * K + 3)) :=
  if (h : ℕ) = K + 1 then {⟨K + 1, by omega⟩} else {⟨h, by omega⟩, ⟨2 * K + 2 - h, by omega⟩}

lemma shE_fib (K : ℕ) (x : Fin (2 * K + 3)) (h : Fin (K + 2)) : shE K x = h ↔ x ∈ FE K h := by
  have hx := x.2; have hh := h.2
  unfold shE FE
  split_ifs <;> simp only [Fin.ext_iff, mem_insert, mem_singleton] <;> omega

lemma sum_FE (K : ℕ) (h : Fin (K + 2)) :
    ∑ x ∈ FE K h, ((2 * K + 2).choose (x : ℕ) : ℚ) = Bali.EvenPsi.nuV K h := by
  have hh := h.2
  unfold FE Bali.EvenPsi.nuV Bali.EvenPsi.FV
  split_ifs with h1 h2 h2
  · omega
  · rw [sum_singleton]; simp [h1]
  · rw [sum_pair (by simp [Fin.ext_iff]; omega)]
    simp only
    rw [Nat.choose_symm (by omega), show 2 * K + 2 = 2 * K + 1 + 1 by ring]; ring
  · omega

/-- **point form = shell form, even `n`.** -/
theorem VBx_eq_even (K d : ℕ) :
    VBs (fun x : Fin (2 * K + 3) => (2 * (x : ℚ) - (2 * K + 2)) ^ 2) (fun x => ((2 * K + 2).choose (x : ℕ) : ℚ)) d
      = Bali.VB.VBvol (fun h : Fin (K + 1 + 1) => Bali.EvenPsi.yv K (h : ℕ)) (Bali.EvenPsi.nuV K) d := by
  have ht : (fun x : Fin (2 * K + 3) => (2 * (x : ℚ) - (2 * K + 2)) ^ 2)
      = (fun h : Fin (K + 2) => Bali.EvenPsi.yv K (h : ℕ)) ∘ shE K := by
    funext x
    have hx := x.2
    simp only [Function.comp_apply, Bali.EvenPsi.yv, shE]
    split_ifs with h
    · push_cast; ring
    · rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [ht, VBs_shellF (shE K) (FE K) (shE_fib K), VBvol_eq_VBs]
  congr 1
  funext h
  exact sum_FE K h

/-- **Conjecture B for even `n = 2m` (`m ≥ 3`), point form**, every `d ≤ m - 1`. -/
theorem conjB_evenN_x (s d : ℕ) (hd : d ≤ s + 2) :
    ((VBs (fun x : Fin (2 * (s + 2) + 3) => (2 * (x : ℚ) - (2 * (s + 2) + 2)) ^ 2)
        (fun x => ((2 * (s + 2) + 2).choose (x : ℕ) : ℚ)) d : ℚ) : ℝ)
      = ∏ j ∈ range d, Bali.VE.crE (s + 3) j (Bali.VE.Kc j) := by
  have h := VBx_eq_even (s + 2) d
  push_cast at h
  rw [h, Bali.VE.conjB_evenN s d hd]

end Bali.ShellXE

#print axioms Bali.ShellXE.conjB_evenN_x
