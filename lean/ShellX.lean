import P699.Final

/-!
# Shell form vs `x` form of `V^B` (Bali lab, 2026-11-01)
(a) pair products without enumeration; (b)–(d) `P² = ∏_{a≠b}` trick, fibres over shell sets,
`VBx_eq_VBvol` and `theorem_Bodd_x` (Theorem Bodd in the point form).
-/

open Finset

namespace Bali.ShellX

lemma map_univ_orderEmb {N d : ℕ} (S : Finset (Fin (N + 1))) (h : S.card = d) :
    (univ : Finset (Fin d)).map (S.orderEmbOfFin h).toEmbedding = S := by
  apply eq_of_subset_of_card_le
  · intro b hb
    obtain ⟨i, _, rfl⟩ := mem_map.1 hb
    exact S.orderEmbOfFin_mem h i
  · rw [card_map, card_univ, Fintype.card_fin, h]

lemma filter_gt_orderEmb {N d : ℕ} (S : Finset (Fin (N + 1))) (h : S.card = d) (i : Fin d) :
    S.filter (fun b => S.orderEmbOfFin h i < b) = (Ioi i).map (S.orderEmbOfFin h).toEmbedding := by
  ext b
  simp only [mem_filter, mem_map, mem_Ioi]
  constructor
  · rintro ⟨hb, hlt⟩
    rw [← map_univ_orderEmb S h] at hb
    obtain ⟨j, _, rfl⟩ := mem_map.1 hb
    exact ⟨j, (S.orderEmbOfFin h).lt_iff_lt.1 hlt, rfl⟩
  · rintro ⟨j, hij, rfl⟩
    exact ⟨S.orderEmbOfFin_mem h j, (S.orderEmbOfFin h).lt_iff_lt.2 hij⟩

/-- **(a)** sorted pair product = pair product over `a < b` in `S`. -/
theorem prod_pairs_orderEmb {N d : ℕ} (S : Finset (Fin (N + 1))) (h : S.card = d)
    (F : Fin (N + 1) → Fin (N + 1) → ℚ) :
    ∏ i : Fin d, ∏ j ∈ Ioi i, F (S.orderEmbOfFin h i) (S.orderEmbOfFin h j)
      = ∏ a ∈ S, ∏ b ∈ S.filter (fun b => a < b), F a b := by
  calc ∏ i : Fin d, ∏ j ∈ Ioi i, F (S.orderEmbOfFin h i) (S.orderEmbOfFin h j)
      = ∏ a ∈ (univ : Finset (Fin d)).map (S.orderEmbOfFin h).toEmbedding,
          ∏ b ∈ S.filter (fun b => a < b), F a b := by
        rw [prod_map]
        refine prod_congr rfl fun i _ => ?_
        rw [show (S.orderEmbOfFin h).toEmbedding i = S.orderEmbOfFin h i from rfl,
          filter_gt_orderEmb S h i, prod_map]
        rfl
    _ = _ := by rw [map_univ_orderEmb]

lemma prod_orderEmb {N d : ℕ} (S : Finset (Fin (N + 1))) (h : S.card = d) (f : Fin (N + 1) → ℚ) :
    ∏ q : Fin d, f (S.orderEmbOfFin h q) = ∏ a ∈ S, f a := by
  conv_rhs => rw [← map_univ_orderEmb S h]
  rw [prod_map]; rfl





/-! ## (b)–(d): order-free pair products, transport through `sh`, fibres over shell sets -/

section Shell
variable {β γ : Type*} [LinearOrder β] [LinearOrder γ]

/-- pair product over `a < b` in `X`. -/
def Pp (f : β → ℚ) (X : Finset β) : ℚ := ∏ a ∈ X, ∏ b ∈ X.filter (fun b => a < b), |f b - f a|

/-- product over all ordered pairs `a ≠ b` in `X` (no order needed). -/
def Qd (f : β → ℚ) (X : Finset β) : ℚ := ∏ a ∈ X, ∏ b ∈ X, if a ≠ b then |f b - f a| else 1

lemma Pp_nonneg (f : β → ℚ) (X : Finset β) : 0 ≤ Pp f X :=
  prod_nonneg fun _ _ => prod_nonneg fun _ _ => abs_nonneg _

/-- the trick: `P² = ∏_{a ≠ b}`. -/
lemma Pp_sq (f : β → ℚ) (X : Finset β) : Pp f X ^ 2 = Qd f X := by
  have h1 : Pp f X = ∏ a ∈ X, ∏ b ∈ X, if a < b then |f b - f a| else 1 := by
    unfold Pp; exact prod_congr rfl fun a _ => prod_filter _ _
  have h2 : Pp f X = ∏ a ∈ X, ∏ b ∈ X, if b < a then |f b - f a| else 1 := by
    rw [h1, prod_comm]
    refine prod_congr rfl fun a _ => prod_congr rfl fun b _ => ?_
    rw [abs_sub_comm]
  rw [sq]
  nth_rewrite 1 [h1]
  rw [h2, ← prod_mul_distrib]
  refine prod_congr rfl fun a _ => ?_
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h, h.ne, lt_asymm h]
  · simp
  · simp [h, h.ne', lt_asymm h]

lemma Qd_image (t : γ → ℚ) (sh : β → γ) (X : Finset β) (hinj : Set.InjOn sh X) :
    Qd (t ∘ sh) X = Qd t (X.image sh) := by
  unfold Qd
  rw [prod_image fun a ha b hb h => hinj ha hb h]
  refine prod_congr rfl fun a ha => ?_
  rw [prod_image fun a ha b hb h => hinj ha hb h]
  refine prod_congr rfl fun b hb => ?_
  simp only [Function.comp_apply, ne_eq, hinj.eq_iff ha hb]

lemma Qd_zero (t : γ → ℚ) (sh : β → γ) (X : Finset β) (h : ¬ Set.InjOn sh X) : Qd (t ∘ sh) X = 0 := by
  rw [Set.InjOn] at h
  push_neg at h
  obtain ⟨a, ha, b, hb, hab, hne⟩ := h
  exact prod_eq_zero ha (prod_eq_zero hb (by simp [Function.comp_apply, hab, hne]))

lemma Pp_image (t : γ → ℚ) (sh : β → γ) (X : Finset β) (hinj : Set.InjOn sh X) :
    Pp (t ∘ sh) X = Pp t (X.image sh) :=
  (pow_left_inj₀ (Pp_nonneg _ _) (Pp_nonneg _ _) two_ne_zero).1
    (by rw [Pp_sq, Pp_sq, Qd_image t sh X hinj])

/-- **(b)** two points in one shell kill the term. -/
lemma Pp_zero (t : γ → ℚ) (sh : β → γ) (X : Finset β) (h : ¬ Set.InjOn sh X) : Pp (t ∘ sh) X = 0 :=
  (pow_eq_zero_iff two_ne_zero).1 (by rw [Pp_sq, Qd_zero t sh X h])

variable [Fintype β] [Fintype γ] (sh : β → γ) (lo hi : γ → β)
  (hfib : ∀ x h, sh x = h ↔ x = lo h ∨ x = hi h) (hlh : ∀ h, lo h ≠ hi h)

/-- point sets lying injectively over the shell set `S`. -/
def Fib (S : Finset γ) : Finset (Finset β) :=
  (univ : Finset (Finset β)).filter (fun X => X.image sh = S ∧ X.card = S.card)

include hfib in
lemma Fib_insert (h : γ) (S : Finset γ) (hS : h ∉ S) :
    Fib sh (insert h S) = (Fib sh S ×ˢ ({lo h, hi h} : Finset β)).image (fun p => insert p.2 p.1) := by
  ext Y
  simp only [Fib, mem_filter, mem_univ, true_and, mem_image, mem_product, mem_insert, mem_singleton,
    Prod.exists]
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

include hfib hlh in
/-- **(c)** the weights of the points over `S` add up to `∏_{h∈S} (w(lo h) + w(hi h))`. -/
lemma sum_Fib (w : β → ℚ) (S : Finset γ) :
    ∑ X ∈ Fib sh S, ∏ x ∈ X, w x = ∏ h ∈ S, (w (lo h) + w (hi h)) := by
  induction S using Finset.induction_on with
  | empty =>
    have : Fib sh (∅ : Finset γ) = {∅} := by
      ext X; simp [Fib]
    simp [this]
  | insert h S hS ih =>
    have hxX : ∀ X ∈ Fib sh S, ∀ x, sh x = h → x ∉ X := fun X hX x hxh hm =>
      hS (by rw [← hxh, ← (mem_filter.1 hX).2.1]; exact mem_image_of_mem sh hm)
    rw [Fib_insert sh lo hi hfib h S hS, sum_image, sum_product, prod_insert hS, ← ih, mul_sum]
    · refine sum_congr rfl fun X hX => ?_
      rw [sum_pair (hlh h), prod_insert (hxX X hX _ ((hfib _ h).2 (Or.inl rfl))),
        prod_insert (hxX X hX _ ((hfib _ h).2 (Or.inr rfl)))]
      ring
    · rintro ⟨X, x⟩ hp ⟨X', x'⟩ hq hpq
      simp only [coe_product, Set.mem_prod, mem_coe, mem_insert, mem_singleton] at hp hq hpq
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

/-- volume with points `f`, weights `wt`, pair product over `a < b`. -/
def VBs (f wt : β → ℚ) (d : ℕ) : ℚ :=
  ∑ X ∈ (univ : Finset β).powersetCard d, (∏ x ∈ X, wt x) * Pp f X

include hfib hlh in
/-- **(d), generic.**  Point form = shell form. -/
theorem VBs_shell (t : γ → ℚ) (w : β → ℚ) (d : ℕ) :
    VBs (t ∘ sh) w d = VBs t (fun h => w (lo h) + w (hi h)) d := by
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
    rw [← sum_Fib sh lo hi hfib hlh w S, sum_mul]
    refine sum_congr rfl fun X hX => ?_
    rw [(mem_filter.1 hX).2.1]
  · intro X hX
    have h := mem_filter.1 hX
    exact mem_powersetCard.2 ⟨subset_univ _, by rw [h.2, (mem_powersetCard.1 h.1).2]⟩

end Shell

/-- `VBvol` (sorted enumeration) is `VBs`. -/
lemma VBvol_eq_VBs {N : ℕ} (t ν : Fin (N + 1) → ℚ) (d : ℕ) : Bali.VB.VBvol t ν d = VBs t ν d := by
  unfold Bali.VB.VBvol VBs Pp
  refine sum_congr rfl fun S hS => ?_
  have h := (mem_powersetCard.1 hS).2
  rw [dif_pos h, prod_orderEmb S h, prod_pairs_orderEmb S h (fun a b => |t b - t a|)]

/-! ## The concrete shells: `n = 2H+1`, points `x = 0..n`, `y_x = (2x-n)²`, weights `C(n,x)` -/

def shF (H : ℕ) (x : Fin (2 * H + 2)) : Fin (H + 1) :=
  if hx : (x : ℕ) ≤ H then ⟨x, by omega⟩ else ⟨2 * H + 1 - x, by omega⟩
def loF (H : ℕ) (h : Fin (H + 1)) : Fin (2 * H + 2) := ⟨h, by omega⟩
def hiF (H : ℕ) (h : Fin (H + 1)) : Fin (2 * H + 2) := ⟨2 * H + 1 - h, by omega⟩

lemma shF_fib (H : ℕ) (x : Fin (2 * H + 2)) (h : Fin (H + 1)) :
    shF H x = h ↔ x = loF H h ∨ x = hiF H h := by
  have hx := x.2; have hh := h.2
  unfold shF loF hiF
  split_ifs <;> simp only [Fin.ext_iff] <;> omega

lemma loF_ne_hiF (H : ℕ) (h : Fin (H + 1)) : loF H h ≠ hiF H h := by
  have hh := h.2
  simp only [loF, hiF, ne_eq, Fin.ext_iff]; omega

/-- **Reservation 1 settled.**  The point form of `V^B` equals the shell form used in `theorem_Bodd`. -/
theorem VBx_eq_VBvol (H d : ℕ) :
    VBs (fun x : Fin (2 * H + 2) => (2 * (x : ℚ) - (2 * H + 1)) ^ 2)
        (fun x => ((2 * H + 1).choose (x : ℕ) : ℚ)) d
      = Bali.VB.VBvol (Bali.Final.tS H) (Bali.Final.nuS H) d := by
  have ht : (fun x : Fin (2 * H + 2) => (2 * (x : ℚ) - (2 * H + 1)) ^ 2) = Bali.Final.tS H ∘ shF H := by
    funext x
    have hx := x.2
    simp only [Function.comp_apply, Bali.Final.tS, shF]
    split_ifs with h
    · ring
    · rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hν : Bali.Final.nuS H
      = fun h => (fun x : Fin (2 * H + 2) => ((2 * H + 1).choose (x : ℕ) : ℚ)) (loF H h)
          + (fun x : Fin (2 * H + 2) => ((2 * H + 1).choose (x : ℕ) : ℚ)) (hiF H h) := by
    funext h
    have hh := h.2
    simp only [Bali.Final.nuS, loF, hiF]
    rw [Nat.choose_symm (by omega)]; ring
  rw [ht, VBs_shell (shF H) (loF H) (hiF H) (shF_fib H) (loF_ne_hiF H), VBvol_eq_VBs, hν]

/-- **Theorem Bodd in the point form.** -/
theorem theorem_Bodd_x (H m : ℕ) (hm : 2 * m ≤ H + 1) :
    Matrix.det (Bali.Final.Brac H m) * (Bali.VB.sgnPairs (2 * m) *
      VBs (fun x : Fin (2 * H + 2) => (2 * (x : ℚ) - (2 * H + 1)) ^ 2)
        (fun x => ((2 * H + 1).choose (x : ℕ) : ℚ)) (2 * m))
      = ∏ i : Fin m, Bali.Final.Dval H i := by
  rw [VBx_eq_VBvol]; exact Bali.Final.theorem_Bodd H m hm

end Bali.ShellX

#print axioms Bali.ShellX.VBx_eq_VBvol
#print axioms Bali.ShellX.theorem_Bodd_x
