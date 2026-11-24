import Mathlib

/-!
# Type B proof, the Gosper step (Bali lab, 2026-10-30)

Lemma ψ of the paper: if `q` satisfies `(n - k) q(k) - k q(k-1) = n g(k)` (with `n = m + 1`), then the partial sums
of `C(n,k) g(k)` telescope:  `Σ_{k ≤ h} C(n,k) g(k) = C(n-1,h) q(h)`.  Here `q`, `g` are arbitrary functions
`ℕ → ℚ` (the existence of a polynomial `q`, the linear-algebra half of the lemma, is not formalized here).
-/

open Finset Nat

namespace Bali

/-- `C(m+1,h+1) (m-h) = (m+1) C(m,h+1)` in `ℚ`, for every `h` (both sides vanish when `h ≥ m`). -/
lemma choose_succ_mul_sub (m h : ℕ) :
    ((m + 1).choose (h + 1) : ℚ) * ((m : ℚ) - h) = ((m : ℚ) + 1) * (m.choose (h + 1) : ℚ) := by
  rcases le_or_gt h m with hh | hh
  · have a := Nat.choose_mul_succ_eq m (h + 1)
    have hs : m + 1 - (h + 1) = m - h := by omega
    rw [hs] at a
    have := congrArg (fun x : ℕ => (x : ℚ)) a
    push_cast [Nat.cast_sub hh] at this; linarith
  · rw [Nat.choose_eq_zero_of_lt (by omega : m + 1 < h + 1), Nat.choose_eq_zero_of_lt (by omega : m < h + 1)]
    simp

/-- `C(m+1,h+1) (h+1) = (m+1) C(m,h)` in `ℚ`. -/
lemma choose_succ_mul_succ (m h : ℕ) :
    ((m + 1).choose (h + 1) : ℚ) * ((h : ℚ) + 1) = ((m : ℚ) + 1) * (m.choose h : ℚ) := by
  have b := Nat.add_one_mul_choose_eq m h
  have := congrArg (fun x : ℕ => (x : ℚ)) b
  push_cast at this; linarith

theorem gosper_partial_sum (m : ℕ) (g q : ℕ → ℚ)
    (hrec : ∀ k, ((m : ℚ) + 1 - k) * q k - k * q (k - 1) = ((m : ℚ) + 1) * g k) :
    ∀ h, (∑ k ∈ range (h + 1), ((m + 1).choose k : ℚ) * g k) = (m.choose h : ℚ) * q h
  | 0 => by
    have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
    have hq : q 0 = g 0 := by
      have h0 := hrec 0
      simp at h0
      rcases h0 with h0 | h0
      · exact h0
      · exact absurd h0 hm
    simp [hq]
  | h + 1 => by
    rw [sum_range_succ, gosper_partial_sum m g q hrec h]
    have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
    have hr := hrec (h + 1)
    simp only [Nat.add_sub_cancel] at hr
    push_cast at hr
    have a := choose_succ_mul_sub m h
    have b := choose_succ_mul_succ m h
    apply mul_left_cancel₀ hm
    linear_combination (-(((m + 1).choose (h + 1) : ℚ))) * hr + q (h + 1) * a - q h * b

/-- **Antisymmetry of `q`.**  If `q` satisfies the Gosper recurrence for every `k` (including `k = n = m+1`, which
encodes `Σ_x C(n,x) g(x) = 0`) and `g` is symmetric, `g k = g (m+1-k)`, then `q h = - q (m - h)` for `h ≤ m`,
i.e. `q(h) = -q(n-1-h)`.  Proof by induction from `h = 0`, using the recurrence at `h+1` and at `m-h`. -/
theorem gosper_antisymm (m : ℕ) (g q : ℕ → ℚ)
    (hrec : ∀ k, ((m : ℚ) + 1 - k) * q k - k * q (k - 1) = ((m : ℚ) + 1) * g k)
    (hsym : ∀ k, k ≤ m + 1 → g k = g (m + 1 - k)) :
    ∀ h, h ≤ m → q h = - q (m - h)
  | 0, _ => by
    have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
    have h0 := hrec 0
    have hlast := hrec (m + 1)
    simp only [Nat.cast_zero, sub_zero, zero_mul, Nat.cast_add, Nat.cast_one, sub_self, Nat.add_sub_cancel]
      at h0 hlast
    have hg := hsym 0 (by omega)
    simp only [Nat.sub_zero] at hg
    have hq0 : q 0 = g 0 := mul_left_cancel₀ hm (by linarith)
    have hqm : q m = - g (m + 1) := mul_left_cancel₀ hm (by linarith)
    simp only [Nat.sub_zero]; rw [hq0, hqm, hg]; ring
  | k + 1, hk => by
    have ih := gosper_antisymm m g q hrec hsym k (by omega)
    have hA := hrec (k + 1)
    have hB := hrec (m - k)
    have hg := hsym (k + 1) (by omega)
    have e1 : m + 1 - (k + 1) = m - k := by omega
    have e2 : m - k - 1 = m - (k + 1) := by omega
    rw [e1] at hg
    simp only [Nat.add_sub_cancel] at hA
    rw [e2] at hB
    have hcast : ((m - k : ℕ) : ℚ) = (m : ℚ) - k := Nat.cast_sub (by omega)
    rw [hcast] at hB
    push_cast at hA
    have hne : ((m : ℚ) - k) ≠ 0 := by
      have : (k : ℚ) < m := by exact_mod_cast (by omega : k < m)
      linarith
    apply mul_left_cancel₀ hne
    rw [hg] at hA
    rw [ih] at hA
    linear_combination hA - hB

/-- **Existence of `q`.**  If `Σ_{k ≤ m+1} C(m+1,k) g(k) = 0`, then `q(h) := (Σ_{k ≤ h} C(m+1,k) g(k)) / C(m,h)` satisfies
the Gosper recurrence `(m+1-k) q(k) - k q(k-1) = (m+1) g(k)` for every `k ≤ m+1` (the case `k = m+1` is exactly the
vanishing total).  (That this `q` is a polynomial of the right degree when `g` is, is the remaining linear-algebra
part.) -/
theorem gosper_exists (m : ℕ) (g : ℕ → ℚ)
    (htot : ∑ k ∈ range (m + 2), ((m + 1).choose k : ℚ) * g k = 0) :
    ∃ q : ℕ → ℚ, ∀ k, k ≤ m + 1 → ((m : ℚ) + 1 - k) * q k - k * q (k - 1) = ((m : ℚ) + 1) * g k := by
  set Sp : ℕ → ℚ := fun h => ∑ k ∈ range (h + 1), ((m + 1).choose k : ℚ) * g k with hSp
  refine ⟨fun h => Sp h / (m.choose h : ℚ), ?_⟩
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp [hSp]
  rcases Nat.lt_or_ge k (m + 1) with hlt | hge
  · -- 1 ≤ k ≤ m
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have a := choose_succ_mul_sub m j        -- C(m+1,j+1)(m-j) = (m+1) C(m,j+1)
    have b := choose_succ_mul_succ m j       -- C(m+1,j+1)(j+1) = (m+1) C(m,j)
    have hc1 : (m.choose (j + 1) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
    have hc0 : (m.choose j : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
    have hC : ((m + 1).choose (j + 1) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
    have hstep : Sp (j + 1) = Sp j + ((m + 1).choose (j + 1) : ℚ) * g (j + 1) := by
      simp only [hSp]; rw [sum_range_succ]
    rw [hstep]
    push_cast
    field_simp
    have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
    -- multiply out using a and b
    have a' : ((m : ℚ) + 1 - (j + 1)) = ((m : ℚ) + 1) * (m.choose (j + 1) : ℚ) / ((m + 1).choose (j + 1) : ℚ) := by
      field_simp; linarith
    have b' : ((j : ℚ) + 1) = ((m : ℚ) + 1) * (m.choose j : ℚ) / ((m + 1).choose (j + 1) : ℚ) := by
      field_simp; linarith
    rw [a', b']
    field_simp
    ring
  · -- k = m + 1: the recurrence is the vanishing total
    have hk' : k = m + 1 := by omega
    subst hk'
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, sub_self, zero_mul, zero_sub]
    have hcm : (m.choose m : ℚ) = 1 := by simp
    have htot' : Sp m + ((m + 1).choose (m + 1) : ℚ) * g (m + 1) = 0 := by
      simp only [hSp]; rw [← sum_range_succ]; exact htot
    rw [hcm, div_one]
    simp at htot'
    have hs : Sp m = - g (m + 1) := by linarith
    rw [hs]; ring

/-! ## Polynomiality of `q` (the linear-algebra half of Lemma ψ, 2026-10-31)

`φ(q)(x) = (n - x) q(x) - x q(x-1)` maps polynomials of degree `< d` into degree `< d+1`, is injective there when
`d ≤ n`, and its image lies in the kernel of `L(g) = Σ_{k ≤ n} C(n,k) g(k)`.  Both spaces have dimension `d`, so every
`g` of degree `≤ d` with `L g = 0` is `φ(q)` for a polynomial `q` of degree `< d`. -/

open Polynomial

noncomputable def phiQ (n : ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] where
  toFun q := (C (n : ℚ) - X) * q - X * q.comp (X - 1)
  map_add' a b := by simp only [add_comp]; ring
  map_smul' c a := by simp only [RingHom.id_apply, smul_eq_C_mul, mul_comp, C_comp]; ring

noncomputable def totL (n : ℕ) : ℚ[X] →ₗ[ℚ] ℚ :=
  ∑ k ∈ range (n + 1), (n.choose k : ℚ) • Polynomial.leval (k : ℚ)

lemma totL_apply (n : ℕ) (g : ℚ[X]) :
    totL n g = ∑ k ∈ range (n + 1), (n.choose k : ℚ) * g.eval (k : ℚ) := by
  simp [totL, LinearMap.sum_apply]

lemma phiQ_eval (n : ℕ) (q : ℚ[X]) (x : ℚ) :
    (phiQ n q).eval x = ((n : ℚ) - x) * q.eval x - x * q.eval (x - 1) := by
  simp [phiQ, eval_comp]

/-- `L ∘ φ = 0`, from the telescoping `gosper_partial_sum`. -/
lemma totL_phiQ (m : ℕ) (q : ℚ[X]) : totL (m + 1) (phiQ (m + 1) q) = 0 := by
  have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
  set E : ℕ → ℚ := fun k => (phiQ (m + 1) q).eval (k : ℚ) with hE
  set g : ℕ → ℚ := fun k => E k / ((m : ℚ) + 1) with hg
  set qq : ℕ → ℚ := fun k => q.eval (k : ℚ) with hqq
  have hrec : ∀ k, ((m : ℚ) + 1 - k) * qq k - k * qq (k - 1) = ((m : ℚ) + 1) * g k := by
    intro k
    have hc : ((m : ℚ) + 1) * g k = E k := by simp only [hg]; field_simp
    rw [hc]; simp only [hE, hqq, phiQ_eval]
    rcases k with _ | j
    · simp
    · push_cast; simp only [add_sub_cancel_right]
  have hs := gosper_partial_sum m g qq hrec (m + 1)
  rw [Nat.choose_eq_zero_of_lt (by omega : m < m + 1)] at hs
  rw [totL_apply]
  have : ∑ k ∈ range (m + 1 + 1), ((m + 1).choose k : ℚ) * (phiQ (m + 1) q).eval (k : ℚ)
      = ((m : ℚ) + 1) * ∑ k ∈ range (m + 1 + 1), ((m + 1).choose k : ℚ) * g k := by
    rw [mul_sum]; refine sum_congr rfl fun k _ => ?_
    simp only [hg, hE]; field_simp
  rw [this, hs]; simp

/-- `φ` is injective on polynomials of degree `< d` when `d ≤ m + 1`. -/
lemma phiQ_inj (m d : ℕ) (hd : d ≤ m + 1) (q : ℚ[X]) (hq : q ∈ degreeLT ℚ d)
    (h0 : phiQ (m + 1) q = 0) : q = 0 := by
  have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
  have hz : ∀ k, k ≤ m → q.eval (k : ℚ) = 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      have e := congrArg (eval 0) h0
      rw [phiQ_eval, eval_zero] at e
      push_cast at e ⊢
      simp only [sub_zero, zero_mul] at e
      exact (mul_eq_zero.mp e).resolve_left hm
    | succ j ih =>
      intro hj
      have e := congrArg (eval ((j + 1 : ℕ) : ℚ)) h0
      rw [phiQ_eval, eval_zero] at e
      push_cast at e ⊢
      rw [add_sub_cancel_right, ih (by omega)] at e
      have hne : ((m : ℚ) + 1 - (j + 1)) ≠ 0 := by
        have : (j : ℚ) < m := by exact_mod_cast (by omega : j < m)
        linarith
      simp only [mul_zero, sub_zero] at e
      exact (mul_eq_zero.mp e).resolve_left hne
  by_contra hne
  have hdeg : q.natDegree < d := (natDegree_lt_iff_degree_lt hne).2 (mem_degreeLT.1 hq)
  apply hne
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero q (f := fun i : Fin (m + 1) => ((i : ℕ) : ℚ))
    (fun a b h => Fin.ext (by exact_mod_cast (show ((a : ℕ) : ℚ) = b from h))) (fun i => hz i (by omega)) ?_
  simp; omega

lemma phiQ_deg (n d : ℕ) (q : ℚ[X]) (hq : q ∈ degreeLT ℚ d) : phiQ n q ∈ degreeLT ℚ (d + 1) := by
  by_cases h : q = 0
  · simp [h]
  have hn : q.natDegree < d := (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hq)
  have a : (C (n : ℚ) - X).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
  have b : (X - 1 : ℚ[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
  have c1 := natDegree_mul_le (p := C (n : ℚ) - X) (q := q)
  have c2 := natDegree_mul_le (p := (X : ℚ[X])) (q := q.comp (X - 1))
  have c3 := natDegree_comp_le (p := q) (q := X - 1)
  have hx : (X : ℚ[X]).natDegree ≤ 1 := natDegree_X_le
  have hle : (phiQ n q).natDegree ≤ d := by
    show ((C (n : ℚ) - X) * q - X * q.comp (X - 1)).natDegree ≤ d
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_) <;> nlinarith
  rw [mem_degreeLT]
  exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hle)

/-- **Lemma ψ, polynomial form.**  If `deg g ≤ d ≤ n = m+1` and `Σ_{k ≤ n} C(n,k) g(k) = 0`, then
`g(x) = (n - x) q(x) - x q(x-1)` for a polynomial `q` of degree `< d`. -/
theorem gosper_poly (m d : ℕ) (hd : d ≤ m + 1) (g : ℚ[X]) (hg : g ∈ degreeLT ℚ (d + 1))
    (htot : totL (m + 1) g = 0) : ∃ q ∈ degreeLT ℚ d, phiQ (m + 1) q = g := by
  let f : degreeLT ℚ d →ₗ[ℚ] degreeLT ℚ (d + 1) :=
    ((phiQ (m + 1)).domRestrict (degreeLT ℚ d)).codRestrict (degreeLT ℚ (d + 1))
      (fun q => phiQ_deg _ _ _ q.2)
  let L' : degreeLT ℚ (d + 1) →ₗ[ℚ] ℚ := (totL (m + 1)).domRestrict (degreeLT ℚ (d + 1))
  have hfin : ∀ k, Module.finrank ℚ (degreeLT ℚ k) = k := fun k => by
    rw [(degreeLTEquiv ℚ k).finrank_eq]; simp
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have h := congrArg Subtype.val hab
    change phiQ (m + 1) a.1 = phiQ (m + 1) b.1 at h
    have h0 : phiQ (m + 1) (a - b) = 0 := by rw [map_sub, h, sub_self]
    exact sub_eq_zero.mp (phiQ_inj m d hd _ (Submodule.sub_mem _ a.2 b.2) h0)
  have hrange : LinearMap.range f ≤ LinearMap.ker L' := by
    rintro _ ⟨q, rfl⟩
    rw [LinearMap.mem_ker]; exact totL_phiQ m q.1
  have h1 : (1 : ℚ[X]) ∈ degreeLT ℚ (d + 1) := by
    rw [mem_degreeLT]; exact degree_one_le.trans_lt (by exact_mod_cast Nat.succ_pos d)
  have hL1 : totL (m + 1) 1 ≠ 0 := by
    rw [totL_apply]; simp only [eval_one, mul_one]
    rw [← Nat.cast_sum, Nat.sum_range_choose]; positivity
  have hsurj : LinearMap.range L' = ⊤ := by
    rw [LinearMap.range_eq_top]; intro c
    refine ⟨(c / totL (m + 1) 1) • ⟨1, h1⟩, ?_⟩
    simp [L', hL1]
  have hker : Module.finrank ℚ (LinearMap.ker L') = d := by
    have := LinearMap.finrank_range_add_finrank_ker L'
    rw [hsurj, finrank_top, Module.finrank_self, hfin (d + 1)] at this; omega
  have hrk : Module.finrank ℚ (LinearMap.range f) = d := by
    rw [LinearMap.finrank_range_of_inj hinj, hfin]
  have heq : LinearMap.range f = LinearMap.ker L' :=
    Submodule.eq_of_le_of_finrank_eq hrange (by rw [hrk, hker])
  have hgk : (⟨g, hg⟩ : degreeLT ℚ (d + 1)) ∈ LinearMap.ker L' := by simpa [L'] using htot
  rw [← heq] at hgk
  obtain ⟨q, hq⟩ := hgk
  exact ⟨q, q.2, congrArg Subtype.val hq⟩

end Bali

#print axioms Bali.gosper_exists
#print axioms Bali.gosper_partial_sum
#print axioms Bali.gosper_antisymm
#print axioms Bali.gosper_poly
