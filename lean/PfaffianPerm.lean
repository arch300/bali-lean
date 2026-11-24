import Mathlib

/-!
# Pfaffian via permutations, and `Pf (B A Bᵀ) = det B · Pf A` (Bali lab, 2026-11-01)

Index set `Fin n × Fin 2`: the pairs are `(i,0),(i,1)`.
`pfP A = Σ_σ sign σ ∏_i A (σ (i,0)) (σ (i,1))` (the usual Pfaffian times `2^n n!`; the constant is irrelevant for
`pfP (B A Bᵀ) = det B · pfP A`).  The proof follows Mathlib's `det_mul`: expand, drop non-injective index maps
(their determinant has two equal columns), and reindex the injective ones by permutations.
-/

open Finset Equiv Matrix

namespace Bali.PfP

variable {R : Type*} [CommRing R] {n : ℕ}

def pfP (A : Matrix (Fin n × Fin 2) (Fin n × Fin 2) R) : R :=
  ∑ σ : Perm (Fin n × Fin 2), (Perm.sign σ : R) * ∏ i : Fin n, A (σ (i, 0)) (σ (i, 1))

/-- `Σ_k Σ_l g k l = Σ_{p : Fin 2 → X} g (p 0) (p 1)`. -/
lemma sum_two {X : Type*} [Fintype X] (g : X → X → R) :
    ∑ k, ∑ l, g k l = ∑ p : Fin 2 → X, g (p 0) (p 1) := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_equiv (piFinTwoEquiv fun _ => X).symm]
  intro x; rfl

lemma entry (A B : Matrix (Fin n × Fin 2) (Fin n × Fin 2) R) (a b : Fin n × Fin 2) :
    (B * A * Bᵀ) a b = ∑ k, ∑ l, B a k * B b l * A k l := by
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

lemma expand (Af Bf : Fin n × Fin 2 → Fin n × Fin 2 → R) (σ : Perm (Fin n × Fin 2)) :
    ∏ i : Fin n, ∑ k, ∑ l, Bf (σ (i, 0)) k * Bf (σ (i, 1)) l * Af k l
      = ∑ F : Fin n × Fin 2 → Fin n × Fin 2, (∏ j, Bf (σ j) (F j)) * ∏ i : Fin n, Af (F (i, 0)) (F (i, 1)) := by
  classical
  simp_rw [sum_two (fun k l => Bf (σ (_, 0)) k * Bf (σ (_, 1)) l * Af k l)]
  rw [prod_univ_sum, Fintype.piFinset_univ]
  rw [← Fintype.sum_equiv (Equiv.curry (Fin n) (Fin 2) (Fin n × Fin 2))]
  · intro F
    rw [Fintype.prod_prod_type, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    simp [Fin.prod_univ_two, Equiv.curry]

theorem pfP_congr (A B : Matrix (Fin n × Fin 2) (Fin n × Fin 2) R) :
    pfP (B * A * Bᵀ) = det B * pfP A := by
  classical
  unfold pfP
  simp_rw [entry A B, expand (fun k l => A k l) (fun a k => B a k), mul_sum]
  rw [sum_comm]
  -- Σ_F Σ_σ sign σ * ((∏ B) * ∏ A)  =  Σ_F (∏ A_F) * det (B.submatrix id F)
  have hF : ∀ F : Fin n × Fin 2 → Fin n × Fin 2,
      ∑ σ : Perm (Fin n × Fin 2), (Perm.sign σ : R) * ((∏ j, B (σ j) (F j)) * ∏ i : Fin n, A (F (i, 0)) (F (i, 1)))
        = (∏ i : Fin n, A (F (i, 0)) (F (i, 1))) * det (B.submatrix id F) := by
    intro F
    rw [det_apply', mul_sum]
    refine sum_congr rfl fun σ _ => ?_
    simp only [submatrix_apply, id]
    ring
  simp_rw [hF]
  -- drop the non-injective F
  rw [← sum_subset (filter_subset (fun F : Fin n × Fin 2 → Fin n × Fin 2 => Function.Bijective F) univ)]
  · -- reindex bijective F by permutations
    refine sum_bij (fun F h => Equiv.ofBijective F (mem_filter.1 h).2) (fun _ _ => mem_univ _)
      (fun F₁ h₁ F₂ h₂ e => ?_) (fun τ _ => ⟨τ, mem_filter.2 ⟨mem_univ _, τ.bijective⟩, Equiv.ext fun _ => rfl⟩) (fun F h => ?_)
    · have := congrArg (fun e : Perm (Fin n × Fin 2) => (e : Fin n × Fin 2 → Fin n × Fin 2)) e
      simpa using this
    · simp only [coe_ofBijective]
      rw [show B.submatrix id F = B.submatrix id (Equiv.ofBijective F (mem_filter.1 h).2) from rfl,
        det_permute']
      ring
  · intro F _ hF
    have hnot : ¬ Function.Injective F := fun hi =>
      hF (mem_filter.2 ⟨mem_univ _, hi.bijective_of_finite⟩)
    obtain ⟨a, b, hab, hne⟩ : ∃ a b, F a = F b ∧ a ≠ b := by
      by_contra h; push Not at h; exact hnot fun a b e => h a b e
    rw [det_zero_of_column_eq hne (fun i => by simp [hab]), mul_zero]

/-! ## Part (a): rectangular `M` (rows `Fin m × Fin 2`, columns `κ`) -/

lemma entry_rect {κ : Type*} [Fintype κ] {m : ℕ} (M : Matrix (Fin m × Fin 2) κ R) (J : Matrix κ κ R)
    (a b : Fin m × Fin 2) : (M * J * Mᵀ) a b = ∑ k, ∑ l, M a k * M b l * J k l := by
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

lemma expand_rect {κ : Type*} [Fintype κ] [DecidableEq κ] {m : ℕ} (Jf : κ → κ → R) (Mf : Fin m × Fin 2 → κ → R)
    (σ : Perm (Fin m × Fin 2)) :
    ∏ i : Fin m, ∑ k, ∑ l, Mf (σ (i, 0)) k * Mf (σ (i, 1)) l * Jf k l
      = ∑ F : Fin m × Fin 2 → κ, (∏ j, Mf (σ j) (F j)) * ∏ i : Fin m, Jf (F (i, 0)) (F (i, 1)) := by
  classical
  simp_rw [sum_two (fun k l => Mf (σ (_, 0)) k * Mf (σ (_, 1)) l * Jf k l)]
  rw [prod_univ_sum, Fintype.piFinset_univ]
  rw [← Fintype.sum_equiv (Equiv.curry (Fin m) (Fin 2) κ)]
  · intro F
    rw [Fintype.prod_prod_type, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    simp [Fin.prod_univ_two, Equiv.curry]

/-- **Pfaffian Cauchy–Binet, first half.**  `pfP (M J Mᵀ) = Σ_{F injective} (∏ J-pairs) · det (M with columns F)`. -/
theorem pfP_rect {κ : Type*} [Fintype κ] [DecidableEq κ] {m : ℕ} (M : Matrix (Fin m × Fin 2) κ R) (J : Matrix κ κ R) :
    pfP (M * J * Mᵀ) = ∑ F ∈ univ.filter (fun F : Fin m × Fin 2 → κ => Function.Injective F),
      (∏ i : Fin m, J (F (i, 0)) (F (i, 1))) * det (M.submatrix id F) := by
  classical
  unfold pfP
  simp_rw [entry_rect M J, expand_rect (fun k l => J k l) (fun a k => M a k), mul_sum]
  rw [sum_comm]
  have hF : ∀ F : Fin m × Fin 2 → κ,
      ∑ σ : Perm (Fin m × Fin 2), (Perm.sign σ : R) * ((∏ j, M (σ j) (F j)) * ∏ i : Fin m, J (F (i, 0)) (F (i, 1)))
        = (∏ i : Fin m, J (F (i, 0)) (F (i, 1))) * det (M.submatrix id F) := by
    intro F
    rw [det_apply', mul_sum]
    refine sum_congr rfl fun σ _ => ?_
    simp only [submatrix_apply, id]
    ring
  simp_rw [hF]
  symm
  apply sum_subset (filter_subset _ _)
  intro F _ hF
  have hnot : ¬ Function.Injective F := fun hi => hF (mem_filter.2 ⟨mem_univ _, hi⟩)
  obtain ⟨a, b, hab, hne⟩ : ∃ a b, F a = F b ∧ a ≠ b := by
    by_contra h; push Not at h; exact hnot fun a b e => h a b e
  rw [det_zero_of_column_eq hne (fun i => by simp [hab]), mul_zero]

/-! ## Part (b'): group injective maps by their image -/

/-- the fixed order on the index set: `(i,b) ↦ 2i+b`. -/
def eι (m : ℕ) : Fin m × Fin 2 ≃ Fin (2 * m) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))

lemma eι_val (m : ℕ) (a : Fin m × Fin 2) : ((eι m a : Fin (2 * m)) : ℕ) = 2 * a.1 + a.2 := by
  simp [eι, finProdFinEquiv]; ring

/-- increasing enumeration of a `2m`-subset of `Fin N`, as a map from the index set. -/
noncomputable def GS {N m : ℕ} (S : Finset (Fin N)) (h : S.card = 2 * m) : Fin m × Fin 2 → Fin N :=
  fun a => S.orderEmbOfFin h (eι m a)

lemma GS_injective {N m : ℕ} (S : Finset (Fin N)) (h : S.card = 2 * m) : Function.Injective (GS S h) :=
  fun a b e => (eι m).injective ((S.orderEmbOfFin h).injective e)

lemma GS_mem {N m : ℕ} (S : Finset (Fin N)) (h : S.card = 2 * m) (a : Fin m × Fin 2) : GS S h a ∈ S :=
  S.orderEmbOfFin_mem h _

/-- total version of `GS` (junk value off the `2m`-subsets). -/
noncomputable def G' {N m : ℕ} (S : Finset (Fin (N + 1))) : Fin m × Fin 2 → Fin (N + 1) :=
  if h : S.card = 2 * m then GS S h else fun _ => 0

lemma card_ι (m : ℕ) : Fintype.card (Fin m × Fin 2) = 2 * m := by simp [Nat.mul_comm]

lemma image_GS_comp {N m : ℕ} (S : Finset (Fin (N + 1))) (h : S.card = 2 * m) (π : Perm (Fin m × Fin 2)) :
    univ.image (G' (m := m) S ∘ π) = S := by
  classical
  have hG : G' (m := m) S = GS S h := by simp [G', h]
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨a, _, rfl⟩ := mem_image.1 hx
    rw [hG]; exact GS_mem S h _
  · rw [card_image_of_injective _ ((hG ▸ GS_injective S h).comp π.injective), card_univ, card_ι, h]

/-- **Grouping.**  A sum over injective index maps is a sum over `2m`-subsets and permutations. -/
theorem sum_injective_group {N m : ℕ} (f : (Fin m × Fin 2 → Fin (N + 1)) → R) :
    ∑ F ∈ univ.filter (fun F : Fin m × Fin 2 → Fin (N + 1) => Function.Injective F), f F
      = ∑ S ∈ univ.powersetCard (2 * m), ∑ π : Perm (Fin m × Fin 2), f (G' S ∘ π) := by
  classical
  rw [sum_sigma']
  symm
  refine sum_bij (fun p _ => G' p.1 ∘ p.2) ?_ ?_ ?_ ?_
  · rintro ⟨S, π⟩ hp
    simp only [mem_sigma, mem_powersetCard, subset_univ, true_and] at hp
    have hG : G' (m := m) S = GS S hp.1 := by simp [G', hp.1]
    simp only [mem_filter, mem_univ, true_and]
    rw [hG]; exact (GS_injective S hp.1).comp π.injective
  · rintro ⟨S₁, π₁⟩ h₁ ⟨S₂, π₂⟩ h₂ e
    simp only [mem_sigma, mem_powersetCard, subset_univ, true_and] at h₁ h₂
    have hS : S₁ = S₂ := by
      rw [← image_GS_comp S₁ h₁.1 π₁, ← image_GS_comp S₂ h₂.1 π₂]; simp only at e; rw [e]
    subst hS
    have hG : G' (m := m) S₁ = GS S₁ h₁.1 := by simp [G', h₁.1]
    simp only at e
    have : π₁ = π₂ := by
      ext a : 1
      apply GS_injective S₁ h₁.1
      have := congrFun e a
      simpa [hG] using this
    subst this; rfl
  · intro F hF
    simp only [mem_filter, mem_univ, true_and] at hF
    set S := univ.image F with hSdef
    have hcard : S.card = 2 * m := by rw [card_image_of_injective _ hF, card_univ, card_ι]
    have hG : G' (m := m) S = GS S hcard := by simp [G', hcard]
    -- both F and GS S are bijections ι → S
    have hFmem : ∀ a, F a ∈ S := fun a => mem_image_of_mem F (mem_univ a)
    let eF : (Fin m × Fin 2) ≃ S := Equiv.ofBijective (fun a => ⟨F a, hFmem a⟩)
      ⟨fun a b e => hF (congrArg Subtype.val e), fun ⟨x, hx⟩ => by
        obtain ⟨a, _, rfl⟩ := mem_image.1 hx; exact ⟨a, rfl⟩⟩
    have hGinj := GS_injective S hcard
    let eG : (Fin m × Fin 2) ≃ S := Equiv.ofBijective (fun a => ⟨GS S hcard a, GS_mem S hcard a⟩)
      ((Fintype.bijective_iff_injective_and_card _).2
        ⟨fun a b e => hGinj (congrArg Subtype.val e), by simp only [Fintype.card_coe, hcard, card_ι]⟩)
    refine ⟨⟨S, eF.trans eG.symm⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_powersetCard, subset_univ, true_and, mem_univ, and_true]; exact hcard
    · funext a
      simp only [Function.comp, hG, Equiv.trans_apply]
      exact congrArg Subtype.val (eG.apply_symm_apply (eF a))
  · intro p _; rfl

/-- **Pfaffian Cauchy–Binet (minor summation).**
`pfP (M J Mᵀ) = Σ_{|S| = 2m} det (M restricted to columns S) · pfP (J restricted to S)`. -/
theorem pfP_cauchy_binet {N m : ℕ} (M : Matrix (Fin m × Fin 2) (Fin (N + 1)) R) (J : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    pfP (M * J * Mᵀ) = ∑ S ∈ univ.powersetCard (2 * m),
      det (M.submatrix id (G' (m := m) S)) * pfP (J.submatrix (G' (m := m) S) (G' (m := m) S)) := by
  classical
  rw [pfP_rect, sum_injective_group (fun F => (∏ i : Fin m, J (F (i, 0)) (F (i, 1))) * det (M.submatrix id F))]
  refine sum_congr rfl fun S _ => ?_
  unfold pfP
  rw [mul_sum]
  refine sum_congr rfl fun π _ => ?_
  have hd : det (M.submatrix id (G' S ∘ π)) = (Perm.sign π : R) * det (M.submatrix id (G' S)) := by
    rw [show M.submatrix id (G' S ∘ π) = (M.submatrix id (G' S)).submatrix id π from rfl, det_permute']
  rw [hd]
  simp only [Function.comp, submatrix_apply]
  ring

/-! ## Part (c): the sign matrix -/

/-- the sign matrix on `Fin (N+1)`. -/
def signM (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  fun k l => if k < l then 1 else if l < k then -1 else 0

/-- the sign matrix on the index set, in the order `eι`. -/
def J0 (m : ℕ) : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R :=
  fun a b => if eι m a < eι m b then 1 else if eι m b < eι m a then -1 else 0

lemma signM_restrict {N m : ℕ} (S : Finset (Fin (N + 1))) (h : S.card = 2 * m) :
    (signM N : Matrix _ _ R).submatrix (G' (m := m) S) (G' (m := m) S) = J0 m := by
  have hG : G' (m := m) S = GS S h := by simp [G', h]
  ext a b
  simp only [submatrix_apply, signM, J0, hG, GS]
  simp only [(S.orderEmbOfFin h).lt_iff_lt]

/-- **Discrete de Bruijn, Pfaffian form.**  With the sign matrix,
`pfP (M J Mᵀ) = pfP J0 · Σ_{|S|=2m} det (M_S)`: the constant `pfP J0` does not depend on `M`. -/
theorem pfP_deBruijn {N m : ℕ} (M : Matrix (Fin m × Fin 2) (Fin (N + 1)) R) :
    pfP (M * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) R) * Mᵀ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R)
      = pfP (J0 m : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R) *
      ∑ S ∈ univ.powersetCard (2 * m), det (M.submatrix id (G' (m := m) S)) := by
  rw [pfP_cauchy_binet, mul_sum]
  refine sum_congr rfl fun S hS => ?_
  have h : S.card = 2 * m := (mem_powersetCard.1 hS).2
  rw [signM_restrict S h]
  ring

/-! ## The pairing matrix `Ω` and `pfP Ω ≠ 0` -/

/-- the basic pairing matrix: `Ω((i,0),(i,1)) = 1`, `Ω((i,1),(i,0)) = -1`, all else `0`. -/
def Om (m : ℕ) : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R :=
  fun a b => if a.1 = b.1 then (if a.2 = 0 ∧ b.2 = 1 then 1 else if a.2 = 1 ∧ b.2 = 0 then -1 else 0) else 0

lemma fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by fin_cases x <;> simp

lemma sign_addRight_fin2 (c : Fin 2) :
    ((Perm.sign (Equiv.addRight c : Perm (Fin 2)) : ℤ) : R) = if c = 0 then 1 else -1 := by
  rcases fin2_cases c with rfl | rfl
  · have : (Equiv.addRight (0 : Fin 2) : Perm (Fin 2)) = 1 := by ext x; simp
    simp [this]
  · have : Perm.sign (Equiv.addRight (1 : Fin 2) : Perm (Fin 2)) = -1 := by decide
    simp [this]

/-- every term of `pfP Ω` is `0` or `1`. -/
lemma term_Om (σ : Perm (Fin m × Fin 2)) :
    (Perm.sign σ : R) * ∏ i : Fin m, (Om m : Matrix _ _ R) (σ (i, 0)) (σ (i, 1)) = 0 ∨
    (Perm.sign σ : R) * ∏ i : Fin m, (Om m : Matrix _ _ R) (σ (i, 0)) (σ (i, 1)) = 1 := by
  classical
  by_cases hgood : ∀ i, (σ (i, 0)).1 = (σ (i, 1)).1
  · right
    -- second coordinates differ
    have hdiff : ∀ i, (σ (i, 1)).2 ≠ (σ (i, 0)).2 := by
      intro i e
      have : σ (i, 0) = σ (i, 1) := Prod.ext (hgood i) e.symm
      exact absurd (σ.injective this) (by simp)
    set f : Fin m → Fin 2 := fun i => (σ (i, 0)).2 with hf
    have h1 : ∀ i, (σ (i, 1)).2 = 1 + f i := by
      intro i
      have := hdiff i
      rcases fin2_cases (σ (i, 0)).2 with h | h <;> rcases fin2_cases (σ (i, 1)).2 with h' | h' <;>
        simp_all
    let φ : Perm (Fin m × Fin 2) := Equiv.prodCongrRight fun i => Equiv.addRight (f i)
    let ρ : Perm (Fin m × Fin 2) := σ * φ
    have hρ : ∀ i b, ρ (i, b) = ((σ (i, 0)).1, b) := by
      intro i b
      show σ (i, b + f i) = _
      rcases fin2_cases (f i) with h | h <;> rcases fin2_cases b with rfl | rfl
      · simp only [h, add_zero]; exact Prod.ext rfl (by simpa [hf] using h)
      · simp only [h, add_zero]
        refine Prod.ext (hgood i).symm ?_
        have := h1 i; rw [h] at this; simpa using this
      · simp only [h, zero_add]
        refine Prod.ext (hgood i).symm ?_
        have := h1 i; rw [h] at this; simpa using this
      · simp only [h]
        have : (1 : Fin 2) + 1 = 0 := by decide
        rw [this]; exact Prod.ext rfl (show (σ (i, 0)).2 = 1 from h)
    have hτinj : Function.Injective (fun i => (σ (i, 0)).1) := by
      intro i j e
      have : ρ (i, 0) = ρ (j, 0) := by rw [hρ, hρ]; simp only at e; rw [e]
      exact congrArg Prod.fst (ρ.injective this)
    let τ : Perm (Fin m) := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hτinj)
    have hρτ : ρ = Equiv.prodCongrLeft fun _ => τ := by
      ext ⟨i, b⟩ <;> simp [hρ, τ]
    have hsignρ : Perm.sign ρ = 1 := by
      rw [hρτ, Perm.sign_prodCongrLeft]; simp [Int.units_mul_self]
    have hσ : σ = ρ * φ⁻¹ := by simp [ρ]
    have hsignσ : Perm.sign σ = Perm.sign φ := by
      rw [hσ, Perm.sign_mul, hsignρ, one_mul, Perm.sign_inv]
    have hsignφ : Perm.sign φ = ∏ i, Perm.sign (Equiv.addRight (f i) : Perm (Fin 2)) :=
      Perm.sign_prodCongrRight _
    have hOm : ∀ i, (Om m : Matrix _ _ R) (σ (i, 0)) (σ (i, 1))
        = ((Perm.sign (Equiv.addRight (f i) : Perm (Fin 2)) : ℤ) : R) := by
      intro i
      rw [sign_addRight_fin2]
      simp only [Om, hgood i, ite_true]
      rcases fin2_cases (f i) with h | h
      · have h0 : (σ (i, 0)).2 = 0 := h
        have h1' : (σ (i, 1)).2 = 1 := by rw [h1, h]; rfl
        simp [h0, h1', h]
      · have h0 : (σ (i, 0)).2 = 1 := h
        have h1' : (σ (i, 1)).2 = 0 := by rw [h1, h]; decide
        simp [h0, h1', h]
    rw [Finset.prod_congr rfl fun i _ => hOm i, hsignσ, hsignφ]
    push_cast
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    rcases Int.units_eq_one_or (Perm.sign (Equiv.addRight (f i) : Perm (Fin 2))) with h | h <;> simp [h]
  · left
    push Not at hgood
    obtain ⟨i, hi⟩ := hgood
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Om, hi]), mul_zero]

/-- `pfP Ω` is a positive integer, in particular nonzero in characteristic `0`. -/
theorem pfP_Om_ne_zero [CharZero R] (m : ℕ) : pfP (Om m : Matrix _ _ R) ≠ 0 := by
  classical
  unfold pfP
  have hsum : ∑ σ : Perm (Fin m × Fin 2), (Perm.sign σ : R) * ∏ i : Fin m, (Om m : Matrix _ _ R) (σ (i, 0)) (σ (i, 1))
      = ((univ.filter fun σ : Perm (Fin m × Fin 2) =>
          (Perm.sign σ : R) * ∏ i : Fin m, (Om m : Matrix _ _ R) (σ (i, 0)) (σ (i, 1)) = 1).card : R) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rcases term_Om (R := R) σ with h | h <;> simp [h]
  rw [hsum, Nat.cast_ne_zero]
  apply Finset.card_ne_zero_of_mem (a := 1)
  simp only [mem_filter, mem_univ, true_and, Perm.sign_one, Units.val_one, Int.cast_one, one_mul,
    Perm.coe_one, id]
  refine Finset.prod_eq_one fun i _ => ?_
  simp [Om]

/-! ## `J₀ = L Ω Lᵀ` with `det L = 1`, hence `pfP J₀ = pfP Ω` -/

def Lm (m : ℕ) : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R :=
  fun a c => if c.2 = 0 then (if a.1 = c.1 then 1 else 0)
    else (if (c.1 : ℕ) < a.1 ∨ ((c.1 : ℕ) = a.1 ∧ a.2 = 1) then 1 else 0)

lemma mul_Om_mul (U V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R) (a b : Fin m × Fin 2) :
    (U * (Om m : Matrix _ _ R) * Vᵀ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R) a b = ∑ k : Fin m, (U a (k, 0) * V b (k, 1) - U a (k, 1) * V b (k, 0)) := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Om]
  simp only [Finset.sum_add_distrib, add_mul, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, mul_neg, neg_mul]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_sub_distrib, sub_eq_add_neg]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]; ring

lemma eι_lt (x y : Fin m × Fin 2) :
    eι m x < eι m y ↔ (x.1 : ℕ) < y.1 ∨ ((x.1 : ℕ) = y.1 ∧ x.2 = 0 ∧ y.2 = 1) := by
  obtain ⟨i, s⟩ := x; obtain ⟨j, t⟩ := y
  rw [Fin.lt_def, eι_val, eι_val]
  fin_cases s <;> fin_cases t <;> simp <;> omega

lemma sum_L (a b : Fin m × Fin 2) :
    ∑ k : Fin m, ((Lm m : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R) a (k, 0) * (Lm m : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R) b (k, 1)
      - (Lm m : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R) a (k, 1) * (Lm m : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R) b (k, 0))
    = (Lm m : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R) b (a.1, 1) - (Lm m : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R) a (b.1, 1) := by
  classical
  have h0 : ∀ (x : Fin m × Fin 2) (k : Fin m), (Lm m : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R) x (k, 0) = if x.1 = k then 1 else 0 := by
    intro x k; simp [Lm]
  rw [Finset.sum_sub_distrib]
  simp only [h0, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma J0_eq (m : ℕ) : (J0 m : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R) = (Lm m * Om m * (Lm m)ᵀ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R) := by
  classical
  ext a b
  rw [mul_Om_mul, sum_L]
  simp only [Lm, J0, eι_lt]
  obtain ⟨i, s⟩ := a; obtain ⟨j, t⟩ := b
  have h10 : ((1 : Fin 2) = 0) ↔ False := by decide
  have h01 : ((0 : Fin 2) = 1) ↔ False := by decide
  fin_cases s <;> fin_cases t <;>
    simp only [Fin.isValue, h10, h01, true_and, and_true, false_and, and_false, or_false, false_or,
      Fin.mk_zero, Fin.mk_one, Fin.zero_eta, if_false] <;>
    split_ifs <;> first | (norm_num; done) | (exfalso; omega) | omega

lemma Lm_upper (a c : Fin m × Fin 2) (h : eι m a < eι m c) :
    (Lm m : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R) a c = 0 := by
  rw [eι_lt] at h
  obtain ⟨i, s⟩ := a; obtain ⟨j, t⟩ := c
  have h10 : ((1 : Fin 2) = 0) ↔ False := by decide
  fin_cases s <;> fin_cases t <;> simp only [Lm, Fin.isValue, h10] at h ⊢ <;> split_ifs <;>
    first | rfl | (exfalso; simp_all [Fin.ext_iff] <;> omega)

lemma Lm_diag (a : Fin m × Fin 2) : (Lm m : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R) a a = 1 := by
  obtain ⟨i, s⟩ := a
  fin_cases s <;> simp [Lm]

lemma det_Lm : det (Lm m : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R) = 1 := by
  classical
  rw [← Matrix.det_reindex_self (eι m)]
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun p _ => ?_
    simp [Matrix.reindex_apply, Lm_diag]
  · intro p q hpq
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    apply Lm_upper
    simpa using hpq

/-- **The constant.**  `pfP J₀ = pfP Ω`, so the de Bruijn constant is that of the pairing matrix. -/
theorem pfP_J0 (m : ℕ) : pfP (J0 m : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R) = pfP (Om m : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R) := by
  rw [J0_eq, pfP_congr, det_Lm, one_mul]

/-! ## Step C: Gram matrices with a zero odd–odd block -/

section Block
variable {K : Type*} [Field K] [CharZero K] {m : ℕ}

/-- block matrix `[[Y, A2], [0, I]]` in the pair indexing (`(i,0)` even rows/cols, `(i,1)` odd). -/
def Bblk (Y A2 : Matrix (Fin m) (Fin m) K) : Matrix (Fin m × Fin 2) (Fin m × Fin 2) K :=
  fun a c => if a.2 = 0 then (if c.2 = 0 then Y a.1 c.1 else A2 a.1 c.1)
    else (if c.2 = 0 then 0 else if a.1 = c.1 then 1 else 0)

/-- `Fin m × Fin 2 ≃ Fin m ⊕ Fin m`, `(i,0) ↦ inl i`, `(i,1) ↦ inr i`. -/
def eSum (m : ℕ) : Fin m × Fin 2 ≃ Fin m ⊕ Fin m :=
  (Equiv.prodComm _ _).trans ((Equiv.prodCongr finTwoEquiv (Equiv.refl _)).trans (Equiv.boolProdEquivSum _))

lemma eSum_symm_inl (i : Fin m) : (eSum m).symm (Sum.inl i) = (i, 0) := by
  simp [eSum, Equiv.boolProdEquivSum, finTwoEquiv]

lemma eSum_symm_inr (i : Fin m) : (eSum m).symm (Sum.inr i) = (i, 1) := by
  simp [eSum, Equiv.boolProdEquivSum, finTwoEquiv]

lemma det_Bblk (Y A2 : Matrix (Fin m) (Fin m) K) : det (Bblk Y A2) = det Y := by
  classical
  rw [← Matrix.det_reindex_self (eSum m)]
  have : Matrix.reindex (eSum m) (eSum m) (Bblk Y A2) = Matrix.fromBlocks Y A2 0 1 := by
    ext (i | i) (j | j) <;>
      simp [Matrix.reindex_apply, eSum_symm_inl, eSum_symm_inr, Bblk, Matrix.one_apply]
  rw [this, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem pfP_gram (G : Matrix (Fin m × Fin 2) (Fin m × Fin 2) K) (hskew : Gᵀ = -G)
    (hOO : ∀ i j, G (i, 1) (j, 1) = 0)
    (hY : IsUnit (det (fun i j => G (i, 0) (j, 1) : Matrix (Fin m) (Fin m) K))) :
    pfP G = det (fun i j => G (i, 0) (j, 1) : Matrix (Fin m) (Fin m) K) * pfP (Om m : Matrix _ _ K) := by
  classical
  set Y : Matrix (Fin m) (Fin m) K := fun i j => G (i, 0) (j, 1) with hYdef
  set X : Matrix (Fin m) (Fin m) K := fun i j => G (i, 0) (j, 0) with hXdef
  have hXskew : Xᵀ = -X := by
    ext i j
    have := congrFun (congrFun hskew (i, 0)) (j, 0)
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    show G (j, 0) (i, 0) = -G (i, 0) (j, 0)
    exact this
  set A2 : Matrix (Fin m) (Fin m) K := -(1 / 2 : K) • (X * (Yᵀ)⁻¹) with hA2
  have hYt : IsUnit (det Yᵀ) := by rwa [Matrix.det_transpose]
  have key : Y * A2ᵀ - A2 * Yᵀ = X := by
    have h1 : Y * A2ᵀ = (1 / 2 : K) • X := by
      rw [hA2, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
        Matrix.transpose_transpose, hXskew, Matrix.mul_smul, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hY, Matrix.one_mul]
      ext i j; simp <;> ring
    have h2 : A2 * Yᵀ = -(1 / 2 : K) • X := by
      rw [hA2, Matrix.smul_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hYt, Matrix.mul_one]
    rw [h1, h2]; ext i j; simp <;> ring
  have hG : G = Bblk Y A2 * Om m * (Bblk Y A2)ᵀ := by
    ext ⟨i, s⟩ ⟨j, t⟩
    rw [mul_Om_mul]
    fin_cases s <;> fin_cases t
    · -- even–even
      have := congrFun (congrFun key i) j
      simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply] at this
      simp only [Bblk, Fin.isValue, if_true, show ((1 : Fin 2) = 0) = False from by decide, if_false]
      rw [Finset.sum_sub_distrib]; simpa [hXdef] using this.symm
    · -- even–odd
      simp [Bblk, hYdef, Finset.sum_ite_eq', Finset.sum_ite_eq]
    · -- odd–even
      have := congrFun (congrFun hskew (j, 0)) (i, 1)
      simp [Bblk, hYdef, Finset.sum_ite_eq', Finset.sum_ite_eq] at this ⊢
      linear_combination this
    · -- odd–odd
      simp [Bblk, hOO]
  rw [hG, pfP_congr, det_Bblk]

end Block

section Final
variable {K : Type*} [Field K] [CharZero K] {N m : ℕ}

lemma signM_transpose : (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) K)ᵀ = -signM N := by
  ext k l
  simp only [Matrix.transpose_apply, Matrix.neg_apply, signM]
  rcases lt_trichotomy k l with h | rfl | h
  · simp [h, not_lt_of_gt h]
  · simp
  · simp [h, not_lt_of_gt h]

/-- **de Bruijn + skew-orthogonality, assembled.**  If the Gram matrix `G = M · signM · Mᵀ` has a zero odd–odd
block and an invertible even–odd block `Y`, then the sum of all maximal minors of `M` is `det Y`. -/
theorem sum_minors_eq_det (M : Matrix (Fin m × Fin 2) (Fin (N + 1)) K)
    (hOO : ∀ i j, (M * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) K) * Mᵀ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) K) (i, 1) (j, 1) = 0)
    (hY : IsUnit (det (fun i j => (M * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) K) * Mᵀ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) K) (i, 0) (j, 1)
      : Matrix (Fin m) (Fin m) K))) :
    ∑ S ∈ univ.powersetCard (2 * m), det (M.submatrix id (G' (m := m) S))
      = det (fun i j => (M * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) K) * Mᵀ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) K) (i, 0) (j, 1)
          : Matrix (Fin m) (Fin m) K) := by
  have hskew : (M * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) K) * Mᵀ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) K)ᵀ = -(M * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) K) * Mᵀ) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, signM_transpose]
    simp [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
  have h1 := pfP_deBruijn (R := K) M
  have h2 := pfP_gram _ hskew hOO hY
  rw [pfP_J0] at h1
  rw [h1] at h2
  have hne := pfP_Om_ne_zero (R := K) m
  rw [mul_comm (pfP _)] at h2
  exact mul_right_cancel₀ hne h2

end Final

end Bali.PfP

#print axioms Bali.PfP.pfP_congr
#print axioms Bali.PfP.pfP_rect
#print axioms Bali.PfP.sum_injective_group
#print axioms Bali.PfP.pfP_cauchy_binet
#print axioms Bali.PfP.pfP_deBruijn
#print axioms Bali.PfP.pfP_Om_ne_zero
#print axioms Bali.PfP.pfP_J0
#print axioms Bali.PfP.pfP_gram
#print axioms Bali.PfP.sum_minors_eq_det
