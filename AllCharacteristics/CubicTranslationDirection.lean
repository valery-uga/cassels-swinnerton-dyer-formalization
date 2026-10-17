import AllCharacteristics.TriplePointDescent

/-!
# Translation directions of a cubic

The multiplicity-three argument in characteristic three uses the polynomial
identity `F(x + s v) = F(x)`, not merely equality of the associated functions
on one field.  The universal formulation below preserves that distinction,
which is essential over finite fields.
-/

open scoped BigOperators
namespace AllCharacteristics

universe u

/-- A vector is a translation direction when the identity `p(x + s v) = p(x)`
continues to hold after every change of coefficient ring.  This is equivalent
to the corresponding polynomial identity with an extra variable. -/
def IsTranslationDirection {K : Type u} [CommRing K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) (v : Fin n → K) : Prop :=
  ∀ {S : Type u} [CommRing S] (f : K →+* S) (x : Fin n → S) (s : S),
    p.eval₂ f (fun i => x i + s * f (v i)) = p.eval₂ f x

theorem isTranslationDirection_zero {K : Type u} [CommRing K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) : IsTranslationDirection p 0 := by
  intro S _ f x s
  congr 1
  funext i
  simp

theorem IsTranslationDirection.add {K : Type u} [CommRing K] {n : ℕ}
    {p : MvPolynomial (Fin n) K} {v w : Fin n → K}
    (hv : IsTranslationDirection p v) (hw : IsTranslationDirection p w) :
    IsTranslationDirection p (v + w) := by
  intro S _ f x s
  calc
    p.eval₂ f (fun i => x i + s * f ((v + w) i)) =
        p.eval₂ f (fun i => (x i + s * f (v i)) + s * f (w i)) := by
          congr 1
          funext i
          simp [mul_add, add_assoc]
    _ = p.eval₂ f (fun i => x i + s * f (v i)) := hw f _ s
    _ = p.eval₂ f x := hv f x s

theorem IsTranslationDirection.neg {K : Type u} [CommRing K] {n : ℕ}
    {p : MvPolynomial (Fin n) K} {v : Fin n → K}
    (hv : IsTranslationDirection p v) : IsTranslationDirection p (-v) := by
  intro S _ f x s
  have h := hv f (fun i => x i + s * f ((-v) i)) s
  symm
  simpa [mul_neg, add_assoc] using h

/-- Translation directions are stable under ground-ring scalar
multiplication. -/
theorem IsTranslationDirection.smul {K : Type u} [CommRing K] {n : ℕ}
    {p : MvPolynomial (Fin n) K} {v : Fin n → K}
    (hv : IsTranslationDirection p v) (a : K) :
    IsTranslationDirection p (a • v) := by
  intro S _ f x s
  have h := hv f x (s * f a)
  convert h using 1
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

/-- Translation directions form an additive subgroup. -/
def translationDirections {K : Type u} [CommRing K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) : AddSubgroup (Fin n → K) where
  carrier := {v | IsTranslationDirection p v}
  zero_mem' := isTranslationDirection_zero p
  add_mem' := IsTranslationDirection.add
  neg_mem' := IsTranslationDirection.neg

@[simp] theorem mem_translationDirections {K : Type u} [CommRing K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) (v : Fin n → K) :
    v ∈ translationDirections p ↔ IsTranslationDirection p v := Iff.rfl

/-- A ground-field embedding carries a translation direction to its
conjugate translation direction. -/
theorem IsTranslationDirection.map_algHom
    {k L E : Type u} [Field k] [Field L] [Field E]
    [Algebra k L] [Algebra k E] {n : ℕ}
    (p : MvPolynomial (Fin n) k) (v : Fin n → L)
    (hv : IsTranslationDirection (p.map (algebraMap k L)) v)
    (σ : L →ₐ[k] E) :
    IsTranslationDirection (p.map (algebraMap k E)) (fun i => σ (v i)) := by
  intro S _ f x s
  have h := hv (f.comp σ.toRingHom) x s
  simp only [MvPolynomial.eval₂_map] at h ⊢
  have hcomp : (f.comp σ.toRingHom).comp (algebraMap k L) =
      f.comp (algebraMap k E) := by
    ext a
    simp only [RingHom.comp_apply]
    exact congrArg f (σ.commutes a)
  rw [hcomp] at h
  exact h

/-- In characteristic three, the trace of a normalized translation direction
over an extension of degree prime to three is a nonzero ground-field zero of
the cubic.  This completes the arithmetic part of the paper's multiplicity-
three argument. -/
theorem exists_ground_cubic_point_of_translation_char_three
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [CharP k 3] {n : ℕ}
    (p : MvPolynomial (Fin n) k) (hp : p.IsHomogeneous 3)
    (hdegree : Nat.Coprime (Module.finrank k L) 3)
    (v : Fin n → L) (i : Fin n) (hi : v i = 1)
    (htrans : IsTranslationDirection (p.map (algebraMap k L)) v) :
    ∃ y : Fin n → k, y ≠ 0 ∧ p.eval y = 0 := by
  let _ : Algebra.IsSeparable k L := isSeparable_of_finrank_coprime_three hdegree
  let E := AlgebraicClosure k
  let W : AddSubgroup (Fin n → E) :=
    translationDirections (p.map (algebraMap k E))
  have hconj : ∀ σ : L →ₐ[k] E, (fun j => σ (v j)) ∈ W := by
    intro σ
    exact IsTranslationDirection.map_algHom p v htrans σ
  have htraceE :
      (fun j => algebraMap k E (traceVector (k := k) v j)) ∈ W :=
    traceVector_mem_of_embeddings_mem W v hconj
  let y : Fin n → k := traceVector (k := k) v
  have hy : y ≠ 0 := traceVector_ne_zero_of_coordinate_eq_one hdegree v i hi
  refine ⟨y, hy, ?_⟩
  change IsTranslationDirection (p.map (algebraMap k E))
    (fun j => algebraMap k E (y j)) at htraceE
  have ht := htraceE (RingHom.id E) (0 : Fin n → E) 1
  have hpconst : MvPolynomial.constantCoeff p = 0 :=
    hp.coeff_eq_zero (by simp)
  have ht' : (p.map (algebraMap k E)).eval
      (fun j => algebraMap k E (y j)) = 0 := by
    simpa [MvPolynomial.eval₂_id, hpconst] using ht
  apply (FaithfulSMul.algebraMap_injective k E)
  rw [MvPolynomial.map_eval]
  rw [map_zero]
  change (p.map (algebraMap k E)).eval
    (fun j => algebraMap k E (y j)) = 0
  exact ht'

end AllCharacteristics
