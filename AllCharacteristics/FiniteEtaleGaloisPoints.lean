import AllCharacteristics.FiniteEtaleGaloisSplitting

/-!
# Geometric points of a split finite étale algebra

An explicit splitting of a finite étale rank-`n` algebra over a field gives
exactly `n` distinct evaluations into the splitting field.  Postcomposition
by a Galois automorphism permutes this enumeration.  These are the algebraic
coordinates used to turn a finite étale subscheme into an unordered
configuration over the ground field.
-/

open scoped TensorProduct

namespace AllCharacteristics

universe u

variable (K A L : Type u) [Field K] [CommRing A] [Algebra K A]
  [Field L] [Algebra K L]

/-- The `i`th geometric evaluation of an algebra split as `Fin n → L`. -/
noncomputable def splitAlgHom
    {n : ℕ} (e : (L ⊗[K] A) ≃ₐ[L] (Fin n → L)) (i : Fin n) :
    A →ₐ[K] L :=
  (Algebra.TensorProduct.liftEquivRight K L A L).symm
    ((Pi.evalAlgHom L (fun _ : Fin n => L) i).comp e.toAlgHom)

/-- Different factors of a split finite algebra give different evaluations
on the original algebra. -/
theorem splitAlgHom_injective
    {n : ℕ} (e : (L ⊗[K] A) ≃ₐ[L] (Fin n → L)) :
    Function.Injective (splitAlgHom K A L e) := by
  intro i j hij
  have hcomp :
      (Pi.evalAlgHom L (fun _ : Fin n => L) i).comp e.toAlgHom =
        (Pi.evalAlgHom L (fun _ : Fin n => L) j).comp e.toAlgHom := by
    exact (Algebra.TensorProduct.liftEquivRight K L A L).symm.injective hij
  have heval : Pi.evalAlgHom L (fun _ : Fin n => L) i =
      Pi.evalAlgHom L (fun _ : Fin n => L) j := by
    apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    exact DFunLike.congr_fun hcomp y
  by_contra hne
  have hvalue := DFunLike.congr_fun heval (fun k => if k = i then (1 : L) else 0)
  simp [Ne.symm hne] at hvalue

/-- For a rank-`n` finite algebra, the split evaluations enumerate all
`K`-algebra maps into the splitting field. -/
noncomputable def splitAlgHomEquiv
    [Module.Finite K A]
    {n : ℕ} (e : (L ⊗[K] A) ≃ₐ[L] (Fin n → L))
    (hn : Module.finrank K A = n) :
    Fin n ≃ (A →ₐ[K] L) :=
  Equiv.ofBijective (splitAlgHom K A L e) <| by
    have hle : Nat.card (A →ₐ[K] L) ≤ Nat.card (Fin n) := by
      simpa [hn] using card_algHom_le_finrank K A L
    exact (splitAlgHom_injective K A L e).bijective_of_nat_card_le hle

/-- Postcomposition by a field automorphism is an equivalence on the set of
algebra maps into that field. -/
noncomputable def algHomPostcompEquiv (g : L ≃ₐ[K] L) :
    (A →ₐ[K] L) ≃ (A →ₐ[K] L) where
  toFun φ := g.toAlgHom.comp φ
  invFun φ := g.symm.toAlgHom.comp φ
  left_inv φ := by
    ext a
    simp
  right_inv φ := by
    ext a
    simp

/-- The permutation of the split factors induced by a field automorphism. -/
noncomputable def splitAlgHomGaloisPerm
    [Module.Finite K A]
    {n : ℕ} (e : (L ⊗[K] A) ≃ₐ[L] (Fin n → L))
    (hn : Module.finrank K A = n) (g : L ≃ₐ[K] L) :
    Equiv.Perm (Fin n) :=
  (splitAlgHomEquiv K A L e hn).trans <|
    (algHomPostcompEquiv K A L g).trans <|
      (splitAlgHomEquiv K A L e hn).symm

/-- The split evaluations transform by the corresponding permutation under
every automorphism of the splitting field. -/
theorem splitAlgHom_galoisPerm
    [Module.Finite K A]
    {n : ℕ} (e : (L ⊗[K] A) ≃ₐ[L] (Fin n → L))
    (hn : Module.finrank K A = n) (g : L ≃ₐ[K] L) (i : Fin n) :
    g.toAlgHom.comp (splitAlgHom K A L e i) =
      splitAlgHom K A L e (splitAlgHomGaloisPerm K A L e hn g i) := by
  change g.toAlgHom.comp ((splitAlgHomEquiv K A L e hn) i) =
    (splitAlgHomEquiv K A L e hn)
      ((splitAlgHomEquiv K A L e hn).symm
        (g.toAlgHom.comp ((splitAlgHomEquiv K A L e hn) i)))
  rw [(splitAlgHomEquiv K A L e hn).apply_symm_apply]

end AllCharacteristics
