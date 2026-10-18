import PfaffianDescent.ArtinBaseRegularElement318

/-!
A residue regular pair on a base-flat Artin algebra
lifts to an actual regular pair. The first principal quotient's flatness
is constructed before the second regularity theorem is applied.
-/

noncomputable section
namespace AllCharacteristics
open Module LinearMap TensorProduct
universe u v

theorem regularPair_of_nilpotent_residue318
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A]
    (I : Ideal R) [I.IsMaximal] (hI : IsNilpotent I) (a b : A)
    (ha : IsSMulRegular ((R ⧸ I) ⊗[R] A) ((1 : R ⧸ I) ⊗ₜ[R] a))
    (hb : IsSMulRegular
      (((R ⧸ I) ⊗[R] A) ⧸ Ideal.span {((1 : R ⧸ I) ⊗ₜ[R] a)})
      ((1 : R ⧸ I) ⊗ₜ[R] b)) :
    IsSMulRegular A a ∧ IsSMulRegular (A ⧸ Ideal.span {a}) b ∧
      Module.Flat R (A ⧸ Ideal.span {a}) ∧
      Module.Flat R ((A ⧸ Ideal.span {a}) ⧸
        Ideal.span {Ideal.Quotient.mk (Ideal.span {a}) b}) := by
  let k := R ⧸ I
  let B := k ⊗[R] A
  let H := Ideal.span ({a} : Set A)
  let Q := A ⧸ H
  obtain ⟨ha', hflatQ⟩ := regularElement_and_flat_quotient_of_nilpotent_residue318 I hI a ha
  letI : Module.Flat R Q := hflatQ
  let inc : A →ₐ[R] B := Algebra.TensorProduct.includeRight
  have hspan : H.map inc.toRingHom = Ideal.span {((1 : k) ⊗ₜ[R] a)} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  let e₀ := Algebra.TensorProduct.tensorQuotientEquiv (R := R) k A k H
  let e₁ := Ideal.quotientEquivAlgOfEq k hspan
  let e : (k ⊗[R] Q) ≃ₐ[k] B ⧸ Ideal.span {((1 : k) ⊗ₜ[R] a)} := e₀.trans e₁
  have he : e ((1 : k) ⊗ₜ[R] (Ideal.Quotient.mk H b)) =
      Ideal.Quotient.mk (Ideal.span {((1 : k) ⊗ₜ[R] a)}) ((1 : k) ⊗ₜ[R] b) := by
    change e₁ (e₀ ((1 : k) ⊗ₜ[R] (Ideal.Quotient.mk H b))) = _
    rw [Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
    exact Ideal.quotientEquivAlgOfEq_mk _ _ _
  have hbQ : IsSMulRegular (k ⊗[R] Q)
      ((1 : k) ⊗ₜ[R] (Ideal.Quotient.mk H b)) := by
    intro x y hxy
    apply e.injective
    apply hb
    change Ideal.Quotient.mk (Ideal.span {((1 : k) ⊗ₜ[R] a)})
        ((1 : k) ⊗ₜ[R] b) * e x =
      Ideal.Quotient.mk (Ideal.span {((1 : k) ⊗ₜ[R] a)})
        ((1 : k) ⊗ₜ[R] b) * e y
    rw [← he, ← map_mul, ← map_mul]
    exact congrArg e hxy
  obtain ⟨hb', hflatLast⟩ := regularElement_and_flat_quotient_of_nilpotent_residue318
    I hI (Ideal.Quotient.mk H b) hbQ
  have hbActual : IsSMulRegular Q b := by
    change Function.Injective (fun x : Q => Ideal.Quotient.mk H b * x)
    change Function.Injective (fun x : Q => Ideal.Quotient.mk H b * x) at hb'
    exact hb'
  exact ⟨ha', hbActual, hflatQ, hflatLast⟩

end AllCharacteristics
end
