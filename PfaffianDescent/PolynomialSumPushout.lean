import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.MvPolynomial.Rename

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (R : Type u) (I J : Type) [CommRing R]

/-- The polynomial ring on a disjoint union is the pushout of the two polynomial rings over the coefficients. -/
theorem polynomialSum_isPushout :
    IsPushout
      (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial I R))
      (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial J R))
      (CommRingCat.ofHom (MvPolynomial.rename (R := R) (Sum.inl : I → I ⊕ J)).toRingHom)
      (CommRingCat.ofHom (MvPolynomial.rename (R := R) (Sum.inr : J → I ⊕ J)).toRingHom) := by
  let f := CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial I R)
  let g := CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial J R)
  let l := CommRingCat.ofHom (MvPolynomial.rename (R := R) (Sum.inl : I → I ⊕ J)).toRingHom
  let r := CommRingCat.ofHom (MvPolynomial.rename (R := R) (Sum.inr : J → I ⊕ J)).toRingHom
  have w : f ≫ l = g ≫ r := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (MvPolynomial.rename_C Sum.inl x).trans (MvPolynomial.rename_C Sum.inr x).symm
  let d (s : PushoutCocone f g) : CommRingCat.of (MvPolynomial (I ⊕ J) R) ⟶ s.pt :=
    CommRingCat.ofHom (MvPolynomial.eval₂Hom (s.inl.hom.comp MvPolynomial.C)
      (Sum.elim (fun i => s.inl.hom (MvPolynomial.X i)) (fun j => s.inr.hom (MvPolynomial.X j))))
  apply IsPushout.of_isColimit (c := PushoutCocone.mk l r w)
  refine PushoutCocone.IsColimit.mk w d ?_ ?_ ?_
  · intro s
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [d, l, MvPolynomial.rename_C]
    · intro i
      simp [d, l, MvPolynomial.rename_X]
  · intro s
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro x
      have h := congrArg (fun h : CommRingCat.of R ⟶ s.pt => h.hom x) s.condition
      simpa [d, r, f, g] using h
    · intro j
      simp [d, r, MvPolynomial.rename_X]
  · intro s m hl hr
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro x
      have h := congrArg (fun h : CommRingCat.of (MvPolynomial I R) ⟶ s.pt => h.hom (MvPolynomial.C x)) hl
      simpa [d, l] using h
    · intro j
      cases j with
      | inl i =>
        have h := congrArg (fun h : CommRingCat.of (MvPolynomial I R) ⟶ s.pt => h.hom (MvPolynomial.X i)) hl
        simpa [d, l] using h
      | inr j =>
        have h := congrArg (fun h : CommRingCat.of (MvPolynomial J R) ⟶ s.pt => h.hom (MvPolynomial.X j)) hr
        simpa [d, r] using h

end
end PfaffianDescent
