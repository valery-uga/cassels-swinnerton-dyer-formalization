import PfaffianDescent.NativeAffineHilbertClassification308
import PfaffianDescent.NativePolynomialScalarScheme300

/-! SOURCE ONLY / UNCHECKED. Naturality for arbitrary fixed-R algebra maps.
Every family map is literal polynomial Cartesian base change; every H-map
is native Spec precomposition. No naturality outcome is an input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Bound the H-projection comparison before inserting the native ambient. -/
private lemma nativeScalarAmbientProjectionComparison308
    {C : Type*} [Category C] {P Q T A D H : C}
    (d : Q ⟶ P) (a : P ⟶ T) (b : Q ⟶ T) (out : T ⟶ H)
    (x : P ⟶ A) (y : Q ⟶ D) (f : D ⟶ A) (g : A ⟶ H)
    (ha : a ≫ out = x ≫ g) (hb : b ≫ out = y ≫ (f ≫ g))
    (hd : d ≫ x = y ≫ f) : (d ≫ a) ≫ out = b ≫ out := by
  rw [Category.assoc, ha, ← Category.assoc, hd, Category.assoc, ← hb]

variable (R : Type u) [CommRing R] {A D : Type u} [CommRing A] [CommRing D]
variable [Algebra R A] [Algebra R D] (m n : ℕ)

/-- Literal contravariant family map for an arbitrary fixed-R coefficient map. -/
def nativeAffineHilbertPointScalarMap308 (f : A →ₐ[R] D)
    (P : FiniteFlatHilbertPoint195 (nativePolynomialProjection300 A m) n) :
    FiniteFlatHilbertPoint195 (nativePolynomialProjection300 D m) n := by
  letI : Algebra A D := f.toRingHom.toAlgebra
  exact finiteFlatHilbertBaseChange195
    (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) f.toRingHom)))
    (nativePolynomialProjection300 D m) (nativePolynomialProjection300 A m)
    (Spec.map (CommRingCat.ofHom f.toRingHom))
    (nativePolynomialScalar_isPullback300 A D m) n P

lemma nativeAffineHilbertPointScalarMap_wholeIdeal308 (f : A →ₐ[R] D)
    (P : FiniteFlatHilbertPoint195 (nativePolynomialProjection300 A m) n) :
    (nativeAffineHilbertPointScalarMap308 R m n f P).val =
      P.val.comap (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) f.toRingHom))) := rfl

/-- Native H-point scalar map is exact Spec precomposition over the same R. -/
def monomialFixedBaseHomScalarMap308 (f : A →ₐ[R] D)
    (g : MonomialFixedBaseHom308 R A m n) : MonomialFixedBaseHom308 R D m n :=
  ⟨Spec.map (CommRingCat.ofHom f.toRingHom) ≫ g.val, by
    rw [Category.assoc, g.property]
    exact algebraHomSpecMap_overBase298 f⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Canonical fixed-base ambient maps commute with arbitrary scalar change.
The equality is derived from the two actual pullback projections. -/
lemma fixedBaseTestAmbientMap_natural308 (f : A →ₐ[R] D)
    (g : MonomialFixedBaseHom308 R A m n) :
    Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) f.toRingHom)) ≫
        fixedBaseTestAmbientMap305 R m n g.val g.property =
      fixedBaseTestAmbientMap305 R m n
        (monomialFixedBaseHomScalarMap308 R m n f g).val
        (monomialFixedBaseHomScalarMap308 R m n f g).property := by
  apply pullback.hom_ext
  · exact nativeScalarAmbientProjectionComparison308 (C := Scheme.{u})
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) f.toRingHom)))
      (fixedBaseTestAmbientMap305 R m n g.val g.property)
      (fixedBaseTestAmbientMap305 R m n
        (monomialFixedBaseHomScalarMap308 R m n f g).val
        (monomialFixedBaseHomScalarMap308 R m n f g).property)
      (monomialCoefficientAmbientToH300 R m n)
      (nativePolynomialProjection300 A m) (nativePolynomialProjection300 D m)
      (Spec.map (CommRingCat.ofHom f.toRingHom)) g.val
      (fixedBaseTestAmbientMap_toH305 R m n g.val g.property)
      (fixedBaseTestAmbientMap_toH305 R m n
        (monomialFixedBaseHomScalarMap308 R m n f g).val
        (monomialFixedBaseHomScalarMap308 R m n f g).property)
      (nativePolynomialMap_projection300 m f.toRingHom)
  · change (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) f.toRingHom)) ≫
        fixedBaseTestAmbientMap305 R m n g.val g.property) ≫
          monomialCoefficientAmbientToGroundAffine300 R m n =
      (fixedBaseTestAmbientMap305 R m n
        (monomialFixedBaseHomScalarMap308 R m n f g).val
        (monomialFixedBaseHomScalarMap308 R m n f g).property) ≫
          monomialCoefficientAmbientToGroundAffine300 R m n
    rw [Category.assoc, fixedBaseTestAmbientMap_toGround305,
      fixedBaseTestAmbientMap_toGround305]
    exact nativePolynomialMap_ground300 m f

/-- Actual universal-family pullback is natural, including its whole native ideal. -/
lemma monomialFixedBasePointPullback_natural308 (f : A →ₐ[R] D)
    (g : MonomialFixedBaseHom308 R A m n) :
    nativeAffineHilbertPointScalarMap308 R m n f (monomialFixedBasePointPullback308 R m n g) =
      monomialFixedBasePointPullback308 R m n (monomialFixedBaseHomScalarMap308 R m n f g) := by
  apply Subtype.ext
  change ((monomialCoefficientUniversalWholeIdeal300 R m n).comap
      (fixedBaseTestAmbientMap305 R m n g.val g.property)).comap
        (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) f.toRingHom))) =
    (monomialCoefficientUniversalWholeIdeal300 R m n).comap
      (fixedBaseTestAmbientMap305 R m n
        (monomialFixedBaseHomScalarMap308 R m n f g).val
        (monomialFixedBaseHomScalarMap308 R m n f g).property)
  rw [← Scheme.IdealSheafData.comap_comp, fixedBaseTestAmbientMap_natural308]

/-- The internally chosen classifier commutes with every fixed-R algebra map.
Uniqueness306 removes all dependence on the choices of affine covers and bases. -/
lemma nativeAffineHilbertClassificationEquiv_natural308 (hn : 0 < n) (f : A →ₐ[R] D)
    (P : FiniteFlatHilbertPoint195 (nativePolynomialProjection300 A m) n) :
    (nativeAffineHilbertClassificationEquiv308 R m n hn)
        (nativeAffineHilbertPointScalarMap308 R m n f P) =
      monomialFixedBaseHomScalarMap308 R m n f
        ((nativeAffineHilbertClassificationEquiv308 R m n hn) P) := by
  apply monomialFixedBasePointPullback_injective308 R m n
  calc
    _ = nativeAffineHilbertPointScalarMap308 R m n f P :=
      (nativeAffineHilbertPointClassifyingHom_pullback308 R m n hn
        (nativeAffineHilbertPointScalarMap308 R m n f P)).symm
    _ = nativeAffineHilbertPointScalarMap308 R m n f
        (monomialFixedBasePointPullback308 R m n
          ((nativeAffineHilbertClassificationEquiv308 R m n hn) P)) :=
      congrArg (nativeAffineHilbertPointScalarMap308 R m n f)
        (nativeAffineHilbertPointClassifyingHom_pullback308 R m n hn P)
    _ = _ := monomialFixedBasePointPullback_natural308 R m n f _

end PfaffianDescent
end
