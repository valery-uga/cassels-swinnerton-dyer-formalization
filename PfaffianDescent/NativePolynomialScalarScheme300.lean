import PfaffianDescent.WholeIdealEmbeddedScalarCartesian296

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Literal polynomial affine-space projection; no substitute coordinate model. -/
def nativePolynomialProjection300 (C : Type u) [CommRing C] (m : ℕ) :
    Spec (.of (MvPolynomial (Fin m) C)) ⟶ Spec (.of C) :=
  Spec.map (CommRingCat.ofHom (algebraMap C (MvPolynomial (Fin m) C)))

/-- Literal coefficient-extension map of the original polynomial spectra. -/
def nativePolynomialScalarMap300 (R C : Type u) [CommRing R] [CommRing C] [Algebra R C]
    (m : ℕ) : Spec (.of (MvPolynomial (Fin m) C)) ⟶ Spec (.of (MvPolynomial (Fin m) R)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap R C)))

lemma nativePolynomialScalar_isPullback300
    (R C : Type u) [CommRing R] [CommRing C] [Algebra R C] (m : ℕ) :
    IsPullback (nativePolynomialScalarMap300 R C m) (nativePolynomialProjection300 C m)
      (nativePolynomialProjection300 R m) (Spec.map (CommRingCat.ofHom (algebraMap R C))) :=
  ambientPolynomialScalar_isCartesian296 (C := R) (S := C) (m := m)

/-- Arbitrary original coefficient morphisms preserve the literal affine-space projections. -/
lemma nativePolynomialMap_projection300
    {C D : Type u} [CommRing C] [CommRing D] (m : ℕ) (f : C →+* D) :
    Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) f)) ≫
      nativePolynomialProjection300 C m =
    nativePolynomialProjection300 D m ≫ Spec.map (CommRingCat.ofHom f) := by
  letI : Algebra C D := f.toAlgebra
  exact (nativePolynomialScalar_isPullback300 C D m).w

/-- Actual R-linear coefficient maps preserve the SAME original ground polynomial spectrum. -/
lemma nativePolynomialMap_ground300
    {R C D : Type u} [CommRing R] [CommRing C] [CommRing D] [Algebra R C] [Algebra R D]
    (m : ℕ) (f : C →ₐ[R] D) :
    Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) f.toRingHom)) ≫
      nativePolynomialScalarMap300 R C m = nativePolynomialScalarMap300 R D m := by
  have ha : f.toRingHom.comp (algebraMap R C) = algebraMap R D := by
    apply RingHom.ext
    intro r
    exact f.commutes r
  have hm : (MvPolynomial.map (σ := Fin m) f.toRingHom).comp
      (MvPolynomial.map (σ := Fin m) (algebraMap R C)) =
      MvPolynomial.map (σ := Fin m) (algebraMap R D) := by
    apply RingHom.ext
    intro p
    change MvPolynomial.map f.toRingHom (MvPolynomial.map (algebraMap R C) p) = _
    rw [MvPolynomial.map_map, ha]
  unfold nativePolynomialScalarMap300
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hm]

/-- Exact contravariant Spec composition for canonical algebra coefficient maps. -/
lemma nativeSpecAlgebraComp300
    {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    Spec.map (CommRingCat.ofHom (g.comp f).toRingHom) =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom) := by
  change Spec.map (CommRingCat.ofHom (g.toRingHom.comp f.toRingHom)) = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

end PfaffianDescent
