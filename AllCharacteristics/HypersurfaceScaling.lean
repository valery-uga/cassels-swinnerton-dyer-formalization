import AllCharacteristics.ProjectiveFiberSmoothness

/-!
# Unit scaling of homogeneous equations

Multiplication by an invertible coefficient preserves the homogeneous ideal.
The induced identification of actual projective hypersurfaces respects their
structure maps and preserves smoothness over any commutative coefficient ring.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "𝒜" => MvPolynomial.homogeneousSubmodule σ R

/-- Identifying equal homogeneous ideals respects the projective structure map. -/
theorem eqToHom_scheme_toBase (I J : HomogeneousIdeal 𝒜) (h : I = J) :
    eqToHom (congrArg scheme h) ≫ toBase J = toBase I := by
  subst J
  simp

/-- Scaling a homogeneous equation by an invertible coefficient leaves its
actual homogeneous ideal unchanged. -/
theorem equationIdeal_C_mul_of_isUnit (a : R) (ha : IsUnit a)
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) :
    equationIdeal (MvPolynomial.C a * p) (hp.C_mul a) = equationIdeal p hp := by
  apply HomogeneousIdeal.ext
  exact Ideal.span_singleton_mul_left_unit (ha.map MvPolynomial.C) p

/-- The actual projective hypersurface of a unit multiple is identified with
that of the original equation. -/
noncomputable def hypersurfaceScalingIso (a : R) (ha : IsUnit a)
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) :
    hypersurface (MvPolynomial.C a * p) (hp.C_mul a) ≅ hypersurface p hp :=
  eqToIso (congrArg scheme (equationIdeal_C_mul_of_isUnit a ha p hp))

/-- The identification from unit scaling is over the original coefficient base. -/
theorem hypersurfaceScalingIso_hom_toBase (a : R) (ha : IsUnit a)
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) :
    (hypersurfaceScalingIso a ha p hp).hom ≫ hypersurfaceToBase p hp =
      hypersurfaceToBase (MvPolynomial.C a * p) (hp.C_mul a) :=
  eqToHom_scheme_toBase _ _ (equationIdeal_C_mul_of_isUnit a ha p hp)

/-- Smoothness of a projective hypersurface is invariant under unit scaling
of its homogeneous equation, without a characteristic hypothesis. -/
theorem smooth_hypersurfaceToBase_C_mul_iff (a : R) (ha : IsUnit a)
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) :
    Smooth (hypersurfaceToBase (MvPolynomial.C a * p) (hp.C_mul a)) ↔
      Smooth (hypersurfaceToBase p hp) := by
  change Smooth (toBase (equationIdeal (MvPolynomial.C a * p) (hp.C_mul a))) ↔
    Smooth (toBase (equationIdeal p hp))
  rw [equationIdeal_C_mul_of_isUnit a ha p hp]

end HomogeneousProjective
end AllCharacteristics
