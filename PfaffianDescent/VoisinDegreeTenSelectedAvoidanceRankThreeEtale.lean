import PfaffianDescent.FiniteSchemeSmallFieldPoint
import PfaffianDescent.FiniteEtaleSchemeFrobenius
import AllCharacteristics.ProjectivePoints
import AllCharacteristics.CubicPolynomialCoordinates

/-! # The degree-three completion is automatically étale

A finite scheme of rank three mapping to a cubic without a rational point
has a residue field of degree three. Its quotient map is consequently an
isomorphism of vector spaces, so its coordinate algebra is reduced. In
characteristic zero the actual structure morphism is étale.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- An actual field-valued point of degree at most two gives a rational
point of the cubic by secant descent. -/
theorem voisinDegreeTenSelectedAvoidance_section_of_smallFieldPoint
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (i : Spec (.of L) ⟶ hypersurface p hp)
    (hi : i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hL : finrank K L ≤ 2) :
    ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨v, hv, he⟩ := hypersurface_coordinates_of_point
    (algebraMap K L) p hp i hi
  obtain ⟨w, hw, hew⟩ := homogeneous_cubic_degree_le_two_descent p hp hL v hv he
  obtain ⟨s, hs⟩ := hypersurface_point_of_coordinates (RingHom.id K) p hp w hw hew
  refine ⟨s, ?_⟩
  simpa only [CommRingCat.ofHom_id, Spec.map_id] using hs

set_option backward.isDefEq.respectTransparency false in
/-- The actual coefficient algebra of a finite rank-three scheme mapping
to a cubic without a rational point is reduced. No transversality premise
is needed. -/
theorem voisinDegreeTenSelectedAvoidance_rankThree_coefficient_reduced
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    {X : Scheme.{u}} (i : X ⟶ hypersurface p hp)
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hr : (i ≫ hypersurfaceToBase p hp).finrank (IsLocalRing.closedPoint K) = 3) :
    _root_.IsReduced Γ(X, ⊤) := by
  let f := i ≫ hypersurfaceToBase p hp
  letI : IsAffine X := isAffine_of_isAffineHom f
  letI := finiteSchemeCoefficientAlgebra f
  haveI : Module.Finite K Γ(X, ⊤) := finiteSchemeCoefficient_finite f
  have hdim : finrank K Γ(X, ⊤) = 3 :=
    (finiteSchemeCoefficient_finrank f).trans
      ((finiteSchemeRank_eq_finrank f).trans hr)
  haveI : Nontrivial Γ(X, ⊤) :=
    Module.nontrivial_of_finrank_pos (hdim.symm ▸ (by decide : 0 < 3))
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (α := Γ(X, ⊤))
  letI : m.IsMaximal := hm
  let L := Γ(X, ⊤) ⧸ m
  letI : Field L := Ideal.Quotient.field m
  let ev : Γ(X, ⊤) →ₐ[K] L := Ideal.Quotient.mkₐ K m
  have hev : Function.Surjective ev := Ideal.Quotient.mk_surjective
  have hdimL : finrank K L = 3 := by
    have hle : finrank K L ≤ 3 :=
      (LinearMap.finrank_le_finrank_of_surjective (f := ev.toLinearMap) hev).trans_eq hdim
    have hgt : 2 < finrank K L := by
      by_contra h
      apply hno
      exact voisinDegreeTenSelectedAvoidance_section_of_smallFieldPoint p hp
        (finiteSchemeGeometricPoint f ev ≫ i)
        (by simpa only [Category.assoc] using finiteSchemeGeometricPoint_over_base f ev)
        (by omega)
    omega
  have hinj : Function.Injective ev :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := ev.toLinearMap) (hdim.trans hdimL.symm)).mpr hev
  exact isReduced_of_injective ev hinj

/-- In characteristic zero, a finite rank-three scheme on a cubic without
a rational point is étale over the ground field. -/
theorem voisinDegreeTenSelectedAvoidance_rankThree_etale
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    {X : Scheme.{u}} (i : X ⟶ hypersurface p hp)
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hr : (i ≫ hypersurfaceToBase p hp).finrank (IsLocalRing.closedPoint K) = 3) :
    Etale (i ≫ hypersurfaceToBase p hp) := by
  letI : _root_.IsReduced Γ(X, ⊤) :=
    voisinDegreeTenSelectedAvoidance_rankThree_coefficient_reduced p hp hno i hr
  exact finiteScheme_etale_of_reduced (i ≫ hypersurfaceToBase p hp)

end PfaffianDescent
