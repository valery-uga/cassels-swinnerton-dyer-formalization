import PfaffianDescent.VoisinFixedCurveFlatIdealBaseChange
import PfaffianDescent.VoisinCartierInverseTwist
import PfaffianDescent.AffineGammaPushforward

/-!
# The inverse Cartier twist of the generic fixed curve

The flat spread of a prime curve has the correct *ideal module* on its generic
fibre, not only the correct set of closed points.  If the generic curve is an
effective Cartier divisor, this module is its literal inverse Cartier twist.
The isomorphism below also identifies the inclusions into the structure
sheaf, so it retains the canonical vanishing section.

This comparison does not assert descent of the generic divisor class to a
line bundle on the original ground-field cubic surface.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- General comparison: when a closed immersion after base change has the
canonical pulled-back ideal-sheaf data, the base-change isomorphism of ideal
modules lands in the actual ideal module of that chosen immersion. -/
noncomputable def closedImmersionGenericIdealModuleIso
    {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i] (j : W ⟶ X)
    (hker : j.ker = i.ker.comap f)
    [IsIso (closedImmersionIdealBaseChangeHom f i)] :
    (Scheme.Modules.pullback f).obj
      (IdealSheafDataModule.closedImmersionModule i) ≅
      IdealSheafDataModule.closedImmersionModule j :=
  asIso (closedImmersionIdealBaseChangeHom f i) ≪≫
    idealModuleTransport
      ((Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i f).trans hker.symm)

/-- On a regular effective Cartier generic curve, the flat model's ideal
module pulls back to the *actual inverse Cartier twist* of the curve. -/
noncomputable def fixedCurve_model_genericInverseCartierTwistIso
    {A F : Type u} [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (e : A) (he : e ≠ 0)
    (φ : Localization.Away e →+* F)
    (hcomp : ∀ a : A, φ (algebraMap A (Localization.Away e) a) =
      algebraMap A F a)
    (p : MvPolynomial (Fin 4) (Localization.Away e))
    (hp : p.IsHomogeneous 3)
    (J : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (Localization.Away e)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hJ : J.toIdeal = Ideal.comap (MvPolynomial.map φ) C.toIdeal)
    (hpJ : p ∈ J.toIdeal) (hflat : Flat (toBase J))
    (H : RegularPrincipalImmersion
      (homogeneousModelToCubic
        (MvPolynomial.map φ p) (hp.map φ) C (by
          change p ∈ Ideal.comap (MvPolynomial.map φ) C.toIdeal
          exact hJ ▸ hpJ))) :
    let cX := projectiveCoefficientMap φ
      (equationIdeal p hp)
      (equationIdeal (MvPolynomial.map φ p) (hp.map φ))
      (equationIdeal_map φ p hp)
    let i := homogeneousModelToCubic p hp J hpJ
    (Scheme.Modules.pullback cX).obj
      (IdealSheafDataModule.closedImmersionModule i) ≅
      H.inverseCartierTwist := by
  let cX := projectiveCoefficientMap φ
    (equationIdeal p hp)
    (equationIdeal (MvPolynomial.map φ p) (hp.map φ))
    (equationIdeal_map φ p hp)
  let i := homogeneousModelToCubic p hp J hpJ
  let hpC : MvPolynomial.map φ p ∈ C.toIdeal := by
    change p ∈ Ideal.comap (MvPolynomial.map φ) C.toIdeal
    exact hJ ▸ hpJ
  let j := homogeneousModelToCubic (MvPolynomial.map φ p) (hp.map φ) C hpC
  have hi : IsClosedImmersion i := homogeneousModelToCubic_closedImmersion p hp J hpJ
  obtain ⟨hiso, hker⟩ :=
    fixedCurve_model_genericIdealSheaf_baseChange
      e he φ hcomp p hp J C hJ hpJ hflat
  letI : IsIso (@closedImmersionIdealBaseChangeHom _ _ _ cX i hi) := hiso
  exact @closedImmersionGenericIdealModuleIso _ _ _ _ cX i hi j hker inferInstance

/-- A denominator-cleared model equation and its original generic equation
have precisely the same zero set at every point over a field extending the
configuration function field. The nonzero denominator cannot introduce a
new generic component. -/
theorem denominator_cleared_equation_evaluation_eq_zero_iff
    {A F L : Type u} [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field L] [Algebra F L] [Algebra A L] [IsScalarTower A F L]
    (q : MvPolynomial (Fin 4) F)
    (d : A) (hd : d ≠ 0) (g : MvPolynomial (Fin 4) A)
    (hclear : MvPolynomial.map (algebraMap A F) g =
      MvPolynomial.C (algebraMap A F d) * q)
    (x : Fin 4 → L) :
    g.eval₂ (algebraMap A L) x = 0 ↔
      q.eval₂ (algebraMap F L) x = 0 := by
  have hdF : algebraMap A F d ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective A F).ne hd
  have hdL : algebraMap A L d ≠ 0 := by
    rw [IsScalarTower.algebraMap_eq A F L]
    change (algebraMap F L) (algebraMap A F d) ≠ 0
    simpa only [map_zero] using (algebraMap F L).injective.ne hdF
  rw [denominator_cleared_equation_evaluation q d g hclear x]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hdL
  · intro h
    rw [h, mul_zero]

end PfaffianDescent
