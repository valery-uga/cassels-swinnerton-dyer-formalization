import PfaffianDescent.NativeAmbientPullbackChart300
import PfaffianDescent.NativePolynomialScalarScheme300
import PfaffianDescent.MonomialCoefficientGluedBase300

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Native contravariant Spec map with both coefficient rings already fixed.
This retains the original coefficient hom, avoiding ofHom carrier/dictionary metavariables. -/
private def nativeCoefficientSpecAlgHom300
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    Spec (.of B) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom f.toRingHom)
variable (R : Type u) [CommRing R] (m n : ℕ)
variable (i j : MonomialCoefficientChartIndex300 m n)

/-- Original B-overlap coefficient point: the SAME native localization scalar map. -/
def monomialCoefficientFirstOverlapPoint300 :
    UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex →ₐ[R]
      MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq :=
  Algebra.algHom R (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)
    (MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq)

/-- Original C-overlap point is the native localization followed by SAME293 inverse transition. -/
def monomialCoefficientSecondOverlapPoint300 :
    UniversalCyclicCoefficientAlgebra282 R m n j.monomials j.zeroIndex →ₐ[R]
      MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq :=
  (monomialOverlapForwardCoefficientMap293 R m n j.monomials i.monomials
    j.zeroIndex i.zeroIndex j.zero_eq i.zero_eq).comp
      (Algebra.algHom R (UniversalCyclicCoefficientAlgebra282 R m n j.monomials j.zeroIndex)
        (MonomialOverlapCoefficientAlgebra292 R m n j.monomials i.monomials j.zeroIndex j.zero_eq))

set_option backward.isDefEq.respectTransparency.types false in
def monomialCoefficientOverlapToFirst300 :
    Spec (.of (MonomialOverlapCoefficientAlgebra292 R m n
      i.monomials j.monomials i.zeroIndex i.zero_eq)) ⟶
    Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)) :=
  nativeCoefficientSpecAlgHom300
    (A := UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)
    (B := MonomialOverlapCoefficientAlgebra292 R m n
      i.monomials j.monomials i.zeroIndex i.zero_eq)
    (monomialCoefficientFirstOverlapPoint300 R m n i j)

set_option backward.isDefEq.respectTransparency.types false in
def monomialCoefficientOverlapToSecond300 :
    Spec (.of (MonomialOverlapCoefficientAlgebra292 R m n
      i.monomials j.monomials i.zeroIndex i.zero_eq)) ⟶
    Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n j.monomials j.zeroIndex)) :=
  nativeCoefficientSpecAlgHom300
    (A := UniversalCyclicCoefficientAlgebra282 R m n j.monomials j.zeroIndex)
    (B := MonomialOverlapCoefficientAlgebra292 R m n
      i.monomials j.monomials i.zeroIndex i.zero_eq)
    (monomialCoefficientSecondOverlapPoint300 R m n i j)

lemma monomialCoefficientOverlapToFirst_original300 :
    (monomialOverlapPrincipalOpenIso294 R m n i.monomials j.monomials i.zeroIndex i.zero_eq).hom ≫
      monomialOverlapOriginalOpenInclusion300 R m n i.monomials j.monomials i.zeroIndex i.zero_eq =
    monomialCoefficientOverlapToFirst300 R m n i j := by
  change (monomialOverlapPrincipalOpenIso294 R m n i.monomials j.monomials i.zeroIndex i.zero_eq).hom ≫
    Scheme.Opens.ι (X := Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n
      i.monomials i.zeroIndex))) (PrimeSpectrum.basicOpen
      (universalMonomialOverlapDet292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq)) =
    monomialOverlapPrincipalOpenMap294 R m n i.monomials j.monomials i.zeroIndex i.zero_eq
  exact monomialOverlapPrincipalOpenIso_hom_fac294 R m n
    i.monomials j.monomials i.zeroIndex i.zero_eq

lemma monomialCoefficientOverlapToSecond_original300 :
    (monomialOverlapPrincipalOpenIso294 R m n i.monomials j.monomials i.zeroIndex i.zero_eq).hom ≫
      (monomialOverlapPrincipalSchemeIso298 R m n i.monomials j.monomials
        i.zeroIndex j.zeroIndex i.zero_eq j.zero_eq).hom ≫
      monomialOverlapOriginalOpenInclusion300 R m n j.monomials i.monomials j.zeroIndex j.zero_eq =
    monomialCoefficientOverlapToSecond300 R m n i j := by
  calc
    _ = (monomialOverlapAffineSchemeIso298 R m n i.monomials j.monomials
        i.zeroIndex j.zeroIndex i.zero_eq j.zero_eq).hom ≫
        (monomialOverlapPrincipalOpenIso294 R m n j.monomials i.monomials j.zeroIndex j.zero_eq).hom ≫
        monomialOverlapOriginalOpenInclusion300 R m n j.monomials i.monomials j.zeroIndex j.zero_eq := by
      simpa only [Category.assoc] using congrArg
        (fun a => a ≫ monomialOverlapOriginalOpenInclusion300 R m n
          j.monomials i.monomials j.zeroIndex j.zero_eq)
        (monomialOverlapPrincipalSchemeIso_transport300 R m n i.monomials j.monomials
          i.zeroIndex j.zeroIndex i.zero_eq j.zero_eq)
    _ = (monomialOverlapAffineSchemeIso298 R m n i.monomials j.monomials
        i.zeroIndex j.zeroIndex i.zero_eq j.zero_eq).hom ≫
        monomialOverlapPrincipalOpenMap294 R m n j.monomials i.monomials j.zeroIndex j.zero_eq := by
      exact congrArg
        (fun a => (monomialOverlapAffineSchemeIso298 R m n i.monomials j.monomials
          i.zeroIndex j.zeroIndex i.zero_eq j.zero_eq).hom ≫ a)
        (monomialCoefficientOverlapToFirst_original300 R m n j i)
    _ = _ := by
      unfold monomialCoefficientOverlapToSecond300 monomialCoefficientSecondOverlapPoint300
        nativeCoefficientSpecAlgHom300
      rw [nativeSpecAlgebraComp300, monomialOverlapAffineSchemeIso_hom298]
      rfl

/-- The actual localization presentation is the intersection of the two ORIGINAL H charts. -/
lemma monomialCoefficientOverlap_isPullback300 :
    IsPullback (monomialCoefficientOverlapToFirst300 R m n i j)
      (monomialCoefficientOverlapToSecond300 R m n i j)
      (monomialCoefficientGluedChartMap300 R m n i)
      (monomialCoefficientGluedChartMap300 R m n j) := by
  have h := nativePullbackDomainIso300
    (nativeSchemeGlueData_pairIsPullback300 (monomialCoefficientSchemeGlueData300 R m n) ⟨i⟩ ⟨j⟩)
    (monomialOverlapPrincipalOpenIso294 R m n i.monomials j.monomials i.zeroIndex i.zero_eq)
  change IsPullback
    ((monomialOverlapPrincipalOpenIso294 R m n i.monomials j.monomials i.zeroIndex i.zero_eq).hom ≫
      monomialOverlapOriginalOpenInclusion300 R m n i.monomials j.monomials i.zeroIndex i.zero_eq)
    ((monomialOverlapPrincipalOpenIso294 R m n i.monomials j.monomials i.zeroIndex i.zero_eq).hom ≫
      ((monomialOverlapPrincipalSchemeIso298 R m n i.monomials j.monomials
        i.zeroIndex j.zeroIndex i.zero_eq j.zero_eq).hom ≫
        monomialOverlapOriginalOpenInclusion300 R m n j.monomials i.monomials j.zeroIndex j.zero_eq))
    (monomialCoefficientGluedChartMap300 R m n i) (monomialCoefficientGluedChartMap300 R m n j) at h
  rw [monomialCoefficientOverlapToFirst_original300,
    monomialCoefficientOverlapToSecond_original300] at h
  exact h

end PfaffianDescent
