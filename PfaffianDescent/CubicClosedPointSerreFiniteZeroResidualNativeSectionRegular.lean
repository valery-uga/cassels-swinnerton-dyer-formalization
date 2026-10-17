import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeSectionStalkQuotient
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualArtinianFibreStalk

/-! # Finite actual section zeros give regular actual surface coordinates -/
noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing RingTheory.Sequence
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_localSection_regular_pair_of_artinian_source
    {X : Scheme.{u}} {E : X.Modules} (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift (Fin 2)) ≅ E.over U)
    (s : E.sections) (z : localSectionZeroSubschemeOfOver U (ULift (Fin 2)) t s)
    [IsRegularLocalRing ((U : Scheme.{u}).presheaf.stalk
      (localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s z))]
    (hd : ringKrullDim ((U : Scheme.{u}).presheaf.stalk
      (localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s z)) = 2)
    [IsArtinianRing ((localSectionZeroSubschemeOfOver U (ULift (Fin 2)) t s).presheaf.stalk z)] :
    let i := localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s
    let ab := cubicClosedPointSerreFiniteZeroResidual_localSectionStalkPair U t s (i z)
    IsRegular ((U : Scheme.{u}).presheaf.stalk (i z)) [ab.1, ab.2] := by
  let i := localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s
  let ab := cubicClosedPointSerreFiniteZeroResidual_localSectionStalkPair U t s (i z)
  let A := (U : Scheme.{u}).presheaf.stalk (i z)
  let e := cubicClosedPointSerreFiniteZeroResidual_localSection_quotientStalkRingEquiv U t s z
  letI : IsArtinianRing (A ⧸ Ideal.span ({ab.1, ab.2} : Set A)) := e.symm.isArtinianRing
  have hk := cubicClosedPointSerreFiniteZeroResidual_localSection_stalkMap_kernel U t s z
  have hm : Ideal.span ({ab.1, ab.2} : Set A) ≤ maximalIdeal A := by
    rw [← hk]
    exact le_maximalIdeal (RingHom.ker_ne_top (i.stalkMap z).hom)
  exact cubicClosedPointSerreFiniteZeroResidual_regular_pair_of_artinian_quotient
    A hd ab.1 ab.2 (hm (Ideal.subset_span (by simp)))
      (hm (Ideal.subset_span (by simp)))

/-- A locally quasi-finite actual zero scheme over a field supplies the
Artinian source stalk used above; regularity is deduced from finite zero
geometry and the actual ambient surface stalk. -/
theorem cubicClosedPointSerreFiniteZeroResidual_localSection_regular_pair_of_quasiFinite
    {X : Scheme.{u}} {E : X.Modules} (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift (Fin 2)) ≅ E.over U)
    (s : E.sections) (z : localSectionZeroSubschemeOfOver U (ULift (Fin 2)) t s)
    (K : Type u) [Field K]
    (f : localSectionZeroSubschemeOfOver U (ULift (Fin 2)) t s ⟶ Spec (.of K))
    [LocallyQuasiFinite f]
    [IsRegularLocalRing ((U : Scheme.{u}).presheaf.stalk
      (localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s z))]
    (hd : ringKrullDim ((U : Scheme.{u}).presheaf.stalk
      (localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s z)) = 2) :
    let i := localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s
    let ab := cubicClosedPointSerreFiniteZeroResidual_localSectionStalkPair U t s (i z)
    IsRegular ((U : Scheme.{u}).presheaf.stalk (i z)) [ab.1, ab.2] := by
  letI : IsLocallyArtinian (localSectionZeroSubschemeOfOver U (ULift (Fin 2)) t s) :=
    IsLocallyArtinian.of_locallyQuasiFinite f
  letI := cubicClosedPointSerreFiniteZeroResidual_isArtinianRing_stalk
    (localSectionZeroSubschemeOfOver U (ULift (Fin 2)) t s) z
  exact cubicClosedPointSerreFiniteZeroResidual_localSection_regular_pair_of_artinian_source
    U t s z hd

end PfaffianDescent
