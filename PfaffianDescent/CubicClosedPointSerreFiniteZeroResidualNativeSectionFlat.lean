import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeSectionRegular

/-! # DVR flatness for the literal rank-two section zero stalk -/
noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u v
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_localSection_stalk_flat_of_surface_fibre
    {X : Scheme.{u}} {E : X.Modules} (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift (Fin 2)) ≅ E.over U)
    (s : E.sections) (z : localSectionZeroSubschemeOfOver U (ULift (Fin 2)) t s)
    (R : Type v) [CommRing R] [IsRegularLocalRing R]
    (hdR : ringKrullDim R = 1) (π : R) (hπ : maximalIdeal R = Ideal.span {π})
    [IsNoetherianRing ((U : Scheme.{u}).presheaf.stalk
      (localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s z))]
    [Algebra R ((U : Scheme.{u}).presheaf.stalk
      (localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s z))]
    [IsLocalHom (algebraMap R ((U : Scheme.{u}).presheaf.stalk
      (localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s z)))]
    [Module.Flat R ((U : Scheme.{u}).presheaf.stalk
      (localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s z))]
    [IsRegularLocalRing (((U : Scheme.{u}).presheaf.stalk
      (localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s z)) ⧸
      Ideal.span {algebraMap R ((U : Scheme.{u}).presheaf.stalk
        (localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s z)) π})]
    (hdA : ringKrullDim (((U : Scheme.{u}).presheaf.stalk
      (localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s z)) ⧸
      Ideal.span {algebraMap R ((U : Scheme.{u}).presheaf.stalk
        (localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s z)) π}) = 2)
    (hArt : let i := localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s
      let A := (U : Scheme.{u}).presheaf.stalk (i z)
      let ab := cubicClosedPointSerreFiniteZeroResidual_localSectionStalkPair U t s (i z)
      IsArtinianRing ((A ⧸ Ideal.span {algebraMap R A π}) ⧸
        Ideal.span ({Ideal.Quotient.mk (Ideal.span {algebraMap R A π}) ab.1,
          Ideal.Quotient.mk (Ideal.span {algebraMap R A π}) ab.2} :
          Set (A ⧸ Ideal.span {algebraMap R A π})))) :
    let i := localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s
    ((i.stalkMap z).hom.comp
      (algebraMap R ((U : Scheme.{u}).presheaf.stalk (i z)))).Flat := by
  let i := localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s
  let A := (U : Scheme.{u}).presheaf.stalk (i z)
  let ab := cubicClosedPointSerreFiniteZeroResidual_localSectionStalkPair U t s (i z)
  have hk := cubicClosedPointSerreFiniteZeroResidual_localSection_stalkMap_kernel U t s z
  have hm : Ideal.span ({ab.1, ab.2} : Set A) ≤ maximalIdeal A := by
    rw [← hk]
    exact le_maximalIdeal (RingHom.ker_ne_top (i.stalkMap z).hom)
  letI := hArt
  letI : Module.Flat R (A ⧸ Ideal.span ({ab.1, ab.2} : Set A)) :=
    cubicClosedPointSerreFiniteZeroResidual_pair_quotient_flat_of_regular_surface_fibre
      R hdR π hπ A hdA ab.1 ab.2 (hm (Ideal.subset_span (by simp)))
        (hm (Ideal.subset_span (by simp)))
  letI : IsClosedImmersion i := isClosedImmersion_localSectionZeroSubschemeOfOverι
    U (ULift (Fin 2)) t s
  apply cubicClosedPointSerreFiniteZeroResidual_flat_comp_of_flat_quotient
    (algebraMap R A) (i.stalkMap z).hom (i.stalkMap_surjective z)
      (Ideal.span ({ab.1, ab.2} : Set A)) hk
  change (algebraMap R (A ⧸ Ideal.span ({ab.1, ab.2} : Set A))).Flat
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

end PfaffianDescent
