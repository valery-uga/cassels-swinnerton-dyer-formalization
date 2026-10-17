import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeLocalFlat
import PfaffianDescent.VoisinSheafStalk

/-! # Literal coordinate quotient for an actual rank-two section zero stalk -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

def cubicClosedPointSerreFiniteZeroResidual_localSectionStalkPair
    {X : Scheme.{u}} {E : X.Modules} (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift (Fin 2)) ≅ E.over U)
    (s : E.sections) (x : (U : Scheme.{u})) :
    (U : Scheme.{u}).presheaf.stalk x × (U : Scheme.{u}).presheaf.stalk x :=
  (((U : Scheme.{u}).presheaf.germ ⊤ x trivial)
    (sectionCoordinateOfFreeIso (ULift (Fin 2))
      (localFreeIsoOfOver U (ULift (Fin 2)) t)
      (restrictSectionToOpen U s) (ULift.up 0)),
   ((U : Scheme.{u}).presheaf.germ ⊤ x trivial)
    (sectionCoordinateOfFreeIso (ULift (Fin 2))
      (localFreeIsoOfOver U (ULift (Fin 2)) t)
      (restrictSectionToOpen U s) (ULift.up 1)))

theorem cubicClosedPointSerreFiniteZeroResidual_localSection_stalkMap_kernel
    {X : Scheme.{u}} {E : X.Modules} (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift (Fin 2)) ≅ E.over U)
    (s : E.sections) (z : localSectionZeroSubschemeOfOver U (ULift (Fin 2)) t s) :
    let i := localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s
    let ab := cubicClosedPointSerreFiniteZeroResidual_localSectionStalkPair U t s (i z)
    RingHom.ker (i.stalkMap z).hom = Ideal.span ({ab.1, ab.2} :
      Set ((U : Scheme.{u}).presheaf.stalk (i z))) := by
  let i := localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s
  letI : IsClosedImmersion i := isClosedImmersion_localSectionZeroSubschemeOfOverι
    U (ULift (Fin 2)) t s
  let M : (U : Scheme.{u}).Modules := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit (localSectionZeroSubschemeOfOver U (ULift (Fin 2)) t s).ringCatSheaf)
  letI : Module ((U : Scheme.{u}).presheaf.stalk (i z)) (M.presheaf.stalk (i z)) :=
    schemeModuleStalkModule M (i z)
  have h := localSectionZeroSubschemeOfOver_stalk_ker_eq_span_pair U t s (i z)
  dsimp only at h ⊢
  ext r
  change i.stalkMap z r = 0 ↔ _
  rw [← closedImmersionPushforwardStalkFromRingLinearMap_eq_zero_iff
    i i.isClosedEmbedding.isInducing z r]
  change r ∈ LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i (i z)) ↔ _
  rw [h]
  rfl

def cubicClosedPointSerreFiniteZeroResidual_localSection_quotientStalkRingEquiv
    {X : Scheme.{u}} {E : X.Modules} (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift (Fin 2)) ≅ E.over U)
    (s : E.sections) (z : localSectionZeroSubschemeOfOver U (ULift (Fin 2)) t s) :
    let i := localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s
    let ab := cubicClosedPointSerreFiniteZeroResidual_localSectionStalkPair U t s (i z)
    ((U : Scheme.{u}).presheaf.stalk (i z) ⧸ Ideal.span ({ab.1, ab.2} :
      Set ((U : Scheme.{u}).presheaf.stalk (i z)))) ≃+*
      (localSectionZeroSubschemeOfOver U (ULift (Fin 2)) t s).presheaf.stalk z := by
  let i := localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s
  letI : IsClosedImmersion i := isClosedImmersion_localSectionZeroSubschemeOfOverι
    U (ULift (Fin 2)) t s
  exact (Ideal.quotEquivOfEq
    (cubicClosedPointSerreFiniteZeroResidual_localSection_stalkMap_kernel U t s z).symm).trans
    ((i.stalkMap z).hom.quotientKerEquivOfSurjective (i.stalkMap_surjective z))

end PfaffianDescent
