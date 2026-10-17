import PfaffianDescent.VoisinSheafStalk
import PfaffianDescent.SchemePushforwardUnitSections

/-!
# Canonical quotient-stalk coordinates

The quotient equivalence constructed from the actual closed-immersion map
preserves residue classes. These formulas fix its scalar normalization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace PfaffianDescent

universe u

/-- The quotient equivalence sends the class of a ring element to its image
under the original surjective map. -/
theorem quotientStalkLinearEquivOfSurjectiveAndKernelEq_mk
    {R S : Type u} [CommRing R] [AddCommGroup S] [Module R S]
    (I : Ideal R) (f : R →ₗ[R] S) (hsurj : Function.Surjective f)
    (hker : LinearMap.ker f = I) (r : R) :
    quotientStalkLinearEquivOfSurjectiveAndKernelEq I f hsurj hker
        (Ideal.Quotient.mk I r) = f r := by
  change ((f.quotKerEquivRange
    ((Submodule.quotEquivOfEq (I : Submodule R R) f.ker hker.symm)
      (Submodule.Quotient.mk r))) : S) = f r
  rw [Submodule.quotEquivOfEq_mk]
  exact f.quotKerEquivRange_apply_mk r

/-- The inverse coordinate has no arbitrary scalar factor. -/
theorem quotientStalkLinearEquivOfSurjectiveAndKernelEq_symm_apply
    {R S : Type u} [CommRing R] [AddCommGroup S] [Module R S]
    (I : Ideal R) (f : R →ₗ[R] S) (hsurj : Function.Surjective f)
    (hker : LinearMap.ker f = I) (r : R) :
    (quotientStalkLinearEquivOfSurjectiveAndKernelEq I f hsurj hker).symm
        (f r) = Ideal.Quotient.mk I r := by
  rw [← quotientStalkLinearEquivOfSurjectiveAndKernelEq_mk I f hsurj hker r]
  exact LinearEquiv.symm_apply_apply _ _

set_option linter.style.haveILetI false in
/-- The canonical coordinate on a closed-immersion stalk sends the image of
`r` to its residue class, in particular the image of `1` to `1`. -/
theorem closedImmersionPushforwardStalkQuotientLinearEquivOfKernelEq_symm_apply
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (x : X) :
    letI := schemeModuleStalkModule (show X.Modules from
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) x
    ∀ (f g : X.presheaf.stalk x)
      (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x)))
      (r : X.presheaf.stalk x),
      (closedImmersionPushforwardStalkQuotientLinearEquivOfKernelEq
        i x f g hkernel).symm (closedImmersionPushforwardStalkFromRingLinearMap i x r) =
          Ideal.Quotient.mk (Ideal.span ({f, g} : Set _)) r := by
  dsimp only
  letI := schemeModuleStalkModule (show X.Modules from
    (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) x
  intro f g hkernel r
  exact quotientStalkLinearEquivOfSurjectiveAndKernelEq_symm_apply
    (Ideal.span ({f, g} : Set _)) (closedImmersionPushforwardStalkFromRingLinearMap i x)
    (closedImmersionPushforwardStalkFromRingLinearMap_surjective i x) hkernel r

set_option backward.isDefEq.respectTransparency false in
/-- The unit-twisted point quotient has a canonical stalk coordinate,
constructed using the tensor-unit isomorphism rather than a chosen twist
trivialization. -/
noncomputable def closedImmersionUnitTwistStalkQuotientIso
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (x : X) :
    letI := schemeModuleStalkModule (show X.Modules from
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) x
    ∀ (f g : X.presheaf.stalk x)
      (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x))),
    (schemeModuleStalkModuleFunctor X x).obj
        (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃ ≅
      ModuleCat.of (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ Ideal.span ({f, g} : Set _)) := by
  dsimp only
  let M : X.Modules := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit Z.ringCatSheaf)
  letI := schemeModuleStalkModule M x
  intro f g hkernel
  exact (schemeModuleStalkModuleFunctor X x).mapIso
    (closedImmersionIdealTwistSequenceUnitTargetIso i) ≪≫
    LinearEquiv.toModuleIso
      (closedImmersionPushforwardStalkQuotientLinearEquivOfKernelEq
        i x f g hkernel).symm

end PfaffianDescent
