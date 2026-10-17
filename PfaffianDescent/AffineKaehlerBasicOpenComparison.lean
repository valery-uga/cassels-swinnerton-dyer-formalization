import PfaffianDescent.AffineKaehlerSheafPointFiber
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.BaseChange

/- SOURCE ONLY / UNVERIFIED. Actual sections on an actual principal open;
this is the canonical Kähler localization comparison required by gluing. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Localize with the genuine pointwise R-action on the structure module.
No forgotten tilde R-action is silently substituted here. -/
private def rawBasicOpenTensorEquiv (M : ModuleCat R) (f : R) :
    ((structureSheafInType R R).obj.obj (Opposite.op (PrimeSpectrum.basicOpen f))) ⊗[R] M
      ≃ₗ[((structureSheafInType R R).obj.obj (Opposite.op (PrimeSpectrum.basicOpen f)))]
        ((structureSheafInType R M).obj.obj (Opposite.op (PrimeSpectrum.basicOpen f))) :=
  (IsLocalizedModule.isBaseChange (Submonoid.powers f)
    ((structureSheafInType R R).obj.obj (Opposite.op (PrimeSpectrum.basicOpen f)))
    (StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen f))).equiv

private lemma rawBasicOpenTensorEquiv_one_tmul (M : ModuleCat R) (f : R) (m : M) :
    rawBasicOpenTensorEquiv M f ((1 :
      (structureSheafInType R R).obj.obj (Opposite.op (PrimeSpectrum.basicOpen f))) ⊗ₜ[R] m) =
      StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen f) m := by
  simp only [rawBasicOpenTensorEquiv, IsBaseChange.equiv_tmul, one_smul]

/-- Supply the ACTUAL local section action at its canonical Spec ring,
then expose that same A-module under the raw section-ring carrier alias. -/
private def rawBasicOpenActualSectionModule (M : ModuleCat R) (f : R) :
    Module ((structureSheafInType R R).obj.obj (Opposite.op (PrimeSpectrum.basicOpen f)))
      Γ(tilde (R := CommRingCat.of R) M, PrimeSpectrum.basicOpen f) :=
  inferInstanceAs
    (Module Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f)
      Γ(tilde (R := CommRingCat.of R) M, PrimeSpectrum.basicOpen f))

/-- The section values and local A-action are the SAME. Only the forgotten
R-actions differ, as accounted for by tilde.modulesSpecToSheafIso. -/
private def rawBasicOpenActualSectionEquiv (M : ModuleCat R) (f : R) :
    letI : Module
        ((structureSheafInType R R).obj.obj (Opposite.op (PrimeSpectrum.basicOpen f)))
        Γ(tilde (R := CommRingCat.of R) M, PrimeSpectrum.basicOpen f) :=
      rawBasicOpenActualSectionModule M f
    ((structureSheafInType R M).obj.obj (Opposite.op (PrimeSpectrum.basicOpen f)))
      ≃ₗ[((structureSheafInType R R).obj.obj (Opposite.op (PrimeSpectrum.basicOpen f)))]
        Γ(tilde (R := CommRingCat.of R) M, PrimeSpectrum.basicOpen f) := by
  letI : Module
      ((structureSheafInType R R).obj.obj (Opposite.op (PrimeSpectrum.basicOpen f)))
      Γ(tilde (R := CommRingCat.of R) M, PrimeSpectrum.basicOpen f) :=
    rawBasicOpenActualSectionModule M f
  exact
    { toFun := fun x => x
      invFun := fun x => x
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

private lemma rawBasicOpenActualSectionEquiv_toOpen (M : ModuleCat R) (f : R) (m : M) :
    rawBasicOpenActualSectionEquiv M f
      (StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen f) m) =
        (tilde.toOpen (R := CommRingCat.of R) M (PrimeSpectrum.basicOpen f)).hom m := by
  rfl

/-- Ring differentials of the actual principal-open ring equal sections of
its actual tilde differential sheaf. The map on d(r) is proved below. -/
def affineKaehlerBasicOpenEquiv (f : R) :
    let A := Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f)
    letI : Algebra R A := inferInstanceAs
      (Algebra R ((Spec.structureSheaf R).obj.obj
        (Opposite.op (PrimeSpectrum.basicOpen f))))
    letI : Algebra k A := ((algebraMap R A).comp (algebraMap k R)).toAlgebra
    KaehlerDifferential k A ≃ₗ[A]
      Γ(affineKaehlerModuleSheaf (k := k) (R := R), PrimeSpectrum.basicOpen f) := by
  let A := Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f)
  letI : Algebra R A := inferInstanceAs
    (Algebra R ((Spec.structureSheaf R).obj.obj
      (Opposite.op (PrimeSpectrum.basicOpen f))))
  letI : Algebra k A := ((algebraMap R A).comp (algebraMap k R)).toAlgebra
  letI : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsLocalization (Submonoid.powers f) A := inferInstanceAs
    (IsLocalization (Submonoid.powers f)
      ((Spec.structureSheaf R).obj.obj (Opposite.op (PrimeSpectrum.basicOpen f))))
  letI : Algebra.FormallyEtale R A :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers f)
  exact (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R A).symm ≪≫ₗ
    rawBasicOpenTensorEquiv (ModuleCat.of R (KaehlerDifferential k R)) f ≪≫ₗ
    rawBasicOpenActualSectionEquiv (ModuleCat.of R (KaehlerDifferential k R)) f

@[simp] lemma affineKaehlerBasicOpenEquiv_D (f r : R) :
    let A := Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f)
    letI : Algebra R A := inferInstanceAs
      (Algebra R ((Spec.structureSheaf R).obj.obj
        (Opposite.op (PrimeSpectrum.basicOpen f))))
    letI : Algebra k A := ((algebraMap R A).comp (algebraMap k R)).toAlgebra
    affineKaehlerBasicOpenEquiv (k := k) f
      (KaehlerDifferential.D k A (algebraMap R A r)) =
        (tilde.toOpen (R := CommRingCat.of R) (ModuleCat.of R (KaehlerDifferential k R))
          (PrimeSpectrum.basicOpen f)).hom (KaehlerDifferential.D k R r) := by
  let A := Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f)
  letI : Algebra R A := inferInstanceAs
    (Algebra R ((Spec.structureSheaf R).obj.obj
      (Opposite.op (PrimeSpectrum.basicOpen f))))
  letI : Algebra k A := ((algebraMap R A).comp (algebraMap k R)).toAlgebra
  letI : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsLocalization (Submonoid.powers f) A := inferInstanceAs
    (IsLocalization (Submonoid.powers f)
      ((Spec.structureSheaf R).obj.obj (Opposite.op (PrimeSpectrum.basicOpen f))))
  letI : Algebra.FormallyEtale R A :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers f)
  change rawBasicOpenActualSectionEquiv (ModuleCat.of R (KaehlerDifferential k R)) f
    (rawBasicOpenTensorEquiv (ModuleCat.of R (KaehlerDifferential k R)) f
      ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R A).symm
        (KaehlerDifferential.D k A (algebraMap R A r)))) = _
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  exact (congrArg
    (rawBasicOpenActualSectionEquiv (ModuleCat.of R (KaehlerDifferential k R)) f)
    (rawBasicOpenTensorEquiv_one_tmul
      (ModuleCat.of R (KaehlerDifferential k R)) f (KaehlerDifferential.D k R r))).trans
        (rawBasicOpenActualSectionEquiv_toOpen
          (ModuleCat.of R (KaehlerDifferential k R)) f (KaehlerDifferential.D k R r))

end PfaffianDescent
