import PfaffianDescent.SchemeModuleOriginalBaseStalkResidueTower
import PfaffianDescent.CorayActualResidueDegreeWeight
import Mathlib.Algebra.Algebra.RestrictScalars

/-! Original base scalars on native stalks and their actual residue weights.
The canonical quotient residue action and the independently original
pointAlgebra action are kept apart until an identity K-linear equivalence
is proved. Actual section germs retain their original pi-induced action.
SOURCE ONLY / UNVERIFIED. Root alone compiles. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The native residue field with the original point-to-base action. -/
def SchemePointResidueOver (pi : X ⟶ Spec (CommRingCat.of K)) (x : X) :=
  X.residueField x

instance schemePointResidueOver_field
    (pi : X ⟶ Spec (CommRingCat.of K)) (x : X) :
    Field (SchemePointResidueOver pi x) :=
  inferInstanceAs (Field (X.residueField x))

instance schemePointResidueOver_algebra
    (pi : X ⟶ Spec (CommRingCat.of K)) (x : X) :
    Algebra K (SchemePointResidueOver pi x) :=
  AllCharacteristics.pointAlgebra pi x

/-- Explicitly pin the module to the original algebra, so the quotient
residue Module instance cannot silently replace its scalar action. -/
instance schemePointResidueOver_module
    (pi : X ⟶ Spec (CommRingCat.of K)) (x : X) :
    Module K (SchemePointResidueOver pi x) :=
  @Algebra.toModule K (SchemePointResidueOver pi x) _ _
    (schemePointResidueOver_algebra pi x)

/-- The canonical quotient action has precisely the original residue map
on constants; this follows from the actual scheme square. -/
theorem schemeStalkCanonicalResidue_algebraMap
    (pi : X ⟶ Spec (CommRingCat.of K)) (x : X) (c : K) :
    letI := schemeStalkBaseAlgebra pi x
    algebraMap K (IsLocalRing.ResidueField (X.presheaf.stalk x)) c =
      (Spec.preimage (X.fromSpecResidueField x ≫ pi)).hom c := by
  letI := schemeStalkBaseAlgebra pi x
  rw [IsScalarTower.algebraMap_apply K (X.presheaf.stalk x)
    (IsLocalRing.ResidueField (X.presheaf.stalk x)),
    IsLocalRing.ResidueField.algebraMap_eq]
  exact RingHom.congr_fun (schemeStalkBaseRingHom_residue pi x) c

/-- Identity on the SAME native residue field, now K-linear between the
canonical quotient action and the independent original point action. -/
def schemeStalkCanonicalResidueLinearEquivOriginal
    (pi : X ⟶ Spec (CommRingCat.of K)) (x : X) :
    letI := schemeStalkBaseAlgebra pi x
    IsLocalRing.ResidueField (X.presheaf.stalk x) ≃ₗ[K]
      SchemePointResidueOver pi x := by
  letI := schemeStalkBaseAlgebra pi x
  refine { toAddEquiv := AddEquiv.refl _
           map_smul' := ?_ }
  intro c z
  change (c • z : IsLocalRing.ResidueField (X.presheaf.stalk x)) =
    c • (show SchemePointResidueOver pi x from z)
  rw [Algebra.smul_def, Algebra.smul_def]
  change algebraMap K (IsLocalRing.ResidueField (X.presheaf.stalk x)) c * z =
    (show IsLocalRing.ResidueField (X.presheaf.stalk x) from
      (Spec.preimage (X.fromSpecResidueField x ≫ pi)).hom c) * z
  exact congrArg (fun a : IsLocalRing.ResidueField (X.presheaf.stalk x) => a * z)
    (schemeStalkCanonicalResidue_algebraMap pi x c)

/-- This scalar comparison is literally identity on the original residue
field; no underlying field element is transported to a different field. -/
theorem schemeStalkCanonicalResidueLinearEquivOriginal_apply
    (pi : X ⟶ Spec (CommRingCat.of K)) (x : X)
    (z : IsLocalRing.ResidueField (X.presheaf.stalk x)) :
    letI := schemeStalkBaseAlgebra pi x
    schemeStalkCanonicalResidueLinearEquivOriginal pi x z =
      (show SchemePointResidueOver pi x from z) := rfl

/-- Closed-point finite type supplies the original finite residue degree.
No native-stalk algebra is installed in this statement or proof. -/
theorem schemePointResidueOver_finite_and_finrank
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (P : closedPoints X) :
    Module.Finite K (SchemePointResidueOver pi P.1) ∧
      Module.finrank K (SchemePointResidueOver pi P.1) = pi.residueDegree P.1 := by
  letI := AllCharacteristics.pointAlgebra pi P.1
  letI : Module K (X.residueField P.1) :=
    @Algebra.toModule K (X.residueField P.1) _ _
      (AllCharacteristics.pointAlgebra pi P.1)
  constructor
  · change Module.Finite K (X.residueField P.1)
    exact AllCharacteristics.closedPoint_moduleFinite pi P
  · change Module.finrank K (X.residueField P.1) = pi.residueDegree P.1
    exact AllCharacteristics.closedPoint_finrank_eq_residueDegree pi P

/-- Finite residue degree for the canonical quotient action is transported
by the proved identity equivalence, rather than assumed from a tower. -/
theorem schemeStalkCanonicalResidue_finite
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (P : closedPoints X) :
    letI := schemeStalkBaseAlgebra pi P.1
    Module.Finite K (IsLocalRing.ResidueField (X.presheaf.stalk P.1)) := by
  letI := schemeStalkBaseAlgebra pi P.1
  letI : Module.Finite K (SchemePointResidueOver pi P.1) :=
    (schemePointResidueOver_finite_and_finrank pi P).1
  exact Module.Finite.equiv
    (schemeStalkCanonicalResidueLinearEquivOriginal pi P.1).symm

/-- The canonical quotient residue finrank equals the SAME original
scheme residue degree through the proved identity equivalence. -/
theorem schemeStalkCanonicalResidue_finrank
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (P : closedPoints X) :
    letI := schemeStalkBaseAlgebra pi P.1
    Module.finrank K (IsLocalRing.ResidueField (X.presheaf.stalk P.1)) =
      pi.residueDegree P.1 := by
  letI := schemeStalkBaseAlgebra pi P.1
  exact (schemeStalkCanonicalResidueLinearEquivOriginal pi P.1).finrank_eq.trans
    (schemePointResidueOver_finite_and_finrank pi P).2

/-- The SAME literal module stalk, restricted along the original native
base-constant germ. Its action does not use a quotient/frame equivalence. -/
def SchemeModuleStalkOver (pi : X ⟶ Spec (CommRingCat.of K))
    (M : X.Modules) (x : X) := M.presheaf.stalk x

instance schemeModuleStalkOver_addCommGroup
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (x : X) :
    AddCommGroup (SchemeModuleStalkOver pi M x) :=
  inferInstanceAs (AddCommGroup (M.presheaf.stalk x))

instance schemeModuleStalkOver_nativeModule
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (SchemeModuleStalkOver pi M x) :=
  schemeModuleStalkModule M x

instance schemeModuleStalkOver_groundModule
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (x : X) :
    Module K (SchemeModuleStalkOver pi M x) :=
  Module.compHom (SchemeModuleStalkOver pi M x) (schemeStalkBaseRingHom pi x)

theorem schemeModuleStalkOver_isScalarTower
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (x : X) :
    letI := schemeStalkBaseAlgebra pi x
    IsScalarTower K (X.presheaf.stalk x) (SchemeModuleStalkOver pi M x) := by
  letI := schemeStalkBaseAlgebra pi x
  exact IsScalarTower.restrictScalars K (X.presheaf.stalk x)
    (SchemeModuleStalkOver pi M x)

/-- Original pi-scalars commute with the original germ on every actual
neighborhood. This identifies restriction scalars by their actual action. -/
theorem schemeModuleStalkOver_germ_smul
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (x : X)
    (U : X.Opens) (hxU : x ∈ U) (c : K)
    (s : SchemeModuleOpenSectionsOver pi M U) :
    (show SchemeModuleStalkOver pi M x from M.presheaf.germ U x hxU (c • s)) =
      c • (show SchemeModuleStalkOver pi M x from M.presheaf.germ U x hxU s) := by
  letI := schemeModuleStalkModule M x
  let sU : Γ(M, U) := s
  have hg : M.presheaf.germ U x hxU (schemeOpenBaseRingHom pi U c • sU) =
      X.presheaf.germ U x hxU (schemeOpenBaseRingHom pi U c) •
        M.presheaf.germ U x hxU sU :=
    PresheafOfModules.germ_smul M.val x U hxU (schemeOpenBaseRingHom pi U c) sU
  have hc := schemeStalkBaseRingHom_germ pi x U hxU c
  exact hg.trans (congrArg (fun r : X.presheaf.stalk x =>
    r • M.presheaf.germ U x hxU sU) hc)

/-- The actual section germ is K-linear for the SAME original action. -/
def schemeModuleOriginalBaseGermLinearMap
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (x : X)
    (U : X.Opens) (hxU : x ∈ U) :
    SchemeModuleOpenSectionsOver pi M U →ₗ[K] SchemeModuleStalkOver pi M x where
  toFun := fun s => M.presheaf.germ U x hxU (show Γ(M, U) from s)
  map_add' := fun s t => (M.presheaf.germ U x hxU).hom.map_add
    (show Γ(M, U) from s) (show Γ(M, U) from t)
  map_smul' := schemeModuleStalkOver_germ_smul pi M x U hxU

/-- The K-linear germ is the SAME original presheaf germ. -/
theorem schemeModuleOriginalBaseGermLinearMap_apply
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (x : X)
    (U : X.Opens) (hxU : x ∈ U) (s : SchemeModuleOpenSectionsOver pi M U) :
    schemeModuleOriginalBaseGermLinearMap pi M x U hxU s =
      (show SchemeModuleStalkOver pi M x from M.presheaf.germ U x hxU s) := rfl

/-- The original categorical scalar endomorphism induces exactly this
original K-action on the SAME actual native module stalk. -/
theorem schemeModuleStalkOver_originalBaseSmul_apply
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (x : X) (c : K)
    (m : SchemeModuleStalkOver pi M x) :
    (show SchemeModuleStalkOver pi M x from
      ((schemeModuleStalkModuleFunctor X x).map
        (schemeModuleHomBaseSmul pi c (𝟙 M))).hom m) = c • m :=
  schemeModuleStalkModuleFunctor_originalBaseSmul_apply pi M x c m

/-- Finite native local length at an actual closed point supplies finite
dimension and the actual original residue-degree weight. Finiteness and
degree of the residue extension are constructed internally. -/
theorem schemeModuleOriginalBaseStalk_finite_and_finrank
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (M : X.Modules) (P : closedPoints X)
    (hM : IsFiniteLength (X.presheaf.stalk P.1)
      ((schemeModuleStalkModuleFunctor X P.1).obj M)) :
    Module.Finite K (SchemeModuleStalkOver pi M P.1) ∧
      Module.finrank K (SchemeModuleStalkOver pi M P.1) =
        (Module.length (X.presheaf.stalk P.1)
          ((schemeModuleStalkModuleFunctor X P.1).obj M)).toNat *
            pi.residueDegree P.1 := by
  letI := schemeStalkBaseAlgebra pi P.1
  letI : IsScalarTower K (X.presheaf.stalk P.1)
      (SchemeModuleStalkOver pi M P.1) :=
    schemeModuleStalkOver_isScalarTower pi M P.1
  letI : Module.Finite K (IsLocalRing.ResidueField (X.presheaf.stalk P.1)) :=
    schemeStalkCanonicalResidue_finite pi P
  have hM' : IsFiniteLength (X.presheaf.stalk P.1)
      (SchemeModuleStalkOver pi M P.1) := hM
  refine ⟨localModule_finite_over_ground_of_finiteLength hM', ?_⟩
  rw [localModule_ground_finrank_eq_residue_weight hM',
    schemeStalkCanonicalResidue_finrank pi P]
  rfl

end PfaffianDescent.Coray
