import PfaffianDescent.SchemeModuleGlobalScalarStalk
import PfaffianDescent.SchemeModuleBaseLinearCategory
import AllCharacteristics.ClosedPointAlgebra
import Mathlib.Algebra.Algebra.Tower

/-! The original pi-induced K -> native stalk -> residue scalar tower.
The SAME base constants and native germs are used. Residue compatibility
with pointAlgebra is proved through the actual scheme maps; module scalar
compatibility follows from the SAME original base-scalar endomorphism.
No weighted length, section existence or cycle degree is claimed.
SOURCE ONLY / UNVERIFIED: root alone compiles. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original base constants followed by the native top germ. This
ring map is not defined through a desired quotient or field comparison. -/
def schemeStalkBaseRingHom (pi : X ⟶ Spec (CommRingCat.of K)) (x : X) :
    K →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom.comp (affineFunctionHom pi)

/-- The canonical algebra induced by that SAME original stalk map. -/
abbrev schemeStalkBaseAlgebra (pi : X ⟶ Spec (CommRingCat.of K)) (x : X) :
    Algebra K (X.presheaf.stalk x) :=
  (schemeStalkBaseRingHom pi x).toAlgebra

/-- On every actual neighborhood, its original base-constant germ is
the SAME native scalar; restriction compatibility is not assumed. -/
theorem schemeStalkBaseRingHom_germ
    (pi : X ⟶ Spec (CommRingCat.of K)) (x : X)
    (U : X.Opens) (hxU : x ∈ U) (c : K) :
    X.presheaf.germ U x hxU (schemeOpenBaseRingHom pi U c) =
      schemeStalkBaseRingHom pi x c :=
  X.presheaf.germ_res_apply (homOfLE (show U ≤ ⊤ from le_top)) x hxU
    (affineFunctionHom pi c)

/-- This actual stalk algebra reproduces the original scheme morphism
from Spec of the SAME native local ring to Spec K. -/
theorem schemeStalkBaseRingHom_spec
    (pi : X ⟶ Spec (CommRingCat.of K)) (x : X) :
    Spec.map (CommRingCat.ofHom (schemeStalkBaseRingHom pi x)) =
      X.fromSpecStalk x ≫ pi := by
  change Spec.map (CommRingCat.ofHom (affineFunctionHom pi) ≫
    X.presheaf.germ ⊤ x trivial) = _
  rw [Spec.map_comp, ← X.fromSpecStalk_toSpecΓ x, Category.assoc]
  change X.fromSpecStalk x ≫ morphismFromAffineFunctions X (affineFunctionHom pi) = _
  exact congrArg (fun f => X.fromSpecStalk x ≫ f) (from_affineFunctionHom pi)

/-- Composing with the ORIGINAL native residue map gives exactly the
Spec-preimage map defining the SAME pointAlgebra. No residue comparison
or scalar compatibility premise is supplied. -/
theorem schemeStalkBaseRingHom_residue
    (pi : X ⟶ Spec (CommRingCat.of K)) (x : X) :
    (X.residue x).hom.comp (schemeStalkBaseRingHom pi x) =
      (Spec.preimage (X.fromSpecResidueField x ≫ pi)).hom := by
  have hspec : Spec.map (CommRingCat.ofHom (schemeStalkBaseRingHom pi x) ≫ X.residue x) =
      X.fromSpecResidueField x ≫ pi := by
    rw [Spec.map_comp, schemeStalkBaseRingHom_spec]
    exact (Category.assoc (Spec.map (X.residue x)) (X.fromSpecStalk x) pi).symm
  have hcat : CommRingCat.ofHom (schemeStalkBaseRingHom pi x) ≫ X.residue x =
      Spec.preimage (X.fromSpecResidueField x ≫ pi) :=
    Spec.map_injective (hspec.trans (Spec.map_preimage _).symm)
  exact CommRingCat.hom_ext_iff.mp hcat

/-- Genuine tower with INDEPENDENT original pointAlgebra; its equality
with the residue-composite algebra is proved above, not defined into it. -/
theorem schemeStalkBaseAlgebra_residue_isScalarTower
    (pi : X ⟶ Spec (CommRingCat.of K)) (x : X) :
    letI := schemeStalkBaseAlgebra pi x
    letI : Algebra (X.presheaf.stalk x) (X.residueField x) := (X.residue x).hom.toAlgebra
    letI : Module (X.presheaf.stalk x) (X.residueField x) :=
      @Algebra.toModule (X.presheaf.stalk x) (X.residueField x) _ _ (X.residue x).hom.toAlgebra
    letI := AllCharacteristics.pointAlgebra pi x
    letI : Module K (X.residueField x) :=
      @Algebra.toModule K (X.residueField x) _ _ (AllCharacteristics.pointAlgebra pi x)
    IsScalarTower K (X.presheaf.stalk x) (X.residueField x) := by
  letI := schemeStalkBaseAlgebra pi x
  letI : Algebra (X.presheaf.stalk x) (X.residueField x) := (X.residue x).hom.toAlgebra
  letI : Module (X.presheaf.stalk x) (X.residueField x) :=
    @Algebra.toModule (X.presheaf.stalk x) (X.residueField x) _ _ (X.residue x).hom.toAlgebra
  letI := AllCharacteristics.pointAlgebra pi x
  letI : Module K (X.residueField x) :=
    @Algebra.toModule K (X.residueField x) _ _ (AllCharacteristics.pointAlgebra pi x)
  apply IsScalarTower.of_algebraMap_eq'
  change (Spec.preimage (X.fromSpecResidueField x ≫ pi)).hom =
    (X.residue x).hom.comp (schemeStalkBaseRingHom pi x)
  exact (schemeStalkBaseRingHom_residue pi x).symm

/-- The ORIGINAL pi-induced scalar endomorphism on M acts on its SAME
native stalk by precisely the original scalar germ. This establishes
action provenance before restricting the native stalk module to K. -/
theorem schemeModuleStalkModuleFunctor_originalBaseSmul_apply
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (x : X) (c : K)
    (m : (schemeModuleStalkModuleFunctor X x).obj M) :
    ((schemeModuleStalkModuleFunctor X x).map (schemeModuleHomBaseSmul pi c (𝟙 M))).hom m =
      schemeStalkBaseRingHom pi x c • m := by
  let phi := schemeModuleHomBaseSmul pi c (𝟙 M)
  have hphi : ∀ (U : X.Opens) (y : M.val.obj (op U)),
      phi.val.app (op U) y =
        X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (affineFunctionHom pi c) • y := by
    intro U y
    rfl
  exact schemeModuleStalkLinearMap_eq_germ_smul_of_app M phi (affineFunctionHom pi c) hphi x m

end PfaffianDescent.Coray
