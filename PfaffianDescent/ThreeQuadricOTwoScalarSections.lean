import PfaffianDescent.VoisinProjectiveThreeGlobalFunctions
import PfaffianDescent.SchemeModuleGlobalSectionsTop
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! SOURCE ONLY / UNVERIFIED. Actual constant unit sections and their
threefold biproduct; no chosen ambient global equivalence is an input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist BundleSectionZeroLocus
universe u v w s
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K
local notation "base" => ambientToBase (R := K) (σ := Fin 4)

private theorem p3OTwo_scalarConstantTripleLift_bijective
    {S : Type s} {D : Type v} [Category.{w} D] [HasZeroMorphisms D]
    (U M : D) [HasBiproduct (fun _ : Fin 3 => M)]
    (g : S → (U ⟶ M)) (hg : Function.Bijective g) :
    Function.Bijective (fun c : Fin 3 → S =>
      biproduct.lift (f := fun _ : Fin 3 => M) (fun r : Fin 3 => g (c r))) := by
  let P : Fin 3 → D := fun _ => M
  constructor
  · intro c d h
    funext r
    apply hg.1
    have hπ := congrArg
      (fun z : U ⟶ ⨁ P => z ≫ biproduct.π P r) h
    exact (biproduct.lift_π (f := P) (fun r => g (c r)) r).symm.trans
      (hπ.trans (biproduct.lift_π (f := P) (fun r => g (d r)) r))
  · intro z
    let c : Fin 3 → S := fun r => Classical.choose
      (hg.2 (z ≫ biproduct.π P r))
    refine ⟨c, ?_⟩
    apply biproduct.hom_ext
    intro r
    exact (biproduct.lift_π (f := P) (fun r => g (c r)) r).trans
      (Classical.choose_spec (hg.2 (z ≫ biproduct.π P r)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual scalar endomorphism O → O. -/
def p3OTwoUnitScalarLinearMap :
    K →ₗ[K] SchemeModuleGlobalSectionsOver base (schemeModuleUnit (Proj PS)) where
  toFun := schemeModuleConstantEndomorphism base
  map_add' a b := (schemeModuleConstantEndomorphismAddHom base).map_add a b
  map_smul' a b := by
    change schemeModuleConstantEndomorphism base (a * b) =
      schemeModuleConstantEndomorphism base a ≫ schemeModuleConstantEndomorphism base b
    simp only [schemeModuleConstantEndomorphism, map_mul,
      unitEndomorphismOfRegularFunction_mul]

/-- Ordinary global functions on actual P3 are internally proved constant. -/
theorem p3OTwoUnitScalarLinearMap_bijective :
    Function.Bijective (p3OTwoUnitScalarLinearMap K) := by
  have hb := ambientToBase_affineFunctionHom_bijective K
  constructor
  · intro a b hab
    apply hb.1
    have h := congrArg (unitEndomorphismValue (X := Proj PS)) hab
    change unitEndomorphismValue (schemeModuleConstantEndomorphism base a) =
      unitEndomorphismValue (schemeModuleConstantEndomorphism base b) at h
    simpa only [schemeModuleConstantEndomorphism,
      unitEndomorphismValue_ofRegularFunction] using h
  · intro s
    obtain ⟨a, ha⟩ := hb.2 (unitEndomorphismValue (X := Proj PS) s)
    refine ⟨a, ?_⟩
    change unitEndomorphismOfRegularFunction (affineFunctionHom base a) = s
    rw [ha]
    exact unitEndomorphismOfRegularFunction_value s

def p3OTwoUnitScalarLinearEquiv :
    K ≃ₗ[K] SchemeModuleGlobalSectionsOver base (schemeModuleUnit (Proj PS)) :=
  LinearEquiv.ofBijective (p3OTwoUnitScalarLinearMap K)
    (p3OTwoUnitScalarLinearMap_bijective K)

abbrev p3OTwoActualUnitTriple : Fin 3 → (Proj PS).Modules :=
  fun _ => SheafOfModules.unit (Proj PS).ringCatSheaf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The three actual scalar unit sections, represented by a biproduct lift. -/
def p3OTwoScalarTripleLinearMap : (Fin 3 → K) →ₗ[K]
    SchemeModuleGlobalSectionsOver base (⨁ p3OTwoActualUnitTriple K) where
  toFun c := biproduct.lift (f := p3OTwoActualUnitTriple K) (fun r => p3OTwoUnitScalarLinearMap K (c r))
  map_add' c d := by
    apply biproduct.hom_ext
    intro r
    change (biproduct.lift (f := p3OTwoActualUnitTriple K)
      (fun t => p3OTwoUnitScalarLinearMap K (c t + d t))) ≫
        biproduct.π (p3OTwoActualUnitTriple K) r =
      ((biproduct.lift (f := p3OTwoActualUnitTriple K)
        (fun t => p3OTwoUnitScalarLinearMap K (c t))) +
        biproduct.lift (f := p3OTwoActualUnitTriple K)
          (fun t => p3OTwoUnitScalarLinearMap K (d t))) ≫
        biproduct.π (p3OTwoActualUnitTriple K) r
    rw [Preadditive.add_comp, biproduct.lift_π, biproduct.lift_π, biproduct.lift_π]
    exact (p3OTwoUnitScalarLinearMap K).map_add (c r) (d r)
  map_smul' a c := by
    apply biproduct.hom_ext
    intro r
    change (biproduct.lift (f := p3OTwoActualUnitTriple K) (fun t => p3OTwoUnitScalarLinearMap K (a * c t))) ≫
        biproduct.π (p3OTwoActualUnitTriple K) r =
      (schemeModuleConstantEndomorphism base a ≫
        biproduct.lift (f := p3OTwoActualUnitTriple K) (fun t => p3OTwoUnitScalarLinearMap K (c t))) ≫
        biproduct.π (p3OTwoActualUnitTriple K) r
    simp only [Category.assoc, biproduct.lift_π]
    exact (p3OTwoUnitScalarLinearMap K).map_smul a (c r)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem p3OTwoScalarTripleLinearMap_bijective :
    Function.Bijective (p3OTwoScalarTripleLinearMap K) := by
  exact p3OTwo_scalarConstantTripleLift_bijective
    (schemeModuleUnit (Proj PS)) (schemeModuleUnit (Proj PS))
    (p3OTwoUnitScalarLinearMap K) (p3OTwoUnitScalarLinearMap_bijective K)

def p3OTwoScalarTripleLinearEquiv : (Fin 3 → K) ≃ₗ[K]
    SchemeModuleGlobalSectionsOver base (⨁ p3OTwoActualUnitTriple K) :=
  LinearEquiv.ofBijective (p3OTwoScalarTripleLinearMap K)
    (p3OTwoScalarTripleLinearMap_bijective K)

end PfaffianDescent
