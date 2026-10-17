import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf

/- SOURCE ONLY / UNVERIFIED. The base scalar map is derived from the actual
scheme structure morphism and actual restrictions of its structure sheaf. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {k : Type u} [CommRing k] {X : Scheme.{u}}

/-- Constants on the actual structure presheaf, derived from X -> Spec k. -/
def schemeBaseScalarPresheafMap (g : X ⟶ Spec (CommRingCat.of k)) :
    (Functor.const X.Opensᵒᵖ).obj (CommRingCat.of k) ⟶ X.presheaf where
  app U := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop ≫
    X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  naturality {U V} f := by
    have hres : X.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op =
        X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op ≫
          X.presheaf.map f := by
      rw [← Functor.map_comp]
      exact congrArg X.presheaf.map (Subsingleton.elim _ _)
    change (𝟙 (CommRingCat.of k)) ≫
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop ≫
          X.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op) =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop ≫
          X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op) ≫
        X.presheaf.map f
    simpa only [Category.id_comp, Category.assoc] using
      congrArg (fun r => (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop ≫ r) hres

/-- The genuine presheaf of relative differentials on all opens of X. -/
def schemeRelativeDifferentialsPresheaf (g : X ⟶ Spec (CommRingCat.of k)) :
    X.PresheafOfModules :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
    (schemeBaseScalarPresheafMap g)

/-- The universal derivation is supplied by the actual ring differentials,
not by a desired chart module comparison. -/
def schemeRelativeDifferentialsPresheafDerivation
    (g : X ⟶ Spec (CommRingCat.of k)) :
    (schemeRelativeDifferentialsPresheaf g).Derivation'
      (schemeBaseScalarPresheafMap g) :=
  PresheafOfModules.DifferentialsConstruction.derivation'
    (schemeBaseScalarPresheafMap g)

def schemeRelativeDifferentialsPresheafUniversal
    (g : X ⟶ Spec (CommRingCat.of k)) :
    (schemeRelativeDifferentialsPresheafDerivation g).Universal :=
  PresheafOfModules.DifferentialsConstruction.isUniversal'
    (schemeBaseScalarPresheafMap g)

end PfaffianDescent
