import PfaffianDescent.CoordinateModuleSheaf
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
section
variable (X : Scheme.{u})

/-- Restriction of a global regular function to an open subset. -/
noncomputable def regularFunctionRestrict (U : X.Opens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom

lemma regularFunctionRestrict_trans {U V : X.Opens} (h : op U ⟶ op V) (r : Γ(X, ⊤)) :
    X.presheaf.map h (regularFunctionRestrict X U r) = regularFunctionRestrict X V r := by
  change (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫ X.presheaf.map h) r = _
  rw [← X.presheaf.map_comp]
  rfl

end
section
variable {X Y : Scheme.{u}} (f : Y ⟶ X) (ι : Type)

/-- Pull back tuples of regular functions along an actual scheme morphism. -/
noncomputable def coordinateModuleSheafPull :
    coordinateModuleSheaf X ι ⟶ (Scheme.Modules.pushforward f).obj (coordinateModuleSheaf Y ι) where
  val :=
    { app U := by
        change ModuleCat.of Γ(X, U.unop) (ι → Γ(X, U.unop)) ⟶
          (ModuleCat.restrictScalars (f.app U.unop).hom).obj
            (ModuleCat.of Γ(Y, f ⁻¹ᵁ U.unop) (ι → Γ(Y, f ⁻¹ᵁ U.unop)))
        exact ModuleCat.ofHom
          (Y := (ModuleCat.restrictScalars (f.app U.unop).hom).obj
            (ModuleCat.of Γ(Y, f ⁻¹ᵁ U.unop) (ι → Γ(Y, f ⁻¹ᵁ U.unop))))
          { toFun c i := f.app U.unop (c i)
            map_add' c d := by funext i; exact map_add (f.app U.unop).hom _ _
            map_smul' r c := by funext i; exact map_mul (f.app U.unop).hom _ _ }
      naturality := fun {U V} h => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro c
        change (fun i => f.app V.unop (X.presheaf.map h (c i))) =
          (fun i => Y.presheaf.map ((TopologicalSpace.Opens.map f.base).map h.unop).op
            (f.app U.unop (c i)))
        funext i
        exact CategoryTheory.congr_fun (f.c.naturality h) (c i) }

end
section
variable (X : Scheme.{u}) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A matrix of global regular functions defines an actual morphism of finite free coordinate sheaves. -/
noncomputable def coordinateModuleSheafMatrix (P : Matrix κ ι Γ(X, ⊤)) :
    coordinateModuleSheaf X ι ⟶ coordinateModuleSheaf X κ where
  val :=
    { app U := ModuleCat.ofHom (Matrix.toLin' (P.map (regularFunctionRestrict X U.unop)))
      naturality := fun {U V} h => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro c
        change (P.map (regularFunctionRestrict X V.unop)).mulVec ((X.presheaf.map h).hom ∘ c) =
          (X.presheaf.map h).hom ∘ (P.map (regularFunctionRestrict X U.unop)).mulVec c
        have he : (P.map (regularFunctionRestrict X U.unop)).map (X.presheaf.map h).hom =
            P.map (regularFunctionRestrict X V.unop) := by
          funext i j
          exact regularFunctionRestrict_trans X h (P i j)
        rw [← he]
        funext i
        exact (RingHom.map_mulVec (X.presheaf.map h).hom _ c i).symm }

end
end PfaffianDescent
