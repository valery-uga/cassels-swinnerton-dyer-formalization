import PfaffianDescent.CubicPointTraceFieldBaseChangeModule
import PfaffianDescent.BundleSectionZeroLocus

/-! # Actual coefficients of sheafified affine unit endomorphisms -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PfaffianDescent.BundleSectionZeroLocus
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Sheafifying an affine unit-module endomorphism gives multiplication by
its actual affine coordinate coefficient. -/
theorem cubicPointTraceFieldBaseChangeAffineEndomorphism_eq_regularFunction
    {R : Type u} [CommRing R] (m : ModuleCat.of R R ⟶ ModuleCat.of R R) :
    (affineGlobalSectionsUnitTildeIso (A := R)).inv ≫
      (tilde.functor (.of R)).map m ≫
        (affineGlobalSectionsUnitTildeIso (A := R)).hom =
      unitEndomorphismOfRegularFunction (affineFunctionHom (𝟙 (Spec (.of R))) (m 1)) := by
  let F := tilde.functor (.of R)
  let G := moduleSpecΓFunctor (R := .of R)
  let O := SheafOfModules.unit (Spec (.of R)).ringCatSheaf
  let e := (affineGlobalSectionsUnitLinearEquiv (A := R)).toModuleIso
  let c := unitEndomorphismOfRegularFunction (affineFunctionHom (𝟙 (Spec (.of R))) (m 1))
  let u := affineGlobalSectionsUnitTildeIso (A := R)
  have hgamma : e.inv ≫ G.map c ≫ e.hom = m := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    have hv : (c.val.app (Opposite.op ⊤)).hom (1 : Γ(Spec (.of R), ⊤)) =
        affineFunctionHom (𝟙 (Spec (.of R))) (m 1) :=
      unitEndomorphismValue_ofRegularFunction _
    change (Scheme.ΓSpecIso (.of R)).hom.hom
      ((c.val.app (Opposite.op ⊤)).hom ((Scheme.ΓSpecIso (.of R)).inv.hom 1)) = m 1
    rw [map_one, hv]
    change (Scheme.ΓSpecIso (.of R)).hom.hom
      ((Scheme.ΓSpecIso (.of R)).inv.hom (m 1)) = m 1
    exact (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.apply_symm_apply _
  have hgamma' : m ≫ e.inv = e.inv ≫ G.map c := by
    rw [← hgamma]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hnat : F.map (G.map c) ≫ Scheme.Modules.fromTildeΓ (R := .of R) O =
      Scheme.Modules.fromTildeΓ (R := .of R) O ≫ c :=
    (tilde.adjunction (R := .of R)).counit.naturality c
  apply (cancel_epi u.hom).mp
  change u.hom ≫ (u.inv ≫ F.map m ≫ u.hom) = u.hom ≫ c
  simp only [Iso.hom_inv_id_assoc]
  change F.map m ≫ (F.map e.inv ≫ Scheme.Modules.fromTildeΓ (R := .of R) O) =
    (F.map e.inv ≫ Scheme.Modules.fromTildeΓ (R := .of R) O) ≫ c
  rw [← Category.assoc, ← F.map_comp, hgamma', F.map_comp, Category.assoc]
  exact (congrArg (fun t => F.map e.inv ≫ t) hnat).trans
    (Category.assoc _ _ _).symm

end PfaffianDescent
