import PfaffianDescent.RelativeOpenFiniteFlatFamilyTransport315

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option autoImplicit false

/-- Commuting physical/relative ambient isomorphisms preserve the entire
pushed chart ideal. The actual finite-family composite supplies closedness. -/
theorem originalPhysicalChartIdealPush_comapAmbientIso001
    {Y Y' X X' : Scheme.{u}} (e : Y ≅ Y') (f : X ≅ X')
    (k : Y ⟶ X) (k' : Y' ⟶ X')
    (h : e.hom ≫ k' = k ≫ f.hom) (Q : Y.IdealSheafData)
    [IsClosedImmersion (Q.subschemeι ≫ k)] :
    ((Q.comap e.inv).map k').comap f.hom = Q.map k := by
  have hinv : e.inv ≫ k = k' ≫ f.inv := by
    apply (cancel_mono f.hom).mp
    calc
      (e.inv ≫ k) ≫ f.hom = e.inv ≫ (k ≫ f.hom) := Category.assoc _ _ _
      _ = e.inv ≫ (e.hom ≫ k') := congrArg (fun a => e.inv ≫ a) h.symm
      _ = k' := e.inv_hom_id_assoc k'
      _ = (k' ≫ f.inv) ≫ f.hom := by simp only [Category.assoc, f.inv_hom_id, Category.comp_id]
  have H : IsPullback e.inv k' k f.inv :=
    IsPullback.of_horiz_isIso_mono ⟨hinv⟩
  have hMap := nativeEmbeddedIdealMapComap315 e.inv k' k f.inv H Q
  exact (congrArg (fun J : X'.IdealSheafData => J.comap f.hom) hMap).trans
    (((Q.map k).comap_comp f.hom f.inv).symm.trans
      ((congrArg (Q.map k).comap f.hom_inv_id).trans (Q.map k).comap_id))

end PfaffianDescent
end
