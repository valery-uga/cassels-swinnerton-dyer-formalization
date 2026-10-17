import Mathlib.AlgebraicGeometry.Gluing

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Ordinary compatible maps out of native Scheme gluing descend by its actual colimit. -/
def nativeSchemeGlueDataDesc300 (D : Scheme.GlueData.{u}) (Y : Scheme.{u})
    (g : ∀ i, D.U i ⟶ Y)
    (hg : ∀ i j, D.t i j ≫ D.f j i ≫ g j = D.f i j ≫ g i) : D.glued ⟶ Y :=
  Multicoequalizer.desc D.toGlueData.diagram Y g (fun ij => by
    rcases ij with ⟨i, j⟩
    change D.f i j ≫ g i = (D.t i j ≫ D.f j i) ≫ g j
    simpa only [Category.assoc] using (hg i j).symm)

lemma nativeSchemeGlueDataDesc_chart300 (D : Scheme.GlueData.{u}) (Y : Scheme.{u})
    (g : ∀ i, D.U i ⟶ Y)
    (hg : ∀ i j, D.t i j ≫ D.f j i ≫ g j = D.f i j ≫ g i) (i : D.J) :
    D.ι i ≫ nativeSchemeGlueDataDesc300 D Y g hg = g i :=
  Multicoequalizer.π_desc D.toGlueData.diagram Y g _ i

lemma nativeSchemeGlueData_hom_ext300 (D : Scheme.GlueData.{u}) {Y : Scheme.{u}}
    (f g : D.glued ⟶ Y) (h : ∀ i, D.ι i ≫ f = D.ι i ≫ g) : f = g :=
  Multicoequalizer.hom_ext D.toGlueData.diagram f g h

/-- Exact original pairwise presentation squares descend the original base morphisms. -/
lemma nativePairTransition_overBase300
    {C : Type*} [Category C] {X Y U V S : C}
    (eX : X ≅ U) (eY : Y ≅ V) (t : U ⟶ V) (a : X ⟶ Y)
    (bU : U ⟶ S) (bV : V ⟶ S) (bX : X ⟶ S) (bY : Y ⟶ S)
    (ht : eX.hom ≫ t = a ≫ eY.hom)
    (hx : eX.hom ≫ bU = bX) (hy : eY.hom ≫ bV = bY)
    (ha : a ≫ bY = bX) : t ≫ bV = bU := by
  apply (cancel_epi eX.hom).mp
  calc
    _ = a ≫ eY.hom ≫ bV := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ bV) ht
    _ = a ≫ bY := congrArg (fun f => a ≫ f) hy
    _ = bX := ha
    _ = _ := hx.symm

end PfaffianDescent
