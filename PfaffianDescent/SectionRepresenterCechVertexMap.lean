import PfaffianDescent.SectionRepresenterScalar

/-!
# Vertex maps and their Cech boundaries

A morphism on each cover member defines a degree-zero map out of the
section-representer Cech chain. Its first boundary on an ordered overlap
is the second vertex restriction minus the first.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology

namespace PfaffianDescent

universe u

variable {C : Type u} [SmallCategory C] [HasFiniteProducts C]
variable {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Assemble morphisms from the cover members into a Cech degree-zero map. -/
def sectionRepresenterCechVertexMap {ι : Type u} (U : ι → C)
    (M : SheafOfModules.{u} R) (v : ∀ i, sectionRepresenter R (U i) ⟶ M) :
    (sectionRepresenterCechChain R U).X 0 ⟶ M :=
  Sigma.desc (fun f : Fin 1 → ι =>
    (sectionRepresenterFunctor R).map (Pi.π (fun k : Fin 1 => U (f k)) 0) ≫ v (f 0))

set_option backward.isDefEq.respectTransparency false in
theorem sectionRepresenterCechVertexMap_component
    {ι : Type u} (U : ι → C) (M : SheafOfModules.{u} R)
    (v : ∀ i, sectionRepresenter R (U i) ⟶ M) (f : Fin 1 → ι) :
    Sigma.ι (fun g : Fin 1 → ι =>
        sectionRepresenter R (∏ᶜ fun k : Fin 1 => U (g k))) f ≫
        sectionRepresenterCechVertexMap R U M v =
      (sectionRepresenterFunctor R).map (Pi.π (fun k : Fin 1 => U (f k)) 0) ≫
        v (f 0) := by
  exact Sigma.ι_desc _ _

set_option backward.isDefEq.respectTransparency false in
theorem sectionRepresenterCechVertexMap_face_component
    {ι : Type u} (U : ι → C) (M : SheafOfModules.{u} R)
    (v : ∀ i, sectionRepresenter R (U i) ⟶ M)
    (f : Fin 2 → ι) (i : Fin 2) :
    Sigma.ι (fun g : Fin 2 → ι =>
        sectionRepresenter R (∏ᶜ fun k : Fin 2 => U (g k))) f ≫
      (sectionRepresenterCechSimplicial R U).δ i ≫
        sectionRepresenterCechVertexMap R U M v =
      (sectionRepresenterFunctor R).map
        (Pi.π (fun k : Fin 2 => U (f k)) (i.succAbove 0)) ≫
        v (f (i.succAbove 0)) := by
  let E := (FormalCoproduct.mk _ U).cech
  let d := E.map (SimplexCategory.δ i).op
  change Sigma.ι (fun g : (E.obj (op ⦋1⦌)).I =>
      (sectionRepresenterFunctor R).obj ((E.obj (op ⦋1⦌)).obj g)) f ≫
      (sectionRepresenterFormalCoproductFunctor R).map d ≫
        sectionRepresenterCechVertexMap R U M v = _
  rw [← Category.assoc, sectionRepresenterFormalCoproductFunctor_ι_map,
    Category.assoc]
  change (sectionRepresenterFunctor R).map
      (Pi.lift (fun k : Fin 1 => Pi.π (fun a : Fin 2 => U (f a)) (i.succAbove k))) ≫
      (Sigma.ι (fun g : Fin 1 → ι =>
        sectionRepresenter R (∏ᶜ fun k : Fin 1 => U (g k)))
        (fun k => f (i.succAbove k)) ≫ sectionRepresenterCechVertexMap R U M v) = _
  rw [sectionRepresenterCechVertexMap_component, ← Category.assoc, ← Functor.map_comp,
    Pi.lift_π]

set_option backward.isDefEq.respectTransparency false in
/-- The first chain differential gives exactly the signed overlap boundary. -/
theorem sectionRepresenterCechVertexMap_boundary_component
    {ι : Type u} (U : ι → C) (M : SheafOfModules.{u} R)
    (v : ∀ i, sectionRepresenter R (U i) ⟶ M) (f : Fin 2 → ι) :
    Sigma.ι (fun g : Fin 2 → ι =>
        sectionRepresenter R (∏ᶜ fun k : Fin 2 => U (g k))) f ≫
      (sectionRepresenterCechChain R U).d 1 0 ≫
        sectionRepresenterCechVertexMap R U M v =
      (sectionRepresenterFunctor R).map (Pi.π (fun k : Fin 2 => U (f k)) 1) ≫ v (f 1) -
        (sectionRepresenterFunctor R).map (Pi.π (fun k : Fin 2 => U (f k)) 0) ≫ v (f 0) := by
  have hd : (sectionRepresenterCechChain R U).d 1 0 =
      (sectionRepresenterCechSimplicial R U).δ (0 : Fin 2) -
        (sectionRepresenterCechSimplicial R U).δ (1 : Fin 2) := by
    change AlternatingFaceMapComplex.objD (sectionRepresenterCechSimplicial R U) 0 = _
    unfold AlternatingFaceMapComplex.objD
    change (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) •
      (sectionRepresenterCechSimplicial R U).δ i) = _
    rw [Fin.sum_univ_two]
    simp [sub_eq_add_neg]
  rw [hd, Preadditive.sub_comp, Preadditive.comp_sub]
  rw [sectionRepresenterCechVertexMap_face_component,
    sectionRepresenterCechVertexMap_face_component]
  rfl

end PfaffianDescent
