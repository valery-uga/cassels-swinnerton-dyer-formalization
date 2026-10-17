import PfaffianDescent.SectionRepresenterCechHomDifferential

/-! # The degree-one Cech boundary on actual overlap morphisms -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology
namespace PfaffianDescent
universe u
variable {C : Type u} [SmallCategory C] [HasFiniteProducts C]
  {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

set_option backward.isDefEq.respectTransparency false in
/-- On a triple intersection, precomposition by a face is the actual
restriction morphism followed by the corresponding pair component. -/
theorem sectionRepresenterCech_degreeOne_face_component
    {ι : Type u} (U : ι → C) (M : SheafOfModules.{u} R)
    (a : (sectionRepresenterCechChain R U).X 1 ⟶ M)
    (s : Fin 3 → ι) (i : Fin 3) :
    let E := (FormalCoproduct.mk ι U).cech
    let d := E.map (SimplexCategory.δ i).op
    Sigma.ι (fun g : Fin 3 → ι =>
        sectionRepresenter R (∏ᶜ fun k : Fin 3 => U (g k))) s ≫
      (sectionRepresenterCechSimplicial R U).δ i ≫ a =
      (sectionRepresenterFunctor R).map (d.φ s) ≫
        Sigma.ι (fun g : Fin 2 → ι =>
          sectionRepresenter R (∏ᶜ fun k : Fin 2 => U (g k))) (d.f s) ≫ a := by
  dsimp only
  let E := (FormalCoproduct.mk ι U).cech
  let d := E.map (SimplexCategory.δ i).op
  change Sigma.ι (fun g : (E.obj (op ⦋2⦌)).I =>
      (sectionRepresenterFunctor R).obj ((E.obj (op ⦋2⦌)).obj g)) s ≫
      (sectionRepresenterFormalCoproductFunctor R).map d ≫ a = _
  rw [← Category.assoc, sectionRepresenterFormalCoproductFunctor_ι_map,
    Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual second differential on one triple component is the signed
sum of the three actual restricted pair-component morphisms. -/
theorem sectionRepresenterCech_degreeOne_boundary_component
    {ι : Type u} (U : ι → C) (M : SheafOfModules.{u} R)
    (a : (sectionRepresenterCechChain R U).X 1 ⟶ M)
    (s : Fin 3 → ι) :
    let E := (FormalCoproduct.mk ι U).cech
    Sigma.ι (fun g : Fin 3 → ι =>
        sectionRepresenter R (∏ᶜ fun k : Fin 3 => U (g k))) s ≫
      (sectionRepresenterCechChain R U).d 2 1 ≫ a =
      ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) •
        ((sectionRepresenterFunctor R).map ((E.map (SimplexCategory.δ i).op).φ s) ≫
          Sigma.ι (fun g : Fin 2 → ι =>
            sectionRepresenter R (∏ᶜ fun k : Fin 2 => U (g k)))
              ((E.map (SimplexCategory.δ i).op).f s) ≫ a) := by
  dsimp only
  let t : sectionRepresenter R (∏ᶜ fun k : Fin 3 => U (s k)) ⟶
      (sectionRepresenterCechChain R U).X 2 :=
    Sigma.ι (fun g : Fin 3 → ι => sectionRepresenter R (∏ᶜ fun k : Fin 3 => U (g k))) s
  let d : Fin 3 → ((sectionRepresenterCechChain R U).X 2 ⟶
      (sectionRepresenterCechChain R U).X 1) :=
    fun i => (sectionRepresenterCechSimplicial R U).δ i
  let rhs : Fin 3 → (sectionRepresenter R (∏ᶜ fun k : Fin 3 => U (s k)) ⟶ M) :=
    fun i => (sectionRepresenterFunctor R).map
        (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ i).op).φ s) ≫
      Sigma.ι (fun g : Fin 2 → ι => sectionRepresenter R (∏ᶜ fun k : Fin 2 => U (g k)))
        (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ i).op).f s) ≫ a
  have hd : (sectionRepresenterCechChain R U).d 2 1 =
      ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • d i := by
    change AlternatingFaceMapComplex.objD (sectionRepresenterCechSimplicial R U) 1 = _
    rfl
  change t ≫ (sectionRepresenterCechChain R U).d 2 1 ≫ a =
    ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • rhs i
  rw [hd, Preadditive.sum_comp, Preadditive.comp_sum]
  simp_rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun v => (-1 : ℤ) ^ (i : ℕ) • v)
    (sectionRepresenterCech_degreeOne_face_component R U M a s i)

end PfaffianDescent
