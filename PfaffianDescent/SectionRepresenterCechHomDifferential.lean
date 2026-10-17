import PfaffianDescent.SectionRepresenterCechSplit

/-!
# Hom differentials for the section-representer Cech chain

The Yoneda equivalence identifies morphisms from a term of the
section-representer Cech chain with tuples of sections.  This file records
that, under this identification, precomposition by a face map is restriction
of sections, and precomposition by the chain differential is the alternating
sum of these restrictions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open AlgebraicTopology

namespace PfaffianDescent

universe u

variable {C : Type u} [SmallCategory C] [HasFiniteProducts C]
variable {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

set_option backward.isDefEq.respectTransparency false in
/-- Under the section-representer equivalence, precomposition by a Cech face
is restriction along the corresponding map of intersections. -/
lemma sectionRepresenterCechHomEquivPi_face
    {ι : Type u} (U : ι → C) (M : SheafOfModules.{u} R)
    (n : ℕ) (i : Fin (n + 2))
    (h : (sectionRepresenterCechChain R U).X n ⟶ M)
    (f : Fin (n + 2) → ι) :
    let E := (FormalCoproduct.mk _ U).cech
    sectionRepresenterCechHomEquivPi R U M (n + 1)
        ((sectionRepresenterCechSimplicial R U).δ i ≫ h) f =
      M.val.map ((E.map (SimplexCategory.δ i).op).φ f).op
        (sectionRepresenterCechHomEquivPi R U M n h
          ((E.map (SimplexCategory.δ i).op).f f)) := by
  let E := (FormalCoproduct.mk ι U).cech
  let q := E.map (SimplexCategory.δ i).op
  change sectionRepresenterHomEquiv R
      ((E.obj (op (SimplexCategory.mk (n + 1)))).obj f) M
      (Sigma.ι (fun j : (E.obj (op (SimplexCategory.mk (n + 1)))).I =>
        (sectionRepresenterFunctor R).obj
          ((E.obj (op (SimplexCategory.mk (n + 1)))).obj j)) f ≫
        ((sectionRepresenterFormalCoproductFunctor R).map q ≫ h)) = _
  rw [← Category.assoc,
    sectionRepresenterFormalCoproductFunctor_ι_map R
      (E.obj (op (SimplexCategory.mk (n + 1))))
      (E.obj (op (SimplexCategory.mk n))) q f,
    Category.assoc]
  exact sectionRepresenterHomEquiv_precomp R (q.φ f) M
    (Sigma.ι (fun j : (E.obj (op (SimplexCategory.mk n))).I =>
      (sectionRepresenterFunctor R).obj
        ((E.obj (op (SimplexCategory.mk n))).obj j)) (q.f f) ≫ h)

set_option backward.isDefEq.respectTransparency false in
/-- The section-representer Yoneda equivalence as an additive equivalence. -/
noncomputable def sectionRepresenterHomAddEquiv
    (X : C) (M : SheafOfModules.{u} R) :
    (sectionRepresenter R X ⟶ M) ≃+ M.val.obj (op X) :=
  { toEquiv := sectionRepresenterHomEquiv R X M
    map_add' := by intros; rfl }

set_option backward.isDefEq.respectTransparency false in
/-- The tuple-valued Cech Yoneda equivalence as an additive equivalence. -/
noncomputable def sectionRepresenterCechHomAddEquivPi
    {ι : Type u} (U : ι → C) (M : SheafOfModules.{u} R) (n : ℕ) :
    ((sectionRepresenterCechChain R U).X n ⟶ M) ≃+
      (∀ f : Fin (n + 1) → ι,
        M.val.obj (op (∏ᶜ fun i : Fin (n + 1) => U (f i)))) :=
  { toEquiv := sectionRepresenterCechHomEquivPi R U M n
    map_add' := by
      intro f g
      funext j
      rfl }

set_option backward.isDefEq.respectTransparency false in
/-- Under the tuple-valued Cech Yoneda equivalence, precomposition by the
chain differential is the alternating sum of restrictions along the faces. -/
lemma sectionRepresenterCechHomEquivPi_d
    {ι : Type u} (U : ι → C) (M : SheafOfModules.{u} R)
    (n : ℕ) (h : (sectionRepresenterCechChain R U).X n ⟶ M)
    (f : Fin (n + 2) → ι) :
    let E := (FormalCoproduct.mk _ U).cech
    sectionRepresenterCechHomEquivPi R U M (n + 1)
        ((sectionRepresenterCechChain R U).d (n + 1) n ≫ h) f =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        M.val.map ((E.map (SimplexCategory.δ i).op).φ f).op
          (sectionRepresenterCechHomEquivPi R U M n h
            ((E.map (SimplexCategory.δ i).op).f f)) := by
  dsimp only
  rw [show (sectionRepresenterCechChain R U).d (n + 1) n =
      AlternatingFaceMapComplex.objD
        (sectionRepresenterCechSimplicial R U) n from
    alternatingFaceMapComplex_obj_d
      (sectionRepresenterCechSimplicial R U) n]
  rw [AlternatingFaceMapComplex.objD, Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp]
  change (sectionRepresenterCechHomAddEquivPi R U M (n + 1))
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((sectionRepresenterCechSimplicial R U).δ i ≫ h)) f = _
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_zsmul]
  exact congrArg (((-1 : ℤ) ^ (i : ℕ)) • ·)
    (sectionRepresenterCechHomEquivPi_face R U M n i h f)

end PfaffianDescent
