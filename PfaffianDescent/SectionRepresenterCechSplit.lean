import PfaffianDescent.SectionRepresenterCech
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology

/-!
# Split section-representer Cech augmentations

A chosen member of a finite family over a terminal object gives an extra
degeneracy of its Cech nerve.  After applying section representers, the
resulting augmented alternating chain complex is exact in positive degrees,
and its degree-zero augmentation is exact and epimorphic.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace PfaffianDescent

universe u

variable {C : Type u} [SmallCategory C] [HasFiniteProducts C]
variable {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A chosen member of the family over the terminal object contracts the
section-representer Cech augmentation. -/
noncomputable def sectionRepresenterCechExtraDegeneracy
    {ι : Type u} (U : ι → C) (T : C) (hT : IsTerminal T)
    {i₀ : ι} (d : T ⟶ U i₀) :
    (sectionRepresenterCechAugmented R U T hT).ExtraDegeneracy :=
  ((FormalCoproduct.mk ι U).extraDegeneracyCech hT d).map
    (sectionRepresenterFormalCoproductFunctor R)

/-- The augmentation from degree zero of the section-representer Cech chain. -/
noncomputable def sectionRepresenterCechAugmentation
    {ι : Type u} (U : ι → C) (T : C) (hT : IsTerminal T) :
    (sectionRepresenterCechChain R U).X 0 ⟶
      (sectionRepresenterCechAugmented R U T hT).right :=
  (sectionRepresenterCechAugmented R U T hT).hom.app (op ⦋0⦌)

set_option backward.isDefEq.respectTransparency false in
lemma sectionRepresenterCech_d_one_zero_comp_augmentation
    {ι : Type u} (U : ι → C) (T : C) (hT : IsTerminal T) :
    (sectionRepresenterCechChain R U).d 1 0 ≫
        sectionRepresenterCechAugmentation R U T hT = 0 := by
  let X := sectionRepresenterCechAugmented R U T hT
  change (AlgebraicTopology.AlternatingFaceMapComplex.obj X.left).d 1 0 ≫
      X.hom.app (op ⦋0⦌) = 0
  have h := ((AlgebraicTopology.AlternatingFaceMapComplex.ε.app X).comm 1 0).symm
  simp only [AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero,
    AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_succ,
    comp_zero, zero_comp] at h
  exact h

/-- A split Cech augmentation is exact in every positive chain degree. -/
lemma sectionRepresenterCechChain_exactAt_succ_of_split
    {ι : Type u} (U : ι → C) (T : C) (hT : IsTerminal T)
    {i₀ : ι} (d : T ⟶ U i₀) (n : ℕ) :
    (sectionRepresenterCechChain R U).ExactAt (n + 1) := by
  let X := sectionRepresenterCechAugmented R U T hT
  let ed : X.ExtraDegeneracy := sectionRepresenterCechExtraDegeneracy R U T hT d
  let e := ed.homotopyEquiv
  haveI : QuasiIsoAt e.hom (n + 1) := e.quasiIsoAt_hom (n + 1)
  have ht : ((ChainComplex.single₀ (SheafOfModules R)).obj X.right).ExactAt (n + 1) :=
    ChainComplex.exactAt_succ_single_obj X.right n
  change (AlgebraicTopology.AlternatingFaceMapComplex.obj X.left).ExactAt (n + 1)
  exact (exactAt_iff_of_quasiIsoAt e.hom (n + 1)).mpr ht

set_option backward.isDefEq.respectTransparency false in
/-- At degree zero, a split Cech augmentation is exact and epimorphic. -/
lemma sectionRepresenterCech_augmentation_exact_and_epi_of_split
    {ι : Type u} (U : ι → C) (T : C) (hT : IsTerminal T)
    {i₀ : ι} (d : T ⟶ U i₀) :
    (ShortComplex.mk
      ((sectionRepresenterCechChain R U).d 1 0)
      (sectionRepresenterCechAugmentation R U T hT)
      (sectionRepresenterCech_d_one_zero_comp_augmentation R U T hT)).Exact ∧
      Epi (sectionRepresenterCechAugmentation R U T hT) := by
  let X := sectionRepresenterCechAugmented R U T hT
  let ed : X.ExtraDegeneracy := sectionRepresenterCechExtraDegeneracy R U T hT d
  let e := ed.homotopyEquiv
  have hq0 : QuasiIsoAt e.hom 0 := e.quasiIsoAt_hom 0
  have hq : ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor'
        (SheafOfModules R) (ComplexShape.down ℕ) 1 0 0).map e.hom) :=
    (ChainComplex.quasiIsoAt₀_iff e.hom).mp hq0
  have hpair := (ShortComplex.quasiIso_iff_of_zeros'
    ((HomologicalComplex.shortComplexFunctor'
      (SheafOfModules R) (ComplexShape.down ℕ) 1 0 0).map e.hom)
    (by simp) (by simp) (by simp)).mp hq
  exact hpair

set_option backward.isDefEq.respectTransparency false in
lemma sectionRepresenterFormalCoproductFunctor_ι_map
    (X Y : FormalCoproduct.{u} C) (q : X ⟶ Y) (i : X.I) :
    Sigma.ι (fun j : X.I => (sectionRepresenterFunctor R).obj (X.obj j)) i ≫
        (sectionRepresenterFormalCoproductFunctor R).map q =
      (sectionRepresenterFunctor R).map (q.φ i) ≫
        Sigma.ι (fun j : Y.I => (sectionRepresenterFunctor R).obj (Y.obj j)) (q.f i) := by
  dsimp [sectionRepresenterFormalCoproductFunctor,
    CategoryTheory.Limits.FormalCoproduct.eval]
  rw [Sigma.ι_desc]
  rfl

end PfaffianDescent
