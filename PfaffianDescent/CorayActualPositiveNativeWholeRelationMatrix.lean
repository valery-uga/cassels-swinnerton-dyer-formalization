import PfaffianDescent.CorayActualPositiveNativeWholeGeneratorMatrix

/-! Reapply the existing canonical frames to the whole relation matrix.
SOURCE ONLY UNVERIFIED. Literal maps and original scalar actions retained. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open ProjectiveNegativeTwist BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "A" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

private theorem thirdNaturalFrame_conjugation
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ E) (R : C ⥤ D) (P : D ⥤ E) (n : Q ≅ R ⋙ P)
    {M N : C} {M' N' : D} {M'' N'' : E}
    (a : R.obj M ≅ M') (b : R.obj N ≅ N')
    (u : P.obj M' ≅ M'') (v : P.obj N' ≅ N'')
    (f : M ⟶ N) (g : M' ⟶ N')
    (h : a.inv ≫ R.map f ≫ b.hom = g) :
    (n.app M ≪≫ P.mapIso a ≪≫ u).inv ≫ Q.map f ≫
      (n.app N ≪≫ P.mapIso b ≪≫ v).hom = u.inv ≫ P.map g ≫ v.hom := by
  have hn : (n.app M).inv ≫ Q.map f ≫ (n.app N).hom = P.map (R.map f) := by
    calc
      _ = (n.app M).inv ≫ (Q.map f ≫ (n.app N).hom) := rfl
      _ = (n.app M).inv ≫ ((n.app M).hom ≫ P.map (R.map f)) :=
        congrArg (fun k => (n.app M).inv ≫ k) (n.hom.naturality f)
      _ = _ := (n.app M).inv_hom_id_assoc _
  calc
    _ = u.inv ≫ P.map a.inv ≫
        ((n.app M).inv ≫ Q.map f ≫ (n.app N).hom) ≫ P.map b.hom ≫ v.hom := by
      simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
        Category.assoc]
    _ = u.inv ≫ P.map a.inv ≫ P.map (R.map f) ≫ P.map b.hom ≫ v.hom :=
      congrArg (fun k => u.inv ≫ P.map a.inv ≫ k ≫ P.map b.hom ≫ v.hom) hn
    _ = u.inv ≫ P.map (a.inv ≫ R.map f ≫ b.hom) ≫ v.hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := congrArg (fun k => u.inv ≫ P.map k ≫ v.hom) h

/-- The SAME arbitrary weighted relation map has its literal normalized
matrix under the canonical native away pullback and existing free frames. -/
theorem actualPositiveFiniteRelationMap_nativeWholeMatrix
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (d : ι → ℕ) (r : κ → ι → A) (e : κ → ℕ)
    (hr : ∀ a, ActualWeightedPolynomialHomogeneous d (e a) (r a))
    (m : ℕ) (he : ∀ a, e a ≤ m) (j : Fin 4) :
    (actualPositiveNativeWholeGeneratorFrame (K := K) j e m).inv ≫
      (Scheme.Modules.pullback
        (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))).map
          (actualPositiveFiniteRelationMap d r e hr m he) ≫
      (actualPositiveNativeWholeGeneratorFrame (K := K) j d m).hom =
      actualNormalizedSpecUnitRelationMatrix j r := by
  let U := Proj.basicOpen PS (X j)
  let z := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let Q := Scheme.Modules.pullback
    (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))
  let R := Scheme.Modules.restrictFunctor U.ι
  let P := Scheme.Modules.pullback z.inv
  let n := actualPositiveNativeChartRestrictionIso (K := K) j
  let a := actualRestrictedPositiveFiniteCoproductUnitIso (K := K) j U le_rfl e m
  let b := actualRestrictedPositiveFiniteCoproductUnitIso (K := K) j U le_rfl d m
  let u := actualCanonicalPullbackUnitCoproductIso z.inv κ
  let v := actualCanonicalPullbackUnitCoproductIso z.inv ι
  exact (thirdNaturalFrame_conjugation Q R P n a b u v
    (actualPositiveFiniteRelationMap d r e hr m he)
    (actualRestrictedPositiveUnitRelationMatrix j U le_rfl r)
    (actualPositiveFiniteRelationMap_restrictedWholeMatrix d r e hr m he j U le_rfl)).trans
      (actualRestrictedPositiveUnitRelationMatrix_basicOpenPullback j r)

end PfaffianDescent.Coray
