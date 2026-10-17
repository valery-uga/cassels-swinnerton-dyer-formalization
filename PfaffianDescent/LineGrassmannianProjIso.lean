import PfaffianDescent.LineProjGrassmannianCompatibility

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
section
variable (K : Type u) [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I₀" => (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K))

/-- The two standard Proj opens form the source cover for the comparison. -/
noncomputable def lineProjOpenCover : (projectiveLineProj K).OpenCover :=
  (coordinateOpenCover I₀).openCover

/-- Each standard chart of the projective line is affine. -/
instance lineProjOpenCover_affine (i : (lineProjOpenCover K).I₀) :
    IsAffine ((lineProjOpenCover K).X i) := by
  change IsAffine (Spec _)
  infer_instance

lemma lineProjToGrassmannian_gluing (b c : (lineProjOpenCover K).I₀) :
    pullback.fst ((lineProjOpenCover K).f b) ((lineProjOpenCover K).f c) ≫
        ((lineGrassmannianProjChartIso K b).hom ≫ grassmannianChartι K (lineChartPermutation b)) =
      pullback.snd ((lineProjOpenCover K).f b) ((lineProjOpenCover K).f c) ≫
        ((lineGrassmannianProjChartIso K c).hom ≫ grassmannianChartι K (lineChartPermutation c)) := by
  exact (Category.assoc _ _ _).symm.trans
    ((lineProjToGrassmannian_compatible K b c _ _ (pullback.condition)).trans (Category.assoc _ _ _))

/-- The global morphism from the standard Proj projective line to the line Grassmannian. -/
noncomputable def lineProjToGrassmannian : projectiveLineProj K ⟶ grassmannianScheme K 1 1 :=
  (lineProjOpenCover K).glueMorphisms
    (fun b => (lineGrassmannianProjChartIso K b).hom ≫ grassmannianChartι K (lineChartPermutation b))
    (lineProjToGrassmannian_gluing K)

lemma lineProjChart_toGrassmannian (b : Bool) :
    chartι I₀ b ≫ lineProjToGrassmannian K =
      (lineGrassmannianProjChartIso K b).hom ≫ grassmannianChartι K (lineChartPermutation b) :=
  (lineProjOpenCover K).ι_glueMorphisms _ (lineProjToGrassmannian_gluing K) b

lemma lineGrassmannianToProj_gluing (b c : (projectiveLineOpenCover K).I₀) :
    pullback.fst ((projectiveLineOpenCover K).f b) ((projectiveLineOpenCover K).f c) ≫
        ((lineGrassmannianProjChartIso K b.down).inv ≫ chartι I₀ b.down) =
      pullback.snd ((projectiveLineOpenCover K).f b) ((projectiveLineOpenCover K).f c) ≫
        ((lineGrassmannianProjChartIso K c.down).inv ≫ chartι I₀ c.down) := by
  exact (Category.assoc _ _ _).symm.trans
    ((lineGrassmannianToProj_compatible K b.down c.down _ _ (pullback.condition)).trans (Category.assoc _ _ _))

/-- The global inverse morphism to the standard Proj projective line. -/
noncomputable def lineGrassmannianToProj : grassmannianScheme K 1 1 ⟶ projectiveLineProj K :=
  (projectiveLineOpenCover K).glueMorphisms
    (fun b => (lineGrassmannianProjChartIso K b.down).inv ≫ chartι I₀ b.down)
    (lineGrassmannianToProj_gluing K)

lemma lineGrassmannianChart_toProj (b : Bool) :
    grassmannianChartι K (lineChartPermutation b) ≫ lineGrassmannianToProj K =
      (lineGrassmannianProjChartIso K b).inv ≫ chartι I₀ b :=
  (projectiveLineOpenCover K).ι_glueMorphisms _ (lineGrassmannianToProj_gluing K) ⟨b⟩

lemma lineGrassmannianToProj_toGrassmannian :
    lineGrassmannianToProj K ≫ lineProjToGrassmannian K = 𝟙 (grassmannianScheme K 1 1) := by
  apply (projectiveLineOpenCover K).hom_ext
  intro b
  change ULift.{u} Bool at b
  let e := lineGrassmannianProjChartIso K b.down
  let j := grassmannianChartι K (lineChartPermutation b.down)
  exact (Category.assoc j (lineGrassmannianToProj K) (lineProjToGrassmannian K)).symm.trans
    ((congrArg (fun q => q ≫ lineProjToGrassmannian K) (lineGrassmannianChart_toProj K b.down)).trans
      ((Category.assoc e.inv (chartι I₀ b.down) (lineProjToGrassmannian K)).trans
        ((congrArg (fun q => e.inv ≫ q) (lineProjChart_toGrassmannian K b.down)).trans
          ((e.inv_hom_id_assoc j).trans (Category.comp_id j).symm))))

lemma lineProjToGrassmannian_toProj :
    lineProjToGrassmannian K ≫ lineGrassmannianToProj K = 𝟙 (projectiveLineProj K) := by
  apply (lineProjOpenCover K).hom_ext
  intro b
  change Bool at b
  let e := lineGrassmannianProjChartIso K b
  let j := chartι I₀ b
  exact (Category.assoc j (lineProjToGrassmannian K) (lineGrassmannianToProj K)).symm.trans
    ((congrArg (fun q => q ≫ lineGrassmannianToProj K) (lineProjChart_toGrassmannian K b)).trans
      ((Category.assoc e.hom (grassmannianChartι K (lineChartPermutation b)) (lineGrassmannianToProj K)).trans
        ((congrArg (fun q => e.hom ≫ q) (lineGrassmannianChart_toProj K b)).trans
          ((e.hom_inv_id_assoc j).trans (Category.comp_id j).symm))))

/-- The line Grassmannian is the standard Proj projective line, as an actual scheme isomorphism. -/
noncomputable def lineGrassmannianProjIso : grassmannianScheme K 1 1 ≅ projectiveLineProj K where
  hom := lineGrassmannianToProj K
  inv := lineProjToGrassmannian K
  hom_inv_id := lineGrassmannianToProj_toGrassmannian K
  inv_hom_id := lineProjToGrassmannian_toProj K

lemma lineGrassmannianProjIso_toBase :
    (lineGrassmannianProjIso K).hom ≫ projectiveLineProjToBase K = grassmannianToBase K 1 1 := by
  apply (projectiveLineOpenCover K).hom_ext
  intro b
  change ULift.{u} Bool at b
  let e := lineGrassmannianProjChartIso K b.down
  let j := grassmannianChartι K (lineChartPermutation b.down)
  exact (Category.assoc j (lineGrassmannianToProj K) (projectiveLineProjToBase K)).symm.trans
    ((congrArg (fun q => q ≫ projectiveLineProjToBase K) (lineGrassmannianChart_toProj K b.down)).trans
      ((Category.assoc e.inv (chartι I₀ b.down) (projectiveLineProjToBase K)).trans
        ((congrArg (fun q => e.inv ≫ q) (lineGrassmannianProjChartIso_toBase K b.down).symm).trans
          ((e.inv_hom_id_assoc (grassmannianChartToBase K 1 1)).trans
            (grassmannianChartι_toBase K (lineChartPermutation b.down)).symm))))

end
end PfaffianDescent
