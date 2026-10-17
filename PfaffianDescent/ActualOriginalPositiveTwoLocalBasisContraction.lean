import PfaffianDescent.ActualOriginalPositiveTwoLocalBasisCoefficient
import PfaffianDescent.ActualPointLocalTensorUnitContraction

/- SOURCE ONLY / UNVERIFIED. Actual original O2 contraction on LOCAL
ideal/module generators. The coefficient is derived from the SAME actual
basis; no desired contraction/generator/source certificate is an input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma actualOriginalPositiveTwoLocalBasisContraction
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (M : (hypersurface p hp).Modules) (U : (hypersurface p hp).Opens)
    (hU : (hypersurface p hp).fromSpecResidueField P.1 ⁻¹ᵁ U = ⊤)
    (m : M.val.obj (op U)) :
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let T := positiveSheafOfModules (grading (equationIdeal p hp)) 2
    (moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))).map
      (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap q M T ≫
        (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj M)
          ((Scheme.Modules.pullback q).obj T)
          (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom)
      (actualPointLocalSectionClass q (schemeModuleTensor M T) U hU
        (actualModuleLocalTensorSection M T U m
          (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))) =
      actualPointLocalSectionClass q M U hU m := by
  dsimp only
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let L := (hypersurface p hp).residueField P.1
  let T := positiveSheafOfModules (grading (equationIdeal p hp)) 2
  let z : ((Scheme.Modules.pullback q).obj M).val.obj (op ⊤) :=
    actualPointLocalSectionClass q M U hU m
  have hc := actualPointLocalTensorUnitContraction q M T U hU
    (actualOriginalPositiveTwoPointTrivialization p hp P hP) m
    (actualOriginalPositiveTwoLocalBasisSection p hp P hP U)
  have hb := actualOriginalPositiveTwoLocalBasisCoefficient_one p hp P hP U hU
  exact hc.trans ((congrArg (fun r : Γ(Spec (.of L), ⊤) => r • z) hb).trans
    (one_smul _ z))

lemma actualOriginalPositiveTwoNativeChartBasisContraction
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (M : (hypersurface p hp).Modules) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι (equationIdeal p hp) C.index
    let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing (equationIdeal p hp) C.index))).Opens)
    let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f
      (Spec.map (CommRingCat.ofHom C.residue)) q C.factorization
    let T := positiveSheafOfModules (grading (equationIdeal p hp)) 2
    ∀ m : M.val.obj (op U),
      (moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))).map
        (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap q M T ≫
          (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj M)
            ((Scheme.Modules.pullback q).obj T)
            (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom)
        (actualPointLocalSectionClass q (schemeModuleTensor M T) U hU
          (actualModuleLocalTensorSection M T U m
            (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))) =
        actualPointLocalSectionClass q M U hU m := by
  dsimp only
  intro m
  exact actualOriginalPositiveTwoLocalBasisContraction p hp P hP M _ _ m

end PfaffianDescent
