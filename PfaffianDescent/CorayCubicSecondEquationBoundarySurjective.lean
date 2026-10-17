import PfaffianDescent.CorayCubicSecondEquationTwoBoundary

/-! SOURCE ONLY / UNVERIFIED161. Genuine surjectivity of the first
q-boundary and the n=1 two-boundary map. All actual vanishings and sequences
are derived from the original smooth cubic. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K
local notation "P" => Proj PS
local notation "piP" => ambientToBase (R := K) (σ := Fin 4)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual ambient H2 of the cubic zero twist vanishes: the genuine cubic
boundary injects it into the already computed zero P3 H3(O(-3)). -/
theorem smoothCubic_zeroTwistPushforward_cohomology_two_subsingleton
    [HasExt.{u} (P).Modules]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    Subsingleton (schemeModuleCohomology P
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (sheafOfModules (grading (equationIdeal p hp)) 0)) 2) := by
  letI : Linear K (P).Modules := schemeModulesLinearOver piP
  letI : Subsingleton (schemeModuleCohomology P (sheafOfModules PS (0 + 3)) 3) :=
    p3NegativeTwist_cohomology_three_subsingleton_of_lt_four K 3 (by omega)
  exact (cubicAmbient_boundaryTwoLinearMap_injective p hp hp0 0).subsingleton

/-- The actual first q-boundary is onto. Its next middle term is the
actual cubic zero twist, whose H2 vanishing was just constructed. -/
theorem cubicSecondEquation_boundaryOneLinearMap_surjective
    [HasExt.{u} (P).Modules]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    Function.Surjective (cubicSecondEquation_boundaryOneLinearMap p q hp hp0 n hq hnot) := by
  letI : Linear K (P).Modules := schemeModulesLinearOver piP
  let T := (homogeneousRestrictionSequence (grading (equationIdeal p hp))
    (cubicSecondEquationHomogeneous p q hp n hq) 0).map
      (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp))
  have hT : T.ShortExact :=
    cubicSecondEquation_pushforwardRestrictionSequence_shortExact p q hp hp0 n hq hnot 0
  letI : Subsingleton (schemeModuleCohomology P T.X₂ 2) :=
    smoothCubic_zeroTwistPushforward_cohomology_two_subsingleton p hp hp0
  have hBoundary : Function.Surjective
      (schemeModuleRestrictionConnectingLinearMapOver piP T hT 1) := by
    intro z
    have hz : z.comp (Ext.mk₀ T.f) (add_zero 2) = 0 := Subsingleton.elim _ _
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
      (show (P).Modules from SheafOfModules.unit (P).ringCatSheaf) hT z hz rfl
    exact ⟨y, hy⟩
  exact (schemeModuleCohomologyIsoLinearEquivOver piP
      (cubicSecondEquation_zeroLeftIso p hp n) 2).surjective.comp hBoundary

/-- Genuine n=1 surjectivity of the SAME actual two-boundary composite,
using the already accepted P3 O(-1) top vanishing for the second boundary. -/
theorem cubicSecondEquation_twoBoundaryLinearMap_surjective_degree_one
    [HasExt.{u} (P).Modules]
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1)
    (hnot : l ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    Function.Surjective (cubicSecondEquation_twoBoundaryLinearMap p l hp hp0 1 hl hnot) := by
  letI : Linear K (P).Modules := schemeModulesLinearOver piP
  exact (cubicAmbient_boundaryTwoLinearMap_surjective_of_lt_four
      p hp hp0 1 (by omega)).comp
    (cubicSecondEquation_boundaryOneLinearMap_surjective p l hp hp0 1 hl hnot)

end PfaffianDescent.Coray
