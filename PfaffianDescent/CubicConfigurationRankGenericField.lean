import AllCharacteristics.GenericPointDominance
import AllCharacteristics.VoisinGenericCubicPoint

/-! The generic point of the actual rank chart is over the SAME unordered
generic configuration, with an internally constructed field embedding. -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicConfigurationRankChart_exists_genericFieldEmbedding
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    [hO : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left]
    [hB : IsIntegral (cubicConfigurationBase p hp n)]
    {A : Scheme.{u}} [IsIntegral A]
    (a : A ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left)
    [IsOpenImmersion a] :
    ∃ β : (cubicConfigurationBase p hp n).functionField →+*
        A.residueField (genericPoint A),
      Spec.map (CommRingCat.ofHom β) ≫
        (cubicConfigurationBase p hp n).fromSpecStalk
          (genericPoint (cubicConfigurationBase p hp n)) =
      (A.fromSpecResidueField (genericPoint A) ≫ a) ≫
        configurationQuotientMap (equationIdeal p hp) n := by
  letI : IsIntegral (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) n).left := hO
  letI : IsIntegral (configurationQuotientOpen (equationIdeal p hp) n).toScheme := hB
  let B := cubicConfigurationBase p hp n
  let d := (A.fromSpecResidueField (genericPoint A) ≫ a) ≫
    configurationQuotientMap (equationIdeal p hp) n
  have hd : d (IsLocalRing.closedPoint (A.residueField (genericPoint A))) = genericPoint B := by
    change configurationQuotientMap (equationIdeal p hp) n
      (a (A.fromSpecResidueField (genericPoint A) _)) = genericPoint B
    rw [Scheme.fromSpecResidueField_apply, genericPoint_eq_of_isOpenImmersion a]
    exact genericPoint_map_of_surjective (configurationQuotientMap (equationIdeal p hp) n)
  exact ⟨B.genericFieldPointRingHom d hd, B.genericFieldPointRingHom_spec d hd⟩

end PfaffianDescent
