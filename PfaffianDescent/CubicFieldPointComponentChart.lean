import PfaffianDescent.FieldPointOpenFactorization
import AllCharacteristics.HomogeneousProjectiveAmbient

/-! An actual component chart descends to the original cubic field point. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicFieldPoint_exists_chart_from_component
    {F L E : Type u} [Field F] [Field L] [Field E] [Algebra F L]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (i : Spec (.of L) ⟶ hypersurface p hp)
    (hi : i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (α : L →+* E) (j : Fin 4)
    (gE : ChartRing (equationIdeal p hp) j →+* E)
    (hE : Spec.map (CommRingCat.ofHom gE) ≫ chartι (equationIdeal p hp) j =
      Spec.map (CommRingCat.ofHom α) ≫ i) :
    ∃ g : ChartRing (equationIdeal p hp) j →+* L,
      g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap F L ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal p hp) j = i ∧
      α.comp g = gE := by
  let l := fieldPointOpenLift (chartι (equationIdeal p hp) j) i α
    (Spec.map (CommRingCat.ofHom gE)) hE.symm
  let g : ChartRing (equationIdeal p hp) j →+* L := (Spec.preimage l).hom
  have hg : Spec.map (CommRingCat.ofHom g) = l := Spec.map_preimage l
  have hpoint : Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal p hp) j = i := by
    rw [hg]
    exact fieldPointOpenLift_fac _ _ _ _ _
  refine ⟨g, ?_, hpoint, ?_⟩
  · have heq : CommRingCat.ofHom (chartBaseMap (equationIdeal p hp) j) ≫
        CommRingCat.ofHom g = CommRingCat.ofHom (algebraMap F L) := by
      apply Spec.map_injective
      rw [Spec.map_comp, ← chartι_toBase, ← Category.assoc, hpoint]
      exact hi
    exact congrArg CommRingCat.Hom.hom heq
  · have heq : CommRingCat.ofHom g ≫ CommRingCat.ofHom α =
        CommRingCat.ofHom gE := by
      apply Spec.map_injective
      rw [Spec.map_comp, hg]
      exact fieldPointOpenLift_extension _ _ _ _ _
    exact congrArg CommRingCat.Hom.hom heq

end PfaffianDescent
