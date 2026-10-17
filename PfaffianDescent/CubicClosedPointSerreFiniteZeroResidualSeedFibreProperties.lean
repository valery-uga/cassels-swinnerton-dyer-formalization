import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualSeedResidueField
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualEtaleFibreStalkField
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_finiteToField_finite
    {E : Type u} [Field E] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of E)) [IsFinite f] : Finite X := by
  have hf := f.finite_preimage_singleton (IsLocalRing.closedPoint E)
  have he : f ⁻¹' {IsLocalRing.closedPoint E} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [he] at hf
  exact Set.finite_univ_iff.mp hf

theorem cubicClosedPointSerreFiniteZeroResidual_seed_residue_fibre_fields
    {E : Type u} [Field E] {X Y : Scheme.{u}}
    (g : X ⟶ Y) (s : Spec (.of E) ⟶ Y)
    [Etale (pullback.snd g s)] (z : g.fiber (s (IsLocalRing.closedPoint E))) :
    IsField ((g.fiber (s (IsLocalRing.closedPoint E))).presheaf.stalk z) := by
  let k := cubicClosedPointSerreFiniteZeroResidual_seedResidueMap s
  let i := Y.fromSpecResidueField (s (IsLocalRing.closedPoint E))
  have hk : k ≫ i = s := cubicClosedPointSerreFiniteZeroResidual_seedResidueMap_comp s
  letI : Flat k := (cubicClosedPointSerreFiniteZeroResidual_seedResidueMap_flat_surjective s).1
  letI : Surjective k := (cubicClosedPointSerreFiniteZeroResidual_seedResidueMap_flat_surjective s).2
  apply cubicClosedPointSerreFiniteZeroResidual_fibre_stalks_isField_descend g i k _ z
  rw [hk]
  exact cubicClosedPointSerreFiniteZeroResidual_unramifiedField_stalk_isField (pullback.snd g s)

theorem cubicClosedPointSerreFiniteZeroResidual_seed_residue_fibre_finite
    {E : Type u} [Field E] {X Y : Scheme.{u}}
    (g : X ⟶ Y) (s : Spec (.of E) ⟶ Y)
    [IsFinite (pullback.snd g s)] : Finite (g.fiber (s (IsLocalRing.closedPoint E))) := by
  let k := cubicClosedPointSerreFiniteZeroResidual_seedResidueMap s
  let i := Y.fromSpecResidueField (s (IsLocalRing.closedPoint E))
  have hk : k ≫ i = s := cubicClosedPointSerreFiniteZeroResidual_seedResidueMap_comp s
  letI : Surjective k := (cubicClosedPointSerreFiniteZeroResidual_seedResidueMap_flat_surjective s).2
  let e := pullbackLeftPullbackSndIso g i k ≪≫ pullback.congrHom rfl hk
  letI : Finite (pullback g s : Scheme) :=
    cubicClosedPointSerreFiniteZeroResidual_finiteToField_finite (pullback.snd g s)
  letI : Finite (pullback (pullback.snd g i) k : Scheme) :=
    Finite.of_injective e.hom e.hom.isOpenEmbedding.injective
  exact Finite.of_surjective (pullback.fst (pullback.snd g i) k)
    ((surjective_iff _).mp inferInstance)

end PfaffianDescent
