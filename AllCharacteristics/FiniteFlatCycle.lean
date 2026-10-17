import AllCharacteristics.FiniteSchemeCycle
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Degree-preserving cycles on finite flat scheme fibers

This connects the intrinsic scheme rank, its base-change theorem, and the
fundamental-cycle construction. No affine presentation of a fiber is assumed.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AllCharacteristics
universe u

/-- Over a field, the coordinate-algebra rank agrees with Mathlib's intrinsic
rank of the scheme morphism. -/
theorem finiteSchemeRank_eq_finrank
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsFinite f] :
    finiteSchemeRank f = f.finrank (IsLocalRing.closedPoint k) := by
  have : Flat f := inferInstance
  have : IsAffine X := isAffine_of_isAffineHom f
  let A := Γ(X, ⊤)
  let g := X.isoSpec.inv ≫ f
  let a := Spec.preimage g
  let : Algebra k A := a.hom.toAlgebra
  have hg : Spec.map (CommRingCat.ofHom (algebraMap k A)) = g := Spec.map_preimage g
  have : IsFinite (Spec.map a) := by
    rw [Spec.map_preimage]
    infer_instance
  have : Module.Finite k A := (IsFinite.SpecMap_iff a).mp inferInstance
  have hga : g.finrank (IsLocalRing.closedPoint k) = Module.finrank k A := by
    rw [← hg, Scheme.Hom.finrank_SpecMap_algebraMap]
    exact congrFun (Module.rankAtStalk_eq_finrank_of_free (R := k) (M := A)) _
  change Module.finrank k A = f.finrank (IsLocalRing.closedPoint k)
  exact hga.symm.trans (congrFun (Scheme.Hom.finrank_comp_left_of_isIso X.isoSpec.inv f) _)

/-- A finite scheme over a field has an effective cycle whose degree is the
intrinsic rank of its structure morphism. -/
theorem exists_effectiveZeroCycle_degree_finrank_morphism
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsFinite f] :
    ∃ z : EffectiveZeroCycle X,
      EffectiveZeroCycle.degree f z = f.finrank (IsLocalRing.closedPoint k) := by
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_degree_finiteSchemeRank f
  exact ⟨z, hz.trans (finiteSchemeRank_eq_finrank f)⟩

/-- Every field-valued fiber of an actual finite flat scheme morphism has an
effective cycle of the rank at its image point. -/
theorem exists_effectiveZeroCycle_finite_flat_baseChange
    {Z B : Scheme.{u}} (f : Z ⟶ B) [IsFinite f] [Flat f]
    {k : Type u} [Field k] (b : Spec (.of k) ⟶ B) :
    ∃ z : EffectiveZeroCycle (pullback f b),
      EffectiveZeroCycle.degree (pullback.snd f b) z =
        f.finrank (b (IsLocalRing.closedPoint k)) := by
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_degree_finrank_morphism (pullback.snd f b)
  exact ⟨z, hz.trans (Scheme.Hom.finrank_pullback_snd f b _)⟩

/-- A finite flat finitely presented family over a local ring has constant rank
from every point to the closed point, including in mixed characteristic. -/
theorem finite_flat_rank_eq_closedPoint
    {R : Type u} [CommRing R] [IsLocalRing R]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of R))
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] (p : PrimeSpectrum R) :
    f.finrank p = f.finrank (IsLocalRing.closedPoint R) := by
  exact specializes_iff_eq.mp ((IsLocalRing.specializes_closedPoint p).map
    f.isLocallyConstant_finrank.continuous)

/-- The cycle on any field-valued fiber of a finite flat family over a local
ring has the same degree as the closed fiber's rank. -/
theorem exists_effectiveZeroCycle_finite_flat_local_baseChange
    {R : Type u} [CommRing R] [IsLocalRing R]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of R))
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    {k : Type u} [Field k] (b : Spec (.of k) ⟶ Spec (.of R)) :
    ∃ z : EffectiveZeroCycle (pullback f b),
      EffectiveZeroCycle.degree (pullback.snd f b) z =
        f.finrank (IsLocalRing.closedPoint R) := by
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_finite_flat_baseChange f b
  exact ⟨z, hz.trans (finite_flat_rank_eq_closedPoint f _)⟩

/-- A finite flat closed subscheme over a local ring supplies cycles of the
same degree on all field-valued fibers of the ambient scheme. This is the
scheme-theoretic degree-preservation step used after lifting a closed point. -/
theorem exists_effectiveZeroCycle_ambient_fiber
    {R : Type u} [CommRing R] [IsLocalRing R] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ Spec (.of R))
    [IsFinite (i ≫ f)] [Flat (i ≫ f)] [LocallyOfFinitePresentation (i ≫ f)]
    {k : Type u} [Field k] (b : Spec (.of k) ⟶ Spec (.of R)) :
    ∃ z : EffectiveZeroCycle (pullback f b),
      EffectiveZeroCycle.degree (pullback.snd f b) z =
        (i ≫ f).finrank (IsLocalRing.closedPoint R) := by
  let e := pullbackRightPullbackFstIso f b i
  let ib := e.inv ≫ pullback.snd i (pullback.fst f b)
  have hiso : IsClosedImmersion e.inv := by infer_instance
  have hbase : IsClosedImmersion (pullback.snd i (pullback.fst f b)) := by infer_instance
  have : IsClosedImmersion ib :=
    @IsClosedImmersion.comp _ _ _ _ _ hiso hbase
  have hcomp : ib ≫ pullback.snd f b = pullback.snd (i ≫ f) b :=
    (Category.assoc _ _ _).trans (pullbackRightPullbackFstIso_inv_snd_snd f b i)
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_finite_flat_local_baseChange (i ≫ f) b
  refine ⟨pushforwardClosedCycle ib z, ?_⟩
  rw [degree_pushforwardClosedCycle, hcomp]
  exact hz

end AllCharacteristics
