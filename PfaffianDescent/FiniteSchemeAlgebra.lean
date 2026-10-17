import AllCharacteristics.FiniteFlatCycle
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
universe u
section
variable {K : Type u} [Field K] {X Z : Scheme.{u}}

/-- The coefficient algebra on the actual global sections of a finite scheme. -/
noncomputable abbrev finiteSchemeCoefficientAlgebra (f : X ⟶ Spec (.of K)) [IsFinite f] :
    Algebra K Γ(X, ⊤) :=
  letI : IsAffine X := isAffine_of_isAffineHom f
  (Spec.preimage (X.isoSpec.inv ≫ f)).hom.toAlgebra

lemma finiteSchemeCoefficient_spec (f : X ⟶ Spec (.of K)) [IsFinite f] [IsAffine X] :
    letI := finiteSchemeCoefficientAlgebra f
    Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤))) = X.isoSpec.inv ≫ f := by
  exact Spec.map_preimage _

/-- Equal finite structural morphisms induce the same coefficient map on
global functions, even when their canonical finite-scheme algebra instances
are introduced separately. -/
lemma finiteSchemeCoefficient_algebraMap_eq_of_eq
    (f g : X ⟶ Spec (.of K)) [IsFinite f] [IsFinite g] (hfg : f = g) :
    @algebraMap K Γ(X, ⊤) _ _ (finiteSchemeCoefficientAlgebra f) =
      @algebraMap K Γ(X, ⊤) _ _ (finiteSchemeCoefficientAlgebra g) := by
  letI : IsAffine X := isAffine_of_isAffineHom f
  apply congrArg CommRingCat.Hom.hom
  apply Spec.map_injective
  calc
    Spec.map (Spec.preimage (X.isoSpec.inv ≫ f)) = X.isoSpec.inv ≫ f :=
      Spec.map_preimage _
    _ = X.isoSpec.inv ≫ g := congrArg (X.isoSpec.inv ≫ ·) hfg
    _ = Spec.map (Spec.preimage (X.isoSpec.inv ≫ g)) := (Spec.map_preimage _).symm

lemma finiteSchemeCoefficient_finite (f : X ⟶ Spec (.of K)) [IsFinite f] :
    letI := finiteSchemeCoefficientAlgebra f
    Module.Finite K Γ(X, ⊤) := by
  letI := finiteSchemeCoefficientAlgebra f
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))) := by
    rw [finiteSchemeCoefficient_spec f]
    infer_instance
  exact (IsFinite.SpecMap_iff _).mp this

lemma finiteSchemeCoefficient_finrank (f : X ⟶ Spec (.of K)) [IsFinite f] :
    letI := finiteSchemeCoefficientAlgebra f
    finrank K Γ(X, ⊤) = AllCharacteristics.finiteSchemeRank f := rfl

/-- A field-valued point of a finite scheme induces an algebra homomorphism
from its global coordinate algebra to the point's coefficient field. -/
noncomputable def finiteSchemePointAlgHom
    {L : Type u} [Field L]
    (f : X ⟶ Spec (.of K)) [IsFinite f]
    (a : Spec (.of L) ⟶ X) (b : K →+* L)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom b)) :
    letI := finiteSchemeCoefficientAlgebra f
    letI : Algebra K L := b.toAlgebra
    Γ(X, ⊤) →ₐ[K] L := by
  letI := finiteSchemeCoefficientAlgebra f
  letI : Algebra K L := b.toAlgebra
  letI : IsAffine X := isAffine_of_isAffineHom f
  let e : Γ(X, ⊤) →+* L :=
    (Spec.preimage (a ≫ X.isoSpec.hom)).hom
  refine { e with commutes' := ?_ }
  have he : CommRingCat.ofHom (algebraMap K Γ(X, ⊤)) ≫
      CommRingCat.ofHom e = CommRingCat.ofHom b := by
    apply Spec.map_injective
    dsimp only [e]
    rw [Spec.map_comp]
    change Spec.map (Spec.preimage (a ≫ X.isoSpec.hom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤))) = _
    rw [Spec.map_preimage, finiteSchemeCoefficient_spec f]
    rw [← Category.assoc, Category.assoc a X.isoSpec.hom X.isoSpec.inv,
      Iso.hom_inv_id, Category.comp_id]
    exact ha
  intro r
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom he) r

/-- The spectrum map of the algebra homomorphism attached to a field-valued
point is the point followed by the canonical affine presentation. -/
lemma finiteSchemePointAlgHom_spec
    {L : Type u} [Field L]
    (f : X ⟶ Spec (.of K)) [IsFinite f]
    (a : Spec (.of L) ⟶ X) (b : K →+* L)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom b)) :
    letI := finiteSchemeCoefficientAlgebra f
    letI : Algebra K L := b.toAlgebra
    letI : IsAffine X := isAffine_of_isAffineHom f
    Spec.map (CommRingCat.ofHom
        (finiteSchemePointAlgHom f a b ha).toRingHom) =
      a ≫ X.isoSpec.hom := by
  exact Spec.map_preimage _

/-- Distinct field-valued points of a finite scheme give distinct maps on
its coordinate algebra. -/
theorem finiteSchemePointAlgHom_injective_of_point_injective
    {L : Type u} [Field L] {ι : Type u}
    (f : X ⟶ Spec (.of K)) [IsFinite f]
    (a : ι → (Spec (.of L) ⟶ X)) (b : K →+* L)
    (ha : ∀ i, a i ≫ f = Spec.map (CommRingCat.ofHom b))
    (hinj : Function.Injective a) :
    letI := finiteSchemeCoefficientAlgebra f
    letI : Algebra K L := b.toAlgebra
    Function.Injective (fun i => finiteSchemePointAlgHom f (a i) b (ha i)) := by
  letI := finiteSchemeCoefficientAlgebra f
  letI : Algebra K L := b.toAlgebra
  letI : IsAffine X := isAffine_of_isAffineHom f
  intro i j hij
  apply hinj
  have hspec := congrArg
    (fun q : Γ(X, ⊤) →ₐ[K] L =>
      Spec.map (CommRingCat.ofHom q.toRingHom)) hij
  rw [finiteSchemePointAlgHom_spec, finiteSchemePointAlgHom_spec] at hspec
  exact (cancel_mono X.isoSpec.hom).mp hspec

/-- After passing through the canonical affine presentation of a finite
scheme, the algebra homomorphism attached to a field-valued point recovers
that point along every subsequent scheme morphism. -/
lemma finiteSchemePointAlgHom_spec_comp
    {L : Type u} [Field L] {Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsFinite f]
    (a : Spec (.of L) ⟶ X) (b : K →+* L)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom b))
    (j : X ⟶ Y) :
    letI := finiteSchemeCoefficientAlgebra f
    letI : Algebra K L := b.toAlgebra
    letI : IsAffine X := isAffine_of_isAffineHom f
    Spec.map (CommRingCat.ofHom
        (finiteSchemePointAlgHom f a b ha).toRingHom) ≫
      X.isoSpec.inv ≫ j = a ≫ j := by
  rw [finiteSchemePointAlgHom_spec]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- If a chosen affine presentation is identified with the canonical one,
the algebra homomorphism attached to a field-valued point recovers the point
through that chosen presentation. -/
lemma finiteSchemePointAlgHom_spec_comp_of_eq
    {L : Type u} [Field L] {Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsFinite f] [IsAffine X]
    (a : Spec (.of L) ⟶ X) (b : K →+* L)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom b))
    (j : X ⟶ Y) (c : Spec (.of Γ(X, ⊤)) ⟶ Y)
    (hc : c = X.isoSpec.inv ≫ j) :
    letI := finiteSchemeCoefficientAlgebra f
    letI : Algebra K L := b.toAlgebra
    Spec.map (CommRingCat.ofHom
        (finiteSchemePointAlgHom f a b ha).toRingHom) ≫ c = a ≫ j := by
  rw [hc]
  exact finiteSchemePointAlgHom_spec_comp f a b ha j

/-- Pullback of global functions for a closed immersion of finite schemes,
with the coefficient algebra structures induced by their scheme morphisms. -/
noncomputable def finiteSchemeClosedMap (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ Spec (.of K)) [IsFinite f] :
    letI := finiteSchemeCoefficientAlgebra f
    letI := finiteSchemeCoefficientAlgebra (i ≫ f)
    Γ(X, ⊤) →ₐ[K] Γ(Z, ⊤) := by
  letI := finiteSchemeCoefficientAlgebra f
  letI := finiteSchemeCoefficientAlgebra (i ≫ f)
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsAffine Z := isAffine_of_isAffineHom (i ≫ f)
  have hc : CommRingCat.ofHom (algebraMap K Γ(X, ⊤)) ≫ i.appTop =
      CommRingCat.ofHom (algebraMap K Γ(Z, ⊤)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, finiteSchemeCoefficient_spec f, ← Category.assoc,
      Scheme.isoSpec_inv_naturality, Category.assoc, finiteSchemeCoefficient_spec (i ≫ f)]
  exact { i.appTop.hom with commutes' := fun r => congr($hc r) }

lemma finiteSchemeClosedMap_surjective (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ Spec (.of K)) [IsFinite f] :
    Function.Surjective (finiteSchemeClosedMap i f) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine i).2

end
end PfaffianDescent
