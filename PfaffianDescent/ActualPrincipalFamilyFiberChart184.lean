import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.Localization.Away.Basic

/-! Source-only184. Construct actual tensor charts in the ORIGINAL
Cartesian family, then specialize to the actual upstairs principal chart.
No target chart or target Cartesian square is supplied as a premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original family square and original upstairs chart construct its
canonical old tensor chart, with both original projections and actual
ambient Cartesian square. This needs no Artin or square-zero hypothesis. -/
lemma exists_actualAffineTensorChart184
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] {X X0 : Scheme.{u}}
    (F : X ⟶ Spec (.of R)) (d : X0 ⟶ X) (F0 : X0 ⟶ Spec (.of S))
    (H : IsPullback d F0 F (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (a : Spec (.of A) ⟶ X) [IsOpenImmersion a]
    (ha : a ≫ F = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    ∃ (a0 : Spec (.of (S ⊗[R] A)) ⟶ X0) (ha0 : IsOpenImmersion a0),
      a0 ≫ d = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) ≫ a ∧
      a0 ≫ F0 = Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) ∧
      IsPullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom)) a0 a d := by
  let delta := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom)
  let q := Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A)))
  have hTensor : IsPullback delta q
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct R S A).flip
  have hcomm : (delta ≫ a) ≫ F =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    calc
      _ = delta ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
        rw [Category.assoc, ha]
      _ = _ := hTensor.w
  obtain ⟨a0, hd, hs⟩ := H.exists_lift (delta ≫ a) q hcomm
  have houter : IsPullback delta (a0 ≫ F0) (a ≫ F)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [hs, ha]
    exact hTensor
  have hchart : IsPullback delta a0 a d := houter.of_bot hd.symm H
  have ha0 : IsOpenImmersion a0 :=
    MorphismProperty.of_isPullback hchart (inferInstance : IsOpenImmersion a)
  exact ⟨a0, ha0, hd, hs, hchart⟩

/-- The actual upstairs principal chart, using the original coefficient
localization and original chart inclusion verbatim. -/
def upstairsPrincipalChart184
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (a : Spec (.of A) ⟶ X) (t : A) : Spec (.of (Localization.Away t)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away t))) ≫ a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma upstairsPrincipalChart184_isOpenImmersion
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (a : Spec (.of A) ⟶ X) [IsOpenImmersion a] (t : A) :
    IsOpenImmersion (upstairsPrincipalChart184 a t) := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap A (Localization.Away t)))) :=
    IsOpenImmersion.of_isLocalization (S := Localization.Away t) t
  dsimp only [upstairsPrincipalChart184]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- All original R scalars commute on the upstairs principal chart. -/
lemma upstairsPrincipalChart184_base
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {X : Scheme.{u}} (F : X ⟶ Spec (.of R)) (a : Spec (.of A) ⟶ X)
    (ha : a ≫ F = Spec.map (CommRingCat.ofHom (algebraMap R A))) (t : A) :
    upstairsPrincipalChart184 a t ≫ F =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t))) := by
  calc
    _ = Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away t))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
      rw [upstairsPrincipalChart184, Category.assoc, ha]
    _ = _ := by
      rw [← Spec.map_comp]
      rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- For the EXACT upstairs parameter chosen178/181, construct the actual
principal tensor chart in the original old family, with literal whole
includeRight reduction, original S scalar map, and ambient pullback square.
No target principal chart or target square is a caller premise. -/
lemma exists_actualPrincipalTensorFiberChart184
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] {X X0 : Scheme.{u}}
    (F : X ⟶ Spec (.of R)) (d : X0 ⟶ X) (F0 : X0 ⟶ Spec (.of S))
    (H : IsPullback d F0 F (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (a : Spec (.of A) ⟶ X) [IsOpenImmersion a]
    (ha : a ≫ F = Spec.map (CommRingCat.ofHom (algebraMap R A))) (t : A) :
    ∃ (a0 : Spec (.of (S ⊗[R] Localization.Away t)) ⟶ X0)
      (ha0 : IsOpenImmersion a0),
      a0 ≫ d = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : Localization.Away t →ₐ[R]
          S ⊗[R] Localization.Away t).toRingHom) ≫ upstairsPrincipalChart184 a t ∧
      a0 ≫ F0 = Spec.map (CommRingCat.ofHom
        (algebraMap S (S ⊗[R] Localization.Away t))) ∧
      IsPullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : Localization.Away t →ₐ[R]
          S ⊗[R] Localization.Away t).toRingHom)) a0
        (upstairsPrincipalChart184 a t) d := by
  letI := upstairsPrincipalChart184_isOpenImmersion a t
  exact exists_actualAffineTensorChart184 F d F0 H (upstairsPrincipalChart184 a t)
    (upstairsPrincipalChart184_base F a ha t)

end PfaffianDescent
