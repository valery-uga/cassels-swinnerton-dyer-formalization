import AllCharacteristics.FreeActionEtale
import Mathlib.AlgebraicGeometry.Pullbacks
import AllCharacteristics.FiniteSigmaSpec

/-!
# The actual affine quotient kernel pair of a free finite-group action

Tensor evaluation constructs the map from the disjoint union of the original
scheme, indexed by the original group, to the actual quotient kernel pair.
The tensor-square isomorphism proves that this map is an isomorphism when the
action is scheme-theoretically free.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AllCharacteristics
universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
variable (G : Type) [Group G] [MulSemiringAction G B] [SMulCommClass G R B]

/-- The spectrum comparison with the actual invariant-quotient kernel pair. -/
noncomputable def affineInvariantPullbackSpecIso :
    pullback (affineInvariantQuotientMap R B G) (affineInvariantQuotientMap R B G) ≅
      Spec (.of (B ⊗[FixedPoints.subalgebra R B G] B)) :=
  pullbackSpecIso (FixedPoints.subalgebra R B G) B B

/-- The spectrum comparison identifies the first projection with tensor inclusion. -/
theorem affineInvariantPullbackSpecIso_inv_fst :
    (affineInvariantPullbackSpecIso R B G).inv ≫
      pullback.fst (affineInvariantQuotientMap R B G) (affineInvariantQuotientMap R B G) =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          B →+* B ⊗[FixedPoints.subalgebra R B G] B)) :=
  pullbackSpecIso_inv_fst _ _ _

/-- The spectrum comparison identifies the second projection with tensor inclusion. -/
theorem affineInvariantPullbackSpecIso_inv_snd :
    (affineInvariantPullbackSpecIso R B G).inv ≫
      pullback.snd (affineInvariantQuotientMap R B G) (affineInvariantQuotientMap R B G) =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          B →ₐ[FixedPoints.subalgebra R B G] B ⊗[FixedPoints.subalgebra R B G] B).toRingHom) :=
  pullbackSpecIso_inv_snd _ _ _

/-- The actual group-indexed map to the quotient kernel pair, constructed from tensor evaluation. -/
noncomputable def affineInvariantKernelPairMap :
    (∐ fun _ : G ↦ Spec (.of B)) ⟶
      pullback (affineInvariantQuotientMap R B G) (affineInvariantQuotientMap R B G) :=
  Sigma.desc (fun g ↦ Spec.map (CommRingCat.ofHom (invariantTensorEvaluation R B G g).toRingHom) ≫
    (affineInvariantPullbackSpecIso R B G).inv)

/-- Each component is the original spectrum of the corresponding tensor evaluation. -/
theorem affineInvariantKernelPairMap_component (g : G) :
    Sigma.ι (fun _ : G ↦ Spec (.of B)) g ≫ affineInvariantKernelPairMap R B G =
      Spec.map (CommRingCat.ofHom (invariantTensorEvaluation R B G g).toRingHom) ≫
        (affineInvariantPullbackSpecIso R B G).inv :=
  Sigma.ι_desc _ _

/-- The first kernel-pair projection is the identity on each original group component. -/
theorem affineInvariantKernelPairMap_component_fst (g : G) :
    (Sigma.ι (fun _ : G ↦ Spec (.of B)) g ≫ affineInvariantKernelPairMap R B G) ≫
      pullback.fst (affineInvariantQuotientMap R B G) (affineInvariantQuotientMap R B G) =
        𝟙 (Spec (.of B)) := by
  rw [affineInvariantKernelPairMap_component, Category.assoc, affineInvariantPullbackSpecIso_inv_fst,
    ← Spec.map_comp]
  have he : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
      B →+* B ⊗[FixedPoints.subalgebra R B G] B) ≫
        CommRingCat.ofHom (invariantTensorEvaluation R B G g).toRingHom = 𝟙 (CommRingCat.of B) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    change b * (g • (1 : B)) = b
    rw [smul_one, mul_one]
  rw [he]
  exact Spec.map_id (.of B)

/-- The second kernel-pair projection is the original action on each group component. -/
theorem affineInvariantKernelPairMap_component_snd (g : G) :
    (Sigma.ι (fun _ : G ↦ Spec (.of B)) g ≫ affineInvariantKernelPairMap R B G) ≫
      pullback.snd (affineInvariantQuotientMap R B G) (affineInvariantQuotientMap R B G) =
        Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G B g)) := by
  rw [affineInvariantKernelPairMap_component, Category.assoc, affineInvariantPullbackSpecIso_inv_snd,
    ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  change 1 * (g • b) = g • b
  exact one_mul _

/-- The actual quotient kernel pair is the disjoint union of the original
action graphs when the finite-group action is scheme-theoretically free. -/
theorem isIso_affineInvariantKernelPairMap_of_free [Fintype G]
    (hfree : ∀ g : G, g ≠ 1 → actionDifferenceIdeal B G g = ⊤) :
    IsIso (affineInvariantKernelPairMap R B G) := by
  let e := freeActionTensorAlgEquiv R B G hfree
  let α : CommRingCat.of (B ⊗[FixedPoints.subalgebra R B G] B) ⟶ CommRingCat.of (G → B) := CommRingCat.ofHom e.toRingHom
  have : IsIso (Spec.map α) := isIso_SpecMap_iff.mpr e.bijective
  have he : affineInvariantKernelPairMap R B G =
      (sigmaSpec (fun _ : G ↦ CommRingCat.of B) ≫ Spec.map α) ≫
        (affineInvariantPullbackSpecIso R B G).inv := by
    apply Sigma.hom_ext
    intro g
    rw [affineInvariantKernelPairMap_component, ← Category.assoc, ← Category.assoc,
      ι_sigmaSpec, ← Spec.map_comp]
    rfl
  have hs : IsIso (sigmaSpec (fun _ : G ↦ CommRingCat.of B)) :=
    isIso_sigmaSpec_const_finite G B
  have hk : IsIso (affineInvariantPullbackSpecIso R B G).inv := inferInstance
  have ht : IsIso ((sigmaSpec (fun _ : G ↦ CommRingCat.of B) ≫ Spec.map α) ≫
      (affineInvariantPullbackSpecIso R B G).inv) := inferInstance
  exact he.symm ▸ ht

end AllCharacteristics
