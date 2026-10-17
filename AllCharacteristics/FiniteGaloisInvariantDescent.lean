import AllCharacteristics.FreeActionAffineFactorization
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Data.Fintype.Shrink

/-!
# Descent of points through a finite Galois splitting field

The unordered configurations used in Voisin's generic-point argument are
obtained from ordered geometric conjugates.  This file supplies the affine
Galois descent mechanism: the automorphism action on a finite Galois field is
scheme-theoretically free, its invariant algebra is the ground field, and an
invariant morphism out of its spectrum descends to the ground field.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u

section
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

abbrev finiteGaloisGroupSmall : Type := Shrink (L ≃ₐ[K] L)

local notation "G" => finiteGaloisGroupSmall K L

noncomputable local instance galoisShrinkAction : MulSemiringAction G L :=
  MulSemiringAction.compHom L Shrink.mulEquiv.toMonoidHom

noncomputable local instance galoisShrink_smulComm : SMulCommClass G K L where
  smul_comm g r x := by
    change (Shrink.mulEquiv g) (r • x) = r • (Shrink.mulEquiv g) x
    simp only [Algebra.smul_def, map_mul, AlgEquiv.commutes]

/-- The canonical map from the ground field to the fixed subalgebra of its
finite Galois group is an equivalence. -/
noncomputable def galoisFixedPointsAlgEquiv :
    K ≃ₐ[K] FixedPoints.subalgebra K L G := by
  apply AlgEquiv.ofBijective (Algebra.ofId K _)
  constructor
  · exact RingHom.injective _
  · intro x
    have hx : ∀ g : L ≃ₐ[K] L, g x.val = x.val := by
      intro g
      have h := x.property (equivShrink.{0} (L ≃ₐ[K] L) g)
      change
        (Shrink.mulEquiv (equivShrink.{0} (L ≃ₐ[K] L) g)) x.val = x.val at h
      have he : Shrink.mulEquiv (equivShrink.{0} (L ≃ₐ[K] L) g) = g :=
        (equivShrink.{0} (L ≃ₐ[K] L)).symm_apply_apply g
      rw [he] at h
      exact h
    obtain ⟨a, ha⟩ :=
      (IsGalois.mem_range_algebraMap_iff_fixed (F := K) x.val).mpr hx
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact ha

/-- The affine invariant quotient of a finite Galois field is the spectrum of
the ground field. -/
noncomputable def finiteGaloisInvariantQuotientIso :
    affineInvariantQuotient K L G ≅ Spec (.of K) :=
  Scheme.Spec.mapIso
    (galoisFixedPointsAlgEquiv K L).toRingEquiv.toCommRingCatIso.op

/-- Under the identification of the invariant quotient with the ground-field
spectrum, the quotient map is the usual extension-of-scalars morphism. -/
theorem affineInvariantQuotientMap_comp_finiteGaloisInvariantQuotientIso_hom :
    affineInvariantQuotientMap K L G ≫
        (finiteGaloisInvariantQuotientIso K L).hom =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  change
    Spec.map (CommRingCat.ofHom
        (algebraMap (FixedPoints.subalgebra K L G) L)) ≫
      Spec.map (CommRingCat.ofHom
        (galoisFixedPointsAlgEquiv K L).toRingHom) = _
  rw [← Spec.map_comp]
  rfl

/-- A nonidentity automorphism of a field has empty fixed-point scheme for
the induced action: one nonzero difference is already a unit. -/
theorem galois_actionDifferenceIdeal_eq_top (g : G) (hg : g ≠ 1) :
    actionDifferenceIdeal L G g = ⊤ := by
  have hmove : ∃ x : L, x - g • x ≠ 0 := by
    by_contra h
    push Not at h
    apply hg
    apply Shrink.mulEquiv.injective
    ext x
    change g • x = (1 : G) • x
    rw [one_smul]
    exact (sub_eq_zero.mp (h x)).symm
  obtain ⟨x, hx⟩ := hmove
  apply Ideal.eq_top_of_isUnit_mem _
  · exact Ideal.subset_span ⟨x, rfl⟩
  · exact (isUnit_iff_ne_zero.mpr hx)

/-- The spectrum map of a finite Galois field extension is an epimorphism of
schemes. -/
theorem epi_specMap_finiteGalois :
    Epi (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  rw [← affineInvariantQuotientMap_comp_finiteGaloisInvariantQuotientIso_hom K L]
  have : IsRegularEpi (affineInvariantQuotientMap K L G) :=
    isRegularEpi_affineInvariantQuotientMap_of_free K L G
      (galois_actionDifferenceIdeal_eq_top K L)
  infer_instance

/-- Every morphism from a finite Galois splitting field which is invariant
under all field automorphisms descends to the invariant spectrum. -/
theorem existsUnique_galoisInvariantFactor {X : Scheme.{u}}
    (a : Spec (.of L) ⟶ X)
    (ha : ∀ g : G,
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G L g)) ≫ a = a) :
    ∃! b : affineInvariantQuotient K L G ⟶ X,
      affineInvariantQuotientMap K L G ≫ b = a :=
  existsUnique_affineInvariantSchemeFactor_of_free K L G
    (galois_actionDifferenceIdeal_eq_top K L) a ha

/-- A morphism from the spectrum of a finite Galois extension descends
uniquely to the ground field exactly when it is invariant under the Galois
action. -/
theorem existsUnique_finiteGaloisDescend {X : Scheme.{u}}
    (a : Spec (.of L) ⟶ X)
    (ha : ∀ g : G,
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G L g)) ≫ a = a) :
    ∃! b : Spec (.of K) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ b = a := by
  obtain ⟨c, hc, -⟩ := existsUnique_galoisInvariantFactor K L a ha
  let b : Spec (.of K) ⟶ X :=
    (finiteGaloisInvariantQuotientIso K L).inv ≫ c
  refine ⟨b, ?_, ?_⟩
  · dsimp only [b]
    rw [← affineInvariantQuotientMap_comp_finiteGaloisInvariantQuotientIso_hom K L,
      Category.assoc, Iso.hom_inv_id_assoc]
    exact hc
  · intro d hd
    let π : Spec (.of L) ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K L))
    haveI : Epi π := by
      dsimp only [π]
      rw [← affineInvariantQuotientMap_comp_finiteGaloisInvariantQuotientIso_hom K L]
      have : IsRegularEpi (affineInvariantQuotientMap K L G) :=
        isRegularEpi_affineInvariantQuotientMap_of_free K L G
          (galois_actionDifferenceIdeal_eq_top K L)
      infer_instance
    apply (cancel_epi π).mp
    exact hd.trans (by
      dsimp only [π]
      rw [← affineInvariantQuotientMap_comp_finiteGaloisInvariantQuotientIso_hom K L,
        Category.assoc, Iso.hom_inv_id_assoc]
      exact hc.symm)

end
end AllCharacteristics
