import PfaffianDescent.FourCoordinateVertexWholeSchemeCoproductIso

/-! The full-base-scheme alternative on a separately supplied WHOLE Z.
Its canonical four-component decomposition and skew row rescaling are
derived, preserving the exact given immersion and every nilpotent. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
attribute [local instance] MvPolynomial.gradedAlgebra

def fourCoordinateVertexWholeActualTangentMatrix
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [IsClosedImmersion i] [IsFinite (i ≫ toBase ⊥)]
    (Y : Fin 4 → Scheme.{u}) (c : ∀ r, Y r ⟶ Z) [∀ r, IsClosedImmersion (c r)]
    (hSupport : ∀ r, Set.range (c r ≫ i) = {coordinateVertex (K := K) r})
    (hComponents : ∀ r, AllCharacteristics.finiteSchemeRank (c r ≫ (i ≫ toBase ⊥)) = 2) :
    Fin 4 → Fin 4 → K := by
  letI : ∀ r, IsClosedImmersion (c r ≫ i) := fun r => inferInstance
  letI : ∀ r, IsFinite ((c r ≫ i) ≫ toBase ⊥) := by
    intro r
    rw [Category.assoc]
    infer_instance
  have hComponents' : ∀ r, AllCharacteristics.finiteSchemeRank ((c r ≫ i) ≫ toBase ⊥) = 2 := by
    intro r
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank, Category.assoc,
      ← AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact hComponents r
  exact fourCoordinateVertexActualTangentMatrix Y (fun r => c r ≫ i) hSupport hComponents'

theorem fourCoordinateVertex_whole_intrinsicDimension_fullBase_alternative
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [IsClosedImmersion i] [IsFinite (i ≫ toBase ⊥)]
    (Y : Fin 4 → Scheme.{u}) (c : ∀ r, Y r ⟶ Z) [∀ r, IsClosedImmersion (c r)]
    (hDisjoint : Pairwise fun r s => Disjoint (Set.range (c r)) (Set.range (c s)))
    (hSupport : ∀ r, Set.range (c r ≫ i) = {coordinateVertex (K := K) r})
    (hComponents : ∀ r, AllCharacteristics.finiteSchemeRank (c r ≫ (i ≫ toBase ⊥)) = 2)
    (hWhole : AllCharacteristics.finiteSchemeRank (i ≫ toBase ⊥) = 8)
    (hdim : 3 ≤ finrank K (intrinsicFullQuadraticSystem (i ≫ quotientProjMap ⊥)))
    (hnonzero : ∀ r s, r ≠ s →
      fourCoordinateVertexWholeActualTangentMatrix i Y c hSupport hComponents r s ≠ 0) :
    QuarticNet.IntrinsicFullBaseEmbeddedAlternative (i ≫ quotientProjMap ⊥) := by
  letI : ∀ r, IsClosedImmersion (c r ≫ i) := fun r => inferInstance
  letI : ∀ r, IsFinite ((c r ≫ i) ≫ toBase ⊥) := by
    intro r
    rw [Category.assoc]
    infer_instance
  have hComponents' : ∀ r, AllCharacteristics.finiteSchemeRank ((c r ≫ i) ≫ toBase ⊥) = 2 := by
    intro r
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank, Category.assoc,
      ← AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact hComponents r
  let j := Sigma.desc c
  letI : IsIso j := fourCoordinateVertex_wholeScheme_canonicalCoproduct_isIso
    i Y c hDisjoint hSupport hComponents hWhole
  let qWhole := i ≫ quotientProjMap (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
  let qSum := Sigma.desc (fun r => (c r ≫ i) ≫ quotientProjMap ⊥)
  have hSum : qSum = j ≫ qWhole := by
    apply Sigma.hom_ext
    intro r
    simp only [qSum, j, qWhole, Category.assoc, Sigma.ι_desc_assoc, Sigma.ι_desc]
  have hdimSum : 3 ≤ finrank K (intrinsicFullQuadraticSystem qSum) := by
    rw [hSum, intrinsicFullQuadraticSystem_comp_isIso]
    exact hdim
  have hNonzeroActual : ∀ r s, r ≠ s →
      fourCoordinateVertexActualTangentMatrix Y (fun r => c r ≫ i) hSupport hComponents' r s ≠ 0 :=
    hnonzero
  have hAlternative : QuarticNet.IntrinsicFullBaseEmbeddedAlternative qSum :=
    fourCoordinateVertex_intrinsicDimension_fullBase_alternative
      Y (fun r => c r ≫ i) hSupport hComponents' hdimSum hNonzeroActual
  have hOriginal : inv j ≫ qSum = qWhole := by
    rw [hSum, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have h := QuarticNet.intrinsicFullBase_embedded_alternative_precomp_iso
    (asIso j).symm qSum hAlternative
  change QuarticNet.IntrinsicFullBaseEmbeddedAlternative (inv j ≫ qSum) at h
  simpa only [hOriginal] using h

end PfaffianDescent
