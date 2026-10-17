import PfaffianDescent.LineGrassmannianProjIso
import PfaffianDescent.GoodPairProductIsomorphism

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K]

/-- The actual product of two standard Proj projective lines over the base. -/
noncomputable abbrev projectiveLineProjPair : Scheme.{u} :=
  pullback (projectiveLineProjToBase K) (projectiveLineProjToBase K)

noncomputable def projectiveLineProjPairToBase : projectiveLineProjPair K ⟶ Spec (.of K) :=
  pullback.fst _ _ ≫ projectiveLineProjToBase K

/-- The actual product of three standard Proj projective lines over the base. -/
noncomputable abbrev projectiveLineProjTriple : Scheme.{u} :=
  pullback (projectiveLineProjToBase K) (projectiveLineProjPairToBase K)

noncomputable def projectiveLineProjTripleToBase : projectiveLineProjTriple K ⟶ Spec (.of K) :=
  pullback.fst _ _ ≫ projectiveLineProjToBase K

noncomputable def linePairProjIso : linePairScheme K ≅ projectiveLineProjPair K :=
  asIso (pullback.map (grassmannianToBase K 1 1) (grassmannianToBase K 1 1)
    (projectiveLineProjToBase K) (projectiveLineProjToBase K)
    (lineGrassmannianProjIso K).hom (lineGrassmannianProjIso K).hom (𝟙 _)
    (by rw [Category.comp_id, lineGrassmannianProjIso_toBase])
    (by rw [Category.comp_id, lineGrassmannianProjIso_toBase]))

lemma linePairProjIso_toBase :
    (linePairProjIso K).hom ≫ projectiveLineProjPairToBase K = linePairToBase K := by
  change pullback.lift _ _ _ ≫ (pullback.fst _ _ ≫ projectiveLineProjToBase K) =
    pullback.fst _ _ ≫ grassmannianToBase K 1 1
  rw [← Category.assoc, pullback.lift_fst, Category.assoc, lineGrassmannianProjIso_toBase]

noncomputable def lineTripleProjIso : lineTripleScheme K ≅ projectiveLineProjTriple K :=
  asIso (pullback.map (grassmannianToBase K 1 1) (linePairToBase K)
    (projectiveLineProjToBase K) (projectiveLineProjPairToBase K)
    (lineGrassmannianProjIso K).hom (linePairProjIso K).hom (𝟙 _)
    (by rw [Category.comp_id, lineGrassmannianProjIso_toBase])
    (by rw [Category.comp_id, linePairProjIso_toBase]))

lemma lineTripleProjIso_toBase :
    (lineTripleProjIso K).hom ≫ projectiveLineProjTripleToBase K = lineTripleToBase K := by
  change pullback.lift _ _ _ ≫ (pullback.fst _ _ ≫ projectiveLineProjToBase K) =
    pullback.fst _ _ ≫ grassmannianToBase K 1 1
  rw [← Category.assoc, pullback.lift_fst, Category.assoc, lineGrassmannianProjIso_toBase]

end
section
variable (K : Type u) [Field K] [CharZero K]

/-- The full first-two-form isotropic locus is the product of three standard Proj projective lines. -/
noncomputable def goodPairProjProductIso : goodPairIncidenceFiber K ≅ projectiveLineProjTriple K :=
  goodPairProductIso K ≪≫ lineTripleProjIso K

lemma goodPairProjProductIso_toBase :
    (goodPairProjProductIso K).hom ≫ projectiveLineProjTripleToBase K = goodPairIncidenceFiberToBase K := by
  change ((goodPairProductIso K).hom ≫ (lineTripleProjIso K).hom) ≫ projectiveLineProjTripleToBase K = _
  rw [Category.assoc, lineTripleProjIso_toBase]
  exact goodPairProductIso_overBase K

end
end PfaffianDescent
