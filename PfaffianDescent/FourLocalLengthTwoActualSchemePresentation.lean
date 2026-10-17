import PfaffianDescent.SingleSupportLengthTwoDualCoordinates
import AllCharacteristics.FiniteSigmaSpec

/-! Four independently supplied geometric length-two components have an
actual product-dual scheme presentation retaining their original immersion.
There is no arithmetic quartic point or external embedding certificate. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem singleSupport_lengthTwo_actual_dual_scheme_presentation
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase I)] (P : closedPoints (scheme I))
    (hSupport : Set.range i = {P.1})
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ toBase I) = 2) :
    ∃ (e : Z ≅ Spec (.of (DualNumber K))) (j : Fin 4)
      (y : Fin 4 → DualNumber K) (hy : y j = 1) (a v : Fin 4 → K),
      a j = 1 ∧ v j = 0 ∧ v ≠ 0 ∧
      (∀ r, y r = TrivSqZeroExt.inl (a r) + TrivSqZeroExt.inr (v r)) ∧
      Function.Surjective (aeval (R := K) y) ∧
      e.hom ≫ ambientNormalizedCoordinateChartPoint (F := K) y j hy =
        i ≫ quotientProjMap I := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  obtain ⟨j, x, hxj, eA, a, v, ha, hvj, hv, hcoords, hgen, hpoint⟩ :=
    singleSupport_lengthTwo_actual_dual_coordinates I i P hSupport hZ
  let eSpec := Scheme.Spec.mapIso eA.toRingEquiv.toCommRingCatIso.symm.op
  let e := Z.isoSpec ≪≫ eSpec
  let y : Fin 4 → DualNumber K := fun r => eA (x r)
  have hy : y j = 1 := by simp only [y, hxj, map_one]
  have hq : ambientNormalizedCoordinateChartPoint (F := K) y j hy =
      e.inv ≫ i ≫ quotientProjMap I := by
    change ambientNormalizedCoordinateChartPoint (F := K) (fun r => eA (x r)) j hy =
      Spec.map (CommRingCat.ofHom eA.toRingHom) ≫ Z.isoSpec.inv ≫ i ≫ quotientProjMap I
    exact hpoint
  refine ⟨e, j, y, hy, a, v, ha, hvj, hv, hcoords, hgen, ?_⟩
  rw [hq]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The actual disjoint-union source is isomorphic to Spec of the four dual
algebras, and the reconstructed ambient morphism is literally the supplied
coproduct immersion. Each normalized component point is obtained internally
from its own length-two scheme and its own algebra. -/
theorem fourLocalLengthTwo_actual_productDual_scheme_presentation
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (Z : Fin 4 → Scheme.{u}) (i : ∀ r, Z r ⟶ scheme I)
    [∀ r, IsClosedImmersion (i r)] [∀ r, IsFinite (i r ≫ toBase I)]
    (P : Fin 4 → closedPoints (scheme I))
    (hSupport : ∀ r, Set.range (i r) = {(P r).1})
    (hZ : ∀ r, AllCharacteristics.finiteSchemeRank (i r ≫ toBase I) = 2) :
    letI : IsIso (sigmaSpec (fun _ : Fin 4 => CommRingCat.of (DualNumber K))) :=
      AllCharacteristics.isIso_sigmaSpec_const_finite (Fin 4) (DualNumber K)
    ∃ (e : (∐ Z) ≅ Spec (.of (QuarticNet.FourTangentDualAlgebra K)))
      (j : Fin 4 → Fin 4) (y : Fin 4 → Fin 4 → DualNumber K)
      (hy : ∀ r, y r (j r) = 1) (a v : Fin 4 → Fin 4 → K),
      (∀ r, a r (j r) = 1 ∧ v r (j r) = 0 ∧ v r ≠ 0) ∧
      (∀ r s, y r s = TrivSqZeroExt.inl (a r s) + TrivSqZeroExt.inr (v r s)) ∧
      (∀ r, Function.Surjective (aeval (R := K) (y r))) ∧
      e.hom ≫
        (inv (sigmaSpec (fun _ : Fin 4 => CommRingCat.of (DualNumber K))) ≫
          Sigma.desc (fun r => ambientNormalizedCoordinateChartPoint (F := K)
            (y r) (j r) (hy r))) =
        Sigma.desc (fun r => i r ≫ quotientProjMap I) := by
  classical
  have hEach (r : Fin 4) := singleSupport_lengthTwo_actual_dual_scheme_presentation
    I (i r) (P r) (hSupport r) (hZ r)
  choose eRow j y hy a v ha hvj hv hcoords hgen hpoint using hEach
  letI : IsIso (sigmaSpec (fun _ : Fin 4 => CommRingCat.of (DualNumber K))) :=
    AllCharacteristics.isIso_sigmaSpec_const_finite (Fin 4) (DualNumber K)
  let e := Sigma.mapIso eRow ≪≫
    asIso (sigmaSpec (fun _ : Fin 4 => CommRingCat.of (DualNumber K)))
  refine ⟨e, j, y, hy, a, v, fun r => ⟨ha r, hvj r, hv r⟩, hcoords, hgen, ?_⟩
  simp only [e, Iso.trans_hom, asIso_hom, ← Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]
  apply Sigma.hom_ext
  intro r
  rw [← Category.assoc, Sigma.ι_mapIso_hom, Category.assoc, Sigma.ι_desc]
  exact hpoint r

end PfaffianDescent
