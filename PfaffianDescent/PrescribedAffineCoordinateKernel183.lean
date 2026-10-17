import PfaffianDescent.PrincipalAffineCoordinates181
import PfaffianDescent.WholeClosedAffineQuotient180

/-! Source-only183: identify the literal quotient kernel using a PROVED
geometric chart-coordinate equation, without assuming whole ideal transport. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual affine coordinate kernel uses exactly the prescribed section
coordinates whenever their Spec map is the actual chart. Equality of actual
and prescribed coordinate maps is DERIVED by faithful Spec and monicity. -/
lemma closedAffineCoordinateIdeal_eq_prescribed_coordinates183
    {T : Type u} [CommRing T] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.affineOpens) (E : Γ(X, V) ≃+* T)
    (a : Spec (.of T) ⟶ X) [IsOpenImmersion a]
    (hcoord : Spec.map (CommRingCat.ofHom E.toRingHom) ≫ V.2.fromSpec = a)
    (j : Z ⟶ Spec (.of T)) [IsClosedImmersion j] (hfac : j ≫ a = i) :
    closedAffineCoordinateIdeal180 j = (i.ker.ideal V).map E.toRingHom := by
  letI : IsIso (CommRingCat.ofHom E.toRingHom) := E.toCommRingCatIso.isIso_hom
  have hr : Set.range a = (V : Set X) := by
    rw [← hcoord]
    change Set.range (V.2.fromSpec ∘ Spec.map (CommRingCat.ofHom E.toRingHom)) = _
    rw [Set.range_comp, Set.range_eq_univ.mpr
      (Spec.map (CommRingCat.ofHom E.toRingHom)).surjective, Set.image_univ]
    exact V.2.range_fromSpec
  have hV : actualAffineChartOpen181 a = V := by
    apply Subtype.ext
    apply TopologicalSpace.Opens.ext
    change a '' (Set.univ : Set (Spec (.of T))) = (V : Set X)
    simpa only [Set.image_univ] using hr
  subst V
  have hmaps : Spec.map (CommRingCat.ofHom (actualAffineChartCoordinates181 a).toRingHom) =
      Spec.map (CommRingCat.ofHom E.toRingHom) := by
    apply (cancel_mono (actualAffineChartOpen181 a).2.fromSpec).mp
    exact (actualAffineChartCoordinates181_spec a).trans hcoord.symm
  have he : (actualAffineChartCoordinates181 a).toRingHom = E.toRingHom :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective hmaps)
  have hwhole := closedAffineCoordinateIdeal180_eq_chart_ideal i a j hfac
  change closedAffineCoordinateIdeal180 j =
    (i.ker.ideal (actualAffineChartOpen181 a)).map
      (actualAffineChartCoordinates181 a).toRingHom at hwhole
  exact hwhole.trans (congrArg
    (fun q => (i.ker.ideal (actualAffineChartOpen181 a)).map q) he)

end PfaffianDescent
