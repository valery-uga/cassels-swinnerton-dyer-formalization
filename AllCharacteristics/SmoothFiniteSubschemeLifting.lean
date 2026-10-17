import AllCharacteristics.SmoothFinitePointLifting
import AllCharacteristics.FiniteLocalClosedImmersion
import AllCharacteristics.ResidueSpecialFiber

/-!
# Embedded finite flat lifting of closed points

Over a complete local ring, a finite residue-field point of a smooth separated
family lifts to an actual finite flat closed subscheme. Its special fiber is
exactly the original point as a scheme, and its free rank is the full residue
extension degree. No separability assumption or Hilbert-scheme input is needed.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
namespace AllCharacteristics
universe u

/-- A finite closed residue point lifts to an embedded finite free algebra,
with its entire special fiber and original embedding retained. -/
theorem lift_smooth_finite_closed_point
    {R k L : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [Field k] [Field L]
    [Algebra k L] [Module.Finite k L]
    (b : R →+* k) (hb : Function.Surjective b)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Smooth f] [IsSeparated f]
    (q : Spec (.of L) ⟶ X) [IsClosedImmersion q]
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom ((algebraMap k L).comp b))) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : IsLocalRing A)
      (_ : Module.Free R A) (_ : Module.Finite R A)
      (_ : IsAdicComplete (maximalIdeal A) A) (c : A →+* L)
      (s : Spec (.of A) ⟶ X),
      IsClosedImmersion s ∧
      Module.finrank R A = Module.finrank k L ∧
      s ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
      Spec.map (CommRingCat.ofHom c) ≫ s = q ∧
      IsPullback (Spec.map (CommRingCat.ofHom c))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom b)) := by
  obtain ⟨A, _, _, _, _, _, _, c, hc, hcomm, hrank, hmax⟩ :=
    hasCompleteLocalLift_of_finite_extension (L := L) b hb
  have hcoef : c.comp (algebraMap R A) = (algebraMap k L).comp b := RingHom.ext hcomm
  obtain ⟨s, hs, hred⟩ := lift_smooth_point_to_complete_local_algebra f c hc q
    (by rw [hcoef]; exact hq)
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom c) ≫ s) := by
    rw [hred]
    infer_instance
  have hi := isClosedImmersion_of_local_residue_closedImmersion c hc hmax f s hs
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, c, s, hi, hrank, hs, hred,
    isPullback_residue_of_extended_maximalIdeal b c hb hc hcoef hmax⟩

/-- Scheme formulation of embedded point lifting: the lifted subscheme is
finite flat of the prescribed rank, and its special fiber equals the given
finite closed point, including its embedding into the ambient family. -/
theorem exists_finite_flat_closed_subscheme_of_smooth_finite_point
    {R k L : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [Field k] [Field L]
    [Algebra k L] [Module.Finite k L]
    (b : R →+* k) (hb : Function.Surjective b)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Smooth f] [IsSeparated f]
    (q : Spec (.of L) ⟶ X) [IsClosedImmersion q]
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom ((algebraMap k L).comp b))) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (j : Spec (.of L) ⟶ Z),
      IsClosedImmersion i ∧ IsFinite (i ≫ f) ∧ Flat (i ≫ f) ∧
      (∀ r, (i ≫ f).finrank r = Module.finrank k L) ∧
      j ≫ i = q ∧
      IsPullback j (Spec.map (CommRingCat.ofHom (algebraMap k L)))
        (i ≫ f) (Spec.map (CommRingCat.ofHom b)) := by
  obtain ⟨A, _, _, _, _, _, _, c, s, hi, hrank, hs, hred, hpull⟩ :=
    lift_smooth_finite_closed_point b hb f q hq
  have hfinite : IsFinite (s ≫ f) := by
    rw [hs]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hflat : Flat (s ≫ f) := by
    rw [hs]
    exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  refine ⟨Spec (.of A), s, Spec.map (CommRingCat.ofHom c), hi, hfinite, hflat,
    ?_, hred, ?_⟩
  · intro r
    rw [hs]
    exact (Scheme.Hom.finrank_SpecMap_algebraMap R A r).trans
      ((congrFun (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := A)) r).trans hrank)
  · rw [hs]
    exact hpull

end AllCharacteristics
