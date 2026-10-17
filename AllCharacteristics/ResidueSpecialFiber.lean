import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Identifying a finite local lift's special fiber

A commutative square of rings is a pushout when its quotient maps are
surjective and the quotient kernel is the extended base kernel. Applied to
local residue maps, this identifies the entire scheme-theoretic special fiber.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
namespace AllCharacteristics
universe u

/-- A surjective quotient map commutes with base change when its kernel is
the extension of the original quotient kernel. -/
theorem isPushout_of_surjective_of_ker_map
    {R A k L : Type u} [CommRing R] [CommRing A] [CommRing k] [CommRing L]
    (a : R →+* A) (b : R →+* k) (c : A →+* L) (d : k →+* L)
    (hb : Function.Surjective b) (hc : Function.Surjective c)
    (hcomm : c.comp a = d.comp b)
    (hker : RingHom.ker c = (RingHom.ker b).map a) :
    IsPushout (CommRingCat.ofHom a) (CommRingCat.ofHom b)
      (CommRingCat.ofHom c) (CommRingCat.ofHom d) where
  w := by ext r; exact congr($hcomm r)
  isColimit' := by
    refine ⟨PushoutCocone.isColimitAux' _ fun t ↦ ?_⟩
    have hk : RingHom.ker c ≤ RingHom.ker t.inl.hom := by
      rw [hker, Ideal.map_le_iff_le_comap]
      intro r hr
      change t.inl (a r) = 0
      have he : t.inl (a r) = t.inr (b r) := congr($(t.condition) r)
      rw [he, show b r = 0 from hr, map_zero]
    let v := c.liftOfSurjective hc ⟨t.inl.hom, hk⟩
    refine ⟨CommRingCat.ofHom v, ?_, ?_, ?_⟩
    · ext x
      exact c.liftOfSurjective_comp_apply hc ⟨t.inl.hom, hk⟩ x
    · ext x
      obtain ⟨r, rfl⟩ := hb x
      change v (d (b r)) = t.inr (b r)
      rw [← show c (a r) = d (b r) from congr($hcomm r)]
      exact (c.liftOfSurjective_comp_apply hc ⟨t.inl.hom, hk⟩ (a r)).trans
        (congr($(t.condition) r))
    · intro h hh _
      ext x
      obtain ⟨a, rfl⟩ := hc x
      exact (congr($hh a)).trans
        (c.liftOfSurjective_comp_apply hc ⟨t.inl.hom, hk⟩ a).symm

/-- The residue field of a local algebra with extended maximal ideal is its
full scheme-theoretic fiber over the presented residue field of the base. -/
theorem isPullback_residue_of_extended_maximalIdeal
    {R A k L : Type u} [CommRing R] [IsLocalRing R] [CommRing A]
    [IsLocalRing A] [Field k] [Field L] [Algebra R A] [Algebra k L]
    (b : R →+* k) (c : A →+* L)
    (hb : Function.Surjective b) (hc : Function.Surjective c)
    (hcomm : c.comp (algebraMap R A) = (algebraMap k L).comp b)
    (hmax : maximalIdeal A = (maximalIdeal R).map (algebraMap R A)) :
    IsPullback (Spec.map (CommRingCat.ofHom c))
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom b)) := by
  apply isPullback_SpecMap_of_isPushout
  apply isPushout_of_surjective_of_ker_map _ _ _ _ hb hc hcomm
  rw [IsLocalRing.ker_eq_maximalIdeal c hc, IsLocalRing.ker_eq_maximalIdeal b hb, hmax]

end AllCharacteristics
